/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Probability.Moments.Basic

/-!
# Domination of moment generating functions and Chernoff bounds

A real random variable `X` under a measure `P` is *dominated* by a real random variable `Y` under
a measure `Q` on a set `Λ` of parameters if `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` for every `t ∈ Λ`,
as an inequality in `[0, ∞]`: at each `t ∈ Λ` where `exp (t Y)` is `Q`-integrable, `exp (t X)` is
`P`-integrable and `mgf X P t ≤ mgf Y Q t`. Domination on `Set.Ici 0` gives the Chernoff bounds of
the upper tail, domination on `Set.Iic 0` those of the lower tail, and domination on `Set.univ`
both. For example, a random variable with values in `[0, 1]` and mean at most `m` is dominated by
the Bernoulli law of mean `m` on `Set.Ici 0`, and identically distributed random variables dominate
each other on every set.

The Chernoff bound transfers through the domination: the sum `∑ i ∈ s, X i` of independent random
variables dominated by `Y` on `Λ` satisfies, for `t ∈ Λ` with `t ≥ 0`,
`P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s`, the Chernoff bound of a sum of `#s`
independent copies of `Y`; symmetrically for the lower tail and `t ≤ 0`. With `Y` the statistic of
an exponential family, this gives Cramér–Chernoff bounds for random variables that are dominated
by a member of the family without following its law.

## Main definitions

* `LMLExplore.MGFDominatedOn X P Y Q Λ`: `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` for every `t ∈ Λ`.

## Main statements

* `ProbabilityTheory.IdentDistrib.mgfDominatedOn`: identically distributed random variables
  dominate each other on every set.
* `LMLExplore.MGFDominatedOn.mono`, `LMLExplore.MGFDominatedOn.neg`,
  `LMLExplore.MGFDominatedOn.trans`: domination on `Λ` implies domination on every subset of `Λ`;
  if `X` is dominated by `Y` on `Λ`, then `-X` is dominated by `-Y` on `-Λ`; domination on `Λ` is
  transitive.
* `LMLExplore.MGFDominatedOn.integrable`: a random variable dominated on a neighbourhood of `0` by
  a random variable with exponential moments near `0` is integrable.
* `LMLExplore.mgfDominatedOn_union`, `LMLExplore.MGFDominatedOn.union`,
  `LMLExplore.MGFDominatedOn.univ_of_Iic_of_Ici`: domination on `Λ ∪ Λ'` is domination on both
  `Λ` and `Λ'`; in particular domination on `Set.Iic 0` and on `Set.Ici 0` gives domination on
  `Set.univ`.
* `ProbabilityTheory.iIndepFun.mgf_sum_le_pow_of_mgfDominatedOn`: for independent `X i` dominated
  by `Y` on `Λ` and `t ∈ Λ` with `exp (t Y)` integrable,
  `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`.
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_mul_mgf_pow`,
  `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_mul_mgf_pow`: the Chernoff bounds
  `P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s` for `t ∈ Λ` with `t ≥ 0`, and
  `P(∑ i ∈ s, X i ≤ a) ≤ exp (-t a) (mgf Y Q t) ^ #s` for `t ∈ Λ` with `t ≤ 0`.
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_mul_sub_cgf`,
  `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_mul_sub_cgf`: the same bounds in cgf
  form, `P(#s x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s (t x - cgf Y Q t)))` for `t ∈ Λ` with `t ≥ 0`, and
  `P(∑ i ∈ s, X i ≤ #s x) ≤ exp (-(#s (t x - cgf Y Q t)))` for `t ∈ Λ` with `t ≤ 0`.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Section 2.2 (the Cramér–Chernoff method).
-/

public section

open MeasureTheory ProbabilityTheory Real Finset

namespace LMLExplore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} {Λ Λ' : Set ℝ}

/-- A real random variable `X` under `P` is *dominated* by `Y` under `Q` on the set of parameters
`Λ` if `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` in `[0, ∞]` for every `t ∈ Λ`: wherever `exp (t Y)` is
`Q`-integrable, `exp (t X)` is `P`-integrable and `mgf X P t ≤ mgf Y Q t`. -/
structure MGFDominatedOn (X : Ω → ℝ) (P : Measure Ω) (Y : Ω' → ℝ) (Q : Measure Ω') (Λ : Set ℝ) :
    Prop where
  integrable_exp_mul ⦃t : ℝ⦄ (ht : t ∈ Λ) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * X ω)) P
  mgf_le ⦃t : ℝ⦄ (ht : t ∈ Λ) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    mgf X P t ≤ mgf Y Q t

/-- Domination on `Λ` implies domination on every subset of `Λ`. -/
lemma MGFDominatedOn.mono (h : MGFDominatedOn X P Y Q Λ) (hΛ : Λ' ⊆ Λ) :
    MGFDominatedOn X P Y Q Λ' where
  integrable_exp_mul _ ht hY := h.integrable_exp_mul (hΛ ht) hY
  mgf_le _ ht hY := h.mgf_le (hΛ ht) hY

/-- If `X` is dominated by `Y` on `Λ` and the parameters of `Λ` at which `exp (t Y)` is
`Q`-integrable form a neighbourhood of `0`, then `X` has exponential moments near `0`, hence is
`P`-integrable. -/
lemma MGFDominatedOn.integrable (h : MGFDominatedOn X P Y Q Λ)
    (h0 : 0 ∈ interior (Λ ∩ integrableExpSet Y Q)) : Integrable X P :=
  integrable_of_mem_interior_integrableExpSet
    (interior_mono (fun _ (ht : _ ∈ Λ ∩ _) ↦ h.integrable_exp_mul ht.1 ht.2) h0)

/-- Domination on `Λ ∪ Λ'` is domination on both `Λ` and `Λ'`. -/
lemma mgfDominatedOn_union :
    MGFDominatedOn X P Y Q (Λ ∪ Λ') ↔ MGFDominatedOn X P Y Q Λ ∧ MGFDominatedOn X P Y Q Λ' where
  mp h := ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩
  mpr h :=
    { integrable_exp_mul _ ht hY :=
        ht.elim (h.1.integrable_exp_mul · hY) (h.2.integrable_exp_mul · hY)
      mgf_le _ ht hY := ht.elim (h.1.mgf_le · hY) (h.2.mgf_le · hY) }

/-- Domination on `Λ` and on `Λ'` gives domination on `Λ ∪ Λ'`. -/
lemma MGFDominatedOn.union (h : MGFDominatedOn X P Y Q Λ) (h' : MGFDominatedOn X P Y Q Λ') :
    MGFDominatedOn X P Y Q (Λ ∪ Λ') :=
  mgfDominatedOn_union.2 ⟨h, h'⟩

/-- Domination on `Set.Iic 0` and on `Set.Ici 0` gives domination on `Set.univ`. -/
lemma MGFDominatedOn.univ_of_Iic_of_Ici (h : MGFDominatedOn X P Y Q (Set.Iic 0))
    (h' : MGFDominatedOn X P Y Q (Set.Ici 0)) : MGFDominatedOn X P Y Q Set.univ :=
  (h.union h').mono Set.Iic_union_Ici.ge

/-- If `X` is dominated by `Y` on `Λ`, then `-X` is dominated by `-Y` on `-Λ`. -/
lemma MGFDominatedOn.neg (h : MGFDominatedOn X P Y Q Λ) :
    MGFDominatedOn (fun ω ↦ -X ω) P (fun ω ↦ -Y ω) Q (-Λ) where
  integrable_exp_mul t ht hY := by
    simpa only [mul_neg, neg_mul] using
      h.integrable_exp_mul (Set.mem_neg.1 ht) (by simpa only [mul_neg, neg_mul] using hY)
  mgf_le t ht hY := by
    simpa only [mgf, mul_neg, neg_mul] using
      h.mgf_le (Set.mem_neg.1 ht) (by simpa only [mul_neg, neg_mul] using hY)

section Trans

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {R : Measure Ω''} {Z : Ω'' → ℝ}

/-- Domination on `Λ` is transitive. -/
lemma MGFDominatedOn.trans (hXY : MGFDominatedOn X P Y Q Λ) (hYZ : MGFDominatedOn Y Q Z R Λ) :
    MGFDominatedOn X P Z R Λ where
  integrable_exp_mul _ ht hZ := hXY.integrable_exp_mul ht (hYZ.integrable_exp_mul ht hZ)
  mgf_le _ ht hZ := (hXY.mgf_le ht (hYZ.integrable_exp_mul ht hZ)).trans (hYZ.mgf_le ht hZ)

end Trans

end LMLExplore

namespace ProbabilityTheory

open LMLExplore

variable {Ω Ω' ι : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {X : ι → Ω → ℝ} {Y : Ω' → ℝ} {s : Finset ι} {t : ℝ} {Λ : Set ℝ}

/-- A random variable is dominated on every set by every random variable with the same law. -/
lemma IdentDistrib.mgfDominatedOn {X : Ω → ℝ} (h : IdentDistrib X Y P Q) :
    MGFDominatedOn X P Y Q Λ where
  integrable_exp_mul t _ := (h.comp (u := fun x ↦ exp (t * x)) (by fun_prop)).integrable_iff.2
  mgf_le t _ _ := (mgf_congr_of_identDistrib X Y h t).le

/-- For independent random variables `X i`, `i ∈ s`, dominated by `Y` under `Q` on `Λ`, and
`t ∈ Λ` with `exp (t Y)` integrable, the sum `∑ i ∈ s, X i` has an exponential moment of
order `t` and `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`. -/
private lemma iIndepFun.integrable_exp_mul_sum_and_mgf_sum_le_pow
    (h_indep : iIndepFun X P) (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (ht : t ∈ Λ)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) P ∧
      mgf (fun ω ↦ ∑ i ∈ s, X i ω) P t ≤ mgf Y Q t ^ #s := by
  have := h_indep.isProbabilityMeasure
  rcases eq_or_ne t 0 with rfl | ht0
  · -- at `t = 0`, both sides are total masses
    refine ⟨by simp, ?_⟩
    rw [mgf_zero]
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · exact one_le_pow₀ ((mgf_zero (X := X i) (μ := P)).symm.trans_le ((hX i hi).mgf_le ht hY))
  -- for `t ≠ 0`, the exponential moments make the `X i` almost everywhere measurable
  have h_int (i : ι) (hi : i ∈ s) := (hX i hi).integrable_exp_mul ht hY
  have h_meas (i : ι) (hi : i ∈ s) : AEMeasurable (X i) P :=
    aemeasurable_of_aemeasurable_exp_mul ht0 (h_int i hi).aemeasurable
  refine ⟨h_indep.integrable_exp_mul_sum_of_aemeasurable h_meas h_int, ?_⟩
  rw [h_indep.mgf_sum_of_aemeasurable h_meas]
  calc ∏ i ∈ s, mgf (X i) P t ≤ ∏ _i ∈ s, mgf Y Q t :=
        prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) fun i hi ↦ (hX i hi).mgf_le ht hY
    _ = mgf Y Q t ^ #s := by simp

/-- For independent random variables `X i`, `i ∈ s`, dominated by `Y` under `Q` on `Λ`, and
`t ∈ Λ` with `exp (t Y)` integrable, the sum `∑ i ∈ s, X i` has an exponential moment of
order `t`. -/
theorem iIndepFun.integrable_exp_mul_sum_of_mgfDominatedOn (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (ht : t ∈ Λ)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) P :=
  (h_indep.integrable_exp_mul_sum_and_mgf_sum_le_pow hX ht hY).1

/-- For independent random variables `X i`, `i ∈ s`, dominated by `Y` under `Q` on `Λ`, and
`t ∈ Λ` with `exp (t Y)` integrable, `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.mgf_sum_le_pow_of_mgfDominatedOn (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (ht : t ∈ Λ)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) P t ≤ mgf Y Q t ^ #s :=
  (h_indep.integrable_exp_mul_sum_and_mgf_sum_le_pow hX ht hY).2

/-- **Chernoff bound under domination, upper tail.** For independent random variables `X i`,
`i ∈ s`, dominated by `Y` under `Q` on `Λ`, every threshold `a` and every `t ∈ Λ` with `t ≥ 0`
and `exp (t Y)` integrable, `P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_mul_mgf_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (a : ℝ) (htΛ : t ∈ Λ) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | a ≤ ∑ i ∈ s, X i ω} ≤ exp (-t * a) * mgf Y Q t ^ #s := by
  have := h_indep.isProbabilityMeasure
  exact (measure_ge_le_exp_mul_mgf a ht
    (h_indep.integrable_exp_mul_sum_of_mgfDominatedOn hX htΛ hY)).trans
    (mul_le_mul_of_nonneg_left (h_indep.mgf_sum_le_pow_of_mgfDominatedOn hX htΛ hY)
      (exp_pos _).le)

/-- **Chernoff bound under domination, lower tail.** For independent random variables `X i`,
`i ∈ s`, dominated by `Y` under `Q` on `Λ`, every threshold `a` and every `t ∈ Λ` with `t ≤ 0`
and `exp (t Y)` integrable, `P(∑ i ∈ s, X i ≤ a) ≤ exp (-t a) (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_mul_mgf_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (a : ℝ) (htΛ : t ∈ Λ) (ht : t ≤ 0)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ a} ≤ exp (-t * a) * mgf Y Q t ^ #s := by
  have := h_indep.isProbabilityMeasure
  exact (measure_le_le_exp_mul_mgf a ht
    (h_indep.integrable_exp_mul_sum_of_mgfDominatedOn hX htΛ hY)).trans
    (mul_le_mul_of_nonneg_left (h_indep.mgf_sum_le_pow_of_mgfDominatedOn hX htΛ hY)
      (exp_pos _).le)

/-- The bound `exp (-t (#s x)) (mgf Y Q t) ^ #s` of the Chernoff bounds is at most
`exp (-(#s (t x - cgf Y Q t)))`. -/
private lemma exp_mul_mgf_pow_le_exp_cgf (s : Finset ι) (x t : ℝ) :
    exp (-t * (#s * x)) * mgf Y Q t ^ #s ≤ exp (-(#s * (t * x - cgf Y Q t))) := by
  calc exp (-t * (#s * x)) * mgf Y Q t ^ #s
      ≤ exp (-t * (#s * x)) * exp (cgf Y Q t) ^ #s := by
        gcongr
        · exact mgf_nonneg
        · exact le_exp_log _
    _ = exp (-(#s * (t * x - cgf Y Q t))) := by
        rw [← exp_nat_mul, ← exp_add]
        ring_nf

/-- **Chernoff bound under domination in cgf form, upper tail.** For independent random variables
`X i`, `i ∈ s`, dominated by `Y` under `Q` on `Λ`, every level `x` and every `t ∈ Λ` with `t ≥ 0`
and `exp (t Y)` integrable, `P(#s x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s (t x - cgf Y Q t)))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_mul_sub_cgf (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (x : ℝ) (htΛ : t ∈ Λ) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * (t * x - cgf Y Q t))) :=
  (h_indep.measureReal_sum_ge_le_exp_mul_mgf_pow hX _ htΛ ht hY).trans
    (exp_mul_mgf_pow_le_exp_cgf s x t)

/-- **Chernoff bound under domination in cgf form, lower tail.** For independent random variables
`X i`, `i ∈ s`, dominated by `Y` under `Q` on `Λ`, every level `x` and every `t ∈ Λ` with `t ≤ 0`
and `exp (t Y)` integrable, `P(∑ i ∈ s, X i ≤ #s x) ≤ exp (-(#s (t x - cgf Y Q t)))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_mul_sub_cgf (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Λ) (x : ℝ) (htΛ : t ∈ Λ) (ht : t ≤ 0)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ #s * x} ≤ exp (-(#s * (t * x - cgf Y Q t))) :=
  (h_indep.measureReal_sum_le_le_exp_mul_mgf_pow hX _ htΛ ht hY).trans
    (exp_mul_mgf_pow_le_exp_cgf s x t)

end ProbabilityTheory
