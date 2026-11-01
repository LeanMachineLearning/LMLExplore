/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic

/-!
# Domination of moment generating functions and Chernoff bounds

A real random variable `X` under a measure `P` is *dominated above* by a real random variable `Y`
under a measure `Q` if `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` for every `t ≥ 0`, as an inequality in
`[0, ∞]`: at each `t ≥ 0` where `exp (t Y)` is `Q`-integrable, `exp (t X)` is `P`-integrable and
`mgf X P t ≤ mgf Y Q t`. It is *dominated below* if the same holds for every `t ≤ 0`. For example,
a random variable with values in `[0, 1]` and mean at most `m` is dominated above by the Bernoulli
law of mean `m`, and identically distributed random variables dominate each other.

The Chernoff bound transfers through the domination: the sum `∑ i ∈ s, X i` of independent random
variables dominated above by `Y` satisfies, for `t ≥ 0`,
`P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s`, the Chernoff bound of a sum of `#s`
independent copies of `Y`; symmetrically for the lower tail. With `Y` the statistic of an
exponential family, this gives Cramér–Chernoff bounds for random variables that are dominated by a
member of the family without following its law.

## Main definitions

* `LMLExplore.MGFDominatedAbove X P Y Q`: `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` for every `t ≥ 0`.
* `LMLExplore.MGFDominatedBelow X P Y Q`: `E_P[exp (t X)] ≤ E_Q[exp (t Y)]` for every `t ≤ 0`.

## Main statements

* `ProbabilityTheory.IdentDistrib.mgfDominatedAbove`,
  `ProbabilityTheory.IdentDistrib.mgfDominatedBelow`: identically distributed random variables
  dominate each other.
* `ProbabilityTheory.iIndepFun.mgf_sum_le_pow`: for independent `X i` dominated above by `Y` and
  `t ≥ 0` with `exp (t Y)` integrable, `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`.
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_mul_mgf_pow`,
  `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_mul_mgf_pow`: the Chernoff bounds
  `P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s` for `t ≥ 0` and variables dominated above,
  and `P(∑ i ∈ s, X i ≤ a) ≤ exp (-t a) (mgf Y Q t) ^ #s` for `t ≤ 0` and variables dominated
  below.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Section 2.2 (the Cramér–Chernoff method).
-/

public section

open MeasureTheory ProbabilityTheory Real Finset

namespace LMLExplore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

/-- A real random variable `X` under `P` is *dominated above* by `Y` under `Q` if
`E_P[exp (t X)] ≤ E_Q[exp (t Y)]` in `[0, ∞]` for every `t ≥ 0`: wherever `exp (t Y)` is
`Q`-integrable, `exp (t X)` is `P`-integrable and `mgf X P t ≤ mgf Y Q t`. -/
structure MGFDominatedAbove (X : Ω → ℝ) (P : Measure Ω) (Y : Ω' → ℝ) (Q : Measure Ω') :
    Prop where
  integrable_exp_mul ⦃t : ℝ⦄ (ht : 0 ≤ t) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * X ω)) P
  mgf_le ⦃t : ℝ⦄ (ht : 0 ≤ t) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    mgf X P t ≤ mgf Y Q t

/-- A real random variable `X` under `P` is *dominated below* by `Y` under `Q` if
`E_P[exp (t X)] ≤ E_Q[exp (t Y)]` in `[0, ∞]` for every `t ≤ 0`: wherever `exp (t Y)` is
`Q`-integrable, `exp (t X)` is `P`-integrable and `mgf X P t ≤ mgf Y Q t`. -/
structure MGFDominatedBelow (X : Ω → ℝ) (P : Measure Ω) (Y : Ω' → ℝ) (Q : Measure Ω') :
    Prop where
  integrable_exp_mul ⦃t : ℝ⦄ (ht : t ≤ 0) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * X ω)) P
  mgf_le ⦃t : ℝ⦄ (ht : t ≤ 0) (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    mgf X P t ≤ mgf Y Q t

/-- If `X` is dominated below by `Y`, then `-X` is dominated above by `-Y`. -/
lemma MGFDominatedBelow.neg (h : MGFDominatedBelow X P Y Q) :
    MGFDominatedAbove (fun ω ↦ -X ω) P (fun ω ↦ -Y ω) Q where
  integrable_exp_mul t ht hY := by
    simpa only [mul_neg, neg_mul] using
      h.integrable_exp_mul (neg_nonpos.2 ht) (by simpa only [mul_neg, neg_mul] using hY)
  mgf_le t ht hY := by
    simpa only [mgf, mul_neg, neg_mul] using
      h.mgf_le (neg_nonpos.2 ht) (by simpa only [mul_neg, neg_mul] using hY)

end LMLExplore

namespace ProbabilityTheory

open LMLExplore

variable {Ω Ω' ι : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {X : ι → Ω → ℝ} {Y : Ω' → ℝ} {s : Finset ι} {t : ℝ}

/-- Moment generating functions of identically distributed random variables agree, and so do
their exponential moments. -/
private lemma IdentDistrib.integrable_exp_mul_and_mgf_eq {X : Ω → ℝ} (h : IdentDistrib X Y P Q)
    (t : ℝ) :
    (Integrable (fun ω ↦ exp (t * Y ω)) Q → Integrable (fun ω ↦ exp (t * X ω)) P) ∧
      mgf X P t = mgf Y Q t := by
  have h' := h.comp (u := fun x ↦ exp (t * x)) (by fun_prop)
  exact ⟨h'.integrable_iff.2, mgf_congr_of_identDistrib X Y h t⟩

/-- A random variable is dominated above by every random variable with the same law. -/
lemma IdentDistrib.mgfDominatedAbove {X : Ω → ℝ} (h : IdentDistrib X Y P Q) :
    MGFDominatedAbove X P Y Q :=
  ⟨fun t _ ↦ (h.integrable_exp_mul_and_mgf_eq t).1,
    fun t _ _ ↦ (h.integrable_exp_mul_and_mgf_eq t).2.le⟩

/-- A random variable is dominated below by every random variable with the same law. -/
lemma IdentDistrib.mgfDominatedBelow {X : Ω → ℝ} (h : IdentDistrib X Y P Q) :
    MGFDominatedBelow X P Y Q :=
  ⟨fun t _ ↦ (h.integrable_exp_mul_and_mgf_eq t).1,
    fun t _ _ ↦ (h.integrable_exp_mul_and_mgf_eq t).2.le⟩

/-- For independent random variables `X i`, `i ∈ s`, dominated above by `Y` under `Q`, and
`t ≥ 0` with `exp (t Y)` integrable, the sum `∑ i ∈ s, X i` has an exponential moment of
order `t` and `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`. -/
private lemma iIndepFun.integrable_exp_mul_sum_and_mgf_sum_le_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedAbove (X i) P Y Q) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) P ∧
      mgf (fun ω ↦ ∑ i ∈ s, X i ω) P t ≤ mgf Y Q t ^ #s := by
  have := h_indep.isProbabilityMeasure
  rcases ht.eq_or_lt with rfl | ht
  · -- at `t = 0`, both sides are total masses
    refine ⟨by simp, ?_⟩
    rw [mgf_zero]
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · exact one_le_pow₀ ((mgf_zero (X := X i) (μ := P)).symm.trans_le ((hX i hi).mgf_le le_rfl hY))
  -- for `t > 0`, the exponential moments make the `X i` almost everywhere measurable
  have h_meas (i : s) : AEMeasurable (X i) P :=
    aemeasurable_of_aemeasurable_exp_mul ht.ne'
      ((hX i i.2).integrable_exp_mul ht.le hY).aemeasurable
  have h_indep' : iIndepFun (fun i : s ↦ X i) P := h_indep.precomp Subtype.val_injective
  have h_sum : mgf (fun ω ↦ ∑ i ∈ s, X i ω) P t = ∏ i : s, mgf (X i) P t := by
    rw [← h_indep'.mgf_sum₀ h_meas univ]
    congr with ω
    rw [Finset.sum_apply, Finset.sum_coe_sort s fun i ↦ X i ω]
  refine ⟨mgf_pos_iff.1 ?_, ?_⟩
  · rw [h_sum]
    exact Finset.prod_pos fun i _ ↦ mgf_pos ((hX i i.2).integrable_exp_mul ht.le hY)
  · rw [h_sum]
    calc ∏ i : s, mgf (X i) P t ≤ ∏ _i : s, mgf Y Q t :=
          prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) fun i _ ↦ (hX i i.2).mgf_le ht.le hY
      _ = mgf Y Q t ^ #s := by simp

/-- For independent random variables `X i`, `i ∈ s`, dominated above by `Y` under `Q`, and
`t ≥ 0` with `exp (t Y)` integrable, the sum `∑ i ∈ s, X i` has an exponential moment of
order `t`. -/
theorem iIndepFun.integrable_exp_mul_sum_of_mgfDominatedAbove (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedAbove (X i) P Y Q) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) P :=
  (h_indep.integrable_exp_mul_sum_and_mgf_sum_le_pow hX ht hY).1

/-- For independent random variables `X i`, `i ∈ s`, dominated above by `Y` under `Q`, and
`t ≥ 0` with `exp (t Y)` integrable, `mgf (∑ i ∈ s, X i) P t ≤ (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.mgf_sum_le_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedAbove (X i) P Y Q) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) P t ≤ mgf Y Q t ^ #s :=
  (h_indep.integrable_exp_mul_sum_and_mgf_sum_le_pow hX ht hY).2

/-- **Chernoff bound under domination, upper tail.** For independent random variables `X i`,
`i ∈ s`, dominated above by `Y` under `Q`, every threshold `a` and every `t ≥ 0` with
`exp (t Y)` integrable, `P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_mul_mgf_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedAbove (X i) P Y Q) (a : ℝ) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | a ≤ ∑ i ∈ s, X i ω} ≤ exp (-t * a) * mgf Y Q t ^ #s := by
  have := h_indep.isProbabilityMeasure
  exact (measure_ge_le_exp_mul_mgf a ht
    (h_indep.integrable_exp_mul_sum_of_mgfDominatedAbove hX ht hY)).trans
    (mul_le_mul_of_nonneg_left (h_indep.mgf_sum_le_pow hX ht hY) (exp_pos _).le)

/-- **Chernoff bound under domination, lower tail.** For independent random variables `X i`,
`i ∈ s`, dominated below by `Y` under `Q`, every threshold `a` and every `t ≤ 0` with
`exp (t Y)` integrable, `P(∑ i ∈ s, X i ≤ a) ≤ exp (-t a) (mgf Y Q t) ^ #s`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_mul_mgf_pow (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedBelow (X i) P Y Q) (a : ℝ) (ht : t ≤ 0)
    (hY : Integrable (fun ω ↦ exp (t * Y ω)) Q) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ a} ≤ exp (-t * a) * mgf Y Q t ^ #s := by
  -- apply the upper tail to `-X i`, dominated above by `-Y`, at `-t ≥ 0`
  have h_indep' : iIndepFun (fun i ω ↦ -X i ω) P :=
    h_indep.comp (fun _ x ↦ -x) fun _ ↦ measurable_neg
  have h := h_indep'.measureReal_sum_ge_le_exp_mul_mgf_pow (fun i hi ↦ (hX i hi).neg) (-a)
    (neg_nonneg.2 ht) (Y := fun ω ↦ -Y ω) (by simpa only [neg_mul_neg] using hY)
  have h_mgf : mgf (fun ω ↦ -Y ω) Q (-t) = mgf Y Q t := by simp only [mgf, neg_mul_neg]
  rw [h_mgf, neg_mul_neg] at h
  refine le_of_eq_of_le ?_ h
  congr 1 with ω
  simp [Finset.sum_neg_distrib]

end ProbabilityTheory
