/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.EVariable
public import TauCeti.Probability.Exchangeability.Family
import Mathlib.Data.Fintype.Perm
import LMLExplore.Algebra.BigOperators.Perm
import LMLExplore.Basic.ENNReal.BigOperators
import LMLExplore.EValues.ConstraintNull.CompleteClass
public import LMLExplore.EValues.Merging

/-!
# Merging functions for exchangeable e-values

A merging function for exchangeable e-values indexed by `ι` is a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every probability measure `μ` on `ι → ℝ≥0∞`
that is invariant under the permutations of the coordinates and whose coordinates have expectation
at most `1`. It turns e-variables that form an exchangeable family under every member of the null
into an e-variable (`ProbabilityTheory.IsExchangeableEMerging.isEVar_comp`). No monotonicity is
assumed. Equivalently, these functions are the e-variables of the merging null of the
exchangeable laws `ProbabilityTheory.exchangeableLaws`, the measures invariant under the
permutations of the coordinates (`ProbabilityTheory.isExchangeableEMerging_iff_isEVar_mergingNull`);
so every e-merging function is one.

For finite `ι`, a measurable `F` is a merging function for exchangeable e-values exactly when its
symmetrization, the average of `F` over the orderings of its arguments, is at most a convex
combination `(1 - l) + l * mean` of `1` and the arithmetic mean, at every point with finite
coordinates.

The exchangeable Markov inequality of Ramdas and Manole [RM26] says that
`β * 𝟙{some running mean reaches β}` is such a function, where the running means are the means of
the first `k + 1` e-values. Wang asks whether it is admissible [Wan25, Section 4 (d)]. It is not:
its maximum with the smallest e-value is a monotone merging function for exchangeable e-values,
which dominates it and differs from it.

## Main definitions

* `ProbabilityTheory.exchangeableLaws`: the measures on `ι → α` invariant under the permutations
  of the coordinates.
* `ProbabilityTheory.IsExchangeableEMerging F`: `F` is a merging function for exchangeable
  e-values.
* `ProbabilityTheory.RunningMeanReaches β e`: some running mean of the `K` e-values `e` reaches
  `β`.
* `ProbabilityTheory.runningMeanTest β`: the function `β * 𝟙{some running mean reaches β}` of
  `K` e-values.

## Main statements

* `ProbabilityTheory.isExchangeableEMerging_iff_isEVar_mergingNull`: the merging functions for
  exchangeable e-values are the e-variables of the merging null of the exchangeable laws, and
  `ProbabilityTheory.IsEMerging.isExchangeableEMerging`: e-merging functions are among them.
* `ProbabilityTheory.IsExchangeableEMerging.isEVar_comp`: a merging function for exchangeable
  e-values of an exchangeable family of e-variables is an e-variable.
* `ProbabilityTheory.isExchangeableEMerging_iff`: the characterization by the symmetrization.
* `ProbabilityTheory.isExchangeableEMerging_runningMeanTest`: the exchangeable Markov inequality
  [RM26].
* `ProbabilityTheory.exists_isExchangeableEMerging_monotone_runningMeanTest_lt`: the function of
  the exchangeable Markov inequality is not admissible.

## Implementation notes

The direction "merging implies the bound" of `isExchangeableEMerging_iff` applies the complete
class theorem in finite-dimensional form
(`ProbabilityTheory.exists_mem_nonredundantWeights_le_of_noArbitrageOn`) on the space `ι → ℝ≥0` of
finite values, to the symmetrization minus `1` and the single constraint `e ↦ mean e - 1`, as for
e-merging functions [Cle26b, closing remark]. Its hypothesis holds because a finite mixture of the
uniform laws on orbits is an exchangeable law, against which `F` integrates to the same mixture of
the symmetrizations and the coordinates to the same mixture of the means; the constant `l` is the
weight of the constraint.

The exchangeable Markov inequality is proved in its orbit form: among the orderings of a point for
which some running mean reaches `β`, the sum of the first coordinates is at least `β` times their
number. The proof splits these orderings according to the last prefix whose mean reaches `β`, an
event that is invariant under the permutations of that prefix.

The characterization and the non-admissibility have no published source other than
[EVR26, Note 09]. The statements and proofs are adapted from the formalization in the paper
project `RemyDegenne/evalues_research` (same author), files
`EValuesResearch/ForLMLExplore/EValues/ExchangeableMerging.lean` (statements, commit `9c51e1d`) and
`EValuesResearch/Results/ExchangeableMerging.lean` (proofs, commit `af4950b`).

## References

* [RM26] A. Ramdas and T. Manole, *Randomized and exchangeable improvements of Markov's,
  Chebyshev's and Chernoff's inequalities*, Statist. Sci. 41 (2026), arXiv:2304.02611v3.
* [Wan25] R. Wang, *The only admissible way of merging arbitrary e-values*, Biometrika (2025),
  arXiv:2409.19888v2: Section 4 (d).
* [Cle26b] E. Clerico, *Sequential testing of conditionally constrained hypotheses*,
  arXiv:2606.06769v2: closing remark.
* [LRR26] M. Larsson, A. Ramdas and J. Ruf, *Testing hypotheses generated by constraints*, Math.
  Oper. Res. (2026), arXiv:2504.02974v5: Theorem 3.1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026: Note 09.
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### The exchangeable laws -/

section ExchangeableLaws

variable {ι α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {μ : Measure (ι → α)}

/-- The **exchangeable laws** on `ι → α`: the measures invariant under the permutations of the
coordinates, the joint laws of exchangeable families
(`TauCeti.Probability.ExchangeableFamily.map_mem_exchangeableLaws`). Their merging null is the null
of the joint laws of exchangeable e-values. -/
def exchangeableLaws : Set (Measure (ι → α)) :=
  {μ | ∀ σ : Equiv.Perm ι, μ.map (fun e i ↦ e (σ i)) = μ}

@[simp]
theorem mem_exchangeableLaws :
    μ ∈ exchangeableLaws ↔ ∀ σ : Equiv.Perm ι, μ.map (fun e i ↦ e (σ i)) = μ :=
  Iff.rfl

/-- The joint law of an exchangeable family of almost everywhere measurable random variables,
indexed by a countable type, under a finite measure is an exchangeable law. -/
theorem _root_.TauCeti.Probability.ExchangeableFamily.map_mem_exchangeableLaws [Countable ι]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → α} (h : ExchangeableFamily P X)
    (hX : ∀ i, AEMeasurable (X i) P) : P.map (fun ω i ↦ X i ω) ∈ exchangeableLaws := fun σ ↦ by
  have hσ : Measurable fun (e : ι → α) i ↦ e (σ i) := by fun_prop
  rw [AEMeasurable.map_map_of_aemeasurable hσ.aemeasurable (AEMeasurable.of_eval hX)]
  exact h.map_eq_of_injective hX σ.injective Function.injective_id

end ExchangeableLaws

/-! ### Merging functions for exchangeable e-values -/

section Definition

variable {ι : Type*} {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A **merging function for exchangeable e-values** indexed by `ι`: a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every probability measure `μ` on
`ι → ℝ≥0∞` that is invariant under the permutations of the coordinates and whose coordinates have
expectation at most `1`. It is not required to be monotone. -/
structure IsExchangeableEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : Measure (ι → ℝ≥0∞)) [IsProbabilityMeasure μ],
    (∀ σ : Equiv.Perm ι, μ.map (fun e i ↦ e (σ i)) = μ) → (∀ i, ∫⁻ e, e i ∂μ ≤ 1) →
    ∫⁻ e, F e ∂μ ≤ 1

/-- **Merging functions for exchangeable e-values are the e-variables of the merging null of the
exchangeable laws**: they are the bets on the space of values against the joint laws of
exchangeable e-values. -/
theorem isExchangeableEMerging_iff_isEVar_mergingNull :
    IsExchangeableEMerging F ↔ IsEVar F (mergingNull exchangeableLaws) :=
  ⟨fun hF ↦ ⟨hF.measurable, fun μ hμ ↦ have := isProbabilityMeasure_of_mem_mergingNull hμ;
      hF.lintegral_le_one μ (mem_mergingNull.1 hμ).1 (mem_mergingNull.1 hμ).2.2⟩,
    fun hF ↦ ⟨hF.measurable, fun μ _ hσ hμ ↦ hF.lintegral_le_one (mem_mergingNull.2 ⟨hσ, ‹_›, hμ⟩)⟩⟩

/-- An e-merging function is a merging function for exchangeable e-values. -/
theorem IsEMerging.isExchangeableEMerging (hF : IsEMerging F) : IsExchangeableEMerging F :=
  isExchangeableEMerging_iff_isEVar_mergingNull.2 (hF.isEVar_mergingNull _)

/-- A measurable function below a merging function for exchangeable e-values is one. -/
theorem IsExchangeableEMerging.of_le (hG : IsExchangeableEMerging G) (hF : Measurable F)
    (hle : F ≤ G) : IsExchangeableEMerging F :=
  isExchangeableEMerging_iff_isEVar_mergingNull.2
    ((isExchangeableEMerging_iff_isEVar_mergingNull.1 hG).mono hF hle)

/-- A constant at most one is a merging function for exchangeable e-values. -/
theorem isExchangeableEMerging_const {c : ℝ≥0∞} (hc : c ≤ 1) :
    IsExchangeableEMerging fun _ : ι → ℝ≥0∞ ↦ c :=
  ⟨measurable_const, fun μ _ _ _ ↦ by simpa using hc⟩

/-- A merging function for exchangeable e-values, applied to e-variables that form an exchangeable
family under every member of the null, is an e-variable. -/
theorem IsExchangeableEMerging.isEVar_comp [Countable ι] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : Set (Measure Ω)} (hF : IsExchangeableEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ι → Ω → ℝ≥0∞} (hE : ∀ i, IsEVar (E i) S) (hexch : ∀ P ∈ S, ExchangeableFamily P E) :
    IsEVar (fun ω ↦ F fun i ↦ E i ω) S :=
  (isExchangeableEMerging_iff_isEVar_mergingNull.1 hF).comp_isEVar hS hE fun P hP ↦
    have := hS P hP
    (hexch P hP).map_mem_exchangeableLaws fun i ↦ (hE i).measurable.aemeasurable

end Definition

/-! ### The characterization by the symmetrization -/

section Characterization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform law on the orbit of `E` under the permutations of the coordinates. -/
private noncomputable def orbitMeasure (E : ι → ℝ≥0∞) : Measure (ι → ℝ≥0∞) :=
  (Fintype.card (Equiv.Perm ι) : ℝ≥0∞)⁻¹ • ∑ σ : Equiv.Perm ι, Measure.dirac fun i ↦ E (σ i)

/-- The integral against the uniform law on an orbit is the average over the orbit. -/
private lemma lintegral_orbitMeasure (E : ι → ℝ≥0∞) (g : (ι → ℝ≥0∞) → ℝ≥0∞) :
    ∫⁻ x, g x ∂orbitMeasure E =
      (∑ σ : Equiv.Perm ι, g fun i ↦ E (σ i)) / Fintype.card (Equiv.Perm ι) := by
  simp only [orbitMeasure, lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac,
    smul_eq_mul]
  rw [ENNReal.div_eq_inv_mul]

/-- The uniform law on an orbit is a probability measure. -/
private lemma orbitMeasure_univ (E : ι → ℝ≥0∞) : orbitMeasure E Set.univ = 1 := by
  rw [← lintegral_one, lintegral_orbitMeasure E fun _ ↦ 1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by simp)

/-- The uniform law on an orbit is invariant under the permutations of the coordinates. -/
private lemma map_orbitMeasure (E : ι → ℝ≥0∞) (τ : Equiv.Perm ι) :
    (orbitMeasure E).map (fun e i ↦ e (τ i)) = orbitMeasure E := by
  have hτ : Measurable fun (e : ι → ℝ≥0∞) i ↦ e (τ i) := by fun_prop
  rw [orbitMeasure, Measure.map_smul _ hτ.aemeasurable, Measure.map_finset_sum' hτ.aemeasurable]
  simp_rw [Measure.map_dirac]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ ↦ by simp

/-- The coordinate means of the uniform law on the orbit of `E` are the mean of `E`. -/
private lemma lintegral_apply_orbitMeasure (E : ι → ℝ≥0∞) (i : ι) :
    ∫⁻ x, x i ∂orbitMeasure E = (∑ j, E j) / Fintype.card ι := by
  rw [lintegral_orbitMeasure E fun x ↦ x i]
  exact ENNReal.sum_perm_apply_div_card E i

/-- The **mixtures of the uniform laws on orbits** are exchangeable laws: invariant under the
permutations of the coordinates. -/
private lemma sum_smul_orbitMeasure_mem_exchangeableLaws {α : Type*} [Fintype α] (w : α → ℝ≥0∞)
    (x : α → ι → ℝ≥0∞) : ∑ k, w k • orbitMeasure (x k) ∈ exchangeableLaws := fun τ ↦ by
  have hτ : Measurable fun (e : ι → ℝ≥0∞) i ↦ e (τ i) := by fun_prop
  rw [Measure.map_finset_sum' hτ.aemeasurable]
  simp_rw [Measure.map_smul _ hτ.aemeasurable, map_orbitMeasure]

/-- If `F` is a merging function for exchangeable e-values, then for every finite mixture with
weights `w k` of the uniform laws on the orbits of points `x k`, whose coordinate means are at
most one, the corresponding mixture of the symmetrizations of `F` at the `x k` is at most one. -/
private lemma sum_mul_sum_perm_div_le_one {F : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) {α : Type*} [Fintype α] {w : α → ℝ≥0∞} (x : α → ι → ℝ≥0∞)
    (hw : ∑ k, w k = 1) (h : ∑ k, w k * ((∑ i, x k i) / Fintype.card ι) ≤ 1) :
    ∑ k, w k * ((∑ σ : Equiv.Perm ι, F fun i ↦ x k (σ i)) / Fintype.card (Equiv.Perm ι)) ≤ 1 := by
  have hprob : IsProbabilityMeasure (∑ k, w k • orbitMeasure (x k)) :=
    ⟨by simp [orbitMeasure_univ, hw]⟩
  have := hF.lintegral_le_one (∑ k, w k • orbitMeasure (x k))
    (sum_smul_orbitMeasure_mem_exchangeableLaws w x)
    (fun i ↦ by simpa [lintegral_finsetSum_measure, lintegral_apply_orbitMeasure] using h)
  simpa [lintegral_finsetSum_measure, lintegral_orbitMeasure] using this

omit [DecidableEq ι] in
/-- The mean of finite values is finite. -/
private lemma sum_coe_div_card_ne_top (e : ι → ℝ≥0) :
    (∑ i, (e i : ℝ≥0∞)) / Fintype.card ι ≠ ⊤ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · exact ENNReal.div_ne_top (by simp) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The symmetrization of a merging function for exchangeable e-values is finite at every point
with finite coordinates: mix the uniform law on the orbit of the point with the Dirac mass at
`0`. -/
private lemma IsExchangeableEMerging.sum_perm_div_ne_top {F : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) (e : ι → ℝ≥0) :
    (∑ σ : Equiv.Perm ι, F fun i ↦ e (σ i)) / (Fintype.card (Equiv.Perm ι) : ℝ≥0∞) ≠ ⊤ := by
  intro htop
  have hM := sum_coe_div_card_ne_top e
  set p := ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι + 1)⁻¹
  have hp : p ≤ 1 := ENNReal.inv_le_one.mpr le_add_self
  have h := sum_mul_sum_perm_div_le_one hF (w := fun b : Bool ↦ if b then p else 1 - p)
    (fun b i ↦ if b then (e i : ℝ≥0∞) else 0) (by simp [add_tsub_cancel_of_le hp]) (by
      simp only [Fintype.sum_bool, ↓reduceIte, Finset.sum_const_zero, ENNReal.zero_div,
        mul_zero, add_zero, Bool.false_eq_true]
      calc p * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι)
          ≤ p * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι + 1) := by gcongr; exact le_self_add
        _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp [hM]))
  simp only [Fintype.sum_bool, ↓reduceIte, htop, Bool.false_eq_true] at h
  rw [ENNReal.mul_top (by simp [p, hM])] at h
  simp at h

/-- The symmetrization of a merging function for exchangeable e-values is at most
`(1 - l) + l * mean` at every point with finite coordinates, for some `l ≤ 1` [EVR26, Note 09].
It is the instance of the complete class theorem for the single constraint `e ↦ mean e - 1` on the
finite values [Cle26b, closing remark; LRR26, Theorem 3.1], as for e-merging functions
(`ProbabilityTheory.IsEMerging.exists_le_add_sum_mul`). -/
theorem IsExchangeableEMerging.exists_sum_perm_div_le {F : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) :
    ∃ l : ℝ≥0∞, l ≤ 1 ∧ ∀ e : ι → ℝ≥0,
      (∑ σ : Equiv.Perm ι, F fun i ↦ e (σ i)) / (Fintype.card (Equiv.Perm ι) : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (Fintype.card ι : ℝ≥0∞)) := by
  let M : (ι → ℝ≥0) → ℝ≥0∞ := fun e ↦ (∑ i, (e i : ℝ≥0∞)) / Fintype.card ι
  let A : (ι → ℝ≥0) → ℝ≥0∞ := fun e ↦
    (∑ σ : Equiv.Perm ι, F fun i ↦ e (σ i)) / Fintype.card (Equiv.Perm ι)
  -- the mixtures of the uniform laws on orbits give: a mean of `A` is at most one when the same
  -- mean of `M` is
  have hmix {α : Type} [Fintype α] (w : α → ℝ≥0∞) (x : α → ι → ℝ≥0) (hw : ∑ k, w k = 1)
      (h : ∑ k, w k * M (x k) ≤ 1) : ∑ k, w k * A (x k) ≤ 1 :=
    sum_mul_sum_perm_div_le_one hF (fun k i ↦ x k i) hw h
  have hM_top (e : ι → ℝ≥0) : M e ≠ ⊤ := sum_coe_div_card_ne_top e
  have hM₀ : M 0 = 0 := by simp [M]
  have hA_top (e : ι → ℝ≥0) : A e ≠ ⊤ := hF.sum_perm_div_ne_top e
  -- the complete class theorem on `ι → ℝ≥0`, for the function `e ↦ A e - 1` and the constraint
  -- `e ↦ M e - 1`, which is negative at `0` and so admits no arbitrage
  obtain ⟨π, hπ, hle⟩ := exists_mem_nonredundantWeights_le_of_noArbitrageOn
    (noArbitrageOn_of_forall_neg (a := fun (_ : Unit) (e : ι → ℝ≥0) ↦ (M e).toReal - 1)
      (Set.mem_univ 0) fun _ ↦ by simp [hM₀])
    (f := fun e ↦ (A e).toReal - 1) fun _ _ x w _ hw hwx ↦ by
      obtain ⟨hw0, hw1⟩ := LMLExplore.mem_simplex_iff.1 hw
      refine LMLExplore.sum_mul_toReal_sub_one_nonpos_of_sum_ofReal_mul_le_one hw
        (hmix (fun k ↦ ENNReal.ofReal (w k)) x ?_ ?_)
      · rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hw0 k, hw1, ENNReal.ofReal_one]
      · exact LMLExplore.sum_ofReal_mul_le_one_of_sum_mul_toReal_sub_one_nonpos hw
          (fun k ↦ hM_top (x k)) (hwx ())
  set l : ℝ := π ()
  have hl₀ : 0 ≤ l := (mem_nonredundantWeights_iff.1 hπ).1 ()
  have hbound (e : ι → ℝ≥0) : (A e).toReal ≤ 1 - l + l * (M e).toReal := by
    have := hle e (Set.mem_univ _)
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    linarith
  have hl₁ : l ≤ 1 := by
    have := (hbound 0).trans' ENNReal.toReal_nonneg
    rw [hM₀, ENNReal.toReal_zero, mul_zero, add_zero] at this
    linarith
  refine ⟨ENNReal.ofReal l, ENNReal.ofReal_le_one.mpr hl₁, fun e ↦ ?_⟩
  calc A e = ENNReal.ofReal (A e).toReal := (ENNReal.ofReal_toReal (hA_top e)).symm
    _ ≤ ENNReal.ofReal (1 - l + l * (M e).toReal) := ENNReal.ofReal_le_ofReal (hbound e)
    _ = (1 - ENNReal.ofReal l) + ENNReal.ofReal l * M e := by
      rw [ENNReal.ofReal_add (by linarith) (by positivity)]
      simp [ENNReal.ofReal_sub _ hl₀, ENNReal.ofReal_mul hl₀, hM_top e]

/-- A measurable function whose symmetrization is at most `(1 - l) + l * mean` at every point
with finite coordinates, for some `l ≤ 1`, is a merging function for exchangeable e-values
[EVR26, Note 09]. -/
theorem isExchangeableEMerging_of_sum_perm_div_le {F : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hF : Measurable F) {l : ℝ≥0∞} (hl : l ≤ 1)
    (h : ∀ e : ι → ℝ≥0,
      (∑ σ : Equiv.Perm ι, F fun i ↦ e (σ i)) / (Fintype.card (Equiv.Perm ι) : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (Fintype.card ι : ℝ≥0∞))) :
    IsExchangeableEMerging F := by
  refine ⟨hF, fun μ hμ hexch hmean ↦ ?_⟩
  have hτ : ∀ τ : Equiv.Perm ι, Measurable fun (e : ι → ℝ≥0∞) i ↦ e (τ i) := fun _ ↦ by
    fun_prop
  have hFτ : ∀ τ : Equiv.Perm ι, Measurable fun e : ι → ℝ≥0∞ ↦ F fun i ↦ e (τ i) :=
    fun τ ↦ hF.comp (hτ τ)
  have hinv : ∀ τ : Equiv.Perm ι, ∫⁻ e, F (fun i ↦ e (τ i)) ∂μ = ∫⁻ e, F e ∂μ := by
    intro τ
    rw [← lintegral_map hF (hτ τ)]
    exact congrArg (fun ν ↦ ∫⁻ e, F e ∂ν) (hexch τ)
  have hfin : ∀ᵐ e ∂μ, ∀ i, e i ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ae_lt_top (measurable_pi_apply i)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hmean i))] with e he using he.ne
  have hK : (Fintype.card (Equiv.Perm ι) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : Measurable fun e : ι → ℝ≥0∞ ↦ ∑ i, e i :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  calc ∫⁻ e, F e ∂μ
      = ∫⁻ e, (Fintype.card (Equiv.Perm ι) : ℝ≥0∞)⁻¹ *
          ∑ σ : Equiv.Perm ι, F (fun i ↦ e (σ i)) ∂μ := by
        simp [lintegral_const_mul _ (Finset.measurable_sum _ fun σ _ ↦ hFτ σ),
          lintegral_finsetSum _ fun σ _ ↦ hFτ σ, hinv, ← mul_assoc, ENNReal.inv_mul_cancel hK]
    _ ≤ ∫⁻ e, (1 - l) + l * ((∑ i, e i) * (Fintype.card ι : ℝ≥0∞)⁻¹) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfin] with e he
        have := h fun i ↦ (e i).toNNReal
        simp only [ENNReal.coe_toNNReal (he _)] at this
        rwa [mul_comm, ← div_eq_mul_inv, ← div_eq_mul_inv]
    _ = (1 - l) + l * ((∑ i, ∫⁻ e, e i ∂μ) / Fintype.card ι) := by
        simp [lintegral_add_left measurable_const, lintegral_const_mul _ (hsum.mul_const _),
          lintegral_mul_const _ hsum, lintegral_finsetSum _ fun i _ ↦ measurable_pi_apply i,
          div_eq_mul_inv]
    _ ≤ (1 - l) + l * 1 := by
        gcongr
        refine ENNReal.div_le_of_le_mul ?_
        calc ∑ i, ∫⁻ e, e i ∂μ ≤ ∑ _ : ι, (1 : ℝ≥0∞) := Finset.sum_le_sum fun i _ ↦ hmean i
          _ = 1 * Fintype.card ι := by simp
    _ = 1 := by rw [mul_one, tsub_add_cancel_of_le hl]

/-- **The merging functions for exchangeable e-values**: a function of finitely many e-values is
one exactly when it is measurable and, for some `l ≤ 1`, its symmetrization is at most
`(1 - l) + l * mean` at every point with finite coordinates [EVR26, Note 09]. -/
theorem isExchangeableEMerging_iff (F : (ι → ℝ≥0∞) → ℝ≥0∞) :
    IsExchangeableEMerging F ↔ Measurable F ∧ ∃ l : ℝ≥0∞, l ≤ 1 ∧ ∀ e : ι → ℝ≥0,
      (∑ σ : Equiv.Perm ι, F fun i ↦ e (σ i)) / (Fintype.card (Equiv.Perm ι) : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (Fintype.card ι : ℝ≥0∞)) :=
  ⟨fun hF ↦ ⟨hF.measurable, hF.exists_sum_perm_div_le⟩,
    fun ⟨hF, _, hl, h⟩ ↦ isExchangeableEMerging_of_sum_perm_div_le hF hl h⟩

end Characterization

/-! ### The exchangeable Markov inequality -/

variable {K : ℕ}

/-- Some running mean of the `K` e-values `e` reaches `β`: for some `k`, the mean of the first
`k + 1` e-values is at least `β`. -/
def RunningMeanReaches (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) : Prop :=
  ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Finset.Iic k, e j

/-- Unfolding `RunningMeanReaches`. -/
theorem runningMeanReaches_iff {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞} :
    RunningMeanReaches β e ↔ ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Finset.Iic k, e j :=
  Iff.rfl

/-- Whether some running mean reaches `β` is decided by the order on `ℝ≥0∞`. -/
noncomputable instance (β : ℝ≥0∞) : DecidablePred (RunningMeanReaches (K := K) β) :=
  fun _ ↦ decidable_of_iff _ runningMeanReaches_iff.symm

/-- The set of e-values some running mean of which reaches `β` is measurable. -/
@[measurability]
theorem measurableSet_runningMeanReaches (β : ℝ≥0∞) :
    MeasurableSet {e : Fin K → ℝ≥0∞ | RunningMeanReaches β e} := by
  simp_rw [runningMeanReaches_iff, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun k ↦ measurableSet_le measurable_const
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- If some running mean of `e` reaches `β`, so does some running mean of every larger `e'`. -/
theorem RunningMeanReaches.mono {β : ℝ≥0∞} {e e' : Fin K → ℝ≥0∞} (h : RunningMeanReaches β e)
    (hle : e ≤ e') : RunningMeanReaches β e' :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.trans (Finset.sum_le_sum fun j _ ↦ hle j)⟩

/-- The function `β * 𝟙{some running mean reaches β}` of `K` e-values [RM26]: its value is `β`
when, for some `k`, the mean of the first `k + 1` e-values is at least `β`, and `0` otherwise. -/
noncomputable def runningMeanTest (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) : ℝ≥0∞ :=
  Set.indicator {e : Fin K → ℝ≥0∞ | RunningMeanReaches β e} (fun _ ↦ β) e

/-- The value of `β * 𝟙{some running mean reaches β}`. -/
theorem runningMeanTest_apply (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    runningMeanTest β e = if RunningMeanReaches β e then β else 0 := by
  simp only [runningMeanTest, Set.indicator_apply, Set.mem_ofPred_eq]

/-- `β * 𝟙{some running mean reaches β}` is `β` when some running mean reaches `β`. -/
theorem runningMeanTest_of_runningMeanReaches {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    (h : RunningMeanReaches β e) : runningMeanTest β e = β :=
  Set.indicator_of_mem h _

/-- `β * 𝟙{some running mean reaches β}` is `0` when no running mean reaches `β`. -/
theorem runningMeanTest_of_not_runningMeanReaches {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    (h : ¬ RunningMeanReaches β e) : runningMeanTest β e = 0 :=
  Set.indicator_of_notMem h _

/-- With no e-values, `β * 𝟙{some running mean reaches β}` is `0`. -/
theorem runningMeanTest_of_isEmpty [IsEmpty (Fin K)] (β : ℝ≥0∞) : runningMeanTest (K := K) β = 0 :=
  funext fun _ ↦ runningMeanTest_of_not_runningMeanReaches fun ⟨k, _⟩ ↦ isEmptyElim k

/-- The function `β * 𝟙{some running mean reaches β}` is measurable. -/
@[fun_prop]
theorem measurable_runningMeanTest (β : ℝ≥0∞) : Measurable (runningMeanTest (K := K) β) :=
  measurable_const.indicator (measurableSet_runningMeanReaches β)

/-- The function `β * 𝟙{some running mean reaches β}` is monotone. -/
theorem monotone_runningMeanTest (β : ℝ≥0∞) : Monotone (runningMeanTest (K := K) β) := by
  intro e e' h
  simp only [runningMeanTest_apply]
  split_ifs with he he'
  · exact le_rfl
  · exact absurd (he.mono h) he'
  · exact zero_le
  · exact le_rfl

open Finset in
/-- If every ordering `σ ∈ B` has a mean of its first `k + 1` coordinates at least `β`, and `B` is
invariant under the swaps of `0` with the indices of that prefix, then
`β * #B ≤ ∑ σ ∈ B, e (σ 0)`: by the invariance, the first coordinate has the same sum over `B` as
every coordinate of the prefix. -/
private lemma mul_card_le_sum_apply_zero_of_swap_mem [NeZero K] {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    {k : Fin K} {B : Finset (Equiv.Perm (Fin K))}
    (hswap : ∀ i ≤ k, ∀ σ ∈ B, σ * Equiv.swap 0 i ∈ B)
    (hB : ∀ σ ∈ B, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)) :
    β * #B ≤ ∑ σ ∈ B, e (σ 0) := by
  have hsym : ∀ i ∈ Iic k, ∑ σ ∈ B, e (σ i) = ∑ σ ∈ B, e (σ 0) := by
    intro i hi
    rw [mem_Iic] at hi
    exact sum_nbij' (· * Equiv.swap 0 i) (· * Equiv.swap 0 i) (hswap i hi) (hswap i hi)
      (fun σ _ ↦ by simp) (fun σ _ ↦ by simp) (fun σ _ ↦ by simp)
  refine (ENNReal.mul_le_mul_iff_right (a := (((k : ℕ) + 1 : ℕ) : ℝ≥0∞)) (by simp)
    (by simp)).mp ?_
  calc (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * (β * #B)
      = ∑ σ ∈ B, β * ((k : ℕ) + 1 : ℕ) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ σ ∈ B, ∑ j ∈ Iic k, e (σ j) := sum_le_sum hB
    _ = ∑ j ∈ Iic k, ∑ σ ∈ B, e (σ j) := sum_comm
    _ = ∑ j ∈ Iic k, ∑ σ ∈ B, e (σ 0) := sum_congr rfl hsym
    _ = (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * ∑ σ ∈ B, e (σ 0) := by
      rw [sum_const, Fin.card_Iic, nsmul_eq_mul]

open Finset in
/-- The orbit form of the exchangeable Markov inequality: if `A` is the set of orderings `σ` of
`e` for which some running mean reaches `β`, then `β * #A ≤ ∑ σ ∈ A, e (σ 0)`. The proof splits
`A` according to the last prefix whose mean reaches `β`; that event is invariant under the
permutations of the prefix, so on it the first coordinate has the same sum as the prefix mean. -/
private lemma mul_card_le_sum_apply_zero_of_runningMean [NeZero K] (β : ℝ≥0∞)
    (e : Fin K → ℝ≥0∞) :
    β * #{σ : Equiv.Perm (Fin K) | RunningMeanReaches β fun j ↦ e (σ j)} ≤
      ∑ σ : Equiv.Perm (Fin K) with RunningMeanReaches β fun j ↦ e (σ j), e (σ 0) := by
  classical
  let P : Fin K → Equiv.Perm (Fin K) → Prop := fun k σ ↦
    β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)
  -- `B k` is the set of orderings for which `k` is the last prefix whose mean reaches `β`
  let B : Fin K → Finset (Equiv.Perm (Fin K)) := fun k ↦ {σ | P k σ ∧ ∀ j, k < j → ¬ P j σ}
  have hunion : ({σ | RunningMeanReaches β fun j ↦ e (σ j)} : Finset (Equiv.Perm (Fin K))) =
      univ.biUnion B := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, B, runningMeanReaches_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk, _⟩ ↦ ⟨k, hk⟩⟩
    have hne : ({j | P j σ} : Finset (Fin K)).Nonempty := ⟨k, by simpa [P] using hk⟩
    refine ⟨_, (mem_filter.mp (max'_mem _ hne)).2, fun j hj hPj ↦ ?_⟩
    exact absurd (le_max' _ j (by simpa using hPj)) (not_le.mpr hj)
  have hdisj : ((univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint B := by
    intro k _ k' _ hkk'
    refine disjoint_left.mpr fun σ hσ hσ' ↦ ?_
    simp only [mem_filter, mem_univ, true_and, B] at hσ hσ'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact hσ.2 k' h hσ'.1
    · exact hσ'.2 k h hσ.1
  -- the event that `k` is the last prefix whose mean reaches `β` is invariant under the swaps
  -- of `0` with an index of the prefix
  have hswap : ∀ k i : Fin K, i ≤ k → ∀ σ ∈ B k, σ * Equiv.swap 0 i ∈ B k := by
    intro k i hi σ hσ
    have hP : ∀ j, k ≤ j → (P j (σ * Equiv.swap 0 i) ↔ P j σ) := fun j hj ↦ by
      simp only [P, Equiv.Perm.mul_apply, Equiv.Perm.sum_comp_swap (mem_Iic.2 (Fin.zero_le j))
        (mem_Iic.2 (hi.trans hj)) fun l ↦ e (σ l)]
    simp only [mem_filter, mem_univ, true_and, B] at hσ ⊢
    exact ⟨(hP k le_rfl).2 hσ.1, fun j hj ↦ by rw [hP j hj.le]; exact hσ.2 j hj⟩
  rw [hunion, card_biUnion hdisj, sum_biUnion hdisj, Nat.cast_sum, mul_sum]
  exact sum_le_sum fun k _ ↦ mul_card_le_sum_apply_zero_of_swap_mem (hswap k)
    fun σ hσ ↦ (mem_filter.mp hσ).2.1

open Finset in
/-- The symmetrization of `max (runningMeanTest β) (min_k e_k)` at `e` is at most the mean of
`e`, in the form `∑ σ, G (fun i ↦ e (σ i)) ≤ ∑ σ, e (σ 0)`. -/
private lemma sum_perm_max_runningMeanTest_iInf_le [NeZero K] (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    ∑ σ : Equiv.Perm (Fin K), max (runningMeanTest β fun i ↦ e (σ i)) (⨅ k, e (σ k)) ≤
      ∑ σ : Equiv.Perm (Fin K), e (σ 0) := by
  classical
  have hc : ∀ σ : Equiv.Perm (Fin K), ⨅ k, e (σ k) = ⨅ k, e k := fun σ ↦ Equiv.iInf_comp σ
  simp_rw [hc]
  rw [← sum_filter_add_sum_filter_not univ fun σ ↦ RunningMeanReaches β fun j ↦ e (σ j),
    ← sum_filter_add_sum_filter_not univ (fun σ ↦ RunningMeanReaches β fun j ↦ e (σ j))
      fun σ : Equiv.Perm (Fin K) ↦ e (σ 0)]
  refine add_le_add ?_ (sum_le_sum fun σ hσ ↦ ?_)
  · rw [sum_congr rfl fun σ hσ ↦ by
      rw [runningMeanTest_of_runningMeanReaches (mem_filter.mp hσ).2], sum_const, nsmul_eq_mul]
    rcases le_total β (⨅ k, e k) with h | h
    · rw [max_eq_right h, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun σ _ ↦ iInf_le _ _
    · rw [max_eq_left h, mul_comm]
      exact mul_card_le_sum_apply_zero_of_runningMean β e
  · rw [runningMeanTest_of_not_runningMeanReaches (mem_filter.mp hσ).2, max_eq_right zero_le]
    exact iInf_le _ _

/-- The maximum of `β * 𝟙{some running mean reaches β}` and the smallest e-value is a merging
function for exchangeable e-values [EVR26, Note 09]. -/
theorem isExchangeableEMerging_max_runningMeanTest_iInf [NeZero K] (β : ℝ≥0∞) :
    IsExchangeableEMerging fun e : Fin K → ℝ≥0∞ ↦ max (runningMeanTest β e) (⨅ k, e k) := by
  refine isExchangeableEMerging_of_sum_perm_div_le ((measurable_runningMeanTest β).max
    (Measurable.iInf fun k ↦ measurable_pi_apply k)) le_rfl fun e ↦ ?_
  have h := ENNReal.sum_perm_apply_div_card (fun i ↦ (e i : ℝ≥0∞)) 0
  rw [tsub_self, zero_add, one_mul, ← h]
  exact ENNReal.div_le_div_right
    (sum_perm_max_runningMeanTest_iInf_le β fun i ↦ (e i : ℝ≥0∞)) _

/-- **The exchangeable Markov inequality** [RM26]: for every number `K` of e-values and every
level `β`, the function `β * 𝟙{some running mean reaches β}` is a merging function for
exchangeable e-values. -/
theorem isExchangeableEMerging_runningMeanTest (β : ℝ≥0∞) :
    IsExchangeableEMerging (runningMeanTest (K := K) β) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [runningMeanTest_of_isEmpty]
    exact isExchangeableEMerging_const zero_le
  · have : NeZero K := ⟨hK.ne'⟩
    exact (isExchangeableEMerging_max_runningMeanTest_iInf β).of_le (measurable_runningMeanTest β)
      fun e ↦ le_max_left _ _

/-- **The function of the exchangeable Markov inequality is not admissible**: for every number
`K` of e-values and every level `β`, there is a monotone merging function for exchangeable
e-values that is at least `β * 𝟙{some running mean reaches β}` and differs from it. This answers
the question of [Wan25, Section 4 (d)], which is asked for `K ≥ 2` and `1 < β < ∞`
[EVR26, Note 09]. For `K ≥ 1` the function is the maximum with the smallest e-value. -/
theorem exists_isExchangeableEMerging_monotone_runningMeanTest_lt (β : ℝ≥0∞) :
    ∃ G : (Fin K → ℝ≥0∞) → ℝ≥0∞, IsExchangeableEMerging G ∧ Monotone G ∧
      runningMeanTest β < G := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine ⟨fun _ ↦ 1, isExchangeableEMerging_const le_rfl, monotone_const,
      lt_of_le_of_ne (fun e ↦ by simp [runningMeanTest_of_isEmpty]) fun h ↦ ?_⟩
    simpa [runningMeanTest_of_isEmpty] using congr_fun h 0
  have : NeZero K := ⟨hK.ne'⟩
  refine ⟨fun e ↦ max (runningMeanTest β e) (⨅ k, e k),
    isExchangeableEMerging_max_runningMeanTest_iInf β, fun e e' h ↦ ?_,
    lt_of_le_of_ne (fun e ↦ le_max_left _ _) fun h ↦ ?_⟩
  · exact max_le_max (monotone_runningMeanTest β h) (iInf_mono fun k ↦ h k)
  · -- at a constant vector `x` with `0 < x < ∞` and `x ≠ β`, the two functions differ
    obtain ⟨x, hx₀, hx_top, hxβ⟩ : ∃ x : ℝ≥0∞, x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ β := by
      by_cases hβ : β = 1
      · exact ⟨2, by simp, by simp, by rw [hβ]; norm_num⟩
      · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, Ne.symm hβ⟩
    have hx : x ≤ runningMeanTest β fun _ ↦ x :=
      calc x = ⨅ _ : Fin K, x := iInf_const.symm
        _ ≤ max (runningMeanTest β fun _ ↦ x) (⨅ _ : Fin K, x) := le_max_right _ _
        _ = runningMeanTest β fun _ ↦ x := (congr_fun h fun _ ↦ x).symm
    rw [runningMeanTest_apply] at hx
    split_ifs at hx with hmem
    · obtain ⟨k, hk⟩ := runningMeanReaches_iff.1 hmem
      rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul, mul_comm β] at hk
      exact hxβ (le_antisymm hx ((ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hk))
    · exact hx₀ (nonpos_iff_eq_zero.mp hx)

end ProbabilityTheory
