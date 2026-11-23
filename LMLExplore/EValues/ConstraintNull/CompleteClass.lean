/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.ConstraintNull.Basic
public import LMLExplore.Probability.QuasiSure
import LMLExplore.Algebra.Order.Archimedean.Basic
import LMLExplore.EValues.EVariable
import LMLExplore.Algebra.Order.Field.Basic
import LMLExplore.LinearAlgebra.Pi
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The complete class theorem for finitely many constraints

Let `g i`, for `i` in a finite type, be measurable real constraints on a measurable space `𝓧`. The
complete class theorem of Larsson, Ramdas and Ruf [LRR26, Theorem 3.1] says that a measurable
`f : 𝓧 → ℝ` has `∫ f ∂μ ≤ 0` under every member `μ` of the null `constraintNull (range g)` exactly
when `f ≤ ∑ i, π i * g i` quasi-surely (almost surely under every member of the null, the filter
`ProbabilityTheory.quasiSure`), for some weights `π ≥ 0`. In particular, the e-variables for the
null are the measurable functions quasi-surely dominated by a bet `1 + ∑ i, π i * g i`.

The proof of [LRR26] shows that a cone is closed in a weak topology and applies a bipolar theorem.
The proof here is finite-dimensional, in three steps.

* *A set carrying the null.* Removing, finitely many times, the set where a nonnegative
  combination of the constraints that is nonnegative on what remains is positive, gives a
  measurable set `Y` that carries every member of the null and on which the constraints admit no
  arbitrage: every nonnegative combination of the constraints that is nonnegative on `Y` vanishes
  on `Y` (`ProbabilityTheory.NoArbitrageOn`). The removed sets are null for every member of the
  null, since there the combination has a nonnegative integrand with a nonpositive integral. The
  same construction, stopped at the first removed set that a given measure `Q` charges, gives
  either such a set `Y` that also carries `Q`, or a nonnegative combination of the constraints,
  nonnegative almost surely under the null and under `Q`, that is positive on a set of positive
  `Q`-measure.
* *The finite step.* On a finite subset of `Y`, separating a compact convex hull from a closed
  convex set gives the domination up to an additive `δ > 0`.
* *Compactness.* Without arbitrage, the weights whose support is not redundant
  (`ProbabilityTheory.nonredundantWeights`) and that keep the combination above `-c` at well chosen
  finitely many points have a total mass at most proportional to `c` [LRR26, proof of Lemma 7.2],
  and every nonnegative combination has such weights on `Y` [LRR26, Lemma 3.2]. A finite
  intersection argument in the compact set of these weights removes `δ` and the finiteness.

The finite-dimensional theorem only uses the finitely supported members of the null. Applied to
multiples of the indicator of a point, it shows that every point of `Y` is charged by a finitely
supported member of the null, so that e-variables are finite on `Y`, and that the quasi-sure filter
of the null is the principal filter of `Y`: a property holds quasi-surely exactly when it holds on
`Y`. The pointwise form of each complete class theorem, on `Y`, and its quasi-sure form follow
from one another.

## Main definitions

* `ProbabilityTheory.NoArbitrageOn a Y`: every nonnegative combination of the functions `a i` that
  is nonnegative on `Y` vanishes on `Y`.
* `ProbabilityTheory.nonredundantWeights a Y`: the nonnegative weights whose support is not
  redundant on `Y` [LRR26, (3.1)].

## Main statements

* `ProbabilityTheory.noArbitrageOn_of_forall_neg`: a point of `Y` at which every function is
  negative excludes arbitrage on `Y`.
* `ProbabilityTheory.exists_mem_nonredundantWeights_sum_mul_eq`: every nonnegative combination is,
  on `Y`, a combination with nonredundant weights [LRR26, Lemma 3.2].
* `ProbabilityTheory.exists_finset_sum_le_of_noArbitrageOn`: without arbitrage, the total mass of
  nonredundant weights is controlled at finitely many points [LRR26, proof of Lemma 7.2].
* `ProbabilityTheory.isCompact_nonredundantWeights_inter_nonneg`: without arbitrage on `Y`, the
  nonredundant weights `π` with `1 + ∑ i, π i * a i` nonnegative on `Y` form a compact set
  [LRR26, Lemma 7.2].
* `ProbabilityTheory.exists_mem_nonredundantWeights_le_of_noArbitrageOn`: the complete class
  theorem in finite-dimensional form, on a set without arbitrage.
* `ProbabilityTheory.exists_measurableSet_noArbitrageOn`: a measurable set carrying the null, on
  which the constraints admit no arbitrage.
* `ProbabilityTheory.exists_measurableSet_noArbitrageOn_or_exists_sum_mul_pos`: such a set
  that also carries a given measure `Q`, or a nonnegative combination of the constraints that is
  positive on a set of positive `Q`-measure.
* `ProbabilityTheory.lt_top_of_isEVar_of_noArbitrageOn`: e-variables are finite on a set without
  arbitrage.
* `ProbabilityTheory.quasiSure_constraintNull_eq_principal`: on a set without arbitrage that
  carries the null, the quasi-sure filter of the null is the principal filter of the set.
* `ProbabilityTheory.forall_integral_nonpos_iff_exists_ae_le`: **the complete class theorem**
  [LRR26, Theorem 3.1].
* `ProbabilityTheory.IsEVar.exists_mem_constraintBets_le_of_noArbitrageOn`,
  `ProbabilityTheory.IsEVar.exists_mem_constraintBets_ae_le`,
  `ProbabilityTheory.isEVar_constraintNull_iff`: the complete class theorem for e-variables
  [LRR26, Theorem 3.1]: every e-variable is dominated by a bet, on a set without arbitrage that
  carries the null, and quasi-surely.
* `ProbabilityTheory.noArbitrageOn_add_integral_div_of_lintegral_le`,
  `ProbabilityTheory.exists_add_sum_smul_dirac_mem_constraintNull`: on a nonempty set without
  arbitrage that carries the null, a finite measure carried by that set that integrates the
  constraints and under which every e-variable has mean at most `c < 1` is completed into a member
  of the null by a finitely supported measure [EVR26, Note 20].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01–34 and the
  Lean library EValuesResearch, github.com/RemyDegenne/evalues_research (2026).
* [LRR26] M. Larsson, A. Ramdas and J. Ruf, *Testing hypotheses generated by constraints*, Math.
  Oper. Res. (2026), arXiv:2504.02974v5.
-/

public section

open MeasureTheory Set LMLExplore
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 ι : Type*} [Fintype ι] {a : ι → 𝓧 → ℝ} {Y : Set 𝓧}

/-! ### Nonredundant weights and the absence of arbitrage -/

/-- The functions `a i` admit no arbitrage on `Y`: every nonnegative combination of them that is
nonnegative on `Y` vanishes on `Y`. -/
def NoArbitrageOn (a : ι → 𝓧 → ℝ) (Y : Set 𝓧) : Prop :=
  ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) → (∀ x ∈ Y, 0 ≤ ∑ i, ρ i * a i x) →
    ∀ x ∈ Y, ∑ i, ρ i * a i x = 0

/-- The absence of arbitrage on `Y`, restated. -/
theorem noArbitrageOn_iff : NoArbitrageOn a Y ↔ ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) →
    (∀ x ∈ Y, 0 ≤ ∑ i, ρ i * a i x) → ∀ x ∈ Y, ∑ i, ρ i * a i x = 0 :=
  Iff.rfl

/-- A point of `Y` at which every function `a i` is negative excludes arbitrage on `Y`: a
nonnegative combination that is nonnegative at that point has all its weights zero. -/
theorem noArbitrageOn_of_forall_neg {x₀ : 𝓧} (hx₀ : x₀ ∈ Y) (ha : ∀ i, a i x₀ < 0) :
    NoArbitrageOn a Y := by
  refine noArbitrageOn_iff.2 fun ρ hρ h x _ ↦ ?_
  have hle : ∀ i ∈ Finset.univ, ρ i * a i x₀ ≤ 0 :=
    fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hρ i) (ha i).le
  have h0 := (Finset.sum_eq_zero_iff_of_nonpos hle).1
    (le_antisymm (Finset.sum_nonpos hle) (h x₀ hx₀))
  have hρ0 (i : ι) : ρ i = 0 :=
    (mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_right (ha i).ne
  simp [hρ0]

/-- The nonnegative weights whose support is not redundant on `Y` [LRR26, (3.1)]: no nonzero
nonnegative combination of the functions `a i` with support inside that of the weights vanishes
on `Y`. -/
def nonredundantWeights (a : ι → 𝓧 → ℝ) (Y : Set 𝓧) : Set (ι → ℝ) :=
  {π | (∀ i, 0 ≤ π i) ∧ ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) → (∀ i, π i = 0 → ρ i = 0) →
    (∀ x ∈ Y, ∑ i, ρ i * a i x = 0) → ρ = 0}

/-- Membership in the nonredundant weights. -/
theorem mem_nonredundantWeights_iff {π : ι → ℝ} :
    π ∈ nonredundantWeights a Y ↔ (∀ i, 0 ≤ π i) ∧ ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) →
      (∀ i, π i = 0 → ρ i = 0) → (∀ x ∈ Y, ∑ i, ρ i * a i x = 0) → ρ = 0 :=
  Iff.rfl

/-- The nonredundant weights form a closed set [LRR26, Section 3]. -/
theorem isClosed_nonredundantWeights : IsClosed (nonredundantWeights a Y) := by
  have h : nonredundantWeights a Y = (⋂ i, {π : ι → ℝ | 0 ≤ π i}) ∩
      ⋂ (ρ : ι → ℝ) (_ : (∀ i, 0 ≤ ρ i) ∧ (∀ x ∈ Y, ∑ i, ρ i * a i x = 0) ∧ ρ ≠ 0),
        ⋃ i ∈ {i | ρ i ≠ 0}, {π | π i = 0} := by
    ext π
    simp only [mem_nonredundantWeights_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_iUnion,
      exists_prop, and_imp]
    refine and_congr_right fun _ ↦ forall_congr' fun ρ ↦ ?_
    constructor
    · intro h hρ hρa hne
      by_contra! hcon
      exact hne (h hρ (fun i hi ↦ by_contra fun h' ↦ hcon i h' hi) hρa)
    · intro h hρ hπρ hρa
      by_contra hne
      obtain ⟨i, hi, hπi⟩ := h hρ hρa hne
      exact hi (hπρ i hπi)
  rw [h]
  refine (isClosed_iInter fun i ↦ isClosed_le continuous_const
    (by fun_prop : Continuous fun π : ι → ℝ ↦ π i)).inter
    (isClosed_iInter fun (ρ : ι → ℝ) ↦ isClosed_iInter fun _ ↦
      (toFinite {i | ρ i ≠ 0}).isClosed_biUnion fun i _ ↦
        isClosed_eq (by fun_prop : Continuous fun π : ι → ℝ ↦ π i) continuous_const)

/-- The nonredundant weights form a cone. -/
theorem smul_mem_nonredundantWeights {π : ι → ℝ} (hπ : π ∈ nonredundantWeights a Y) {c : ℝ}
    (hc : 0 ≤ c) : c • π ∈ nonredundantWeights a Y := by
  refine ⟨fun i ↦ by simpa using mul_nonneg hc (hπ.1 i), fun ρ hρ hρπ hρa ↦ ?_⟩
  refine hπ.2 ρ hρ (fun i hi ↦ hρπ i ?_) hρa
  simp [hi]

/-- Every nonnegative combination of the functions `a i` is, on `Y`, a combination with
nonredundant weights [LRR26, Lemma 3.2]. -/
theorem exists_mem_nonredundantWeights_sum_mul_eq {π : ι → ℝ} (hπ : ∀ i, 0 ≤ π i) :
    ∃ π' ∈ nonredundantWeights a Y, ∀ x ∈ Y, ∑ i, π' i * a i x = ∑ i, π i * a i x := by
  classical
  induction h : (Finset.univ.filter fun i ↦ π i ≠ 0).card using Nat.strong_induction_on
    generalizing π with
  | _ n ih =>
  by_cases hK : π ∈ nonredundantWeights a Y
  · exact ⟨π, hK, fun _ _ ↦ rfl⟩
  simp only [mem_nonredundantWeights_iff, hπ, implies_true, true_and, not_forall] at hK
  obtain ⟨ρ, hρ, hπρ, hρa, hne⟩ := hK
  have hsne : (Finset.univ.filter fun i ↦ ρ i ≠ 0).Nonempty := by
    by_contra hs
    refine hne (funext fun i ↦ ?_)
    by_contra hi
    exact hs ⟨i, by simpa using hi⟩
  obtain ⟨j, hj, hmin⟩ := (Finset.univ.filter fun i ↦ ρ i ≠ 0).exists_min_image
    (fun i ↦ π i / ρ i) hsne
  have hj' : ρ j ≠ 0 := (Finset.mem_filter.1 hj).2
  have hπj : π j ≠ 0 := fun h ↦ hj' (hπρ j h)
  set t := π j / ρ j with ht
  set π'' : ι → ℝ := fun i ↦ π i - t * ρ i with hπ''
  have hπ''0 : ∀ i, 0 ≤ π'' i := by
    intro i
    by_cases hi : ρ i = 0
    · simp [π'', hi, hπ i]
    · have hρi : 0 < ρ i := lt_of_le_of_ne (hρ i) (Ne.symm hi)
      have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      rw [le_div_iff₀ hρi] at this
      simp only [π'', sub_nonneg]
      exact this
  have hπ''j : π'' j = 0 := by
    simp only [π'', ht]
    field_simp
    ring
  have hsub : (Finset.univ.filter fun i ↦ π'' i ≠ 0) ⊂
      (Finset.univ.filter fun i ↦ π i ≠ 0) := by
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨j, by simpa using hπj, by simp [hπ''j]⟩
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hπi
    exact hi (by simp [π'', hπi, hπρ i hπi])
  obtain ⟨π', hπ', heq⟩ := ih _ (h ▸ Finset.card_lt_card hsub) hπ''0 rfl
  refine ⟨π', hπ', fun x hx ↦ (heq x hx).trans ?_⟩
  have := hρa x hx
  simp only [π'', sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, this,
    mul_zero, sub_zero]

/-- A closed set of nonredundant weights with bounded total mass is compact. -/
theorem isCompact_nonredundantWeights_inter {T : Set (ι → ℝ)} (hT : IsClosed T) {c : ℝ}
    (hc : ∀ π ∈ nonredundantWeights a Y ∩ T, ∑ i, π i ≤ c) :
    IsCompact (nonredundantWeights a Y ∩ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_nonredundantWeights.inter hT) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max c 0, fun π hπ ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
  intro i
  rw [Real.norm_of_nonneg (hπ.1.1 i)]
  exact ((Finset.single_le_sum (fun j _ ↦ hπ.1.1 j) (Finset.mem_univ i)).trans
    (hc π hπ)).trans (le_max_left _ _)

/-- Without arbitrage on `Y`, there are a finite set `F₀ ⊆ Y` and `R ≥ 0` such that every
nonredundant weight keeping the combination of the functions `a i` above `-c` on `F₀` has total
mass at most `R * c` [LRR26, proof of Lemma 7.2]. -/
theorem exists_finset_sum_le_of_noArbitrageOn (h : NoArbitrageOn a Y) :
    ∃ F₀ : Finset 𝓧, ↑F₀ ⊆ Y ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ π ∈ nonredundantWeights a Y, ∀ c : ℝ,
      0 ≤ c → (∀ x ∈ F₀, -c ≤ ∑ i, π i * a i x) → ∑ i, π i ≤ R * c := by
  classical
  -- The nonredundant weights of total mass `1` form a compact set `S`. Without arbitrage, it
  -- misses the intersection of the closed sets `t (x, n)` of the weights keeping the combination
  -- above `-1 / (n + 1)` at `x ∈ Y`.
  set S := nonredundantWeights a Y ∩ {ρ | ∑ i, ρ i = 1}
  have hS : IsCompact S := isCompact_nonredundantWeights_inter
    (isClosed_eq (by fun_prop) continuous_const) (c := 1) fun ρ hρ ↦ hρ.2.le
  let t : Y × ℕ → Set (ι → ℝ) := fun p ↦ {ρ | -(1 / ((p.2 : ℝ) + 1)) ≤ ∑ i, ρ i * a i p.1}
  have htc : ∀ p, IsClosed (t p) := fun p ↦ isClosed_le continuous_const (by fun_prop)
  have hdisj : Disjoint S (⋂ p, t p) := by
    rw [disjoint_left]
    rintro ρ ⟨hρK, hρS⟩ hρt
    simp only [mem_iInter, t, mem_ofPred_eq] at hρt
    have h0 : ∀ x ∈ Y, 0 ≤ ∑ i, ρ i * a i x := fun x hx ↦
      le_of_forall_nat_le_add_one_div fun n ↦ by
        have := hρt (⟨x, hx⟩, n)
        simp only at this
        linarith
    have hρ0 := hρK.2 ρ hρK.1 (fun i hi ↦ hi) (h ρ hρK.1 h0)
    simp [hρ0] at hρS
  -- Finite subcover: finitely many `t p`, `p ∈ u`, already miss `S`; their points form `F₀`.
  obtain ⟨u, hu⟩ := hS.elim_finite_subfamily_closed t htc hdisj
  set N := u.sup Prod.snd
  refine ⟨u.image fun p ↦ (p.1 : 𝓧), ?_, (N : ℝ) + 1, by positivity, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx
    obtain ⟨p, -, rfl⟩ := hx
    exact p.1.property
  intro π hπ c hc hπc
  have hsum0 : 0 ≤ ∑ i, π i := Finset.sum_nonneg fun i _ ↦ hπ.1 i
  rcases hsum0.eq_or_lt with hs | hs
  · rw [← hs]
    positivity
  -- Normalisation to the simplex: `s⁻¹ • π ∈ S`, so it leaves some `t p` with `p ∈ u`.
  set s := ∑ i, π i with hs_def
  have hρS : s⁻¹ • π ∈ S := by
    refine ⟨smul_mem_nonredundantWeights hπ (inv_nonneg.2 hs.le), ?_⟩
    simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  have hnot : s⁻¹ • π ∉ ⋂ p ∈ u, t p := fun h' ↦ disjoint_left.1 hu hρS h'
  simp only [mem_iInter, not_forall, t, mem_ofPred_eq, not_le, Pi.smul_apply,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum] at hnot
  obtain ⟨p, hp, hlt⟩ := hnot
  -- The final bound: `-c ≤ ∑ i, π i * a i p.1 < -s / (p.2 + 1) ≤ -s / (N + 1)`.
  have hc' := hπc _ (Finset.mem_image_of_mem _ hp)
  have hN := Nat.one_div_le_one_div (α := ℝ) (Finset.le_sup (f := Prod.snd) hp)
  rw [inv_mul_lt_iff₀ hs] at hlt
  have : s * (1 / ((N : ℝ) + 1)) < c := by linarith [mul_le_mul_of_nonneg_left hN hs.le]
  rw [mul_one_div, div_lt_iff₀ (by positivity)] at this
  linarith

/-- Without arbitrage on `Y`, the nonredundant weights `π` for which `1 + ∑ i, π i * a i` is
nonnegative on `Y` form a compact set [LRR26, Lemma 7.2]. -/
theorem isCompact_nonredundantWeights_inter_nonneg (h : NoArbitrageOn a Y) :
    IsCompact (nonredundantWeights a Y ∩ {π | ∀ x ∈ Y, 0 ≤ 1 + ∑ i, π i * a i x}) := by
  obtain ⟨F₀, hF₀, R, -, hbound⟩ := exists_finset_sum_le_of_noArbitrageOn h
  refine isCompact_nonredundantWeights_inter ?_ (c := R * 1) fun π hπ ↦
    hbound π hπ.1 1 zero_le_one fun x hx ↦ by linarith [hπ.2 x (hF₀ hx)]
  simp only [ofPred_forall]
  exact isClosed_biInter fun x _ ↦ isClosed_le continuous_const (by fun_prop)

/-- The finite step of the complete class theorem, up to `δ`: if `f` has a nonpositive mean under
every finitely supported law on `Y` under which the functions `a i` have nonpositive means, then on
a finite subset of `Y` it is at most `δ` plus a nonnegative combination of the `a i`. The proof
separates a compact convex hull from a closed convex set. -/
private lemma exists_le_add_sum_mul_of_finset {f : 𝓧 → ℝ}
    (hf : ∀ (α : Type) [Fintype α] (x : α → 𝓧) (w : α → ℝ), (∀ k, x k ∈ Y) →
      w ∈ simplex α → (∀ i, ∑ k, w k * a i (x k) ≤ 0) → ∑ k, w k * f (x k) ≤ 0)
    {F : Finset 𝓧} (hF : ↑F ⊆ Y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ π : ι → ℝ, (∀ i, 0 ≤ π i) ∧ ∀ x ∈ F, f x ≤ δ + ∑ i, π i * a i x := by
  classical
  -- Separate the compact convex hull of the points `(f x, (a i x)ᵢ)`, `x ∈ F`, from the closed
  -- convex set of the points `(r, y)` with `δ ≤ r` and `y ≤ 0`.
  let φ : 𝓧 → ℝ × (ι → ℝ) := fun x ↦ (f x, fun i ↦ a i x)
  have hdisj : Disjoint (convexHull ℝ (φ '' F)) (Ici δ ×ˢ Iic 0) := by
    rw [disjoint_left]
    rintro p hp ⟨hp1, hp2⟩
    obtain ⟨α, _, w, z, hw0, hw1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hp
    choose x hxF hxz using hz
    have hsum2 : ∀ i, ∑ k, w k * a i (x k) ≤ 0 := fun i ↦ by
      simpa [← hxz, φ, Prod.snd_sum, Finset.sum_apply] using hp2 i
    have key := hf α x w (fun k ↦ hF (hxF k)) (mem_simplex_iff.2 ⟨hw0, hw1⟩) hsum2
    have h1 : δ ≤ ∑ k, w k * f (x k) := by simpa [← hxz, φ, Prod.fst_sum] using hp1
    linarith
  obtain ⟨ℓ, u, v, hℓP, huv, hℓQ⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) ((F.finite_toSet.image φ).isCompact_convexHull ℝ)
    ((convex_Ici δ).prod (convex_Iic 0)) (isClosed_Ici.prod isClosed_Iic) hdisj
  -- Read off the separating functional: `ℓ (r, y) = β * r - ∑ i, π i * y i`.
  set β := ℓ (1, 0) with hβ_def
  set π : ι → ℝ := fun i ↦ -ℓ (0, Pi.single i 1) with hπ_def
  have hℓ : ∀ p : ℝ × (ι → ℝ), ℓ p = β * p.1 - ∑ i, π i * p.2 i := fun p ↦ by
    simpa [π, mul_comm, sub_eq_add_neg] using
      LinearMap.prod_pi_apply_eq_sum_univ (ℓ : ℝ × (ι → ℝ) →ₗ[ℝ] ℝ) p.1 p.2
  -- `ℓ` is bounded below on the closed convex set, so `β` and the `π i` are nonnegative.
  have hβ : 0 ≤ β := by
    refine nonneg_of_forall_lt_add_mul (A := β * δ) (v := v) fun t ht ↦ ?_
    have := hℓQ (δ + t, 0) ⟨by simpa using ht, mem_Iic.2 le_rfl⟩
    rw [hℓ] at this
    simpa [add_mul, mul_comm] using this
  have hπ : ∀ i, 0 ≤ π i := by
    intro i
    refine nonneg_of_forall_lt_add_mul (A := β * δ) (v := v) fun t ht ↦ ?_
    have := hℓQ (δ, fun j ↦ if i = j then -t else 0)
      ⟨mem_Ici.2 le_rfl, fun j ↦ by simp only [Pi.zero_apply]; split_ifs <;> linarith⟩
    rw [hℓ] at this
    simpa [mul_ite, Finset.sum_ite_eq, mul_comm] using this
  have hx : ∀ x ∈ F, β * f x - ∑ i, π i * a i x < u := fun x hx ↦ by
    simpa [hℓ, φ] using hℓP (φ x) (subset_convexHull ℝ _ (mem_image_of_mem φ hx))
  have hv : v < β * δ := by simpa [hℓ] using hℓQ (δ, 0) ⟨mem_Ici.2 le_rfl, mem_Iic.2 le_rfl⟩
  rcases hβ.eq_or_lt with hβ0 | hβ0
  · -- The separating functional is vertical: the combination is positive on `F`, and a large
    -- multiple of it dominates `f` there.
    rw [← hβ0, zero_mul] at hv
    set M := (∑ y ∈ F, |f y|) / -u
    have hM : 0 ≤ M := div_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by linarith)
    refine ⟨M • π, fun i ↦ by simpa using mul_nonneg hM (hπ i), fun x hxF ↦ ?_⟩
    have h1 := hx x hxF
    rw [← hβ0, zero_mul, zero_sub] at h1
    have h2 : M * -u ≤ M * ∑ i, π i * a i x := mul_le_mul_of_nonneg_left (by linarith) hM
    have h3 : M * -u = ∑ y ∈ F, |f y| := div_mul_cancel₀ _ (by linarith)
    have h4 : f x ≤ ∑ y ∈ F, |f y| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun y _ ↦ abs_nonneg (f y)) hxF)
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    linarith
  · -- Otherwise, dividing by `β` gives `f ≤ δ + ∑ i, β⁻¹ * π i * a i` on `F`.
    refine ⟨β⁻¹ • π, fun i ↦ by simpa using mul_nonneg (inv_nonneg.2 hβ) (hπ i),
      fun x hxF ↦ ?_⟩
    have h1 := hx x hxF
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    have h2 : f x - δ < β⁻¹ * ∑ i, π i * a i x := by
      rw [lt_inv_mul_iff₀ hβ0]
      nlinarith
    linarith

/-- **The complete class theorem on a set without arbitrage**, in finite-dimensional form: if `f`
has a nonpositive mean under every finitely supported law on `Y` under which the functions `a i`
have nonpositive means, then `f ≤ ∑ i, π i * a i` on `Y` for some nonredundant weights `π`. -/
theorem exists_mem_nonredundantWeights_le_of_noArbitrageOn (h : NoArbitrageOn a Y) {f : 𝓧 → ℝ}
    (hf : ∀ (α : Type) [Fintype α] (x : α → 𝓧) (w : α → ℝ), (∀ k, x k ∈ Y) →
      w ∈ simplex α → (∀ i, ∑ k, w k * a i (x k) ≤ 0) → ∑ k, w k * f (x k) ≤ 0) :
    ∃ π ∈ nonredundantWeights a Y, ∀ x ∈ Y, f x ≤ ∑ i, π i * a i x := by
  classical
  -- The nonredundant weights keeping the combination above `-C` on `F₀` form a compact set.
  obtain ⟨F₀, hF₀, R, hR, hbound⟩ := exists_finset_sum_le_of_noArbitrageOn h
  have hC0 : 0 ≤ 1 + ∑ x ∈ F₀, |f x| :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  set C := 1 + ∑ x ∈ F₀, |f x| with hC
  set T : Set (ι → ℝ) := {π | ∀ x ∈ F₀, -C ≤ ∑ i, π i * a i x}
  have hTc : IsClosed T := by
    simp only [T, ofPred_forall]
    exact isClosed_biInter fun x _ ↦ isClosed_le continuous_const (by fun_prop)
  have hs : IsCompact (nonredundantWeights a Y ∩ T) :=
    isCompact_nonredundantWeights_inter hTc (c := R * C) fun π hπ ↦
      hbound π hπ.1 C hC0 hπ.2
  -- By the finite step, it meets every finite intersection of the closed sets `t (x, n)` of the
  -- weights with `f x ≤ 1 / (n + 1) + ∑ i, π i * a i x`, so it meets their intersection.
  let t : Y × ℕ → Set (ι → ℝ) := fun p ↦
    {π | f p.1 ≤ 1 / ((p.2 : ℝ) + 1) + ∑ i, π i * a i p.1}
  have htc : ∀ p, IsClosed (t p) := fun p ↦ isClosed_le continuous_const (by fun_prop)
  obtain ⟨π, ⟨hπK, -⟩, hπt⟩ := hs.inter_iInter_nonempty t htc fun u ↦ by
    set N := u.sup Prod.snd
    set F := F₀ ∪ u.image fun p ↦ (p.1 : 𝓧)
    have hF : ↑F ⊆ Y := by
      intro x hx
      simp only [F, Finset.coe_union, Finset.coe_image, mem_union, Finset.mem_coe,
        mem_image] at hx
      rcases hx with hx | ⟨p, -, rfl⟩
      · exact hF₀ hx
      · exact p.1.property
    obtain ⟨π, hπ0, hπ⟩ := exists_le_add_sum_mul_of_finset hf hF
      (δ := 1 / ((N : ℝ) + 1)) (by positivity)
    obtain ⟨π', hπ'K, hπ'eq⟩ := exists_mem_nonredundantWeights_sum_mul_eq (a := a) (Y := Y) hπ0
    refine ⟨π', ⟨hπ'K, fun x hx ↦ ?_⟩, ?_⟩
    · have h1 := hπ x (Finset.mem_union_left _ hx)
      have h2 : -|f x| ≤ f x := neg_abs_le _
      have h3 : |f x| ≤ ∑ y ∈ F₀, |f y| :=
        Finset.single_le_sum (f := fun y ↦ |f y|) (fun y _ ↦ abs_nonneg _) hx
      have h4 : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [N.cast_nonneg (α := ℝ)]
      rw [hπ'eq x (hF₀ hx)]
      linarith
    · simp only [mem_iInter]
      intro p hp
      have h1 := hπ p.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
      have h2 := Nat.one_div_le_one_div (α := ℝ) (Finset.le_sup (f := Prod.snd) hp)
      simp only [t, mem_ofPred_eq]
      rw [hπ'eq p.1 p.1.property]
      linarith
  refine ⟨π, hπK, fun x hx ↦ le_of_forall_nat_le_add_one_div fun n ↦ ?_⟩
  have := mem_iInter.1 hπt (⟨x, hx⟩, n)
  simp only [t, mem_ofPred_eq] at this
  linarith

/-- Without arbitrage on `Y`, every point of `Y` is charged by a finitely supported law on `Y`
under which the functions `a i` have nonpositive means. This is what makes e-variables for the
null finite on `Y` (`ProbabilityTheory.lt_top_of_isEVar_of_noArbitrageOn`). -/
theorem exists_charging_family_of_noArbitrageOn (h : NoArbitrageOn a Y) {x₀ : 𝓧}
    (hx₀ : x₀ ∈ Y) :
    ∃ (α : Type) (_ : Fintype α) (x : α → 𝓧) (w : α → ℝ), (∀ k, x k ∈ Y) ∧ w ∈ simplex α ∧
      (∀ i, ∑ k, w k * a i (x k) ≤ 0) ∧ ∃ k, x k = x₀ ∧ 0 < w k := by
  classical
  by_contra hcon
  -- if no such law charges `x₀`, then `E - 1`, with `E = n • 1_{x₀}`, has nonpositive means
  -- under all of them, for any `n`
  obtain ⟨F₀, hF₀, R, hR, hbound⟩ := exists_finset_sum_le_of_noArbitrageOn h
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + R * ∑ i, |a i x₀|)
  set E : 𝓧 → ℝ := fun y ↦ if y = x₀ then (n : ℝ) else 0
  have hE0 : ∀ y, 0 ≤ E y := fun y ↦ by
    simp only [E]
    split_ifs <;> positivity
  have hE : ∀ (α : Type) [Fintype α] (x : α → 𝓧) (w : α → ℝ), (∀ k, x k ∈ Y) →
      w ∈ simplex α → (∀ i, ∑ k, w k * a i (x k) ≤ 0) → ∑ k, w k * (E (x k) - 1) ≤ 0 := by
    intro α _ x w hxY hw hwa
    have : ∀ k, w k * E (x k) = 0 := by
      intro k
      by_cases hk : x k = x₀
      · have : w k = 0 := by
          by_contra hne
          exact hcon ⟨α, inferInstance, x, w, hxY, hw, hwa, k, hk,
            lt_of_le_of_ne ((mem_simplex_iff.1 hw).1 k) (Ne.symm hne)⟩
        simp [this]
      · simp [E, hk]
    simp [mul_sub, this, (mem_simplex_iff.1 hw).2]
  -- the finite-dimensional theorem dominates `E - 1` by weights of total mass at most `R`
  obtain ⟨π, hπK, hπ⟩ := exists_mem_nonredundantWeights_le_of_noArbitrageOn h
    (f := fun y ↦ E y - 1) hE
  have hsum : ∑ i, π i ≤ R * 1 := hbound π hπK 1 zero_le_one fun x hx ↦ by
    have := hπ x (hF₀ hx)
    linarith [hE0 x]
  -- at `x₀` this gives `n - 1 ≤ R * ∑ i, |a i x₀|`, contradicting the choice of `n`
  have h1 := hπ x₀ hx₀
  simp only [E, ↓reduceIte] at h1
  have h2 : ∑ i, π i * a i x₀ ≤ R * ∑ i, |a i x₀| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc π i * a i x₀ ≤ π i * |a i x₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hπK.1 i)
      _ ≤ R * |a i x₀| := mul_le_mul_of_nonneg_right
          ((Finset.single_le_sum (fun j _ ↦ hπK.1 j) (Finset.mem_univ i)).trans
            (by simpa using hsum)) (abs_nonneg _)
  linarith

/-! ### A set carrying the null -/

variable [MeasurableSpace 𝓧] {g : ι → 𝓧 → ℝ} {f : 𝓧 → ℝ} {E : 𝓧 → ℝ≥0∞}

/-- A set carrying a null generated by finitely many measurable constraints, seen from a measure
`Q`: either a measurable set of full measure for every member of the null and for `Q`, on which the
constraints admit no arbitrage, or a nonnegative combination of the constraints that is
nonnegative almost surely under every member of the null and under `Q`, and positive on a set of
positive `Q`-measure. -/
theorem exists_measurableSet_noArbitrageOn_or_exists_sum_mul_pos
    (hg : ∀ i, Measurable (g i)) (Q : Measure 𝓧) :
    (∃ Y : Set 𝓧, MeasurableSet Y ∧ (∀ μ ∈ constraintNull (range g), μ Yᶜ = 0) ∧ Q Yᶜ = 0 ∧
      NoArbitrageOn g Y) ∨
    ∃ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) ∧
      (∀ μ ∈ constraintNull (range g), ∀ᵐ x ∂μ, 0 ≤ ∑ i, ρ i * g i x) ∧
      (∀ᵐ x ∂Q, 0 ≤ ∑ i, ρ i * g i x) ∧ Q {x | 0 < ∑ i, ρ i * g i x} ≠ 0 := by
  classical
  let V : Set 𝓧 → Submodule ℝ (ι → ℝ) := fun Y ↦ Submodule.span ℝ ((fun x i ↦ g i x) '' Y)
  suffices H : ∀ n : ℕ, ∀ Y : Set 𝓧, MeasurableSet Y →
      (∀ μ ∈ constraintNull (range g), μ Yᶜ = 0) → Q Yᶜ = 0 → Module.finrank ℝ (V Y) = n →
      (∃ Y : Set 𝓧, MeasurableSet Y ∧ (∀ μ ∈ constraintNull (range g), μ Yᶜ = 0) ∧ Q Yᶜ = 0 ∧
        NoArbitrageOn g Y) ∨
      ∃ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) ∧
        (∀ μ ∈ constraintNull (range g), ∀ᵐ x ∂μ, 0 ≤ ∑ i, ρ i * g i x) ∧
        (∀ᵐ x ∂Q, 0 ≤ ∑ i, ρ i * g i x) ∧ Q {x | 0 < ∑ i, ρ i * g i x} ≠ 0 from
    H _ univ MeasurableSet.univ (by simp) (by simp) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hμY hQY hn
  by_cases hT : NoArbitrageOn g Y
  · exact .inl ⟨Y, hY, hμY, hQY, hT⟩
  simp only [noArbitrageOn_iff, not_forall] at hT
  obtain ⟨ρ, hρ0, hρY, x₀, hx₀, hne⟩ := hT
  -- the combination is nonnegative almost everywhere for the measures carried by `Y`
  have hnn : ∀ ν : Measure 𝓧, ν Yᶜ = 0 → ∀ᵐ x ∂ν, 0 ≤ ∑ i, ρ i * g i x := fun ν hν ↦
    Filter.eventually_of_mem (mem_ae_iff.2 hν) hρY
  by_cases hQρ : Q {x | 0 < ∑ i, ρ i * g i x} = 0
  swap
  · exact .inr ⟨ρ, hρ0, fun μ hμ ↦ hnn μ (hμY μ hμ), hnn Q hQY, hQρ⟩
  set Y' := Y ∩ {x | ∑ i, ρ i * g i x ≤ 0}
  have hY' : MeasurableSet Y' := hY.inter (measurableSet_le (by fun_prop) measurable_const)
  have hsub : Y'ᶜ ⊆ Yᶜ ∪ {x | 0 < ∑ i, ρ i * g i x} := by
    intro x hx
    simp only [Y', mem_compl_iff, mem_inter_iff, mem_ofPred_eq, not_and, not_le] at hx
    by_cases hxY : x ∈ Y
    · exact Or.inr (hx hxY)
    · exact Or.inl hxY
  -- the combination has a nonnegative integrand and a nonpositive integral under the null
  have hμY' : ∀ μ ∈ constraintNull (range g), μ Y'ᶜ = 0 := by
    intro μ hμ
    have hint := integrable_sum_mul_of_mem_constraintNull hμ ρ
    have h0 := (integral_eq_zero_iff_of_nonneg_ae (hnn μ (hμY μ hμ)) hint).1
      (le_antisymm (integral_sum_mul_nonpos_of_mem_constraintNull hμ hρ0)
        (integral_nonneg_of_ae (hnn μ (hμY μ hμ))))
    refine measure_mono_null hsub (measure_union_null (hμY μ hμ) ?_)
    exact measure_mono_null (fun x hx ↦ (mem_ofPred_eq ▸ hx).ne') (ae_iff.1 h0)
  have hQY' : Q Y'ᶜ = 0 := measure_mono_null hsub (measure_union_null hQY hQρ)
  -- removing the set where the combination is positive lowers the dimension
  have hlt : V Y' < V Y := by
    refine lt_of_le_of_ne (Submodule.span_mono (image_mono inter_subset_left)) fun heq ↦ ?_
    let ℓ : (ι → ℝ) →ₗ[ℝ] ℝ := Fintype.linearCombination ℝ ρ
    have hℓ : ∀ y, ℓ (fun i ↦ g i y) = ∑ i, ρ i * g i y := fun y ↦ by
      simp [ℓ, Fintype.linearCombination_apply, mul_comm]
    have hle : V Y' ≤ LinearMap.ker ℓ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, ⟨hyY, hy⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hℓ]
      exact le_antisymm hy (hρY y hyY)
    have : (fun i ↦ g i x₀) ∈ V Y := Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    rw [← heq] at this
    exact hne (by simpa [hℓ] using hle this)
  exact ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Y' hY' hμY' hQY' rfl

/-- A set carrying a null generated by finitely many measurable constraints: a measurable set of
full measure for every member of the null, on which the constraints admit no arbitrage. -/
theorem exists_measurableSet_noArbitrageOn (hg : ∀ i, Measurable (g i)) :
    ∃ Y : Set 𝓧, MeasurableSet Y ∧ (∀ μ ∈ constraintNull (range g), μ Yᶜ = 0) ∧
      NoArbitrageOn g Y := by
  obtain ⟨Y, hY, hμY, -, hT⟩ | ⟨_, -, -, -, h⟩ :=
    exists_measurableSet_noArbitrageOn_or_exists_sum_mul_pos hg 0
  · exact ⟨Y, hY, hμY, hT⟩
  · simp at h

/-- On a set without arbitrage, an e-variable for the null is finite. -/
theorem lt_top_of_isEVar_of_noArbitrageOn (hg : ∀ i, Measurable (g i)) (hY : NoArbitrageOn g Y)
    (hE : IsEVar E (constraintNull (range g))) {x₀ : 𝓧} (hx₀ : x₀ ∈ Y) : E x₀ < ∞ := by
  obtain ⟨α, _, x, w, -, hw, hwg, k, hk, hwk⟩ := exists_charging_family_of_noArbitrageOn hY hx₀
  have h2 : ENNReal.ofReal (w k) * E (x k) ≤ 1 :=
    (Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_univ k)).trans
      (sum_ofReal_mul_le_one_of_isEVar (forall_mem_range.2 hg) hE hw (forall_mem_range.2 hwg))
  rw [hk] at h2
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.mul_top (by simpa using hwk)] at h2
  exact ENNReal.one_ne_top (top_le_iff.1 h2)

/-- Without arbitrage on `Y`, every point of `Y` is an atom of a member of the null. -/
theorem exists_mem_constraintNull_measure_singleton_ne_zero (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) {x₀ : 𝓧} (hx₀ : x₀ ∈ Y) :
    ∃ μ ∈ constraintNull (range g), μ {x₀} ≠ 0 := by
  obtain ⟨α, _, x, w, -, hw, hwg, k, hk, hwk⟩ := exists_charging_family_of_noArbitrageOn hY hx₀
  rw [mem_simplex_iff] at hw
  refine ⟨∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k),
    (sum_smul_dirac_mem_constraintNull_iff (forall_mem_range.2 hg) hw.1).2
      ⟨hw.2, forall_mem_range.2 hwg⟩, fun h0 ↦ ?_⟩
  have h1 : ENNReal.ofReal (w k) * Measure.dirac (x k) {x₀} ≤
      (∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)) {x₀} := by
    rw [sum_apply]
    exact Finset.single_le_sum
      (f := fun j ↦ (ENNReal.ofReal (w j) • Measure.dirac (x j)) {x₀}) (fun _ _ ↦ zero_le)
      (Finset.mem_univ k)
  rw [h0, hk, Measure.dirac_apply_of_mem (mem_singleton x₀), mul_one, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at h1
  exact hwk.not_ge h1

/-- **The quasi-sure filter of a constraint null is principal**: on a set `Y` without arbitrage
that carries the null, a property holds quasi-surely, that is, almost surely under every member
of the null, exactly when it holds on `Y`. -/
theorem quasiSure_constraintNull_eq_principal (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hYμ : ∀ μ ∈ constraintNull (range g), μ Yᶜ = 0) :
    quasiSure (constraintNull (range g)) = Filter.principal Y := by
  refine Filter.ext fun s ↦ ⟨fun h x hx ↦ by_contra fun hxs ↦ ?_,
    fun h ↦ mem_quasiSure_iff.2 fun μ hμ ↦ Filter.mem_of_superset (mem_ae_iff.2 (hYμ μ hμ)) h⟩
  obtain ⟨μ, hμ, hμx⟩ := exists_mem_constraintNull_measure_singleton_ne_zero hg hY hx
  exact hμx (measure_mono_null (singleton_subset_iff.2 hxs)
    (mem_ae_iff.1 (mem_quasiSure_iff.1 h μ hμ)))

/-! ### The complete class theorem -/

/-- **The complete class theorem on a set without arbitrage**: a measurable `f` with a nonpositive
integral under every member of the null is at most `∑ i, π i * g i` on `Y`, for some nonredundant
weights `π`. -/
theorem exists_mem_nonredundantWeights_le_of_forall_integral_nonpos (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hf : Measurable f)
    (h : ∀ μ ∈ constraintNull (range g), ∫ x, f x ∂μ ≤ 0) :
    ∃ π ∈ nonredundantWeights g Y, ∀ x ∈ Y, f x ≤ ∑ i, π i * g i x :=
  exists_mem_nonredundantWeights_le_of_noArbitrageOn hY fun _ _ _ _ _ hw hwg ↦
    sum_mul_nonpos_of_forall_integral_nonpos (forall_mem_range.2 hg) hf h hw
      (forall_mem_range.2 hwg)

/-- **The complete class theorem for e-variables on a set without arbitrage**: every e-variable
for the null is at most `1 + ∑ i, π i * g i` on `Y`, for some nonredundant weights `π`. -/
theorem exists_mem_nonredundantWeights_toReal_le_of_isEVar (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hE : IsEVar E (constraintNull (range g))) :
    ∃ π ∈ nonredundantWeights g Y, ∀ x ∈ Y, (E x).toReal ≤ 1 + ∑ i, π i * g i x := by
  obtain ⟨π, hπK, hπ⟩ := exists_mem_nonredundantWeights_le_of_noArbitrageOn hY
    (f := fun x ↦ (E x).toReal - 1) fun _ _ _ _ hxY hw hwg ↦
      sum_mul_toReal_sub_one_nonpos_of_sum_ofReal_mul_le_one hw
        (sum_ofReal_mul_le_one_of_isEVar (forall_mem_range.2 hg) hE hw (forall_mem_range.2 hwg))
  exact ⟨π, hπK, fun x hx ↦ by linarith [hπ x hx]⟩

/-- **The complete class theorem for finitely many constraints** [LRR26, Theorem 3.1]: for
measurable constraints `g i` and a measurable `f`, the integral of `f` is nonpositive under every
member of the null generated by the `g i` exactly when `f ≤ ∑ i, π i * g i` quasi-surely, for
some weights `π ≥ 0`. No integrability of `f` is assumed: the integral of a function that is not
integrable is `0`. -/
theorem forall_integral_nonpos_iff_exists_ae_le (hg : ∀ i, Measurable (g i))
    (hf : Measurable f) :
    (∀ μ ∈ constraintNull (range g), ∫ x, f x ∂μ ≤ 0) ↔
      ∃ π : ι → ℝ≥0,
        f ≤ᶠ[quasiSure (constraintNull (range g))] fun x ↦ ∑ i, (π i : ℝ) * g i x := by
  refine ⟨fun h ↦ ?_, fun ⟨π, hπ⟩ μ hμ ↦ ?_⟩
  · obtain ⟨Y, -, hYμ, hY⟩ := exists_measurableSet_noArbitrageOn hg
    obtain ⟨π, hπK, hπ⟩ := exists_mem_nonredundantWeights_le_of_forall_integral_nonpos hg hY hf h
    refine ⟨fun i ↦ (π i).toNNReal, ?_⟩
    rw [quasiSure_constraintNull_eq_principal hg hY hYμ]
    exact Filter.eventually_principal.2 fun x hx ↦ by
      simpa only [Real.coe_toNNReal _ (hπK.1 _)] using hπ x hx
  · by_cases hfi : Integrable f μ
    · exact (integral_mono_ae hfi (integrable_sum_mul_of_mem_constraintNull hμ _)
        (ae_of_eventually_quasiSure hπ hμ)).trans
        (integral_sum_mul_nonpos_of_mem_constraintNull hμ fun i ↦ (π i).coe_nonneg)
    · rw [integral_undef hfi]

/-- **The complete class theorem for e-variables on a set without arbitrage** [LRR26,
Theorem 3.1]: on a set `Y` without arbitrage that carries the null, every e-variable for the null
is at most a bet `1 + ∑ i, π i * g i`. -/
theorem IsEVar.exists_mem_constraintBets_le_of_noArbitrageOn (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hYμ : ∀ μ ∈ constraintNull (range g), μ Yᶜ = 0)
    (hE : IsEVar E (constraintNull (range g))) :
    ∃ π ∈ constraintBets g, ∀ x ∈ Y, E x ≤ ENNReal.ofReal (1 + ∑ i, (π i : ℝ) * g i x) := by
  obtain ⟨π, hπK, hπ⟩ := exists_mem_nonredundantWeights_toReal_le_of_isEVar hg hY hE
  refine ⟨fun i ↦ (π i).toNNReal, toNNReal_mem_constraintBets hYμ hπK.1 fun x hx ↦
    ENNReal.toReal_nonneg.trans (hπ x hx), fun x hx ↦ ?_⟩
  rw [← ENNReal.ofReal_toReal (lt_top_of_isEVar_of_noArbitrageOn hg hY hE hx).ne]
  simpa only [Real.coe_toNNReal _ (hπK.1 _)] using ENNReal.ofReal_le_ofReal (hπ x hx)

/-- **The complete class theorem for e-variables** [LRR26, Theorem 3.1]: every e-variable for the
null generated by finitely many measurable constraints `g i` is quasi-surely dominated by a bet
`1 + ∑ i, π i * g i`. -/
theorem IsEVar.exists_mem_constraintBets_ae_le (hg : ∀ i, Measurable (g i))
    (hE : IsEVar E (constraintNull (range g))) :
    ∃ π ∈ constraintBets g, E ≤ᶠ[quasiSure (constraintNull (range g))]
      fun x ↦ ENNReal.ofReal (1 + ∑ i, (π i : ℝ) * g i x) := by
  obtain ⟨Y, -, hYμ, hY⟩ := exists_measurableSet_noArbitrageOn hg
  obtain ⟨π, hπ, hπY⟩ := hE.exists_mem_constraintBets_le_of_noArbitrageOn hg hY hYμ
  refine ⟨π, hπ, ?_⟩
  rw [quasiSure_constraintNull_eq_principal hg hY hYμ]
  exact Filter.eventually_principal.2 hπY

/-- **The e-variables for a null generated by finitely many constraints** [LRR26, Theorem 3.1]:
for measurable constraints `g i`, the e-variables for the null are the measurable functions that
are quasi-surely dominated by a bet `1 + ∑ i, π i * g i`. -/
theorem isEVar_constraintNull_iff (hg : ∀ i, Measurable (g i)) :
    IsEVar E (constraintNull (range g)) ↔ Measurable E ∧ ∃ π ∈ constraintBets g,
      E ≤ᶠ[quasiSure (constraintNull (range g))]
        fun x ↦ ENNReal.ofReal (1 + ∑ i, (π i : ℝ) * g i x) :=
  ⟨fun hE ↦ ⟨hE.measurable, hE.exists_mem_constraintBets_ae_le hg⟩, fun ⟨hEm, _, hπ, hEπ⟩ ↦
    (isEVar_ofReal_one_add_of_mem_constraintBets hg hπ).mono_ae hEm hEπ⟩

/-! ### Completion into a member of the null -/

/-- **The shifted constraints admit no arbitrage**: on a set `Y` without arbitrage that carries
the null, let `μ` be a finite measure carried by `Y` that integrates the constraints and under
which every e-variable has mean at most `c`, for some `c < 1`. Then the constraints shifted by
their means under `μ` divided by the mass `1 - μ 𝓧` that `μ` lacks,
`g i + (∫ g i ∂μ) / (1 - μ 𝓧)`, admit no arbitrage on `Y`. -/
theorem noArbitrageOn_add_integral_div_of_lintegral_le (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hYμ : ∀ ν ∈ constraintNull (range g), ν Yᶜ = 0)
    {μ : Measure 𝓧} [IsFiniteMeasure μ] (hμY : μ Yᶜ = 0) (hgμ : ∀ i, Integrable (g i) μ)
    {c : ℝ≥0∞} (hc : c < 1)
    (hμE : ∀ E, IsEVar E (constraintNull (range g)) → ∫⁻ x, E x ∂μ ≤ c) :
    NoArbitrageOn (fun i x ↦ g i x + (∫ y, g i y ∂μ) / (1 - μ.real univ)) Y := by
  set m := 1 - μ.real univ with hm_def
  refine noArbitrageOn_iff.2 fun π hπ hπY ↦ ?_
  set σ := (∑ i, π i * ∫ x, g i x ∂μ) / m with hσ_def
  have hσa : ∑ i, π i * ((∫ x, g i x ∂μ) / m) = σ := by
    simp only [hσ_def, Finset.sum_div, mul_div_assoc]
  have hπg : ∀ x ∈ Y, -σ ≤ ∑ i, π i * g i x := by
    intro x hx
    have := hπY x hx
    simp only [mul_add, Finset.sum_add_distrib, hσa] at this
    linarith
  rcases lt_or_ge 0 σ with hσ | hσ
  · -- a positive deficit would be paid by the mass that `μ` lacks: the bet with weights `π / σ`
    -- would have mean `1` under `μ`
    exfalso
    have hsum : ∀ x, ∑ i, π i / σ * g i x = (∑ i, π i * g i x) / σ := fun x ↦ by
      simp only [Finset.sum_div, div_mul_eq_mul_div]
    have hEY : ∀ x ∈ Y, 0 ≤ 1 + ∑ i, π i / σ * g i x := by
      intro x hx
      rw [hsum]
      have : -1 ≤ (∑ i, π i * g i x) / σ := by
        rw [le_div_iff₀ hσ]
        linarith [hπg x hx]
      linarith
    have hcoe : ∀ i, ((π i / σ).toNNReal : ℝ) = π i / σ := fun i ↦
      Real.coe_toNNReal _ (div_nonneg (hπ i) hσ.le)
    have h1 := hμE _ (isEVar_ofReal_one_add_of_mem_constraintBets hg
      (toNNReal_mem_constraintBets hYμ (fun i ↦ div_nonneg (hπ i) hσ.le) hEY))
    simp only [hcoe] at h1
    rw [lintegral_ofReal_one_add_sum_mul hgμ _
      (Filter.eventually_of_mem (mem_ae_iff.2 hμY) hEY)] at h1
    have h2 : ∑ i, π i / σ * ∫ x, g i x ∂μ = m := by
      have : ∑ i, π i / σ * ∫ x, g i x ∂μ = (∑ i, π i * ∫ x, g i x ∂μ) / σ := by
        simp only [Finset.sum_div, div_mul_eq_mul_div]
      rw [this, hσ_def, div_div_cancel₀ (by
        intro h0
        rw [h0, zero_div] at hσ_def
        exact hσ.ne' hσ_def)]
    rw [h2, hm_def, add_sub_cancel, ENNReal.ofReal_one] at h1
    exact lt_irrefl _ (h1.trans_lt hc)
  · -- no deficit: the combination is nonnegative, hence zero, on `Y`
    have h0 : ∀ x ∈ Y, 0 ≤ ∑ i, π i * g i x := fun x hx ↦ by linarith [hπg x hx]
    have hzero := noArbitrageOn_iff.1 hY π hπ h0
    have hb : ∑ i, π i * ∫ x, g i x ∂μ = 0 := by
      have hgi : ∀ i, Integrable (fun x ↦ π i * g i x) μ := fun i ↦ (hgμ i).const_mul (π i)
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun i _ ↦ hgi i]
      exact integral_eq_zero_of_ae (Filter.eventually_of_mem (mem_ae_iff.2 hμY) hzero)
    have hσ0 : σ = 0 := by rw [hσ_def, hb, zero_div]
    intro x hx
    simp only [mul_add, Finset.sum_add_distrib, hσa, hσ0, add_zero]
    exact hzero x hx

/-- **Completion by a finitely supported measure**: on a nonempty set `Y` without arbitrage that
carries the null, a finite measure carried by `Y` that integrates the constraints and under which
every e-variable has mean at most `c`, for some `c < 1`, becomes a member of the null once a
finitely supported measure is added. It rests on the complete class theorem [LRR26, Theorem 3.1],
and follows [EVR26, Note 20]. -/
theorem exists_add_sum_smul_dirac_mem_constraintNull (hg : ∀ i, Measurable (g i))
    (hY : NoArbitrageOn g Y) (hYμ : ∀ ν ∈ constraintNull (range g), ν Yᶜ = 0)
    (hYne : Y.Nonempty) {μ : Measure 𝓧} [IsFiniteMeasure μ] (hμY : μ Yᶜ = 0)
    (hgμ : ∀ i, Integrable (g i) μ) {c : ℝ≥0∞} (hc : c < 1)
    (hμE : ∀ E, IsEVar E (constraintNull (range g)) → ∫⁻ x, E x ∂μ ≤ c) :
    ∃ (α : Type) (_ : Fintype α) (x : α → 𝓧) (w : α → ℝ), (∀ k, 0 ≤ w k) ∧
      μ + ∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k) ∈ constraintNull (range g) := by
  classical
  set r := μ.real univ with hr_def
  set m := 1 - r with hm_def
  have hm0 : 0 < m := by
    have h1 := hμE 1 (isEVar_one fun _ hν ↦
      (isProbabilityMeasure_of_mem_constraintNull hν).measure_univ.le)
    simp only [Pi.one_apply, lintegral_one] at h1
    have h2 : r < 1 := by
      rw [hr_def, measureReal_def]
      exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using h1.trans_lt hc)
    linarith
  -- the complete class theorem, applied to the constraints shifted by multiples of their means
  -- under `μ`, gives a finitely supported law under which the shifted constraints have
  -- nonpositive means
  obtain ⟨x₀, hx₀⟩ := hYne
  obtain ⟨α, _, x, w, -, hw, hwz, -⟩ := exists_charging_family_of_noArbitrageOn
    (noArbitrageOn_add_integral_div_of_lintegral_le hg hY hYμ hμY hgμ hc hμE) hx₀
  obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hw
  refine ⟨α, inferInstance, x, fun k ↦ m * w k, fun k ↦ mul_nonneg hm0.le (hw0 k), ?_⟩
  have hdirac : ∀ (f : 𝓧 → ℝ), Measurable f → ∀ k ∈ Finset.univ,
      Integrable f (ENNReal.ofReal (m * w k) • Measure.dirac (x k)) := fun f hf k _ ↦
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine mem_constraintNull_range_iff.2 ⟨⟨?_⟩, fun i ↦ ?_⟩
  · simp only [add_apply, sum_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    -- the added mass is `m = 1 - r`, the mass that `μ` lacks
    have hmass : ∑ k, ENNReal.ofReal (m * w k) = ENNReal.ofReal m := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ mul_nonneg hm0.le (hw0 k), ← Finset.mul_sum,
        hw1, mul_one]
    rw [hmass, ← ofReal_measureReal, ← hr_def, ← ENNReal.ofReal_add measureReal_nonneg hm0.le,
      hm_def, add_sub_cancel, ENNReal.ofReal_one]
  · refine ⟨(hgμ i).add_measure (integrable_finsetSum_measure.2 (hdirac _ (hg i))), ?_⟩
    rw [integral_add_measure (hgμ i) (integrable_finsetSum_measure.2 (hdirac _ (hg i))),
      integral_sum_smul_dirac (fun k ↦ mul_nonneg hm0.le (hw0 k)) (hg i).stronglyMeasurable]
    simp_rw [smul_eq_mul]
    have h1 := hwz i
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul] at h1
    have h2 : ∑ k, m * w k * g i (x k) = m * ∑ k, w k * g i (x k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have h3 : m * ((∫ x, g i x ∂μ) / m) = ∫ x, g i x ∂μ := by
      field_simp
    rw [h2]
    nlinarith

end ProbabilityTheory
