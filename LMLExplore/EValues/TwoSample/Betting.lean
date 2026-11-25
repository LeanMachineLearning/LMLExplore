/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.ConstraintNull.Sequential
public import LMLExplore.EValues.Null.Involution
public import LMLExplore.Probability.Martingale.ExactVille

/-!
# Two-sample and invariance testing by betting

Let `T` be a measurable map of a space `𝓧`, typically an involution, and let `Z k` be observations
in `𝓧`, each measurable for `ℱ (k + 1)` for a filtration `ℱ`. The null of invariance is the
sequential constraint null `sequentialConstraintNull (invarianceConstraints T) Z ℱ` of the
constraints `g - g ∘ T` of invariance, for the bounded measurable `g`: the probability measures
under which, given the past `ℱ k`, `g (Z k)` and `g (T (Z k))` have the same conditional
expectation for every bounded measurable `g`. Its one-step null is the set of the laws invariant
under `T` (`ProbabilityTheory.invariantLaws_eq_constraintNull`), and it is the conditional form of
invariance: under one of its members, the pairs `(ω, Z k ω)` and `(ω, T (Z k ω))` have the same
law on `(Ω, ℱ k) × 𝓧`
(`ProbabilityTheory.lintegral_comp_eq_of_mem_sequentialConstraintNull_invarianceConstraints`). It
contains every law under which each observation has a conditional distribution given the past that
is invariant under `T`
(`ProbabilityTheory.sequentialNull_invariantLaws_subset_sequentialConstraintNull`), and the laws of
independent observations with invariant laws
(`ProbabilityTheory.infinitePi_mem_sequentialConstraintNull_invarianceConstraints`). For the swap
`T (x, y) = (y, x)` of the pairs `Z k = (X k, Y k)`, these include the two-sample null of
[SR23, (2)], independent pairs of independent observations with a common law at each round, which
may change with the round as in [SR23, §5.1]
(`ProbabilityTheory.infinitePi_prod_self_mem_sequentialConstraintNull_invarianceConstraints_swap`).
For `T z = -z` it is the null of conditionally symmetric observations [SR23, §5.2].

A bettor chooses from the past, before round `k`, a factor `r k ω : 𝓧 → ℝ≥0∞` and multiplies the
wealth by `r k ω (Z k ω)`. When `r k ω z + r k ω (T z) = 2` everywhere, as for the factors
`1 + v k ω z` of payoffs `v k ω` that are antisymmetric (`v k ω (T z) = -v k ω z`) and at least
`-1`, each factor is an exact conditional e-variable given the past
(`ProbabilityTheory.isExactCondEVar_invarianceConstraints_of_add_eq`), and the wealth is a test
martingale for the null of invariance
(`ProbabilityTheory.isTestMartingale_prod_invarianceConstraints_of_add_eq`); with
`r k ω z + r k ω (T z) ≤ 2` it is a test supermartingale. The tests of [SR23] bet
`v k ω z = c k ω * (g k ω z - g k ω (T z))` with predictable functions `g k ω`, with values in
`[-1/2, 1/2]` and chosen from a class by a prediction strategy, and predictable bets
`c k ω ∈ [-1, 1]`
(`ProbabilityTheory.isTestMartingale_prod_ofReal_one_add_mul_sub_invarianceConstraints`): whatever
the prediction and betting strategies, their wealth is a test martingale, and the test that rejects
as soon as the wealth reaches `α⁻¹` has type I error at most `α`, uniformly over the null
[SR23, Theorem 1 (eq. (13)), Corollary 1]
(`ProbabilityTheory.measure_exists_inv_le_prod_ofReal_one_add_mul_sub_le`).

For finitely many fixed payoffs `g i - g i ∘ T`, this is the betting wealth against the equality
constraints of a sequential constraint null
(`ProbabilityTheory.isTestMartingale_prod_ofReal_one_add_sum_mul`).
The payoffs here are chosen from the past, so that the constraint bet on changes with the round:
their conditional means vanish because the conditional law of `Z k` is invariant, not because of
finitely many constraints.

## Main statements

* `ProbabilityTheory.lintegral_comp_eq_of_mem_sequentialConstraintNull_invarianceConstraints`:
  given the past, `Z k` and `T (Z k)` have the same law under the null of invariance.
* `ProbabilityTheory.isTestSupermartingale_prod_invarianceConstraints_of_add_le`,
  `ProbabilityTheory.isTestMartingale_prod_invarianceConstraints_of_add_eq`: betting against the
  null of invariance with factors chosen from the past.
* `ProbabilityTheory.isTestMartingale_prod_ofReal_one_add_mul_sub_invarianceConstraints`: the
  wealth of the tests of [SR23] is a test martingale, for every prediction and betting strategy.
* `ProbabilityTheory.measure_exists_inv_le_prod_ofReal_one_add_mul_sub_le`: their type I error is
  at most `α` [SR23, Theorem 1, Corollary 1].
* `ProbabilityTheory.sequentialNull_invariantLaws_subset_sequentialConstraintNull`,
  `ProbabilityTheory.infinitePi_mem_sequentialConstraintNull_invarianceConstraints`,
  `ProbabilityTheory.infinitePi_prod_self_mem_sequentialConstraintNull_invarianceConstraints_swap`:
  members of the null of invariance.

## References

* [SR23] S. Shekhar and A. Ramdas, *Nonparametric two-sample testing by betting*, IEEE Trans. Inf.
  Theory 70 (2024), arXiv:2112.09162: (2), Theorem 1, §5.1 and §5.2, Corollary 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  [MeasurableSpace 𝓨] {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → 𝓧} {T : 𝓧 → 𝓧} {P : Measure Ω}

/-! ### The null of invariance -/

section Null

variable {k : ℕ} {s : Set Ω}

/-- **The null of invariance.** Under a member of the sequential constraint null of the
constraints of invariance under a measurable `T`, the law of a measurable observation `Z k` on an
`ℱ k`-measurable set `s` is invariant under `T`. -/
theorem map_map_restrict_eq_of_mem_sequentialConstraintNull_invarianceConstraints
    (hT : Measurable T) (hP : P ∈ sequentialConstraintNull (invarianceConstraints T) Z ℱ)
    (hZ : Measurable (Z k))
    (hs : MeasurableSet[ℱ k] s) :
    ((P.restrict s).map (Z k)).map T = (P.restrict s).map (Z k) := by
  have := isFiniteMeasure_of_mem_sequentialConstraintNull hP
  refine (map_eq_iff_forall_integral_eq_zero hT).2 fun f hf ↦ ?_
  rw [integral_map hZ.aemeasurable
    (measurable_of_mem_invarianceConstraints hT hf).aestronglyMeasurable]
  exact setIntegral_eq_zero_of_mem_sequentialConstraintNull hP hf
    (neg_mem_invarianceConstraints hf) hs

/-- **Given the past, `Z k` and `T (Z k)` have the same law.** Under a member of the sequential
constraint null of the constraints of invariance under a measurable `T`, for a measurable
observation `Z k` and every `h : Ω → 𝓧 → ℝ≥0∞` jointly measurable for `ℱ k` and `𝓧`,
`∫⁻ ω, h ω (T (Z k ω)) ∂P = ∫⁻ ω, h ω (Z k ω) ∂P`: the pairs `(ω, Z k ω)` and `(ω, T (Z k ω))`
have the same law on `(Ω, ℱ k) × 𝓧`. -/
theorem lintegral_comp_eq_of_mem_sequentialConstraintNull_invarianceConstraints
    (hT : Measurable T) (hP : P ∈ sequentialConstraintNull (invarianceConstraints T) Z ℱ)
    (hZ : Measurable (Z k))
    {h : Ω → 𝓧 → ℝ≥0∞} (hh : Measurable[(ℱ k).prod m𝓧] (Function.uncurry h)) :
    ∫⁻ ω, h ω (T (Z k ω)) ∂P = ∫⁻ ω, h ω (Z k ω) ∂P := by
  have := isFiniteMeasure_of_mem_sequentialConstraintNull hP
  -- the σ-algebra on `Ω × 𝓧` is the one built from `ℱ k`, not from `mΩ`
  let : MeasurableSpace (Ω × 𝓧) := (ℱ k).prod m𝓧
  have hφ : Measurable fun ω ↦ (ω, Z k ω) := (measurable_id'' (ℱ.le k)).prodMk hZ
  have hψ : Measurable fun ω ↦ (ω, T (Z k ω)) :=
    (measurable_id'' (ℱ.le k)).prodMk (hT.comp hZ)
  -- the two pairs have the same law: they agree on the rectangles
  have hlaw : P.map (fun ω ↦ (ω, T (Z k ω))) = P.map (fun ω ↦ (ω, Z k ω)) := by
    refine Measure.ext_prod (mα := ℱ k) fun {s t} hs ht ↦ ?_
    have h := congrArg (· t)
      (map_map_restrict_eq_of_mem_sequentialConstraintNull_invarianceConstraints hT hP hZ hs)
    simp only [Measure.map_apply hT ht, Measure.map_apply hZ ht, Measure.map_apply hZ (hT ht),
      Measure.restrict_apply (hZ (hT ht)), Measure.restrict_apply (hZ ht)] at h
    rw [Set.preimage_preimage] at h
    rw [Measure.map_apply hψ (hs.prod ht), Measure.map_apply hφ (hs.prod ht),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.preimage_id', inter_comm s, inter_comm s, h]
  have h₁ := lintegral_map (μ := P) hh hψ
  have h₂ := lintegral_map (μ := P) hh hφ
  simp only [Function.uncurry_apply_pair] at h₁ h₂
  rw [← h₁, ← h₂, hlaw]

/-- Under the null of invariance under a measurable `T`, for a measurable observation `Z k`, an
`ℱ k`-measurable set `s` and `r : Ω → 𝓧 → ℝ≥0∞` jointly measurable for `ℱ k` and `𝓧`, the
integral of `r ω (Z k ω) + r ω (T (Z k ω))` on `s` is twice that of `r ω (Z k ω)`. -/
theorem setLIntegral_add_comp_of_mem_sequentialConstraintNull_invarianceConstraints
    (hT : Measurable T) (hP : P ∈ sequentialConstraintNull (invarianceConstraints T) Z ℱ)
    (hZ : Measurable (Z k))
    {r : Ω → 𝓧 → ℝ≥0∞} (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r))
    (hs : MeasurableSet[ℱ k] s) :
    ∫⁻ ω in s, (r ω (Z k ω) + r ω (T (Z k ω))) ∂P = 2 * ∫⁻ ω in s, r ω (Z k ω) ∂P := by
  -- `indicator_apply` below needs decidable membership in `s`
  classical
  -- `r` on `s`, as a function jointly measurable for `ℱ k` and `𝓧`
  set h : Ω → 𝓧 → ℝ≥0∞ := fun ω z ↦ s.indicator (fun ω' ↦ r ω' z) ω
  have hh : Measurable[(ℱ k).prod m𝓧] (Function.uncurry h) := by
    have : Function.uncurry h = (s ×ˢ univ).indicator (Function.uncurry r) := by
      ext ⟨ω, z⟩
      by_cases hω : ω ∈ s <;> simp [h, hω]
    rw [this]
    exact hr.indicator (hs.prod MeasurableSet.univ)
  have hsym : ∫⁻ ω in s, r ω (T (Z k ω)) ∂P = ∫⁻ ω in s, r ω (Z k ω) ∂P := by
    rw [← lintegral_indicator (ℱ.le k s hs), ← lintegral_indicator (ℱ.le k s hs)]
    simpa only [h, indicator_apply] using
      lintegral_comp_eq_of_mem_sequentialConstraintNull_invarianceConstraints hT hP hZ hh
  rw [lintegral_add_left (hr.comp_prodMk_of_le (ℱ.le k) hZ), hsym, two_mul]

/-- **One round of betting under the null of invariance.** Under the null of invariance under a
measurable `T`, for a measurable observation `Z k` and `r : Ω → 𝓧 → ℝ≥0∞` jointly measurable
for `ℱ k` and `𝓧` with `r ω z + r ω (T z) ≤ 2` everywhere, `r ω (Z k ω)` is a conditional
e-variable given `ℱ k`. -/
theorem isCondEVar_invarianceConstraints_of_add_le (hT : Measurable T) (hZ : Measurable (Z k))
    {r : Ω → 𝓧 → ℝ≥0∞} (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r))
    (h : ∀ ω z, r ω z + r ω (T z) ≤ 2) :
    IsCondEVar (fun ω ↦ r ω (Z k ω)) (ℱ k)
      (sequentialConstraintNull (invarianceConstraints T) Z ℱ) := by
  refine ⟨hr.comp_prodMk_of_le (ℱ.le k) hZ, fun P hP s hs ↦ ?_⟩
  have h2 : 2 * ∫⁻ ω in s, r ω (Z k ω) ∂P ≤ 2 * P s := by
    rw [← setLIntegral_add_comp_of_mem_sequentialConstraintNull_invarianceConstraints hT hP hZ hr
      hs]
    calc ∫⁻ ω in s, (r ω (Z k ω) + r ω (T (Z k ω))) ∂P ≤ ∫⁻ _ in s, 2 ∂P :=
          lintegral_mono fun ω ↦ h ω (Z k ω)
      _ = 2 * P s := by rw [setLIntegral_const]
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h2

/-- **One round of betting under the null of invariance, exact case.** Under the null of
invariance under a measurable `T`, for a measurable observation `Z k` and `r : Ω → 𝓧 → ℝ≥0∞`
jointly measurable for `ℱ k` and `𝓧` with `r ω z + r ω (T z) = 2` everywhere, `r ω (Z k ω)` is
an exact conditional e-variable given `ℱ k`. -/
theorem isExactCondEVar_invarianceConstraints_of_add_eq (hT : Measurable T)
    (hZ : Measurable (Z k)) {r : Ω → 𝓧 → ℝ≥0∞}
    (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r)) (h : ∀ ω z, r ω z + r ω (T z) = 2) :
    IsExactCondEVar (fun ω ↦ r ω (Z k ω)) (ℱ k)
      (sequentialConstraintNull (invarianceConstraints T) Z ℱ) := by
  refine ⟨hr.comp_prodMk_of_le (ℱ.le k) hZ, fun P hP s hs ↦ ?_⟩
  have h2 : 2 * ∫⁻ ω in s, r ω (Z k ω) ∂P = 2 * P s := by
    rw [← setLIntegral_add_comp_of_mem_sequentialConstraintNull_invarianceConstraints hT hP hZ hr
      hs]
    simp [h]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h2

end Null

/-! ### Betting against the null of invariance -/

/-- **Betting against the null of invariance gives test supermartingales.** Let `T` be
measurable, let `Z k` be `ℱ (k + 1)`-measurable, and let `r k : Ω → 𝓧 → ℝ≥0∞` be jointly
measurable for `ℱ k` and `𝓧` with `r k ω z + r k ω (T z) ≤ 2` everywhere. Then
`∏ k < n, r k ω (Z k ω)` is a test supermartingale for the null of invariance under `T`. -/
theorem isTestSupermartingale_prod_invarianceConstraints_of_add_le (hT : Measurable T)
    (hZ : ∀ k, Measurable[ℱ (k + 1)] (Z k)) {r : ℕ → Ω → 𝓧 → ℝ≥0∞}
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (h : ∀ k ω z, r k ω z + r k ω (T z) ≤ 2) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ Finset.range n, r k ω (Z k ω)) ℱ
      (sequentialConstraintNull (invarianceConstraints T) Z ℱ) :=
  isTestSupermartingale_prod
    (fun _ hP ↦ (isProbabilityMeasure_of_mem_sequentialConstraintNull hP).measure_univ.le)
    (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hZ k)) fun k ↦
      isCondEVar_invarianceConstraints_of_add_le hT ((hZ k).mono (ℱ.le _) le_rfl) (hr k) (h k)

/-- **Betting against the null of invariance gives test martingales** [SR23, §5.2]. Let `T` be
measurable, let `Z k` be `ℱ (k + 1)`-measurable, and let `r k : Ω → 𝓧 → ℝ≥0∞` be jointly
measurable for `ℱ k` and `𝓧` with `r k ω z + r k ω (T z) = 2` everywhere, as the factors
`1 + v k ω z` of payoffs `v k ω` that are antisymmetric (`v k ω (T z) = -v k ω z`) and at least
`-1`. Then `∏ k < n, r k ω (Z k ω)` is a test martingale for the null of invariance under `T`. -/
theorem isTestMartingale_prod_invarianceConstraints_of_add_eq (hT : Measurable T)
    (hZ : ∀ k, Measurable[ℱ (k + 1)] (Z k)) {r : ℕ → Ω → 𝓧 → ℝ≥0∞}
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (h : ∀ k ω z, r k ω z + r k ω (T z) = 2) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ Finset.range n, r k ω (Z k ω)) ℱ
      (sequentialConstraintNull (invarianceConstraints T) Z ℱ) :=
  isTestMartingale_prod
    (fun _ hP ↦ (isProbabilityMeasure_of_mem_sequentialConstraintNull hP).measure_univ.le)
    (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hZ k)) fun k ↦
      isExactCondEVar_invarianceConstraints_of_add_eq hT ((hZ k).mono (ℱ.le _) le_rfl) (hr k)
        (h k)

/-- **The wealth of the tests of Shekhar and Ramdas is a test martingale** [SR23, §2 and §5.2].
Let `T` be a measurable involution and `Z k` be `ℱ (k + 1)`-measurable. For predictable bets
`c k ω ∈ [-1, 1]` and predictable functions `g k ω : 𝓧 → ℝ`, jointly measurable for `ℱ k` and
`𝓧`, with `|g k ω z - g k ω (T z)| ≤ 1` (which holds when `g k ω` has values in `[-1/2, 1/2]`),
the wealth `∏ k < n, (1 + c k ω * (g k ω (Z k ω) - g k ω (T (Z k ω))))` is a test martingale for
the sequential constraint null of the constraints of invariance under `T`. The two-sample test is
the case of the swap `T (x, y) = (y, x)`, and the test of symmetry the case `T z = -z`. -/
theorem isTestMartingale_prod_ofReal_one_add_mul_sub_invarianceConstraints (hT : Measurable T)
    (hTT : Function.Involutive T) (hZ : ∀ k, Measurable[ℱ (k + 1)] (Z k)) {c : ℕ → Ω → ℝ}
    (hc : ∀ k, Measurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {g : ℕ → Ω → 𝓧 → ℝ}
    (hg : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (g k)))
    (hg1 : ∀ k ω z, |g k ω z - g k ω (T z)| ≤ 1) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ Finset.range n,
        ENNReal.ofReal (1 + c k ω * (g k ω (Z k ω) - g k ω (T (Z k ω))))) ℱ
      (sequentialConstraintNull (invarianceConstraints T) Z ℱ) := by
  have hv : ∀ k, Measurable[(ℱ k).prod m𝓧]
      (Function.uncurry fun ω z ↦ c k ω * (g k ω z - g k ω (T z))) :=
    fun k ↦ ((hc k).comp measurable_fst).mul
      ((hg k).sub ((hg k).comp (measurable_fst.prodMk (hT.comp measurable_snd))))
  refine isTestMartingale_prod_invarianceConstraints_of_add_eq hT hZ
    (r := fun k ω z ↦ ENNReal.ofReal (1 + c k ω * (g k ω z - g k ω (T z))))
    (fun k ↦ (measurable_const.add (hv k)).ennreal_ofReal) fun k ω z ↦ ?_
  -- the factor is an exact e-variable for the laws invariant under `T`
  refine ((isExactEVar_invariantLaws_iff hT hTT).1 (isExactEVar_invariantLaws_ofReal_one_add hT
    (hv k).of_uncurry_left (fun z ↦ by rw [hTT z]; ring) fun z ↦ ?_)).2 z
  refine neg_le_of_abs_le ?_
  rw [abs_mul, ← one_mul 1]
  exact mul_le_mul (hc1 k ω) (hg1 k ω z) (abs_nonneg _) zero_le_one

/-- **The tests of Shekhar and Ramdas have level `α`** [SR23, Theorem 1 (eq. (13)),
Corollary 1]. In the setting of
`ProbabilityTheory.isTestMartingale_prod_ofReal_one_add_mul_sub_invarianceConstraints`, under
every member of the sequential constraint null of the constraints of invariance under `T`, the
wealth reaches `α⁻¹` with probability at most `α`, whatever the prediction and betting
strategies. -/
theorem measure_exists_inv_le_prod_ofReal_one_add_mul_sub_le (hT : Measurable T)
    (hTT : Function.Involutive T) (hZ : ∀ k, Measurable[ℱ (k + 1)] (Z k)) {c : ℕ → Ω → ℝ}
    (hc : ∀ k, Measurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {g : ℕ → Ω → 𝓧 → ℝ}
    (hg : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (g k)))
    (hg1 : ∀ k ω z, |g k ω z - g k ω (T z)| ≤ 1)
    (hP : P ∈ sequentialConstraintNull (invarianceConstraints T) Z ℱ) (α : ℝ≥0∞) :
    P {ω | ∃ n, α⁻¹ ≤ ∏ k ∈ Finset.range n,
        ENNReal.ofReal (1 + c k ω * (g k ω (Z k ω) - g k ω (T (Z k ω))))} ≤ α :=
  (isTestMartingale_prod_ofReal_one_add_mul_sub_invarianceConstraints hT hTT hZ hc hc1 hg
    hg1).isTestSupermartingale.measure_exists_inv_le_le hP α

/-! ### Members of the null of invariance -/

/-- **Invariant conditional laws.** For a measurable `T` and measurable observations, every member
of the sequential null of the laws invariant under `T`, under which every observation has a
conditional distribution given the past that is invariant under `T`, belongs to the sequential
constraint null of the constraints `g - g ∘ T` of invariance. -/
theorem sequentialNull_invariantLaws_subset_sequentialConstraintNull (hT : Measurable T)
    (hZ : ∀ k, Measurable (Z k)) :
    sequentialNull (fun _ _ ↦ invariantLaws T) Z ℱ ⊆
      sequentialConstraintNull (invarianceConstraints T) Z ℱ := by
  intro P hP
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  rw [invariantLaws_eq_constraintNull hT] at hP
  exact mem_sequentialConstraintNull_of_mem_sequentialNull
    (fun f hf ↦ measurable_of_mem_invarianceConstraints hT hf) hP fun f hf k ↦
      (integrable_map_measure (measurable_of_mem_invarianceConstraints hT hf).aestronglyMeasurable
        (hZ k).aemeasurable).1 (integrable_of_mem_invarianceConstraints hT hf)

/-- **Independent observations with invariant laws.** For a measurable `T`, the law
`Measure.infinitePi μ` of a sequence of independent observations on `ℕ → 𝓧` with laws `μ k`
invariant under `T` belongs to the sequential constraint null of the constraints of invariance,
for the coordinates and the filtration `Filtration.naturalLT` of the strict past. -/
theorem infinitePi_mem_sequentialConstraintNull_invarianceConstraints (hT : Measurable T)
    {μ : ℕ → Measure 𝓧} [∀ k, IsProbabilityMeasure (μ k)] (hμ : ∀ k, (μ k).map T = μ k) :
    Measure.infinitePi μ ∈ sequentialConstraintNull (invarianceConstraints T)
      (fun k (ω : ℕ → 𝓧) ↦ ω k) (Filtration.naturalLT (fun k (ω : ℕ → 𝓧) ↦ ω k)
        measurable_pi_apply) :=
  infinitePi_mem_sequentialConstraintNull (fun _ hf ↦ measurable_of_mem_invarianceConstraints hT hf)
    fun k ↦ invariantLaws_eq_constraintNull hT ▸ mem_invariantLaws_iff.2 ⟨inferInstance, hμ k⟩

/-- **The two-sample null is in the null of invariance under the swap** [SR23, (2) and §5.1]. For
probability measures `μ k` on `𝓨`, the law of independent pairs `(X k, Y k)` of independent
observations with the common law `μ k`, which may change with the round, belongs to the sequential
constraint null of the constraints of invariance under the swap `(x, y) ↦ (y, x)`, for the
coordinates and the filtration `Filtration.naturalLT` of the strict past. -/
theorem infinitePi_prod_self_mem_sequentialConstraintNull_invarianceConstraints_swap
    {μ : ℕ → Measure 𝓨} [∀ k, IsProbabilityMeasure (μ k)] :
    Measure.infinitePi (fun k ↦ (μ k).prod (μ k)) ∈
      sequentialConstraintNull (invarianceConstraints Prod.swap) (fun k (ω : ℕ → 𝓨 × 𝓨) ↦ ω k)
        (Filtration.naturalLT (fun k (ω : ℕ → 𝓨 × 𝓨) ↦ ω k) measurable_pi_apply) :=
  infinitePi_mem_sequentialConstraintNull_invarianceConstraints measurable_swap fun _ ↦
    map_eq_of_mem_invariantLaws (prod_mem_invariantLaws_swap_iff.2 rfl)

end ProbabilityTheory
