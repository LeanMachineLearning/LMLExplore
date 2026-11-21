/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.Martingale.TestSupermartingale
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.Convex.ENNReal
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import LMLExplore.Probability.Martingale.OptionalStopping
import LMLExplore.Probability.ProductMeasure

/-!
# Test martingales for convex i.i.d. nulls have no power against the span of the null

The observations are the coordinates of `ℕ → 𝓧`. For a set `S₁` of probability measures on `𝓧`,
the i.i.d. null is the set of the laws `Measure.infinitePi fun _ ↦ P` with `P ∈ S₁`. Zhang, Ramdas
and Wang conjecture that if a test martingale for the i.i.d. null has power one against the i.i.d.
law of `Q₁`, then `Q₁` lies outside the linear span of `S₁`, perhaps under additional conditions
[ZRW24, §7].

For a convex `S₁` this holds [EVR26, Note 03, Theorem 1], for every filtration each of whose
σ-algebras depends on finitely many observations. Let `Q₁` be a probability measure in the linear
span of `S₁`, written as `Q₁ + ∑ i, b i • P i = ∑ i, c i • P i` with finitely many `P i ∈ S₁` and
`b i, c i ≥ 0`. Then every test martingale for the i.i.d. null whose initial value has expectation
`1` under the null is a test martingale under the i.i.d. law of `Q₁`. In particular its `limsup`
is almost surely finite under that law: it does not have power one against `Q₁`.

Convexity is needed. For the null of the two point masses on `Bool`, the fair coin is the midpoint
of the null, yet the process equal to `1` while all observations agree, and to `2 ^ n` at time `n`
once two different ones have been seen, is a test martingale for the i.i.d. null that tends to `∞`
almost surely under i.i.d. fair coin flips [EVR26, Note 03, Counterexample 1].

## Main statements

* `ProbabilityTheory.isTestMartingale_infinitePi_of_add_sum_eq_sum`: for a convex null, a test
  martingale for the i.i.d. null with initial expectation `1` is a test martingale under the i.i.d.
  law of every probability measure in the linear span of the null.
* `ProbabilityTheory.ae_limsup_lt_top_infinitePi_of_add_sum_eq_sum`: such a test martingale has an
  almost surely finite `limsup` under that law, so it does not have power one against it.
* `ProbabilityTheory.exists_isTestMartingale_dirac_tendsto_top`: for the null of the two point
  masses on `Bool`, some test martingale for the i.i.d. null with initial value `1` tends to `∞`
  almost surely under i.i.d. fair coin flips.

## Implementation notes

An `ℱ n`-measurable set and the values `M n` and `M (n + 1)` are functions of the first `N + 1`
observations for some `N`, so their integrals under `Measure.infinitePi` are integrals under
`Measure.pi` over `Finset.Iic N`. The finite-dimensional step is a polarization argument. Write
`B = ∑ i, b i • P i`. The integral of a function of finitely many observations under the product
of copies of `Q₁ + t • B` is a polynomial in `t`. For `t ≥ 1`, the measure `Q₁ + t • B` is a
positive multiple of a convex combination of the `P i`, which lies in the null, so the identities
of the martingale hold for these `t`. By the identity theorem for analytic functions they hold at
`t = 0`, that is under `Q₁`. These polarization steps are
`MeasureTheory.Measure.lintegral_pi_eq_of_add_sum_eq_sum` and its i.i.d. form
`MeasureTheory.Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum`.

The statements and proofs are adapted from `EValuesResearch/Results/TestMartingaleConverse.lean`
(commit `6f05c5f`) in the paper project `RemyDegenne/evalues_research`, which formalizes
[EVR26, Note 03] (`results/03-test-martingale-converse.md` there).

## References

* [ZRW24] Z. Zhang, A. Ramdas and R. Wang, *On the existence of powerful p-values and e-values for
  composite hypotheses*, Ann. Statist. 52 (2024), arXiv:2305.16539: §7.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 03, *Converse of the power-one theorem for test martingales*,
  Theorem 1 and Counterexample 1.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### Test martingales for convex i.i.d. nulls -/

/-- **Test martingales for a convex i.i.d. null have no power against its linear span.** Let `S₁`
be a convex set of measures and `Q₁` a probability measure in its linear span, written as
`Q₁ + ∑ i, b i • P i = ∑ i, c i • P i` with finitely many probability measures `P i ∈ S₁`. Let `ℱ`
be a filtration each of whose σ-algebras depends on finitely many observations. Then a test
martingale for the i.i.d. laws of the members of `S₁` whose initial value has expectation `1`
under each of them is a test martingale for the i.i.d. law of `Q₁` [EVR26, Note 03, Theorem 1].
This proves, for convex nulls, the conjecture of [ZRW24, §7] that a test martingale with power one
against `Q₁` forces `Q₁` out of the linear span of the null. -/
theorem isTestMartingale_infinitePi_of_add_sum_eq_sum {S₁ : Set (Measure 𝓧)}
    (hS₁ : Convex ℝ≥0∞ S₁) {ι : Type*} [Fintype ι] {P : ι → Measure 𝓧}
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, P i ∈ S₁) {b c : ι → ℝ≥0} {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hQ₁ : Q₁ + ∑ i, b i • P i = ∑ i, c i • P i)
    {ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → 𝓧))}
    (hℱ : ∀ n, ∃ N, ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N) {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hM : IsTestMartingale M ℱ (iidNull S₁))
    (hM0 : ∀ P ∈ S₁, ∫⁻ ω, M 0 ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) = 1) :
    IsTestMartingale M ℱ {Measure.infinitePi fun _ : ℕ ↦ Q₁} := by
  have hmem (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) : ∑ i, w i • P i ∈ S₁ :=
    hS₁.sum_nnreal_smul_mem hw fun i _ ↦ hP i
  have hnull (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) : Measure.infinitePi (fun _ : ℕ ↦ ∑ i, w i • P i) ∈
      iidNull S₁ :=
    infinitePi_mem_iidNull (hmem w hw)
  refine ⟨hM.adapted, ?_, ?_⟩
  · rintro _ rfl
    obtain ⟨N, hN⟩ := hℱ 0
    refine (Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum hQ₁ ((hM.adapted 0).mono hN le_rfl)
      (measurable_const (a := (1 : ℝ≥0∞))) (fun w hw ↦ ?_) fun w hw ↦ ?_).trans_le (by simp)
    · have := isProbabilityMeasure_sum_smul (P := P) hw
      rw [hM0 _ (hmem w hw)]
      simp
    · rw [hM0 _ (hmem w hw)]
      exact ENNReal.one_ne_top
  · rintro _ rfl n s hs
    obtain ⟨N₁, hN₁⟩ := hℱ n
    obtain ⟨N₂, hN₂⟩ := hℱ (n + 1)
    have h₁ : ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) (max N₁ N₂) :=
      hN₁.trans (Filtration.mono _ (le_max_left _ _))
    have h₂ : ℱ (n + 1) ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) (max N₁ N₂) :=
      hN₂.trans (Filtration.mono _ (le_max_right _ _))
    have hs' : MeasurableSet s := ℱ.le n s hs
    rw [← lintegral_indicator hs', ← lintegral_indicator hs']
    refine Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum hQ₁
      (((hM.adapted (n + 1)).mono h₂ le_rfl).indicator (h₁ s hs))
      (((hM.adapted n).mono h₁ le_rfl).indicator (h₁ s hs)) (fun w hw ↦ ?_) fun w hw ↦ ?_
    · rw [lintegral_indicator hs', lintegral_indicator hs']
      exact hM.setLIntegral_succ_eq _ (hnull w hw) n s hs
    · have := isProbabilityMeasure_sum_smul (P := P) hw
      rw [lintegral_indicator hs']
      exact ((setLIntegral_le_lintegral _ _).trans_lt
        ((hM.isTestSupermartingale.lintegral_le_one (hnull w hw) (n + 1)).trans_lt
          ENNReal.one_lt_top)).ne

/-- **No power one against the linear span of a convex i.i.d. null.** Under the hypotheses of
`isTestMartingale_infinitePi_of_add_sum_eq_sum`, the test martingale has an almost surely finite
`limsup` under the i.i.d. law of `Q₁`: it does not have power one against `Q₁`
[EVR26, Note 03, Theorem 1]. -/
theorem ae_limsup_lt_top_infinitePi_of_add_sum_eq_sum {S₁ : Set (Measure 𝓧)}
    (hS₁ : Convex ℝ≥0∞ S₁) {ι : Type*} [Fintype ι] {P : ι → Measure 𝓧}
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, P i ∈ S₁) {b c : ι → ℝ≥0} {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hQ₁ : Q₁ + ∑ i, b i • P i = ∑ i, c i • P i)
    {ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → 𝓧))}
    (hℱ : ∀ n, ∃ N, ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N) {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hM : IsTestMartingale M ℱ (iidNull S₁))
    (hM0 : ∀ P ∈ S₁, ∫⁻ ω, M 0 ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) = 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), limsup (fun n ↦ M n ω) atTop < ∞ :=
  (isTestMartingale_infinitePi_of_add_sum_eq_sum hS₁ hP hQ₁ hℱ hM
    hM0).isTestSupermartingale.ae_limsup_lt_top (Set.mem_singleton _)

/-! ### Convexity is needed -/

/-- The process of the counterexample: `1` while the observations up to time `n` all equal the
first one, and `2 ^ n` once two different values have been seen. -/
private noncomputable def doublingProcess (n : ℕ) (ω : ℕ → Bool) : ℝ≥0∞ :=
  if ∀ i ≤ n, ω i = ω 0 then 1 else 2 ^ n

/-- The doubling process equals `1` on constant sequences. -/
private lemma doublingProcess_const (n : ℕ) (x : Bool) : doublingProcess n (fun _ ↦ x) = 1 := by
  simp [doublingProcess]

/-- The doubling process is a test martingale for the i.i.d. laws of the two point masses on
`Bool`: under each of them the observations are almost surely constant and the process stays at
`1`. -/
private lemma isTestMartingale_doublingProcess :
    IsTestMartingale doublingProcess (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
      (iidNull {Measure.dirac false, Measure.dirac true}) := by
  have hmem : ∀ μ ∈ iidNull {Measure.dirac false, Measure.dirac true},
      ∃ x : Bool, μ = Measure.dirac (fun _ ↦ x) := by
    refine forall_mem_iidNull.2 fun P hP ↦ ?_
    rcases hP with rfl | rfl
    · exact ⟨false, Measure.infinitePi_dirac (fun _ ↦ false)⟩
    · exact ⟨true, Measure.infinitePi_dirac (fun _ ↦ true)⟩
  have hadapted : Adapted (Filtration.piLE (X := fun _ : ℕ ↦ Bool)) doublingProcess := by
    intro n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have h : doublingProcess n = (fun y : (Finset.Iic n → Bool) ↦
        if ∀ i : Finset.Iic n, y i = y ⟨0, Finset.mem_Iic.2 n.zero_le⟩ then (1 : ℝ≥0∞)
        else 2 ^ n) ∘ Preorder.frestrictLe n := by
      ext ω
      simp only [doublingProcess, Function.comp_apply, Preorder.frestrictLe_apply, Subtype.forall,
        Finset.mem_Iic]
      -- the two sides differ only in their `Decidable` instances
      congr
    rw [h]
    exact (measurable_of_finite _).comp (comap_measurable _)
  refine ⟨hadapted, fun μ hμ ↦ ?_, fun μ hμ n s hs ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hmem μ hμ
    rw [lintegral_dirac, doublingProcess_const]
  · obtain ⟨x, rfl⟩ := hmem μ hμ
    classical
    rw [restrict_dirac' (Filtration.le _ n s hs)]
    split_ifs
    · rw [lintegral_dirac, lintegral_dirac, doublingProcess_const, doublingProcess_const]
    · simp

/-- Under i.i.d. fair coin flips, two different values appear almost surely. -/
private lemma ae_exists_ne_infinitePi_coin : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦
    (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)), ∃ i, ω i ≠ ω 0 := by
  have : IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) :=
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  -- a constant sequence has probability at most `2⁻¹ ^ n` for every `n`, hence `0`
  have hconst (x : Bool) : Measure.infinitePi (fun _ : ℕ ↦
      (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {fun _ ↦ x} = 0 := by
    have hx : ((2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {x} = 2⁻¹ := by
      cases x <;> simp
    have hle (n : ℕ) : Measure.infinitePi (fun _ : ℕ ↦
        (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {fun _ ↦ x} ≤ 2⁻¹ ^ n := by
      calc _ ≤ Measure.infinitePi (fun _ : ℕ ↦
            (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true))
            (Set.pi (Finset.range n : Set ℕ) fun _ ↦ {x}) := measure_mono fun ω hω ↦ by simp_all
        _ = 2⁻¹ ^ n := by
          rw [Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton x, hx, Finset.prod_const,
            Finset.card_range]
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num)) hle) bot_le
  refine measure_mono_null (fun ω hω ↦ ?_) (measure_union_null (hconst false) (hconst true))
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not] at hω
  have hω' : ω = fun _ ↦ ω 0 := funext hω
  cases h : ω 0
  · exact Or.inl (hω'.trans (by rw [h]))
  · exact Or.inr (hω'.trans (by rw [h]))

/-- Once two different values have been seen, the doubling process tends to `∞`. -/
private lemma tendsto_doublingProcess {ω : ℕ → Bool} (hω : ∃ i, ω i ≠ ω 0) :
    Tendsto (fun n ↦ doublingProcess n ω) atTop (𝓝 ∞) := by
  obtain ⟨i, hi⟩ := hω
  refine (ENNReal.tendsto_pow_atTop_nhds_top_iff.2 (by norm_num : (1 : ℝ≥0∞) < 2)).congr' ?_
  filter_upwards [eventually_ge_atTop i] with n hn
  rw [doublingProcess, ite_eq_right fun h ↦ hi (h i hn)]

/-- **Convexity is needed.** For the null of the two point masses on `Bool`, whose midpoint is the
fair coin, some test martingale for the i.i.d. null with initial value `1`, for the filtration of
the observations, tends to `∞` almost surely under i.i.d. fair coin flips
[EVR26, Note 03, Counterexample 1]. -/
theorem exists_isTestMartingale_dirac_tendsto_top :
    ∃ M : ℕ → (ℕ → Bool) → ℝ≥0∞, M 0 = 1 ∧
      IsTestMartingale M (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
        (iidNull {Measure.dirac false, Measure.dirac true}) ∧
      ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦
          (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)),
        Tendsto (fun n ↦ M n ω) atTop (𝓝 ∞) :=
  ⟨doublingProcess, funext fun ω ↦ by simp [doublingProcess], isTestMartingale_doublingProcess,
    ae_exists_ne_infinitePi_coin.mono fun _ ↦ tendsto_doublingProcess⟩

end ProbabilityTheory
