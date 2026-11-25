/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.TruncLog
public import LMLExplore.EValues.BipolarRate.Design.Growth
public import LMLExplore.Probability.ProductMeasure.Table
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# The Wald inequality with a design, for a round on a table of observations

Finitely many sources `a : α` produce observations in `𝓧`, and seeds in `𝓤` drive the
randomization of an algorithm that reads them. A point is a pair `ω = (u, x)` of seeds and of a
table of observations, with the law `ProbabilityTheory.arrayLaw ρ ν` under the instance
`ν : α → Measure 𝓧`. A *round* is a random shape `σ`, the numbers of seeds and of observations of
each source that it reads, and a payoff `V : Ω → ℝ≥0∞`, both determined by the entries read
(`ProbabilityTheory.DependsOnBelow σ σ` and `ProbabilityTheory.DependsOnBelow σ V`): what an
algorithm reads when it chooses adaptively which source to observe and stops, and a function of
what it has read.

The Wald inequality with a design [EVR26, Note 41]: if the payoff has expectation at most `1` under
every instance of `Λ`, then its expected logarithm under `μ`, truncated above at `c`, is at most
`G x`, the growth `designGrowth μ Λ x` of the designs proportional to the vector
`x = 𝔼_μ[(σ ω).2]` of the expected numbers of observations of each source, and so at most
`D* * 𝔼_μ[∑ a, (σ ω).2 a]`, where `D* = designRate μ Λ` is the rate of the designs. Adaptive
sampling does not beat the best fixed design.

## Main statements

* `ProbabilityTheory.eintegral_log_le_designValue`: a function of the seeds and of the first
  `n a` observations of each source `a`, with expectation at most `1` under the instances of `Λ`,
  has expected logarithm at most the value `designValue μ Λ n` of the design `n` under `μ`: the
  seeds have the same law under every instance, so they do not help.
* `ProbabilityTheory.integral_truncLog_le_designGrowth`: the Wald inequality with a design for a
  round that reads at most `K` observations of each source, with payoff at least `δ > 0`, with the
  growth `G` of the designs proportional to the expected numbers of observations.
* `ProbabilityTheory.integral_truncLog_le_designRate_mul`: the same inequality with the rate of
  the designs, `G x ≤ D* * ∑ a, x a`.

## Implementation notes

The proof restarts the round `m` times on the entries not yet read
(`ProbabilityTheory.restartShape`). By Chebyshev's inequality for these independent rounds, they
fit with high probability in the table of the design `⌈m (x + ε 𝟙_{supp x})⌉`
(`ProbabilityTheory.proportionalDesign`), on which `1/2 + 1/2 * 𝟙{the rounds fit} * ∏ i < m, V_i`
is an e-variable. Its expected logarithm is at least `m 𝔼_μ[truncLog c V]` up to a constant, which
gives the bound with `G x` (`ProbabilityTheory.le_designGrowth_of_forall_sub_le`); the bound with
`D*` follows from `ProbabilityTheory.designGrowth_le_designRate_mul`.

The proofs are adapted from the draft `notes/lean-wip/SeveralArmsRound.lean` of the paper project
`RemyDegenne/evalues_research`, which formalizes [EVR26, Note 41]. The one-stream analogue is
`ProbabilityTheory.integral_truncLog_le_bipolarRate_mul`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Theorem 1.
-/

public section

open MeasureTheory InformationTheory
open ENNReal (truncLog)
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α 𝓤 𝓧 : Type*} [Fintype α] {m𝓤 : MeasurableSpace 𝓤} {m𝓧 : MeasurableSpace 𝓧}
  {Λ : Set (α → Measure 𝓧)}

/-- **The seeds are integrated out.** A function `Z` of the seeds and of the first `n a`
observations of each source `a`, with expectation at most `1` under the instances of `Λ`, has
expected logarithm under `μ` at most the value of the design `n`. -/
theorem eintegral_log_le_designValue (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) {n : α → ℕ}
    {Z : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞} (hZ : Measurable Z)
    (hZn : ∀ ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧), ω.1 = ω'.1 →
      (∀ a, ∀ i < n a, ω.2 i a = ω'.2 i a) → Z ω = Z ω')
    (h_null : ∀ ν ∈ Λ, ∫⁻ ω, Z ω ∂arrayLaw ρ ν ≤ 1) :
    ∫ᵉ ω, ENNReal.log (Z ω) ∂arrayLaw ρ μ ≤ designValue μ Λ n := by
  classical
  -- an empty space of tables carries only the zero measure
  rcases isEmpty_or_nonempty (ℕ → α → 𝓧) with hE | hne
  · rw [Measure.eq_zero_of_isEmpty (arrayLaw ρ μ), eintegral_zero_measure]
    exact designValue_nonneg μ (fun ν hν a ↦ (hΛ ν hν a).measure_univ.le) n
  obtain ⟨x₀⟩ := hne
  set Pu := Measure.infinitePi fun _ : ℕ ↦ ρ
  -- the table of the design `n` and the seeds
  let π : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ((Σ a, Fin (n a)) → 𝓧) × (ℕ → 𝓤) :=
    fun ω ↦ (tableOfArray n ω.2, ω.1)
  have hπ : Measurable π :=
    ((measurable_tableOfArray n).comp measurable_snd).prodMk measurable_fst
  have h_map (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] :
      (arrayLaw ρ ν).map π = (designLaw ν n).prod Pu := by
    have hπ_eq : π = Prod.map (tableOfArray n) id ∘ Prod.swap := rfl
    rw [hπ_eq, ← Measure.map_map ((measurable_tableOfArray n).prodMap measurable_id)
      measurable_swap, arrayLaw_def, Measure.prod_swap,
      ← Measure.map_prod_map _ _ (measurable_tableOfArray n) measurable_id, map_tableOfArray,
      Measure.map_id, designLaw_def]
  -- `Z` is a function of the table of the design `n` and of the seeds
  let ext : ((Σ a, Fin (n a)) → 𝓧) × (ℕ → 𝓤) → (ℕ → 𝓤) × (ℕ → α → 𝓧) :=
    fun q ↦ (q.2, arrayOfTable n x₀ q.1)
  have hext : Measurable ext :=
    measurable_snd.prodMk ((measurable_arrayOfTable n x₀).comp measurable_fst)
  have hZ' : Measurable (Z ∘ ext) := hZ.comp hext
  have hZ_eq (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : Z ω = (Z ∘ ext) (π ω) :=
    hZn _ _ rfl fun a i hi ↦ (arrayOfTable_tableOfArray_of_lt n x₀ ω.2 hi).symm
  -- it is an e-variable for the laws of the table of `n` and of the seeds
  have hS : ∀ P ∈ (fun ν ↦ designLaw ν n) '' Λ, P Set.univ ≤ 1 := by
    rintro _ ⟨ν, hν, rfl⟩
    have := hΛ ν hν
    exact prob_le_one
  have hE : IsEVar (Z ∘ ext) (Set.image2 Measure.prod ((fun ν ↦ designLaw ν n) '' Λ) {Pu}) := by
    refine ⟨hZ', ?_⟩
    rintro _ ⟨_, ⟨ν, hν, rfl⟩, _, rfl, rfl⟩
    have := hΛ ν hν
    rw [← h_map ν, lintegral_map hZ' hπ]
    exact (lintegral_congr fun ω ↦ (hZ_eq ω).symm).trans_le (h_null ν hν)
  calc ∫ᵉ ω, ENNReal.log (Z ω) ∂arrayLaw ρ μ
  _ = ∫ᵉ q, ENNReal.log ((Z ∘ ext) q) ∂((designLaw μ n).prod Pu) := by
    rw [← h_map μ, eintegral_map (hZ'.ennreal_log) hπ]
    exact eintegral_congr fun ω ↦ by rw [hZ_eq ω]
  _ ≤ maxEPower ((designLaw μ n).prod Pu)
      (Set.image2 Measure.prod ((fun ν ↦ designLaw ν n) '' Λ) {Pu}) :=
    hE.eintegral_log_le_maxEPower _
  _ = designValue μ Λ n := by
    rw [maxEPower_prod_eq_add hS (by simp), maxEPower_singleton_eq_klDiv, klDiv_self,
      EReal.coe_ennreal_zero, add_zero, designValue_def]

section Wald

variable {σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)}
  {V : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞}

/-- The bet on `m` restarted rounds within the table of the design `n`: the variable equal to
`1/2 + 1/2 * ∏ i < m, V_i` when the `m` rounds fit in that table, and to `1/2` otherwise, is a
function of the seeds and of the table of `n` with expectation at most `1` under the instances of
`Λ`, so its expected logarithm under `μ` is at most the value of `n`. -/
private lemma eintegral_log_restartBet_le_designValue (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hσm : Measurable σ) (hσ : DependsOnBelow σ σ)
    (hVm : Measurable V) (hV : DependsOnBelow σ V) (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1)
    (m : ℕ) (n : α → ℕ) :
    ∫ᵉ ω, ENNReal.log (2⁻¹ + 2⁻¹ * {ω | (restartShape σ m ω).2 ≤ n}.indicator
        (fun ω ↦ ∏ i ∈ Finset.range m, V (restartPoint σ i ω)) ω) ∂arrayLaw ρ μ ≤
      designValue μ Λ n := by
  set fit : Set ((ℕ → 𝓤) × (ℕ → α → 𝓧)) := {ω | (restartShape σ m ω).2 ≤ n} with hfit_def
  set W : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞ := fun ω ↦ ∏ i ∈ Finset.range m, V (restartPoint σ i ω)
  have hfit : MeasurableSet fit := measurableSet_restartShape_snd_le hσm m n
  have hWm : Measurable (fit.indicator W) :=
    (Finset.measurable_fun_prod _ fun i _ ↦ hVm.comp (measurable_restartPoint hσm i)).indicator
      hfit
  refine eintegral_log_le_designValue ρ μ hΛ (measurable_const.add (measurable_const.mul hWm))
    ?_ fun ν hν ↦ ?_
  · -- the bet is a function of the seeds and of the table of `n`: the rounds that fit in it read
    -- only entries of that table
    have key (ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)) (h1 : ω.1 = ω'.1)
        (h2 : ∀ a, ∀ i < n a, ω.2 i a = ω'.2 i a) (hω : ω ∈ fit) : ω' ∈ fit ∧ W ω' = W ω := by
      have hag : AgreeBelow (restartShape σ m ω) ω ω' :=
        agreeBelow_iff.2 ⟨fun i _ ↦ by rw [h1], fun a i hi ↦ h2 a i (hi.trans_le (hω a))⟩
      refine ⟨?_, (dependsOnBelow_prod_restartPoint hσ hV m).eq_of_agreeBelow hag⟩
      rw [hfit_def, Set.mem_ofPred_eq, (dependsOnBelow_restartShape hσ m).eq_of_agreeBelow hag]
      exact hω
    intro ω ω' h1 h2
    by_cases hω : ω ∈ fit
    · obtain ⟨hω', hW⟩ := key ω ω' h1 h2 hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω', hW]
    · have hω' : ω' ∉ fit := fun hω' ↦
        hω (key ω' ω h1.symm (fun a i hi ↦ (h2 a i hi).symm) hω').1
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω']
  · -- the product of the payoffs of the rounds has expectation at most `1` under `ν`
    have := hΛ ν hν
    calc ∫⁻ ω, 2⁻¹ + 2⁻¹ * fit.indicator W ω ∂arrayLaw ρ ν
    _ = 2⁻¹ + 2⁻¹ * ∫⁻ ω, fit.indicator W ω ∂arrayLaw ρ ν := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hWm, lintegral_const,
        measure_univ, mul_one]
    _ ≤ 2⁻¹ + 2⁻¹ * 1 := by
      gcongr
      exact (lintegral_mono fun ω ↦ Set.indicator_le_self' (fun _ _ ↦ bot_le) ω).trans
        (lintegral_prod_restartPoint_le_one ρ ν hσm hσ hVm hV (h_null ν hν) m)
    _ = 1 := by rw [mul_one, ENNReal.inv_two_add_inv_two]

/-- **The value of a design and the restarted rounds.** Let the payoff `V ≥ δ > 0` of a round
have expectation at most `1` under the instances of `Λ`. The value of the design `n` is at least
`m` times the expected truncated logarithm of `V` under `μ`, minus `log 2` and the contribution of
the event that `m` restarted rounds do not fit in the table of `n`. -/
private lemma mul_integral_truncLog_sub_le_designValue (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hσm : Measurable σ) (hσ : DependsOnBelow σ σ)
    (hVm : Measurable V) (hV : DependsOnBelow σ V)
    (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) (c : ℝ) (m : ℕ) (n : α → ℕ) :
    ((m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ - Real.log 2 -
        m * max |Real.log δ| |c| *
          (arrayLaw ρ μ).real {ω | ¬ (restartShape σ m ω).2 ≤ n} : ℝ) : EReal) ≤
      designValue μ Λ n := by
  set C := max |Real.log δ| |c|
  set Ls : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ := fun ω ↦
    ∑ i ∈ Finset.range m, truncLog c (V (restartPoint σ i ω))
  set fit : Set ((ℕ → 𝓤) × (ℕ → α → 𝓧)) := {ω | (restartShape σ m ω).2 ≤ n} with hfit_def
  have hfit : MeasurableSet fit := measurableSet_restartShape_snd_le hσm m n
  -- the sum of the truncated logarithms of the payoffs of the `m` rounds: it is bounded by
  -- `m * C`, and its expectation is `m` times that of one round
  have hTm : Measurable fun ω ↦ truncLog c (V ω) := (ENNReal.measurable_truncLog c).comp hVm
  have hLi (i : ℕ) : Integrable (fun ω ↦ truncLog c (V (restartPoint σ i ω))) (arrayLaw ρ μ) :=
    ENNReal.integrable_truncLog_comp hδ (hVm.comp (measurable_restartPoint hσm i)) fun _ ↦ hVδ _
  have hLsC (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : ‖Ls ω‖ ≤ m * C := by
    calc ‖Ls ω‖ ≤ ∑ i ∈ Finset.range m, ‖truncLog c (V (restartPoint σ i ω))‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, C :=
      Finset.sum_le_sum fun i _ ↦ ENNReal.abs_truncLog_le hδ (hVδ _)
    _ = m * C := by simp
  have hLsi : Integrable Ls (arrayLaw ρ μ) := integrable_finsetSum _ fun i _ ↦ hLi i
  have hLs_int : ∫ ω, Ls ω ∂arrayLaw ρ μ = m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ := by
    rw [integral_finsetSum _ fun i _ ↦ hLi i, Finset.sum_congr rfl fun i _ ↦ by
      rw [← integral_map (measurable_restartPoint hσm i).aemeasurable hTm.aestronglyMeasurable,
        map_restartPoint ρ μ hσm hσ i]]
    simp
  -- a lower bound on the logarithm of the bet of `eintegral_log_restartBet_le_designValue`
  have hlog (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : ((-Real.log 2 + fit.indicator Ls ω : ℝ) : EReal) ≤
      ENNReal.log (2⁻¹ + 2⁻¹ *
        fit.indicator (fun ω ↦ ∏ i ∈ Finset.range m, V (restartPoint σ i ω)) ω) := by
    rw [← ENNReal.log_ofReal_exp]
    refine ENNReal.log_monotone ?_
    rw [Real.exp_add, Real.exp_neg, Real.exp_log two_pos,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
    by_cases hω : ω ∈ fit
    · simp only [Set.indicator_of_mem hω]
      refine le_trans ?_ le_add_self
      gcongr
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
      exact Finset.prod_le_prod fun i _ ↦ ENNReal.ofReal_exp_truncLog_le
        (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) (hVδ _)).ne'
    · simp [Set.indicator_of_notMem hω]
  have hint : Integrable (fun ω ↦ -Real.log 2 + fit.indicator Ls ω) (arrayLaw ρ μ) :=
    (integrable_const _).add (hLsi.indicator hfit)
  -- the expectation of the lower bound
  have h_real : m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ - Real.log 2 -
      m * C * (arrayLaw ρ μ).real fitᶜ ≤ ∫ ω, -Real.log 2 + fit.indicator Ls ω ∂arrayLaw ρ μ := by
    have h1 : ∫ ω in fitᶜ, Ls ω ∂arrayLaw ρ μ ≤ m * C * (arrayLaw ρ μ).real fitᶜ :=
      (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
        (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun ω _ ↦ hLsC ω))
    have h2 := integral_add_compl hfit hLsi
    rw [integral_add (integrable_const _) (hLsi.indicator hfit), integral_indicator hfit,
      integral_const, probReal_univ, one_smul]
    linarith
  calc ((m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ - Real.log 2 -
        m * C * (arrayLaw ρ μ).real fitᶜ : ℝ) : EReal)
  _ ≤ ((∫ ω, -Real.log 2 + fit.indicator Ls ω ∂arrayLaw ρ μ : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.2 h_real
  _ = ∫ᵉ ω, ((-Real.log 2 + fit.indicator Ls ω : ℝ) : EReal) ∂arrayLaw ρ μ :=
    (eintegral_eq_integral hint).symm
  _ ≤ _ := (eintegral_mono hlog).trans
    (eintegral_log_restartBet_le_designValue ρ μ hΛ hσm hσ hVm hV h_null m n)

/-- **The design proportional to the mean numbers of observations.** For `m ≥ 1` and `ε > 0`, the
design `⌈m (x + ε 𝟙_{supp x})⌉`, with `x a = 𝔼_μ[(σ ω).2 a]` the mean number of observations of
the source `a` in a round, has value at least `m 𝔼_μ[truncLog c V] - log 2 - C`, with a constant
`C` that does not depend on `m`: the `m` restarted rounds fit in its table with probability at
least `1 - |α| K² / (m ε²)`. -/
private lemma sub_le_designValue_proportionalDesign (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hσm : Measurable σ) (hσ : DependsOnBelow σ σ)
    (hVm : Measurable V) (hV : DependsOnBelow σ V) {K : ℕ} (hσK : ∀ ω a, (σ ω).2 a ≤ K)
    (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) (c : ℝ) {m : ℕ} (hm : 0 < m) {ε : ℝ≥0} (hε : 0 < ε) :
    ((m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ - (Real.log 2 + max |Real.log δ| |c| *
        (Fintype.card α * (K : ℝ) ^ 2 / (ε : ℝ) ^ 2)) : ℝ) : EReal) ≤
      designValue μ Λ (proportionalDesign
        (fun a ↦ (∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ).toNNReal) ε m) := by
  set x : α → ℝ≥0 := fun a ↦ (∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ).toNNReal with hx_def
  have hx (a : α) : (x a : ℝ) = ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ :=
    Real.coe_toNNReal _ (integral_nonneg fun ω ↦ Nat.cast_nonneg _)
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (mul_integral_truncLog_sub_le_designValue ρ μ
    hΛ hσm hσ hVm hV h_null hδ hVδ c m (proportionalDesign x ε m))
  -- Chebyshev's inequality for the restarted rounds
  have hp := measureReal_not_restartShape_snd_le ρ μ hσm hσ hσK hm (NNReal.coe_pos.2 hε)
    (n := proportionalDesign x ε m) fun a ha ↦ by
      have hxa : x a ≠ 0 := by
        rw [← NNReal.coe_ne_zero, hx]
        exact ha
      rw [← hx]
      exact_mod_cast le_proportionalDesign (m := m) hxa
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set p := (arrayLaw ρ μ).real {ω | ¬ (restartShape σ m ω).2 ≤ proportionalDesign x ε m}
  set C := max |Real.log δ| |c|
  have h1 : m * C * p ≤ C * (Fintype.card α * (K : ℝ) ^ 2 / (ε : ℝ) ^ 2) := by
    calc m * C * p
    _ ≤ m * C * (Fintype.card α * (K : ℝ) ^ 2 / (m * (ε : ℝ) ^ 2)) := by gcongr
    _ = C * (Fintype.card α * (K : ℝ) ^ 2 / (ε : ℝ) ^ 2) := by field_simp
  linarith

/-- **The Wald inequality with a design, for a bounded round** [EVR26, Note 41, Theorem 1]. Let
`σ` be the shape and `V ≥ δ > 0` the payoff of a round, both determined by the seeds and the
observations that the round reads, with at most `K` observations of each source. If the payoff
has expectation at most `1` under every instance of `Λ`, then under the instance `μ` the expected
logarithm of the payoff, truncated above at `c`, is at most the growth `G x` of the designs
proportional to the vector `x` of the expected numbers of observations of each source that the
round reads. -/
theorem integral_truncLog_le_designGrowth (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hσm : Measurable σ)
    (hσ : DependsOnBelow σ σ) (hVm : Measurable V) (hV : DependsOnBelow σ V) {K : ℕ}
    (hσK : ∀ ω a, (σ ω).2 a ≤ K) (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) (c : ℝ) :
    ((∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ : ℝ) : EReal) ≤
      designGrowth μ Λ fun a ↦ (∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ).toNNReal :=
  le_designGrowth_of_forall_sub_le fun _ hε ↦ ⟨_, fun _ hm ↦
    sub_le_designValue_proportionalDesign ρ μ hΛ hσm hσ hVm hV hσK h_null hδ hVδ c hm hε⟩

/-- **The Wald inequality with a design, for a bounded round, with the rate of the designs**
[EVR26, Note 41, Theorem 1]. Under the hypotheses of
`ProbabilityTheory.integral_truncLog_le_designGrowth`, for a nonempty set `Λ` of instances, the
expected logarithm of the payoff under `μ`, truncated above at `c`, is at most the rate of the
designs times the expected number of observations that the round reads. The product is in
`EReal`, with `⊤ * 0 = 0`. -/
theorem integral_truncLog_le_designRate_mul (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hΛne : Λ.Nonempty)
    (hσm : Measurable σ) (hσ : DependsOnBelow σ σ) (hVm : Measurable V)
    (hV : DependsOnBelow σ V) {K : ℕ} (hσK : ∀ ω a, (σ ω).2 a ≤ K)
    (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) (c : ℝ) :
    ((∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ : ℝ) : EReal) ≤
      designRate μ Λ * ((∫ ω, ∑ a, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ : ℝ) : EReal) := by
  have h_sum : ∑ a, ((∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ).toNNReal : ℝ) =
      ∫ ω, ∑ a, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ := by
    rw [integral_finsetSum _ fun a _ ↦ integrable_shape_snd_apply hσm fun ω ↦ hσK ω a]
    exact Finset.sum_congr rfl fun a _ ↦
      Real.coe_toNNReal _ (integral_nonneg fun ω ↦ Nat.cast_nonneg _)
  rw [← h_sum]
  exact (integral_truncLog_le_designGrowth ρ μ hΛ hσm hσ hVm hV hσK h_null hδ hVδ c).trans
    (designGrowth_le_designRate_mul hΛne _)

end Wald

end ProbabilityTheory
