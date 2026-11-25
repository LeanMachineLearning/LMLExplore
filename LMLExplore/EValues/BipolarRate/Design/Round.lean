/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.TruncLog
public import LMLExplore.EValues.BipolarRate.Design.Basic
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
`D* * 𝔼_μ[∑ a, (σ ω).2 a]`, where `D* = designRate μ Λ` is the rate of the designs. Adaptive
sampling does not beat the best fixed design.

## Main statements

* `ProbabilityTheory.eintegral_log_le_designValue`: a function of the seeds and of the first
  `n a` observations of each source `a`, with expectation at most `1` under the instances of `Λ`,
  has expected logarithm at most the value `designValue μ Λ n` of the design `n` under `μ`: the
  seeds have the same law under every instance, so they do not help.
* `ProbabilityTheory.integral_truncLog_le_designRate_mul`: the Wald inequality with a design for
  a round that reads at most `K` observations of each source, with payoff at least `δ > 0`.

## Implementation notes

The proof restarts the round `m` times on the entries not yet read
(`ProbabilityTheory.restartShape`). By Chebyshev's inequality for these independent rounds, they
fit with high probability in the table of the design `n` with `n a ≈ m (𝔼_μ[(σ ω).2 a] + ε)`, on
which `1/2 + 1/2 * 𝟙{the rounds fit} * ∏ i < m, V_i` is an e-variable. Comparing its expected
logarithm with `designValue μ Λ n ≤ (∑ a, n a) * D*` and letting `m → ∞`, then `ε → 0`, gives the
bound.

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
open scoped ENNReal

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

/-- The limit argument of the Wald inequality with a design: if for every `ε > 0` there is `c₁`
with `m ℓ - c₁ ≤ (m X + m ε k + k) d` for every `m ≥ 1`, then `ℓ ≤ d X`. -/
private lemma le_mul_of_forall_design_le {ℓ d X k : ℝ} (hd : 0 ≤ d) (hk : 0 ≤ k)
    (h : ∀ ε : ℝ, 0 < ε → ∃ c₁ : ℝ, ∀ m : ℕ, 0 < m →
      m * ℓ - c₁ ≤ (m * X + m * ε * k + k) * d) :
    ℓ ≤ d * X := by
  by_contra hlt
  rw [not_le] at hlt
  set η := ℓ - d * X with hη
  have hη0 : 0 < η := sub_pos.2 hlt
  have hkd : 0 ≤ k * d := mul_nonneg hk hd
  obtain ⟨c₁, hc₁⟩ := h (η / (2 * (k * d + 1))) (by positivity)
  have hε : η / (2 * (k * d + 1)) * (k * d) ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (c₁ + k * d) / η)
  have hm' := hc₁ (m + 1) (Nat.succ_pos m)
  have h2 : 2 * (c₁ + k * d) < m * η := (div_lt_iff₀ hη0).1 hm
  have h3 : ((m : ℝ) + 1) * (η / (2 * (k * d + 1)) * (k * d)) ≤ ((m : ℝ) + 1) * (η / 2) :=
    mul_le_mul_of_nonneg_left hε (by positivity)
  have h4 : ((m : ℝ) + 1) * ℓ = ((m : ℝ) + 1) * η + ((m : ℝ) + 1) * (d * X) := by
    rw [hη]
    ring
  push_cast at hm'
  nlinarith

/-- **The design proportional to the mean numbers of observations.** For `m ≥ 1` and `ε > 0`, the
design `n` with `n a = ⌈m (𝔼_μ[(σ ω).2 a] + ε)⌉` for the sources that the round reads (and
`n a = 0` for the others) has at most `m (X + ε |α|) + |α|` observations, with `X` the expected
number of observations of a round, and value at least `m 𝔼_μ[truncLog c V] - log 2 - C`, with a
constant `C` that does not depend on `m`: the `m` restarted rounds fit in its table with
probability at least `1 - |α| K² / (m ε²)`. -/
private lemma exists_le_designValue (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hσm : Measurable σ) (hσ : DependsOnBelow σ σ)
    (hVm : Measurable V) (hV : DependsOnBelow σ V) {K : ℕ} (hσK : ∀ ω a, (σ ω).2 a ≤ K)
    (h_null : ∀ ν ∈ Λ, ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) (c : ℝ) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : α → ℕ, (∀ a, ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ = 0 → n a = 0) ∧
      ((∑ a, n a : ℕ) : ℝ) ≤ m * ∑ a, ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ +
        m * ε * Fintype.card α + Fintype.card α ∧
      ((m * ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ - (Real.log 2 + max |Real.log δ| |c| *
        (Fintype.card α * (K : ℝ) ^ 2 / ε ^ 2)) : ℝ) : EReal) ≤ designValue μ Λ n := by
  classical
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set x : α → ℝ := fun a ↦ ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ
  have hx0 (a : α) : 0 ≤ x a := integral_nonneg fun ω ↦ Nat.cast_nonneg _
  set n : α → ℕ := fun a ↦ if x a = 0 then 0 else ⌈m * (x a + ε)⌉₊ with hn_def
  refine ⟨n, fun a ha ↦ by simp [hn_def, x, ha], ?_, ?_⟩
  · -- the number of observations of the design
    have h_le (a : α) : (n a : ℝ) ≤ m * (x a + ε) + 1 := by
      have h_pos : 0 ≤ m * (x a + ε) := mul_nonneg hmr.le (add_nonneg (hx0 a) hε.le)
      simp only [hn_def]
      split_ifs
      · simpa using by linarith
      · exact (Nat.ceil_lt_add_one h_pos).le
    calc ((∑ a, n a : ℕ) : ℝ) = ∑ a, (n a : ℝ) := by push_cast; rfl
    _ ≤ ∑ a, (m * (x a + ε) + 1) := Finset.sum_le_sum fun a _ ↦ h_le a
    _ = m * ∑ a, x a + m * ε * Fintype.card α + Fintype.card α := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      ring
  · -- its value, by Chebyshev's inequality for the restarted rounds
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (mul_integral_truncLog_sub_le_designValue ρ μ
      hΛ hσm hσ hVm hV h_null hδ hVδ c m n)
    have hp := measureReal_not_restartShape_snd_le ρ μ hσm hσ hσK hm hε (n := n) fun a ha ↦ by
      simpa [hn_def, x, ha] using Nat.le_ceil _
    have hC0 : 0 ≤ max |Real.log δ| |c| := (abs_nonneg _).trans (le_max_left _ _)
    have h1 : m * max |Real.log δ| |c| * (arrayLaw ρ μ).real {ω | ¬ (restartShape σ m ω).2 ≤ n} ≤
        max |Real.log δ| |c| * (Fintype.card α * (K : ℝ) ^ 2 / ε ^ 2) := by
      calc m * max |Real.log δ| |c| * (arrayLaw ρ μ).real {ω | ¬ (restartShape σ m ω).2 ≤ n}
      _ ≤ m * max |Real.log δ| |c| * (Fintype.card α * (K : ℝ) ^ 2 / (m * ε ^ 2)) := by gcongr
      _ = max |Real.log δ| |c| * (Fintype.card α * (K : ℝ) ^ 2 / ε ^ 2) := by field_simp
    linarith

/-- **The Wald inequality with a design, for a bounded round** [EVR26, Note 41, Theorem 1]. Let
`σ` be the shape and `V ≥ δ > 0` the payoff of a round, both determined by the seeds and the
observations that the round reads, with at most `K` observations of each source. If the payoff
has expectation at most `1` under every instance of the nonempty set `Λ`, then under the instance
`μ` the expected logarithm of the payoff, truncated above at `c`, is at most the rate of the
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
  have hN (a : α) : Integrable (fun ω ↦ ((σ ω).2 a : ℝ)) (arrayLaw ρ μ) :=
    integrable_shape_snd_apply hσm fun ω ↦ hσK ω a
  rw [integral_finsetSum _ fun a _ ↦ hN a]
  have key := fun (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) ↦
    exists_le_designValue ρ μ hΛ hσm hσ hVm hV hσK h_null hδ hVδ c hm hε
  have hx0 (a : α) : 0 ≤ ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ :=
    integral_nonneg fun ω ↦ Nat.cast_nonneg _
  set ℓ := ∫ ω, truncLog c (V ω) ∂arrayLaw ρ μ
  set X := ∑ a, ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ with hX
  set C := max |Real.log δ| |c|
  set k : ℝ := ((Fintype.card α : ℕ) : ℝ)
  have hX_nonneg : 0 ≤ X := Finset.sum_nonneg fun a _ ↦ hx0 a
  rcases eq_or_ne (designRate μ Λ) ⊤ with hD | hD
  · rcases hX_nonneg.eq_or_lt with hX0 | hXpos
    · -- no observation is read: the designs of `key` are empty, of value `0`
      rw [← hX0, EReal.coe_zero, mul_zero, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      have hx_all (a : α) : ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ hx0 a).1 (hX.symm.trans hX0.symm) a
          (Finset.mem_univ a)
      by_contra hℓ
      rw [not_le] at hℓ
      obtain ⟨m, hm⟩ := exists_nat_gt ((Real.log 2 + C * (k * (K : ℝ) ^ 2 / 1 ^ 2)) / ℓ)
      obtain ⟨n, hn0, -, hn⟩ := key (m + 1) (Nat.succ_pos m) 1 one_pos
      have hn_eq : n = 0 := funext fun a ↦ hn0 a (hx_all a)
      rw [hn_eq, designValue_zero μ hΛne, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hn
      have h1 := (div_lt_iff₀ hℓ).1 hm
      push_cast at hn
      nlinarith
    · rw [hD, EReal.top_mul_of_pos (EReal.coe_pos.2 hXpos)]
      exact le_top
  · -- the values of the designs of `key` are at most their numbers of observations times `D*`
    have hd0 := designRate_nonneg μ Λ
    have hd : (((designRate μ Λ).toReal : ℝ) : EReal) = designRate μ Λ :=
      EReal.coe_toReal hD (ne_bot_of_le_ne_bot EReal.zero_ne_bot hd0)
    rw [← hd, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    refine le_mul_of_forall_design_le (k := k) (EReal.toReal_nonneg hd0) (Nat.cast_nonneg _)
      fun ε hε ↦ ⟨Real.log 2 + C * (k * (K : ℝ) ^ 2 / ε ^ 2), fun m hm ↦ ?_⟩
    obtain ⟨n, -, hn_sum, hn⟩ := key m hm ε hε
    have h1 : ((m * ℓ - (Real.log 2 + C * (k * (K : ℝ) ^ 2 / ε ^ 2)) : ℝ) : EReal) ≤
        ((∑ a, n a : ℕ) : EReal) * designRate μ Λ := by
      refine hn.trans ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [designValue_zero μ hΛne]
      · exact designValue_le_mul_designRate μ Λ hn0
    rw [← hd, ← EReal.coe_coe_eq_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hn_sum (EReal.toReal_nonneg hd0))

end Wald

end ProbabilityTheory
