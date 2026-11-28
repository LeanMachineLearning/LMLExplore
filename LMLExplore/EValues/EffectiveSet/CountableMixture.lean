/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EffectiveSet.Dominated
public import LMLExplore.EValues.KLInf
public import LMLExplore.MeasureTheory.Measure.SigmaConvex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Data.EReal.Operations

/-!
# Countable mixtures suffice for the largest e-power of a dominated null

By Statlib's duality, the largest e-power `maxEPower Q S` of a null `S` under a probability
measure `Q` is the smallest relative entropy `klIntegral Q ν` over the members `ν` of the effective
null `effectiveSet S`. For a null dominated by a σ-finite measure, the members of the effective
null may be replaced by the countable mixtures of members of `S`, with no other hypothesis
[EVR26, Note 48, Theorem 2]:
`maxEPower Q S = ⨅ m ∈ sigmaConvexHull S, klIntegral Q m`.
Finite mixtures do not suffice [EVR26, Note 48]: on `ℕ`, for `Q` of full support and the laws
`Q (· | {0, …, k})`, every finite mixture has infinite divergence from `Q`, while
`maxEPower Q S = 0`.

The statement holds for every σ-convex set of measures between `S` and its effective null
(`ProbabilityTheory.maxEPower_eq_iInf_klIntegral_of_isSigmaConvex`); the σ-convex hull of `S` is
the smallest one (`ProbabilityTheory.maxEPower_eq_iInf_klIntegral_sigmaConvexHull`).

## Main statements

* `ProbabilityTheory.maxEPower_eq_iInf_klIntegral_of_isSigmaConvex`: for a null `S` of measures of
  mass at most one, absolutely continuous with respect to a σ-finite measure, and a σ-convex `𝒞`
  with `S ⊆ 𝒞 ⊆ effectiveSet S`, `maxEPower Q S = ⨅ m ∈ 𝒞, klIntegral Q m`.
* `ProbabilityTheory.maxEPower_eq_iInf_klIntegral_sigmaConvexHull`: **countable mixtures suffice**
  [EVR26, Note 48, Theorem 2].
* `ProbabilityTheory.toENNReal_maxEPower_eq_iInf_klDiv`: on a countable alphabet, with the relative
  entropy `klDiv`.

## Implementation notes

The proof follows [EVR26, Note 48]. Only `⨅ m ∈ 𝒞, klIntegral Q m ≤ maxEPower Q S` needs a proof
when the right side is finite. Let `μ*` be Statlib's reverse information projection `ripr Q S`,
with `klIntegral Q μ* = maxEPower Q S`; then `Q ≪ μ* ≪ μ`. By the description of the effective
null of a dominated null through the bipolar theorem
(`ProbabilityTheory.mem_effectiveSet_iff_rnDeriv_mem_closedSolidConvexHull`), the density
`q = dμ*/dμ` is in the closed solid convex hull of the densities of `S`. The functions `h` such
that, for every `t < 1` and `δ > 0`, some member of `𝒞` has a sub-density `p` with
`Q {p < t * h} ≤ δ` form a convex, solid and closed set that contains the densities of `S`, hence
`q`.

Choose such members `m k` with sub-densities `p k` for `t = 1 - ε` and errors `δ k` of sum at most
`δ`, and mix them with the weights `w k = (1 - ε) * ε ^ k`. The mixture dominates
`μ*.withDensity c` for `c = (1 - ε) * ∑ k, w k * 𝟙 {(1 - ε) * q ≤ p k}`, so that `c * E` is an
e-variable for `μ*` for every e-variable `E` of the mixture, and `log E = log (c * E) + log c⁻¹`
where `c ≠ 0`. If `K` is the first good index, then `(1 - ε) ^ 2 * ε ^ K ≤ c`, and `K` is at most
the number of bad indices, whose expectation is at most `δ`. So the expected value of `log c⁻¹`
is at most `log ((1 - ε) ^ 2)⁻¹ + log ε⁻¹ * δ`, which tends to `0` with `ε` and `δ`. This
counting argument replaces the nested sets of the proof of [EVR26, Note 48, Lemma 1].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 48
  (`results/48-mixtures-in-the-dual.md`), of the paper project
  github.com/RemyDegenne/evalues_research, 2026.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ Q : Measure Ω} {S 𝒞 : Set (Measure Ω)}

/-! ### Approximate domination by members of a set of measures -/

/-- The measurable functions `h` that members of `𝒞` dominate approximately under `Q`: for every
`t < 1` and `δ > 0`, some `m ∈ 𝒞` has a sub-density `p` (`μ.withDensity p ≤ m`) with
`Q {p < t * h} ≤ δ`. -/
private def approxDominated (μ Q : Measure Ω) (𝒞 : Set (Measure Ω)) : Set (Ω → ℝ≥0∞) :=
  {h | Measurable h ∧ ∀ t < 1, ∀ δ ≠ 0, ∃ m ∈ 𝒞, ∃ p : Ω → ℝ≥0∞, Measurable p ∧
    μ.withDensity p ≤ m ∧ Q {ω | p ω < t * h ω} ≤ δ}

private lemma convex_approxDominated (h𝒞 : Convex ℝ≥0∞ 𝒞) :
    Convex ℝ≥0∞ (approxDominated μ Q 𝒞) := by
  rintro h₁ ⟨hh₁, H₁⟩ h₂ ⟨hh₂, H₂⟩ a b ha hb hab
  refine ⟨(hh₁.const_smul a).add (hh₂.const_smul b), fun t ht δ hδ ↦ ?_⟩
  obtain ⟨m₁, hm₁, p₁, hp₁, hle₁, hQ₁⟩ := H₁ t ht (δ / 2) (ENNReal.half_pos hδ).ne'
  obtain ⟨m₂, hm₂, p₂, hp₂, hle₂, hQ₂⟩ := H₂ t ht (δ / 2) (ENNReal.half_pos hδ).ne'
  refine ⟨a • m₁ + b • m₂, h𝒞 hm₁ hm₂ ha hb hab, a • p₁ + b • p₂,
    (hp₁.const_smul a).add (hp₂.const_smul b), ?_, ?_⟩
  · rw [withDensity_add_left (hp₁.const_smul a), withDensity_smul _ hp₁, withDensity_smul _ hp₂]
    refine Measure.le_iff'.2 fun s ↦ ?_
    simp only [add_apply, smul_apply, smul_eq_mul]
    gcongr
  -- where both members dominate, so does the mixture
  calc Q {ω | (a • p₁ + b • p₂) ω < t * (a • h₁ + b • h₂) ω}
      ≤ Q ({ω | p₁ ω < t * h₁ ω} ∪ {ω | p₂ ω < t * h₂ ω}) := by
        refine measure_mono fun ω hω ↦ ?_
        by_contra hω'
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hω hω'
        refine hω.not_ge ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc t * (a * h₁ ω + b * h₂ ω) = a * (t * h₁ ω) + b * (t * h₂ ω) := by ring
          _ ≤ a * p₁ ω + b * p₂ ω := by gcongr <;> tauto
    _ ≤ δ / 2 + δ / 2 := (measure_union_le _ _).trans (add_le_add hQ₁ hQ₂)
    _ = δ := ENNReal.add_halves δ

private lemma isAESolid_approxDominated : IsAESolid Q (approxDominated μ Q 𝒞) := by
  rw [isAESolid_iff]
  rintro h g ⟨-, H⟩ hg hgh
  refine ⟨hg, fun t ht δ hδ ↦ ?_⟩
  obtain ⟨m, hm, p, hp, hle, hQ⟩ := H t ht δ hδ
  refine ⟨m, hm, p, hp, hle, (measure_mono_ae ?_).trans hQ⟩
  filter_upwards [hgh] with ω hω hlt
  exact hlt.trans_le (by gcongr)

private lemma isAESeqClosed_approxDominated [IsFiniteMeasure Q] :
    IsAESeqClosed Q (approxDominated μ Q 𝒞) := by
  rw [isAESeqClosed_iff]
  intro f g hf hg hg_top hfg
  refine ⟨hg, fun t ht δ hδ ↦ ?_⟩
  obtain ⟨t', htt', ht'⟩ := exists_between ht
  -- the sets where `t' * f n` is below `t * g` have measures tending to `0`
  have h_lim : Tendsto (fun n ↦ Q {ω | t' * f n ω < t * g ω}) atTop (𝓝 0) := by
    have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := Q) atTop (A := ∅)
      MeasurableSet.empty (fun n ↦ measurableSet_lt ((hf n).1.const_mul t') (hg.const_mul t)) ?_
    · simpa using this
    filter_upwards [hfg, hg_top] with ω hω hω_top
    rcases eq_or_ne (g ω) 0 with h0 | h0
    · exact Eventually.of_forall fun n ↦ by simp [h0]
    have hlt : t * g ω < t' * g ω := ENNReal.mul_lt_mul_left h0 hω_top htt'
    filter_upwards [(ENNReal.Tendsto.const_mul hω (.inr ht'.ne_top)).eventually
      (lt_mem_nhds hlt)] with n hn
    simp [hn.not_gt]
  obtain ⟨n, hn⟩ := (h_lim.eventually (gt_mem_nhds (ENNReal.half_pos hδ))).exists
  obtain ⟨m, hm, p, hp, hle, hQ⟩ := (hf n).2 t' ht' (δ / 2) (ENNReal.half_pos hδ).ne'
  refine ⟨m, hm, p, hp, hle, ?_⟩
  calc Q {ω | p ω < t * g ω}
      ≤ Q ({ω | p ω < t' * f n ω} ∪ {ω | t' * f n ω < t * g ω}) := by
        refine measure_mono fun ω hω ↦ ?_
        by_contra hω'
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hω hω'
        exact hω.not_ge (hω'.2.trans hω'.1)
    _ ≤ δ / 2 + δ / 2 := (measure_union_le _ _).trans (add_le_add hQ hn.le)
    _ = δ := ENNReal.add_halves δ

/-- The densities of the members of `S` are dominated by themselves. -/
private lemma rnDeriv_mem_approxDominated (hS𝒞 : S ⊆ 𝒞) {P : Measure Ω} (hP : P ∈ S) :
    P.rnDeriv μ ∈ approxDominated μ Q 𝒞 := by
  refine ⟨Measure.measurable_rnDeriv P μ, fun t ht δ _ ↦ ⟨P, hS𝒞 hP, P.rnDeriv μ,
    Measure.measurable_rnDeriv P μ, Measure.withDensity_rnDeriv_le P μ, ?_⟩⟩
  have h_empty : {ω | P.rnDeriv μ ω < t * P.rnDeriv μ ω} = ∅ :=
    eq_empty_of_forall_notMem fun ω hω ↦ (not_lt.2 (mul_le_of_le_one_left' ht.le)) hω
  simp [h_empty]

/-! ### The mixture -/

/-- **The cost of the mixture weights.** For sets `G k` and `ε ∈ (0, 1)`, let
`c = (1 - ε) * ∑' k, (1 - ε) * ε ^ k * 𝟙 (G k)`. At a point `ω` outside only finitely many of
the `G k`, say `N` of them, `c` is positive and `log c⁻¹ ≤ log ((1 - ε) ^ 2)⁻¹ + N * log ε⁻¹`:
the first index `K` with `ω ∈ G K` is at most `N`, and `(1 - ε) ^ 2 * ε ^ K ≤ c`. -/
private lemma log_inv_mixtureFactor_le {G : ℕ → Set Ω} {ε : ℝ≥0∞} (hε0 : ε ≠ 0) (hε1 : ε < 1)
    {ω : Ω} (hω : ∑' k, (G k)ᶜ.indicator (1 : Ω → ℝ≥0∞) ω ≠ ∞) :
    (1 - ε) * ∑' k, (1 - ε) * ε ^ k * (G k).indicator (1 : Ω → ℝ≥0∞) ω ≠ 0 ∧
      ENNReal.log ((1 - ε) * ∑' k, (1 - ε) * ε ^ k * (G k).indicator (1 : Ω → ℝ≥0∞) ω)⁻¹ ≤
        (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal +
          (∑' k, (G k)ᶜ.indicator (1 : Ω → ℝ≥0∞) ω) * (ENNReal.log ε⁻¹).toENNReal : ℝ≥0∞) :
            EReal) := by
  have h1ε : 1 - ε ≠ 0 := (tsub_pos_of_lt hε1).ne'
  have h1ε_top : 1 - ε ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  -- some index is good, else infinitely many are bad
  have h_ex : ∃ k, ω ∈ G k := by
    by_contra h_all
    push Not at h_all
    have h_one (k : ℕ) : (G k)ᶜ.indicator (1 : Ω → ℝ≥0∞) ω = 1 := indicator_of_mem (h_all k) _
    simp only [h_one] at hω
    exact hω (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  classical
  -- the first good index `K`: the indices below it are bad
  obtain ⟨K, hK_mem, hK_min⟩ : ∃ K, ω ∈ G K ∧ ∀ k < K, ω ∉ G k :=
    ⟨Nat.find h_ex, Nat.find_spec h_ex, fun k hk ↦ Nat.find_min h_ex hk⟩
  have hK : (K : ℝ≥0∞) ≤ ∑' k, (G k)ᶜ.indicator (1 : Ω → ℝ≥0∞) ω := by
    calc (K : ℝ≥0∞) = ∑ k ∈ Finset.range K, (G k)ᶜ.indicator (1 : Ω → ℝ≥0∞) ω := by
          rw [Finset.sum_congr rfl fun k hk ↦ indicator_of_mem
            (hK_min k (Finset.mem_range.1 hk)) _]
          simp
      _ ≤ _ := sum_le_tsum _
  have hcK : (1 - ε) ^ 2 * ε ^ K ≤
      (1 - ε) * ∑' k, (1 - ε) * ε ^ k * (G k).indicator (1 : Ω → ℝ≥0∞) ω := by
    calc (1 - ε) ^ 2 * ε ^ K = (1 - ε) * ((1 - ε) * ε ^ K * (G K).indicator 1 ω) := by
          rw [indicator_of_mem hK_mem, Pi.one_apply]
          ring
      _ ≤ _ := by
          gcongr
          exact le_tsum (fun k ↦ (1 - ε) * ε ^ k * (G k).indicator (1 : Ω → ℝ≥0∞) ω) K
  have hcK0 : (1 - ε) ^ 2 * ε ^ K ≠ 0 := mul_ne_zero (pow_ne_zero _ h1ε) (pow_ne_zero _ hε0)
  refine ⟨(hcK0.bot_lt.trans_le hcK).ne', ?_⟩
  have hA : (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal : ℝ≥0∞) : EReal) =
      ENNReal.log ((1 - ε) ^ 2)⁻¹ :=
    EReal.coe_toENNReal (ENNReal.zero_le_log_iff.2 (ENNReal.one_le_inv.2
      (pow_le_one₀ zero_le tsub_le_self)))
  have hB : (((ENNReal.log ε⁻¹).toENNReal : ℝ≥0∞) : EReal) = ENNReal.log ε⁻¹ :=
    EReal.coe_toENNReal (ENNReal.zero_le_log_iff.2 (ENNReal.one_le_inv.2 hε1.le))
  calc _ ≤ ENNReal.log ((1 - ε) ^ 2 * ε ^ K)⁻¹ := ENNReal.log_le_log (ENNReal.inv_le_inv.2 hcK)
    _ = (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal + K * (ENNReal.log ε⁻¹).toENNReal : ℝ≥0∞) :
          EReal) := by
        rw [ENNReal.mul_inv (.inl (pow_ne_zero _ h1ε)) (.inl (ENNReal.pow_ne_top h1ε_top)),
          ENNReal.log_mul_add, ENNReal.inv_pow (a := ε), ENNReal.log_pow, EReal.coe_ennreal_add,
          EReal.coe_ennreal_mul, hA, hB]
        simp
    _ ≤ _ := by gcongr

/-- **The mixture of [EVR26, Note 48, Lemma 1].** If `q` is approximately dominated by members of
a σ-convex set `𝒞`, then for `ε ∈ (0, 1)` and `δ ∈ (0, ∞)` some `m ∈ 𝒞` has largest e-power at
most that of `μ.withDensity q` plus `log ((1 - ε) ^ 2)⁻¹ + log ε⁻¹ * δ`. -/
private lemma exists_maxEPower_singleton_le [IsProbabilityMeasure Q] (h𝒞 : IsSigmaConvex 𝒞)
    {q : Ω → ℝ≥0∞} (hq : q ∈ approxDominated μ Q 𝒞) {ε δ : ℝ≥0∞} (hε0 : ε ≠ 0) (hε1 : ε < 1)
    (hδ0 : δ ≠ 0) (hδ : δ ≠ ∞) :
    ∃ m ∈ 𝒞, maxEPower Q {m} ≤ maxEPower Q {μ.withDensity q} +
      (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal + (ENNReal.log ε⁻¹).toENNReal * δ : ℝ≥0∞) :
        EReal) := by
  obtain ⟨hq_meas, H⟩ := hq
  have h1ε : 1 - ε ≠ 0 := (tsub_pos_of_lt hε1).ne'
  have h1ε_lt : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε0
  -- members `m k` with sub-densities `p k` that dominate `(1 - ε) * q` outside sets of
  -- measures `δs k`, of sum at most `δ`, mixed with the weights `w k = (1 - ε) * ε ^ k`
  obtain ⟨δs, hδs0, hδs⟩ := ENNReal.exists_pos_sum_of_countable' hδ0 ℕ
  choose m hm p hp hle hQ using fun k ↦ H (1 - ε) h1ε_lt (δs k) (hδs0 k).ne'
  set w : ℕ → ℝ≥0∞ := fun k ↦ (1 - ε) * ε ^ k with hw_def
  have hw : ∑' k, w k = 1 := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ENNReal.mul_inv_cancel h1ε (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  -- the good sets `G k`, where `p k` dominates `(1 - ε) * q`, the factor `c` and the number `N`
  -- of bad indices
  set G : ℕ → Set Ω := fun k ↦ {ω | (1 - ε) * q ω ≤ p k ω} with hG_def
  have hG (k : ℕ) : MeasurableSet (G k) := measurableSet_le (hq_meas.const_mul _) (hp k)
  set c : Ω → ℝ≥0∞ := fun ω ↦ (1 - ε) * ∑' k, w k * (G k).indicator 1 ω with hc_def
  have hc_meas : Measurable c :=
    (Measurable.tsum fun k ↦ (measurable_one.indicator (hG k)).const_mul _).const_mul _
  set N : Ω → ℝ≥0∞ := fun ω ↦ ∑' k, (G k)ᶜ.indicator 1 ω with hN_def
  have hN_meas : Measurable N := Measurable.tsum fun k ↦ measurable_one.indicator (hG k).compl
  have hN_int : ∫⁻ ω, N ω ∂Q ≤ δ := by
    rw [lintegral_tsum fun k ↦ (measurable_one.indicator (hG k).compl).aemeasurable]
    refine (tsum_le_tsum fun k ↦ ?_).trans hδs.le
    rw [lintegral_indicator_one (hG k).compl]
    convert hQ k using 2
    ext ω
    simp [hG_def]
  have hN_fin : ∀ᵐ ω ∂Q, N ω ≠ ∞ :=
    (ae_lt_top hN_meas (ne_top_of_le_ne_top hδ hN_int)).mono fun _ h ↦ h.ne
  have h_bound (ω : Ω) (hω : N ω ≠ ∞) := log_inv_mixtureFactor_le hε0 hε1 hω
  set A := (ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal with hA_def
  set B := (ENNReal.log ε⁻¹).toENNReal with hB_def
  -- the expected value of `log c⁻¹` is at most `A + B * δ`
  have hlog_int : ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q ≤ ((A + B * δ : ℝ≥0∞) : EReal) := by
    calc ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q ≤ ∫ᵉ ω, ((A + N ω * B : ℝ≥0∞) : EReal) ∂Q :=
          eintegral_mono_ae (hN_fin.mono fun ω hω ↦ (h_bound ω hω).2)
      _ = ((∫⁻ ω, A + N ω * B ∂Q : ℝ≥0∞) : EReal) := eintegral_coe_ennreal _
      _ ≤ ((A + B * δ : ℝ≥0∞) : EReal) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_mul_const _ hN_meas, mul_comm]
          gcongr
  have hAB_top : A + B * δ ≠ ∞ := ENNReal.add_ne_top.2
    ⟨by simp [hA_def, ENNReal.inv_eq_top, h1ε], ENNReal.mul_ne_top (by simp [hB_def, hε0]) hδ⟩
  -- the mixture dominates `μ.withDensity (q * c)`, since `q * c ≤ ∑' k, w k * p k`
  refine ⟨Measure.sum fun k ↦ w k • m k, h𝒞.sum_smul_mem hw hm, ?_⟩
  refine (maxEPower_singleton_le_add_eintegral_log_inv (ν := μ.withDensity q) hc_meas
    (fun ω ↦ ?_) (hN_fin.mono fun ω hω ↦ (h_bound ω hω).1) ?_
    (ne_top_of_le_ne_top ((EReal.coe_ennreal_eq_top_iff.not).2 hAB_top) hlog_int)).trans
    (add_le_add_right hlog_int _)
  · calc c ω ≤ (1 - ε) * ∑' k, w k := by
          simp only [hc_def]
          gcongr with k
          refine mul_le_of_le_one_right' ?_
          by_cases h : ω ∈ G k <;> simp [h]
      _ ≤ 1 := by rw [hw, mul_one]; exact tsub_le_self
  rw [← withDensity_mul μ hq_meas hc_meas]
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [withDensity_apply _ hs, Measure.sum_apply _ hs]
  calc ∫⁻ ω in s, (q * c) ω ∂μ ≤ ∫⁻ ω in s, ∑' k, w k * p k ω ∂μ := by
        refine lintegral_mono fun ω ↦ ?_
        simp only [Pi.mul_apply, hc_def, ← ENNReal.tsum_mul_left]
        refine tsum_le_tsum fun k ↦ ?_
        by_cases hω : ω ∈ G k
        · simp only [indicator_of_mem hω, Pi.one_apply, mul_one]
          calc q ω * ((1 - ε) * w k) = w k * ((1 - ε) * q ω) := by ring
            _ ≤ w k * p k ω := by
              rw [hG_def, mem_ofPred_eq] at hω
              gcongr
        · simp [indicator_of_notMem hω]
    _ = ∑' k, w k * ∫⁻ ω in s, p k ω ∂μ := by
        rw [lintegral_tsum fun k ↦ ((hp k).const_mul _).aemeasurable]
        exact tsum_congr fun k ↦ lintegral_const_mul _ (hp k)
    _ ≤ ∑' k, (w k • m k) s := tsum_le_tsum fun k ↦ by
        rw [smul_apply, smul_eq_mul, ← withDensity_apply _ hs]
        gcongr
        exact hle k

/-- **Letting the cost of the mixture tend to `0`.** If `0 ≤ v ≤ x` and `x` is at most `v` plus
`log ((1 - ε) ^ 2)⁻¹ + log ε⁻¹ * δ` for all `ε ∈ (0, 1)` and `δ ∈ (0, ∞)`, then `x ≤ v`. -/
private lemma le_of_forall_le_add_mixtureCost {x v : EReal} (hv : 0 ≤ v) (hvx : v ≤ x)
    (key : ∀ ε δ : ℝ≥0∞, ε ≠ 0 → ε < 1 → δ ≠ 0 → δ ≠ ∞ → x ≤ v +
      (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal + (ENNReal.log ε⁻¹).toENNReal * δ : ℝ≥0∞) :
        EReal)) :
    x ≤ v := by
  -- work in `ℝ≥0∞`
  have h0' : 0 ≤ x := hv.trans hvx
  rw [← EReal.coe_toENNReal hv, ← EReal.coe_toENNReal h0', EReal.coe_ennreal_le_coe_ennreal_iff]
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos (by exact_mod_cast hη.ne')
  -- choose `ε` with `log ((1 - ε) ^ 2)⁻¹ < η / 2`
  have h_cont : Continuous fun ε : ℝ≥0∞ ↦ (ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal :=
    EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp (continuous_inv.comp
      ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_sub_left ENNReal.one_ne_top))))
  have h_tendsto : Tendsto (fun ε : ℝ≥0∞ ↦ (ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 0) := by
    simpa using (h_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεA, hε1, hε0⟩ := ((h_tendsto.eventually (gt_mem_nhds hη2)).and
    ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)).and
      self_mem_nhdsWithin)).exists
  -- and `δ` with `log ε⁻¹ * δ = η / 2`
  set B := (ENNReal.log ε⁻¹).toENNReal
  have hB0 : B ≠ 0 := (EReal.toENNReal_pos_iff.2 (ENNReal.zero_lt_log_iff.2
    (ENNReal.one_lt_inv.2 hε1))).ne'
  have hB_top : B ≠ ∞ := by
    simp [B, ENNReal.inv_eq_top, (show ε ≠ 0 from hε0.ne')]
  have hη2_top : η / 2 ≠ ∞ := ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero
  have h := key ε (η / 2 / B) hε0.ne' hε1 (ENNReal.div_ne_zero.2 ⟨hη2.ne', hB_top⟩)
    (ENNReal.div_ne_top hη2_top hB0)
  rw [ENNReal.mul_div_cancel hB0 hB_top, ← EReal.coe_toENNReal hv, ← EReal.coe_ennreal_add] at h
  rw [← EReal.coe_toENNReal h0', EReal.coe_ennreal_le_coe_ennreal_iff] at h
  refine h.trans ?_
  gcongr
  calc _ ≤ (η : ℝ≥0∞) / 2 + η / 2 := add_le_add_left hεA.le _
    _ = η := ENNReal.add_halves _

/-! ### Countable mixtures suffice -/

/-- **Countable mixtures suffice for the largest e-power** [EVR26, Note 48, Theorem 2], for any
σ-convex set between the null and its effective null. Let `S` be a null of measures of mass at
most one, absolutely continuous with respect to a σ-finite measure `μ`, and `Q` a probability
measure. For every σ-convex `𝒞` with `S ⊆ 𝒞 ⊆ effectiveSet S`, the largest e-power of `S` under
`Q` is the infimum of the relative entropy `klIntegral Q m` over `m ∈ 𝒞`. -/
theorem maxEPower_eq_iInf_klIntegral_of_isSigmaConvex [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hSμ : ∀ P ∈ S, P ≪ μ) (hS : ∀ P ∈ S, P univ ≤ 1) (h𝒞 : IsSigmaConvex 𝒞) (hS𝒞 : S ⊆ 𝒞)
    (h𝒞S : 𝒞 ⊆ effectiveSet S) :
    maxEPower Q S = ⨅ m ∈ 𝒞, klIntegral Q m := by
  have h_le : maxEPower Q S ≤ ⨅ m ∈ 𝒞, klIntegral Q m := le_iInf₂ fun m hm ↦ by
    rw [maxEPower_eq_klInf_effectiveSet hS]
    exact klInf_le_klIntegral (h𝒞S hm)
  refine le_antisymm h_le ?_
  rcases eq_or_ne (maxEPower Q S) ⊤ with h_top | h_top
  · rw [h_top]
    exact le_top
  have hne : S.Nonempty := ne_empty_iff_nonempty.1 fun h ↦ h_top (h ▸ maxEPower_empty)
  -- the reverse information projection `μ'`, of density `q` with respect to `μ`
  set μ' := ripr Q S
  have hμ' : μ' ∈ effectiveSet S := ripr_mem_effectiveSet Q hS
  have hμ'_le : μ' univ ≤ 1 := measure_univ_le_one_of_mem_effectiveSet hS hμ'
  have : IsFiniteMeasure μ' := isFiniteMeasure_of_mem_effectiveSet hS hμ'
  have h_eq : maxEPower Q S = klIntegral Q μ' := by
    rw [maxEPower_def]
    exact maxUtility_eq_klIntegral_ripr hS
  have hQμ' : Q ≪ μ' := by
    by_contra h
    exact h_top (h_eq.trans (klIntegral_of_not_ac h))
  have hμ'μ : μ' ≪ μ := absolutelyContinuous_of_mem_effectiveSet hμ' hSμ
  have hQμ : Q ≪ μ := hQμ'.trans hμ'μ
  have hS_fin : ∀ P ∈ S, SFinite P := fun P hP ↦
    have : IsFiniteMeasure P := ⟨(hS P hP).trans_lt ENNReal.one_lt_top⟩
    inferInstance
  -- the density of `μ'` is in the closed solid convex hull of the densities of `S`, hence it is
  -- approximately dominated by members of `𝒞`
  have hq := ((mem_effectiveSet_iff_rnDeriv_mem_closedSolidConvexHull hne hSμ hS_fin).1 hμ').2
  have hqD : μ'.rnDeriv μ ∈ approxDominated μ Q 𝒞 :=
    closedSolidConvexHull_subset
      (forall_mem_image.2 fun P hP ↦ rnDeriv_mem_approxDominated hS𝒞 hP)
      (convex_approxDominated h𝒞.convex) (isAESolid_approxDominated.mono_ac hQμ)
      (isAESeqClosed_approxDominated.mono_ac hQμ) hq
  have hμ'_eq : μ.withDensity (μ'.rnDeriv μ) = μ' := Measure.withDensity_rnDeriv_eq _ _ hμ'μ
  -- the bound of the mixture, for all `ε` and `δ`
  have key {ε δ : ℝ≥0∞} (hε0 : ε ≠ 0) (hε1 : ε < 1) (hδ0 : δ ≠ 0) (hδ : δ ≠ ∞) :
      ⨅ m ∈ 𝒞, klIntegral Q m ≤ maxEPower Q S +
        (((ENNReal.log ((1 - ε) ^ 2)⁻¹).toENNReal + (ENNReal.log ε⁻¹).toENNReal * δ : ℝ≥0∞) :
          EReal) := by
    obtain ⟨m, hm, hle⟩ := exists_maxEPower_singleton_le h𝒞 hqD hε0 hε1 hδ0 hδ
    rw [hμ'_eq, maxEPower_singleton hμ'_le, ← h_eq,
      maxEPower_singleton (measure_univ_le_one_of_mem_effectiveSet hS (h𝒞S hm))] at hle
    exact (iInf₂_le m hm).trans hle
  exact le_of_forall_le_add_mixtureCost (maxEPower_nonneg Q hS) h_le
    fun ε δ hε0 hε1 hδ0 hδ ↦ key hε0 hε1 hδ0 hδ

/-- **Countable mixtures suffice for the largest e-power** [EVR26, Note 48, Theorem 2]. For a null
`S` of measures of mass at most one, absolutely continuous with respect to a σ-finite measure, and
a probability measure `Q`, the largest e-power of `S` under `Q` is the infimum of the relative
entropy `klIntegral Q m` over the countable mixtures `m = ∑ n, w n • P n` of members of `S`, with
no other hypothesis. -/
theorem maxEPower_eq_iInf_klIntegral_sigmaConvexHull [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hSμ : ∀ P ∈ S, P ≪ μ) (hS : ∀ P ∈ S, P univ ≤ 1) :
    maxEPower Q S = ⨅ m ∈ sigmaConvexHull S, klIntegral Q m :=
  maxEPower_eq_iInf_klIntegral_of_isSigmaConvex hSμ hS isSigmaConvex_sigmaConvexHull
    subset_sigmaConvexHull (isSigmaConvex_effectiveSet.sigmaConvexHull_subset subset_effectiveSet)

open InformationTheory in
/-- **Countable mixtures suffice for the largest e-power, on a countable alphabet.** On a countable
alphabet with measurable singletons, the largest e-power of a set `S` of probability measures
under a probability measure `Q` is the infimum of the relative entropies `KL(Q ‖ m)` over the
countable mixtures `m` of members of `S`: the counting measure dominates every measure. -/
theorem toENNReal_maxEPower_eq_iInf_klDiv [Countable Ω] [MeasurableSingletonClass Ω]
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (Q : Measure Ω) [IsProbabilityMeasure Q] :
    (maxEPower Q S).toENNReal = ⨅ m ∈ sigmaConvexHull S, klDiv Q m := by
  rw [maxEPower_eq_iInf_klIntegral_sigmaConvexHull (μ := Measure.count)
    (fun P _ s hs ↦ by rw [Measure.count_eq_zero_iff] at hs; simp [hs])
    (fun P hP ↦ (hS P hP).measure_univ.le)]
  have hm : ∀ m ∈ sigmaConvexHull S, klIntegral Q m = (klDiv Q m : EReal) := fun m hm ↦ by
    have := isProbabilityMeasure_of_mem_sigmaConvexHull hS hm
    exact klIntegral_eq_klDiv (by simp)
  rw [iInf_congr fun m ↦ iInf_congr fun hm' ↦ hm m hm']
  simp_rw [← EReal.coe_ennreal_iInf]
  rw [EReal.toENNReal_coe]

end ProbabilityTheory
