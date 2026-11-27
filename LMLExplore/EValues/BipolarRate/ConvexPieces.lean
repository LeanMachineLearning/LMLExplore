/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
public import LMLExplore.Probability.Distributions.ProdBernoulli
public import Mathlib.Probability.Process.HittingTime
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import LMLExplore.EValues.BipolarRate.EProcess
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.InformationTheory.KullbackLeibler.Finite
import LMLExplore.MeasureTheory.Measure.Real
import LMLExplore.Probability.Independence.LastExit
import LMLExplore.Probability.Process.LevelCrossing
import Mathlib.Probability.Independence.InfinitePi
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import TauCeti.InformationTheory.KullbackLeibler.Basic
import TauCeti.Probability.StrongLaw

/-!
# The minimum of likelihood ratios over convex pieces of a null

For a null `S₁` that is not convex, whose members charge every point, the tests of the test
supermartingales of its i.i.d. null need at least `log (1/α) / a₁` observations in expectation,
with `a₁ = maxEPower Q₁ S₁` the rate of one observation
(`ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_hittingAfter`), which can be much
smaller than the optimal rate `d = bipolarRate Q₁ S₁`. When the null is a finite union of convex
pieces of a parametric family, the rate `KL_inf` is reached by an e-process that is not, in
general, a test supermartingale: the minimum over the pieces of the likelihood ratio processes of
the alternative against its projections on the pieces, a sequential intersection–union test
[EVR26, Note 32, Statement 2].

**The minimum of likelihood ratios.** On a discrete alphabet `𝓧`, for laws `Q` and `P j`, `j` in a
type `κ`, the process `minLikelihoodRatio Q P` is `⨅ j, ∏ k < n, Q {ω k} / P j {ω k}` at time `n`.
On a finite alphabet, with `κ` finite and `Q ≪ P j` for every `j`, the logarithm of the product
for `j` is a random walk with bounded increments of mean `KL(Q ‖ P j)` under the i.i.d. law of
`Q`. By the strong law of large numbers (Tau Ceti's `strong_law_ae_infinitePi`) and dominated
convergence, `(1/n) log` of the minimum tends to `min_j KL(Q ‖ P j)` almost surely and in
expectation; and since finitely many walks with bounded increments are above `c n` from a time of
finite mean on, for every `c` below their drifts
(`ProbabilityTheory.exists_lintegral_ne_top_forall_ge_mul_le_sum`), the test that rejects when the
minimum reaches `α⁻¹` makes at most `(1 + o(1)) log (1/α) / min_j KL(Q ‖ P j)` observations in
expectation (`ProbabilityTheory.limsup_lintegral_hittingAfter_div_log_le`).

**Convex pieces of independent coins.** In the model of [EVR26, Note 32], an observation is a
vector of `ι` independent coins with law `prodBernoulli θ`; the null is the set of the laws
`prodBernoulli θ` for `θ` in a union of convex sets `C j ⊆ [0, 1] ^ ι`, `j` in a finite type, the
alternative is `prodBernoulli ψ`, and `η j ∈ C j`, in the open cube, minimizes
`θ ↦ KL(prodBernoulli ψ ‖ prodBernoulli θ)` over `C j`. Under `prodBernoulli θ`, the likelihood
ratio of `prodBernoulli ψ` against `prodBernoulli (η j)` has expectation `∏ i, (1 + u i)` with
`u i = (θ i - η i) (ψ i - η i) / (η i (1 - η i))`, and `∑ i, u i ≤ 0` is the first-order condition
of the minimization over the convex set `C j`, so the expectation is at most `exp (∑ i, u i) ≤ 1`:
the likelihood ratio is an e-variable for the piece, and the product of its values at the
observations is a test supermartingale for the sequential null of the piece. The minimum over
the pieces is below each of them, so it is an e-process for every law under which the
observations are drawn sequentially from one piece, in particular for the i.i.d. null. The
minimal relative entropies to the pieces are attained at the `η j`, so the rate is `KL_inf`, and
since the expected logarithm of an e-process at time `n` is at most `maxLogGrowth` at `n`
(`ProbabilityTheory.IsEProcess.eintegral_log_le_maxLogGrowth`), the bipolar rate is `KL_inf`. The
test of the minimum then attains the lower bound `log (1/α) / d` on expected stopping times
(`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`) to first order.

## Main definitions

* `ProbabilityTheory.minLikelihoodRatio Q P`: the minimum over `j` of the likelihood ratio
  processes of `Q` against `P j` on a discrete alphabet.

## Main statements

* `ProbabilityTheory.ae_tendsto_log_minLikelihoodRatio_div`,
  `ProbabilityTheory.tendsto_eintegral_log_minLikelihoodRatio_div`: on a finite alphabet,
  `(1/n) log` of the minimum tends to `min_j KL(Q ‖ P j)`, almost surely and in expectation.
* `ProbabilityTheory.limsup_lintegral_hittingAfter_minLikelihoodRatio_div_log_le`: its test of level
  `α` makes at most `(1 + o(1)) log (1/α) / min_j KL(Q ‖ P j)` observations in expectation.
* `ProbabilityTheory.isEVar_prodBernoulli_div_prodBernoulli`,
  `ProbabilityTheory.isTestSupermartingale_prod_prodBernoulli_div_prodBernoulli`
  [EVR26, Note 32, Statement 2]: the likelihood ratio against the projection on a convex set of
  coins is an e-variable for that set, and its products are a test supermartingale for its
  sequential null.
* `ProbabilityTheory.isEProcess_minLikelihoodRatio_prodBernoulli`,
  `ProbabilityTheory.isLevelStoppingTime_hittingAfter_minLikelihoodRatio_prodBernoulli`
  [EVR26, Note 32, Statement 2]: the minimum over the pieces is an e-process for the union of the
  sequential nulls of the pieces, and its test of level `α` has level `α`.
* `ProbabilityTheory.ae_tendsto_log_minLikelihoodRatio_prodBernoulli_div`,
  `ProbabilityTheory.bipolarRate_prodBernoulli_iUnion_eq_klInf` [EVR26, Note 32, Statement 2]:
  `(1/n) log` of the minimum tends to `KL_inf` almost surely, and the bipolar rate is `KL_inf`.
* `ProbabilityTheory.tendsto_lintegral_hittingAfter_minLikelihoodRatio_prodBernoulli_div_log`
  [EVR26, Note 32, Statement 2]: the test makes `(1 + o(1)) log (1/α) / KL_inf` observations in
  expectation as `α → 0`.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/ConvexPieces.lean` (commit
`83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore: the growth of the minimum of likelihood ratios is stated for any laws on a finite
alphabet, and the bipolar rate is computed from the e-process.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 κ : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### The minimum of likelihood ratios on a discrete alphabet -/

/-- The minimum over `j` of the likelihood ratio processes of `Q` against `P j` on a discrete
alphabet: at time `n`, `⨅ j, ∏ k < n, Q {ω k} / P j {ω k}`, a function of the first `n`
observations. -/
noncomputable def minLikelihoodRatio (Q : Measure 𝓧) (P : κ → Measure 𝓧) (n : ℕ) (ω : ℕ → 𝓧) :
    ℝ≥0∞ :=
  ⨅ j, ∏ k ∈ Finset.range n, Q {ω k} / P j {ω k}

/-- The value of `minLikelihoodRatio`. -/
theorem minLikelihoodRatio_def (Q : Measure 𝓧) (P : κ → Measure 𝓧) (n : ℕ) (ω : ℕ → 𝓧) :
    minLikelihoodRatio Q P n ω = ⨅ j, ∏ k ∈ Finset.range n, Q {ω k} / P j {ω k} :=
  (rfl)

/-- The minimum of the likelihood ratios is at most each of them. -/
theorem minLikelihoodRatio_le (Q : Measure 𝓧) (P : κ → Measure 𝓧) (j : κ) (n : ℕ)
    (ω : ℕ → 𝓧) : minLikelihoodRatio Q P n ω ≤ ∏ k ∈ Finset.range n, Q {ω k} / P j {ω k} :=
  iInf_le _ j

/-- On a countable alphabet with measurable singletons, the minimum of countably many likelihood
ratio processes is adapted to the filtration `Filtration.piLT` of the past observations. -/
theorem adapted_minLikelihoodRatio [Countable 𝓧] [MeasurableSingletonClass 𝓧] [Countable κ]
    (Q : Measure 𝓧) (P : κ → Measure 𝓧) :
    Adapted Filtration.piLT (minLikelihoodRatio Q P) := fun _ ↦
  Measurable.iInf fun j ↦ Finset.measurable_prod _ fun _ hk ↦
    (measurable_of_countable fun x : 𝓧 ↦ Q {x} / P j {x}).comp
      (Filtration.measurable_piLT_apply (Finset.mem_range.1 hk))

variable [MeasurableSingletonClass 𝓧] {Q : Measure 𝓧} {P : κ → Measure 𝓧}

/-- On a finite alphabet, the minimum of the relative entropies from a finite measure `Q` to
measures `P j` with `Q ≪ P j`, all finite, as an extended real, is the minimum of their real
values. -/
private lemma coe_iInf_klDiv_eq [Finite 𝓧] [Fintype κ] [Nonempty κ] [IsFiniteMeasure Q]
    (hQP : ∀ j, Q ≪ P j) :
    ((⨅ j, klDiv Q (P j) : ℝ≥0∞) : EReal) =
      ((Finset.univ.inf' Finset.univ_nonempty fun j ↦ (klDiv Q (P j)).toReal : ℝ) : EReal) := by
  have hne (j : κ) : klDiv Q (P j) ≠ ∞ := klDiv_ne_top_iff.2 ⟨hQP j, Integrable.of_finite⟩
  rw [Finset.inf'_univ_eq_ciInf, ← ENNReal.toReal_iInf hne,
    EReal.coe_ennreal_toReal (ne_top_of_le_ne_top (hne (Classical.arbitrary κ))
      (iInf_le (fun j ↦ klDiv Q (P j)) (Classical.arbitrary κ)))]

omit [MeasurableSingletonClass 𝓧] in
/-- **The logarithm of the minimum of the likelihood ratios** on a path of atoms of `Q` and of the
`P j` is the minimum of the sums of the log-likelihood ratios. -/
private lemma log_minLikelihoodRatio_eq [Fintype κ] [Nonempty κ] [IsFiniteMeasure Q]
    [∀ j, IsFiniteMeasure (P j)] {ω : ℕ → 𝓧} (hQ : ∀ k, Q {ω k} ≠ 0)
    (hP : ∀ j k, P j {ω k} ≠ 0) (n : ℕ) :
    ENNReal.log (minLikelihoodRatio Q P n ω) = ((Finset.univ.inf' Finset.univ_nonempty fun j ↦
      ∑ k ∈ Finset.range n, Real.log (Q.real {ω k} / (P j).real {ω k}) : ℝ) : EReal) := by
  -- each product of ratios is the exponential of the sum of the logarithms of the real ratios
  have hprod (j : κ) : ∏ k ∈ Finset.range n, Q {ω k} / P j {ω k} = ENNReal.ofReal (Real.exp
      (∑ k ∈ Finset.range n, Real.log (Q.real {ω k} / (P j).real {ω k}))) := by
    rw [prod_measure_div_eq_ofReal_prod fun k _ ↦ hP j k, Real.exp_sum]
    exact congrArg ENNReal.ofReal (Finset.prod_congr rfl fun k _ ↦ (Real.exp_log (div_pos
      (measureReal_pos_of_ne_zero (hQ k)) (measureReal_pos_of_ne_zero (hP j k)))).symm)
  set S : κ → ℝ := fun j ↦ ∑ k ∈ Finset.range n, Real.log (Q.real {ω k} / (P j).real {ω k})
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty S
  have hM : minLikelihoodRatio Q P n ω = ENNReal.ofReal (Real.exp (S j₀)) := by
    simp_rw [minLikelihoodRatio_def, hprod]
    refine le_antisymm (iInf_le _ j₀) (le_iInf fun j ↦ ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_))
    rw [← hj₀]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  rw [hM, ENNReal.log_ofReal]
  simp only [(Real.exp_pos (S j₀)).not_ge, ite_false, Real.log_exp]
  rw [hj₀]

omit [MeasurableSingletonClass 𝓧] in
/-- Almost surely under the i.i.d. law of `Q`, every observation is an atom of `Q`, and of every
`P j` with `Q ≪ P j`. -/
private lemma ae_forall_measure_singleton_ne_zero [Countable 𝓧] [IsProbabilityMeasure Q]
    (hQP : ∀ j, Q ≪ P j) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), (∀ k, Q {ω k} ≠ 0) ∧ ∀ j k, P j {ω k} ≠ 0 := by
  filter_upwards [Measure.ae_forall_apply_infinitePi (fun _ : ℕ ↦ Q)
    (p := fun _ y ↦ Q {y} ≠ 0) fun _ ↦ ae_iff_of_countable.2 fun _ h ↦ h] with ω hω
  exact ⟨hω, fun j k h ↦ hω k (hQP j h)⟩

omit [MeasurableSingletonClass 𝓧] in
/-- On finite types, the log-likelihood ratios of `Q` against the `P j` are bounded by a
nonnegative constant. -/
private lemma exists_forall_abs_log_div_le [Finite 𝓧] [Finite κ] :
    ∃ B, 0 ≤ B ∧ ∀ j x, |Real.log (Q.real {x} / (P j).real {x})| ≤ B := by
  obtain ⟨B, hB⟩ := Finite.bddAbove_range
    fun p : κ × 𝓧 ↦ |Real.log (Q.real {p.2} / (P p.1).real {p.2})|
  exact ⟨max B 0, le_max_right _ _, fun j x ↦ (hB ⟨(j, x), rfl⟩).trans (le_max_left _ _)⟩

/-- **The strong law for the minimum of the log-likelihood ratios.** Almost surely under the
i.i.d. law of `Q`, the minimum over `j` of the sums of the log-likelihood ratios against `P j`,
divided by `n`, tends to the minimum of the relative entropies. -/
private lemma ae_tendsto_inf'_sum_log_div [Finite 𝓧] [Fintype κ] [Nonempty κ]
    [IsProbabilityMeasure Q] [∀ j, IsProbabilityMeasure (P j)] (hQP : ∀ j, Q ≪ P j) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun n : ℕ ↦ (Finset.univ.inf' Finset.univ_nonempty fun j ↦
          ∑ k ∈ Finset.range n, Real.log (Q.real {ω k} / (P j).real {ω k})) / n)
        atTop (𝓝 (Finset.univ.inf' Finset.univ_nonempty fun j ↦ (klDiv Q (P j)).toReal)) := by
  have hslln : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ j,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n,
          Real.log (Q.real {ω k} / (P j).real {ω k})) atTop (𝓝 (klDiv Q (P j)).toReal) := by
    refine ae_all_iff.2 fun j ↦ ?_
    have := TauCeti.Probability.strong_law_ae_infinitePi Q
      (f := fun x ↦ Real.log (Q.real {x} / (P j).real {x})) Integrable.of_finite
    rwa [LMLExplore.integral_log_measureReal_div_eq_toReal_klDiv (hQP j)] at this
  filter_upwards [hslln] with ω hω
  refine (Tendsto.finset_inf'_nhds (s := Finset.univ) Finset.univ_nonempty
    fun j _ ↦ hω j).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.inf'_apply, Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty (· / (n : ℝ))
    fun x y ↦ (min_div_div_right hn'.le x y).symm]
  simp only [Function.comp_def, smul_eq_mul, div_eq_inv_mul]

/-- **The minimum of the likelihood ratios grows at the smallest relative entropy, almost
surely.** On a finite alphabet, let `Q` and `P j`, for `j` in a finite type, be probability
measures with `Q ≪ P j`. Almost surely under the i.i.d. law of `Q`, `(1/n) log` of the minimum
over `j` of the likelihood ratios of `Q` against `P j` tends to `min_j KL(Q ‖ P j)`. -/
theorem ae_tendsto_log_minLikelihoodRatio_div [Finite 𝓧] [Finite κ] (Q : Measure 𝓧)
    [IsProbabilityMeasure Q] [∀ j, IsProbabilityMeasure (P j)] (hQP : ∀ j, Q ≪ P j) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun n : ℕ ↦ ENNReal.log (minLikelihoodRatio Q P n ω) / (n : EReal)) atTop
        (𝓝 ((⨅ j, klDiv Q (P j) : ℝ≥0∞) : EReal)) := by
  have := Fintype.ofFinite κ
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine .of_forall fun ω ↦ tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [minLikelihoodRatio_def, iInf_of_empty, iInf_of_empty, ENNReal.log_top,
      EReal.top_div_of_pos_ne_top (by exact_mod_cast hn) (EReal.natCast_ne_top n),
      EReal.coe_ennreal_top]
  filter_upwards [ae_tendsto_inf'_sum_log_div hQP, ae_forall_measure_singleton_ne_zero hQP]
    with ω hω hpos
  rw [coe_iInf_klDiv_eq hQP]
  refine ((continuous_coe_real_ereal.tendsto _).comp hω).congr' ?_
  filter_upwards with n
  rw [log_minLikelihoodRatio_eq hpos.1 hpos.2 n, Function.comp_apply, ← EReal.coe_natCast,
    EReal.coe_div]

/-- **The minimum of the likelihood ratios grows at the smallest relative entropy, in
expectation.** Under the hypotheses of `ae_tendsto_log_minLikelihoodRatio_div`, the expected
logarithm of the minimum of the likelihood ratios at time `n`, divided by `n`, tends to
`min_j KL(Q ‖ P j)`: the log-likelihood ratios are bounded on a finite alphabet, and dominated
convergence applies. -/
theorem tendsto_eintegral_log_minLikelihoodRatio_div [Finite 𝓧] [Finite κ] (Q : Measure 𝓧)
    [IsProbabilityMeasure Q] [∀ j, IsProbabilityMeasure (P j)] (hQP : ∀ j, Q ≪ P j) :
    Tendsto (fun n : ℕ ↦ (∫ᵉ ω, ENNReal.log (minLikelihoodRatio Q P n ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q)) / (n : EReal)) atTop
      (𝓝 ((⨅ j, klDiv Q (P j) : ℝ≥0∞) : EReal)) := by
  classical
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite 𝓧
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [minLikelihoodRatio_def, iInf_of_empty, ENNReal.log_top, eintegral_const,
      measure_univ, EReal.coe_ennreal_one, mul_one, EReal.coe_ennreal_top]
    rw [EReal.top_div_of_pos_ne_top (by exact_mod_cast hn) (EReal.natCast_ne_top n)]
  set L : κ → 𝓧 → ℝ := fun j x ↦ Real.log (Q.real {x} / (P j).real {x})
  set F : ℕ → (ℕ → 𝓧) → ℝ := fun n ω ↦
    Finset.univ.inf' Finset.univ_nonempty fun j ↦ ∑ k ∈ Finset.range n, L j (ω k) with hF
  -- a bound on the log-likelihood ratios, on a finite alphabet
  obtain ⟨c, hc0, hcL⟩ := exists_forall_abs_log_div_le (Q := Q) (P := P)
  have hFbound (n : ℕ) (ω : ℕ → 𝓧) : |F n ω| ≤ n * c := by
    have hS (j : κ) : |∑ k ∈ Finset.range n, L j (ω k)| ≤ n * c := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ c fun k _ ↦ hcL j (ω k)).trans ?_
      simp
    refine abs_le.2 ⟨Finset.le_inf' _ _ fun j _ ↦ (abs_le.1 (hS j)).1, ?_⟩
    obtain ⟨j₀, -, h₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      fun j ↦ ∑ k ∈ Finset.range n, L j (ω k)
    rw [hF]
    dsimp only
    rw [h₀]
    exact (abs_le.1 (hS j₀)).2
  have hFmeas (n : ℕ) : Measurable (F n) := by
    simp_rw [hF, Finset.inf'_univ_eq_ciInf]
    exact Measurable.iInf fun j ↦ Finset.measurable_sum _ fun k _ ↦
      (measurable_of_countable (L j)).comp (measurable_pi_apply k)
  have hFint (n : ℕ) : Integrable (F n) (Measure.infinitePi fun _ : ℕ ↦ Q) :=
    Integrable.of_bound (hFmeas n).aestronglyMeasurable (n * c)
      (.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hFbound n ω)
  have heint (n : ℕ) : ∫ᵉ ω, ENNReal.log (minLikelihoodRatio Q P n ω)
      ∂Measure.infinitePi (fun _ : ℕ ↦ Q) =
        ((∫ ω, F n ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q) : ℝ) : EReal) := by
    rw [← eintegral_eq_integral (hFint n)]
    refine eintegral_congr_ae ?_
    filter_upwards [ae_forall_measure_singleton_ne_zero hQP] with ω hpos
    exact log_minLikelihoodRatio_eq hpos.1 hpos.2 n
  -- dominated convergence for `F n / n`
  have hlim : Tendsto (fun n : ℕ ↦ ∫ ω, F n ω / n ∂Measure.infinitePi (fun _ : ℕ ↦ Q)) atTop
      (𝓝 (Finset.univ.inf' Finset.univ_nonempty fun j ↦ (klDiv Q (P j)).toReal)) := by
    have := tendsto_integral_of_dominated_convergence (μ := Measure.infinitePi fun _ : ℕ ↦ Q)
      (F := fun n ω ↦ F n ω / n)
      (f := fun _ ↦ Finset.univ.inf' Finset.univ_nonempty fun j ↦ (klDiv Q (P j)).toReal)
      (fun _ ↦ c) (fun n ↦ ((hFmeas n).div_const _).aestronglyMeasurable) (integrable_const c)
      (fun n ↦ .of_forall fun ω ↦ ?_) (ae_tendsto_inf'_sum_log_div hQP)
    · simpa using this
    · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hc0
      · rw [div_le_iff₀ (by exact_mod_cast hn), mul_comm]
        exact hFbound n ω
  rw [coe_iInf_klDiv_eq hQP]
  refine ((continuous_coe_real_ereal.tendsto _).comp hlim).congr' ?_
  filter_upwards with n
  rw [heint n, Function.comp_apply, integral_div, ← EReal.coe_natCast, EReal.coe_div]

/-- **The test of the minimum of the likelihood ratios is fast.** Under the hypotheses of
`ae_tendsto_log_minLikelihoodRatio_div`, the first time `τ α` at which the minimum of the
likelihood ratios reaches `α⁻¹` satisfies
`limsup_{α → 0} 𝔼[τ α] / log (1/α) ≤ 1 / min_j KL(Q ‖ P j)` under the i.i.d. law of `Q`: for
every `c` below the drifts `KL(Q ‖ P j)` of the walks of the log-likelihood ratios, which have
bounded increments, the walks are all above `c n` from a time of finite mean on. -/
theorem limsup_lintegral_hittingAfter_minLikelihoodRatio_div_log_le [Finite 𝓧] [Finite κ]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] [∀ j, IsProbabilityMeasure (P j)]
    (hQP : ∀ j, Q ≪ P j) :
    limsup (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter (minLikelihoodRatio Q P) (Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q)) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) ≤
      (⨅ j, klDiv Q (P j))⁻¹ := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite 𝓧
  have h := limsup_lintegral_hittingAfter_div_log_le (E := minLikelihoodRatio Q P)
    (Q := Measure.infinitePi fun _ : ℕ ↦ Q) (L := ((⨅ j, klDiv Q (P j) : ℝ≥0∞) : EReal))
    fun c hc hcL ↦ ?_
  · rwa [EReal.toENNReal_coe] at h
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun _ ↦ 0, by simp, .of_forall fun ω k _ ↦ by simp [minLikelihoodRatio_def]⟩
  rw [coe_iInf_klDiv_eq hQP, EReal.coe_lt_coe_iff] at hcL
  -- the walks of the log-likelihood ratios, with bounded increments
  set L : κ → 𝓧 → ℝ := fun j x ↦ Real.log (Q.real {x} / (P j).real {x})
  obtain ⟨B, -, hLB⟩ := exists_forall_abs_log_div_le (Q := Q) (P := P)
  -- their drifts are the relative entropies
  have hmean (j : κ) (i : ℕ) : Finset.univ.inf' Finset.univ_nonempty
      (fun j ↦ (klDiv Q (P j)).toReal) ≤ ∫ ω, L j (ω i) ∂Measure.infinitePi (fun _ : ℕ ↦ Q) := by
    have := integral_map (μ := Measure.infinitePi fun _ : ℕ ↦ Q)
      (measurable_pi_apply i).aemeasurable (f := L j)
      (measurable_of_countable (L j)).aestronglyMeasurable
    rw [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q) i).map_eq,
      LMLExplore.integral_log_measureReal_div_eq_toReal_klDiv (hQP j)] at this
    rw [← this]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  obtain ⟨N, hN, hNω⟩ := exists_lintegral_ne_top_forall_ge_mul_le_sum
    (μ := Measure.infinitePi fun _ : ℕ ↦ Q) (X := fun j i ω ↦ L j (ω i))
    (fun j ↦ iIndepFun_infinitePi (P := fun _ ↦ Q) (X := fun _ ↦ L j)
      fun _ ↦ measurable_of_countable _)
    (fun j i ↦ ((measurable_of_countable (L j)).comp (measurable_pi_apply i)).aemeasurable)
    (l := -B) (u := B) (fun j i ↦ .of_forall fun ω ↦ abs_le.1 (hLB j (ω i))) hmean hcL
  refine ⟨N, hN, ?_⟩
  filter_upwards [hNω, ae_forall_measure_singleton_ne_zero hQP] with ω hω hpos k hk
  rw [log_minLikelihoodRatio_eq hpos.1 hpos.2 k]
  exact EReal.coe_le_coe_iff.2 (Finset.le_inf' _ _ fun j _ ↦ hω k hk j)

/-! ### Convex pieces of independent coins -/

section Coins

variable {ι : Type*} [Fintype ι]

/-- **The first-order condition of the projection on a convex set of coins.** If `η`, in the open
cube, minimizes `θ ↦ KL(prodBernoulli ψ ‖ prodBernoulli θ)` over a convex set `C` inside the
closed cube, then for every `θ ∈ C`, `∑ i, (θ i - η i) (ψ i - η i) / (η i (1 - η i)) ≤ 0`, with
`ψ` clamped to `[0, 1]`: the derivative of the relative entropy at `η` in the direction of `θ` is
nonnegative. -/
private lemma sum_mul_div_le_zero_of_isMinOn {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hC01 : C ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ) {η θ : ι → ℝ}
    (hη01 : η ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : η ∈ C) (hθ : θ ∈ C)
    (hmin : IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) C η) :
    ∑ i, (θ i - η i) * ((projIcc 0 1 zero_le_one (ψ i) : ℝ) - η i) / (η i * (1 - η i)) ≤ 0 := by
  set ψ' : ι → ℝ := fun i ↦ (projIcc 0 1 zero_le_one (ψ i) : ℝ)
  have hη' (i : ι) : η i ∈ Ioo (0 : ℝ) 1 := hη01 i (mem_univ i)
  -- the relative entropy along the segment from `η` to `θ`, which stays in the open cube
  set g : ℝ → ℝ := fun t ↦ ∑ i, klBerReal (ψ' i) (η i + t * (θ i - η i))
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (fun i ↦ η i + t * (θ i - η i)) ∈ C := by
    convert hC.add_smul_sub_mem hη hθ ht using 1
  have hseg01 (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      (fun i ↦ η i + t * (θ i - η i)) ∈ univ.pi fun _ ↦ Ioo (0 : ℝ) 1 := fun i _ ↦ by
    have h1 := hη' i
    have h2 := hC01 hθ i (mem_univ i)
    constructor <;> nlinarith [ht.1, ht.2, h1.1, h1.2, h2.1, h2.2]
  have hg (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      g t = (klDiv (prodBernoulli ψ) (prodBernoulli fun i ↦ η i + t * (θ i - η i))).toReal :=
    (toReal_klDiv_prodBernoulli ψ (hseg01 t ht)).symm
  have hg_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : g 0 ≤ g t := by
    rw [hg 0 ⟨le_rfl, zero_lt_one⟩, hg t ⟨ht.1.le, ht.2⟩]
    simp only [zero_mul, add_zero]
    exact ENNReal.toReal_mono (klDiv_prodBernoulli_ne_top ψ (hseg01 t ⟨ht.1.le, ht.2⟩))
      (hmin (hseg t ⟨ht.1.le, ht.2.le⟩))
  -- its derivative at `0` is nonnegative
  have hderiv : HasDerivAt g (∑ i, (η i - ψ' i) / (η i * (1 - η i)) * (θ i - η i)) 0 := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    have h1 : HasDerivAt (fun t : ℝ ↦ η i + t * (θ i - η i)) (θ i - η i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (θ i - η i)).const_add (η i)
    exact (LMLExplore.hasDerivAt_klBerReal (ψ' i) (hη' i)).comp_of_eq 0 h1 (by simp)
  have hnonneg : 0 ≤ ∑ i, (η i - ψ' i) / (η i * (1 - η i)) * (θ i - η i) := by
    refine ge_of_tendsto hderiv.tendsto_slope_zero_right ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    simp only [zero_add, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.1.le) (sub_nonneg.2 (hg_le t ht))
  have heq : ∑ i, (θ i - η i) * (ψ' i - η i) / (η i * (1 - η i)) =
      -∑ i, (η i - ψ' i) / (η i * (1 - η i)) * (θ i - η i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [heq]
  exact neg_nonpos.2 hnonneg

/-- **The likelihood ratio against the projection on a convex set of coins is an e-variable**
[EVR26, Note 32, Statement 2]. Let `C` be a convex set of parameters inside the cube `[0, 1] ^ ι`,
and `η ∈ C`, in the open cube, a minimizer over `C` of the relative entropy
`θ ↦ KL(prodBernoulli ψ ‖ prodBernoulli θ)`. The likelihood ratio of `prodBernoulli ψ` against
`prodBernoulli η` is an e-variable for the laws of the coins with parameters in `C`: its
expectation under `prodBernoulli θ` is `∏ i, (1 + u i) ≤ exp (∑ i, u i)` with
`u i = (θ i - η i) (ψ i - η i) / (η i (1 - η i))`, and `∑ i, u i ≤ 0` is the first-order
condition of the minimization. -/
theorem isEVar_prodBernoulli_div_prodBernoulli {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hC01 : C ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ) {η : ι → ℝ}
    (hη01 : η ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : η ∈ C)
    (hmin : IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) C η) :
    IsEVar (fun x ↦ prodBernoulli ψ {x} / prodBernoulli η {x}) (prodBernoulli '' C) := by
  refine ⟨measurable_of_countable _, ?_⟩
  rintro _ ⟨θ, hθ, rfl⟩
  have hθ01 := hC01 hθ
  rw [← prodBernoulli_projIcc ψ, lintegral_prodBernoulli_div_prodBernoulli
    (fun i _ ↦ (projIcc 0 1 zero_le_one (ψ i)).property) hη01 hθ01]
  set ψ' : ι → ℝ := fun i ↦ (projIcc 0 1 zero_le_one (ψ i) : ℝ)
  have hfoc := sum_mul_div_le_zero_of_isMinOn hC hC01 ψ hη01 hη hθ hmin
  -- each factor is `1 + u i`, with `∑ i, u i ≤ 0`
  have hfac (i : ι) : ψ' i / η i * θ i + (1 - ψ' i) / (1 - η i) * (1 - θ i) =
      1 + (θ i - η i) * (ψ' i - η i) / (η i * (1 - η i)) := by
    have h := hη01 i (mem_univ i)
    have h0 : η i ≠ 0 := h.1.ne'
    have h1 : 1 - η i ≠ 0 := (sub_pos.2 h.2).ne'
    field_simp
    ring
  calc ∏ i, ENNReal.ofReal (ψ' i / η i * θ i + (1 - ψ' i) / (1 - η i) * (1 - θ i))
      ≤ ∏ i, ENNReal.ofReal (Real.exp ((θ i - η i) * (ψ' i - η i) / (η i * (1 - η i)))) :=
        Finset.prod_le_prod fun i _ ↦ ENNReal.ofReal_le_ofReal (by
          rw [hfac i, add_comm]
          exact Real.add_one_le_exp _)
    _ = ENNReal.ofReal (Real.exp (∑ i, (θ i - η i) * (ψ' i - η i) / (η i * (1 - η i)))) := by
        rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
    _ ≤ 1 := ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 hfoc)

/-- **The likelihood ratio process against the projection on a convex piece is a test
supermartingale** [EVR26, Note 32, Statement 2]. Under the hypotheses of
`isEVar_prodBernoulli_div_prodBernoulli`, the likelihood ratio process of `prodBernoulli ψ`
against `prodBernoulli η`, the product of the likelihood ratios of the past observations, is a
test supermartingale for the sequential null of the laws of the coins with parameters in `C`: for
every law under which every observation, given the past, has such a law. -/
theorem isTestSupermartingale_prod_prodBernoulli_div_prodBernoulli {C : Set (ι → ℝ)}
    (hC : Convex ℝ C) (hC01 : C ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ) {η : ι → ℝ}
    (hη01 : η ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : η ∈ C)
    (hmin : IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) C η) :
    IsTestSupermartingale
      (fun n ω ↦ ∏ k ∈ Finset.range n, prodBernoulli ψ {ω k} / prodBernoulli η {ω k})
      Filtration.piLT
      (sequentialNull (fun _ _ ↦ prodBernoulli '' C) (fun k ω ↦ ω k) Filtration.piLT) :=
  (isEVar_prodBernoulli_div_prodBernoulli hC hC01 ψ hη01 hη
    hmin).isTestSupermartingale_prod_sequentialNull fun k ↦
      Filtration.measurable_piLT_apply k.lt_succ_self

variable {C : κ → Set (ι → ℝ)} {η : κ → ι → ℝ}

/-- **The minimum over the convex pieces of the likelihood ratios is an e-process**
[EVR26, Note 32, Statement 2]. Let `C j`, for `j` in a countable type, be convex sets of
parameters inside the cube `[0, 1] ^ ι`, and `η j ∈ C j`, in the open cube, a minimizer over `C j`
of `θ ↦ KL(prodBernoulli ψ ‖ prodBernoulli θ)`. The minimum over `j` of the likelihood ratio
processes of `prodBernoulli ψ` against `prodBernoulli (η j)` is an e-process for every law under
which the observations are drawn sequentially from the laws of one piece: under such a law it is
below a test supermartingale. This contains the i.i.d. laws of the coins with parameters in the
union of the `C j`. -/
theorem isEProcess_minLikelihoodRatio_prodBernoulli [Countable κ] (hC : ∀ j, Convex ℝ (C j))
    (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ)
    (hη01 : ∀ j, η j ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j)) :
    IsEProcess (minLikelihoodRatio (prodBernoulli ψ) fun j ↦ prodBernoulli (η j))
      Filtration.piLT
      (⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT) := by
  refine isEProcess_iff_forall_singleton.2 ⟨adapted_minLikelihoodRatio _ _, fun P hP ↦ ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hP
  have hE := ((isTestSupermartingale_prod_prodBernoulli_div_prodBernoulli (hC j) (hC01 j) ψ
    (hη01 j) (hη j) (hmin j)).isEProcess fun P hP ↦
      have := isProbabilityMeasure_of_mem_sequentialNull hP; inferInstance).anti_set
    (singleton_subset_iff.2 hj)
  exact hE.mono (adapted_minLikelihoodRatio _ _) fun n ω ↦ minLikelihoodRatio_le _ _ j n ω

/-- The i.i.d. laws of the coins with parameters in a union of pieces are drawn sequentially from
the laws of one piece. -/
private lemma iidNull_prodBernoulli_iUnion_subset :
    iidNull (prodBernoulli '' ⋃ j, C j) ⊆
      ⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT := by
  intro μ hμ
  obtain ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩ := mem_iidNull.1 hμ
  obtain ⟨j, hj⟩ := mem_iUnion.1 hθ
  exact mem_iUnion.2 ⟨j, iidNull_subset_sequentialNull (by rintro _ ⟨θ, -, rfl⟩; infer_instance)
    (infinitePi_mem_iidNull (mem_image_of_mem _ hj))⟩

/-- **The sequential intersection–union test has level `α`** [EVR26, Note 32, Statement 2].
Under the hypotheses of `isEProcess_minLikelihoodRatio_prodBernoulli`, the test that rejects the
first time the minimum of the likelihood ratios reaches `α⁻¹` has level `α` for every law under
which the observations are drawn sequentially from the laws of one piece. -/
theorem isLevelStoppingTime_hittingAfter_minLikelihoodRatio_prodBernoulli [Countable κ]
    (hC : ∀ j, Convex ℝ (C j)) (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ)
    (hη01 : ∀ j, η j ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j))
    (α : ℝ≥0∞) :
    IsLevelStoppingTime
      (hittingAfter (minLikelihoodRatio (prodBernoulli ψ) fun j ↦ prodBernoulli (η j))
        (Ici α⁻¹) 0) Filtration.piLT
      (⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT)
      α :=
  (isEProcess_minLikelihoodRatio_prodBernoulli hC hC01 ψ hη01 hη
    hmin).isLevelStoppingTime_hittingAfter α

/-- The smallest relative entropy from `prodBernoulli ψ` to a union of pieces, each with a
minimizer `η j`, is the smallest of the relative entropies to the minimizers. -/
private lemma klInf_prodBernoulli_iUnion (ψ : ι → ℝ) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j)) :
    klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j) =
      ((⨅ j, klDiv (prodBernoulli ψ) (prodBernoulli (η j)) : ℝ≥0∞) : EReal) := by
  rw [klInf_eq_coe_iInf_klDiv (by rintro _ ⟨θ, -, rfl⟩; simp)]
  congr 1
  refine le_antisymm (le_iInf fun j ↦ iInf₂_le _ ⟨η j, mem_iUnion.2 ⟨j, hη j⟩, rfl⟩) ?_
  refine le_iInf₂ fun P hP ↦ ?_
  obtain ⟨θ, hθ, rfl⟩ := hP
  obtain ⟨j, hj⟩ := mem_iUnion.1 hθ
  exact (iInf_le _ j).trans (hmin j hj)

/-- **The minimum of the likelihood ratios grows at the rate `KL_inf`**
[EVR26, Note 32, Statement 2]. Let `η j ∈ C j`, in the open cube, minimize
`θ ↦ KL(prodBernoulli ψ ‖ prodBernoulli θ)` over sets of parameters `C j`, for `j` in a finite
type. Almost surely under the i.i.d. law of `prodBernoulli ψ`, `(1/n) log` of the minimum of the
likelihood ratios against the `prodBernoulli (η j)` tends to the smallest relative entropy
`KL_inf` from `prodBernoulli ψ` to the laws of the coins with parameters in the union of the
`C j`. No convexity is used here. -/
theorem ae_tendsto_log_minLikelihoodRatio_prodBernoulli_div [Finite κ] (ψ : ι → ℝ)
    (hη01 : ∀ j, η j ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun n : ℕ ↦ ENNReal.log (minLikelihoodRatio (prodBernoulli ψ)
          (fun j ↦ prodBernoulli (η j)) n ω) / (n : EReal)) atTop
        (𝓝 (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j))) := by
  rw [klInf_prodBernoulli_iUnion ψ hη hmin]
  exact ae_tendsto_log_minLikelihoodRatio_div _ fun j ↦
    prodBernoulli_absolutelyContinuous ψ (hη01 j)

/-- **The bipolar rate of a union of convex pieces is `KL_inf`** [EVR26, Note 32, Statement 2].
Under the hypotheses of `isEProcess_minLikelihoodRatio_prodBernoulli`, with finitely many pieces,
the bipolar rate of `prodBernoulli ψ` against the laws of the coins with parameters in the union
of the `C j` is the smallest relative entropy `KL_inf` to them. The bipolar rate is at most
`KL_inf` (`ProbabilityTheory.bipolarRate_le_klInf`); conversely, the expected logarithm of the
e-process `minLikelihoodRatio` at time `n`, divided by `n`, is at most the bipolar rate
(`ProbabilityTheory.IsEProcess.eintegral_log_div_le_bipolarRate`) and tends to `KL_inf`. -/
theorem bipolarRate_prodBernoulli_iUnion_eq_klInf [Finite κ] (hC : ∀ j, Convex ℝ (C j))
    (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ)
    (hη01 : ∀ j, η j ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j)) :
    bipolarRate (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j) =
      klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j) := by
  have hS : ∀ P ∈ prodBernoulli '' ⋃ j, C j, IsProbabilityMeasure P := by
    rintro _ ⟨θ, -, rfl⟩; infer_instance
  refine le_antisymm (bipolarRate_le_klInf _ hS) ?_
  have hE := (isEProcess_minLikelihoodRatio_prodBernoulli hC hC01 ψ hη01 hη hmin).anti_set
    iidNull_prodBernoulli_iUnion_subset
  have hlim := tendsto_eintegral_log_minLikelihoodRatio_div (prodBernoulli ψ)
    (P := fun j ↦ prodBernoulli (η j)) fun j ↦ prodBernoulli_absolutelyContinuous ψ (hη01 j)
  rw [← klInf_prodBernoulli_iUnion ψ hη hmin] at hlim
  exact le_of_tendsto hlim ((eventually_ne_atTop 0).mono fun n hn ↦
    hE.eintegral_log_div_le_bipolarRate _ hS hn)

/-- **The sequential intersection–union test attains the lower bound on expected stopping times**
[EVR26, Note 32, Statement 2]. Under the hypotheses of
`isEProcess_minLikelihoodRatio_prodBernoulli`, with finitely many pieces, the expected number of
observations of the test that rejects the first time the minimum of the likelihood ratios reaches
`α⁻¹`, under the i.i.d. law of `prodBernoulli ψ`, divided by `log (1/α)`, tends to `1 / KL_inf`
as `α → 0`, in `ℝ≥0∞`. If `KL_inf = 0`, the limit is `⊤`. The lower bound holds for every
sequential test of level `α` (`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`),
with `bipolarRate_prodBernoulli_iUnion_eq_klInf`; the upper bound is
`limsup_lintegral_hittingAfter_minLikelihoodRatio_div_log_le`. -/
theorem tendsto_lintegral_hittingAfter_minLikelihoodRatio_prodBernoulli_div_log [Finite κ]
    (hC : ∀ j, Convex ℝ (C j)) (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1) (ψ : ι → ℝ)
    (hη01 : ∀ j, η j ∈ univ.pi fun _ ↦ Ioo 0 1) (hη : ∀ j, η j ∈ C j)
    (hmin : ∀ j, IsMinOn (fun θ ↦ klDiv (prodBernoulli ψ) (prodBernoulli θ)) (C j) (η j)) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter (minLikelihoodRatio (prodBernoulli ψ)
        fun j ↦ prodBernoulli (η j)) (Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ)) / (ENNReal.log α⁻¹).toENNReal)
      (𝓝[>] 0) (𝓝 (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j)).toENNReal⁻¹) := by
  -- the upper bound
  have hup := limsup_lintegral_hittingAfter_minLikelihoodRatio_div_log_le (prodBernoulli ψ)
    (P := fun j ↦ prodBernoulli (η j)) fun j ↦ prodBernoulli_absolutelyContinuous ψ (hη01 j)
  have hK : (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j)).toENNReal =
      ⨅ j, klDiv (prodBernoulli ψ) (prodBernoulli (η j)) := by
    rw [klInf_prodBernoulli_iUnion ψ hη hmin, EReal.toENNReal_coe]
  rw [← hK] at hup
  set K := (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j)).toENNReal
  -- the lower bound: at the bipolar rate, which is `KL_inf`
  have hlow (α : ℝ≥0∞) : (ENNReal.log α⁻¹).toENNReal / K ≤
      ∫⁻ ω, ENat.toENNReal (hittingAfter (minLikelihoodRatio (prodBernoulli ψ)
        fun j ↦ prodBernoulli (η j)) (Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ) := by
    have h := toENNReal_log_inv_div_bipolarRate_le_lintegral (prodBernoulli ψ)
      (S₁ := prodBernoulli '' ⋃ j, C j) (by rintro _ ⟨θ, -, rfl⟩; infer_instance)
      ((isLevelStoppingTime_hittingAfter_minLikelihoodRatio_prodBernoulli hC hC01 ψ hη01 hη
        hmin α).anti_set iidNull_prodBernoulli_iUnion_subset)
    rwa [bipolarRate_prodBernoulli_iUnion_eq_klInf hC hC01 ψ hη01 hη hmin] at h
  refine tendsto_of_le_liminf_of_limsup_le ?_ hup
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with α ⟨hα0, hα1⟩
  set l := (ENNReal.log α⁻¹).toENNReal
  have hl0 : l ≠ 0 := (EReal.toENNReal_pos_iff.2
    (ENNReal.zero_lt_log_iff.2 (ENNReal.one_lt_inv.2 hα1))).ne'
  have hltop : l ≠ ∞ := by
    simp only [l, ne_eq, EReal.toENNReal_eq_top_iff]
    simpa using hα0.ne'
  calc K⁻¹ = l / K / l := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hl0 hltop,
          one_mul]
    _ ≤ _ := by gcongr; exact hlow α

end Coins

end ProbabilityTheory
