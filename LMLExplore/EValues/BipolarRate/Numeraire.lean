/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.EProcess
public import LMLExplore.Probability.ProductMeasure.Blocks
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.MeasureTheory.Integral.EReal
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# The numeraires of an i.i.d. null grow at the bipolar rate, almost surely

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a law on `𝓧` (the
alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`. Write `X* n` for Statlib's `numeraire` of the `n`-sample null
`{P ^ n | P ∈ S₁}` under `Q₁ ^ n`, the log-optimal `n`-sample e-variable, and `d` for the bipolar
rate `bipolarRate Q₁ S₁`. Almost surely under the i.i.d. law of `Q₁`, `(1/n) log (X* n)`, at the
first `n` observations, tends to `d`, also when `d = ∞` [EVR26, Note 01]. Nothing is assumed on
`S₁` or `Q₁` besides that the members of `S₁` are probability measures: no domination, convexity
or compactness.

The upper bound `limsup (1/n) log (X* n) ≤ d` holds for every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`). The lower bound has two steps.

* **Comparison with the numeraire.** For every sequence of `n`-sample e-variables `M n` and every
  `ε > 0`, almost surely `log (M n) ≤ log (X* n) + n ε` for all large `n`: the ratio
  `M n / X* n` has mean at most `1` under `Q₁ ^ n`, so Markov's inequality bounds the probability
  that it exceeds `exp (n ε)` by `exp (- n ε)`, and the Borel–Cantelli lemma applies
  [EVR26, Note 01].
* **Products over blocks.** For `L < d` there is a block length `m` with
  `maxLogGrowth Q₁ S₁ m > m L`. The product of `X* m` over the successive blocks of `m`
  observations is a function of the first `n` observations with mean at most `1` under the null,
  and by the strong law of large numbers along the blocks it grows almost surely at a rate above
  `L`: the products over blocks of the numeraires attain every rate below `d`
  [RR26, Theorem 3.5]. The logarithm of `X* m` can have
  an infinite mean under `Q₁ ^ m`, so the strong law is applied to its truncation from above at a
  large level, whose mean still exceeds `m L`. Any sequence that keeps up with every sequence of
  functions of the first `n` observations with mean at most `1` under the null, as `X* n` does by
  the comparison step, therefore grows almost surely at least at the rate `d`.

## Main statements

* `ProbabilityTheory.ae_tendsto_log_numeraire_div_bipolarRate`: `(1/n) log (X* n)` tends to the
  bipolar rate almost surely.
* `ProbabilityTheory.ae_eventually_log_le_log_numeraire_add`,
  `ProbabilityTheory.ae_eventually_log_le_log_numeraire_add_of_dependsOn`: the comparison of
  `n`-sample e-variables, and of functions of the first `n` observations with mean at most `1`
  under the null, with the numeraire.
* `ProbabilityTheory.exists_ae_eventually_mul_le_log_seqBlockProd_numeraire`: the products over
  blocks of length `m` of the numeraire of the `m`-sample null attain every rate below the bipolar
  rate almost surely [RR26, Theorem 3.5].
* `ProbabilityTheory.ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le`: a sequence
  that keeps up with every such sequence, up to a factor `exp (n ε)` for every `ε > 0`, has
  `liminf (1/n) log ≥ d` almost surely.

## Implementation notes

The truncated logarithm `min (log x) c`, as a real number, is a private helper; the monotone
convergence of the extended integrals of the truncations `min f k` is
`MeasureTheory.eintegral_le_of_forall_min_le`. The statements and proofs are adapted from
`EValuesResearch/Results/Numeraire.lean` and `EValuesResearch/Results/NumeraireAux.lean` (commit
`dd4072f`) in the paper project `RemyDegenne/evalues_research`, which formalize [EVR26, Note 01],
rewritten on the API of LMLExplore.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### Auxiliary inequalities -/

/-- If `a ≤ x + c` and `b + c ≤ a` for reals `a, b, c`, then `b ≤ x`. -/
private lemma coe_le_of_coe_le_add {a b c : ℝ} {x : EReal} (h : (a : EReal) ≤ x + c)
    (hab : b + c ≤ a) : (b : EReal) ≤ x := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.bot_add, le_bot_iff] at h
    exact absurd h (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe x =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]
    linarith

/-! ### The truncated logarithm -/

/-- The logarithm truncated above at `c`, as a real number. -/
private noncomputable def truncLog (c : ℝ) (x : ℝ≥0∞) : ℝ := (min (ENNReal.log x) c).toReal

/-- The truncated logarithm is measurable. -/
private lemma measurable_truncLog (c : ℝ) : Measurable (truncLog c) :=
  measurable_ereal_toReal.comp (ENNReal.measurable_log.min measurable_const)

/-- The truncated logarithm of a positive finite number. -/
private lemma truncLog_of_ne {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) (htop : x ≠ ∞) :
    truncLog c x = min (Real.log x.toReal) c := by
  rw [truncLog, ENNReal.log_pos_real h0 htop, ← EReal.coe_strictMono.monotone.map_min,
    EReal.toReal_coe]

/-- The truncated logarithm of `∞` is the truncation level. -/
private lemma truncLog_top (c : ℝ) : truncLog c ∞ = c := by simp [truncLog]

/-- The exponential of the truncated logarithm of `x` is at most `x`. -/
private lemma ofReal_exp_truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) :
    ENNReal.ofReal (Real.exp (truncLog c x)) ≤ x := by
  by_cases htop : x = ∞
  · rw [htop]
    exact le_top
  · rw [truncLog_of_ne h0 htop]
    calc ENNReal.ofReal (Real.exp (min (Real.log x.toReal) c))
    _ ≤ ENNReal.ofReal (Real.exp (Real.log x.toReal)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _))
    _ = x := by
      rw [Real.exp_log (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop]

/-- The truncated logarithm of a nonzero `x`, as an extended real, is `min (log x) c`. -/
private lemma coe_truncLog {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) :
    (truncLog c x : EReal) = min (ENNReal.log x) c := by
  refine EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top c) (min_le_right _ _)) ?_
  simp [h0, EReal.coe_ne_bot]

/-- The truncated logarithm of `x` is at most `|c|` plus the negative part of `log x` in absolute
value. -/
private lemma abs_truncLog_le_abs_add (c : ℝ) (x : ℝ≥0∞) :
    |truncLog c x| ≤ |c| + (-ENNReal.log x).toENNReal.toReal := by
  have h0 : 0 ≤ (-ENNReal.log x).toENNReal.toReal := ENNReal.toReal_nonneg
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [truncLog, ENNReal.log_zero, bot_le, min_eq_left, EReal.toReal_bot, abs_zero]
    positivity
  rcases eq_or_ne x ∞ with rfl | hxtop
  · rw [truncLog_top]
    linarith [abs_nonneg c]
  rw [truncLog_of_ne hx0 hxtop, ENNReal.log_pos_real hx0 hxtop, ← EReal.coe_neg,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, ENNReal.toReal_ofReal']
  have h1 : -Real.log x.toReal ≤ max (-Real.log x.toReal) 0 := le_max_left _ _
  have h2 : 0 ≤ max (-Real.log x.toReal) 0 := le_max_right _ _
  rw [abs_le]
  constructor
  · rcases le_total (Real.log x.toReal) c with h | h
    · rw [min_eq_left h]
      linarith [abs_nonneg c]
    · rw [min_eq_right h]
      linarith [neg_abs_le c]
  · linarith [min_le_right (Real.log x.toReal) c, le_abs_self c]

/-- The truncated logarithm of a measurable function whose logarithm has a negative part of finite
mean is integrable under a finite measure. -/
private lemma integrable_truncLog_comp_of_lintegral_ne_top {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hneg : ∫⁻ x, (-ENNReal.log (f x)).toENNReal ∂μ ≠ ∞) (c : ℝ) :
    Integrable (fun x ↦ truncLog c (f x)) μ := by
  have hm : Measurable fun x ↦ (-ENNReal.log (f x)).toENNReal :=
    measurable_ereal_toENNReal.comp (ENNReal.measurable_log.comp hf).neg
  refine Integrable.mono' ((integrable_const |c|).add (integrable_toReal_of_lintegral_ne_top
    hm.aemeasurable hneg)) ((measurable_truncLog c).comp hf).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_truncLog_le_abs_add c (f x)

/-- **Truncation of an expected logarithm.** Let `f` be measurable and almost everywhere nonzero,
with a logarithm whose negative part has a finite mean under a finite measure. If the extended
mean of `log f` exceeds `a`, then for some level `c` the logarithm truncated at `c` is integrable
with mean above `a`: the truncations at the levels `0, 1, 2, …` increase to `log f`. -/
private lemma exists_integrable_truncLog_lt_integral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hf0 : ∀ᵐ x ∂μ, f x ≠ 0) (hneg : ∫⁻ x, (-ENNReal.log (f x)).toENNReal ∂μ ≠ ∞) {a : ℝ}
    (ha : (a : EReal) < ∫ᵉ x, ENNReal.log (f x) ∂μ) :
    ∃ c : ℝ, Integrable (fun x ↦ truncLog c (f x)) μ ∧ a < ∫ x, truncLog c (f x) ∂μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (a : EReal) < ∫ᵉ x, min (ENNReal.log (f x)) (c : EReal) ∂μ := by
    by_contra! h
    exact absurd (eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hf) h) (not_le.2 ha)
  have hi := integrable_truncLog_comp_of_lintegral_ne_top hf hneg c
  refine ⟨c, hi, ?_⟩
  have heq : ∫ᵉ x, min (ENNReal.log (f x)) (c : EReal) ∂μ =
      ∫ᵉ x, (truncLog c (f x) : EReal) ∂μ := by
    refine eintegral_congr_ae ?_
    filter_upwards [hf0] with x hx
    rw [coe_truncLog hx, EReal.coe_natCast]
  rw [heq, eintegral_eq_integral hi] at hc
  exact_mod_cast hc

/-- The sum of the truncated logarithms of nonzero factors over blocks is at most the logarithm of
their product. -/
private lemma sum_truncLog_le_log_seqBlockProd {m : ℕ} {V : (Fin m → 𝓧) → ℝ≥0∞} (c : ℝ) (k : ℕ)
    {ω : ℕ → 𝓧} (h : ∀ j, V (seqBlock m j ω) ≠ 0) :
    ((∑ j ∈ Finset.range k, truncLog c (V (seqBlock m j ω)) : ℝ) : EReal) ≤
      ENNReal.log (seqBlockProd m V k ω) := by
  rw [← ENNReal.log_ofReal_exp (∑ j ∈ Finset.range k, truncLog c (V (seqBlock m j ω))),
    seqBlockProd_def]
  refine ENNReal.log_le_log ?_
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
  exact Finset.prod_le_prod fun j _ ↦ ofReal_exp_truncLog_le (h j)

/-! ### Comparison with the numeraire -/

/-- **Comparison of an `n`-sample e-variable with the numeraire.** For every sequence of
e-variables `M n` for the `n`-fold products of the members of `S₁` and every `ε > 0`, almost
surely under the i.i.d. law of `Q₁`, eventually `log (M n) ≤ log (X* n) + n ε` at the first `n`
observations, where `X* n` is Statlib's `numeraire` of the `n`-sample null under `Q₁ ^ n`. The
ratio `M n / X* n` has mean at most `1` under `Q₁ ^ n`, so this is Markov's inequality and the
Borel–Cantelli lemma [EVR26, Note 01]. The members of `S₁` need only be finite measures. If `Q₁`
is not a probability measure, its i.i.d. law is `0` and the statement holds trivially. -/
theorem ae_eventually_log_le_log_numeraire_add (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) {M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hM : ∀ n, IsEVar (M n) ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (M n (initSeg n ω)) ≤ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  set E : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞ := fun n ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
    ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)
  -- Markov's inequality and the Borel–Cantelli lemma for the ratio to the numeraire
  filter_upwards [ae_eventually_lt_exp_of_lintegral_le Q₁ (F := fun n x ↦ M n x / E n x)
    (fun n ↦ ((hM n).measurable.div (measurable_numeraire _ _)).aemeasurable) ENNReal.one_ne_top
    (fun n ↦ lintegral_div_numeraire_le_one _ (isFiniteMeasure_of_mem_image_pi hS₁ n) (hM n))
    hε] with ω hω
  filter_upwards [hω] with n hn
  exact ENNReal.log_le_log_add_of_div_le hn.le

/-- **Comparison of a function of the first observations with the numeraire.** Let `F n` be
measurable functions of the first `n` observations with expectation at most `1` under the i.i.d.
laws of the members of `S₁`. For every `ε > 0`, almost surely under the i.i.d. law of `Q₁`,
eventually `log (F n) ≤ log (X* n) + n ε`, where `X* n` is the numeraire of the `n`-sample null
under `Q₁ ^ n`, at the first `n` observations. -/
theorem ae_eventually_log_le_log_numeraire_add_of_dependsOn (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {F : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) (hFn : ∀ n, DependsOn (F n) (Set.Iio n))
    (h_null : ∀ P ∈ S₁, ∀ n, ∫⁻ ω, F n ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (F n ω) ≤ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  have := nonempty_of_isProbabilityMeasure Q₁
  choose G hG hFG using fun n ↦
    exists_isEVar_eq_comp_initSeg hS₁ (hF n) (hFn n) fun P hP ↦ h_null P hP n
  filter_upwards [ae_eventually_log_le_log_numeraire_add Q₁
    (fun P hP ↦ have := hS₁ P hP; inferInstance) hG hε] with ω hω
  filter_upwards [hω] with n hn
  rw [hFG n]
  exact hn

/-! ### The almost sure lower bound -/

/-- **Products over blocks of the numeraires attain every rate below the bipolar rate.** For a
real `L` below `bipolarRate Q₁ S₁` there is a block length `m ≠ 0` such that, almost surely under
the i.i.d. law of `Q₁`, eventually `n L ≤ log` of the product of the numeraire `X* m` of the
`m`-sample null under `Q₁ ^ m` over the `n / m` complete blocks among the first `n` observations
[RR26, Theorem 3.5]. Pick `m` with `maxLogGrowth Q₁ S₁ m > m L`, truncate the logarithm of `X* m`
from above at a level where its mean still exceeds `m L`, and apply the strong law of large
numbers along the blocks. If `Q₁` is not a probability measure, its i.i.d. law is `0` and the
statement holds trivially. -/
theorem exists_ae_eventually_mul_le_log_seqBlockProd_numeraire (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) {L : ℝ} (hL : (L : EReal) < bipolarRate Q₁ S₁) :
    ∃ m ≠ 0, ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ((n * L : ℝ) : EReal) ≤ ENNReal.log (seqBlockProd m
        (numeraire (Measure.pi fun _ : Fin m ↦ Q₁) ((fun P ↦ Measure.pi fun _ : Fin m ↦ P) '' S₁))
        (n / m) ω) := by
  rw [bipolarRate_def] at hL
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hL
  refine ⟨k + 1, k.succ_ne_zero, ?_⟩
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  set m := k + 1
  have hm : m ≠ 0 := k.succ_ne_zero
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hfin := isFiniteMeasure_of_mem_image_pi hS₁ m
  set Em := numeraire (Measure.pi fun _ : Fin m ↦ Q₁)
    ((fun P ↦ Measure.pi fun _ : Fin m ↦ P) '' S₁)
  have hnum : IsNumeraire Em ((fun P ↦ Measure.pi fun _ : Fin m ↦ P) '' S₁)
      (Measure.pi fun _ : Fin m ↦ Q₁) := isNumeraire_numeraire _ hfin
  have hEm : Measurable Em := measurable_numeraire _ _
  -- the expected logarithm of the numeraire exceeds `m L`
  have hmL : ((m * L : ℝ) : EReal) <
      ∫ᵉ x, ENNReal.log (Em x) ∂Measure.pi fun _ : Fin m ↦ Q₁ := by
    rw [← maxUtility_eq_eintegral_numeraire _ hfin, ← maxLogGrowth_def]
    rw [EReal.lt_div_iff (by exact_mod_cast hm0) (EReal.natCast_ne_top _)] at hk
    rw [EReal.coe_mul, mul_comm, EReal.coe_natCast]
    exact hk
  -- so does the expected logarithm truncated at a level `c`, which is integrable
  obtain ⟨c, hgi, hgint⟩ := exists_integrable_truncLog_lt_integral hEm hnum.ae_ne_zero
    (lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot hnum.eintegral_log_ne_bot) hmL
  set g : (Fin m → 𝓧) → ℝ := fun x ↦ truncLog c (Em x)
  have hlt : L < (m : ℝ)⁻¹ • ∫ x, g x ∂Measure.pi fun _ : Fin m ↦ Q₁ := by
    rw [smul_eq_mul, ← div_eq_inv_mul, lt_div_iff₀ hm0]
    linarith
  -- the strong law along blocks, and the nonzero factors
  have h1 := strong_law_ae_seqBlock_nat_div Q₁ hgi
  have h2 : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ j, Em (seqBlock m j ω) ≠ 0 :=
    ae_all_iff.2 fun j ↦ (measurePreserving_seqBlock (fun _ ↦ Q₁) m j).quasiMeasurePreserving.ae
      hnum.ae_ne_zero
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [hω1.eventually (lt_mem_nhds hlt), eventually_ge_atTop 1] with n hn1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [smul_eq_mul, ← div_eq_inv_mul, lt_div_iff₀ hn0] at hn1
  refine le_trans ?_ (sum_truncLog_le_log_seqBlockProd c (n / m) hω2)
  exact EReal.coe_le_coe_iff.2 (by linarith)

/-- The almost sure lower bound for a fixed real `L` below the bipolar rate: almost surely,
eventually `n L ≤ log (T n)`. For a real `L'` between `L` and the bipolar rate, the products over
blocks of the numeraire grow at least at the rate `L'`
(`exists_ae_eventually_mul_le_log_seqBlockProd_numeraire`), and `T` keeps up with them up to a
factor `exp (n (L' - L))`. -/
private lemma ae_eventually_mul_le_log_of_forall_ae_eventually_log_le (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {T : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hT : ∀ F : ℕ → (ℕ → 𝓧) → ℝ≥0∞, (∀ n, Measurable (F n)) →
      (∀ n, DependsOn (F n) (Set.Iio n)) →
      (∀ P ∈ S₁, ∀ n, ∫⁻ ω, F n ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
        ENNReal.log (F n ω) ≤ ENNReal.log (T n ω) + ((n * ε : ℝ) : EReal))
    {L : ℝ} (hL : (L : EReal) < bipolarRate Q₁ S₁) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ((n * L : ℝ) : EReal) ≤ ENNReal.log (T n ω) := by
  obtain ⟨L', hLL', hL'⟩ := EReal.lt_iff_exists_real_btwn.1 hL
  obtain ⟨m, -, h1⟩ := exists_ae_eventually_mul_le_log_seqBlockProd_numeraire Q₁
    (fun P hP ↦ have := hS₁ P hP; inferInstance) hL'
  set Em := numeraire (Measure.pi fun _ : Fin m ↦ Q₁)
    ((fun P ↦ Measure.pi fun _ : Fin m ↦ P) '' S₁)
  have hEm : Measurable Em := measurable_numeraire _ _
  -- `T` keeps up with the product of the numeraire over blocks
  have h2 := hT (fun n ↦ seqBlockProd m Em (n / m)) (fun n ↦ measurable_seqBlockProd hEm _)
    (fun n ↦ (dependsOn_seqBlockProd Em _).mono (Set.Iio_subset_Iio (Nat.div_mul_le_self n m)))
    (fun P hP n ↦ by
      have := hS₁ P hP
      rw [lintegral_seqBlockProd_const P hEm]
      exact pow_le_one₀ (by positivity) ((isEVar_numeraire _ _).lintegral_le_one ⟨P, hP, rfl⟩))
    (L' - L) (sub_pos.2 (EReal.coe_lt_coe_iff.1 hLL'))
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [hω1, hω2] with n hn1 hn2
  exact coe_le_of_coe_le_add (hn1.trans hn2) (le_of_eq (by ring))

/-- **A sequence that keeps up with every sequence of bets grows at least at the bipolar rate.**
Let `T n` be functions of the observations such that, for every sequence of measurable functions
`F n` of the first `n` observations with expectation at most `1` under the i.i.d. laws of the
members of `S₁` and every `ε > 0`, almost surely under the i.i.d. law of `Q₁`, eventually
`log (F n) ≤ log (T n) + n ε`. Then almost surely `liminf (1/n) log (T n) ≥ bipolarRate Q₁ S₁`
[EVR26, Note 01].
The products over blocks of length `m` of the numeraire of the `m`-sample null attain every rate
below the bipolar rate [RR26, Theorem 3.5], almost surely by the strong law of large numbers along
the blocks. If `Q₁` is not a probability measure, its i.i.d. law is `0` and the statement holds
trivially. -/
theorem ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {T : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hT : ∀ F : ℕ → (ℕ → 𝓧) → ℝ≥0∞, (∀ n, Measurable (F n)) →
      (∀ n, DependsOn (F n) (Set.Iio n)) →
      (∀ P ∈ S₁, ∀ n, ∫⁻ ω, F n ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
        ENNReal.log (F n ω) ≤ ENNReal.log (T n ω) + ((n * ε : ℝ) : EReal)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      bipolarRate Q₁ S₁ ≤ liminf (fun n : ℕ ↦ ENNReal.log (T n ω) / (n : EReal)) atTop := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  -- the bound for every rational below the bipolar rate
  have h (q : ℚ) : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      ((q : ℝ) : EReal) < bipolarRate Q₁ S₁ → ∀ᶠ n : ℕ in atTop,
        ((n * q : ℝ) : EReal) ≤ ENNReal.log (T n ω) := by
    by_cases hq : ((q : ℝ) : EReal) < bipolarRate Q₁ S₁
    · filter_upwards [ae_eventually_mul_le_log_of_forall_ae_eventually_log_le Q₁ hS₁ hT hq]
        with ω hω _ using hω
    · exact ae_of_all _ fun ω h ↦ absurd h hq
  filter_upwards [ae_all_iff.2 h] with ω hω
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  obtain ⟨q, haq, hqd⟩ := EReal.lt_iff_exists_rat_btwn.1 ha
  refine haq.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [hω q hqd, eventually_ge_atTop 1] with n hn hn1
  rw [EReal.le_div_iff_mul_le (by exact_mod_cast hn1) (EReal.natCast_ne_top n), mul_comm,
    ← EReal.coe_natCast, ← EReal.coe_mul]
  exact hn

/-! ### The numeraires grow at the bipolar rate -/

/-- **The numeraires grow at the bipolar rate, almost surely.** Almost surely under the i.i.d.
law of `Q₁`, the logarithm of the numeraire of the `n`-sample null under `Q₁ ^ n`, at the first
`n` observations, divided by `n`, tends to `bipolarRate Q₁ S₁`, also when the bipolar rate is
infinite [EVR26, Note 01]. The upper bound holds for every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`), and the lower bound follows from the
comparison with the numeraire and the products of the numeraires over blocks
[RR26, Theorem 3.5]. If `Q₁` is not a probability measure, its i.i.d. law is `0` and the
statement holds trivially. -/
theorem ae_tendsto_log_numeraire_div_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  filter_upwards [ae_limsup_log_div_le_bipolarRate Q₁ hS₁ fun n ↦ isEVar_numeraire _ _,
    ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le Q₁ hS₁
      (T := fun n ω ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω))
      fun _ hF hFn h_null _ hε ↦
        ae_eventually_log_le_log_numeraire_add_of_dependsOn Q₁ hS₁ hF hFn h_null hε]
    with ω hsup hinf
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

end ProbabilityTheory
