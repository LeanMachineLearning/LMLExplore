/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.EProcess
public import LMLExplore.Probability.ProductMeasure.Blocks
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.Null.PrefixBet
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
* `ProbabilityTheory.isEVar_numeraire_sampleNull`: `X* n` is an e-variable for the `n`-sample
  null.
* `ProbabilityTheory.ae_eventually_log_le_log_numeraire_add`,
  `ProbabilityTheory.ae_eventually_log_le_log_numeraire_add_of_adapted`: the comparison of
  `n`-sample e-variables, and of e-variables of the i.i.d. null adapted to the filtration
  `Filtration.piLT` of the observations, with the numeraire.
* `ProbabilityTheory.exists_ae_eventually_mul_le_log_seqBlockProd_numeraire`: the products over
  blocks of length `m` of the numeraire of the `m`-sample null attain every rate below the bipolar
  rate almost surely [RR26, Theorem 3.5].
* `ProbabilityTheory.ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le`: a sequence
  that keeps up with every such sequence, up to a factor `exp (n ε)` for every `ε > 0`, has
  `liminf (1/n) log ≥ d` almost surely.

## Implementation notes

The logarithm of the numeraire is truncated above, as a real number, with `ENNReal.truncLog`, at
a level where its mean still exceeds a given real, by monotone convergence
(`MeasureTheory.exists_integrable_truncLog_lt_integral`). The statements and proofs are adapted from
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

/-- The sum of the truncated logarithms of nonzero factors over blocks is at most the logarithm of
their product. -/
private lemma sum_truncLog_le_log_seqBlockProd {m : ℕ} {V : (Fin m → 𝓧) → ℝ≥0∞} (c : ℝ) (k : ℕ)
    {ω : ℕ → 𝓧} (h : ∀ j, V (seqBlock m j ω) ≠ 0) :
    ((∑ j ∈ Finset.range k, ENNReal.truncLog c (V (seqBlock m j ω)) : ℝ) : EReal) ≤
      ENNReal.log (seqBlockProd m V k ω) := by
  rw [← ENNReal.log_ofReal_exp
    (∑ j ∈ Finset.range k, ENNReal.truncLog c (V (seqBlock m j ω))), seqBlockProd_def]
  refine ENNReal.log_le_log ?_
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
  exact Finset.prod_le_prod fun j _ ↦ ENNReal.ofReal_exp_truncLog_le (h j)

/-! ### Comparison with the numeraire -/

/-- The numeraire of the `n`-sample null under `Q₁ ^ n` is an e-variable for the `n`-sample null,
for a null `S₁` of measures of mass at most one. -/
theorem isEVar_numeraire_sampleNull (Q₁ : Measure 𝓧) (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (n : ℕ) :
    IsEVar (numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n)) (sampleNull S₁ n) :=
  isEVar_numeraire _ (measure_univ_le_one_of_mem_sampleNull hS₁ n)

/-- **Comparison of an `n`-sample e-variable with the numeraire.** For every sequence of
e-variables `M n` for the `n`-fold products of the members of `S₁` and every `ε > 0`, almost
surely under the i.i.d. law of `Q₁`, eventually `log (M n) ≤ log (X* n) + n ε` at the first `n`
observations, where `X* n` is Statlib's `numeraire` of the `n`-sample null under `Q₁ ^ n`. The
ratio `M n / X* n` has mean at most `1` under `Q₁ ^ n`, so this is Markov's inequality and the
Borel–Cantelli lemma [EVR26, Note 01]. The members of `S₁` need only have mass at most `1`. -/
theorem ae_eventually_log_le_log_numeraire_add (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) {M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hM : ∀ n, IsEVar (M n) (sampleNull S₁ n)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (M n (initSeg n ω)) ≤ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        (sampleNull S₁ n) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  set E : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞ := fun n ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
    (sampleNull S₁ n)
  -- Markov's inequality and the Borel–Cantelli lemma for the ratio to the numeraire
  filter_upwards [ae_eventually_lt_exp_of_lintegral_le Q₁ (F := fun n x ↦ M n x / E n x)
    (fun n ↦ ((hM n).measurable.div (measurable_numeraire _ _)).aemeasurable) ENNReal.one_ne_top
    (fun n ↦ lintegral_div_numeraire_le_one _
      (measure_univ_le_one_of_mem_sampleNull hS₁ n) (hM n))
    hε] with ω hω
  filter_upwards [hω] with n hn
  exact ENNReal.log_le_log_add_of_div_le hn.le

/-- **Comparison of a function of the first observations with the numeraire.** Let `F n` be
e-variables for the i.i.d. laws of the members of `S₁` such that `F n` is a function of the first
`n` observations: `F` is adapted to the filtration `Filtration.piLT` of the observations. For every
`ε > 0`, almost surely under the i.i.d. law of `Q₁`, eventually `log (F n) ≤ log (X* n) + n ε`,
where `X* n` is the numeraire of the `n`-sample null under `Q₁ ^ n`, at the first `n`
observations. -/
theorem ae_eventually_log_le_log_numeraire_add_of_adapted (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {F : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hF : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) F)
    (hFe : ∀ n, IsEVar (F n) (iidNull S₁)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (F n ω) ≤ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        (sampleNull S₁ n) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  choose G hG hFG using fun n ↦ exists_isEVar_eq_comp_initSeg hS₁ (hF n) (hFe n)
  filter_upwards [ae_eventually_log_le_log_numeraire_add Q₁
    (fun P hP ↦ (hS₁ P hP).measure_univ.le) hG hε] with ω hω
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
numbers along the blocks. -/
theorem exists_ae_eventually_mul_le_log_seqBlockProd_numeraire (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) {L : ℝ}
    (hL : (L : EReal) < bipolarRate Q₁ S₁) :
    ∃ m ≠ 0, ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ((n * L : ℝ) : EReal) ≤ ENNReal.log (seqBlockProd m
        (numeraire (Measure.pi fun _ : Fin m ↦ Q₁) (sampleNull S₁ m))
        (n / m) ω) := by
  rw [bipolarRate_def] at hL
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hL
  refine ⟨k + 1, k.succ_ne_zero, ?_⟩
  set m := k + 1
  have hm : m ≠ 0 := k.succ_ne_zero
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hfin : ∀ μ ∈ sampleNull S₁ m, μ Set.univ ≤ 1 :=
    measure_univ_le_one_of_mem_sampleNull hS₁ m
  set Em := numeraire (Measure.pi fun _ : Fin m ↦ Q₁)
    (sampleNull S₁ m)
  have hnum : IsNumeraire Em (sampleNull S₁ m)
      (Measure.pi fun _ : Fin m ↦ Q₁) := isNumeraire_numeraire _ hfin
  have hEm : Measurable Em := measurable_numeraire _ _
  -- the expected logarithm of the numeraire exceeds `m L`
  have hmL : ((m * L : ℝ) : EReal) <
      ∫ᵉ x, ENNReal.log (Em x) ∂Measure.pi fun _ : Fin m ↦ Q₁ := by
    rw [← maxEPower_eq_eintegral_numeraire hfin, ← maxLogGrowth_def]
    exact (EReal.coe_lt_div_natCast_iff (Nat.pos_of_ne_zero hm)).1 hk
  -- so does the expected logarithm truncated at a level `c`, which is integrable
  obtain ⟨c, hgi, hgint⟩ := exists_integrable_truncLog_lt_integral hEm
    (lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot (hnum.eintegral_log_ne_bot hfin)) hmL
  set g : (Fin m → 𝓧) → ℝ := fun x ↦ ENNReal.truncLog c (Em x)
  have hlt : L < (m : ℝ)⁻¹ • ∫ x, g x ∂Measure.pi fun _ : Fin m ↦ Q₁ := by
    rw [smul_eq_mul, ← div_eq_inv_mul, lt_div_iff₀ hm0]
    linarith
  -- the strong law along blocks, and the nonzero factors
  have h1 := strong_law_ae_seqBlock_nat_div Q₁ hgi
  have h2 : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ j, Em (seqBlock m j ω) ≠ 0 :=
    ae_all_iff.2 fun j ↦ (measurePreserving_seqBlock (fun _ ↦ Q₁) m j).quasiMeasurePreserving.ae
      (hnum.ae_ne_zero hfin)
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
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {T : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hT : ∀ F : ℕ → (ℕ → 𝓧) → ℝ≥0∞, Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) F →
      (∀ n, IsEVar (F n) (iidNull S₁)) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
        ENNReal.log (F n ω) ≤ ENNReal.log (T n ω) + ((n * ε : ℝ) : EReal))
    {L : ℝ} (hL : (L : EReal) < bipolarRate Q₁ S₁) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ((n * L : ℝ) : EReal) ≤ ENNReal.log (T n ω) := by
  obtain ⟨L', hLL', hL'⟩ := EReal.lt_iff_exists_real_btwn.1 hL
  obtain ⟨m, -, h1⟩ := exists_ae_eventually_mul_le_log_seqBlockProd_numeraire Q₁
    (fun P hP ↦ (hS₁ P hP).measure_univ.le) hL'
  set Em := numeraire (Measure.pi fun _ : Fin m ↦ Q₁)
    (sampleNull S₁ m)
  have hEm : Measurable Em := measurable_numeraire _ _
  -- `T` keeps up with the product of the numeraire over blocks
  have h2 := hT (fun n ↦ seqBlockProd m Em (n / m))
    (fun n ↦ Filtration.measurable_piLT_of_dependsOn (measurable_seqBlockProd hEm _)
      ((dependsOn_seqBlockProd Em _).mono (Set.Iio_subset_Iio (Nat.div_mul_le_self n m))))
    (fun n ↦ isEVar_seqBlockProd
      (isEVar_numeraire_sampleNull Q₁ (fun P hP ↦ (hS₁ P hP).measure_univ.le) m) _)
    (L' - L) (sub_pos.2 (EReal.coe_lt_coe_iff.1 hLL'))
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [hω1, hω2] with n hn1 hn2
  exact coe_le_of_coe_le_add (hn1.trans hn2) (le_of_eq (by ring))

/-- **A sequence that keeps up with every sequence of bets grows at least at the bipolar rate.**
Let `T n` be functions of the observations such that, for every sequence of e-variables `F n` for
the i.i.d. laws of the members of `S₁` that is adapted to the filtration `Filtration.piLT` of the
observations (`F n` is a function of the first `n` observations) and every `ε > 0`, almost surely
under the i.i.d. law of `Q₁`, eventually `log (F n) ≤ log (T n) + n ε`. Then almost surely
`liminf (1/n) log (T n) ≥ bipolarRate Q₁ S₁` [EVR26, Note 01].
The products over blocks of length `m` of the numeraire of the `m`-sample null attain every rate
below the bipolar rate [RR26, Theorem 3.5], almost surely by the strong law of large numbers along
the blocks. -/
theorem ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {T : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hT : ∀ F : ℕ → (ℕ → 𝓧) → ℝ≥0∞, Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) F →
      (∀ n, IsEVar (F n) (iidNull S₁)) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
        ENNReal.log (F n ω) ≤ ENNReal.log (T n ω) + ((n * ε : ℝ) : EReal)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      bipolarRate Q₁ S₁ ≤ liminf (fun n : ℕ ↦ ENNReal.log (T n ω) / (n : EReal)) atTop := by
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
  exact (EReal.coe_le_div_natCast_iff hn1).2 hn

/-! ### The numeraires grow at the bipolar rate -/

/-- **The numeraires grow at the bipolar rate, almost surely.** Almost surely under the i.i.d.
law of `Q₁`, the logarithm of the numeraire of the `n`-sample null under `Q₁ ^ n`, at the first
`n` observations, divided by `n`, tends to `bipolarRate Q₁ S₁`, also when the bipolar rate is
infinite [EVR26, Note 01]. The upper bound holds for every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`), and the lower bound follows from the
comparison with the numeraire and the products of the numeraires over blocks
[RR26, Theorem 3.5]. -/
theorem ae_tendsto_log_numeraire_div_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        (sampleNull S₁ n) (initSeg n ω)) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  filter_upwards [ae_limsup_log_div_le_bipolarRate Q₁ hS₁ fun n ↦
      isEVar_numeraire_sampleNull Q₁ (fun P hP ↦ (hS₁ P hP).measure_univ.le) n,
    ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le Q₁ hS₁
      (T := fun n ω ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
        (sampleNull S₁ n) (initSeg n ω))
      fun _ hF hFe _ hε ↦
        ae_eventually_log_le_log_numeraire_add_of_adapted Q₁ hS₁ hF hFe hε]
    with ω hsup hinf
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

end ProbabilityTheory
