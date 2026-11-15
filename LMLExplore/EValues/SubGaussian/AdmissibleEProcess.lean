/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Admissible
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProductMeasure
import LMLExplore.EValues.TestSupermartingale
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.MGFAnalytic
import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RNDerivProd
import Statlib.ForMathlib.Probability.Process.Filtration

/-!
# Admissibility of the sub-Gaussian exponential e-process for nonatomic i.i.d. laws

Observe a sequence `X 0, X 1, …` of real numbers, the coordinates of `ℕ → ℝ`, with the filtration
`MeasureTheory.Filtration.piLE`, so that time `n` has seen the `n + 1` observations
`X 0, …, X n`. The null is the set of the i.i.d. laws whose marginal `μ` is `1`-sub-Gaussian
(`∫ exp (t x) ∂μ ≤ exp (t ^ 2 / 2)` for every real `t`, Mathlib's `HasSubgaussianMGF id 1 μ`) and
has no atom (`MeasureTheory.NullSingletonClass μ`). The process
`E n = exp (∑ i ≤ n, X i - (n + 1) / 2)` is a test supermartingale for this null, hence an
e-process, and it is admissible: every e-process that is at least `E` at every time, almost surely
under every member of the null, is equal to `E` at every time, almost surely under every member of
the null. Ramdas, Ruf, Larsson and Koolen prove the admissibility of this process for the larger
null of conditionally `1`-sub-Gaussian increments [RRLK, Theorem 35], and conjecture it for the
nonatomic laws; this file proves that conjecture for the i.i.d. nonatomic laws.

## Main statements

* `ProbabilityTheory.isAdmissibleEProcess_ofReal_exp_sum_sub_iid`: the exponential process is an
  admissible e-process for the i.i.d. laws of a nonatomic `1`-sub-Gaussian marginal.

## Implementation notes

Call a law `ν` touching when it is a nonatomic `1`-sub-Gaussian law with
`∫ exp (x - 1 / 2) ∂ν = 1`. Under the i.i.d. law of a touching `ν`, the process is a test
martingale, so an e-process that dominates it is equal to it almost surely. It then suffices that
every event of time `n` charged by the i.i.d. law of a member of the null is charged by the i.i.d.
law of a touching law (`ProbabilityTheory.IsEProcess.isAdmissibleEProcess_of_exists_lintegral_eq`).
Such an event is a Borel set of the first `n + 1` coordinates, so it is enough that every finite
nonatomic measure `m` carried by a compact interval `[-b, b]` is absolutely continuous with respect
to a touching law.

That law is `ν₀ + c₀ (m - ∑ j, c j N_j)`. The base law `ν₀ = ∑ j, w j N_j` is the law of
`Y + Z`, where `Y` is `3 p` subtracted from a sum of three independent Bernoulli variables of
parameter `p = 1 / (1 + √e)` and `Z` is an independent centred Gaussian variable of variance
`6 p - 2`: a mixture of the four Gaussian laws `N_j = N (j - 3 p, 6 p - 2)` with binomial weights
`w j`. Its moment generating function is `exp (t ^ 2 / 2 - 3 g t)`, where
`g t = (1 - 2 p) t ^ 2 / 2 + p t - log (p e ^ t + 1 - p)` vanishes at `0` and at `1` and is
otherwise positive, with a quadratic margin, by the Kearns–Saul inequality: `ν₀` is a touching
law with strict slack away from `0` and `1`. The coefficients `c j` match the mass, the mean and
the moments `∫ exp x` and `∫ x exp x` of `m`, which is possible because the moment vectors of the
four components form a basis of `ℝ ^ 4`; so the perturbation vanishes to second order at `0` and
`1`, and for `c₀ > 0` small the slack of the base law absorbs it.

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3: Theorem 35 and the
  conjecture that follows it.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### The coordinates of an i.i.d. sequence -/

section IID

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- Under an i.i.d. law, the coordinate `n + 1` is independent of the first `n + 1`
coordinates. -/
private lemma indep_piLE_comap_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) (m𝓧.comap fun ω : ℕ → 𝓧 ↦ ω (n + 1))
      (Measure.infinitePi fun _ ↦ μ) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    fun _ ↦ measurable_id).indepFun_finset (Finset.Iic n) {n + 1} (by simp)
    fun i ↦ measurable_pi_apply i
  have h' : (fun ω : ℕ → 𝓧 ↦ Preorder.frestrictLe n ω)
      ⟂ᵢ[Measure.infinitePi fun _ ↦ μ] fun ω ↦ ω (n + 1) := by
    exact h.comp measurable_id (measurable_pi_apply ⟨n + 1, by simp⟩)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (IndepFun_iff_Indep _ _ _).mp h'

/-- For an event `s` determined by the first `n + 1` coordinates of an i.i.d. sequence,
`∫⁻ ω in s, f (ω (n + 1)) ∂μ^ℕ = μ^ℕ s * ∫⁻ f ∂μ`. -/
private lemma setLIntegral_comp_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ]
    {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (n : ℕ) {s : Set (ℕ → 𝓧)}
    (hs : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n] s) :
    ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) =
      (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
  have hs' : MeasurableSet s := Filtration.le _ n _ hs
  have h1 : Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n]
      (s.indicator (1 : (ℕ → 𝓧) → ℝ≥0∞)) :=
    Measurable.indicator (m := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) measurable_const hs
  calc ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ)
      = ∫⁻ ω, s.indicator 1 ω * f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) := by
        rw [← lintegral_indicator hs']
        congr 1 with ω
        by_cases h : ω ∈ s <;> simp [h]
    _ = (∫⁻ ω, s.indicator 1 ω ∂(Measure.infinitePi fun _ ↦ μ)) *
          ∫⁻ ω, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
          (Filtration.le _ n) (measurable_pi_apply (n + 1)).comap_le
          (indep_piLE_comap_eval_succ μ n) h1 (hf.comp (comap_measurable _))
    _ = (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
        rw [lintegral_indicator_one hs',
          (measurePreserving_eval_infinitePi (fun _ ↦ μ) (n + 1)).lintegral_comp hf]

end IID

/-! ### The exponential process is a test supermartingale -/

/-- The exponential process `exp (∑ i ≤ n, X i - (n + 1) / 2)`. -/
private noncomputable def expProcess (n : ℕ) (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range (n + 1), ω i - (n + 1) / 2))

/-- The factor `exp (x - 1 / 2)` of the exponential process. -/
private noncomputable def expFactor (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (x - 1 / 2))

/-- The factor of the exponential process is measurable. -/
private lemma measurable_expFactor : Measurable expFactor := by
  unfold expFactor
  fun_prop

/-- The exponential process is the product of its factors. -/
private lemma expProcess_eq_mul_prod (n : ℕ) (ω : ℕ → ℝ) :
    expProcess n ω = expFactor (ω 0) * ∏ k ∈ Finset.range n, expFactor (ω (k + 1)) := by
  have h : ∑ i ∈ Finset.range (n + 1), ω i - (n + 1) / 2 =
      ∑ i ∈ Finset.range (n + 1), (ω i - 1 / 2) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [expProcess, h, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le,
    Finset.prod_range_succ', mul_comm]
  rfl

/-- The factor of the exponential process at the coordinate `k` is measurable with respect to the
first `j + 1` coordinates for `k ≤ j`. -/
private lemma measurable_expFactor_apply {k j : ℕ} (hkj : k ≤ j) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) j] fun ω : ℕ → ℝ ↦ expFactor (ω k) :=
  measurable_expFactor.comp (Filtration.measurable_piLE_apply hkj)

/-- For i.i.d. sampling from probability laws `μ` with `∫⁻ exp (x - 1 / 2) ∂μ ≤ 1`, the
exponential process is a test supermartingale. -/
private lemma isTestSupermartingale_expProcess {N : Set (Measure ℝ)}
    (hN : ∀ μ ∈ N, IsProbabilityMeasure μ ∧ ∫⁻ x, expFactor x ∂μ ≤ 1) :
    IsTestSupermartingale expProcess (Filtration.piLE (X := fun _ : ℕ ↦ ℝ))
      ((fun μ ↦ Measure.infinitePi fun _ : ℕ ↦ μ) '' N) := by
  have h := isTestSupermartingale_mul_prod (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ ℝ))
    (S := (fun μ ↦ Measure.infinitePi fun _ : ℕ ↦ μ) '' N)
    (M₀ := fun ω ↦ expFactor (ω 0)) (F := fun k ω ↦ expFactor (ω (k + 1)))
    (measurable_expFactor_apply le_rfl) ?_ (fun k ↦ measurable_expFactor_apply le_rfl)
    fun k ↦ ⟨measurable_expFactor.comp (measurable_pi_apply _), ?_⟩
  · convert h using 1
    exact funext fun n ↦ funext (expProcess_eq_mul_prod n)
  · rintro _ ⟨μ, hμ, rfl⟩
    have := (hN μ hμ).1
    rw [(measurePreserving_eval_infinitePi (fun _ ↦ μ) 0).lintegral_comp measurable_expFactor]
    exact (hN μ hμ).2
  · rintro _ ⟨μ, hμ, rfl⟩ s hs
    have := (hN μ hμ).1
    rw [setLIntegral_comp_eval_succ μ measurable_expFactor k hs]
    exact mul_le_of_le_one_right' (hN μ hμ).2

/-- For i.i.d. sampling from a probability law `ν` with `∫⁻ exp (x - 1 / 2) ∂ν = 1`, the
exponential process has expectation `1` at every time. -/
private lemma lintegral_expProcess_of_touching {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∫⁻ x, expFactor x ∂ν = 1) (n : ℕ) :
    ∫⁻ ω, expProcess n ω ∂Measure.infinitePi (fun _ : ℕ ↦ ν) = 1 := by
  have h0 : ∫⁻ ω, expFactor (ω 0) ∂Measure.infinitePi (fun _ : ℕ ↦ ν) = 1 := by
    rw [(measurePreserving_eval_infinitePi (fun _ ↦ ν) 0).lintegral_comp measurable_expFactor, hν]
  have h := isTestMartingale_mul_prod (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ ℝ))
    (S := {Measure.infinitePi fun _ : ℕ ↦ ν})
    (M₀ := fun ω ↦ expFactor (ω 0)) (F := fun k ω ↦ expFactor (ω (k + 1)))
    (measurable_expFactor_apply le_rfl) (by rintro _ rfl; exact h0.le)
    (fun k ↦ measurable_expFactor_apply le_rfl)
    fun k ↦ ⟨measurable_expFactor.comp (measurable_pi_apply _), by
      rintro _ rfl s hs
      rw [setLIntegral_comp_eval_succ ν measurable_expFactor k hs, hν, mul_one]⟩
  have := h.lintegral_eq (Set.mem_singleton _) n 0
  simp only [Finset.range_zero, Finset.prod_empty, mul_one] at this
  rw [← h0, this]
  exact lintegral_congr fun ω ↦ expProcess_eq_mul_prod n ω

/-- `∫⁻ exp (x - 1 / 2) ∂μ = exp (-1 / 2) ∫⁻ exp x ∂μ`. -/
private lemma lintegral_expFactor_eq (μ : Measure ℝ) :
    ∫⁻ x, expFactor x ∂μ =
      ENNReal.ofReal (Real.exp (-(1 / 2))) * ∫⁻ x, ENNReal.ofReal (Real.exp (1 * x)) ∂μ := by
  have h_eq (x : ℝ) : expFactor x = ENNReal.ofReal (Real.exp (-(1 / 2))) *
      ENNReal.ofReal (Real.exp (1 * x)) := by
    rw [expFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  simp_rw [h_eq]
  exact lintegral_const_mul _ (by fun_prop)

/-- A `1`-sub-Gaussian law satisfies `∫⁻ exp (x - 1 / 2) ∂μ ≤ 1`. -/
private lemma lintegral_expFactor_le_one {μ : Measure ℝ} (hμ : HasSubgaussianMGF id 1 μ) :
    ∫⁻ x, expFactor x ∂μ ≤ 1 := by
  have h : ∫ x, Real.exp (1 * x) ∂μ ≤ Real.exp (1 / 2) := by
    simpa [mgf] using hμ.mgf_le 1
  rw [lintegral_expFactor_eq, ← ofReal_integral_eq_lintegral_ofReal
    (by simpa using hμ.integrable_exp_mul 1) (ae_of_all _ fun _ ↦ (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_le_one]
  calc Real.exp (-(1 / 2)) * ∫ x, Real.exp (1 * x) ∂μ
      ≤ Real.exp (-(1 / 2)) * Real.exp (1 / 2) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

/-- A measure whose Laplace transform is at most `exp (t ^ 2 / 2)`, as a lower integral, is
`1`-sub-Gaussian. -/
private lemma hasSubgaussianMGF_of_lintegral_le {μ : Measure ℝ}
    (h : ∀ t : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂μ ≤
      ENNReal.ofReal (Real.exp (t ^ 2 / 2))) :
    HasSubgaussianMGF id 1 μ := by
  have hint (t : ℝ) : Integrable (fun x ↦ Real.exp (t * id x)) μ :=
    ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).2
      ((h t).trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, fun t ↦ ?_⟩
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)
    (hint t).aestronglyMeasurable]
  simpa using ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (h t)

/-- The exponential process is an e-process for i.i.d. sampling from `1`-sub-Gaussian laws. -/
private lemma isEProcess_expProcess :
    IsEProcess expProcess (Filtration.piLE (X := fun _ : ℕ ↦ ℝ))
      ((fun μ ↦ Measure.infinitePi fun _ : ℕ ↦ μ) ''
        {μ : Measure ℝ | IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧
          HasSubgaussianMGF id 1 μ}) := by
  refine (isTestSupermartingale_expProcess (N := {μ : Measure ℝ | IsProbabilityMeasure μ ∧
    NullSingletonClass μ ∧ HasSubgaussianMGF id 1 μ}) fun μ hμ ↦
      ⟨hμ.1, lintegral_expFactor_le_one hμ.2.2⟩).isEProcess ?_
  rintro _ ⟨μ, hμ, rfl⟩
  have := hμ.1
  infer_instance

/-! ### A second-order lower bound -/

/-- **Second-order lower bound.** If `c ≤ f''` on a convex set `I` containing `a`, then
`f a + f' a * (x - a) + c / 2 * (x - a) ^ 2 ≤ f x` on `I`. -/
private lemma add_mul_add_mul_sq_le_of_le_deriv2 {f f' f'' : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    {a c : ℝ} (ha : a ∈ I) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : ∀ x ∈ I, c ≤ f'' x) {x : ℝ} (hx : x ∈ I) :
    f a + f' a * (x - a) + c / 2 * (x - a) ^ 2 ≤ f x := by
  set g := fun y ↦ f y - (f a + f' a * (y - a) + c / 2 * (y - a) ^ 2) with hg_def
  set g' := fun y ↦ f' y - (f' a + c * (y - a)) with hg'_def
  have h1 (y : ℝ) : HasDerivAt (fun y ↦ f a + f' a * (y - a) + c / 2 * (y - a) ^ 2)
      (f' a + c * (y - a)) y := by
    have h := (hasDerivAt_id y).sub_const a
    exact (((h.const_mul (f' a)).const_add (f a)).add ((h.pow 2).const_mul (c / 2))).congr_deriv
      (by simp only [id, Nat.cast_ofNat]; ring)
  have hg (y : ℝ) : HasDerivAt g (g' y) y := (hf y).sub (h1 y)
  have hg' (y : ℝ) : HasDerivAt g' (f'' y - c) y :=
    (hf' y).sub (((((hasDerivAt_id y).sub_const a).const_mul c).const_add (f' a)).congr_deriv
      (by simp))
  have hmono : MonotoneOn g' I :=
    monotoneOn_of_hasDerivWithinAt_nonneg hI
      (fun y _ ↦ (hg' y).continuousAt.continuousWithinAt) (fun y _ ↦ (hg' y).hasDerivWithinAt)
      fun y hy ↦ sub_nonneg.2 (hc y (interior_subset hy))
  have hga : g a = 0 := by simp [g]
  have hg'a : g' a = 0 := by simp [g']
  suffices 0 ≤ g x by simp only [g] at this; linarith
  rcases le_total a x with hax | hxa
  · have h : MonotoneOn g (I ∩ Set.Ici a) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (hI.inter (convex_Ici a))
        (fun y _ ↦ (hg y).continuousAt.continuousWithinAt) (fun y _ ↦ (hg y).hasDerivWithinAt)
        fun y hy ↦ by
          have hy' := interior_subset hy
          rw [← hg'a]
          exact hmono ha hy'.1 hy'.2
    rw [← hga]
    exact h ⟨ha, Set.mem_Ici.2 le_rfl⟩ ⟨hx, hax⟩ hax
  · have h : AntitoneOn g (I ∩ Set.Iic a) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (hI.inter (convex_Iic a))
        (fun y _ ↦ (hg y).continuousAt.continuousWithinAt) (fun y _ ↦ (hg y).hasDerivWithinAt)
        fun y hy ↦ by
          have hy' := interior_subset hy
          rw [← hg'a]
          exact hmono hy'.1 ha hy'.2
    rw [← hga]
    exact h ⟨hx, hxa⟩ ⟨ha, Set.mem_Iic.2 le_rfl⟩ hxa

/-! ### The Kearns–Saul gap -/

/-- The parameter `p = 1 / (1 + √e)` of the Bernoulli law in the base law. -/
private noncomputable def ksParam : ℝ := 1 / (1 + Real.exp (1 / 2))

/-- The mean `p e^t / (p e^t + 1 - p)` of the exponential tilt by `t` of the Bernoulli law of
parameter `p = ksParam`. -/
private noncomputable def ksSigmoid (t : ℝ) : ℝ :=
  ksParam * Real.exp t / (ksParam * Real.exp t + (1 - ksParam))

/-- The gap `(1 - 2 p) t ^ 2 / 2 + p t - log (p e^t + 1 - p)` between the sub-Gaussian bound with
variance proxy `1 - 2 p` and the cumulant generating function of the centred Bernoulli law of
parameter `p = ksParam`. -/
private noncomputable def ksGap (t : ℝ) : ℝ :=
  (1 - 2 * ksParam) * t ^ 2 / 2 + ksParam * t - Real.log (ksParam * Real.exp t + (1 - ksParam))

/-- The parameter `ksParam` is positive. -/
private lemma ksParam_pos : 0 < ksParam := by unfold ksParam; positivity

/-- `1 < √e`. -/
private lemma one_lt_exp_half : 1 < Real.exp (1 / 2) := by
  linarith [Real.add_one_le_exp (1 / 2)]

/-- `√e ^ 2 = e`. -/
private lemma exp_half_sq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- The parameter `ksParam` is less than `1 / 2`. -/
private lemma ksParam_lt_half : ksParam < 1 / 2 := by
  unfold ksParam
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith [one_lt_exp_half]

/-- `√e < 1.65`. -/
private lemma exp_half_lt : Real.exp (1 / 2) < 1.65 := by
  have h := exp_half_sq
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos (1 / 2)
  nlinarith

/-- The parameter `ksParam` is more than `1 / 3`. -/
private lemma one_third_lt_ksParam : 1 / 3 < ksParam := by
  unfold ksParam
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  linarith [exp_half_lt]

/-- `1 - p = p √e` for `p = ksParam`. -/
private lemma one_sub_ksParam : 1 - ksParam = ksParam * Real.exp (1 / 2) := by
  unfold ksParam
  field_simp
  ring

/-- The denominator `p e^t + 1 - p` of `ksSigmoid` is positive. -/
private lemma ksDen_pos (t : ℝ) : 0 < ksParam * Real.exp t + (1 - ksParam) := by
  have : 0 < 1 - ksParam := by linarith [ksParam_lt_half]
  have := ksParam_pos
  positivity

/-- The curvature gap `1 - 2 p - p (1 - p)` at the touching point is positive. -/
private lemma ksCurv_pos : 0 < 1 - 2 * ksParam - ksParam * (1 - ksParam) := by
  have hr := exp_half_lt
  have hr1 := one_lt_exp_half
  have he := Real.exp_one_gt_d9
  have hsq := exp_half_sq
  have hp : ksParam * (1 + Real.exp (1 / 2)) = 1 := by unfold ksParam; field_simp
  have hp0 := ksParam_pos
  -- `(1 - 2 p - p (1 - p)) (1 + r) ^ 2 = r ^ 2 - r - 1` with `r = √e`
  have key : (1 - 2 * ksParam - ksParam * (1 - ksParam)) * (1 + Real.exp (1 / 2)) ^ 2 =
      Real.exp (1 / 2) ^ 2 - Real.exp (1 / 2) - 1 := by
    have : ksParam = 1 / (1 + Real.exp (1 / 2)) := rfl
    rw [this]
    field_simp
    ring
  have : 0 < Real.exp (1 / 2) ^ 2 - Real.exp (1 / 2) - 1 := by nlinarith
  rw [← key] at this
  exact pos_of_mul_pos_left this (by positivity)

/-- The derivative of `ksSigmoid` is `ksSigmoid (1 - ksSigmoid)`. -/
private lemma hasDerivAt_ksSigmoid (t : ℝ) :
    HasDerivAt ksSigmoid (ksSigmoid t * (1 - ksSigmoid t)) t := by
  have h1 := (Real.hasDerivAt_exp t).const_mul ksParam
  have h2 := h1.add_const (1 - ksParam)
  have := (ksDen_pos t).ne'
  exact (h1.div h2 this).congr_deriv (by unfold ksSigmoid; field_simp)

/-- The derivative of the Kearns–Saul gap. -/
private lemma hasDerivAt_ksGap (t : ℝ) :
    HasDerivAt ksGap ((1 - 2 * ksParam) * t + ksParam - ksSigmoid t) t := by
  have h1 : HasDerivAt (fun t ↦ ksParam * Real.exp t + (1 - ksParam)) (ksParam * Real.exp t) t :=
    ((Real.hasDerivAt_exp t).const_mul _).add_const _
  have h2 := h1.log (ksDen_pos t).ne'
  have h3 : HasDerivAt (fun t ↦ (1 - 2 * ksParam) * t ^ 2 / 2 + ksParam * t)
      ((1 - 2 * ksParam) * t + ksParam) t := by
    exact ((((hasDerivAt_pow 2 t).const_mul (1 - 2 * ksParam)).div_const 2).add
      ((hasDerivAt_id t).const_mul ksParam)).congr_deriv (by simp only [Nat.cast_ofNat]; ring)
  exact h3.sub h2

/-- The second derivative of the Kearns–Saul gap. -/
private lemma hasDerivAt_ksGap_deriv (t : ℝ) :
    HasDerivAt (fun t ↦ (1 - 2 * ksParam) * t + ksParam - ksSigmoid t)
      (1 - 2 * ksParam - ksSigmoid t * (1 - ksSigmoid t)) t := by
  exact ((((hasDerivAt_id t).const_mul (1 - 2 * ksParam)).add_const ksParam).sub
    (hasDerivAt_ksSigmoid t)).congr_deriv (by simp)

/-- `ksSigmoid` is continuous. -/
private lemma continuous_ksSigmoid : Continuous ksSigmoid :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_ksSigmoid t).continuousAt

/-- `ksSigmoid` is monotone. -/
private lemma ksSigmoid_mono {x y : ℝ} (hxy : x ≤ y) : ksSigmoid x ≤ ksSigmoid y := by
  unfold ksSigmoid
  rw [div_le_div_iff₀ (ksDen_pos x) (ksDen_pos y)]
  have h := Real.exp_le_exp.2 hxy
  have hp : 0 ≤ ksParam * (1 - ksParam) :=
    mul_nonneg ksParam_pos.le (by linarith [ksParam_lt_half])
  nlinarith [mul_le_mul_of_nonneg_left h hp]

/-- `ksSigmoid (1 / 2) = 1 / 2`. -/
private lemma ksSigmoid_half : ksSigmoid (1 / 2) = 1 / 2 := by
  have := (ksDen_pos (1 / 2)).ne'
  unfold ksSigmoid
  rw [div_eq_iff this, ← one_sub_ksParam]
  ring

/-- `p e + 1 - p = √e` for `p = ksParam`. -/
private lemma ksDen_one : ksParam * Real.exp 1 + (1 - ksParam) = Real.exp (1 / 2) := by
  have hp : ksParam * (1 + Real.exp (1 / 2)) = 1 := by unfold ksParam; field_simp
  rw [one_sub_ksParam, ← exp_half_sq]
  linear_combination Real.exp (1 / 2) * hp

/-- `ksSigmoid 1 = 1 - p` for `p = ksParam`. -/
private lemma ksSigmoid_one : ksSigmoid 1 = 1 - ksParam := by
  rw [ksSigmoid, ksDen_one, one_sub_ksParam, ← exp_half_sq]
  field_simp

/-- The Kearns–Saul gap vanishes at `0`. -/
private lemma ksGap_zero : ksGap 0 = 0 := by simp [ksGap]

/-- The Kearns–Saul gap vanishes at `1`. -/
private lemma ksGap_one : ksGap 1 = 0 := by
  rw [ksGap, ksDen_one, Real.log_exp]
  ring

/-- The Kearns–Saul gap is symmetric about `1 / 2`. -/
private lemma ksGap_one_sub (t : ℝ) : ksGap (1 - t) = ksGap t := by
  have hden : ksParam * Real.exp (1 - t) + (1 - ksParam) =
      Real.exp (1 / 2 - t) * (ksParam * Real.exp t + (1 - ksParam)) := by
    have h1 : Real.exp (1 - t) = Real.exp (1 / 2) * Real.exp (1 / 2 - t) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (1 / 2 - t) * Real.exp t = Real.exp (1 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, one_sub_ksParam]
    linear_combination (-ksParam) * h2
  rw [ksGap, ksGap, hden, Real.log_mul (Real.exp_pos _).ne' (ksDen_pos t).ne', Real.log_exp]
  ring

/-- **Kearns–Saul with a quadratic margin.** The gap is at least `κ min (t ^ 2, (t - 1) ^ 2)`
for some `κ > 0`. -/
private lemma exists_mul_min_le_ksGap :
    ∃ κ > 0, ∀ t, κ * min (t ^ 2) ((t - 1) ^ 2) ≤ ksGap t := by
  set G1 := fun t ↦ (1 - 2 * ksParam) * t + ksParam - ksSigmoid t with hG1
  set G2 := fun t ↦ 1 - 2 * ksParam - ksSigmoid t * (1 - ksSigmoid t) with hG2
  set κ₀ := 1 - 2 * ksParam - ksParam * (1 - ksParam) with hκ₀
  have hκ₀pos : 0 < κ₀ := ksCurv_pos
  have hG2one : G2 1 = κ₀ := by simp only [G2, ksSigmoid_one, κ₀]; ring
  -- `G2` is monotone on `[1/2, ∞)`
  have hG2mono : MonotoneOn G2 (Set.Ici (1 / 2)) := by
    intro x hx y hy hxy
    have hSx : 1 / 2 ≤ ksSigmoid x := ksSigmoid_half ▸ ksSigmoid_mono hx
    have hSxy := ksSigmoid_mono hxy
    simp only [G2]
    nlinarith [mul_nonneg (sub_nonneg.2 hSxy)
      (by linarith : (0 : ℝ) ≤ ksSigmoid x + ksSigmoid y - 1)]
  -- `G2 ≥ κ₀ / 2` on `[1 - δ, ∞)`
  have hG2cont : Continuous G2 := by
    exact continuous_const.sub
      (continuous_ksSigmoid.mul (continuous_const.sub continuous_ksSigmoid))
  have hhalf : κ₀ / 2 < G2 1 := by rw [hG2one]; exact half_lt_self hκ₀pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    ((hG2cont.tendsto 1).eventually (lt_mem_nhds hhalf))
  set δ := min (ε / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hG2ge : ∀ x ∈ Set.Ici (1 - δ), κ₀ / 2 ≤ G2 x := by
    intro x hx
    have hx' : 1 - δ ≤ x := hx
    rcases le_total x 1 with hx1 | hx1
    · refine (hball ?_).le
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    · have : G2 1 ≤ G2 x :=
        hG2mono (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2 (by linarith)) hx1
      linarith
  -- quadratic growth on `[1 - δ, ∞)`
  have hnear : ∀ x, 1 - δ ≤ x → κ₀ / 4 * (x - 1) ^ 2 ≤ ksGap x := by
    intro x hx
    have := add_mul_add_mul_sq_le_of_le_deriv2 (convex_Ici (1 - δ)) (a := 1)
      (Set.mem_Ici.2 (by linarith)) hasDerivAt_ksGap hasDerivAt_ksGap_deriv hG2ge
      (Set.mem_Ici.2 hx)
    have hG1one : (1 - 2 * ksParam) * 1 + ksParam - ksSigmoid 1 = 0 := by
      rw [ksSigmoid_one]; ring
    rw [ksGap_one, hG1one] at this
    linarith
  -- the gap decreases on `[1 / 2, 1]`
  have hG1conv : ConvexOn ℝ (Set.Ici (1 / 2)) G1 := by
    refine MonotoneOn.convexOn_of_deriv (convex_Ici _)
      (fun x _ ↦ (hasDerivAt_ksGap_deriv x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hasDerivAt_ksGap_deriv x).differentiableAt.differentiableWithinAt) ?_
    have : deriv G1 = G2 := funext fun x ↦ (hasDerivAt_ksGap_deriv x).deriv
    rw [this]
    exact hG2mono.mono interior_subset
  have hG1nonpos : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, G1 x ≤ 0 := by
    intro x hx
    have h := hG1conv.le_on_segment (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      (by rw [segment_eq_Icc (by norm_num)]; exact hx)
    have h1 : G1 (1 / 2) = 0 := by simp only [G1, ksSigmoid_half]; ring
    have h2 : G1 1 = 0 := by simp only [G1, ksSigmoid_one]; ring
    rw [h1, h2, max_self] at h
    exact h
  have hanti : AntitoneOn ksGap (Set.Icc (1 / 2) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun x _ ↦ (hasDerivAt_ksGap x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hasDerivAt_ksGap x).hasDerivWithinAt)
      fun x hx ↦ hG1nonpos x (interior_subset hx)
  set κ := κ₀ / 4 * δ ^ 2 with hκ
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hright : ∀ x, 1 / 2 ≤ x → κ * (x - 1) ^ 2 ≤ ksGap x := by
    intro x hx
    rcases le_total (1 - δ) x with h | h
    · have h1 := hnear x h
      have h2 : κ * (x - 1) ^ 2 ≤ κ₀ / 4 * (x - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      linarith
    · have h1 : ksGap (1 - δ) ≤ ksGap x :=
        hanti ⟨hx, by linarith⟩ ⟨by linarith, by linarith⟩ h
      have h2 := hnear (1 - δ) le_rfl
      have h3 : (x - 1) ^ 2 ≤ 1 := by nlinarith
      have h4 : (1 - δ - 1) ^ 2 = δ ^ 2 := by ring
      rw [h4] at h2
      have h5 : κ * (x - 1) ^ 2 ≤ κ := mul_le_of_le_one_right (by positivity) h3
      linarith
  refine ⟨κ, by positivity, fun t ↦ ?_⟩
  rcases le_total (1 / 2) t with ht | ht
  · calc κ * min (t ^ 2) ((t - 1) ^ 2) ≤ κ * (t - 1) ^ 2 := by
          gcongr
          exact min_le_right _ _
      _ ≤ ksGap t := hright t ht
  · have := hright (1 - t) (by linarith)
    rw [ksGap_one_sub] at this
    calc κ * min (t ^ 2) ((t - 1) ^ 2) ≤ κ * t ^ 2 := by
          gcongr
          exact min_le_left _ _
      _ = κ * (1 - t - 1) ^ 2 := by ring
      _ ≤ ksGap t := this

/-! ### The base law: a Gaussian mixture with strict slack -/

/-- The variance `6 p - 2` of the Gaussian components of the base law. -/
private noncomputable def baseVar : ℝ := 6 * ksParam - 2

/-- The means `j - 3 p` of the Gaussian components of the base law. -/
private noncomputable def baseMean (j : Fin 4) : ℝ := (j : ℕ) - 3 * ksParam

/-- The binomial weights of the Gaussian components of the base law. -/
private noncomputable def baseWeight (j : Fin 4) : ℝ :=
  (Nat.choose 3 j : ℝ) * ksParam ^ (j : ℕ) * (1 - ksParam) ^ (3 - (j : ℕ))

/-- The variance of the Gaussian components of the base law is positive. -/
private lemma baseVar_pos : 0 < baseVar := by
  unfold baseVar
  linarith [one_third_lt_ksParam]

/-- The weights of the base law sum to `1`. -/
private lemma sum_baseWeight : ∑ j, baseWeight j = 1 := by
  simp only [baseWeight, Fin.sum_univ_four, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, tsub_zero, one_mul, Nat.one_mod,
    Nat.choose_one_right, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one, Nat.reduceMod,
    Nat.choose_succ_self_right, Nat.reduceAdd, Nat.reduceSub, Nat.mod_succ, Nat.choose_self,
    tsub_self]
  ring

/-- Each weight of the base law is at least `p ^ 3`. -/
private lemma pow_three_le_baseWeight (j : Fin 4) : ksParam ^ 3 ≤ baseWeight j := by
  have hp := ksParam_pos
  have hq : ksParam ≤ 1 - ksParam := by linarith [ksParam_lt_half]
  have hq3 : ksParam ^ 3 ≤ (1 - ksParam) ^ 3 := pow_le_pow_left₀ hp.le hq 3
  have hq2 : ksParam ^ 2 ≤ (1 - ksParam) ^ 2 := pow_le_pow_left₀ hp.le hq 2
  fin_cases j <;>
  simp only [baseWeight, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, tsub_zero,
    one_mul, Nat.choose_one_right, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one,
    Nat.choose_succ_self_right, Nat.reduceAdd, Nat.reduceSub, Nat.choose_self, tsub_self] <;>
  nlinarith [mul_le_mul_of_nonneg_left hq2 hp.le, mul_le_mul_of_nonneg_left hq (sq_nonneg ksParam)]

/-- The moment generating function of the base law is `exp (t ^ 2 / 2 - 3 ksGap t)`. -/
private lemma sum_baseWeight_mul_exp (t : ℝ) :
    ∑ j, baseWeight j * Real.exp (baseMean j * t + baseVar * t ^ 2 / 2) =
      Real.exp (t ^ 2 / 2 - 3 * ksGap t) := by
  have h (j : Fin 4) : Real.exp (baseMean j * t + baseVar * t ^ 2 / 2) =
      Real.exp (baseVar * t ^ 2 / 2 - 3 * ksParam * t) * Real.exp t ^ (j : ℕ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [baseMean]
    ring
  have hR : Real.exp (t ^ 2 / 2 - 3 * ksGap t) = Real.exp (baseVar * t ^ 2 / 2 - 3 * ksParam * t) *
      (ksParam * Real.exp t + (1 - ksParam)) ^ 3 := by
    have h3 : t ^ 2 / 2 - 3 * ksGap t = (baseVar * t ^ 2 / 2 - 3 * ksParam * t) +
        ((3 : ℕ) : ℝ) * Real.log (ksParam * Real.exp t + (1 - ksParam)) := by
      simp only [ksGap, baseVar, Nat.cast_ofNat]
      ring
    rw [h3, Real.exp_add, Real.exp_nat_mul, Real.exp_log (ksDen_pos t)]
  simp_rw [h]
  rw [hR, Fin.sum_univ_four]
  simp only [baseWeight, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, tsub_zero, one_mul, Nat.one_mod, Nat.choose_one_right,
    Nat.cast_ofNat, pow_one, Nat.add_one_sub_one, Nat.reduceMod, Nat.choose_succ_self_right,
    Nat.reduceAdd, Nat.reduceSub, Nat.mod_succ, Nat.choose_self, tsub_self]
  ring

/-- The base law has strict slack: `exp (-3 ksGap t) ≤ 1 - κ min (t ^ 2, (t - 1) ^ 2, 1)` for
some `κ > 0`. -/
private lemma exists_exp_neg_ksGap_le :
    ∃ κ > 0, ∀ t, Real.exp (-(3 * ksGap t)) ≤ 1 - κ * min (min (t ^ 2) ((t - 1) ^ 2)) 1 := by
  obtain ⟨κ₁, hκ₁, hG⟩ := exists_mul_min_le_ksGap
  refine ⟨3 * κ₁ / (1 + 3 * κ₁), by positivity, fun t ↦ ?_⟩
  set ρ := min (min (t ^ 2) ((t - 1) ^ 2)) 1
  have hρ0 : 0 ≤ ρ := le_min (le_min (sq_nonneg _) (sq_nonneg _)) zero_le_one
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρG : κ₁ * ρ ≤ ksGap t :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hκ₁.le).trans (hG t)
  set y := 3 * κ₁ * ρ
  have hy : 0 ≤ y := by positivity
  calc Real.exp (-(3 * ksGap t)) ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp y := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (y + 1) := one_div_le_one_div_of_le (by positivity) (Real.add_one_le_exp y)
    _ ≤ 1 - 3 * κ₁ / (1 + 3 * κ₁) * ρ := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 3 * κ₁ / (1 + 3 * κ₁) * ρ * (1 + 3 * κ₁) = 3 * κ₁ * ρ := by
        field_simp
      have h2 : 3 * κ₁ / (1 + 3 * κ₁) * ρ * y ≤ 3 * κ₁ / (1 + 3 * κ₁) * ρ * (3 * κ₁) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_of_le_one_right (by positivity) hρ1
      nlinarith

/-! ### A function vanishing to second order at `0` and `1` -/

/-- A function `D` with `D = D' = 0` at `0` and at `1`, a continuous second derivative, and
`exp (-t ^ 2 / 2) D t` bounded above, satisfies
`exp (-t ^ 2 / 2) D t ≤ L min (t ^ 2, (t - 1) ^ 2, 1)` for some `L > 0`. -/
private lemma exists_exp_mul_le_mul_min {D D1 D2 : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (D1 x) x)
    (hD1 : ∀ x, HasDerivAt D1 (D2 x) x) (hD2 : Continuous D2) (h0 : D 0 = 0) (h0' : D1 0 = 0)
    (h1 : D 1 = 0) (h1' : D1 1 = 0) {L₀ : ℝ} (hL₀ : ∀ t, Real.exp (-(t ^ 2 / 2)) * D t ≤ L₀) :
    ∃ L > 0, ∀ t, Real.exp (-(t ^ 2 / 2)) * D t ≤ L * min (min (t ^ 2) ((t - 1) ^ 2)) 1 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 3 / 2)).exists_bound_of_continuousOn
    hD2.continuousOn
  -- second-order upper bound of `D` near `a ∈ {0, 1}`
  have htaylor (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hDa : D a = 0) (hD1a : D1 a = 0) (t : ℝ)
      (ht : t ∈ Set.Icc (a - 1 / 2) (a + 1 / 2)) : D t ≤ C / 2 * (t - a) ^ 2 := by
    have hsub : Set.Icc (a - 1 / 2) (a + 1 / 2) ⊆ Set.Icc (-1 / 2) (3 / 2) :=
      Set.Icc_subset_Icc (by linarith [ha.1]) (by linarith [ha.2])
    have := add_mul_add_mul_sq_le_of_le_deriv2 (f := fun x ↦ -D x) (f' := fun x ↦ -D1 x)
      (f'' := fun x ↦ -D2 x) (convex_Icc _ _) (a := a) (c := -C)
      ⟨by linarith, by linarith⟩ (fun x ↦ (hD x).neg) (fun x ↦ (hD1 x).neg)
      (fun x hx ↦ neg_le_neg ((le_abs_self _).trans (hC x (hsub hx)))) ht
    simp only [hDa, hD1a, neg_zero, zero_mul, add_zero, zero_add] at this
    linarith
  have hmax (t : ℝ) : Real.exp (-(t ^ 2 / 2)) * D t ≤ max (D t) 0 := by
    rcases le_total 0 (D t) with h | h
    · exact (mul_le_of_le_one_left h (Real.exp_le_one_iff.2 (by nlinarith))).trans
        (le_max_left _ _)
    · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h).trans (le_max_right _ _)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨max (C / 2) (4 * max L₀ 0) + 1, by positivity, fun t ↦ ?_⟩
  set L := max (C / 2) (4 * max L₀ 0) + 1
  have hL1 : C / 2 ≤ L := by simp only [L]; linarith [le_max_left (C / 2) (4 * max L₀ 0)]
  have hL2 : 4 * max L₀ 0 ≤ L := by simp only [L]; linarith [le_max_right (C / 2) (4 * max L₀ 0)]
  by_cases ht0 : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
  · have hρ : min (min (t ^ 2) ((t - 1) ^ 2)) 1 = t ^ 2 := by
      obtain ⟨h1, h2⟩ := ht0
      rw [min_eq_left (show t ^ 2 ≤ (t - 1) ^ 2 by nlinarith),
        min_eq_left (show t ^ 2 ≤ 1 by nlinarith)]
    have h := htaylor 0 ⟨le_rfl, zero_le_one⟩ h0 h0' t
      ⟨by linarith [ht0.1], by linarith [ht0.2]⟩
    rw [hρ]
    refine (hmax t).trans (max_le (h.trans ?_) (by positivity))
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_right hL1 (sq_nonneg _)
  by_cases ht1 : t ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)
  · have hρ : min (min (t ^ 2) ((t - 1) ^ 2)) 1 = (t - 1) ^ 2 := by
      obtain ⟨h1, h2⟩ := ht1
      rw [min_eq_right (show (t - 1) ^ 2 ≤ t ^ 2 by nlinarith),
        min_eq_left (show (t - 1) ^ 2 ≤ 1 by nlinarith)]
    have h := htaylor 1 ⟨zero_le_one, le_rfl⟩ h1 h1' t
      ⟨by linarith [ht1.1], by linarith [ht1.2]⟩
    rw [hρ]
    refine (hmax t).trans (max_le (h.trans ?_) (by positivity))
    exact mul_le_mul_of_nonneg_right hL1 (sq_nonneg _)
  · have hρ : 1 / 4 ≤ min (min (t ^ 2) ((t - 1) ^ 2)) 1 := by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht0 ht1
      refine le_min (le_min ?_ ?_) (by norm_num)
      · rcases ht0 with h | h <;> rcases ht1 with h' | h' <;> nlinarith
      · rcases ht0 with h | h <;> rcases ht1 with h' | h' <;> nlinarith
    calc Real.exp (-(t ^ 2 / 2)) * D t ≤ max L₀ 0 := (hL₀ t).trans (le_max_left _ _)
      _ = 4 * max L₀ 0 * (1 / 4) := by ring
      _ ≤ L * min (min (t ^ 2) ((t - 1) ^ 2)) 1 :=
        mul_le_mul hL2 hρ (by norm_num) (by positivity)

/-! ### Moment matching -/

/-- **Moment matching, algebraic part.** For `E ∉ {0, 1}`, the vectors `(1, j, E ^ j, j E ^ j)`,
`j = 0, …, 3`, form a basis of `ℝ ^ 4`: every vector is a combination of them. -/
private lemma exists_coeffs_four {E : ℝ} (hE : E ≠ 0) (hE1 : E ≠ 1) (U₁ U₂ U₃ U₄ : ℝ) :
    ∃ c : Fin 4 → ℝ, ∑ j, c j = U₁ ∧ ∑ j, c j * (j : ℕ) = U₂ ∧
      ∑ j, c j * E ^ (j : ℕ) = U₃ ∧ ∑ j, c j * (j : ℕ) * E ^ (j : ℕ) = U₄ := by
  have h1 : E - 1 ≠ 0 := sub_ne_zero.2 hE1
  refine ⟨![(E ^ 3 * U₁ - E ^ 3 * U₂ - 3 * E ^ 2 * U₁ + E ^ 2 * U₂ + 3 * E * U₃ - E * U₄ - U₃ + U₄)
      / (E - 1) ^ 3,
    (E ^ 4 * U₂ + E ^ 3 * U₂ + 6 * E ^ 2 * U₁ - 2 * E ^ 2 * U₂ - 6 * E ^ 2 * U₃ + 2 * E ^ 2 * U₄
      - E * U₄ - U₄) / (E * (E - 1) ^ 3),
    -(2 * E ^ 3 * U₂ + 3 * E ^ 2 * U₁ - E ^ 2 * U₂ - 3 * E ^ 2 * U₃ + E ^ 2 * U₄ + 3 * E * U₁
      - E * U₂ - 3 * E * U₃ + E * U₄ - 2 * U₄) / (E * (E - 1) ^ 3),
    (E ^ 2 * U₂ + 2 * E * U₁ - E * U₂ - 2 * E * U₃ + E * U₄ - U₄) / (E * (E - 1) ^ 3)],
    ?_, ?_, ?_, ?_⟩ <;>
  · simp only [neg_sub, Fin.sum_univ_four, Fin.isValue, Matrix.cons_val_zero,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, mul_zero, pow_zero, mul_one,
      Matrix.cons_val_one, Nat.one_mod, Nat.cast_one, pow_one, zero_add, Matrix.cons_val,
      Nat.reduceMod, Nat.cast_ofNat, Nat.mod_succ]
    field_simp
    ring

/-- **Moment matching.** Every vector `(T₁, T₂, T₃, T₄)` is a combination, with coefficients
`c j`, of the vectors `(1, m_j, ∫ exp, ∫ x exp)` of the mass, mean and exponential moments of the
Gaussian components `N (m_j, baseVar)` of the base law. -/
private lemma exists_base_coeffs (T₁ T₂ T₃ T₄ : ℝ) :
    ∃ c : Fin 4 → ℝ, ∑ j, c j = T₁ ∧ ∑ j, c j * baseMean j = T₂ ∧
      ∑ j, c j * Real.exp (baseMean j + baseVar / 2) = T₃ ∧
      ∑ j, c j * ((baseMean j + baseVar) * Real.exp (baseMean j + baseVar / 2)) = T₄ := by
  set Q := Real.exp (-3 * ksParam + baseVar / 2) with hQ_def
  have hQ : Q * Q⁻¹ = 1 := mul_inv_cancel₀ (Real.exp_pos _).ne'
  have hE : Real.exp 1 ≠ 1 := by linarith [Real.exp_one_gt_d9]
  obtain ⟨c, h1, h2, h3, h4⟩ := exists_coeffs_four (Real.exp_pos 1).ne' hE T₁
    (T₂ + 3 * ksParam * T₁) (T₃ * Q⁻¹) ((T₄ - (baseVar - 3 * ksParam) * T₃) * Q⁻¹)
  have hexp (j : Fin 4) : Real.exp (baseMean j + baseVar / 2) = Q * Real.exp 1 ^ (j : ℕ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [baseMean]
    ring
  have hmean (j : Fin 4) : baseMean j = (j : ℕ) - 3 * ksParam := rfl
  refine ⟨c, h1, ?_, ?_, ?_⟩
  · simp only [hmean]
    simp only [Fin.sum_univ_four] at h1 h2 ⊢
    linear_combination h2 - 3 * ksParam * h1
  · simp only [hexp]
    simp only [Fin.sum_univ_four] at h3 ⊢
    linear_combination Q * h3 + T₃ * hQ
  · simp only [hexp]
    simp only [hmean]
    simp only [Fin.sum_univ_four] at h3 h4 ⊢
    linear_combination Q * h4 + Q * (baseVar - 3 * ksParam) * h3 + T₄ * hQ

/-! ### Perturbing the base law by a piece of a nonatomic measure -/

/-- A measure carried by `[-b, b]` is almost surely in `[-b, b]`. -/
private lemma ae_mem_Icc_of_measure_compl {m : Measure ℝ} {b : ℝ} (hb : m (Set.Icc (-b) b)ᶜ = 0) :
    ∀ᵐ x ∂m, x ∈ Set.Icc (-b) b :=
  ae_iff.2 hb

section Perturbation

variable {m : Measure ℝ} [IsFiniteMeasure m] {b : ℝ}

/-- Under a finite measure carried by `[-b, b]`, `x ^ n exp (t x)` is integrable. -/
private lemma integrable_pow_mul_exp_of_measure_compl (hb : m (Set.Icc (-b) b)ᶜ = 0) (n : ℕ)
    (t : ℝ) : Integrable (fun x ↦ x ^ n * Real.exp (t * x)) m := by
  refine Integrable.of_bound (by fun_prop) (|b| ^ n * Real.exp (|t| * |b|)) ?_
  filter_upwards [ae_mem_Icc_of_measure_compl hb] with x hx
  have hxb : |x| ≤ |b| := (abs_le.2 hx).trans (le_abs_self b)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]
  refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hxb n) (Real.exp_le_exp.2 ?_)
    (Real.exp_pos _).le (by positivity)
  calc t * x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul _ _
    _ ≤ |t| * |b| := mul_le_mul_of_nonneg_left hxb (abs_nonneg _)

/-- Under a finite measure carried by `[-b, b]`, the derivative of `t ↦ ∫ x ^ n exp (t x)` is
`t ↦ ∫ x ^ (n + 1) exp (t x)`. -/
private lemma hasDerivAt_integral_pow_mul_exp_of_measure_compl (hb : m (Set.Icc (-b) b)ᶜ = 0)
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, x ^ n * Real.exp (t * x) ∂m)
      (∫ x, x ^ (n + 1) * Real.exp (t * x) ∂m) t := by
  have h : integrableExpSet (fun x ↦ x) m = Set.univ := Set.eq_univ_of_forall fun t ↦ by
    simpa [integrableExpSet] using integrable_pow_mul_exp_of_measure_compl hb 0 t
  exact hasDerivAt_integral_pow_mul_exp_real (X := fun x ↦ x) (by rw [h, interior_univ]; trivial) n

/-- Under a finite measure carried by `[-b, b]`,
`exp (-t ^ 2 / 2) ∫ exp (t x) ≤ exp (b ^ 2 / 2) m(ℝ)`. -/
private lemma exp_neg_mul_integral_exp_le (hb : m (Set.Icc (-b) b)ᶜ = 0) (t : ℝ) :
    Real.exp (-(t ^ 2 / 2)) * ∫ x, Real.exp (t * x) ∂m ≤
      Real.exp (b ^ 2 / 2) * m.real Set.univ := by
  rw [← integral_const_mul]
  calc ∫ x, Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x) ∂m ≤ ∫ _, Real.exp (b ^ 2 / 2) ∂m := by
        refine integral_mono_ae ?_ (integrable_const _) ?_
        · simpa using (integrable_pow_mul_exp_of_measure_compl hb 0 t).const_mul
            (Real.exp (-(t ^ 2 / 2)))
        · filter_upwards [ae_mem_Icc_of_measure_compl hb] with x hx
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          nlinarith [sq_nonneg (t - x), mul_nonneg (sub_nonneg.2 hx.2)
            (by linarith [hx.1] : (0 : ℝ) ≤ b + x)]
    _ = Real.exp (b ^ 2 / 2) * m.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]

/-- The Laplace transform of a finite measure carried by `[-b, b]`, as a Lebesgue integral. -/
private lemma lintegral_ofReal_exp_of_measure_compl (hb : m (Set.Icc (-b) b)ᶜ = 0) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂m = ENNReal.ofReal (∫ x, Real.exp (t * x) ∂m) :=
  (ofReal_integral_eq_lintegral_ofReal
    (by simpa using integrable_pow_mul_exp_of_measure_compl hb 0 t)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).symm

end Perturbation

/-- The moment generating function of a Gaussian law, as a Lebesgue integral. -/
private lemma lintegral_ofReal_exp_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂gaussianReal μ v =
      ENNReal.ofReal (Real.exp (μ * t + v * t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
  exact congrArg ENNReal.ofReal (congrFun mgf_fun_id_gaussianReal t)

/-- **Polar sets**: every finite nonatomic measure `m` carried by `[-b, b]` is absolutely
continuous with respect to a nonatomic `1`-sub-Gaussian law `ν` with `∫⁻ exp (x - 1 / 2) ∂ν = 1`.
The law is `ν₀ + c₀ (m - ∑ j, c j N_j)`, with `ν₀ = ∑ j, w_j N_j` the base law and `N_j` its
Gaussian components: the coefficients `c j` match the four moments `(mass, mean, ∫ exp, ∫ x exp)`
of `m`, so that the perturbation vanishes to second order at `0` and `1`, where the slack of the
base law does; elsewhere the slack is bounded below. -/
private lemma exists_touching_absolutelyContinuous {m : Measure ℝ} [IsFiniteMeasure m]
    [NullSingletonClass m] {b : ℝ} (hb : m (Set.Icc (-b) b)ᶜ = 0) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ NullSingletonClass ν ∧ HasSubgaussianMGF id 1 ν ∧
      ∫⁻ x, expFactor x ∂ν = 1 ∧ m ≪ ν := by
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_base_coeffs (m.real Set.univ) (∫ x, x ∂m)
    (∫ x, Real.exp x ∂m) (∫ x, x * Real.exp x ∂m)
  set F : ℕ → ℝ → ℝ := fun n t ↦ ∫ x, x ^ n * Real.exp (t * x) ∂m with hF
  set g : Fin 4 → ℝ → ℝ := fun j t ↦ Real.exp (baseMean j * t + baseVar * t ^ 2 / 2) with hg
  set D : ℝ → ℝ := fun t ↦ F 0 t - ∑ j, c j * g j t with hD_def
  have hF0 (t : ℝ) : F 0 t = ∫ x, Real.exp (t * x) ∂m := by simp [F]
  have hFd (n : ℕ) (t : ℝ) : HasDerivAt (F n) (F (n + 1) t) t :=
    hasDerivAt_integral_pow_mul_exp_of_measure_compl hb n t
  have hgd (j : Fin 4) (t : ℝ) : HasDerivAt (g j) ((baseMean j + baseVar * t) * g j t) t := by
    have := ((hasDerivAt_id t).const_mul (baseMean j)).add
      (((hasDerivAt_pow 2 t).const_mul baseVar).div_const 2)
    exact this.exp.congr_deriv (by simp only [g, id, Nat.cast_ofNat, Pi.add_apply]; ring)
  have hgd' (j : Fin 4) (t : ℝ) : HasDerivAt (fun t ↦ (baseMean j + baseVar * t) * g j t)
      (((baseMean j + baseVar * t) ^ 2 + baseVar) * g j t) t := by
    have := (((hasDerivAt_id t).const_mul baseVar).const_add (baseMean j)).mul (hgd j t)
    exact this.congr_deriv (by simp only [id]; ring)
  have hDd (t : ℝ) : HasDerivAt D (F 1 t - ∑ j, c j * ((baseMean j + baseVar * t) * g j t)) t :=
    (hFd 0 t).sub (HasDerivAt.fun_sum fun j _ ↦ (hgd j t).const_mul (c j))
  have hDd' (t : ℝ) : HasDerivAt (fun t ↦ F 1 t - ∑ j, c j * ((baseMean j + baseVar * t) * g j t))
      (F 2 t - ∑ j, c j * (((baseMean j + baseVar * t) ^ 2 + baseVar) * g j t)) t :=
    (hFd 1 t).sub (HasDerivAt.fun_sum fun j _ ↦ (hgd' j t).const_mul (c j))
  have hcont : Continuous fun t ↦
      F 2 t - ∑ j, c j * (((baseMean j + baseVar * t) ^ 2 + baseVar) * g j t) := by
    refine (continuous_iff_continuousAt.2 fun t ↦ (hFd 2 t).continuousAt).sub ?_
    refine continuous_finsetSum _ fun j _ ↦ continuous_const.mul ?_
    exact (by fun_prop : Continuous fun t : ℝ ↦ (baseMean j + baseVar * t) ^ 2 + baseVar).mul
      (continuous_iff_continuousAt.2 fun t ↦ (hgd j t).continuousAt)
  -- the four moment conditions
  have h0 : D 0 = 0 := by simp [D, F, g, hc1]
  have h0' : F 1 0 - ∑ j, c j * ((baseMean j + baseVar * 0) * g j 0) = 0 := by
    simp [F, g, hc2]
  have h1 : D 1 = 0 := by simp [D, F, g, hc3]
  have h1' : F 1 1 - ∑ j, c j * ((baseMean j + baseVar * 1) * g j 1) = 0 := by
    simp [F, g, hc4]
  -- a global upper bound for `exp (-t ^ 2 / 2) D t`
  have hk : 0 < 1 - baseVar := by unfold baseVar; linarith [ksParam_lt_half]
  have hL₀ (t : ℝ) : Real.exp (-(t ^ 2 / 2)) * D t ≤ Real.exp (b ^ 2 / 2) * m.real Set.univ +
      ∑ j, |c j| * Real.exp (baseMean j ^ 2 / (2 * (1 - baseVar))) := by
    have hj (j : Fin 4) : -(c j * (Real.exp (-(t ^ 2 / 2)) * g j t)) ≤
        |c j| * Real.exp (baseMean j ^ 2 / (2 * (1 - baseVar))) := by
      have h1 : Real.exp (-(t ^ 2 / 2)) * g j t ≤
          Real.exp (baseMean j ^ 2 / (2 * (1 - baseVar))) := by
        simp only [g]
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((1 - baseVar) * t - baseMean j)]
      have h2 : 0 ≤ Real.exp (-(t ^ 2 / 2)) * g j t := by positivity
      calc -(c j * (Real.exp (-(t ^ 2 / 2)) * g j t))
          ≤ |c j| * (Real.exp (-(t ^ 2 / 2)) * g j t) := by
            rw [← neg_mul]
            exact mul_le_mul_of_nonneg_right (neg_le_abs _) h2
        _ ≤ |c j| * Real.exp (baseMean j ^ 2 / (2 * (1 - baseVar))) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hj j
    have hm := exp_neg_mul_integral_exp_le hb t
    have heq : Real.exp (-(t ^ 2 / 2)) * D t = Real.exp (-(t ^ 2 / 2)) * F 0 t +
        ∑ j, -(c j * (Real.exp (-(t ^ 2 / 2)) * g j t)) := by
      have hs : ∑ j, -(c j * (Real.exp (-(t ^ 2 / 2)) * g j t)) =
          -(Real.exp (-(t ^ 2 / 2)) * ∑ j, c j * g j t) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ by ring)
      rw [hs]
      change Real.exp (-(t ^ 2 / 2)) * (F 0 t - ∑ j, c j * g j t) = _
      ring
    rw [heq, hF0]
    linarith
  obtain ⟨L, hL, hDL⟩ := exists_exp_mul_le_mul_min hDd hDd' hcont h0 h0' h1 h1' hL₀
  obtain ⟨κ, hκ, hslack⟩ := exists_exp_neg_ksGap_le
  -- the mixing weight
  set c₀ := min (κ / L) (ksParam ^ 3 / (1 + ∑ j, |c j|)) with hc₀
  have hS : 0 < 1 + ∑ j, |c j| := by positivity
  have hc₀pos : 0 < c₀ := lt_min (div_pos hκ hL) (div_pos (pow_pos ksParam_pos 3) hS)
  have hc₀L : c₀ * L ≤ κ := (le_div_iff₀ hL).1 (min_le_left _ _)
  have hw (j : Fin 4) : 0 ≤ baseWeight j - c₀ * c j := by
    have h1 : c₀ * c j ≤ c₀ * (1 + ∑ j, |c j|) := by
      refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) hc₀pos.le
      have := Finset.single_le_sum (fun k _ ↦ abs_nonneg (c k)) (Finset.mem_univ j)
      linarith
    have h2 : c₀ * (1 + ∑ j, |c j|) ≤ ksParam ^ 3 := (le_div_iff₀ hS).1 (min_le_right _ _)
    linarith [pow_three_le_baseWeight j]
  -- the real inequality
  have hreal (t : ℝ) : ∑ j, (baseWeight j - c₀ * c j) * g j t + c₀ * F 0 t =
      Real.exp (t ^ 2 / 2) * (Real.exp (-(3 * ksGap t)) +
        c₀ * (Real.exp (-(t ^ 2 / 2)) * D t)) := by
    have e1 : ∑ j, (baseWeight j - c₀ * c j) * g j t + c₀ * F 0 t =
        ∑ j, baseWeight j * g j t + c₀ * D t := by
      simp only [D, sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, mul_assoc]
      ring
    have e2 : Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [e1, sum_baseWeight_mul_exp, mul_add, ← Real.exp_add, sub_eq_add_neg]
    congr 1
    calc c₀ * D t = c₀ * D t * (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2))) := by
          rw [e2, mul_one]
      _ = Real.exp (t ^ 2 / 2) * (c₀ * (Real.exp (-(t ^ 2 / 2)) * D t)) := by ring
  have hle (t : ℝ) :
      ∑ j, (baseWeight j - c₀ * c j) * g j t + c₀ * F 0 t ≤ Real.exp (t ^ 2 / 2) := by
    rw [hreal]
    have hρ : 0 ≤ min (min (t ^ 2) ((t - 1) ^ 2)) 1 :=
      le_min (le_min (sq_nonneg _) (sq_nonneg _)) zero_le_one
    have key : Real.exp (-(3 * ksGap t)) + c₀ * (Real.exp (-(t ^ 2 / 2)) * D t) ≤ 1 := by
      nlinarith [hslack t, mul_le_mul_of_nonneg_left (hDL t) hc₀pos.le,
        mul_le_mul_of_nonneg_right hc₀L hρ]
    calc Real.exp (t ^ 2 / 2) * (Real.exp (-(3 * ksGap t)) + c₀ * (Real.exp (-(t ^ 2 / 2)) * D t))
        ≤ Real.exp (t ^ 2 / 2) * 1 := mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 / 2) := mul_one _
  -- the law
  have hv : baseVar.toNNReal ≠ 0 := by simpa using baseVar_pos
  have hvar : ((baseVar.toNNReal : ℝ≥0) : ℝ) = baseVar := Real.coe_toNNReal _ baseVar_pos.le
  set ν : Measure ℝ := ∑ j, ENNReal.ofReal (baseWeight j - c₀ * c j) •
      gaussianReal (baseMean j) baseVar.toNNReal + ENNReal.ofReal c₀ • m with hν
  have hmgf (t : ℝ) : ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂ν =
      ENNReal.ofReal (∑ j, (baseWeight j - c₀ * c j) * g j t + c₀ * F 0 t) := by
    rw [hν, lintegral_add_measure, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_ofReal_exp_of_measure_compl hb, ← hF0,
      ENNReal.ofReal_add (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (Real.exp_pos _).le)
        (mul_nonneg hc₀pos.le (by rw [hF0]; exact integral_nonneg fun _ ↦ (Real.exp_pos _).le)),
      ENNReal.ofReal_sum_of_nonneg fun j _ ↦ mul_nonneg (hw j) (Real.exp_pos _).le,
      ENNReal.ofReal_mul hc₀pos.le, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [lintegral_smul_measure, lintegral_ofReal_exp_gaussianReal, hvar, smul_eq_mul,
      ENNReal.ofReal_mul (hw j)]
  refine ⟨ν, ⟨?_⟩, ⟨fun x ↦ ?_⟩, hasSubgaussianMGF_of_lintegral_le fun t ↦ ?_, ?_,
    fun s hs ↦ ?_⟩
  · have h := hmgf 0
    rw [hreal 0, ksGap_zero, h0] at h
    simpa using h
  · have hg (j : Fin 4) : gaussianReal (baseMean j) baseVar.toNNReal {x} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := baseMean j) hv
      exact measure_singleton x
    simp [ν, hg]
  · rw [hmgf]
    exact ENNReal.ofReal_le_ofReal (hle t)
  · have he : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [lintegral_expFactor_eq, hmgf, hreal 1, ksGap_one, h1,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    norm_num [he]
  · have h : (ENNReal.ofReal c₀ • m) s ≤ ν s := by
      rw [hν, add_apply]
      exact le_add_self
    rw [hs, nonpos_iff_eq_zero, smul_apply, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left (ENNReal.ofReal_pos.2 hc₀pos).ne'

/-! ### Polar sets and admissibility -/

/-- A Borel set of `ℝ^ι` charged by the product of a nonatomic probability law is charged by the
product of a nonatomic `1`-sub-Gaussian law `ν` with `∫⁻ exp (x - 1 / 2) ∂ν = 1`. -/
private lemma exists_touching_pi_ne_zero {ι : Type*} [Fintype ι] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {A : Set (ι → ℝ)}
    (h : Measure.pi (fun _ ↦ μ) A ≠ 0) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ NullSingletonClass ν ∧ HasSubgaussianMGF id 1 ν ∧
      ∫⁻ x, expFactor x ∂ν = 1 ∧ Measure.pi (fun _ ↦ ν) A ≠ 0 := by
  -- some box `[-b, b]^ι` meets `A` in a set of positive measure
  obtain ⟨b, hb⟩ : ∃ b : ℕ,
      Measure.pi (fun _ ↦ μ) (A ∩ Set.univ.pi fun _ ↦ Set.Icc (-(b : ℝ)) b) ≠ 0 := by
    by_contra! h0
    refine h (measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null h0))
    obtain ⟨b, hb⟩ := exists_nat_ge (∑ i, |x i|)
    refine Set.mem_iUnion.2 ⟨b, hx, fun i _ ↦ abs_le.1 ?_⟩
    exact (Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (Finset.mem_univ i)).trans hb
  set m := μ.restrict (Set.Icc (-(b : ℝ)) b)
  have hmb : m (Set.Icc (-(b : ℝ)) b)ᶜ = 0 := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    simp
  obtain ⟨ν, hν, hνa, hνs, hν1, hmν⟩ := exists_touching_absolutelyContinuous hmb
  refine ⟨ν, hν, hνa, hνs, hν1, fun h0 ↦ hb ?_⟩
  have h1 : Measure.pi (fun _ : ι ↦ m) A = 0 :=
    Measure.AbsolutelyContinuous.pi' (fun _ ↦ hmν) h0
  rwa [← Measure.restrict_pi_pi,
    Measure.restrict_apply' (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)] at h1

/-- An event determined by the first `n + 1` coordinates that is charged by the i.i.d. law of a
nonatomic probability law is charged by the i.i.d. law of a nonatomic `1`-sub-Gaussian law `ν`
with `∫⁻ exp (x - 1 / 2) ∂ν = 1`. -/
private lemma exists_touching_infinitePi_ne_zero {n : ℕ} {A : Set (ℕ → ℝ)}
    (hA : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n] A) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (h : Measure.infinitePi (fun _ : ℕ ↦ μ) A ≠ 0) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ NullSingletonClass ν ∧ HasSubgaussianMGF id 1 ν ∧
      ∫⁻ x, expFactor x ∂ν = 1 ∧ Measure.infinitePi (fun _ : ℕ ↦ ν) A ≠ 0 := by
  rw [Filtration.piLE_eq_comap_frestrictLe, MeasurableSpace.measurableSet_comap] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  have h_eq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      Measure.infinitePi (fun _ : ℕ ↦ ρ) (Preorder.frestrictLe n ⁻¹' B) =
        Measure.pi (fun _ : Finset.Iic n ↦ ρ) B := by
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe n) hB]
    exact congrArg (· B) (Measure.infinitePi_map_restrict (fun _ ↦ ρ))
  rw [h_eq] at h
  obtain ⟨ν, hν, hνa, hνs, hν1, hνB⟩ := exists_touching_pi_ne_zero h
  exact ⟨ν, hν, hνa, hνs, hν1, by rwa [h_eq]⟩

/-- **Admissibility of the sub-Gaussian exponential e-process for nonatomic laws.** For the i.i.d.
laws on `ℕ → ℝ` whose marginal is `1`-sub-Gaussian and has no atom, with the filtration
`Filtration.piLE` of the first coordinates, the process `exp (∑ i ≤ n, X i - (n + 1) / 2)` is an
admissible e-process: every e-process that is at least it at every time, almost surely under every
member of the null, is equal to it at every time, almost surely under every member of the null.
[RRLK] proves this for the larger null of conditionally `1`-sub-Gaussian increments
[RRLK, Theorem 35] and conjectures it for the nonatomic laws. -/
theorem isAdmissibleEProcess_ofReal_exp_sum_sub_iid :
    IsAdmissibleEProcess
      (fun n ω ↦ ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range (n + 1), ω i - (n + 1) / 2)))
      (Filtration.piLE (X := fun _ : ℕ ↦ ℝ))
      ((fun μ ↦ Measure.infinitePi fun _ : ℕ ↦ μ) ''
        {μ : Measure ℝ | IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧
          HasSubgaussianMGF id 1 μ}) := by
  refine isEProcess_expProcess.isAdmissibleEProcess_of_exists_lintegral_eq ?_ ?_
  · rintro _ ⟨μ, hμ, rfl⟩
    have := hμ.1
    infer_instance
  · rintro n A hA ⟨_, ⟨μ, ⟨hμ, hμa, -⟩, rfl⟩, hμA⟩
    obtain ⟨ν, hν, hνa, hνs, hν1, hνA⟩ := exists_touching_infinitePi_ne_zero hA hμA
    exact ⟨_, ⟨ν, ⟨hν, hνa, hνs⟩, rfl⟩, hνA, by
      rw [lintegral_expProcess_of_touching hν1 n, measure_univ]⟩

end ProbabilityTheory
