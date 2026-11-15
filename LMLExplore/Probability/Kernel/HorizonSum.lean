/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.Analysis.Real.Sqrt
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import LMLExplore.Probability.Moments.Variance

/-!
# Finite-horizon sums along a sequence of kernels

For a sequence of kernels `κ : ℕ → Kernel α α`, a horizon `H` and rewards `f : ℕ → α → ℝ`, the
finite-horizon sum `horizonSum κ H f h x` is the expected sum `∑_{j = h}^{H - 1} f j (X j)` of the
rewards along the time-inhomogeneous Markov chain started at `X h = x` with transitions
`X (j + 1) ∼ κ j (X j)`. It is defined by backward induction from the horizon:
`horizonSum κ H f h x = f h x + ∫ horizonSum κ H f (h + 1) d(κ h x)` for `h < H`, and `0` from
the horizon on. In an episodic MDP, the value of a Markov policy is the finite-horizon sum of its
rewards along its state kernels.

For Markov kernels, the finite-horizon sum of bounded measurable rewards is bounded measurable
and affine in the rewards. Comparing the backward recursions of two sequences of kernels gives
the simulation bound: `|horizonSum κ' H f - horizonSum κ H f| ≤ horizonSum κ' H e` as soon as the
one-step prediction errors `|(κ' j - κ j) (horizonSum κ H f (j + 1))|` are at most `e j`.

The finite-horizon form of the total-variance argument controls the one-step variances
`Var[W (j + 1); κ j y]` of a sum `W = horizonSum κ H f` of nonnegative rewards bounded by `B`:
their finite-horizon sum is at most `2 B W - W ^ 2 ≤ B ^ 2`. Since the finite-horizon sum of square
roots satisfies `horizonSum κ H √g h ≤ √((H - h) horizonSum κ H g h)` (Jensen's inequality and
the Cauchy–Schwarz inequality along the horizon), the finite-horizon sum of the one-step standard
deviations of `W` is at most `√H B` [LWCGC24, Lemma 12].

Iterating this bound along the levels `V 0 = horizonSum κ H f` and
`V (l + 1) = horizonSum κ H √Var_κ(V l)` (`horizonSumLevel`), the level `l` is at most
`C H √H ^ l` for rewards in `[0, C]`. If a second sequence of kernels `κ'` deviates from `κ` on
the levels `l ≤ m` by a Bernstein-type bound `√(ε Var_κ(V l)) + ε C H √H ^ l`, with
`H ≤ 4 ^ m` and `9 ε H ≤ 1`, the simulation bound along the levels gives
`|horizonSum κ' H f - horizonSum κ H f| ≤ 4 C H √(ε H)` [LWCGC24, Lemma 9]. This is the
finite-horizon counterpart of
`ProbabilityTheory.Kernel.abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le`.

## Main definitions

* `ProbabilityTheory.Kernel.horizonSum κ H f`: the finite-horizon sum of the rewards `f` along the
  kernels `κ`, with the horizon `H`.
* `ProbabilityTheory.Kernel.horizonSumLevel κ H f`: the levels `V 0 = horizonSum κ H f` and
  `V (l + 1) = horizonSum κ H √Var_κ(V l)` of [LWCGC24, (62)].

## Main statements

* `ProbabilityTheory.Kernel.horizonSum_congr`, `ProbabilityTheory.Kernel.horizonSumLevel_congr`: the
  sums and the levels from the step `h₀` on only depend on the kernels and rewards from `h₀` on.
* `ProbabilityTheory.Kernel.horizonSum_mem_Icc`: for rewards in `[a, b]`, the sum from the step
  `h` lies in `[(H - h) a, (H - h) b]`.
* `ProbabilityTheory.Kernel.horizonSum_add`, `ProbabilityTheory.Kernel.horizonSum_const_mul`,
  `ProbabilityTheory.Kernel.horizonSum_const`: the finite-horizon sum is affine in the rewards.
* `ProbabilityTheory.Kernel.abs_horizonSum_sub_horizonSum_le`: the simulation bound.
* `ProbabilityTheory.Kernel.horizonSum_variance_le`: the total-variance bound
  `horizonSum κ H Var_κ(W) ≤ 2 B W - W ^ 2`.
* `ProbabilityTheory.Kernel.horizonSum_sqrt_le`:
  `horizonSum κ H √g h ≤ √((H - h) horizonSum κ H g h)`.
* `ProbabilityTheory.Kernel.horizonSum_sqrt_variance_le`: the finite-horizon sum of the one-step
  standard deviations of `W ≤ B` is at most `√(H - h) B`.
* `ProbabilityTheory.Kernel.horizonSumLevel_mem_Icc`: the level `l` lies in `[0, C H √H ^ l]`
  [LWCGC24, Lemma 12].
* `ProbabilityTheory.Kernel.abs_horizonSum_sub_horizonSum_le_of_abs_sub_le`: the comparison of
  the finite-horizon sums along two sequences of kernels with Bernstein-type deviations on the
  levels [LWCGC24, Lemma 9].

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], §7.2 and
  Appendix C (arXiv:2005.12900)
-/

public section

open MeasureTheory LMLExplore

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The finite-horizon sum of the rewards `f j` along the kernels `κ j`, with the horizon `H`:
`horizonSum κ H f h x` is the expected sum `∑_{j = h}^{H - 1} f j (X j)` along the Markov chain
started at `X h = x` with transitions `X (j + 1) ∼ κ j (X j)`. It is defined by backward
induction: `horizonSum κ H f h x = f h x + ∫ horizonSum κ H f (h + 1) d(κ h x)` for `h < H`, and
`horizonSum κ H f h = 0` for `h ≥ H`. See `horizonSum_of_lt` and `horizonSum_of_le`. -/
noncomputable def horizonSum (κ : ℕ → Kernel α α) (H : ℕ) (f : ℕ → α → ℝ) (h : ℕ) (x : α) :
    ℝ :=
  if h < H then f h x + ∫ y, horizonSum κ H f (h + 1) y ∂(κ h x) else 0
termination_by H - h

variable {κ κ' : ℕ → Kernel α α} {H : ℕ} {f g : ℕ → α → ℝ}

/-- Before the horizon, the finite-horizon sum is the reward of the step plus the integral of the
sum from the next step. -/
theorem horizonSum_of_lt {h : ℕ} (hh : h < H) (x : α) :
    horizonSum κ H f h x = f h x + ∫ y, horizonSum κ H f (h + 1) y ∂(κ h x) := by
  rw [horizonSum]
  simp [hh]

/-- From the horizon on, the finite-horizon sum is zero. -/
theorem horizonSum_of_le {h : ℕ} (hh : H ≤ h) (x : α) : horizonSum κ H f h x = 0 := by
  rw [horizonSum]
  simp [not_lt.2 hh]

@[simp]
lemma horizonSum_self (x : α) : horizonSum κ H f H x = 0 :=
  horizonSum_of_le le_rfl x

/-- The finite-horizon sums from the step `h₀` on only depend on the kernels and the rewards from
the step `h₀` on. -/
theorem horizonSum_congr {h₀ : ℕ} (hκ : ∀ j, h₀ ≤ j → κ j = κ' j) (hf : ∀ j, h₀ ≤ j → f j = g j)
    {h : ℕ} (hh : h₀ ≤ h) : horizonSum κ H f h = horizonSum κ' H g h := by
  funext x
  by_cases hH : h < H
  · rw [horizonSum_of_lt hH, horizonSum_of_lt hH, hκ h hh, hf h hh,
      horizonSum_congr hκ hf (hh.trans (Nat.le_succ h))]
  · rw [horizonSum_of_le (not_lt.1 hH), horizonSum_of_le (not_lt.1 hH)]
termination_by H - h

/-- The finite-horizon sum of measurable rewards is measurable. -/
theorem measurable_horizonSum (hf : ∀ j, Measurable (f j))
    (h : ℕ) : Measurable (horizonSum κ H f h) := by
  by_cases hh : h < H
  · rw [funext (horizonSum_of_lt hh)]
    exact (hf h).add ((measurable_horizonSum hf (h + 1)).stronglyMeasurable.integral_kernel
      (κ := κ h)).measurable
  · rw [funext (horizonSum_of_le (not_lt.1 hh))]
    exact measurable_const
termination_by H - h

/-! ### The levels of [LWCGC24, Lemma 9] -/

variable (κ H f) in
/-- The levels of [LWCGC24, (62)]: `V 0 = horizonSum κ H f` and
`V (l + 1) = horizonSum κ H √Var_κ(V l)`, the finite-horizon sum of the one-step standard
deviations `√Var[V l (j + 1); κ j y]` of the previous level. -/
noncomputable def horizonSumLevel : ℕ → ℕ → α → ℝ
  | 0 => horizonSum κ H f
  | l + 1 => horizonSum κ H fun j y ↦ √Var[horizonSumLevel l (j + 1); κ j y]

variable (κ H f) in
@[simp]
lemma horizonSumLevel_zero : horizonSumLevel κ H f 0 = horizonSum κ H f :=
  (rfl)

variable (κ H f) in
@[simp]
lemma horizonSumLevel_succ (l : ℕ) :
    horizonSumLevel κ H f (l + 1) =
      horizonSum κ H fun j y ↦ √Var[horizonSumLevel κ H f l (j + 1); κ j y] :=
  (rfl)

/-- The levels from the step `h₀` on only depend on the kernels and the rewards from the step `h₀`
on. -/
theorem horizonSumLevel_congr {h₀ : ℕ} (hκ : ∀ j, h₀ ≤ j → κ j = κ' j)
    (hf : ∀ j, h₀ ≤ j → f j = g j) (l : ℕ) {h : ℕ} (hh : h₀ ≤ h) :
    horizonSumLevel κ H f l h = horizonSumLevel κ' H g l h := by
  induction l generalizing h with
  | zero => exact horizonSum_congr hκ hf hh
  | succ l ih =>
    refine horizonSum_congr hκ (fun j hj ↦ funext fun y ↦ ?_) hh
    rw [ih (by omega : h₀ ≤ j + 1), hκ j hj]

/-- The levels of measurable rewards along s-finite kernels are measurable. -/
theorem measurable_horizonSumLevel [∀ j, IsSFiniteKernel (κ j)] (hf : ∀ j, Measurable (f j))
    (l h : ℕ) : Measurable (horizonSumLevel κ H f l h) := by
  induction l generalizing h with
  | zero => exact measurable_horizonSum hf h
  | succ l ih => exact measurable_horizonSum (fun j ↦ (ih (j + 1)).variance_kernel.sqrt) h

section Markov

variable [∀ j, IsMarkovKernel (κ j)] [∀ j, IsMarkovKernel (κ' j)]

/-- For rewards in `[a, b]`, the finite-horizon sum from the step `h` lies in
`[(H - h) a, (H - h) b]`. -/
theorem horizonSum_mem_Icc {a b : ℝ} (hf : ∀ j, Measurable (f j))
    (hfab : ∀ j x, f j x ∈ Set.Icc a b) (h : ℕ) (x : α) :
    horizonSum κ H f h x ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  by_cases hh : h < H
  · have hW (y : α) := horizonSum_mem_Icc hf hfab (h + 1) y
    have hPW := integral_mem_Icc_of_ae_mem_Icc (μ := κ h x)
      (measurable_horizonSum hf (h + 1)).aemeasurable (.of_forall hW)
    rw [horizonSum_of_lt hh, show H - h = H - (h + 1) + 1 by omega, Nat.cast_add_one]
    have := hfab h x
    constructor <;> nlinarith [this.1, this.2, hPW.1, hPW.2]
  · rw [horizonSum_of_le (not_lt.1 hh), Nat.sub_eq_zero_of_le (not_lt.1 hh)]
    simp
termination_by H - h

/-- For rewards bounded by `C` in absolute value, the finite-horizon sum from the step `h` is
bounded by `(H - h) C` in absolute value. -/
theorem abs_horizonSum_le {C : ℝ} (hf : ∀ j, Measurable (f j)) (hfC : ∀ j x, |f j x| ≤ C)
    (h : ℕ) (x : α) : |horizonSum κ H f h x| ≤ (H - h : ℕ) * C := by
  have hW := horizonSum_mem_Icc (κ := κ) (H := H) hf (fun j x ↦ abs_le.1 (hfC j x)) h x
  rw [mul_neg] at hW
  exact abs_le.2 hW

/-- For rewards bounded by `C` in absolute value, the finite-horizon sum is bounded by `H |C|` in
absolute value, uniformly over the steps. -/
theorem abs_horizonSum_le_mul_abs {C : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, |f j x| ≤ C) (h : ℕ) (x : α) : |horizonSum κ H f h x| ≤ H * |C| :=
  (abs_horizonSum_le hf hfC h x).trans (mul_le_mul (by exact_mod_cast Nat.sub_le H h)
    (le_abs_self C) (le_trans (abs_nonneg _) (hfC 0 x)) (Nat.cast_nonneg _))

/-- For bounded measurable rewards, the finite-horizon sum is integrable for every finite
measure. -/
theorem integrable_horizonSum {C : ℝ} (hf : ∀ j, Measurable (f j)) (hfC : ∀ j x, |f j x| ≤ C)
    (h : ℕ) (μ : Measure α) [IsFiniteMeasure μ] : Integrable (horizonSum κ H f h) μ :=
  integrable_of_abs_le (measurable_horizonSum hf h) (abs_horizonSum_le_mul_abs hf hfC h) μ

/-- The finite-horizon sum of bounded measurable rewards is additive in the rewards. -/
theorem horizonSum_add {C D : ℝ} (hf : ∀ j, Measurable (f j)) (hfC : ∀ j x, |f j x| ≤ C)
    (hg : ∀ j, Measurable (g j)) (hgD : ∀ j x, |g j x| ≤ D) (h : ℕ) (x : α) :
    horizonSum κ H (fun j y ↦ f j y + g j y) h x = horizonSum κ H f h x + horizonSum κ H g h x := by
  by_cases hh : h < H
  · rw [horizonSum_of_lt hh, horizonSum_of_lt hh, horizonSum_of_lt hh,
      funext (horizonSum_add hf hfC hg hgD (h + 1)),
      integral_add (integrable_horizonSum hf hfC _ _) (integrable_horizonSum hg hgD _ _)]
    ring
  · simp [horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

omit [∀ j, IsMarkovKernel (κ j)] in
/-- The finite-horizon sum is homogeneous in the rewards. -/
theorem horizonSum_const_mul (c : ℝ) (h : ℕ) (x : α) :
    horizonSum κ H (fun j y ↦ c * f j y) h x = c * horizonSum κ H f h x := by
  by_cases hh : h < H
  · rw [horizonSum_of_lt hh, horizonSum_of_lt hh, funext (horizonSum_const_mul c (h + 1)),
      integral_const_mul]
    ring
  · simp [horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

/-- The finite-horizon sum of a constant reward `c` from the step `h` is `(H - h) c`. -/
@[simp]
theorem horizonSum_const (c : ℝ) (h : ℕ) (x : α) :
    horizonSum κ H (fun _ _ ↦ c) h x = (H - h : ℕ) * c := by
  by_cases hh : h < H
  · rw [horizonSum_of_lt hh, funext (horizonSum_const c (h + 1)), integral_const, probReal_univ,
      one_smul, show H - h = H - (h + 1) + 1 by omega, Nat.cast_add_one]
    ring
  · rw [horizonSum_of_le (not_lt.1 hh), Nat.sub_eq_zero_of_le (not_lt.1 hh)]
    simp
termination_by H - h

/-- **The simulation bound**: if the one-step prediction errors of the finite-horizon sums along
`κ` satisfy `|(κ' j - κ j) (horizonSum κ H f (j + 1))| ≤ e j` at every step `j < H`, for bounded
measurable rewards `f` and `e`, then the finite-horizon sums along `κ'` and `κ` are within the
finite-horizon sum of `e` along `κ'`. -/
theorem abs_horizonSum_sub_horizonSum_le {e : ℕ → α → ℝ} {C D : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, |f j x| ≤ C) (he : ∀ j, Measurable (e j)) (heD : ∀ j x, |e j x| ≤ D)
    (hdev : ∀ j < H, ∀ y, |∫ z, horizonSum κ H f (j + 1) z ∂(κ' j y) -
      ∫ z, horizonSum κ H f (j + 1) z ∂(κ j y)| ≤ e j y) (h : ℕ) (x : α) :
    |horizonSum κ' H f h x - horizonSum κ H f h x| ≤ horizonSum κ' H e h x := by
  by_cases hh : h < H
  · -- `(κ' W' - κ W) = κ' (W' - W) + (κ' - κ) W` with `W' = horizonSum κ' H f (h + 1)` and
    -- `W = horizonSum κ H f (h + 1)`
    have hW' := integrable_horizonSum (κ := κ') (H := H) hf hfC (h + 1) (κ' h x)
    have hW := integrable_horizonSum (κ := κ) (H := H) hf hfC (h + 1) (κ' h x)
    rw [horizonSum_of_lt hh, horizonSum_of_lt hh, horizonSum_of_lt hh, add_sub_add_left_eq_sub,
      show ∀ a b c : ℝ, a - c = (a - b) + (b - c) by intros; ring,
      ← integral_sub hW' hW, add_comm (e h x)]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hdev h hh x))
    refine abs_integral_le_integral_abs.trans (integral_mono (hW'.sub hW).abs
      (integrable_horizonSum he heD (h + 1) _) fun y ↦ ?_)
    exact abs_horizonSum_sub_horizonSum_le hf hfC he heD hdev (h + 1) y
  · simp [horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

/-! ### The one-step variances of a finite-horizon sum -/

/-- **The total-variance bound** in finite horizon: for nonnegative bounded measurable rewards
`f` whose finite-horizon sum `W = horizonSum κ H f` is bounded by `B` at every step, the
finite-horizon sum of the one-step variances `Var[W (j + 1); κ j y]` is at most
`2 B W - W ^ 2`, hence at most `B ^ 2`. -/
theorem horizonSum_variance_le {B C : ℝ} (hf : ∀ j, Measurable (f j)) (hfC : ∀ j x, |f j x| ≤ C)
    (hf₀ : ∀ j x, 0 ≤ f j x) (hWB : ∀ j x, horizonSum κ H f j x ≤ B) (h : ℕ) (x : α) :
    horizonSum κ H (fun j y ↦ Var[horizonSum κ H f (j + 1); κ j y]) h x ≤
      2 * B * horizonSum κ H f h x - horizonSum κ H f h x ^ 2 := by
  by_cases hh : h < H
  · set W := horizonSum κ H f (h + 1) with hW_def
    have hWm : Measurable W := measurable_horizonSum hf (h + 1)
    have hWC := abs_horizonSum_le_mul_abs (κ := κ) (H := H) hf hfC
    have hVarm (j : ℕ) : Measurable fun y ↦ Var[horizonSum κ H f (j + 1); κ j y] :=
      (measurable_horizonSum hf (j + 1)).variance_kernel
    have hVarB (j : ℕ) (y : α) :
        |Var[horizonSum κ H f (j + 1); κ j y]| ≤ (H * |C|) ^ 2 := by
      rw [abs_of_nonneg (variance_nonneg _ _)]
      exact variance_le_sq_of_abs_le (measurable_horizonSum hf (j + 1)).aemeasurable
        (.of_forall (hWC (j + 1)))
    have hint := integrable_of_abs_le hWm (hWC (h + 1)) (κ h x)
    have hint₂ : Integrable (fun y ↦ W y ^ 2) (κ h x) :=
      integrable_of_abs_le (hWm.pow_const 2) (B := (H * |C|) ^ 2)
        (fun y ↦ by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hWC (h + 1) y) 2) _
    have hT := integrable_horizonSum (κ := κ) (H := H) hVarm hVarB (h + 1) (κ h x)
    -- the induction hypothesis at the next step, integrated against `κ h x`
    have hstep : ∫ y, horizonSum κ H (fun j y ↦ Var[horizonSum κ H f (j + 1); κ j y]) (h + 1) y
        ∂(κ h x) ≤ 2 * B * ∫ y, W y ∂(κ h x) - ∫ y, W y ^ 2 ∂(κ h x) := by
      rw [← integral_const_mul, ← integral_sub (hint.const_mul _) hint₂]
      exact integral_mono hT ((hint.const_mul _).sub hint₂)
        fun y ↦ horizonSum_variance_le hf hfC hf₀ hWB (h + 1) y
    have hWh := horizonSum_of_lt (κ := κ) (f := f) hh x
    have hWhB := hWB h x
    rw [horizonSum_of_lt hh, variance_eq_sub (MemLp.of_bound hWm.aestronglyMeasurable _
      (.of_forall fun y ↦ (Real.norm_eq_abs _).trans_le (hWC (h + 1) y)))]
    simp only [Pi.pow_apply]
    rw [hWh] at hWhB ⊢
    nlinarith [mul_nonneg (hf₀ h x) (sub_nonneg.2 hWhB), sq_nonneg (f h x)]
  · simp [horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

/-- **Jensen's and the Cauchy–Schwarz inequality along the horizon**: for nonnegative bounded
measurable rewards `g`, the finite-horizon sum of the square roots `√(g j)` from the step `h` is
at most `√((H - h) horizonSum κ H g h)`. -/
theorem horizonSum_sqrt_le {C : ℝ} (hg : ∀ j, Measurable (g j)) (hgC : ∀ j x, |g j x| ≤ C)
    (hg₀ : ∀ j x, 0 ≤ g j x) (h : ℕ) (x : α) :
    horizonSum κ H (fun j y ↦ √(g j y)) h x ≤ √((H - h : ℕ) * horizonSum κ H g h x) := by
  by_cases hh : h < H
  · have hT₀ (j : ℕ) (y : α) : 0 ≤ horizonSum κ H g j y := by
      simpa using (horizonSum_mem_Icc (κ := κ) (H := H) hg
        (fun j y ↦ ⟨hg₀ j y, (le_abs_self _).trans (hgC j y)⟩) j y).1
    have hsm (j : ℕ) : Measurable fun y ↦ √(g j y) := (hg j).sqrt
    have hsC (j : ℕ) (y : α) : |√(g j y)| ≤ √|C| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((le_abs_self _).trans ((hgC j y).trans (le_abs_self C)))
    have hT := integrable_horizonSum (κ := κ) (H := H) hg hgC (h + 1) (κ h x)
    set n : ℝ := ((H - (h + 1) : ℕ) : ℝ) with hn
    have hn₀ : 0 ≤ n := Nat.cast_nonneg _
    -- the induction hypothesis at the next step, integrated against `κ h x`, then Jensen
    have hstep : ∫ y, horizonSum κ H (fun j y ↦ √(g j y)) (h + 1) y ∂(κ h x) ≤
        √(n * ∫ y, horizonSum κ H g (h + 1) y ∂(κ h x)) := by
      have hsq : Integrable (fun y ↦ √(n * horizonSum κ H g (h + 1) y)) (κ h x) := by
        refine integrable_of_abs_le ((measurable_horizonSum hg (h + 1)).const_mul n).sqrt
          (B := √(n * (H * |C|))) (fun y ↦ ?_) _
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (abs_horizonSum_le_mul_abs hg hgC (h + 1) y)) hn₀)
      refine (integral_mono (integrable_horizonSum hsm hsC (h + 1) _) hsq
        fun y ↦ horizonSum_sqrt_le hg hgC hg₀ (h + 1) y).trans ?_
      have hJ := integral_sqrt_le_sqrt_measureReal_mul_integral (μ := κ h x)
        (.of_forall fun y ↦ mul_nonneg hn₀ (hT₀ (h + 1) y)) (hT.const_mul n)
      rwa [probReal_univ, one_mul, integral_const_mul] at hJ
    rw [horizonSum_of_lt hh, horizonSum_of_lt hh, show H - h = H - (h + 1) + 1 by omega,
      Nat.cast_add_one, ← hn]
    exact (add_le_add le_rfl hstep).trans
      (Real.sqrt_add_sqrt_mul_le (hg₀ h x) (integral_nonneg (hT₀ (h + 1))) hn₀)
  · simp [horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

/-- **The finite-horizon sum of the one-step standard deviations** [LWCGC24, Lemma 12]: for
nonnegative bounded measurable rewards `f` whose finite-horizon sum `W = horizonSum κ H f` is
bounded by `B` at every step, the finite-horizon sum of the one-step standard deviations
`√Var[W (j + 1); κ j y]` from the step `h` is at most `√(H - h) B`. -/
theorem horizonSum_sqrt_variance_le {B C : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, |f j x| ≤ C) (hf₀ : ∀ j x, 0 ≤ f j x) (hWB : ∀ j x, horizonSum κ H f j x ≤ B)
    (h : ℕ) (x : α) :
    horizonSum κ H (fun j y ↦ √Var[horizonSum κ H f (j + 1); κ j y]) h x ≤ √(H - h : ℕ) * B := by
  have hWC := abs_horizonSum_le_mul_abs (κ := κ) (H := H) hf hfC
  have hW₀ : 0 ≤ horizonSum κ H f h x := by
    simpa using (horizonSum_mem_Icc (κ := κ) (H := H) hf
      (fun j y ↦ ⟨hf₀ j y, (le_abs_self _).trans (hfC j y)⟩) h x).1
  have hB : 0 ≤ B := hW₀.trans (hWB h x)
  have hVarB (j : ℕ) (y : α) : |Var[horizonSum κ H f (j + 1); κ j y]| ≤ (H * |C|) ^ 2 := by
    rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le (measurable_horizonSum hf (j + 1)).aemeasurable
      (.of_forall (hWC (j + 1)))
  refine (horizonSum_sqrt_le (fun j ↦ (measurable_horizonSum hf (j + 1)).variance_kernel) hVarB
    (fun j y ↦ variance_nonneg _ _) h x).trans ?_
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have := horizonSum_variance_le hf hfC hf₀ hWB h x
  nlinarith [sq_nonneg (B - horizonSum κ H f h x)]

/-- The levels of measurable rewards in `[0, C]` lie in `[0, C H √H ^ l]`, and each of them is the
finite-horizon sum of nonnegative bounded measurable rewards. -/
private lemma horizonSumLevel_mem_Icc_and_exists {C : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, f j x ∈ Set.Icc 0 C) (hC : 0 ≤ C) (l : ℕ) :
    (∀ h x, horizonSumLevel κ H f l h x ∈ Set.Icc 0 (C * H * √H ^ l)) ∧
      ∃ g : ℕ → α → ℝ, (∀ j, Measurable (g j)) ∧ (∀ j y, |g j y| ≤ C * H * √H ^ l + C) ∧
        (∀ j y, 0 ≤ g j y) ∧ horizonSumLevel κ H f l = horizonSum κ H g := by
  have hb (l : ℕ) : 0 ≤ C * H * √H ^ l := by positivity
  induction l with
  | zero =>
    refine ⟨fun h x ↦ ?_, f, hf, fun j y ↦ ?_, fun j y ↦ (hfC j y).1, rfl⟩
    · have hW := horizonSum_mem_Icc (κ := κ) (H := H) hf hfC h x
      simp only [mul_zero, horizonSumLevel_zero, pow_zero, mul_one] at hW ⊢
      exact ⟨hW.1, hW.2.trans (by rw [mul_comm]; gcongr; exact_mod_cast Nat.sub_le H h)⟩
    · rw [abs_of_nonneg (hfC j y).1]
      linarith [(hfC j y).2, hb 0]
  | succ l ih =>
    obtain ⟨hVl, g, hg, hgC, hg₀, hVg⟩ := ih
    have hσ (j : ℕ) (y : α) : √Var[horizonSumLevel κ H f l (j + 1); κ j y] ≤ C * H * √H ^ l :=
      sqrt_variance_le_of_abs_le (measurable_horizonSumLevel hf l (j + 1)).aemeasurable (hb l)
        (.of_forall fun z ↦ abs_le.2 ⟨by linarith [(hVl (j + 1) z).1, hb l], (hVl (j + 1) z).2⟩)
    have hσm (j : ℕ) : Measurable fun y ↦ √Var[horizonSumLevel κ H f l (j + 1); κ j y] :=
      (measurable_horizonSumLevel hf l (j + 1)).variance_kernel.sqrt
    have hHl : C * H * √H ^ l ≤ C * H * √H ^ (l + 1) + C := by
      rcases Nat.eq_zero_or_pos H with hH | hH
      · simp [hH, hC]
      · have h1 : (1 : ℝ) ≤ √H := Real.one_le_sqrt.2 (by exact_mod_cast hH)
        have := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ h1 (Nat.le_succ l) : √H ^ l ≤ √H ^ (l + 1))
          (mul_nonneg hC (Nat.cast_nonneg H))
        linarith
    refine ⟨fun h x ↦ ⟨?_, ?_⟩, fun j y ↦ √Var[horizonSumLevel κ H f l (j + 1); κ j y], hσm,
      fun j y ↦ ?_, fun j y ↦ Real.sqrt_nonneg _, rfl⟩
    · simpa using (horizonSum_mem_Icc (κ := κ) (H := H) hσm
        (fun j y ↦ ⟨Real.sqrt_nonneg _, hσ j y⟩) h x).1
    · have h₁ := horizonSum_sqrt_variance_le (κ := κ) hg hgC hg₀
        (fun j y ↦ hVg ▸ (hVl j y).2) h x
      rw [← hVg] at h₁
      calc horizonSumLevel κ H f (l + 1) h x ≤ √(H - h : ℕ) * (C * H * √H ^ l) := h₁
        _ ≤ √H * (C * H * √H ^ l) := mul_le_mul_of_nonneg_right
            (Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le H h)) (hb l)
        _ = C * H * √H ^ (l + 1) := by ring
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (hσ j y).trans hHl

/-- **A priori bounds on the levels** [LWCGC24, Lemma 12]: for measurable rewards `f` in
`[0, C]`, the level `l` lies in `[0, C H √H ^ l]`. The level `0` is at most `C H`, and each level
multiplies the bound by `√H` (`ProbabilityTheory.Kernel.horizonSum_sqrt_variance_le`). -/
theorem horizonSumLevel_mem_Icc {C : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, f j x ∈ Set.Icc 0 C) (l h : ℕ) (x : α) :
    horizonSumLevel κ H f l h x ∈ Set.Icc 0 (C * H * √H ^ l) :=
  (horizonSumLevel_mem_Icc_and_exists hf hfC ((hfC 0 x).1.trans (hfC 0 x).2) l).1 h x

/-- The scalar recursion behind [LWCGC24, (113)–(119)]: for `B, ε ≥ 0`, `9 ε H ≤ 1` and
`H ≤ 4 ^ m`, if the errors `d l` and the next-level terms `e l` satisfy
`d l ≤ √ε e l + ε H B √H ^ l` for `l ≤ m`, `e l ≤ B √H ^ (l + 1) + d (l + 1)` and
`e m ≤ H B √H ^ m`, then `d 0 ≤ 4 B √(ε H)`. -/
private lemma le_four_mul_sqrt_of_le_mul_add {B ε : ℝ} (hB : 0 ≤ B) (hε₀ : 0 ≤ ε) {H m : ℕ}
    (hε : 9 * ε * H ≤ 1) (hm : H ≤ 4 ^ m) {d e : ℕ → ℝ}
    (hd : ∀ l ≤ m, d l ≤ √ε * e l + ε * H * (B * √H ^ l))
    (he : ∀ l, e l ≤ B * √H ^ (l + 1) + d (l + 1)) (hem : e m ≤ H * (B * √H ^ m)) :
    d 0 ≤ 4 * B * √(ε * H) := by
  -- rescaling: with `a = √ε` and `q = √(ε H)`, `a ^ l (B √H ^ l) = B q ^ l`
  set a : ℝ := √ε with ha_def
  set q : ℝ := √(ε * H) with hq_def
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have hq₀ : 0 ≤ q := Real.sqrt_nonneg _
  have hqa : q = a * √H := Real.sqrt_mul hε₀ _
  have hsH : √(H : ℝ) ^ 2 = H := Real.sq_sqrt (Nat.cast_nonneg _)
  have hq2 : q ^ 2 = ε * H := Real.sq_sqrt (mul_nonneg hε₀ (Nat.cast_nonneg _))
  have hab (l : ℕ) : a ^ l * (B * √H ^ l) = B * q ^ l := by rw [hqa, mul_pow]; ring
  have hq13 : q ≤ 1 / 3 := by
    rw [hq_def, show (1 / 3 : ℝ) = √(1 / 9) by
      rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  set θ : ℝ := q * (1 + q) / (1 - q) with hθ_def
  have hq1 : 0 < 1 - q := by linarith
  have hθ : q + q ^ 2 + θ * q = θ := by
    rw [hθ_def]
    field_simp
    ring
  have hθ₀ : 0 ≤ θ := by positivity
  set X : ℝ := q * √H + q ^ 2 with hX_def
  -- backward induction over the levels: `a ^ l d l ≤ B (θ q ^ l + q ^ m X)`
  have hind (k : ℕ) (hk : k ≤ m) : a ^ (m - k) * d (m - k) ≤ B * (θ * q ^ (m - k) + q ^ m * X) := by
    induction k with
    | zero =>
      rw [Nat.sub_zero]
      calc a ^ m * d m ≤ a ^ m * (a * (H * (B * √H ^ m)) + ε * H * (B * √H ^ m)) := by
            gcongr
            exact (hd m le_rfl).trans (by gcongr)
        _ = (a ^ m * (B * √H ^ m)) * (a * H + ε * H) := by ring
        _ = (B * q ^ m) * X := by
            have haH : a * H = q * √H := by
              rw [hqa, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
            rw [hab, hX_def, haH, ← hq2]
        _ ≤ B * (θ * q ^ m + q ^ m * X) := by nlinarith [mul_nonneg hθ₀ (pow_nonneg hq₀ m)]
    | succ k ih =>
      have hl : m - k = m - (k + 1) + 1 := by omega
      have h₁ := hd (m - (k + 1)) (Nat.sub_le _ _)
      have h₂ := he (m - (k + 1))
      have h₃ := ih (by omega)
      rw [hl] at h₃
      set l := m - (k + 1)
      calc a ^ l * d l ≤ a ^ l * (a * (B * √H ^ (l + 1) + d (l + 1)) +
            ε * H * (B * √H ^ l)) := by
            gcongr
            exact h₁.trans (by gcongr)
        _ = a ^ (l + 1) * (B * √H ^ (l + 1)) + a ^ (l + 1) * d (l + 1) +
            (a ^ l * (B * √H ^ l)) * (ε * H) := by ring
        _ ≤ B * q ^ (l + 1) + B * (θ * q ^ (l + 1) + q ^ m * X) + (B * q ^ l) * q ^ 2 := by
            rw [hab, hab, hq2]
            gcongr
        _ = B * (q ^ l * (q + q ^ 2 + θ * q) + q ^ m * X) := by ring
        _ = B * (θ * q ^ l + q ^ m * X) := by rw [hθ]; ring
  have h₀ := hind m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul, pow_zero, mul_one] at h₀
  -- after `m ≥ log₄ H` levels, `q ^ m √H ≤ 1`
  have hqm : q ^ m * √H ≤ 1 := by
    have h2 : √(H : ℝ) ≤ 2 ^ m := by
      rw [Real.sqrt_le_left (by positivity), ← pow_mul, mul_comm, pow_mul]
      exact_mod_cast hm.trans (by norm_num)
    calc q ^ m * √H ≤ (1 / 2) ^ m * 2 ^ m := by
          gcongr
          linarith
      _ = 1 := by rw [← mul_pow]; norm_num
  have hqm1 : q ^ m ≤ 1 := pow_le_one₀ hq₀ (by linarith)
  have hfin : q ^ m * X ≤ q + q ^ 2 := by
    rw [hX_def, mul_add, ← mul_assoc, mul_comm (q ^ m) q, mul_assoc]
    gcongr
    · exact mul_le_of_le_one_right hq₀ hqm
    · exact mul_le_of_le_one_left (sq_nonneg q) hqm1
  have hθ2 : θ ≤ 2 * q := by
    rw [hθ_def, div_le_iff₀ hq1]
    nlinarith
  calc d 0 ≤ B * (θ + q ^ m * X) := h₀
    _ ≤ B * (2 * q + (q + q ^ 2)) := by gcongr
    _ ≤ B * (4 * q) := by gcongr; nlinarith
    _ = 4 * B * √(ε * H) := by ring

/-- **The finite-horizon sums along two sequences of kernels with Bernstein-type deviations**
[LWCGC24, Lemma 9]. Let `κ` and `κ'` be sequences of Markov kernels and `f` measurable rewards in
`[0, C]`. Let `V = horizonSumLevel κ H f` be the levels `V 0 = horizonSum κ H f` and
`V (l + 1) = horizonSum κ H √Var_κ(V l)`, so that `0 ≤ V l ≤ C H √H ^ l`
(`ProbabilityTheory.Kernel.horizonSumLevel_mem_Icc`). Suppose that `κ'` deviates from `κ` on the
first levels by a Bernstein-type bound
`|κ' j (V l (j + 1)) - κ j (V l (j + 1))| ≤ √(ε Var_κ j(V l (j + 1))) + ε C H √H ^ l` at every step
`j < H`, for every `l ≤ m`, with `H ≤ 4 ^ m` and `9 ε H ≤ 1`. Then the finite-horizon sums of `f`
satisfy `|horizonSum κ' H f - horizonSum κ H f| ≤ 4 C H √(ε H)`.

With `ε = β / N`, [LWCGC24] assumes the deviation bound with the sup norm of `V l (j + 1)` in
place of `C H √H ^ l`, `m = log₂ H` and `12 β H < N`, and concludes the bound
`6 H √(3 β H / N)` for rewards in `[0, 1]`. The total-variance bound
`ProbabilityTheory.Kernel.horizonSum_variance_le`, through `W H = 0`, improves the factor `√(3 H)`
of each level in [LWCGC24, Lemma 12] to `√H`. -/
theorem abs_horizonSum_sub_horizonSum_le_of_abs_sub_le {C ε : ℝ} (hf : ∀ j, Measurable (f j))
    (hfC : ∀ j x, f j x ∈ Set.Icc 0 C) {m : ℕ} (hm : H ≤ 4 ^ m) (hε₀ : 0 ≤ ε)
    (hε : 9 * ε * H ≤ 1)
    (hdev : ∀ l ≤ m, ∀ j < H, ∀ y,
      |∫ z, horizonSumLevel κ H f l (j + 1) z ∂(κ' j y) -
          ∫ z, horizonSumLevel κ H f l (j + 1) z ∂(κ j y)| ≤
        √(ε * Var[horizonSumLevel κ H f l (j + 1); κ j y]) + ε * (C * H * √H ^ l))
    (h : ℕ) (x : α) :
    |horizonSum κ' H f h x - horizonSum κ H f h x| ≤ 4 * C * H * √(ε * H) := by
  -- The error `D l = |horizonSum κ' H (r l) h x - V l h x|` at level `l`, where
  -- `V l = horizonSum κ H (r l)`, is bounded by the simulation bound by `√ε` times
  -- `horizonSum κ' H (r (l + 1)) h x` plus `ε H C H √H ^ l`, and the former is `V (l + 1) h x` up
  -- to the error at level `l + 1` [LWCGC24, (113)–(116)]. The scalar recursion
  -- `le_four_mul_sqrt_of_le_mul_add` unrolls these bounds over the levels `l ≤ m`.
  have hC : 0 ≤ C := (hfC 0 x).1.trans (hfC 0 x).2
  set V := horizonSumLevel κ H f with hV_def
  set b : ℕ → ℝ := fun l ↦ C * H * √H ^ l with hb_def
  have hVm := measurable_horizonSumLevel (κ := κ) (H := H) hf
  have hVb : ∀ l j y, V l j y ∈ Set.Icc 0 (b l) := horizonSumLevel_mem_Icc hf hfC
  have hb₀ (l : ℕ) : 0 ≤ b l := (hVb l 0 x).1.trans (hVb l 0 x).2
  have hσ (l j : ℕ) (y : α) : √Var[V l (j + 1); κ j y] ≤ b l :=
    sqrt_variance_le_of_abs_le (hVm l (j + 1)).aemeasurable (hb₀ l)
      (.of_forall fun z ↦ abs_le.2 ⟨by linarith [(hVb l (j + 1) z).1, hb₀ l],
        (hVb l (j + 1) z).2⟩)
  -- the rewards `r l` of the levels: `V l = horizonSum κ H (r l)`
  set r : ℕ → ℕ → α → ℝ := fun l ↦ Nat.casesOn l f fun k j y ↦ √Var[V k (j + 1); κ j y]
    with hr_def
  have hr₀ : r 0 = f := rfl
  have hr (l : ℕ) : r (l + 1) = fun j y ↦ √Var[V l (j + 1); κ j y] := rfl
  have hr_meas (l j : ℕ) : Measurable (r l j) := by
    cases l
    exacts [hf j, (hVm _ (j + 1)).variance_kernel.sqrt]
  have hrB (l : ℕ) : ∃ B, ∀ j y, |r l j y| ≤ B := by
    cases l with
    | zero =>
      rw [hr₀]
      exact ⟨C, fun j y ↦ abs_le.2 ⟨by linarith [(hfC j y).1], (hfC j y).2⟩⟩
    | succ k => exact ⟨b k, fun j y ↦ (abs_of_nonneg (Real.sqrt_nonneg _)).trans_le (hσ k j y)⟩
  have hVr (l : ℕ) : V l = horizonSum κ H (r l) := by
    cases l <;> rfl
  -- the error `D l` at level `l`
  set D : ℕ → ℝ := fun l ↦ |horizonSum κ' H (r l) h x - V l h x| with hD_def
  have hstep (l : ℕ) (hl : l ≤ m) :
      D l ≤ √ε * horizonSum κ' H (r (l + 1)) h x + ε * H * (C * H * √H ^ l) := by
    obtain ⟨B, hB⟩ := hrB l
    obtain ⟨B', hB'⟩ := hrB (l + 1)
    have hdev' (j : ℕ) (hj : j < H) (y : α) :
        |∫ z, horizonSum κ H (r l) (j + 1) z ∂(κ' j y) -
          ∫ z, horizonSum κ H (r l) (j + 1) z ∂(κ j y)| ≤
          √ε * r (l + 1) j y + ε * b l := by
      rw [← hVr l, hr, ← Real.sqrt_mul hε₀]
      exact hdev l hl j hj y
    have hsim := abs_horizonSum_sub_horizonSum_le (κ := κ) (κ' := κ') (hr_meas l) hB
      (e := fun j y ↦ √ε * r (l + 1) j y + ε * b l)
      (fun j ↦ ((hr_meas (l + 1) j).const_mul _).add_const _)
      (D := √ε * B' + ε * b l) (fun j y ↦ (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]; gcongr; exact hB' j y)
        (abs_of_nonneg (mul_nonneg hε₀ (hb₀ l))).le)) hdev' h x
    rw [horizonSum_add (fun j ↦ (hr_meas (l + 1) j).const_mul _)
        (C := √ε * B') (fun j y ↦ by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]; gcongr; exact hB' j y)
        (fun _ ↦ measurable_const) (fun _ _ ↦ le_rfl),
      horizonSum_const_mul, horizonSum_const, ← hVr l] at hsim
    refine hsim.trans (add_le_add le_rfl ?_)
    rw [show ε * H * (C * H * √H ^ l) = H * (ε * b l) by simp only [hb_def]; ring]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le H h)
      (mul_nonneg hε₀ (hb₀ l))
  -- the next level: `horizonSum κ' H (r (l + 1)) h x ≤ V (l + 1) h x + D (l + 1)`
  have hnext (l : ℕ) :
      horizonSum κ' H (r (l + 1)) h x ≤ C * H * √H ^ (l + 1) + D (l + 1) := by
    have h₁ := le_abs_self (horizonSum κ' H (r (l + 1)) h x - V (l + 1) h x)
    linarith [(hVb (l + 1) h x).2]
  -- the last level: `horizonSum κ' H (r (m + 1)) h x ≤ H b m`
  have hlast : horizonSum κ' H (r (m + 1)) h x ≤ H * (C * H * √H ^ m) := by
    have := (horizonSum_mem_Icc (κ := κ') (H := H) (hr_meas (m + 1))
      (fun j y ↦ ⟨Real.sqrt_nonneg _, hσ m j y⟩) h x).2
    exact this.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le H h) (hb₀ m))
  have hD₀ : D 0 = |horizonSum κ' H f h x - horizonSum κ H f h x| := rfl
  rw [← hD₀, mul_assoc 4, mul_assoc 4]
  refine (le_four_mul_sqrt_of_le_mul_add (mul_nonneg hC (Nat.cast_nonneg _)) hε₀ hε hm
    (fun l hl ↦ (hstep l hl).trans_eq (by ring)) (fun l ↦ (hnext l).trans_eq (by ring))
    (hlast.trans_eq (by ring))).trans_eq ?_
  ring

end Markov

end ProbabilityTheory.Kernel
