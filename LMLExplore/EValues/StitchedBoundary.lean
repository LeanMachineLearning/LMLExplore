/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.SubPsi
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# Stitched boundaries for sub-ψ processes

The line-crossing inequality (`ProbabilityTheory.IsSubPsiProcess.measure_exists_add_mul_le_le`)
bounds the probability that a sub-ψ process `(S, V)` ever crosses one line `a + b V`. A line is a
poor time-uniform boundary: it is tight at one intrinsic time only. *Stitching* [HRMS21, §3.1]
splits intrinsic time into the geometric epochs `m η ^ k ≤ V < m η ^ (k + 1)`, takes on the
epoch `k` a line tuned to that epoch, with crossing probability `α / h k`, and bounds the
probability that any of them is crossed by the union bound `∑ k, α / h k ≤ α`. A single concave
curve above all these lines on their epochs is then crossed with probability at most `α`.

For the sub-gamma `ψ t = t ^ 2 / (2 (1 - c t))` on `0 ≤ t < 1 / c`, with `c ≥ 0`, the curve is the
*stitching function* of [HRMS21, (8)],
`𝒮(v) = √(k₁² v ℓ(v) + k₂² c² ℓ(v)²) + k₂ c ℓ(v)`, with
`ℓ(v) = log h (log_η (v / m)) + log (l₀ / α)`, `k₁ = (η^{1/4} + η^{-1/4}) / √2` and
`k₂ = (√η + 1) / 2` (`ProbabilityTheory.stitching η c ℓ v`). It grows like `√(v log h(log_η v))`:
for `h k = (k + 1) ^ s ζ(s)`, `s > 1`, it is the *polynomial stitched boundary*, of order
`√(v log log v)`, a finite-time law of the iterated logarithm. The sub-Gaussian case is `c = 0`.

The line of the epoch `k` has the parameter `t_k` with `ψ t_k = r_k / w_k`, where
`r_k = log (l₀ h k / α)` and `w_k = m η ^ (k + 1/2)` is the geometric mean of the ends of the
epoch; its value `(r_k + ψ t_k v) / t_k` at every `v` of the epoch is at most `𝒮(v)`.

## Main definitions

* `ProbabilityTheory.stitching η c ℓ v`: the stitching function at the intrinsic time `v` and the
  level `ℓ`.

## Main statements

* `ProbabilityTheory.IsSubPsiProcess.measure_exists_stitching_le_le` [HRMS21, Theorem 1]: the
  stitched boundary `v ↦ 𝒮(max v m)` is crossed with probability at most `α`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_le_and_stitching_le_le` [HRMS21, Theorem 1,
  (9)]: the probability of a crossing after the intrinsic time `v₀ ≥ m` is at most
  `α ∑ k ≥ ⌊log_η (v₀ / m)⌋, 1 / h k`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_stitching_mul_log_log_le_le` [HRMS21, (10)]: the
  polynomial stitched boundary, with
  `ℓ(v) = s log log (η v / m) + log (l₀ ζ(s) / (α log^s η))`.
* `ProbabilityTheory.measure_exists_stitching_le_sum_le_of_mem_oneSidedCondSubgaussianNull`: the
  stitched boundary for the random walks of the one-sided conditionally sub-Gaussian null.

## Implementation notes

[HRMS21] states the theorem for `α ∈ (0, 1)` and `l₀ ≥ 1`; the proof only uses `0 < α < l₀`. The
event is over all times `n`, including `n = 0`, and the intrinsic time need not be nonnegative.
The level `ℓ` may be any function above the level of [HRMS21] on `[m, ∞)`, which gives the closed
forms of `ℓ` directly. The weight `h` need only be monotone on `[0, ∞)`, positive at `0`, with
`∑ k, 1 / h k ≤ 1` in `ℝ≥0∞`.

## References

* [HRMS21] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform, nonparametric,
  nonasymptotic confidence sequences*, Ann. Statist. 49 (2021), 1055–1080, arXiv:1810.08240.
  Equation numbers are those of the arXiv version.
-/

public section

open MeasureTheory Set Finset Real Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {𝒩 : Set (Measure Ω)}
  {P : Measure Ω} {S V : ℕ → Ω → ℝ} {ψ : ℝ → ℝ} {Λ : Set ℝ}

/-! ### The stitching function -/

/-- The **stitching function** of [HRMS21, (8)] at the intrinsic time `v` and the level `ℓ`:
`√(k₁² v ℓ + k₂² c² ℓ²) + k₂ c ℓ`, with `k₁ = (η^{1/4} + η^{-1/4}) / √2` and
`k₂ = (√η + 1) / 2`. With the level `ℓ(v) = log h (log_η (v / m)) + log (l₀ / α)` it is the
time-uniform boundary of the sub-gamma processes of scale `c`, at the geometric spacing `η` of the
epochs. -/
noncomputable def stitching (η c ℓ v : ℝ) : ℝ :=
  √((√√η + (√√η)⁻¹) ^ 2 / 2 * v * ℓ + ((√η + 1) / 2) ^ 2 * c ^ 2 * ℓ ^ 2) + (√η + 1) / 2 * c * ℓ

theorem stitching_def (η c ℓ v : ℝ) :
    stitching η c ℓ v = √((√√η + (√√η)⁻¹) ^ 2 / 2 * v * ℓ + ((√η + 1) / 2) ^ 2 * c ^ 2 * ℓ ^ 2) +
      (√η + 1) / 2 * c * ℓ :=
  (rfl)

/-- The stitching function grows with the level. -/
theorem stitching_le_stitching {η c ℓ ℓ' v : ℝ} (hc : 0 ≤ c) (hv : 0 ≤ v) (hℓ : 0 ≤ ℓ)
    (hℓℓ' : ℓ ≤ ℓ') : stitching η c ℓ v ≤ stitching η c ℓ' v := by
  rw [stitching_def, stitching_def]
  gcongr

/-- The parameter `t = 2 / (c + √(c² + 2 w / r))` of the sub-gamma line through the level `r`
tuned to the intrinsic time `w` lies in `[0, 1 / c)`, with `ψ t = r / w`. -/
private theorem subGamma_param {c r w : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (hw : 0 < w) :
    0 < 2 / (c + √(c ^ 2 + 2 * w / r)) ∧ c * (2 / (c + √(c ^ 2 + 2 * w / r))) < 1 ∧
    (2 / (c + √(c ^ 2 + 2 * w / r))) ^ 2 / (2 * (1 - c * (2 / (c + √(c ^ 2 + 2 * w / r))))) =
      r / w := by
  set D := √(c ^ 2 + 2 * w / r) with hD_def
  have hD2 : D ^ 2 = c ^ 2 + 2 * w / r := sq_sqrt (by positivity)
  have hcD : c < D := (lt_sqrt hc).2 (lt_add_of_pos_right _ (by positivity))
  have hcD0 : 0 < c + D := by linarith
  have hD2r : D ^ 2 * r = c ^ 2 * r + 2 * w := by
    rw [hD2, add_mul, div_mul_cancel₀ _ hr.ne']
  refine ⟨by positivity, ?_, ?_⟩
  · rw [mul_div_assoc', div_lt_one hcD0]
    linarith
  · have h1 : 1 - c * (2 / (c + D)) = (D - c) / (c + D) := by
      field_simp
      ring
    have hDc : 0 < D - c := by linarith
    rw [h1, div_eq_div_iff (by positivity) hw.ne']
    field_simp
    nlinarith

/-- The sub-gamma line of the level `r`, tuned to the intrinsic time `w`, is below the stitching
curve, written with `q = η^{1/4}`, on `[w / q², q² w]`. -/
private theorem line_le_stitching_aux {c r w q v : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (hw : 0 < w)
    (hq : 0 < q) (hwv : w ≤ q ^ 2 * v) (hvw : v ≤ q ^ 2 * w) :
    (r + r / w * v) / (2 / (c + √(c ^ 2 + 2 * w / r))) ≤
      √((q + q⁻¹) ^ 2 / 2 * v * r + ((q ^ 2 + 1) / 2) ^ 2 * c ^ 2 * r ^ 2) +
        (q ^ 2 + 1) / 2 * c * r := by
  set D := √(c ^ 2 + 2 * w / r) with hD_def
  have hD2 : D ^ 2 = c ^ 2 + 2 * w / r := sq_sqrt (by positivity)
  have hD2r : D ^ 2 * r = c ^ 2 * r + 2 * w := by
    rw [hD2, add_mul, div_mul_cancel₀ _ hr.ne']
  have hv : 0 < v := pos_of_mul_pos_right (hw.trans_le hwv) (by positivity)
  -- `y = √(v / w)`, with `q⁻¹ ≤ y ≤ q`
  set y := √(v / w) with hy_def
  have hy2 : y ^ 2 = v / w := sq_sqrt (by positivity)
  have hy0 : 0 < y := sqrt_pos.2 (by positivity)
  have hyq : y ≤ q := by
    refine (pow_le_pow_iff_left₀ hy0.le hq.le two_ne_zero).1 ?_
    rw [hy2, div_le_iff₀ hw]
    linarith
  have hqy : q⁻¹ ≤ y := by
    refine (pow_le_pow_iff_left₀ (by positivity) hy0.le two_ne_zero).1 ?_
    rw [hy2, inv_pow, inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hw]
    linarith
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  have hq2 : q ^ 2 + 1 = q * (q + q⁻¹) := by
    rw [mul_add, hqq]
    ring
  -- the line is `(1 + y²) (c + D) r / 2`, and `1 + y² ≤ (q + q⁻¹) y`
  have h1 : 1 + y ^ 2 ≤ (q + q⁻¹) * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hqy)]
  have hg : (r + r / w * v) / (2 / (c + D)) = (1 + y ^ 2) * (c + D) * r / 2 := by
    rw [hy2]
    field_simp
  have h2 : (q + q⁻¹) / 2 * (y * D * r) ≤
      √((q + q⁻¹) ^ 2 / 2 * v * r + ((q ^ 2 + 1) / 2) ^ 2 * c ^ 2 * r ^ 2) := by
    refine le_sqrt_of_sq_le ?_
    have hv' : v = y ^ 2 * w := by rw [hy2, div_mul_cancel₀ _ hw.ne']
    rw [hq2, hv']
    have hyq2 : y ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hy0.le hyq 2
    have hc2 : 0 ≤ (q + q⁻¹) ^ 2 * c ^ 2 * r ^ 2 := by positivity
    have : ((q + q⁻¹) / 2 * (y * D * r)) ^ 2 =
        (q + q⁻¹) ^ 2 / 4 * y ^ 2 * (c ^ 2 * r ^ 2) + (q + q⁻¹) ^ 2 / 2 * (y ^ 2 * w) * r := by
      have : (y * D * r) ^ 2 = y ^ 2 * r * (D ^ 2 * r) := by ring
      rw [mul_pow, this, hD2r]
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hyq2 hc2]
  have h3 : (q + q⁻¹) / 2 * (y * c * r) ≤ (q ^ 2 + 1) / 2 * c * r := by
    rw [hq2]
    have : 0 ≤ (q + q⁻¹) / 2 * c * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hyq this]
  rw [hg]
  have : 0 ≤ (c + D) * r := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 this]

variable {c η m α : ℝ} {h : ℝ → ℝ}

/-- A weight `h`, monotone on `[0, ∞)` and positive at `0`, with `∑ k, 1 / h k ≤ 1`, is at least
`1` on `ℕ`. -/
private theorem pos_and_one_le_of_tsum (hh : MonotoneOn h (Ici 0)) (hh0 : 0 < h 0)
    (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1) (k : ℕ) : 0 < h k ∧ 1 ≤ h k := by
  have hk : 0 < h k :=
    hh0.trans_le (hh (mem_Ici.2 le_rfl) (mem_Ici.2 k.cast_nonneg) k.cast_nonneg)
  exact ⟨hk, (inv_le_one₀ hk).1 (ENNReal.ofReal_le_one.1 ((le_tsum _ k).trans hhs))⟩

/-- **The line of the epoch `k`.** Its parameter `t` lies in `[0, 1 / c)`, and on the epoch
`m η ^ k ≤ v ≤ m η ^ (k + 1)` the line `(log (l₀ h k / α) + ψ t v') / t` at every `v' ≤ v` is at
most the stitching function at `v`, at every level `ℓ ≥ log (l₀ h k / α)`. -/
private theorem exists_line {l₀ : ℝ} (hc : 0 ≤ c) (hα : 0 < α) (hαl₀ : α < l₀) (hη : 1 < η)
    (hm : 0 < m) (hh : MonotoneOn h (Ici 0)) (hh0 : 0 < h 0)
    (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1) (k : ℕ) :
    ∃ t, (0 ≤ t ∧ c * t < 1) ∧ 0 < t ∧ ∀ v v' ℓ, m * η ^ k ≤ v → v ≤ m * η ^ (k + 1) →
      v' ≤ v → log (l₀ * h k / α) ≤ ℓ →
        (log (l₀ * h k / α) + t ^ 2 / (2 * (1 - c * t)) * v') / t ≤ stitching η c ℓ v := by
  obtain ⟨hk0, hk1⟩ := pos_and_one_le_of_tsum hh hh0 hhs k
  set r := log (l₀ * h k / α) with hr_def
  have hl₀ : 0 < l₀ := hα.trans hαl₀
  have hr : 0 < r := log_pos ((one_lt_div hα).2 (by nlinarith))
  have hη0 : 0 < η := zero_lt_one.trans hη
  have hsη : 0 < √η := sqrt_pos.2 hη0
  set w := m * η ^ k * √η with hw_def
  have hw : 0 < w := by positivity
  obtain ⟨ht0, htc, hψ⟩ := subGamma_param hc hr hw
  refine ⟨_, ⟨ht0.le, htc⟩, ht0, fun v v' ℓ hkv hvk hv'v hrℓ ↦ ?_⟩
  set q := √√η with hq_def
  have hq : 0 < q := sqrt_pos.2 hsη
  have hq2 : q ^ 2 = √η := sq_sqrt hsη.le
  have hv : 0 ≤ v := (by positivity : 0 ≤ m * η ^ k).trans hkv
  rw [hψ]
  calc (r + r / w * v') / (2 / (c + √(c ^ 2 + 2 * w / r)))
      ≤ (r + r / w * v) / (2 / (c + √(c ^ 2 + 2 * w / r))) := by gcongr
    _ ≤ √((q + q⁻¹) ^ 2 / 2 * v * r + ((q ^ 2 + 1) / 2) ^ 2 * c ^ 2 * r ^ 2) +
        (q ^ 2 + 1) / 2 * c * r := by
      refine line_le_stitching_aux hc hr hw hq ?_ ?_
      · rw [hq2, hw_def, mul_comm _ √η]
        exact mul_le_mul_of_nonneg_left hkv hsη.le
      · calc v ≤ m * η ^ (k + 1) := hvk
          _ = q ^ 2 * w := by
            rw [hq2, hw_def, pow_succ]
            linear_combination (m * η ^ k) * (mul_self_sqrt hη0.le).symm
    _ = stitching η c r v := by
      rw [stitching_def, ← hq_def, ← hq2]
    _ ≤ stitching η c ℓ v := stitching_le_stitching hc hv hr.le hrℓ

/-- On the epoch `k ≤ x`, the level `log (l₀ h k / α)` of the line is at most the level
`log (h x) + log (l₀ / α)` of the stitching function. -/
private theorem log_le_log_add_log {l₀ : ℝ} (hα : 0 < α) (hαl₀ : α < l₀)
    (hh : MonotoneOn h (Ici 0)) (hh0 : 0 < h 0) (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1)
    {k : ℕ} {x : ℝ} (hkx : (k : ℝ) ≤ x) : log (l₀ * h k / α) ≤ log (h x) + log (l₀ / α) := by
  have hk0 := (pos_and_one_le_of_tsum hh hh0 hhs k).1
  have hl₀ : 0 < l₀ := hα.trans hαl₀
  rw [show l₀ * h k / α = h k * (l₀ / α) by ring, log_mul hk0.ne' (by positivity)]
  gcongr
  exact hh (mem_Ici.2 k.cast_nonneg) (mem_Ici.2 (k.cast_nonneg.trans hkx)) hkx

/-- The union bound over the lines of the epochs: `l₀ ∑ i, exp (-log (l₀ f i / α))` is
`α ∑ i, 1 / f i`. -/
private theorem ofReal_mul_tsum_exp_neg_log {l₀ : ℝ} (hα : 0 < α) (hαl₀ : α < l₀) {f : ℕ → ℝ}
    (hf : ∀ i, 0 < f i) :
    ENNReal.ofReal l₀ * ∑' i, ENNReal.ofReal (exp (-log (l₀ * f i / α))) =
      ENNReal.ofReal α * ∑' i, ENNReal.ofReal (f i)⁻¹ := by
  have hl₀ : 0 < l₀ := hα.trans hαl₀
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  congr 1
  ext i
  have := hf i
  rw [← ENNReal.ofReal_mul hl₀.le, ← ENNReal.ofReal_mul hα.le, exp_neg, exp_log (by positivity)]
  congr 1
  field_simp

/-- For `v ≥ m`, `⌊log_η (v / m)⌋₊` is the epoch of `v`. -/
private theorem mem_epoch {v : ℝ} (hη : 1 < η) (hm : 0 < m) (hv : m ≤ v) :
    m * η ^ ⌊logb η (v / m)⌋₊ ≤ v ∧ v ≤ m * η ^ (⌊logb η (v / m)⌋₊ + 1) := by
  constructor
  · rw [mul_comm, ← le_div_iff₀ hm]
    exact pow_natFloor_logb_le_self hη ((one_le_div hm).2 hv)
  · rw [mul_comm, ← div_le_iff₀ hm]
    exact (lt_pow_natFloor_logb_add_one hη (div_pos (hm.trans_le hv) hm)).le

/-! ### The stitched boundary -/

namespace IsSubPsiProcess

/-- **The stitched boundary** [HRMS21, Theorem 1]. Let `(S, V)` be an `l₀`-sub-gamma process of
scale `c ≥ 0`, sub-ψ for `ψ t = t ^ 2 / (2 (1 - c t))` on `0 ≤ t < 1 / c`, and `P` a probability
measure of the null. Let `0 < α < l₀`, `η > 1`, `m > 0`, and `h` a weight monotone on `[0, ∞)`,
positive at `0`, with `∑ k, 1 / h k ≤ 1`. For every level `ℓ` at least
`log h (log_η (v / m)) + log (l₀ / α)` at every `v ≥ m`, the probability that `S` ever crosses
the stitched boundary `v ↦ 𝒮(max v m)` is at most `α`. -/
theorem measure_exists_stitching_le_le {l₀ : ℝ}
    (hS : IsSubPsiProcess S V (fun t ↦ t ^ 2 / (2 * (1 - c * t))) {t | 0 ≤ t ∧ c * t < 1}
      (ENNReal.ofReal l₀) ℱ 𝒩) (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hc : 0 ≤ c)
    (hα : 0 < α) (hαl₀ : α < l₀) (hη : 1 < η) (hm : 0 < m) (hh : MonotoneOn h (Ici 0))
    (hh0 : 0 < h 0) (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1) {ℓ : ℝ → ℝ}
    (hℓ : ∀ v, m ≤ v → log (h (logb η (v / m))) + log (l₀ / α) ≤ ℓ v) :
    P {ω | ∃ n, stitching η c (ℓ (max (V n ω) m)) (max (V n ω) m) ≤ S n ω} ≤
      ENNReal.ofReal α := by
  choose t ht ht0 hline using exists_line hc hα hαl₀ hη hm hh hh0 hhs
  have hmain := hS.measure_exists_mem_and_le_le hP (r := fun k : ℕ ↦ log (l₀ * h k / α)) ht ht0
    (A := univ) (u := fun v ↦ stitching η c (ℓ (max v m)) (max v m)) fun v _ ↦ by
      have hv : m ≤ max v m := le_max_right v m
      obtain ⟨h₁, h₂⟩ := mem_epoch hη hm hv
      refine ⟨_, hline _ _ v _ h₁ h₂ (le_max_left v m) ?_⟩
      refine (log_le_log_add_log hα hαl₀ hh hh0 hhs ?_).trans (hℓ _ hv)
      exact Nat.floor_le (logb_nonneg hη ((one_le_div hm).2 hv))
  simp only [mem_univ, true_and] at hmain
  refine hmain.trans ?_
  rw [ofReal_mul_tsum_exp_neg_log hα hαl₀ fun i ↦ (pos_and_one_le_of_tsum hh hh0 hhs i).1]
  exact (mul_le_mul_right hhs _).trans_eq (mul_one _)

/-- **Late crossings of the stitched boundary** [HRMS21, Theorem 1, (9)]. Under the hypotheses of
`ProbabilityTheory.IsSubPsiProcess.measure_exists_stitching_le_le`, for every `v₀ ≥ m`, the
probability that `S` crosses the stitching curve `v ↦ 𝒮(v)` at some time with intrinsic time at
least `v₀` is at most `α ∑ k ≥ ⌊log_η (v₀ / m)⌋, 1 / h k`. -/
theorem measure_exists_le_and_stitching_le_le {l₀ : ℝ}
    (hS : IsSubPsiProcess S V (fun t ↦ t ^ 2 / (2 * (1 - c * t))) {t | 0 ≤ t ∧ c * t < 1}
      (ENNReal.ofReal l₀) ℱ 𝒩) (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hc : 0 ≤ c)
    (hα : 0 < α) (hαl₀ : α < l₀) (hη : 1 < η) (hm : 0 < m) (hh : MonotoneOn h (Ici 0))
    (hh0 : 0 < h 0) (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1) {ℓ : ℝ → ℝ}
    (hℓ : ∀ v, m ≤ v → log (h (logb η (v / m))) + log (l₀ / α) ≤ ℓ v) {v₀ : ℝ} (hv₀ : m ≤ v₀) :
    P {ω | ∃ n, v₀ ≤ V n ω ∧ stitching η c (ℓ (V n ω)) (V n ω) ≤ S n ω} ≤
      ENNReal.ofReal α * ∑' k : ℕ, ENNReal.ofReal (h ↑(k + ⌊logb η (v₀ / m)⌋₊))⁻¹ := by
  choose t ht ht0 hline using exists_line hc hα hαl₀ hη hm hh hh0 hhs
  set k₀ := ⌊logb η (v₀ / m)⌋₊
  have hmain := hS.measure_exists_mem_and_le_le hP (t := fun i ↦ t (i + k₀))
    (r := fun i : ℕ ↦ log (l₀ * h ↑(i + k₀) / α)) (fun i ↦ ht _) (fun i ↦ ht0 _)
    (A := Ici v₀) (u := fun v ↦ stitching η c (ℓ v) v) fun v hv ↦ by
      have hmv : m ≤ v := hv₀.trans hv
      obtain ⟨h₁, h₂⟩ := mem_epoch hη hm hmv
      have hk : k₀ ≤ ⌊logb η (v / m)⌋₊ := Nat.floor_mono (logb_le_logb_of_le hη
        (div_pos (hm.trans_le hv₀) hm) (div_le_div_of_nonneg_right (mem_Ici.1 hv) hm.le))
      refine ⟨⌊logb η (v / m)⌋₊ - k₀, ?_⟩
      simp only [Nat.sub_add_cancel hk]
      refine hline _ _ v _ h₁ h₂ le_rfl ?_
      refine (log_le_log_add_log hα hαl₀ hh hh0 hhs ?_).trans (hℓ _ hmv)
      exact Nat.floor_le (logb_nonneg hη ((one_le_div hm).2 hmv))
  simp only [Set.mem_Ici] at hmain
  exact hmain.trans_eq
    (ofReal_mul_tsum_exp_neg_log hα hαl₀ fun i ↦ (pos_and_one_le_of_tsum hh hh0 hhs _).1)

/-- **The polynomial stitched boundary** [HRMS21, (10)]. Under the hypotheses of
`ProbabilityTheory.IsSubPsiProcess.measure_exists_stitching_le_le`, with the weight
`h k = (k + 1) ^ s ζ(s)` for `s > 1`, the stitched boundary with the level
`ℓ(v) = s log log (η v / m) + log (l₀ ζ(s) / (α log^s η))` is crossed with probability at most
`α`. It grows like `√(s k₁² v log log v)`, a finite-time law of the iterated logarithm. -/
theorem measure_exists_stitching_mul_log_log_le_le {l₀ s : ℝ}
    (hS : IsSubPsiProcess S V (fun t ↦ t ^ 2 / (2 * (1 - c * t))) {t | 0 ≤ t ∧ c * t < 1}
      (ENNReal.ofReal l₀) ℱ 𝒩) (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hc : 0 ≤ c)
    (hα : 0 < α) (hαl₀ : α < l₀) (hη : 1 < η) (hm : 0 < m) (hs : 1 < s) :
    P {ω | ∃ n, stitching η c (s * log (log (η * max (V n ω) m / m)) +
      log (l₀ * (riemannZeta s).re / (α * log η ^ s))) (max (V n ω) m) ≤ S n ω} ≤
      ENNReal.ofReal α := by
  set Z := (riemannZeta s).re with hZ_def
  have hZs := TauCeti.hasSum_nat_add_one_rpow_neg_riemannZeta_re hs
  rw [← hZ_def] at hZs
  have hZ : 0 < Z := hZs.tsum_eq ▸ hZs.summable.tsum_pos (fun _ ↦ by positivity) 0 (by simp)
  have hl₀ : 0 < l₀ := hα.trans hαl₀
  have hlη : 0 < log η := log_pos hη
  refine hS.measure_exists_stitching_le_le hP hc hα hαl₀ hη hm (h := fun x ↦ (x + 1) ^ s * Z)
    (ℓ := fun v ↦ s * log (log (η * v / m)) + log (l₀ * Z / (α * log η ^ s)))
    (fun x hx y hy hxy ↦ ?_) (by simpa using hZ) ?_ fun v hv ↦ le_of_eq ?_
  · have := mem_Ici.1 hx
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow (by linarith) (by linarith) (by linarith)) hZ.le
  · have hf : ∀ k : ℕ, ((((k : ℝ) + 1) ^ s * Z)⁻¹) = ((k : ℝ) + 1) ^ (-s) / Z := fun k ↦ by
      rw [rpow_neg (by positivity), div_eq_mul_inv, mul_inv]
    simp only [hf]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (hZs.summable.div_const Z),
      (hZs.div_const Z).tsum_eq, div_self hZ.ne', ENNReal.ofReal_one]
  · -- `log_η (v / m) + 1 = log (η v / m) / log η`
    have hvm : 0 < v / m := div_pos (hm.trans_le hv) hm
    have hx : 0 ≤ logb η (v / m) := logb_nonneg hη ((one_le_div hm).2 hv)
    have hηvm : η * v / m = η * (v / m) := mul_div_assoc η v m
    have hlog : 0 < log (η * v / m) := by
      rw [hηvm, log_mul (by positivity) hvm.ne']
      have := log_nonneg ((one_le_div hm).2 hv)
      linarith
    have h1 : logb η (v / m) + 1 = log (η * v / m) / log η := by
      rw [hηvm, log_mul (by positivity) hvm.ne', logb]
      field_simp
      ring
    have e₁ : log ((logb η (v / m) + 1) ^ s * Z) =
        s * (log (log (η * v / m)) - log (log η)) + log Z := by
      rw [log_mul (by positivity) hZ.ne', log_rpow (by positivity), h1, log_div hlog.ne' hlη.ne']
    have e₂ : log (l₀ * Z / (α * log η ^ s)) = log l₀ + log Z - (log α + s * log (log η)) := by
      rw [log_div (by positivity) (by positivity), log_mul hl₀.ne' hZ.ne',
        log_mul hα.ne' (by positivity), log_rpow hlη]
    rw [e₁, e₂, log_div hl₀.ne' hα.ne']
    ring

end IsSubPsiProcess

/-- **The stitched boundary for the one-sided conditionally sub-Gaussian null** [HRMS21,
Theorem 1, `c = 0`]. Under every member of `oneSidedCondSubgaussianNull`, for `0 < α < 1`,
`η > 1`, `m > 0`, a weight `h` monotone on `[0, ∞)`, positive at `0`, with `∑ k, 1 / h k ≤ 1`,
and every level `ℓ` at least `log h (log_η (v / m)) + log (1 / α)` at every `v ≥ m`, the
probability that the random walk `∑ k < n, ω k` ever crosses `n ↦ 𝒮(max n m)` is at most `α`. -/
theorem measure_exists_stitching_le_sum_le_of_mem_oneSidedCondSubgaussianNull
    {P : Measure (ℕ → ℝ)} (hP : P ∈ oneSidedCondSubgaussianNull) (hα : 0 < α) (hα1 : α < 1)
    (hη : 1 < η) (hm : 0 < m) (hh : MonotoneOn h (Ici 0)) (hh0 : 0 < h 0)
    (hhs : ∑' k : ℕ, ENNReal.ofReal (h k)⁻¹ ≤ 1) {ℓ : ℝ → ℝ}
    (hℓ : ∀ v, m ≤ v → log (h (logb η (v / m))) + log (1 / α) ≤ ℓ v) :
    P {ω | ∃ n : ℕ, stitching η 0 (ℓ (max (n : ℝ) m)) (max (n : ℝ) m) ≤ ∑ k ∈ range n, ω k} ≤
      ENNReal.ofReal α := by
  have := isProbabilityMeasure_of_mem_oneSidedCondSubgaussianNull hP
  have hsub := isSubPsiProcess_sum_condEVarNull (ψ := fun t ↦ t ^ 2 / 2) (Λ := Ici 0)
    (ℱ := Filtration.piLT) (X := fun k ω ↦ ω k)
    fun k ↦ Filtration.measurable_piLT_apply k.lt_succ_self
  rw [← oneSidedCondSubgaussianNull_eq_condEVarNull] at hsub
  have hsub' : IsSubPsiProcess (fun n ω ↦ ∑ k ∈ range n, ω k) (fun n _ ↦ (n : ℝ))
      (fun t ↦ t ^ 2 / (2 * (1 - 0 * t))) {t | 0 ≤ t ∧ 0 * t < 1} (ENNReal.ofReal 1)
      Filtration.piLT oneSidedCondSubgaussianNull := by
    simpa using hsub.mono_param (Λ' := {t | 0 ≤ t ∧ 0 * t < 1}) fun t ht ↦ ht.1
  exact hsub'.measure_exists_stitching_le_le hP le_rfl hα hα1 hη hm hh hh0 hhs hℓ

end ProbabilityTheory
