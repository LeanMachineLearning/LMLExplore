/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue
import LMLExplore.InformationTheory.KullbackLeibler.Pinsker
import LMLExplore.MeasureTheory.Measure.Weighted
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# The relative entropy of vectors on a finite type

For nonnegative vectors `x z : α → ℝ` on a finite type `α`, with `x a = 0` whenever `z a = 0`, the
relative entropy of `x` with respect to `z` is `∑ a, x a * log (x a / z a)`. When `x` and `z` are
probability vectors, it is the Kullback–Leibler divergence of the corresponding laws on `α`: for
finite measures `μ ≪ ν` on `α` with measurable singletons, `(klDiv μ ν).toReal` is the relative
entropy of the vectors of masses `a ↦ μ.real {a}` and `a ↦ ν.real {a}`, plus Mathlib's mass
correction `ν.real univ - μ.real univ`.

**Gibbs' inequality** states that it is nonnegative as soon as `∑ a, z a ≤ ∑ a, x a`; it follows
from the log-sum inequality. **Pinsker's inequality** for probability vectors reads
`(∑ a, |x a - z a|) ^ 2 ≤ 2 ∑ a, x a * log (x a / z a)` [CT, Lemma 11.6.1]. It is Tau Ceti's
Pinsker inequality `TauCeti.etvDist_sq_le_two_mul_klDiv`, in its real form
`LMLExplore.tvDist_sq_le_two_mul_toReal_klDiv`, for the laws on `α` of masses `x` and `z`
(`LMLExplore.weightedMeasure`), whose total variation distance is the `ℓ¹` distance of `x` and
`z` (`MeasureTheory.tvDist_eq_tsum_abs_singleton`) and whose Kullback–Leibler divergence is the
relative entropy of `x` with respect to `z`. In particular, the relative entropy of two
probability vectors vanishes only when they are equal.

The **Gibbs variational principle** describes the log-partition function of a vector `v` under a
probability vector `p` with positive coordinates as a maximum over probability vectors `q`:
`log (∑ a, p a * exp (v a)) = max_q (∑ a, q a * v a - ∑ a, q a * log (q a / p a))`, attained at the
Gibbs vector `q a = p a * exp (v a) / ∑ b, p b * exp (v b)`. The inequality is Gibbs' inequality
for `q` with respect to the Gibbs vector. This is the finite case of the duality between the
log-partition function and the relative entropy, and the computation of the stability term of
exponential weights in online learning.

## Main statements

* `LMLExplore.toReal_klDiv_eq_sum_mul_log_div`: the Kullback–Leibler divergence of finite measures
  `μ ≪ ν` on a finite type is the relative entropy of their vectors of masses, up to the mass
  correction.
* `LMLExplore.sum_mul_log_div_nonneg`: Gibbs' inequality.
* `LMLExplore.sq_sum_abs_sub_le_two_mul_sum_mul_log_div`: Pinsker's inequality for probability
  vectors.
* `LMLExplore.sum_mul_log_div_eq_zero_iff`: the relative entropy of two probability vectors
  vanishes if and only if they are equal.
* `LMLExplore.sum_mul_log_div_mul_exp_div_eq`: the relative entropy with respect to the Gibbs
  vector.
* `LMLExplore.sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp`,
  `LMLExplore.isGreatest_sum_mul_sub_sum_mul_log_div`: the Gibbs variational principle.

## References

* [CT] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.

`LMLExplore.toReal_klDiv_eq_sum_mul_log_div` is adapted, and generalised from probability vectors
to finite measures, from the formalization Essakine2026Tight
(`github.com/RemyDegenne/Essakine2026Tight`, file
`ForLMLExplore/InformationTheory/KullbackLeibler/Fintype.lean`, commit
`520dd39a55fa4e9a62a4a2d51f48163926176a5d`, by Rémy Degenne, Apache 2.0) of A. Essakine and
C. Vernade, *Tight sample complexity bounds for entropic best policy identification*, COLT 2026.
-/

public section

open Finset Real MeasureTheory InformationTheory
open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- **Gibbs' inequality**: for nonnegative vectors `x` and `z` with `x a = 0` whenever `z a = 0`
and `∑ a, z a ≤ ∑ a, x a`, the relative entropy `∑ a, x a * log (x a / z a)` is nonnegative. This
holds in particular for two probability vectors. -/
theorem sum_mul_log_div_nonneg {x z : α → ℝ} (hx : ∀ a, 0 ≤ x a) (hz : ∀ a, 0 ≤ z a)
    (hxz : ∀ a, z a = 0 → x a = 0) (hsum : ∑ a, z a ≤ ∑ a, x a) :
    0 ≤ ∑ a, x a * log (x a / z a) := by
  refine le_trans ?_ (sum_mul_log_div_sum_le_sum_mul_log_div univ (fun a _ ↦ hx a)
    (fun a _ ↦ hz a) fun a _ ↦ hxz a)
  rcases (sum_nonneg fun a (_ : a ∈ univ) ↦ hz a).eq_or_lt with hZ | hZ
  · rw [← hZ, div_zero, log_zero, mul_zero]
  · exact mul_nonneg (sum_nonneg fun a _ ↦ hx a) (log_nonneg ((one_le_div hZ).2 hsum))

/-- The Kullback–Leibler divergence of finite measures `μ ≪ ν` on a finite type with measurable
singletons is the relative entropy `∑ a, μ{a} log (μ{a} / ν{a})` of their vectors of masses, plus
the mass correction `ν(univ) - μ(univ)`, which vanishes for probability measures. Unlike Tau Ceti's
`TauCeti.klDiv_eq_ofReal_sum_log_singleton`, `ν` may have atoms of mass zero. -/
theorem toReal_klDiv_eq_sum_mul_log_div [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ a, μ.real {a} * log (μ.real {a} / ν.real {a}) + ν.real Set.univ
      - μ.real Set.univ := by
  rw [toReal_klDiv hμν Integrable.of_finite, integral_fintype Integrable.of_finite]
  congr 2
  refine sum_congr rfl fun a _ ↦ ?_
  rw [smul_eq_mul]
  by_cases hμa : μ {a} = 0
  · simp [measureReal_def, hμa]
  rw [llr, Measure.rnDeriv_eq_measure_singleton_div (fun h ↦ hμa (hμν h)) (measure_ne_top ν _),
    ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- **Pinsker's inequality** for probability vectors: if `x` and `z` lie in the simplex and
`x a = 0` whenever `z a = 0`, then `(∑ a, |x a - z a|) ^ 2 ≤ 2 ∑ a, x a * log (x a / z a)`.
The sum on the right is the relative entropy of `x` with respect to `z`, and the sum on the left
the total variation distance of the laws on `α` of masses `x` and `z`. This is Tau Ceti's
`TauCeti.etvDist_sq_le_two_mul_klDiv`, in its real form `tvDist_sq_le_two_mul_toReal_klDiv`, for
these laws. -/
theorem sq_sum_abs_sub_le_two_mul_sum_mul_log_div {x z : α → ℝ} (hx : x ∈ simplex α)
    (hz : z ∈ simplex α) (hxz : ∀ a, z a = 0 → x a = 0) :
    (∑ a, |x a - z a|) ^ 2 ≤ 2 * ∑ a, x a * log (x a / z a) := by
  -- the laws `μ` and `ν` on `α`, with the discrete σ-algebra, of masses `x` and `z`
  let _ : MeasurableSpace α := ⊤
  set μ := weightedMeasure x
  set ν := weightedMeasure z
  have := isProbabilityMeasure_weightedMeasure hx
  have := isProbabilityMeasure_weightedMeasure hz
  have hμν : μ ≪ ν := weightedMeasure_absolutelyContinuous fun a ha ↦
    ((mem_simplex_iff.1 hz).1 a).lt_of_ne' fun h ↦ ha.ne' (hxz a h)
  have hμ (a : α) : μ.real {a} = x a := measureReal_weightedMeasure_singleton_of_mem_simplex hx a
  have hν (a : α) : ν.real {a} = z a := measureReal_weightedMeasure_singleton_of_mem_simplex hz a
  -- the relative entropy is `KL(μ, ν)` and the `ℓ¹` distance is `tvDist μ ν`
  have h_kl : (klDiv μ ν).toReal = ∑ a, x a * log (x a / z a) := by
    simp [toReal_klDiv_eq_sum_mul_log_div hμν, hμ, hν]
  have h_tv : tvDist μ ν = ∑ a, |x a - z a| := by
    simp [tvDist_eq_tsum_abs_singleton, hμ, hν]
  have h_fin : klDiv μ ν ≠ ∞ := klDiv_ne_top_iff.2 ⟨hμν, Integrable.of_finite⟩
  rw [← h_kl, ← h_tv]
  exact tvDist_sq_le_two_mul_toReal_klDiv h_fin

/-- The relative entropy of two probability vectors `x` and `z`, with `x a = 0` whenever
`z a = 0`, vanishes if and only if `x = z`. The forward direction follows from Pinsker's
inequality. -/
theorem sum_mul_log_div_eq_zero_iff {x z : α → ℝ} (hx : x ∈ simplex α) (hz : z ∈ simplex α)
    (hxz : ∀ a, z a = 0 → x a = 0) : ∑ a, x a * log (x a / z a) = 0 ↔ x = z := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h_pinsker := sq_sum_abs_sub_le_two_mul_sum_mul_log_div hx hz hxz
  rw [h, mul_zero] at h_pinsker
  have h_sum : ∑ a, |x a - z a| = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h_pinsker (sq_nonneg _))
  funext a
  exact sub_eq_zero.1 (abs_eq_zero.1
    ((sum_eq_zero_iff_of_nonneg fun a _ ↦ abs_nonneg _).1 h_sum a (mem_univ a)))

/-- The relative entropy of a vector `q` with `∑ a, q a = 1` with respect to the Gibbs vector
`a ↦ p a * exp (v a) / ∑ b, p b * exp (v b)` is
`∑ a, q a * log (q a / p a) - ∑ a, q a * v a + log (∑ b, p b * exp (v b))`, provided `q a = 0`
whenever `p a = 0` and the partition function `∑ b, p b * exp (v b)` does not vanish. -/
theorem sum_mul_log_div_mul_exp_div_eq {p q v : α → ℝ} (hq : ∑ a, q a = 1)
    (hqp : ∀ a, p a = 0 → q a = 0) (hZ : ∑ b, p b * exp (v b) ≠ 0) :
    ∑ a, q a * log (q a / (p a * exp (v a) / ∑ b, p b * exp (v b))) =
      ∑ a, q a * log (q a / p a) - ∑ a, q a * v a + log (∑ b, p b * exp (v b)) := by
  have h_pt (a : α) : q a * log (q a / (p a * exp (v a) / ∑ b, p b * exp (v b))) =
      q a * log (q a / p a) - q a * v a + q a * log (∑ b, p b * exp (v b)) := by
    rcases eq_or_ne (q a) 0 with h0 | h0
    · simp [h0]
    have hpa : p a ≠ 0 := fun h ↦ h0 (hqp a h)
    rw [log_div h0 (div_ne_zero (mul_ne_zero hpa (exp_pos _).ne') hZ),
      log_div (mul_ne_zero hpa (exp_pos _).ne') hZ, log_mul hpa (exp_pos _).ne', log_exp,
      log_div h0 hpa]
    ring
  simp_rw [h_pt, sum_add_distrib, sum_sub_distrib, ← sum_mul, hq, one_mul]

/-- **Gibbs variational principle**, upper bound. For probability vectors `p` and `q` with
`q a = 0` whenever `p a = 0` and every vector `v`,
`∑ a, q a * v a - ∑ a, q a * log (q a / p a) ≤ log (∑ a, p a * exp (v a))`. This is Gibbs'
inequality for `q` with respect to the Gibbs vector `a ↦ p a * exp (v a) / ∑ b, p b * exp (v b)`.
-/
theorem sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp {p q : α → ℝ} (hp : p ∈ simplex α)
    (hq : q ∈ simplex α) (hqp : ∀ a, p a = 0 → q a = 0) (v : α → ℝ) :
    ∑ a, q a * v a - ∑ a, q a * log (q a / p a) ≤ log (∑ a, p a * exp (v a)) := by
  obtain ⟨hp0, -⟩ := mem_simplex_iff.1 hp
  obtain ⟨hq0, hq1⟩ := mem_simplex_iff.1 hq
  have hZ : 0 < ∑ a, p a * exp (v a) := sum_mul_pos_of_mem_simplex hp fun a ↦ exp_pos (v a)
  -- Gibbs' inequality for `q` with respect to the Gibbs vector
  have hr0 (a : α) : 0 ≤ p a * exp (v a) / ∑ b, p b * exp (v b) :=
    div_nonneg (mul_nonneg (hp0 a) (exp_pos _).le) hZ.le
  have hr1 : ∑ a, p a * exp (v a) / ∑ b, p b * exp (v b) = 1 := by
    rw [← sum_div, div_self hZ.ne']
  have hrq (a : α) (ha : p a * exp (v a) / ∑ b, p b * exp (v b) = 0) : q a = 0 :=
    hqp a (by simpa [hZ.ne', (exp_pos _).ne'] using ha)
  have h_gibbs := sum_mul_log_div_nonneg hq0 hr0 hrq (hr1.trans hq1.symm).le
  rw [sum_mul_log_div_mul_exp_div_eq hq1 hqp hZ.ne'] at h_gibbs
  linarith

/-- **Gibbs variational principle**. For a probability vector `p` with positive coordinates and
every vector `v`, the maximum over probability vectors `q` of
`∑ a, q a * v a - ∑ a, q a * log (q a / p a)` is the log-partition function
`log (∑ a, p a * exp (v a))`. It is attained at the Gibbs vector
`a ↦ p a * exp (v a) / ∑ b, p b * exp (v b)`. -/
theorem isGreatest_sum_mul_sub_sum_mul_log_div {p : α → ℝ} (hp : p ∈ simplex α)
    (hp0 : ∀ a, 0 < p a) (v : α → ℝ) :
    IsGreatest ((fun q ↦ ∑ a, q a * v a - ∑ a, q a * log (q a / p a)) '' simplex α)
      (log (∑ a, p a * exp (v a))) := by
  refine ⟨?_, ?_⟩
  · have hZ : 0 < ∑ a, p a * exp (v a) := sum_mul_pos_of_mem_simplex hp fun a ↦ exp_pos (v a)
    have h_one : ∑ a, p a * exp (v a) / ∑ b, p b * exp (v b) = 1 := by
      rw [← sum_div, div_self hZ.ne']
    -- the Gibbs vector attains the bound, since its relative entropy to itself vanishes
    refine ⟨fun a ↦ p a * exp (v a) / ∑ b, p b * exp (v b), mem_simplex_iff.2
      ⟨fun a ↦ div_nonneg (mul_nonneg (hp0 a).le (exp_pos _).le) hZ.le, h_one⟩, ?_⟩
    have h_self (x : ℝ) : x * log (x / x) = 0 := by
      rcases eq_or_ne x 0 with h | h <;> simp [h]
    have h := sum_mul_log_div_mul_exp_div_eq h_one (fun a h ↦ by simp [h]) hZ.ne'
    simp only [h_self, sum_const_zero] at h
    dsimp only
    linarith
  · rintro _ ⟨q, hq, rfl⟩
    exact sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp hp hq (fun a h ↦ absurd h (hp0 a).ne') v

end LMLExplore
