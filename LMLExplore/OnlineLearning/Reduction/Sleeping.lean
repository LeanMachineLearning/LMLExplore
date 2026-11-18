/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Finsupp.Pointwise
public import LMLExplore.OnlineLearning.Learner.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Sleeping experts

In prediction with expert advice with *sleeping experts* [Ora, Section 12.2], only some experts
are active at each round. The experts form a type `ι`, possibly infinite. Before the play of round
`t`, the learner receives *activity weights* `a t : ι →₀ ℝ`, with values in `[0, 1]` and finitely
many nonzero ones: the active experts of round `t` are those of `(a t).support`, and the weight
`a t i` is the confidence of expert `i` in its prediction [Ora, Remark 12.15]. The learner plays a
distribution `x t : ι →₀ ℝ` over the active experts, then the losses `y t : ι → ℝ` of the experts
are revealed and the learner suffers `⟨y t, x t⟩ = ∑ j ∈ (x t).support, x t j * y t j`. The
*sleeping regret* against a weighting `u : ι → ℝ` of the experts
(`sleepingRegret a y x u n`) counts the loss of the learner relative to the loss of expert `i` only
on the rounds where expert `i` is active, weighted by `a t i`:
`∑ t < n, ∑ i ∈ (a t).support, u i * a t i * (⟨y t, x t⟩ - y t i)`. Against the unit vector of
expert `i`, it is `∑ t < n, a t i * (⟨y t, x t⟩ - y t i)` (`sleepingRegret_single`).

The reduction of [Ora, Algorithm 12.2, Theorem 12.13] turns an online linear optimization learner
with plays `z t ≥ 0` on `ι → ℝ` into a sleeping-experts learner:

* the outer play is `sleepingPlay (a t) (z t)`, proportional to the weights `a t i * z t i`, or
  proportional to `a t` when these weights sum to `0`; on rounds with an active expert
  (`a t ≠ 0`), nonnegative weights and inner plays make it a distribution;
* the inner learner receives the linear loss `sleepingSurrogate (a t) (x t) (y t)`, whose
  coordinates are `a t i * (y t i - ⟨y t, x t⟩)` and which is supported by the active experts.

The surrogate loss vanishes at the inner play: `∑ i, a i * (y i - ⟨y, x⟩) * z i = 0` whenever
`a i * z i = (∑ j, a j * z j) * x i` for all `i` (`sum_sleepingSurrogate_mul_eq_zero`). Hence the
sleeping regret against `u` is the linear regret of the inner plays against `u` for the surrogate
losses (`sleepingRegret_eq_regret`). For nonnegative activity weights, inner plays nonnegative on
the active experts and surrogate losses admissible for the inner learner, every regret bound of the
inner learner is therefore a sleeping regret bound. For losses whose range on the active experts
is at most `R`, the coordinates of the surrogate are at most `a t i * R` in absolute value
(`abs_sleepingSurrogate_le`, `abs_sleepingSurrogate_sleepingPlay_le`). The normalization of
nonnegative plays to the simplex [Ora, (12.1)] is the case of finitely many experts, all active
with weight `1` (`regret_eq_regret_sub_of_sum_eq_one`).

The learner `A.sleeping` runs the reduction with an inner learner `A` that receives the activity
weights as contexts (`OnlineLearner.run_sleeping`). Its sleeping regret is the regret of the
closed-loop run of `A` on the surrogate losses (`OnlineLearner.sleepingRegret_run_sleeping`), so a
regret guarantee of `A` against comparators of `U` bounds its sleeping regret against `U`
(`OnlineLearner.HasRegretBound.sleepingRegret_run_sleeping_le`), in particular for losses of range
at most `R` and an inner guarantee for coordinates bounded by `R`
(`OnlineLearner.HasRegretBound.sleepingRegret_run_sleeping_le_of_range`).

## Main definitions

* `LMLExplore.OnlineLearning.sleepingRegret a y x u n`: the sleeping regret.
* `LMLExplore.OnlineLearning.sleepingPlay a z`: the play of the reduction.
* `LMLExplore.OnlineLearning.sleepingSurrogate a x y`: the surrogate loss of the reduction.
* `LMLExplore.OnlineLearning.OnlineLearner.sleeping A`: the sleeping-experts learner built from
  `A`.

## Main statements

* `sleepingRegret_eq_regret` [Ora, Theorem 12.13]: the sleeping regret is the inner linear regret
  for the surrogate losses.
* `abs_sleepingSurrogate_le` [Ora, Theorem 12.13]: the surrogate losses are bounded by the range of
  the active losses.
* `regret_eq_regret_sub_of_sum_eq_one` [Ora, (12.1)]: the normalization to the simplex.
* `OnlineLearner.HasRegretBound.sleepingRegret_run_sleeping_le`: the sleeping regret guarantee of
  `A.sleeping`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Sections 12.1 and 12.2.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {ι : Type*}

section Sequences

/-- The **sleeping regret** [Ora, Section 12.2] after `n` rounds of the distributions `x t` over
the experts, for the activity weights `a t` and the losses `y t` of the experts, against the
weighting `u` of the experts: `∑ t < n, ∑ i ∈ (a t).support, u i * a t i * (⟨y t, x t⟩ - y t i)`,
where `⟨y t, x t⟩ = ∑ j ∈ (x t).support, x t j * y t j` is the loss of the play. Each expert is
compared with the learner only on the rounds where it is active. -/
def sleepingRegret (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) (x : ℕ → ι →₀ ℝ) (u : ι → ℝ) (n : ℕ) :
    ℝ :=
  ∑ t ∈ range n, ∑ i ∈ (a t).support, u i * a t i * (∑ j ∈ (x t).support, x t j * y t j - y t i)

lemma sleepingRegret_def (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) (x : ℕ → ι →₀ ℝ) (u : ι → ℝ)
    (n : ℕ) : sleepingRegret a y x u n = ∑ t ∈ range n, ∑ i ∈ (a t).support,
      u i * a t i * (∑ j ∈ (x t).support, x t j * y t j - y t i) := (rfl)

/-- The sleeping regret against expert `i` is the regret against `i` on the rounds where it is
active, weighted by its activity. -/
lemma sleepingRegret_single [DecidableEq ι] (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) (x : ℕ → ι →₀ ℝ)
    (i : ι) (n : ℕ) : sleepingRegret a y x (Pi.single i 1) n =
      ∑ t ∈ range n, a t i * (∑ j ∈ (x t).support, x t j * y t j - y t i) := by
  rw [sleepingRegret_def]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_eq_single i (fun j _ hj ↦ by simp [hj])
    fun hi ↦ by simp [Finsupp.notMem_support_iff.mp hi]]
  simp

/-- The **surrogate loss** of the sleeping-experts reduction [Ora, Algorithm 12.2]: for the
activity weights `a`, the play `x` and the losses `y` of the experts, the linear loss on `ι → ℝ`
whose coordinates are `a i * (y i - ⟨y, x⟩)` (`sleepingSurrogate_apply`). It is supported by the
active experts (`support_sleepingSurrogate_subset`). -/
noncomputable def sleepingSurrogate (a x : ι →₀ ℝ) (y : ι → ℝ) : ι →₀ ℝ :=
  (fun i ↦ y i - ∑ j ∈ x.support, x j * y j) • a

lemma sleepingSurrogate_def (a x : ι →₀ ℝ) (y : ι → ℝ) :
    sleepingSurrogate a x y = (fun i ↦ y i - ∑ j ∈ x.support, x j * y j) • a := (rfl)

@[simp]
lemma sleepingSurrogate_apply (a x : ι →₀ ℝ) (y : ι → ℝ) (i : ι) :
    sleepingSurrogate a x y i = a i * (y i - ∑ j ∈ x.support, x j * y j) := by
  simp [sleepingSurrogate_def, mul_comm]

lemma support_sleepingSurrogate_subset (a x : ι →₀ ℝ) (y : ι → ℝ) :
    (sleepingSurrogate a x y).support ⊆ a.support := fun i hi ↦ by
  rw [Finsupp.mem_support_iff, sleepingSurrogate_apply] at hi
  exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hi)

/-- The surrogate linear loss of `w`, written as a sum over the active experts. -/
lemma sum_sleepingSurrogate_mul (a x : ι →₀ ℝ) (y w : ι → ℝ) :
    ∑ i ∈ (sleepingSurrogate a x y).support, sleepingSurrogate a x y i * w i =
      ∑ i ∈ a.support, a i * (y i - ∑ j ∈ x.support, x j * y j) * w i := by
  rw [sum_subset (support_sleepingSurrogate_subset a x y)
    fun i _ hi ↦ by rw [Finsupp.notMem_support_iff.mp hi, zero_mul]]
  simp only [sleepingSurrogate_apply]

/-- **The surrogate loss vanishes at the inner play** [Ora, Theorem 12.13]. If the play `x` is
the distribution proportional to the weights `a i * z i`, in the sense that
`a i * z i = (∑ j, a j * z j) * x i` for every expert `i` (which forces `a i * z i = 0` when the
weights sum to `0`), then the surrogate linear loss of the inner play `z` is `0`. -/
theorem sum_sleepingSurrogate_mul_eq_zero {a x : ι →₀ ℝ} {z : ι → ℝ} (y : ι → ℝ)
    (hx : ∀ i, a i * z i = (∑ j ∈ a.support, a j * z j) * x i) :
    ∑ i ∈ (sleepingSurrogate a x y).support, sleepingSurrogate a x y i * z i = 0 := by
  rw [sum_sleepingSurrogate_mul]
  set S := ∑ j ∈ a.support, a j * z j with hSdef
  set p := ∑ j ∈ x.support, x j * y j
  have h : ∀ i, a i * (y i - p) * z i = S * (x i * y i) - p * (a i * z i) := fun i ↦ by
    linear_combination y i * hx i
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, ← hSdef]
  rcases eq_or_ne S 0 with hS | hS
  · simp [hS]
  -- When `S ≠ 0`, the play is supported by the active experts, so its loss is a sum over them.
  have hsub : x.support ⊆ a.support := fun i hi ↦ by
    refine Finsupp.mem_support_iff.mpr fun hai ↦ Finsupp.mem_support_iff.mp hi ?_
    have := hx i
    rw [hai, zero_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hS
  rw [← sum_subset hsub fun i _ hi ↦ by rw [Finsupp.notMem_support_iff.mp hi, zero_mul]]
  ring

/-- **Sleeping regret through surrogate losses** [Ora, Theorem 12.13]. If at each round `t < n`
the play `x t` is the distribution proportional to the weights `a t i * z t i` of the inner plays
`z t`, then for every weighting `u` of the experts, the sleeping regret of the plays `x t` against
`u` is the linear regret of the inner plays `z t` against `u` for the surrogate losses
`sleepingSurrogate (a t) (x t) (y t)`. -/
theorem sleepingRegret_eq_regret (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) (x : ℕ → ι →₀ ℝ)
    (z : ℕ → ι → ℝ) {n : ℕ}
    (hx : ∀ t < n, ∀ i, a t i * z t i = (∑ j ∈ (a t).support, a t j * z t j) * x t i)
    (u : ι → ℝ) :
    sleepingRegret a y x u n = regret (fun t w ↦
      ∑ i ∈ (sleepingSurrogate (a t) (x t) (y t)).support,
        sleepingSurrogate (a t) (x t) (y t) i * w i) z u n := by
  rw [sleepingRegret_def, regret_def]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [sum_sleepingSurrogate_mul_eq_zero (y t) (hx t (mem_range.mp ht)), zero_sub,
    sum_sleepingSurrogate_mul, ← sum_neg_distrib]
  exact sum_congr rfl fun i _ ↦ by ring

/-- **The range of the surrogate losses** [Ora, Theorem 12.13]. Let the play `x` be a
distribution over the active experts, and let the losses of the active experts have range at
most `R`. Then the coordinate `i` of the surrogate loss is at most `a i * R` in absolute value. -/
theorem abs_sleepingSurrogate_le {a x : ι →₀ ℝ} {y : ι → ℝ} {R : ℝ} (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, 0 ≤ x i) (hx₁ : ∑ i ∈ a.support, x i = 1) (hxa : x.support ⊆ a.support)
    (hR : ∀ i ∈ a.support, ∀ j ∈ a.support, y i - y j ≤ R) (i : ι) :
    |sleepingSurrogate a x y i| ≤ a i * R := by
  rw [sleepingSurrogate_apply, abs_mul, abs_of_nonneg (ha i)]
  by_cases hi : i ∈ a.support
  swap
  · simp [Finsupp.notMem_support_iff.mp hi]
  refine mul_le_mul_of_nonneg_left ?_ (ha i)
  -- `y i - ⟨y, x⟩` is the average of the differences `y i - y j` over the active experts `j`.
  have hp : y i - ∑ j ∈ x.support, x j * y j = ∑ j ∈ a.support, x j * (y i - y j) := by
    rw [sum_subset hxa fun j _ hj ↦ by rw [Finsupp.notMem_support_iff.mp hj, zero_mul]]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hx₁, one_mul]
  rw [hp]
  calc |∑ j ∈ a.support, x j * (y i - y j)| ≤ ∑ j ∈ a.support, |x j * (y i - y j)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ a.support, x j * R := sum_le_sum fun j hj ↦ by
        rw [abs_mul, abs_of_nonneg (hx j)]
        exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.mpr ⟨hR i hi j hj, hR j hj i hi⟩) (hx j)
    _ = R := by rw [← sum_mul, hx₁, one_mul]

/-- The **play of the sleeping-experts reduction** [Ora, Algorithm 12.2] for the activity weights
`a` and the inner play `z`: the weights `a i * z i` normalized by their sum when it is not `0`, and
`a` normalized by its sum otherwise (this is `0` when no expert is active, `a = 0`). When some
expert is active (`a ≠ 0`), for nonnegative weights and nonnegative inner plays on the active
experts, it is a distribution over the active experts (`sleepingPlay_nonneg`, `sum_sleepingPlay`,
`support_sleepingPlay_subset`). -/
noncomputable def sleepingPlay (a : ι →₀ ℝ) (z : ι → ℝ) : ι →₀ ℝ :=
  if ∑ i ∈ a.support, a i * z i = 0 then (∑ i ∈ a.support, a i)⁻¹ • a
  else (∑ i ∈ a.support, a i * z i)⁻¹ • (z • a)

lemma sleepingPlay_def (a : ι →₀ ℝ) (z : ι → ℝ) : sleepingPlay a z =
    if ∑ i ∈ a.support, a i * z i = 0 then (∑ i ∈ a.support, a i)⁻¹ • a
    else (∑ i ∈ a.support, a i * z i)⁻¹ • (z • a) := (rfl)

lemma sleepingPlay_apply_of_sum_eq_zero {a : ι →₀ ℝ} {z : ι → ℝ}
    (h : ∑ i ∈ a.support, a i * z i = 0) (i : ι) :
    sleepingPlay a z i = (∑ j ∈ a.support, a j)⁻¹ * a i := by
  simp [sleepingPlay_def, h]

lemma sleepingPlay_apply_of_sum_ne_zero {a : ι →₀ ℝ} {z : ι → ℝ}
    (h : ∑ i ∈ a.support, a i * z i ≠ 0) (i : ι) :
    sleepingPlay a z i = (∑ j ∈ a.support, a j * z j)⁻¹ * (a i * z i) := by
  simp [sleepingPlay_def, h, mul_comm (z i)]

/-- The play of the reduction vanishes on the inactive experts. -/
lemma sleepingPlay_apply_of_notMem {a : ι →₀ ℝ} {i : ι} (hi : i ∉ a.support) (z : ι → ℝ) :
    sleepingPlay a z i = 0 := by
  have hai := Finsupp.notMem_support_iff.mp hi
  by_cases h : ∑ i ∈ a.support, a i * z i = 0
  · simp [sleepingPlay_apply_of_sum_eq_zero h, hai]
  · simp [sleepingPlay_apply_of_sum_ne_zero h, hai]

lemma support_sleepingPlay_subset (a : ι →₀ ℝ) (z : ι → ℝ) :
    (sleepingPlay a z).support ⊆ a.support := fun i hi ↦ by
  by_contra h
  exact Finsupp.mem_support_iff.mp hi (sleepingPlay_apply_of_notMem h z)

/-- The play of the reduction is proportional to the weights `a i * z i`: for nonnegative weights
and inner plays nonnegative on the active experts, `a i * z i = (∑ j, a j * z j) * x i`, the
hypothesis of `sleepingRegret_eq_regret`. -/
lemma mul_eq_sum_mul_sleepingPlay {a : ι →₀ ℝ} {z : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i ∈ a.support, 0 ≤ z i) (i : ι) :
    a i * z i = (∑ j ∈ a.support, a j * z j) * sleepingPlay a z i := by
  by_cases h : ∑ j ∈ a.support, a j * z j = 0
  · rw [h, zero_mul]
    by_cases hi : i ∈ a.support
    · exact (sum_eq_zero_iff_of_nonneg fun j hj ↦ mul_nonneg (ha j) (hz j hj)).mp h i hi
    · rw [Finsupp.notMem_support_iff.mp hi, zero_mul]
  · rw [sleepingPlay_apply_of_sum_ne_zero h, mul_inv_cancel_left₀ h]

lemma sleepingPlay_nonneg {a : ι →₀ ℝ} {z : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i ∈ a.support, 0 ≤ z i) (i : ι) : 0 ≤ sleepingPlay a z i := by
  by_cases hi : i ∈ a.support
  swap
  · rw [sleepingPlay_apply_of_notMem hi]
  by_cases h : ∑ j ∈ a.support, a j * z j = 0
  · rw [sleepingPlay_apply_of_sum_eq_zero h]
    exact mul_nonneg (inv_nonneg.mpr (sum_nonneg fun j _ ↦ ha j)) (ha i)
  · rw [sleepingPlay_apply_of_sum_ne_zero h]
    exact mul_nonneg (inv_nonneg.mpr (sum_nonneg fun j hj ↦ mul_nonneg (ha j) (hz j hj)))
      (mul_nonneg (ha i) (hz i hi))

/-- For nonnegative activity weights, not all zero, the play of the reduction sums to `1`. -/
lemma sum_sleepingPlay {a : ι →₀ ℝ} (ha : ∀ i, 0 ≤ a i) (ha₀ : a ≠ 0) (z : ι → ℝ) :
    ∑ i ∈ a.support, sleepingPlay a z i = 1 := by
  by_cases h : ∑ j ∈ a.support, a j * z j = 0
  · simp_rw [sleepingPlay_apply_of_sum_eq_zero h, ← mul_sum]
    refine inv_mul_cancel₀ (sum_pos (fun i hi ↦ ?_) (Finsupp.support_nonempty_iff.mpr ha₀)).ne'
    exact (ha i).lt_of_ne' (Finsupp.mem_support_iff.mp hi)
  · simp_rw [sleepingPlay_apply_of_sum_ne_zero h, ← mul_sum]
    exact inv_mul_cancel₀ h

/-- **The range of the surrogate losses of the reduction** [Ora, Theorem 12.13]. For activity
weights `a ≥ 0`, inner plays nonnegative on the active experts, and losses of range at most `R` on
the active experts, the coordinate `i` of the surrogate loss of the play of the reduction is at
most `a i * R` in absolute value. -/
theorem abs_sleepingSurrogate_sleepingPlay_le {a : ι →₀ ℝ} {z y : ι → ℝ} {R : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hz : ∀ i ∈ a.support, 0 ≤ z i)
    (hR : ∀ i ∈ a.support, ∀ j ∈ a.support, y i - y j ≤ R) (i : ι) :
    |sleepingSurrogate a (sleepingPlay a z) y i| ≤ a i * R := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp
  exact abs_sleepingSurrogate_le ha (sleepingPlay_nonneg ha hz) (sum_sleepingPlay ha ha₀ z)
    (support_sleepingPlay_subset a z) hR i

/-- **Normalization to the simplex** [Ora, (12.1)], the case of the sleeping-experts reduction
where finitely many experts are all active with weight `1`. If the plays `x t` are the
normalizations of the inner plays `z t`, in the sense that `z t i = (∑ j, z t j) * x t i`, then
for every `u` whose coordinates sum to `1` (in particular every `u` in the simplex), the linear
regret of the plays `x t` against `u` for the losses `y t` is the linear regret of the inner plays
`z t` against `u` for the losses `y t - ⟨y t, x t⟩`. -/
theorem regret_eq_regret_sub_of_sum_eq_one [Fintype ι] (y x z : ℕ → ι → ℝ) {n : ℕ}
    (hx : ∀ t < n, ∀ i, z t i = (∑ j, z t j) * x t i) {u : ι → ℝ} (hu : ∑ i, u i = 1) :
    regret (fun t w ↦ ∑ i, w i * y t i) x u n =
      regret (fun t w ↦ ∑ i, (y t i - ∑ j, x t j * y t j) * w i) z u n := by
  classical
  -- All the experts are active with weight `1`, and the plays are the distributions `x t`.
  set a : ℕ → ι →₀ ℝ := fun _ ↦ Finsupp.equivFunOnFinite.symm 1
  set X : ℕ → ι →₀ ℝ := fun t ↦ Finsupp.equivFunOnFinite.symm (x t)
  have hsum (f : ι →₀ ℝ) (g : ι → ℝ) : ∑ i ∈ f.support, f i * g i = ∑ i, f i * g i :=
    f.sum_fintype (fun i r ↦ r * g i) fun _ ↦ zero_mul _
  have hsupp (t : ℕ) : (a t).support = univ := by
    ext i
    simp [a]
  have hX (t : ℕ) (g : ι → ℝ) : ∑ j ∈ (X t).support, X t j * g j = ∑ j, x t j * g j := by
    rw [hsum]
    simp only [X, Finsupp.coe_equivFunOnFinite_symm]
  have h := sleepingRegret_eq_regret a y X z (n := n) (fun t ht i ↦ by
    simpa [hsupp, a, X] using hx t ht i) u
  simp only [sleepingRegret_def, regret_def, sum_sleepingSurrogate_mul, hsupp, hX] at h
  simp only [a, Finsupp.coe_equivFunOnFinite_symm, Pi.one_apply, mul_one, one_mul] at h
  rw [regret_def, regret_def, ← h]
  refine sum_congr rfl fun t _ ↦ ?_
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hu, one_mul]

end Sequences

namespace OnlineLearner

section Learner

variable (A : OnlineLearner (ι →₀ ℝ) (ι →₀ ℝ) (ι → ℝ))

/-- The **sleeping-experts learner** [Ora, Algorithm 12.2] built from a learner `A` with plays in
`ι → ℝ`, linear losses in `ι →₀ ℝ` and the activity weights as contexts. At round `t`, `A` plays
`z t`, the learner plays `sleepingPlay (a t) (z t)`, and after the losses `y t` of the experts are
revealed, `A` receives the surrogate loss `sleepingSurrogate (a t) (x t) (y t)` of the play
`x t` (`run_sleeping`). It is the black-box reduction to `A.withContext`, whose output map and
surrogate read the activity weights. -/
noncomputable def sleeping : OnlineLearner (ι →₀ ℝ) (ι → ℝ) (ι →₀ ℝ) :=
  A.withContext.reduce (fun p ↦ sleepingPlay p.1 p.2)
    fun p y ↦ sleepingSurrogate p.1 (sleepingPlay p.1 p.2) y

lemma sleeping_def : A.sleeping = A.withContext.reduce (fun p ↦ sleepingPlay p.1 p.2)
    fun p y ↦ sleepingSurrogate p.1 (sleepingPlay p.1 p.2) y := (rfl)

/-- The plays of `A.sleeping` are the plays of the reduction for the plays of the closed-loop run
of `A` fed the surrogate losses. -/
@[simp]
lemma run_sleeping (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) (t : ℕ) :
    A.sleeping.run a y t = sleepingPlay (a t) (A.run a (A.closedLoopFeedback a
      fun s z ↦ sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) t) := by
  rw [sleeping_def, run_reduce, closedLoopFeedback_withContext, run_withContext]

/-- The feedback of `A` inside `A.sleeping` is the surrogate loss of the play of the learner. -/
lemma closedLoopFeedback_eq_sleepingSurrogate_run_sleeping (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ)
    (t : ℕ) :
    A.closedLoopFeedback a (fun s z ↦ sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) t =
      sleepingSurrogate (a t) (A.sleeping.run a y t) (y t) := by
  rw [closedLoopFeedback_eq, run_sleeping]

/-- **Sleeping regret of `A.sleeping`** [Ora, Theorem 12.13]. For nonnegative activity weights
and plays of `A` nonnegative on the active experts, the sleeping regret of `A.sleeping` against
every `u` is the linear regret against `u` of the closed-loop run of `A` on the surrogate
losses. -/
theorem sleepingRegret_run_sleeping (a : ℕ → ι →₀ ℝ) (y : ℕ → ι → ℝ) {n : ℕ}
    (ha : ∀ t < n, ∀ i, 0 ≤ a t i)
    (hz : ∀ t < n, ∀ i ∈ (a t).support, 0 ≤ A.run a (A.closedLoopFeedback a
      fun s z ↦ sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) t i) (u : ι → ℝ) :
    sleepingRegret a y (A.sleeping.run a y) u n =
      regret (fun t w ↦ ∑ i ∈ (A.closedLoopFeedback a (fun s z ↦
          sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) t).support,
        A.closedLoopFeedback a (fun s z ↦
          sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) t i * w i)
        (A.run a (A.closedLoopFeedback a fun s z ↦
          sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s))) u n := by
  simp_rw [closedLoopFeedback_eq_sleepingSurrogate_run_sleeping]
  refine sleepingRegret_eq_regret a y _ _ (fun t ht i ↦ ?_) u
  rw [run_sleeping]
  exact mul_eq_sum_mul_sleepingPlay (ha t ht) (hz t ht) i

variable {A} {adm : (ι →₀ ℝ) → (ι →₀ ℝ) → Prop} {U : Set (ι → ℝ)}
  {B : ℕ → (ℕ → ι →₀ ℝ) → (ℕ → ι →₀ ℝ) → (ι → ℝ) → ℝ}

/-- **Sleeping regret guarantee of `A.sleeping`** [Ora, Theorem 12.13]. Let `A` have the regret
bound `B` for linear losses against the comparators of `U`, with plays nonnegative on the active
experts. If the activity weights are nonnegative and the surrogate losses of the rounds `t < n`
are admissible for `A`, then the sleeping regret of `A.sleeping` against every `u ∈ U` is at most
`B` at the surrogate losses fed to `A`. -/
theorem HasRegretBound.sleepingRegret_run_sleeping_le
    (hA : A.HasRegretBound (fun g w ↦ ∑ i ∈ g.support, g i * w i) adm U B)
    (hpos : ∀ (c : ℕ → ι →₀ ℝ) (g : ℕ → ι →₀ ℝ) (t : ℕ), ∀ i ∈ (c t).support, 0 ≤ A.run c g t i)
    {a : ℕ → ι →₀ ℝ} {y : ℕ → ι → ℝ} {n : ℕ} (ha : ∀ t < n, ∀ i, 0 ≤ a t i)
    (hadm : ∀ t < n, ∀ z : ι → ℝ, (∀ i ∈ (a t).support, 0 ≤ z i) →
      adm (a t) (sleepingSurrogate (a t) (sleepingPlay (a t) z) (y t)))
    {u : ι → ℝ} (hu : u ∈ U) :
    sleepingRegret a y (A.sleeping.run a y) u n ≤
      B n a (A.closedLoopFeedback a fun s z ↦
        sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) u := by
  rw [A.sleepingRegret_run_sleeping a y ha (fun t _ ↦ hpos _ _ t) u]
  refine hA.regret_le (fun t ht ↦ ?_) hu
  rw [closedLoopFeedback_eq]
  exact hadm t ht _ (hpos _ _ t)

/-- **Sleeping regret guarantee of `A.sleeping` for bounded ranges** [Ora, Theorem 12.13]. Let `A`
have the regret bound `B` for linear losses with coordinates in `[-R, R]` against the comparators
of `U`, with plays nonnegative on the active experts. For activity weights in `[0, 1]` and losses
of range at most `R` on the active experts, the sleeping regret of `A.sleeping` against every
`u ∈ U` is at most `B` at the surrogate losses fed to `A`. -/
theorem HasRegretBound.sleepingRegret_run_sleeping_le_of_range {R : ℝ} (hR₀ : 0 ≤ R)
    (hA : A.HasRegretBound (fun g w ↦ ∑ i ∈ g.support, g i * w i) (fun _ g ↦ ∀ i, |g i| ≤ R) U B)
    (hpos : ∀ (c : ℕ → ι →₀ ℝ) (g : ℕ → ι →₀ ℝ) (t : ℕ), ∀ i ∈ (c t).support, 0 ≤ A.run c g t i)
    {a : ℕ → ι →₀ ℝ} {y : ℕ → ι → ℝ} {n : ℕ} (ha : ∀ t < n, ∀ i, 0 ≤ a t i ∧ a t i ≤ 1)
    (hR : ∀ t < n, ∀ i ∈ (a t).support, ∀ j ∈ (a t).support, y t i - y t j ≤ R)
    {u : ι → ℝ} (hu : u ∈ U) :
    sleepingRegret a y (A.sleeping.run a y) u n ≤
      B n a (A.closedLoopFeedback a fun s z ↦
        sleepingSurrogate (a s) (sleepingPlay (a s) z) (y s)) u := by
  refine hA.sleepingRegret_run_sleeping_le hpos (fun t ht i ↦ (ha t ht i).1)
    (fun t ht z hz i ↦ ?_) hu
  exact (abs_sleepingSurrogate_sleepingPlay_le (fun i ↦ (ha t ht i).1) hz (hR t ht) i).trans
    (mul_le_of_le_one_left hR₀ (ha t ht i).2)

end Learner

end OnlineLearner

end LMLExplore.OnlineLearning
