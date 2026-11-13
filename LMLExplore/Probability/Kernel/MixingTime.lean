/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Kernel.Dobrushin
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mixing times of Markov kernels

For a Markov kernel `κ : Kernel α α` and a probability measure `π` (in the statements below, an
invariant one), the *distance to stationarity* at time `t` is
`d(t) = ⨆ x, tvDist ((κ ^ t) x) π / 2`, and the *mixing time* at level `ε` is
`t_mix(ε) = inf {t | d(t) ≤ ε}`, a value in `ℕ∞` that is `⊤` when no time works.

The distance to stationarity is nonincreasing in time and is comparable to the Dobrushin
coefficient of the `t`-step kernel: `d(t) ≤ δ(κ ^ t) ≤ 2 * d(t)`. The submultiplicativity of the
Dobrushin coefficient then gives `d((ℓ + 1) * s) ≤ d(s) * (2 * d(s)) ^ ℓ`, from which the two
standard consequences of a finite mixing time `t_mix(1/4)` follow:
* `t_mix(ε) ≤ ⌈log₂ (1 / ε)⌉ * t_mix(1/4)` for every `ε > 0`;
* `tvDist ((κ ^ t) x) π ≤ 2⁻¹ ^ ⌊t / t_mix(1/4)⌋` for every `t ≥ t_mix(1/4)`.

These quantify the convergence to equilibrium of Markov chains, and they are the form in which
the mixing of the state chains of Markov decision processes enters the comparison of discounted
and average rewards and the analysis of temporal-difference learning along a trajectory.

## Main definitions

* `ProbabilityTheory.Kernel.distToStationary κ π t`: the distance to stationarity
  `⨆ x, tvDist ((κ ^ t) x) π / 2`.
* `ProbabilityTheory.Kernel.mixingTime κ π ε`: the mixing time `⨅ t, ⨅ (_ : d(t) ≤ ε), t` in
  `ℕ∞`.

## Main statements

* `ProbabilityTheory.Kernel.distToStationary_le_dobrushinCoeff`,
  `ProbabilityTheory.Kernel.dobrushinCoeff_le_two_mul_distToStationary`:
  `d(t) ≤ δ(κ ^ t) ≤ 2 * d(t)`.
* `ProbabilityTheory.Kernel.antitone_distToStationary`: `d` is nonincreasing.
* `ProbabilityTheory.Kernel.distToStationary_succ_mul_le`:
  `d((ℓ + 1) * s) ≤ d(s) * (2 * d(s)) ^ ℓ`.
* `ProbabilityTheory.Kernel.mixingTime_le_iff`: `t_mix(ε) ≤ t ↔ d(t) ≤ ε`.
* `ProbabilityTheory.Kernel.mixingTime_le_ceil_logb_mul`:
  `t_mix(ε) ≤ ⌈log₂ ε⁻¹⌉ * t_mix(1/4)`.
* `ProbabilityTheory.Kernel.tvDist_pow_apply_le_inv_two_pow_div_mixingTime`: geometric
  convergence at the rate `2⁻¹` per mixing time `t_mix(1/4)`.
* `ProbabilityTheory.Kernel.mixingTime_lt_top_of_dobrushinCoeff_pow_lt_one`: a kernel with
  `δ(κ ^ m) < 1` has finite mixing times at every positive level.

## References

* [D. A. Levin, Y. Peres and E. L. Wilmer, *Markov chains and mixing times*, 2nd edition,
  2017][LPW17], §§4.4–4.5: (4.22), (4.30), Lemmas 4.10–4.11 and (4.29)–(4.34)
* [Y. Jin and A. Sidford, *Towards tight bounds on the sample complexity of average-reward
  MDPs*, 2021][JS21], Lemma 1
-/

public section

open MeasureTheory Set Filter

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {π : Measure α}

/-! ### The distance to stationarity -/

/-- The *distance to stationarity* `d(t) = ⨆ x, tvDist ((κ ^ t) x) π / 2` of a kernel `κ` from a
measure `π` at time `t`. For a Markov kernel and an invariant probability measure `π`, it is
nonincreasing in `t` (`antitone_distToStationary`) and lies between `δ(κ ^ t) / 2` and
`δ(κ ^ t)` (`dobrushinCoeff_le_two_mul_distToStationary`,
`distToStationary_le_dobrushinCoeff`). -/
noncomputable def distToStationary (κ : Kernel α α) (π : Measure α) (t : ℕ) : ℝ :=
  ⨆ x, tvDist ((κ ^ t) x) π / 2

lemma distToStationary_def (κ : Kernel α α) (π : Measure α) (t : ℕ) :
    distToStationary κ π t = ⨆ x, tvDist ((κ ^ t) x) π / 2 :=
  (rfl)

/-- The distance to stationarity is nonnegative. -/
lemma distToStationary_nonneg (κ : Kernel α α) (π : Measure α) (t : ℕ) :
    0 ≤ distToStationary κ π t :=
  Real.iSup_nonneg fun _ ↦ div_nonneg tvDist_nonneg zero_le_two

/-- A bound `c ≥ 0` on the total variation distances `tvDist ((κ ^ t) x) π / 2` bounds the
distance to stationarity. -/
lemma distToStationary_le {c : ℝ} {t : ℕ} (hc : 0 ≤ c)
    (h : ∀ x, tvDist ((κ ^ t) x) π ≤ 2 * c) :
    distToStationary κ π t ≤ c :=
  Real.iSup_le (fun x ↦ by linarith [h x]) hc

section Markov

variable [IsMarkovKernel κ] [IsProbabilityMeasure π]

/-- The `t`-step law from any starting point is within twice the distance to stationarity of
`π`. -/
lemma tvDist_pow_apply_le_two_mul_distToStationary (t : ℕ) (x : α) :
    tvDist ((κ ^ t) x) π ≤ 2 * distToStationary κ π t := by
  have hbdd : BddAbove (range fun x ↦ tvDist ((κ ^ t) x) π / 2) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    linarith [tvDist_le_two (μ := (κ ^ t) y) (ν := π)]
  have := le_ciSup hbdd x
  rw [← distToStationary_def] at this
  linarith

/-- `d(t) ≤ c` if and only if `tvDist ((κ ^ t) x) π ≤ 2 * c` for every `x`, for every
`c ≥ 0`. -/
lemma distToStationary_le_iff {c : ℝ} {t : ℕ} (hc : 0 ≤ c) :
    distToStationary κ π t ≤ c ↔ ∀ x, tvDist ((κ ^ t) x) π ≤ 2 * c :=
  ⟨fun h x ↦ (tvDist_pow_apply_le_two_mul_distToStationary t x).trans (by linarith),
    distToStationary_le hc⟩

/-- The distance to stationarity is at most one. -/
lemma distToStationary_le_one (t : ℕ) : distToStationary κ π t ≤ 1 :=
  distToStationary_le zero_le_one fun x ↦ by simpa using tvDist_le_two (μ := (κ ^ t) x) (ν := π)

/-- `δ(κ ^ t) ≤ 2 * d(t)`: two `t`-step laws are close when both are close to `π`. -/
theorem dobrushinCoeff_le_two_mul_distToStationary (t : ℕ) :
    dobrushinCoeff (κ ^ t) ≤ 2 * distToStationary κ π t := by
  refine dobrushinCoeff_le (by linarith [distToStationary_nonneg κ π t]) fun x y ↦ ?_
  have := tvDist_triangle ((κ ^ t) x) π ((κ ^ t) y)
  rw [tvDist_comm π] at this
  linarith [tvDist_pow_apply_le_two_mul_distToStationary (κ := κ) (π := π) t x,
    tvDist_pow_apply_le_two_mul_distToStationary (κ := κ) (π := π) t y]

variable (hπ : κ.Invariant π)
include hπ

/-- `d(t) ≤ δ(κ ^ t)` for an invariant probability measure `π`. -/
theorem distToStationary_le_dobrushinCoeff (t : ℕ) :
    distToStationary κ π t ≤ dobrushinCoeff (κ ^ t) :=
  distToStationary_le (dobrushinCoeff_nonneg _) (tvDist_pow_apply_le_two_mul_dobrushinCoeff hπ t)

/-- `d(t + s) ≤ δ(κ ^ t) * d(s)` for an invariant probability measure `π`. -/
theorem distToStationary_add_le (t s : ℕ) :
    distToStationary κ π (t + s) ≤ dobrushinCoeff (κ ^ t) * distToStationary κ π s := by
  refine distToStationary_le
    (mul_nonneg (dobrushinCoeff_nonneg _) (distToStationary_nonneg _ _ _)) fun x ↦ ?_
  -- `(κ ^ (t + s)) x = κ ^ t ∘ₘ (κ ^ s) x` and `π = κ ^ t ∘ₘ π`
  have h := tvDist_comp_right_le_dobrushinCoeff_mul (μ := (κ ^ s) x) (ν := π) (by simp) (κ ^ t)
  rw [(hπ.pow t).def, ← comp_apply, ← Kernel.pow_add] at h
  have := tvDist_pow_apply_le_two_mul_distToStationary (κ := κ) (π := π) s x
  nlinarith [dobrushinCoeff_nonneg (κ ^ t)]

/-- The distance to stationarity from an invariant probability measure is nonincreasing. -/
theorem antitone_distToStationary : Antitone (distToStationary κ π) := by
  refine antitone_nat_of_succ_le fun t ↦ ?_
  rw [add_comm]
  exact (distToStationary_add_le hπ 1 t).trans
    (mul_le_of_le_one_left (distToStationary_nonneg _ _ _) dobrushinCoeff_le_one)

/-- `d((ℓ + 1) * s) ≤ d(s) * (2 * d(s)) ^ ℓ` for an invariant probability measure `π`. -/
theorem distToStationary_succ_mul_le (ℓ s : ℕ) :
    distToStationary κ π ((ℓ + 1) * s) ≤
      distToStationary κ π s * (2 * distToStationary κ π s) ^ ℓ := by
  have h := distToStationary_add_le hπ (s * ℓ) s
  rw [show s * ℓ + s = (ℓ + 1) * s by ring, pow_mul] at h
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  · exact distToStationary_nonneg _ _ _
  · exact (dobrushinCoeff_pow_le _ _).trans (pow_le_pow_left₀ (dobrushinCoeff_nonneg _)
      (dobrushinCoeff_le_two_mul_distToStationary s) ℓ)

/-- If `d(s) ≤ 1 / 4`, then `d(ℓ * s) ≤ 2⁻¹ ^ (ℓ + 1)` for every `ℓ ≥ 1`. -/
theorem distToStationary_mul_le_inv_two_pow {s : ℕ} (hs : distToStationary κ π s ≤ 1 / 4)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    distToStationary κ π (ℓ * s) ≤ 2⁻¹ ^ (ℓ + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ
  have h0 := distToStationary_nonneg κ π s
  refine (distToStationary_succ_mul_le hπ k s).trans ?_
  calc distToStationary κ π s * (2 * distToStationary κ π s) ^ k
      ≤ 1 / 4 * (1 / 2) ^ k := by gcongr; linarith
    _ = 2⁻¹ ^ (k + 1 + 1) := by rw [pow_succ, pow_succ]; ring

/-- **Geometric convergence**: if `d(s) ≤ 1 / 4` and `s ≤ t`, then
`tvDist ((κ ^ t) x) π ≤ 2⁻¹ ^ (t / s)`. -/
theorem tvDist_pow_apply_le_inv_two_pow_div {s t : ℕ} (hs : distToStationary κ π s ≤ 1 / 4)
    (hst : s ≤ t) (x : α) :
    tvDist ((κ ^ t) x) π ≤ 2⁻¹ ^ (t / s) := by
  refine (tvDist_pow_apply_le_two_mul_distToStationary t x).trans ?_
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · -- `d(t) ≤ d(0) ≤ 1 / 4`
    have := antitone_distToStationary hπ (Nat.zero_le t)
    rw [Nat.div_zero, _root_.pow_zero]
    linarith
  · -- `d(t) ≤ d((t / s) * s) ≤ 2⁻¹ ^ (t / s + 1)`
    have hℓ : t / s ≠ 0 := (Nat.div_pos hst hs0).ne'
    have := (antitone_distToStationary hπ (Nat.div_mul_le_self t s)).trans
      (distToStationary_mul_le_inv_two_pow hπ hs hℓ)
    rw [pow_succ] at this
    linarith

end Markov

/-! ### Mixing times -/

/-- The *mixing time* `t_mix(ε) = inf {t | d(t) ≤ ε}` of a kernel `κ` from a measure `π` at level
`ε`, in `ℕ∞`: it is `⊤` when `d(t) > ε` for every `t` (`mixingTime_eq_top_iff`). For a Markov
kernel and an invariant probability measure, `t_mix(ε) ≤ t ↔ d(t) ≤ ε` (`mixingTime_le_iff`). -/
noncomputable def mixingTime (κ : Kernel α α) (π : Measure α) (ε : ℝ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : distToStationary κ π t ≤ ε), (t : ℕ∞)

lemma mixingTime_def (κ : Kernel α α) (π : Measure α) (ε : ℝ) :
    mixingTime κ π ε = ⨅ (t : ℕ) (_ : distToStationary κ π t ≤ ε), (t : ℕ∞) :=
  (rfl)

/-- A time at which the distance to stationarity is at most `ε` bounds the mixing time. -/
lemma mixingTime_le_of_distToStationary_le {ε : ℝ} {t : ℕ} (h : distToStationary κ π t ≤ ε) :
    mixingTime κ π ε ≤ t :=
  iInf₂_le t h

/-- The mixing time is infinite if and only if the distance to stationarity exceeds `ε` at every
time. -/
lemma mixingTime_eq_top_iff {ε : ℝ} : mixingTime κ π ε = ⊤ ↔ ∀ t, ε < distToStationary κ π t := by
  simp [mixingTime_def, iInf_eq_top]

/-- The mixing time is nonincreasing in the level. -/
lemma mixingTime_anti {ε ε' : ℝ} (h : ε ≤ ε') : mixingTime κ π ε' ≤ mixingTime κ π ε :=
  le_iInf₂ fun _ ht ↦ mixingTime_le_of_distToStationary_le (ht.trans h)

/-- At a finite mixing time `s = t_mix(ε)`, the distance to stationarity is at most `ε`: the
infimum defining the mixing time is attained. -/
lemma distToStationary_le_of_mixingTime_eq {ε : ℝ} {s : ℕ} (hs : mixingTime κ π ε = s) :
    distToStationary κ π s ≤ ε := by
  rw [mixingTime_def, iInf_subtype'] at hs
  obtain ⟨⟨⟨t, ht⟩, h⟩, -⟩ := ENat.iInf_eq_natCast_iff.1 hs
  exact Nat.cast_injective h ▸ ht

variable [IsMarkovKernel κ] [IsProbabilityMeasure π]

/-- For a Markov kernel and an invariant probability measure, `t_mix(ε) ≤ t` if and only if
`d(t) ≤ ε`. -/
theorem mixingTime_le_iff (hπ : κ.Invariant π) {ε : ℝ} {t : ℕ} :
    mixingTime κ π ε ≤ t ↔ distToStationary κ π t ≤ ε := by
  refine ⟨fun h ↦ ?_, mixingTime_le_of_distToStationary_le⟩
  -- the mixing time is a finite `s ≤ t` with `d(s) ≤ ε`, and `d` is nonincreasing
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 (h.trans_lt (ENat.natCast_lt_top t)).ne
  exact (antitone_distToStationary hπ (by exact_mod_cast hs ▸ h)).trans
    (distToStationary_le_of_mixingTime_eq hs.symm)

/-- `t_mix(ε) ≤ ⌈log₂ ε⁻¹⌉ * t_mix(1/4)` for every `ε > 0`. -/
theorem mixingTime_le_ceil_logb_mul (hπ : κ.Invariant π) {ε : ℝ} (hε : 0 < ε) :
    mixingTime κ π ε ≤ ⌈Real.logb 2 ε⁻¹⌉₊ * mixingTime κ π (1 / 4) := by
  set ℓ := ⌈Real.logb 2 ε⁻¹⌉₊
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  · -- `ε ≥ 1`, and `d(0) ≤ 1 ≤ ε`
    rw [hℓ, Nat.cast_zero, zero_mul, ← Nat.cast_zero, mixingTime_le_iff hπ]
    have hlog : Real.logb 2 ε⁻¹ ≤ 0 := Nat.ceil_eq_zero.1 hℓ
    have h1 : 1 ≤ ε := by
      rw [Real.logb_nonpos_iff one_lt_two (inv_pos.2 hε), inv_le_one₀ hε] at hlog
      exact hlog
    exact (distToStationary_le_one 0).trans h1
  obtain h | ⟨s, hs⟩ : mixingTime κ π (1 / 4) = ⊤ ∨ ∃ s : ℕ, mixingTime κ π (1 / 4) = s := by
    cases mixingTime κ π (1 / 4) using ENat.recTopCoe <;> simp
  · rw [h, ENat.mul_top (by exact_mod_cast hℓ)]
    exact le_top
  -- `d(ℓ * s) ≤ 2⁻¹ ^ (ℓ + 1) ≤ 2⁻¹ ^ ℓ ≤ ε`
  have hpow : (2⁻¹ : ℝ) ^ ℓ ≤ ε := by
    have hceil : ε⁻¹ ≤ 2 ^ ℓ := by
      have := (Real.logb_le_iff_le_rpow one_lt_two (inv_pos.2 hε)).1 (Nat.le_ceil (Real.logb 2 ε⁻¹))
      rwa [Real.rpow_natCast] at this
    rw [inv_pow]
    exact inv_le_of_inv_le₀ hε hceil
  have hd : distToStationary κ π (ℓ * s) ≤ ε := by
    refine (distToStationary_mul_le_inv_two_pow hπ (distToStationary_le_of_mixingTime_eq hs)
      hℓ).trans (le_trans ?_ hpow)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ ℓ)
  rw [hs]
  exact_mod_cast mixingTime_le_of_distToStationary_le hd

/-- **Geometric convergence at the mixing time**: `tvDist ((κ ^ t) x) π ≤ 2⁻¹ ^ (t / s)` for every
`t ≥ s`, when `s = t_mix(1/4)` is finite. -/
theorem tvDist_pow_apply_le_inv_two_pow_div_mixingTime (hπ : κ.Invariant π) {s t : ℕ}
    (hs : mixingTime κ π (1 / 4) = s) (hst : s ≤ t) (x : α) :
    tvDist ((κ ^ t) x) π ≤ 2⁻¹ ^ (t / s) :=
  tvDist_pow_apply_le_inv_two_pow_div hπ (distToStationary_le_of_mixingTime_eq hs) hst x

/-- If `δ(κ ^ m) < 1` for some `m`, the mixing times from an invariant probability measure are
finite at every positive level. -/
theorem mixingTime_lt_top_of_dobrushinCoeff_pow_lt_one (hπ : κ.Invariant π) {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) {ε : ℝ} (hε : 0 < ε) :
    mixingTime κ π ε < ⊤ := by
  obtain ⟨t, ht⟩ := ((tendsto_dobrushinCoeff_pow κ hm).eventually (gt_mem_nhds hε)).exists
  exact (mixingTime_le_of_distToStationary_le
    ((distToStationary_le_dobrushinCoeff hπ t).trans ht.le)).trans_lt (ENat.natCast_lt_top t)

end ProbabilityTheory.Kernel
