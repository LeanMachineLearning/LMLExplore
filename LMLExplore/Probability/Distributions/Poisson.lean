/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Poisson laws: exponential moments and the increase of the masses up to the mode

The count under the Poisson law `Po(r)` on `ℕ` has the moment generating function
`η ↦ exp (r (exp η - 1))`, finite for every `η`, hence the cumulant generating function
`η ↦ r (exp η - 1)`. Tau Ceti states these facts for the identity under the real-valued law
`Po(ℝ, r) = (poissonMeasure r).map Nat.cast` (`TauCeti.Probability.mgf_id_map_cast_poissonMeasure`,
`TauCeti.Probability.cgf_id_map_cast_poissonMeasure` and
`TauCeti.Probability.integrableExpSet_id_map_cast_poissonMeasure`); this file transfers them to the
count through `ProbabilityTheory.mgf_id_map`, `LMLExplore.cgf_id_map` and
`LMLExplore.integrableExpSet_id_map`. Tilting `Po(r)` by `n ↦ η n` multiplies its rate by `exp η`:
that is Tau Ceti's `TauCeti.Probability.poissonMeasure_tilted_mul`.

The masses `Po(r) {k} = exp (-r) r ^ k / k!` increase in `k` as long as `k ≤ r`, since the ratio
of two consecutive masses is `r / (k + 1)`.

## Main statements

* `LMLExplore.mgf_natCast_poissonMeasure`, `LMLExplore.cgf_natCast_poissonMeasure`: the moment and
  cumulant generating functions of the count under `Po(r)`.
* `LMLExplore.integrableExpSet_natCast_poissonMeasure`: every exponential moment of the count under
  `Po(r)` is finite.
* `LMLExplore.poissonMeasure_singleton_le_of_le`: `Po(r) {k} ≤ Po(r) {k₁}` for `k ≤ k₁ ≤ r`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal Nat

namespace LMLExplore

/-- The moment generating function of the count under `Po(r)` is `η ↦ exp (r (exp η - 1))`. -/
@[simp]
lemma mgf_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    mgf (Nat.cast : ℕ → ℝ) (poissonMeasure r) η = exp (r * (exp η - 1)) :=
  congrFun ((mgf_id_map .of_discrete).symm.trans
    (TauCeti.Probability.mgf_id_map_cast_poissonMeasure r)) η

/-- The cumulant generating function of the count under `Po(r)` is `η ↦ r (exp η - 1)`. -/
@[simp]
theorem cgf_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    cgf (Nat.cast : ℕ → ℝ) (poissonMeasure r) η = r * (exp η - 1) :=
  congrFun ((cgf_id_map .of_discrete).symm.trans
    (TauCeti.Probability.cgf_id_map_cast_poissonMeasure r)) η

/-- Every exponential moment of the count under `Po(r)` is finite. -/
@[simp]
theorem integrableExpSet_natCast_poissonMeasure (r : ℝ≥0) :
    integrableExpSet (Nat.cast : ℕ → ℝ) (poissonMeasure r) = univ :=
  (integrableExpSet_id_map .of_discrete).symm.trans
    (TauCeti.Probability.integrableExpSet_id_map_cast_poissonMeasure r)

/-- The masses of the Poisson law `Po(r)` increase up to its mode: `Po(r) {k} ≤ Po(r) {k₁}` for
`k ≤ k₁ ≤ r`. -/
theorem poissonMeasure_singleton_le_of_le {r : ℝ≥0} {k k₁ : ℕ} (hk : k ≤ k₁) (hr : (k₁ : ℝ) ≤ r) :
    poissonMeasure r {k} ≤ poissonMeasure r {k₁} := by
  rw [poissonMeasure_singleton, poissonMeasure_singleton]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  -- induction on `k₁`, the hypothesis `k₁ ≤ r` weakening along the way
  revert hr
  induction k₁, hk using Nat.le_induction with
  | base => exact fun _ ↦ le_rfl
  | succ n hkn ih =>
    intro hr
    push_cast at hr
    have hn : (n : ℝ) ≤ r := by linarith
    refine (ih hn).trans ?_
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have h1 : 0 ≤ (r : ℝ) ^ n * (n ! : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hr h1]

end LMLExplore
