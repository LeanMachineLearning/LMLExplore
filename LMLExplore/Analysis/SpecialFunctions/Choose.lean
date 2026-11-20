/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The descending factorial over a power

The fraction `n (n - 1) ⋯ (n - k + 1) / nᵏ` of the injective maps among the maps from a set of
size `k` to a set of size `n` tends to `1` as `n → ∞`. This is the `tendsto_one` form of
Mathlib's `isEquivalent_descFactorial`.

## Main statements

* `Nat.tendsto_descFactorial_div_pow`: the limit in `ℝ`.
* `ENNReal.tendsto_descFactorial_mul_inv_pow`: the limit in `ℝ≥0∞`.
-/

public section

open Filter Topology Asymptotics
open scoped ENNReal

namespace Nat

/-- `n (n - 1) ⋯ (n - k + 1) / nᵏ` tends to `1` as `n → ∞`, in `ℝ`. -/
theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n.descFactorial k : ℝ) / (n : ℝ) ^ k) atTop (𝓝 1) :=
  (isEquivalent_iff_tendsto_one ((eventually_ne_atTop 0).mono fun _ hn ↦
    pow_ne_zero k (Nat.cast_ne_zero.2 hn))).1 (isEquivalent_descFactorial k)

end Nat

namespace ENNReal

/-- `n (n - 1) ⋯ (n - k + 1) / nᵏ` tends to `1` as `n → ∞`, in `ℝ≥0∞`. -/
theorem tendsto_descFactorial_mul_inv_pow (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n.descFactorial k : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ^ k) atTop (𝓝 1) := by
  refine (by simpa using ENNReal.tendsto_ofReal (Nat.tendsto_descFactorial_div_pow k) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n.descFactorial k : ℝ) / (n : ℝ) ^ k)) atTop
      (𝓝 1)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [div_eq_mul_inv, ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_pow,
    Nat.pos_of_ne_zero hn, ENNReal.inv_pow]

end ENNReal
