/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Powers near `0` from above

A complement to `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: for `t > 0`, the power
`x ↦ x ^ t` maps small positive numbers to small positive numbers. It reparametrizes statements
that hold for all small enough `δ > 0`, such as the asymptotic bounds of fixed-confidence
identification at small confidence levels, by the confidence level `δ ^ t`.

## Main statements

* `Real.tendsto_rpow_nhdsGT_zero`: for `t > 0`, `x ^ t → 0⁺` as `x → 0⁺`.
* `Real.eventually_le_mul_ofReal_log_of_rpow_inv`: bounds `f (δ ^ (1 / s)) ≤ c' log (1 / δ)` for
  every `c' > t` and `s > 1` give `f δ ≤ c log (1 / δ)` for every `c > t`.
-/

public section

open Filter Set

open scoped Topology ENNReal NNReal

namespace Real

/-- For `t > 0`, `x ^ t` tends to `0` from above as `x` does. -/
theorem tendsto_rpow_nhdsGT_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ ↦ x ^ t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx ↦
    rpow_pos_of_pos hx t⟩
  simpa [zero_rpow ht.ne'] using
    ((continuousAt_rpow_const 0 t (Or.inr ht.le)).tendsto).mono_left nhdsWithin_le_nhds

/-- **Rescaling the confidence level.** If for every `c' > t` and every `s > 1`, a quantity `f` of
the confidence level satisfies `f (δ ^ (1 / s)) ≤ c' log (1 / δ)` for all small enough `δ > 0`,
then for every `c > t`, `f δ ≤ c log (1 / δ)` for all small enough `δ > 0`. Together with
`LMLExplore.Identification.eventually_unionBoundThreshold_rpow_inv_le`, this turns sample
complexity bounds for thresholds `log (r n / δ)` into bounds for the union-bound thresholds
`β_{x_δ}` of `Identification/GLR.lean`. -/
lemma eventually_le_mul_ofReal_log_of_rpow_inv {f : ℝ → ℝ≥0∞} {t : ℝ≥0∞}
    (h : ∀ c' : ℝ≥0, t < c' → ∀ s : ℝ, 1 < s →
      ∀ᶠ δ in 𝓝[>] 0, f (δ ^ s⁻¹) ≤ c' * ENNReal.ofReal (log (1 / δ)))
    {c : ℝ≥0} (hc : t < c) :
    ∀ᶠ δ in 𝓝[>] 0, f δ ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- Choose `t < c' < c` and the exponent `s = c / c' > 1`.
  obtain ⟨c', hc', hc'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  have hc'c_real : (c' : ℝ) < c := mod_cast ENNReal.coe_lt_coe.1 hc'c
  have hc'0 : (0 : ℝ) < c' := mod_cast ENNReal.coe_pos.1 (zero_le.trans_lt hc')
  set s : ℝ := c / c'
  have hs : 1 < s := (one_lt_div hc'0).2 hc'c_real
  have hs0 : 0 < s := one_pos.trans hs
  -- At `δ' = δ ^ s`, `f δ ≤ c' log (1 / δ') = c log (1 / δ)` for small `δ`.
  filter_upwards [(tendsto_rpow_nhdsGT_zero hs0).eventually (h c' hc' s hs), self_mem_nhdsWithin]
    with δ hδ hδ0
  have hδ0 : 0 < δ := Set.mem_Ioi.1 hδ0
  rw [rpow_rpow_inv hδ0.le hs0.ne'] at hδ
  have h_log : log (1 / δ ^ s) = s * log (1 / δ) := by
    rw [one_div, one_div, log_inv, log_inv, log_rpow hδ0, mul_neg]
  have hc_eq : (c' : ℝ) * s = c := by
    simp only [s]
    field_simp
  refine hδ.trans_eq ?_
  calc (c' : ℝ≥0∞) * ENNReal.ofReal (log (1 / δ ^ s))
  _ = ENNReal.ofReal (c' * s * log (1 / δ)) := by
    rw [h_log, mul_assoc, ENNReal.ofReal_mul c'.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  _ = c * ENNReal.ofReal (log (1 / δ)) := by
    rw [hc_eq, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end Real
