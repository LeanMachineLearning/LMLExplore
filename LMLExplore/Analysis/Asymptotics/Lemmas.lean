/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Limits of ratios from two-sided eventual bounds

## Main statements

* `Asymptotics.tendsto_div_of_eventually_mul_le`: if `g` is eventually positive, `c g ≤ f`
  eventually for every `c < L` and `f ≤ c g` eventually for every `c > L`, then `f / g → L`.

Tau Ceti's `Asymptotics.isLittleO_sub_mul_iff_tendsto_div` turns such a limit into the estimate
`f - L g = o(g)`.
-/

public section

open Filter Topology

namespace Asymptotics

variable {ι : Type*} {l : Filter ι}

/-- If `g` is eventually positive, `c g ≤ f` eventually for every `c < L`, and `f ≤ c g`
eventually for every `c > L`, then `f / g → L`. -/
theorem tendsto_div_of_eventually_mul_le {f g : ι → ℝ} {L : ℝ} (hg : ∀ᶠ x in l, 0 < g x)
    (hlow : ∀ c < L, ∀ᶠ x in l, c * g x ≤ f x) (hup : ∀ c, L < c → ∀ᶠ x in l, f x ≤ c * g x) :
    Tendsto (fun x ↦ f x / g x) l (𝓝 L) := by
  refine tendsto_order.mpr ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨c', hcc', hc'⟩ := exists_between hc
    filter_upwards [hlow c' hc', hg] with x hx hgx
    rw [lt_div_iff₀ hgx]
    exact (mul_lt_mul_of_pos_right hcc' hgx).trans_le hx
  · obtain ⟨c', hc', hc'c⟩ := exists_between hc
    filter_upwards [hup c' hc', hg] with x hx hgx
    rw [div_lt_iff₀ hgx]
    exact hx.trans_lt (mul_lt_mul_of_pos_right hc'c hgx)

end Asymptotics
