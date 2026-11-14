/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Suprema of `f x / x` over a dense set of points

For `f : ℝ≥0∞ → ℝ≥0∞` monotone on an open interval `Ioo a b`, the supremum of `f x / x` over
`x ∈ Ioo a b` is already the supremum over the points of any dense set: the value at `x` is
approached by the values at points `c > x` of the dense set, since `f c ≥ f x` and `f x / c`
tends to `f x / x` as `c` decreases to `x`. With a countable dense set, this turns the supremum
over an interval, an uncountable family, into a countable one, which is what makes it measurable
when `f` depends measurably on a parameter; post-hoc valid families of tests, indexed by their
levels, are the main instance.

## Main statements

* `ENNReal.biSup_Ioo_div_eq_biSup_inter_of_dense`: for `f` monotone on `Ioo a b` and a dense set
  `D`, `⨆ x ∈ Ioo a b, f x / x = ⨆ x ∈ Ioo a b ∩ D, f x / x`.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace ENNReal

/-- For `f` monotone on an open interval `Ioo a b`, the supremum of `f x / x` over the interval is
the supremum over the points of the interval in any dense set `D`, for instance the rational
points. -/
theorem biSup_Ioo_div_eq_biSup_inter_of_dense {f : ℝ≥0∞ → ℝ≥0∞} {a b : ℝ≥0∞} {D : Set ℝ≥0∞}
    (hD : Dense D) (hf : MonotoneOn f (Ioo a b)) :
    ⨆ x ∈ Ioo a b, f x / x = ⨆ x ∈ Ioo a b ∩ D, f x / x := by
  refine le_antisymm (iSup₂_le fun x hx ↦ le_of_forall_lt fun r hr ↦ ?_)
    (biSup_mono fun _ hx ↦ hx.1)
  -- `c ↦ f x / c` is continuous at `x`, so it stays above `r` on a neighbourhood of `x`
  have h_tendsto : Tendsto (fun c ↦ f x / c) (𝓝 x) (𝓝 (f x / x)) :=
    ENNReal.Tendsto.const_div tendsto_id (Or.inl (ne_top_of_lt hx.2))
  obtain ⟨l, u, hxlu, hlu⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨a, hx.1⟩ ⟨b, hx.2⟩).1
    ((h_tendsto.eventually (lt_mem_nhds hr)).and (Iio_mem_nhds hx.2))
  -- a point `c` of `D` slightly to the right of `x` does the job
  obtain ⟨c, hcD, hc⟩ := hD.exists_between hxlu.2
  have hc_mem : c ∈ Ioo a b := ⟨hx.1.trans hc.1, (hlu ⟨hxlu.1.trans hc.1, hc.2⟩).2⟩
  calc r < f x / c := (hlu ⟨hxlu.1.trans hc.1, hc.2⟩).1
    _ ≤ f c / c := by
      gcongr
      exact hf hx hc_mem hc.1.le
    _ ≤ ⨆ x ∈ Ioo a b ∩ D, f x / x := le_iSup₂_of_le c ⟨hc_mem, hcD⟩ le_rfl

end ENNReal
