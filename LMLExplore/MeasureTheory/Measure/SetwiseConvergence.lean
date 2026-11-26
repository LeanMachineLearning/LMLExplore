/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Setwise convergence of measures

Measures `μs i` converge *setwise* to `μ` along a filter `l` when `μs i s → μ s` for every
measurable set `s`. This file proves the convergence theorems of integration along a setwise
convergent family of measures, and that setwise convergence passes to finite products.

Fatou's lemma holds along measures `μs i` with `μ s ≤ liminf (μs i s)` for every measurable `s`:
`∫⁻ liminf f i ∂μ ≤ liminf ∫⁻ f i ∂μs i`. Applied to `f i` and to `C - f i`, it gives a dominated
convergence theorem along a setwise convergent family with a finite limit `μ`: if measurable
functions `f i`, bounded by a constant, converge `μ`-almost everywhere to `g`, then
`∫ f i ∂μs i → ∫ g ∂μ`. No uniform absolute continuity of the `μs i` (the conclusion of the
Vitali–Hahn–Saks theorem) is needed. For a fixed bounded measurable function, the integrals
converge along any filter.

With Fubini's theorem, the dominated convergence theorem shows that setwise convergence passes to
products: if `μs i → μ` and `νs i → ν` setwise, with finite limits, then
`(μs i).prod (νs i) → μ.prod ν` setwise, and by induction the finite products
`Measure.pi (μs i)` converge setwise to `Measure.pi μ`.

## Main statements

* `MeasureTheory.lintegral_liminf_le_of_forall_measurableSet_measure_le_liminf_measure`: Fatou's
  lemma along measures whose values on measurable sets are lower semicontinuous.
* `MeasureTheory.tendsto_lintegral_of_tendsto_measure`,
  `MeasureTheory.tendsto_integral_of_tendsto_measure`: setwise convergence gives the convergence of
  the integrals of a bounded measurable function, along any filter.
* `MeasureTheory.tendsto_lintegral_of_tendsto_measure_of_tendsto`,
  `MeasureTheory.tendsto_integral_of_tendsto_measure_of_tendsto`: the dominated convergence
  theorem along a setwise convergent family of measures.
* `MeasureTheory.tendsto_measure_prod_of_tendsto_measure`: setwise convergence of the products of
  two families.
* `MeasureTheory.tendsto_measure_pi_of_tendsto_measure`: setwise convergence of finite products.

## Implementation notes

The statements and proofs are adapted from
`EValuesResearch/ForLMLExplore/MeasureTheory/Measure/SetwiseConvergence.lean` (commit `83205cb`)
in the paper project `RemyDegenne/evalues_research`, stated there for sequences of probability
measures, functions converging everywhere and the powers `Measure.pi fun _ : Fin n ↦ μs k`, and
rewritten here on the API of LMLExplore: the proofs go through Fatou's lemma along varying
measures, built on the lower semicontinuity of the Lebesgue integral
`MeasureTheory.lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure`,
instead of a uniform approximation by functions with finitely many values.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 19, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {l : Filter ι}
  {μ : Measure α} {μs : ι → Measure α}

section Fatou

/-- Fatou's lemma along a sequence of measures whose values on measurable sets are lower
semicontinuous. -/
private lemma lintegral_liminf_le_nat {μs : ℕ → Measure α}
    (h : ∀ s, MeasurableSet s → μ s ≤ liminf (fun n ↦ μs n s) atTop) {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ ≤ liminf (fun n ↦ ∫⁻ x, f n x ∂μs n) atTop := by
  have hinf (n : ℕ) : Measurable fun x ↦ ⨅ k ≥ n, f k x :=
    .biInf {k | k ≥ n} (to_countable _) fun k _ ↦ hf k
  simp_rw [liminf_eq_iSup_iInf_of_nat]
  rw [lintegral_iSup hinf fun n m hnm x ↦ biInf_mono fun k hk ↦ hnm.trans hk]
  refine iSup_le fun n ↦ ?_
  refine (lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure
    (hinf n) h).trans ?_
  rw [← liminf_eq_iSup_iInf_of_nat]
  exact liminf_le_liminf ((eventually_ge_atTop n).mono fun k hk ↦
    lintegral_mono fun x ↦ iInf₂_le k hk)

/-- **Fatou's lemma along varying measures.** If `μ s ≤ liminf (μs i s)` along a countably
generated filter for every measurable set `s`, then
`∫⁻ liminf f i ∂μ ≤ liminf ∫⁻ f i ∂μs i` for measurable functions `f i`. With `μs i = μ` this is
`MeasureTheory.lintegral_liminf_le`; it applies to setwise convergent measures. -/
theorem lintegral_liminf_le_of_forall_measurableSet_measure_le_liminf_measure
    [l.IsCountablyGenerated] (h : ∀ s, MeasurableSet s → μ s ≤ liminf (fun i ↦ μs i s) l)
    {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, liminf (fun i ↦ f i x) l ∂μ ≤ liminf (fun i ↦ ∫⁻ x, f i x ∂μs i) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  obtain ⟨u, hu, hul⟩ := exists_seq_tendsto_liminf (f := l) (u := fun i ↦ ∫⁻ x, f i x ∂μs i)
  calc ∫⁻ x, liminf (fun i ↦ f i x) l ∂μ
  _ ≤ ∫⁻ x, liminf (fun n ↦ f (u n) x) atTop ∂μ := lintegral_mono fun x ↦ hul.liminf_le_liminf_comp
  _ ≤ liminf (fun n ↦ ∫⁻ x, f (u n) x ∂μs (u n)) atTop :=
    lintegral_liminf_le_nat (fun s hs ↦ (h s hs).trans hul.liminf_le_liminf_comp) fun n ↦ hf (u n)
  _ = liminf (fun i ↦ ∫⁻ x, f i x ∂μs i) l := hu.liminf_eq

end Fatou

section Convergence

/-- The common step of the convergence theorems: if the integrals of `f i ≤ C` and of `C - f i`
against `μs i` have liminfs at least `a` and `b`, and `C * μ univ ≤ a + b` where
`μs i univ → μ univ < ∞`, then the integrals of `f i` tend to `a`. -/
private lemma tendsto_lintegral_of_le_liminf [IsFiniteMeasure μ]
    (hμ : Tendsto (fun i ↦ μs i univ) l (𝓝 (μ univ))) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, f i x ≤ C)
    {a b : ℝ≥0∞} (ha : a ≤ liminf (fun i ↦ ∫⁻ x, f i x ∂μs i) l)
    (hb : b ≤ liminf (fun i ↦ ∫⁻ x, C - f i x ∂μs i) l) (hab : C * μ univ ≤ a + b) :
    Tendsto (fun i ↦ ∫⁻ x, f i x ∂μs i) l (𝓝 a) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  -- the two integrals add up to `C * μs i univ`, which tends to `C * μ univ`
  have hsum : Tendsto (fun i ↦ ∫⁻ x, f i x ∂μs i + ∫⁻ x, C - f i x ∂μs i) l
      (𝓝 (C * μ univ)) := by
    refine (ENNReal.Tendsto.const_mul hμ (.inr hC)).congr' ?_
    filter_upwards [hfC] with i hi
    rw [← lintegral_add_left (hf i), ← lintegral_const]
    exact lintegral_congr_ae (hi.mono fun x hx ↦ (add_tsub_cancel_of_le hx).symm)
  have hb' : b ≠ ∞ := by
    refine ((hb.trans ?_).trans_lt (ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ))).ne
    exact (liminf_le_liminf (.of_forall fun i ↦ le_add_self)).trans_eq hsum.liminf_eq
  refine tendsto_order.2 ⟨fun a' ha' ↦ eventually_lt_of_lt_liminf (ha'.trans_le ha),
    fun a' ha' ↦ ?_⟩
  have hlt : C * μ univ < a' + b := hab.trans_lt (ENNReal.add_lt_add_right hb' ha')
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [add_zero] at hlt
    filter_upwards [hsum.eventually (gt_mem_nhds hlt)] with i hi
    exact le_self_add.trans_lt hi
  obtain ⟨a'', ha'', b', hb'b, hlt'⟩ :=
    ENNReal.exists_lt_add_of_lt_add hlt (zero_le.trans_lt ha').ne' hb0
  filter_upwards [hsum.eventually (gt_mem_nhds hlt'),
    eventually_lt_of_lt_liminf (hb'b.trans_le hb)] with i h₁ h₂
  exact lt_of_add_lt_add_right (h₁.trans_le (add_le_add ha''.le h₂.le))

/-- **Setwise convergence gives the convergence of the integrals of a bounded measurable
function.** If measures `μs i` converge setwise to a finite measure `μ` along any filter, and a
measurable `f` is eventually at most a finite constant `μs i`-almost everywhere, then
`∫⁻ f ∂μs i → ∫⁻ f ∂μ`. -/
theorem tendsto_lintegral_of_tendsto_measure [IsFiniteMeasure μ]
    (hμ : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) {f : α → ℝ≥0∞}
    (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, f x ≤ C) :
    Tendsto (fun i ↦ ∫⁻ x, f x ∂μs i) l (𝓝 (∫⁻ x, f x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hle (s : Set α) (hs : MeasurableSet s) : μ s ≤ liminf (fun i ↦ μs i s) l :=
    (hμ s hs).liminf_eq.ge
  refine tendsto_lintegral_of_le_liminf (hμ _ .univ) (fun _ ↦ hf) hC hfC
    (lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure hf hle)
    (lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure
      (measurable_const.sub hf) hle) ?_
  rw [← lintegral_const, ← lintegral_add_left hf]
  exact lintegral_mono fun x ↦ le_add_tsub

/-- **Dominated convergence along setwise convergent measures.** If measures `μs i` converge
setwise to a finite measure `μ` along a countably generated filter, and measurable functions
`f i`, eventually at most a finite constant `μs i`-almost everywhere, converge `μ`-almost
everywhere to `g`, then `∫⁻ f i ∂μs i → ∫⁻ g ∂μ`. -/
theorem tendsto_lintegral_of_tendsto_measure_of_tendsto [l.IsCountablyGenerated]
    [IsFiniteMeasure μ] (hμ : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)))
    {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, f i x ≤ C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) :
    Tendsto (fun i ↦ ∫⁻ x, f i x ∂μs i) l (𝓝 (∫⁻ x, g x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hle (s : Set α) (hs : MeasurableSet s) : μ s ≤ liminf (fun i ↦ μs i s) l :=
    (hμ s hs).liminf_eq.ge
  have hga : ∫⁻ x, g x ∂μ ≤ liminf (fun i ↦ ∫⁻ x, f i x ∂μs i) l :=
    (lintegral_congr_ae (hfg.mono fun x hx ↦ hx.liminf_eq.symm)).trans_le
      (lintegral_liminf_le_of_forall_measurableSet_measure_le_liminf_measure hle hf)
  have hgb : ∫⁻ x, C - g x ∂μ ≤ liminf (fun i ↦ ∫⁻ x, C - f i x ∂μs i) l :=
    (lintegral_congr_ae (hfg.mono fun x hx ↦
      (ENNReal.Tendsto.sub tendsto_const_nhds hx (.inl hC)).liminf_eq.symm)).trans_le
      (lintegral_liminf_le_of_forall_measurableSet_measure_le_liminf_measure hle
        fun i ↦ measurable_const.sub (hf i))
  refine tendsto_lintegral_of_le_liminf (hμ _ .univ) hf hC hfC hga hgb ?_
  rw [← lintegral_const, ← lintegral_add_left' (aemeasurable_of_tendsto_metrizable_ae l
    (fun i ↦ (hf i).aemeasurable) hfg)]
  exact lintegral_mono fun x ↦ le_add_tsub

/-- The Bochner integrals of `f i` against `μs i` converge to that of `g` against `μ` when the
Lebesgue integrals of their positive and negative parts do. -/
private lemma tendsto_integral_of_tendsto_lintegral_ofReal [IsFiniteMeasure μ]
    (hμ : Tendsto (fun i ↦ μs i univ) l (𝓝 (μ univ))) {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ i, Measurable (f i)) {C : ℝ} (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, ‖f i x‖ ≤ C)
    (hg : Integrable g μ)
    (h₁ : Tendsto (fun i ↦ ∫⁻ x, .ofReal (f i x) ∂μs i) l (𝓝 (∫⁻ x, .ofReal (g x) ∂μ)))
    (h₂ : Tendsto (fun i ↦ ∫⁻ x, .ofReal (-f i x) ∂μs i) l (𝓝 (∫⁻ x, .ofReal (-g x) ∂μ))) :
    Tendsto (fun i ↦ ∫ x, f i x ∂μs i) l (𝓝 (∫ x, g x ∂μ)) := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  refine (((ENNReal.tendsto_toReal hg.lintegral_lt_top.ne).comp h₁).sub
    ((ENNReal.tendsto_toReal hg.neg.lintegral_lt_top.ne).comp h₂)).congr' ?_
  filter_upwards [hfC, hμ.eventually (gt_mem_nhds (measure_lt_top μ univ))] with i hi hfin
  have : IsFiniteMeasure (μs i) := ⟨hfin⟩
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (.of_bound (hf i).aestronglyMeasurable C hi)).symm

/-- **Setwise convergence gives the convergence of the integrals of a bounded measurable
function.** If measures `μs i` converge setwise to a finite measure `μ` along any filter, and a
measurable real function `f` is eventually bounded by a constant `μs i`-almost everywhere, then
`∫ f ∂μs i → ∫ f ∂μ`. -/
theorem tendsto_integral_of_tendsto_measure [IsFiniteMeasure μ]
    (hμ : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) {f : α → ℝ}
    (hf : Measurable f) {C : ℝ} (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, ‖f x‖ ≤ C) :
    Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  -- the bound holds `μ`-almost everywhere, since `μs i` tends to `μ` on the set where it fails
  have hfμ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
    have hs : MeasurableSet {x | ¬‖f x‖ ≤ C} := (measurableSet_le hf.norm measurable_const).compl
    rw [ae_iff]
    exact tendsto_nhds_unique (hμ _ hs)
      (tendsto_const_nhds.congr' (hfC.mono fun i hi ↦ (ae_iff.1 hi).symm))
  refine tendsto_integral_of_tendsto_lintegral_ofReal (hμ _ .univ) (fun _ ↦ hf) hfC
    (.of_bound hf.aestronglyMeasurable C hfμ) ?_ ?_
  · refine tendsto_lintegral_of_tendsto_measure hμ hf.ennreal_ofReal (C := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top
      (hfC.mono fun i hi ↦ hi.mono fun x hx ↦ ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self _).trans hx
  · refine tendsto_lintegral_of_tendsto_measure hμ hf.neg.ennreal_ofReal (C := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top
      (hfC.mono fun i hi ↦ hi.mono fun x hx ↦ ENNReal.ofReal_le_ofReal ?_)
    exact (neg_le_abs _).trans hx

/-- **Dominated convergence along setwise convergent measures.** If measures `μs i` converge
setwise to a finite measure `μ` along a countably generated filter, and measurable real functions
`f i`, eventually bounded by a constant `μs i`-almost everywhere, converge `μ`-almost everywhere
to `g`, then `∫ f i ∂μs i → ∫ g ∂μ`. -/
theorem tendsto_integral_of_tendsto_measure_of_tendsto [l.IsCountablyGenerated]
    [IsFiniteMeasure μ] (hμ : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)))
    {f : ι → α → ℝ} {g : α → ℝ} (hf : ∀ i, Measurable (f i)) {C : ℝ}
    (hfC : ∀ᶠ i in l, ∀ᵐ x ∂μs i, ‖f i x‖ ≤ C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) :
    Tendsto (fun i ↦ ∫ x, f i x ∂μs i) l (𝓝 (∫ x, g x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  -- `g` is integrable, by Fatou's lemma for `‖f i‖ₑ`
  have hg : Integrable g μ := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae l (fun i ↦ (hf i).aestronglyMeasurable) hfg, ?_⟩
    have hbd : ∀ᶠ i in l, ∫⁻ x, ‖f i x‖ₑ ∂μs i ≤ ENNReal.ofReal C * (μ univ + 1) := by
      filter_upwards [hfC, (hμ _ .univ).eventually
        (gt_mem_nhds (ENNReal.lt_add_right (measure_ne_top μ univ) one_ne_zero))] with i hi hμi
      calc ∫⁻ x, ‖f i x‖ₑ ∂μs i
      _ ≤ ∫⁻ _, ENNReal.ofReal C ∂μs i := lintegral_mono_ae (hi.mono fun x hx ↦ by
        rw [Real.eNorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal hx)
      _ ≤ ENNReal.ofReal C * (μ univ + 1) := by
        rw [lintegral_const]
        gcongr
    calc ∫⁻ x, ‖g x‖ₑ ∂μ
    _ = ∫⁻ x, liminf (fun i ↦ ‖f i x‖ₑ) l ∂μ :=
      lintegral_congr_ae (hfg.mono fun x hx ↦ hx.eNorm.liminf_eq.symm)
    _ ≤ liminf (fun i ↦ ∫⁻ x, ‖f i x‖ₑ ∂μs i) l :=
      lintegral_liminf_le_of_forall_measurableSet_measure_le_liminf_measure
        (fun s hs ↦ (hμ s hs).liminf_eq.ge) fun i ↦ (hf i).eNorm
    _ ≤ ENNReal.ofReal C * (μ univ + 1) := liminf_le_of_frequently_le' hbd.frequently
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨measure_lt_top μ univ, ENNReal.one_lt_top⟩)
  refine tendsto_integral_of_tendsto_lintegral_ofReal (hμ _ .univ) hf hfC hg ?_ ?_
  · refine tendsto_lintegral_of_tendsto_measure_of_tendsto hμ (fun i ↦ (hf i).ennreal_ofReal)
      (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top
      (hfC.mono fun i hi ↦ hi.mono fun x hx ↦ ENNReal.ofReal_le_ofReal ?_)
      (hfg.mono fun x hx ↦ ENNReal.tendsto_ofReal hx)
    exact (le_abs_self _).trans hx
  · refine tendsto_lintegral_of_tendsto_measure_of_tendsto hμ
      (fun i ↦ (hf i).neg.ennreal_ofReal) (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top
      (hfC.mono fun i hi ↦ hi.mono fun x hx ↦ ENNReal.ofReal_le_ofReal ?_)
      (hfg.mono fun x hx ↦ ENNReal.tendsto_ofReal hx.neg)
    exact (neg_le_abs _).trans hx

end Convergence

section Products

/-- **Setwise convergence of products.** If measures `μs i` and `νs i` converge setwise to
finite measures `μ` and `ν` along a countably generated filter, the products `(μs i).prod (νs i)`
converge setwise to `μ.prod ν`. -/
theorem tendsto_measure_prod_of_tendsto_measure [l.IsCountablyGenerated] {νs : ι → Measure β}
    {ν : Measure β} [∀ i, SFinite (νs i)] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)))
    (hν : ∀ s, MeasurableSet s → Tendsto (fun i ↦ νs i s) l (𝓝 (ν s))) {s : Set (α × β)}
    (hs : MeasurableSet s) : Tendsto (fun i ↦ (μs i).prod (νs i) s) l (𝓝 (μ.prod ν s)) := by
  simp_rw [Measure.prod_apply hs]
  refine tendsto_lintegral_of_tendsto_measure_of_tendsto hμ
    (fun i ↦ measurable_measure_prodMk_left hs)
    (ENNReal.add_ne_top.2 ⟨measure_ne_top ν univ, ENNReal.one_ne_top⟩) ?_
    (.of_forall fun x ↦ hν _ (measurable_prodMk_left hs))
  filter_upwards [(hν _ .univ).eventually
    (gt_mem_nhds (ENNReal.lt_add_right (measure_ne_top ν univ) one_ne_zero))] with i hi
  exact .of_forall fun x ↦ (measure_mono (subset_univ _)).trans hi.le

/-- Setwise convergence of the products indexed by `Fin n`. -/
private lemma tendsto_measure_pi_fin [l.IsCountablyGenerated] (n : ℕ) :
    ∀ {γ : Fin n → Type*} [∀ j, MeasurableSpace (γ j)] {μs : ι → (j : Fin n) → Measure (γ j)}
      {μ : (j : Fin n) → Measure (γ j)} [∀ i j, SigmaFinite (μs i j)] [∀ j, IsFiniteMeasure (μ j)],
      (∀ j s, MeasurableSet s → Tendsto (fun i ↦ μs i j s) l (𝓝 (μ j s))) →
      ∀ {s : Set ((j : Fin n) → γ j)}, MeasurableSet s →
        Tendsto (fun i ↦ Measure.pi (μs i) s) l (𝓝 (Measure.pi μ s)) := by
  induction n with
  | zero =>
    intro γ _ μs μ _ _ _ s _
    have h (ν : (j : Fin 0) → Measure (γ j)) : Measure.pi ν s = Measure.dirac isEmptyElim s := by
      rw [Measure.pi_of_empty]
    simp_rw [h]
    exact tendsto_const_nhds
  | succ n ih =>
    intro γ _ μs μ _ _ hμ s hs
    have h (ν : (j : Fin (n + 1)) → Measure (γ j)) [∀ j, SigmaFinite (ν j)] :
        Measure.pi ν s = ((ν 0).prod (Measure.pi fun j ↦ ν (Fin.succAbove 0 j)))
          ((MeasurableEquiv.piFinSuccAbove γ 0).symm ⁻¹' s) :=
      ((measurePreserving_piFinSuccAbove ν 0).symm.measure_preimage_equiv s).symm
    simp_rw [h]
    exact tendsto_measure_prod_of_tendsto_measure (hμ 0)
      (fun t ht ↦ ih (fun j ↦ hμ (Fin.succAbove 0 j)) ht)
      ((MeasurableEquiv.piFinSuccAbove γ 0).symm.measurable hs)

/-- **Setwise convergence of finite products.** If, for each `j` of a finite type, measures
`μs i j` converge setwise to a finite measure `μ j` along a countably generated filter, the
products `Measure.pi (μs i)` converge setwise to `Measure.pi μ`. For the powers
`Measure.pi fun _ : Fin n ↦ μs i` of setwise convergent probability measures, this is a step of
[EVR26, Note 19]. -/
theorem tendsto_measure_pi_of_tendsto_measure [l.IsCountablyGenerated] {κ : Type*} [Fintype κ]
    {γ : κ → Type*} [∀ j, MeasurableSpace (γ j)] {μs : ι → (j : κ) → Measure (γ j)}
    {μ : (j : κ) → Measure (γ j)} [∀ i j, SigmaFinite (μs i j)] [∀ j, IsFiniteMeasure (μ j)]
    (hμ : ∀ j s, MeasurableSet s → Tendsto (fun i ↦ μs i j s) l (𝓝 (μ j s)))
    {s : Set ((j : κ) → γ j)} (hs : MeasurableSet s) :
    Tendsto (fun i ↦ Measure.pi (μs i) s) l (𝓝 (Measure.pi μ s)) := by
  classical
  set e := (Fintype.equivFin κ).symm
  have h (ν : (j : κ) → Measure (γ j)) [∀ j, SigmaFinite (ν j)] :
      Measure.pi ν s = Measure.pi (fun j ↦ ν (e j)) (MeasurableEquiv.piCongrLeft γ e ⁻¹' s) :=
    ((measurePreserving_piCongrLeft ν e).measure_preimage_equiv s).symm
  simp_rw [h]
  exact tendsto_measure_pi_fin _ (fun j ↦ hμ (e j))
    ((MeasurableEquiv.piCongrLeft γ e).measurable hs)

end Products

end MeasureTheory
