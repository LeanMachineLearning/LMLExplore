/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Topology.Semicontinuity.Berge
public import LMLExplore.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Continuity of the value of the pure exploration game

Asymptotically optimal identification algorithms such as Track-and-Stop sample the arms with
proportions that track an optimal allocation `w*(θ̂, ¬i)` at the current estimate `θ̂` of the
model, and stop when the cost `D(θ̂, w, ¬i)` of the alternatives is large enough. Their analysis
needs these quantities to depend continuously on the model: as `θ̂ → θ`, the value `D(θ̂, ¬i)` of
the game must converge to `D(θ, ¬i)`, and the optimal allocations at `θ̂` must eventually be close
to those at `θ`.

Degenne and Koolen (2019) derive these properties from the joint continuity of
`(θ, w) ↦ D(θ, w, ¬i)` on the models times the simplex, through Berge's maximum theorem
(`LMLExplore/Topology/Semicontinuity/Berge.lean`): the value `D(θ, ¬i) = sup_{w ∈ Δ_K} D(θ, w, ¬i)`
is a supremum over a fixed compact set. This file proves these consequences, at a point within a
set of models `s`, under that continuity hypothesis:
* the value `D(θ, ¬i)` of an answer is continuous [DK19, Lemma 28];
* the optimal allocations `w*(θ, ¬i)` are upper hemicontinuous [DK19, Lemma 28], with nonempty
  compact values;
* for finitely many answers, the value `D(θ)` of the game and the characteristic time `T*(θ)` are
  continuous on the admissible models [DK19, Lemma 29].

The file also proves the joint continuity that these consequences assume, for the cost
`(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` of any set `A` of alternatives, `D(θ, w, ¬i)` being the case
`A = ¬i`. It is an infimum of functions continuous in `(θ, w)`, hence upper semicontinuous as soon
as the divergences to the models of `A` are finite and continuous in `θ`; the lower
semicontinuity is the difficult half. It holds in two settings [DK19, Lemmas 24–27]:
* when `A` lies in a compact set `K`, with real divergences continuous in both models: the costs to
  the models of `K` then converge uniformly;
* for every `A`, compact or not, on a product model: models `θ : α → Θ₀` whose divergences on
  `∏ a, S a` are real per-arm divergences `k a (θ a) (θ' a)`, continuous on `S a ×ˢ S a`, such that
  every `x ∈ S a` has a neighbourhood `U` for which the parameters `y ∈ S a` with `k a x' y ≤ r` for
  some `x' ∈ U` form a relatively compact subset of `S a`, for every `r`. This is the non-compact
  setting of Feinberg, Kasyanov and Voorneveld (2014) used by Degenne and Koolen: near `(θ, w)`,
  the alternatives of bounded cost have their coordinates of positive weight in compact sets.
  Degenne and Koolen check this hypothesis for exponential families whose divergence `d(x, y)`
  tends to infinity as `y` tends to an endpoint of the interval of means.

In both settings the continuity holds for all allocations `w : α → ℝ` (a negative weight counts as
`0`), and on a product model it gives the continuity of `D(θ)` and of `T*(θ)` on the admissible
models.

Upper hemicontinuity of `w*(·, ¬i)` at `θ` means that for every open set `U` containing
`w*(θ, ¬i)`, `w*(θ', ¬i) ⊆ U` for `θ'` close to `θ`; when `w*(θ, ¬i)` is a single allocation,
the optimal allocations at nearby models converge to it.

## Main statements

* `IdentTask.isCompact_optAlloc`, `IdentTask.optAlloc_nonempty`: if `w ↦ D(θ, w, ¬i)` is upper
  semicontinuous on the simplex, the optimal allocations form a nonempty compact set.
* `IdentTask.continuousWithinAt_answerValue`: continuity of `θ ↦ D(θ, ¬i)`.
* `IdentTask.upperHemicontinuousWithinAt_optAlloc`: upper hemicontinuity of `θ ↦ w*(θ, ¬i)`.
* `IdentTask.continuousWithinAt_gameValue`, `IdentTask.continuousWithinAt_charTime`: continuity
  of `θ ↦ D(θ)` and of `θ ↦ T*(θ)` for finitely many answers.
* `IdentTask.upperSemicontinuousOn_biInf_cost`, `IdentTask.upperSemicontinuous_altCost`,
  `IdentTask.measurable_altCost`: upper semicontinuity, and measurability, of the cost of a set of
  alternatives in the model and the allocation.
* `IdentTask.continuousOn_biInf_cost_of_isCompact`, `IdentTask.continuousOn_altCost_of_isCompact`:
  joint continuity of the cost of alternatives contained in a compact set [DK19, Lemma 24].
* `IdentTask.continuousOn_biInf_cost_pi`, `IdentTask.continuousOn_altCost_pi`: joint continuity of
  the cost of any set of alternatives on a product model [DK19, Lemmas 25–27].
* `IdentTask.continuousOn_gameValue_pi`, `IdentTask.continuousOn_charTime_pi`: on a product model
  with finitely many answers, `D(θ)` and `T*(θ)` are continuous on the admissible models.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Theorems 22–23, Lemmas 24–29.
* [FKV14] E. A. Feinberg, P. O. Kasyanov and M. Voorneveld, *Berge's maximum theorem for
  noncompact image sets*, J. Math. Anal. Appl. 413 (2014).
-/

public section

open Set Filter Topology InformationTheory

open scoped ENNReal

namespace LMLExplore.Identification

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ} {w : α → ℝ}

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, the
optimal allocations form a compact set. -/
lemma isCompact_optAlloc (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    IsCompact (task.optAlloc θ i) := by
  convert h.isCompact_setOfPred_isMaxOn (isCompact_simplex α) using 1
  ext w
  exact task.mem_optAlloc_iff_isMaxOn

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, an
optimal allocation exists: the supremum `D(θ, ¬i)` is attained. -/
lemma optAlloc_nonempty [Nonempty α]
    (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    (task.optAlloc θ i).Nonempty := by
  obtain ⟨w, hw, hmax⟩ := h.exists_isMaxOn (simplex_nonempty α) (isCompact_simplex α)
  exact ⟨w, task.mem_optAlloc_iff_isMaxOn.2 ⟨hw, hmax⟩⟩

/-- The cost of the alternatives as a function on the models times the simplex, as a subtype. -/
private noncomputable def altCostSimplex (task : IdentTask α Θ ℐ 𝓨) (i : ℐ) (θ : Θ)
    (w : simplex α) : ℝ≥0∞ :=
  task.altCost θ w i

private lemma iSup_altCostSimplex (θ : Θ) :
    ⨆ w ∈ (univ : Set (simplex α)), altCostSimplex task i θ w = task.answerValue θ i := by
  simp only [mem_univ, iSup_pos, altCostSimplex, answerValue_def]
  exact (iSup_subtype' (p := (· ∈ simplex α)) (f := fun w _ ↦ task.altCost θ w i)).symm

/-- The maximizers of the cost of the alternatives over the simplex, as a subtype, are the optimal
allocations. -/
private lemma image_val_isMaxOn_altCostSimplex (θ : Θ) :
    Subtype.val '' {v : simplex α | v ∈ univ ∧ IsMaxOn (altCostSimplex task i θ) univ v} =
      task.optAlloc θ i := by
  ext w
  rw [task.mem_optAlloc_iff_isMaxOn]
  constructor
  · rintro ⟨v, ⟨-, hv⟩, rfl⟩
    exact ⟨v.2, fun w' hw' ↦ hv (mem_univ ⟨w', hw'⟩)⟩
  · rintro ⟨hw, hmax⟩
    exact ⟨⟨w, hw⟩, ⟨mem_univ _, fun v _ ↦ hmax v.2⟩, rfl⟩

variable [TopologicalSpace Θ] {s : Set Θ}

/-! ### Joint continuity of the cost of a set of alternatives -/

/-- **Upper semicontinuity of the cost of a set of alternatives.** If for every model `θ'` of `A`
and every arm `a`, the divergence `θ ↦ KL(ν_a(θ), ν_a(θ'))` is finite and continuous on `s`, then
`(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` is upper semicontinuous on `s ×ˢ univ`: it is an infimum of
continuous functions. -/
theorem upperSemicontinuousOn_biInf_cost {A : Set Θ}
    (h : ∀ θ' ∈ A, ∀ a, ContinuousOn (fun θ ↦ klDiv (task.ν θ a) (task.ν θ' a)) s)
    (h_top : ∀ θ' ∈ A, ∀ θ ∈ s, ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    UpperSemicontinuousOn (fun p : Θ × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ') (s ×ˢ univ) := by
  refine upperSemicontinuousOn_biInf fun θ' hθ' ↦ ContinuousOn.upperSemicontinuousOn ?_
  simp_rw [cost_def]
  refine continuousOn_finsetSum _ fun a _ p hp ↦ ?_
  refine ENNReal.Tendsto.mul ?_ (Or.inr (h_top θ' hθ' p.1 hp.1 a)) ?_
    (Or.inr ENNReal.ofReal_ne_top)
  · exact ((ENNReal.continuous_ofReal.comp ((continuous_apply a).comp continuous_snd)).tendsto
      p).mono_left nhdsWithin_le_nhds
  · exact ((h θ' hθ' a).comp continuousOn_fst fun q (hq : q ∈ s ×ˢ univ) ↦ hq.1) p hp

/-- **Upper semicontinuity of the cost of the alternatives** (`(θ, w) ↦ D(θ, w, ¬i)`), on a
space of models on which `θ ↦ KL(ν_a(θ), ν_a(θ'))` is finite and continuous for every arm `a`
and every alternative `θ'` to `i`. -/
theorem upperSemicontinuous_altCost
    (h : ∀ θ' ∈ task.alt i, ∀ a, Continuous fun θ ↦ klDiv (task.ν θ a) (task.ν θ' a))
    (h_top : ∀ θ' ∈ task.alt i, ∀ θ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    UpperSemicontinuous fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i := by
  rw [← upperSemicontinuousOn_univ_iff, ← univ_prod_univ]
  simp_rw [altCost_def]
  exact task.upperSemicontinuousOn_biInf_cost (fun θ' hθ' a ↦ (h θ' hθ' a).continuousOn)
    fun θ' hθ' θ _ a ↦ h_top θ' hθ' θ a

/-- **Measurability of the cost of the alternatives**: under the hypotheses of
`upperSemicontinuous_altCost`, `(θ, w) ↦ D(θ, w, ¬i)` is measurable. -/
theorem measurable_altCost [MeasurableSpace Θ] [OpensMeasurableSpace (Θ × (α → ℝ))]
    (h : ∀ θ' ∈ task.alt i, ∀ a, Continuous fun θ ↦ klDiv (task.ν θ a) (task.ν θ' a))
    (h_top : ∀ θ' ∈ task.alt i, ∀ θ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    Measurable fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i :=
  (task.upperSemicontinuous_altCost h h_top).measurable

omit [TopologicalSpace Θ] in
/-- With real divergences `k a θ θ'`, the transportation cost is a sum of real terms, a negative
weight or divergence counting as `0`. -/
private lemma cost_eq_sum_ofReal_max_mul_max {k : α → Θ → Θ → ℝ} {θ θ' : Θ}
    (hν : ∀ a, klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a θ θ')) (w : α → ℝ) :
    task.cost w θ θ' = ∑ a, ENNReal.ofReal (max (w a) 0 * max (k a θ θ') 0) := by
  simp_rw [cost_def, hν, ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_max,
    ENNReal.ofReal_zero, max_zero]

/-- Lower semicontinuity of the cost of a set of alternatives contained in a compact set, for real
divergences continuous in both models: the transportation costs to the models of the compact
set converge uniformly. -/
private lemma lowerSemicontinuousOn_biInf_cost_of_isCompact {k : α → Θ → Θ → ℝ} {A K : Set Θ}
    (hν : ∀ θ ∈ s, ∀ θ' ∈ K, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a θ θ'))
    (hk : ∀ a, ContinuousOn (fun p : Θ × Θ ↦ k a p.1 p.2) (s ×ˢ K))
    (hK : IsCompact K) (hAK : A ⊆ K) :
    LowerSemicontinuousOn (fun p : Θ × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ') (s ×ˢ univ) := by
  -- The real transportation cost from `p.1` to `θ'` with the allocation `p.2`.
  set G : Θ × (α → ℝ) → Θ → ℝ := fun p θ' ↦ ∑ a, max (p.2 a) 0 * max (k a p.1 θ') 0
  have hG_cont : ContinuousOn (Function.uncurry G) ((s ×ˢ univ) ×ˢ K) := by
    refine continuousOn_finsetSum _ fun a _ ↦ ?_
    refine (((continuous_apply a).comp (continuous_snd.comp continuous_fst)).max
      continuous_const).continuousOn.mul (ContinuousOn.sup ?_ continuousOn_const)
    exact (hk a).comp (f := fun q : (Θ × (α → ℝ)) × Θ ↦ (q.1.1, q.2)) (by fun_prop)
      fun q hq ↦ ⟨hq.1.1, hq.2⟩
  have h_eq : ∀ p ∈ s ×ˢ univ, ∀ θ' ∈ A, task.cost p.2 p.1 θ' = ENNReal.ofReal (G p θ') :=
    fun p hp θ' hθ' ↦ by
      rw [task.cost_eq_sum_ofReal_max_mul_max (hν p.1 hp.1 θ' (hAK hθ')),
        ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg (le_max_right _ _) (le_max_right _ _)]
  intro p₀ hp₀ c hc
  obtain ⟨r, -, hcr, hrD⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨r₂, -, hcr₂, hr₂r⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcr
  have hr₂r' : r₂ < r := (ENNReal.ofReal_lt_ofReal_iff'.1 hr₂r).1
  -- Near `p₀`, the real costs to the models of `K` are uniformly within `r - r₂` of those at `p₀`.
  obtain ⟨V, hV, hVG⟩ := hK.mem_uniformity_of_prod hG_cont hp₀
    (Metric.dist_mem_uniformity (sub_pos.2 hr₂r'))
  filter_upwards [hV, self_mem_nhdsWithin] with p hp hps
  refine hcr₂.trans_le (le_iInf₂ fun θ' hθ' ↦ ?_)
  have h₀ : r < G p₀ θ' := (ENNReal.ofReal_lt_ofReal_iff'.1
    (hrD.trans_le ((biInf_le _ hθ').trans_eq (h_eq p₀ hp₀ θ' hθ')))).1
  have h₁ := hVG p hp θ' (hAK hθ')
  rw [mem_ofPred_eq, Real.dist_eq, abs_lt] at h₁
  rw [h_eq p hps θ' hθ']
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Continuity of the cost of alternatives in a compact set** [DK19, Lemma 24]. Let `K` be a
compact set of models, and `s` a set of models such that the divergences
`KL(ν_a(θ), ν_a(θ')) = k a θ θ'` are real and continuous in `(θ, θ') ∈ s ×ˢ K`. Then for every set
`A ⊆ K`, the cost `(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` is continuous on `s ×ˢ univ`, the models
of `s` and all allocations. -/
theorem continuousOn_biInf_cost_of_isCompact {k : α → Θ → Θ → ℝ} {A K : Set Θ}
    (hν : ∀ θ ∈ s, ∀ θ' ∈ K, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a θ θ'))
    (hk : ∀ a, ContinuousOn (fun p : Θ × Θ ↦ k a p.1 p.2) (s ×ˢ K))
    (hK : IsCompact K) (hAK : A ⊆ K) :
    ContinuousOn (fun p : Θ × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ') (s ×ˢ univ) := by
  refine continuousOn_iff_lower_upperSemicontinuousOn.2
    ⟨task.lowerSemicontinuousOn_biInf_cost_of_isCompact hν hk hK hAK,
      task.upperSemicontinuousOn_biInf_cost (fun θ' hθ' a ↦ ?_) fun θ' hθ' θ hθ a ↦ ?_⟩
  · refine (ENNReal.continuous_ofReal.comp_continuousOn ((hk a).comp
      (f := fun θ ↦ (θ, θ')) (by fun_prop) fun θ hθ ↦ ⟨hθ, hAK hθ'⟩)).congr fun θ hθ ↦ ?_
    exact hν θ hθ θ' (hAK hθ') a
  · rw [hν θ hθ θ' (hAK hθ') a]
    exact ENNReal.ofReal_ne_top

/-- **Continuity of the cost of the alternatives in a compact set** [DK19, Lemma 24]: under the
hypotheses of `continuousOn_biInf_cost_of_isCompact`, if the alternatives to `i` lie in the compact
set `K`, then `(θ, w) ↦ D(θ, w, ¬i)` is continuous on `s ×ˢ univ`. -/
theorem continuousOn_altCost_of_isCompact {k : α → Θ → Θ → ℝ} {K : Set Θ}
    (hν : ∀ θ ∈ s, ∀ θ' ∈ K, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a θ θ'))
    (hk : ∀ a, ContinuousOn (fun p : Θ × Θ ↦ k a p.1 p.2) (s ×ˢ K))
    (hK : IsCompact K) (h_alt : task.alt i ⊆ K) :
    ContinuousOn (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i) (s ×ˢ univ) := by
  simp_rw [altCost_def]
  exact task.continuousOn_biInf_cost_of_isCompact hν hk hK h_alt

/-! ### Continuity in the model, through Berge's maximum theorem -/

/-- Continuity within `s ×ˢ simplex α` of `(θ, w) ↦ D(θ, w, ¬i)` is continuity within
`s ×ˢ univ` of its restriction to the subtype `simplex α`. -/
private lemma continuousWithinAt_altCostSimplex {w : simplex α}
    (h : ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i) (s ×ˢ simplex α)
      (θ, w)) :
    ContinuousWithinAt ↿(altCostSimplex task i) (s ×ˢ univ) (θ, w) := by
  -- `↿(altCostSimplex task i)` is the cost of the alternatives composed with `(θ, v) ↦ (θ, ↑v)`.
  have h_eq : ↿(altCostSimplex task i) =
      (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i) ∘ fun p : Θ × simplex α ↦ (p.1, ↑p.2) := by
    ext p
    simp [altCostSimplex, Function.HasUncurry.uncurry]
  rw [h_eq]
  exact h.comp (x := (θ, w)) (t := s ×ˢ simplex α)
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousWithinAt
    fun p hp ↦ ⟨hp.1, p.2.2⟩

/-- **Continuity of the value of an answer** [DK19, Lemma 28]. If `(θ, w) ↦ D(θ, w, ¬i)` is
continuous within `s ×ˢ simplex α` at every point `(θ, w)` with `w` in the simplex, then the value
`θ ↦ D(θ, ¬i)` of the game of the answer `i` is continuous within `s` at `θ`. -/
theorem continuousWithinAt_answerValue
    (h : ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt (task.answerValue · i) s θ := by
  have : CompactSpace (simplex α) := isCompact_iff_compactSpace.1 (isCompact_simplex α)
  simp_rw [← iSup_altCostSimplex task]
  exact (UpperHemicontinuousWithinAt.const (z := (univ : Set (simplex α))))
    |>.continuousWithinAt_biSup .const isCompact_univ
    fun v _ ↦ continuousWithinAt_altCostSimplex task (h v v.2)

/-- **Upper hemicontinuity of the optimal allocations** [DK19, Lemma 28]. If
`(θ, w) ↦ D(θ, w, ¬i)` is continuous within `s ×ˢ simplex α` at every point `(θ, w)` with `w` in
the simplex, then the optimal allocations `θ ↦ w*(θ, ¬i)` are upper hemicontinuous within `s` at
`θ`: for every open set `U ⊇ w*(θ, ¬i)`, `w*(θ', ¬i) ⊆ U` for `θ' ∈ s` close enough to `θ`. -/
theorem upperHemicontinuousWithinAt_optAlloc
    (h : ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    UpperHemicontinuousWithinAt (task.optAlloc · i) s θ := by
  have : CompactSpace (simplex α) := isCompact_iff_compactSpace.1 (isCompact_simplex α)
  have hm : LowerSemicontinuousWithinAt
      (fun θ ↦ ⨆ w ∈ (univ : Set (simplex α)), altCostSimplex task i θ w) s θ := by
    simp_rw [iSup_altCostSimplex task]
    exact (task.continuousWithinAt_answerValue h).lowerSemicontinuousWithinAt
  have h_uhc := ((UpperHemicontinuousWithinAt.const
    (z := (univ : Set (simplex α)))).upperHemicontinuousWithinAt_isMaxOn isCompact_univ (fun v _ ↦
      (continuousWithinAt_altCostSimplex task (h v v.2)).upperSemicontinuousWithinAt) hm).image
    continuous_subtype_val
  -- The maximizers in the subtype are the optimal allocations.
  simpa only [image_val_isMaxOn_altCostSimplex] using h_uhc

/-- **Continuity of the value of the game** [DK19, Lemma 29]. For finitely many answers, if for
every answer `i` the function `(θ, w) ↦ D(θ, w, ¬i)` is continuous within `s ×ˢ simplex α` at
every point `(θ, w)` with `w` in the simplex, then the value `θ ↦ D(θ)` of the game is continuous
within a set `s` of admissible models at an admissible model `θ`. -/
theorem continuousWithinAt_gameValue [Finite ℐ] (hs : s ⊆ task.M) (hθ : θ ∈ task.M)
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt task.gameValue s θ := by
  have : Fintype ℐ := Fintype.ofFinite ℐ
  have h_sup : ContinuousWithinAt (fun θ ↦ (Finset.univ : Finset ℐ).sup (task.answerValue θ))
      s θ :=
    ContinuousWithinAt.finset_sup_apply fun i _ ↦ task.continuousWithinAt_answerValue (h i)
  refine h_sup.congr (fun θ' hθ' ↦ ?_) ?_
  · rw [task.gameValue_eq_iSup_answerValue (hs hθ'), Finset.sup_univ_eq_iSup]
  · rw [task.gameValue_eq_iSup_answerValue hθ, Finset.sup_univ_eq_iSup]

/-- **Continuity of the characteristic time** [DK19, Lemma 29]. Under the hypotheses of
`continuousWithinAt_gameValue`, the characteristic time `θ ↦ T*(θ) = D(θ)⁻¹` is continuous within
`s` at `θ`. -/
theorem continuousWithinAt_charTime [Finite ℐ] (hs : s ⊆ task.M) (hθ : θ ∈ task.M)
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt task.charTime s θ := by
  rw [show task.charTime = fun θ ↦ (task.gameValue θ)⁻¹ from funext task.charTime_def]
  exact (task.continuousWithinAt_gameValue hs hθ h).inv

end IdentTask

/-! ### Joint continuity on product models -/

namespace IdentTask

variable {α Θ₀ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [TopologicalSpace Θ₀] (task : IdentTask α (α → Θ₀) ℐ 𝓨) {S : α → Set Θ₀}
  {k : α → Θ₀ → Θ₀ → ℝ} {i : ℐ}

/-- The step of `lowerSemicontinuousOn_biInf_cost_pi` for one arm of positive weight `v` at the
parameter `x ∈ S`: near `(x, v)`, the parameters `y ∈ S` at divergence at most `2 r / v` from the
current parameter lie in a compact subset `K` of `S`, on which the weighted divergences
`max v 0 * max (k x y) 0` converge uniformly. -/
private lemma exists_isCompact_eventually_dist_lt {k : Θ₀ → Θ₀ → ℝ} {S' : Set Θ₀}
    (hk : ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k p.1 p.2) (S' ×ˢ S')) {x : Θ₀} (hx : x ∈ S')
    (hk_compact : ∃ U ∈ 𝓝[S'] x, ∀ r : ℝ,
      ∃ K ⊆ S', IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S', k x' y ≤ r → y ∈ K)
    {v : ℝ} (hv : 0 < v) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K ⊆ S', IsCompact K ∧ ∀ᶠ q in 𝓝[S' ×ˢ univ] (x, v),
      v / 2 < q.2 ∧ (∀ y ∈ S', k q.1 y ≤ 2 * r / v → y ∈ K) ∧
        ∀ y ∈ K, dist (max q.2 0 * max (k q.1 y) 0) (max v 0 * max (k x y) 0) < ε := by
  obtain ⟨U, hU, hUK⟩ := hk_compact
  obtain ⟨K, hKS, hK, hK_mem⟩ := hUK (2 * r / v)
  have hg_cont : ContinuousOn (fun z : (Θ₀ × ℝ) × Θ₀ ↦ max z.1.2 0 * max (k z.1.1 z.2) 0)
      ((S' ×ˢ univ) ×ˢ K) := by
    refine (continuous_snd.comp continuous_fst |>.max continuous_const).continuousOn.mul
      (ContinuousOn.sup ?_ continuousOn_const)
    exact hk.comp (f := fun z : (Θ₀ × ℝ) × Θ₀ ↦ (z.1.1, z.2)) (by fun_prop)
      fun z hz ↦ ⟨hz.1.1, hKS hz.2⟩
  obtain ⟨V, hV, hVg⟩ := hK.mem_uniformity_of_prod
    (f := fun (q : Θ₀ × ℝ) y ↦ max q.2 0 * max (k q.1 y) 0)
    hg_cont (⟨hx, mem_univ _⟩ : (x, v) ∈ S' ×ˢ univ) (Metric.dist_mem_uniformity hε)
  refine ⟨K, hKS, hK, ?_⟩
  have hU' : ∀ᶠ q in 𝓝[S' ×ˢ univ] (x, v), q.1 ∈ U := by
    rw [nhdsWithin_prod_eq]
    exact Filter.Eventually.prod_inl hU _
  have hv' : ∀ᶠ q in 𝓝[S' ×ˢ univ] (x, v), v / 2 < q.2 :=
    ((continuous_snd.tendsto (x, v)).mono_left nhdsWithin_le_nhds).eventually
      (lt_mem_nhds (half_lt_self hv))
  filter_upwards [hU', hv', hV] with q hqU hqv hqV
  exact ⟨hqv, fun y hy hky ↦ hK_mem q.1 hqU y hy hky, hVg q hqV⟩

/-- Lower semicontinuity of the cost of a set of alternatives on a product model with locally
relatively compact sublevel sets of the per-arm divergences. Near a point `(θ, w)`, the
alternatives whose cost stays bounded have their coordinates of positive weight in compact sets,
on which the per-arm costs converge uniformly; the coordinates of zero weight only add a
nonnegative term. -/
private lemma lowerSemicontinuousOn_biInf_cost_pi
    (hν : ∀ θ ∈ univ.pi S, ∀ θ' ∈ univ.pi S, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a (θ a) (θ' a)))
    (hk : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k a p.1 p.2) (S a ×ˢ S a))
    (hk_compact : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ,
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, k a x' y ≤ r → y ∈ K)
    {A : Set (α → Θ₀)} (hA : A ⊆ univ.pi S) :
    LowerSemicontinuousOn (fun p : (α → Θ₀) × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ')
      (univ.pi S ×ˢ univ) := by
  -- The real cost of arm `a` with parameter and weight `q` against the parameter `y`.
  set g : α → Θ₀ × ℝ → Θ₀ → ℝ := fun a q y ↦ max q.2 0 * max (k a q.1 y) 0 with hg
  have h_eq : ∀ p ∈ univ.pi S ×ˢ (univ : Set (α → ℝ)), ∀ θ' ∈ A,
      task.cost p.2 p.1 θ' = ∑ a, ENNReal.ofReal (g a (p.1 a, p.2 a) (θ' a)) :=
    fun p hp θ' hθ' ↦ task.cost_eq_sum_ofReal_max_mul_max (k := fun a θ θ' ↦ k a (θ a) (θ' a))
      (hν p.1 hp.1 θ' (hA hθ')) p.2
  rintro ⟨θ, w⟩ ⟨hθ, -⟩ c hc
  obtain ⟨r, hr0, hcr, hrD⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨r₂, -, hcr₂, hr₂r⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcr
  have hr₂r' : r₂ < r := (ENNReal.ofReal_lt_ofReal_iff'.1 hr₂r).1
  set ε := (r - r₂) / (Fintype.card α + 1) with hε_def
  have hε : 0 < ε := div_pos (sub_pos.2 hr₂r') (by positivity)
  -- For an arm of positive weight, the parameters of the alternatives of cost at most `r` near
  -- `(θ, w)` lie in a compact set, on which the cost of that arm converges uniformly.
  have h_arm : ∀ a, 0 < w a → ∃ K ⊆ S a, IsCompact K ∧ ∀ᶠ q in 𝓝[S a ×ˢ univ] (θ a, w a),
      w a / 2 < q.2 ∧ (∀ y ∈ S a, k a q.1 y ≤ 2 * r / w a → y ∈ K) ∧
        ∀ y ∈ K, dist (g a q y) (g a (θ a, w a) y) < ε := fun a ha ↦
    exists_isCompact_eventually_dist_lt (hk a) (hθ a (mem_univ a))
      (hk_compact a _ (hθ a (mem_univ a))) ha r hε
  choose! K hKS hK h_arm using h_arm
  -- These properties hold simultaneously for all arms of positive weight near `(θ, w)`.
  have h_ev : ∀ᶠ p in 𝓝[univ.pi S ×ˢ univ] (θ, w), ∀ a, 0 < w a →
      w a / 2 < p.2 a ∧ (∀ y ∈ S a, k a (p.1 a) y ≤ 2 * r / w a → y ∈ K a) ∧
        ∀ y ∈ K a, dist (g a (p.1 a, p.2 a) y) (g a (θ a, w a) y) < ε := by
    refine Filter.eventually_all.2 fun a ↦ ?_
    by_cases ha : 0 < w a
    · have h_tendsto : Tendsto (fun p : (α → Θ₀) × (α → ℝ) ↦ (p.1 a, p.2 a))
          (𝓝[univ.pi S ×ˢ univ] (θ, w)) (𝓝[S a ×ˢ univ] (θ a, w a)) :=
        (by fun_prop : Continuous fun p : (α → Θ₀) × (α → ℝ) ↦ (p.1 a, p.2 a)).continuousWithinAt
          |>.tendsto_nhdsWithin fun p hp ↦ ⟨hp.1 a (mem_univ a), mem_univ _⟩
      exact (h_tendsto.eventually (h_arm a ha)).mono fun p hp _ ↦ hp
    · exact Eventually.of_forall fun p h ↦ absurd h ha
  filter_upwards [h_ev, self_mem_nhdsWithin] with p hp hpS
  refine hcr₂.trans_le (le_iInf₂ fun θ' hθ' ↦ ?_)
  -- An alternative of cost more than `r` costs more than `r₂`.
  by_cases hle : task.cost p.2 p.1 θ' ≤ ENNReal.ofReal r
  swap
  · exact (ENNReal.ofReal_le_ofReal hr₂r'.le).trans (not_le.1 hle).le
  rw [h_eq p hpS θ' hθ'] at hle ⊢
  -- Each arm of positive weight of an alternative of cost at most `r` lies in its compact set.
  have h_close : ∀ a, 0 < w a → g a (θ a, w a) (θ' a) - ε < g a (p.1 a, p.2 a) (θ' a) := by
    intro a ha
    obtain ⟨hpw, hpK, hpg⟩ := hp a ha
    have hpa : 0 < p.2 a := (half_pos ha).trans hpw
    have hga : g a (p.1 a, p.2 a) (θ' a) ≤ r := by
      refine (ENNReal.ofReal_le_ofReal_iff hr0).1
        ((Finset.single_le_sum (f := fun a ↦ ENNReal.ofReal (g a (p.1 a, p.2 a) (θ' a)))
          (fun _ _ ↦ zero_le) (Finset.mem_univ a)).trans hle)
    have hk_le : k a (p.1 a) (θ' a) ≤ 2 * r / w a := by
      simp only [hg, max_eq_left hpa.le] at hga
      calc k a (p.1 a) (θ' a) ≤ max (k a (p.1 a) (θ' a)) 0 := le_max_left _ _
        _ ≤ r / p.2 a := (le_div_iff₀' hpa).2 hga
        _ ≤ r / (w a / 2) := div_le_div_of_nonneg_left hr0 (half_pos ha) hpw.le
        _ = 2 * r / w a := by field_simp
    have h := hpg (θ' a) (hpK (θ' a) (hA hθ' a (mem_univ a)) hk_le)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  -- The cost at `(θ, w)` comes from the arms of positive weight, and exceeds `r`.
  set P := Finset.univ.filter fun a ↦ 0 < w a with hP
  have h_sum₀ : r < ∑ a ∈ P, g a (θ a, w a) (θ' a) := by
    have h₀ := hrD.trans_le ((biInf_le _ hθ').trans_eq (h_eq (θ, w) ⟨hθ, mem_univ _⟩ θ' hθ'))
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg (le_max_right _ _)
      (le_max_right _ _)] at h₀
    rw [hP, Finset.sum_filter_of_ne fun a _ h ↦ ?_]
    · exact (ENNReal.ofReal_lt_ofReal_iff'.1 h₀).1
    · by_contra ha
      exact h (by simp [hg, max_eq_right (not_lt.1 ha)])
  have h_card : (P.card : ℝ) * ε < r - r₂ := by
    have hP_card : (P.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ P
    calc (P.card : ℝ) * ε ≤ Fintype.card α * ε := by gcongr
      _ < (Fintype.card α + 1) * ε := by linarith
      _ = r - r₂ := by rw [hε_def]; field_simp
  have h_sum : r₂ ≤ ∑ a ∈ P, g a (p.1 a, p.2 a) (θ' a) := by
    have := Finset.sum_le_sum fun a (ha : a ∈ P) ↦ (h_close a (Finset.mem_filter.1 ha).2).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
    linarith
  calc ENNReal.ofReal r₂ ≤ ENNReal.ofReal (∑ a ∈ P, g a (p.1 a, p.2 a) (θ' a)) :=
        ENNReal.ofReal_le_ofReal h_sum
    _ = ∑ a ∈ P, ENNReal.ofReal (g a (p.1 a, p.2 a) (θ' a)) :=
        ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg (le_max_right _ _) (le_max_right _ _)
    _ ≤ ∑ a, ENNReal.ofReal (g a (p.1 a, p.2 a) (θ' a)) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Continuity of the cost of a set of alternatives on a product model** [DK19, Lemmas 25–27;
FKV14].
Consider a task on the models `θ : α → Θ₀` whose divergences are given, on the models of
`∏ a, S a`, by real per-arm divergences `KL(ν_a(θ), ν_a(θ')) = k a (θ a) (θ' a)`, continuous on
`S a ×ˢ S a`. Suppose that every `x ∈ S a` has a neighbourhood `U` in `S a` such that for every
`r`, the parameters `y ∈ S a` with `k a x' y ≤ r` for some `x' ∈ U` lie in a compact subset of
`S a`. Then for every set `A ⊆ ∏ a, S a` of models, compact or not, the cost
`(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` is continuous on `(∏ a, S a) ×ˢ univ`, the models of
`∏ a, S a` and all allocations. -/
theorem continuousOn_biInf_cost_pi
    (hν : ∀ θ ∈ univ.pi S, ∀ θ' ∈ univ.pi S, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a (θ a) (θ' a)))
    (hk : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k a p.1 p.2) (S a ×ˢ S a))
    (hk_compact : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ,
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, k a x' y ≤ r → y ∈ K)
    {A : Set (α → Θ₀)} (hA : A ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → Θ₀) × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ')
      (univ.pi S ×ˢ univ) := by
  refine continuousOn_iff_lower_upperSemicontinuousOn.2
    ⟨task.lowerSemicontinuousOn_biInf_cost_pi hν hk hk_compact hA,
      task.upperSemicontinuousOn_biInf_cost (fun θ' hθ' a ↦ ?_) fun θ' hθ' θ hθ a ↦ ?_⟩
  · have hθ'a := hA hθ' a (mem_univ a)
    refine (ENNReal.continuous_ofReal.comp_continuousOn ((hk a).comp
      (f := fun θ : α → Θ₀ ↦ (θ a, θ' a)) (by fun_prop)
        fun θ (hθ : θ ∈ univ.pi S) ↦ ⟨hθ a (mem_univ a), hθ'a⟩)).congr fun θ hθ ↦ ?_
    exact hν θ hθ θ' (hA hθ') a
  · rw [hν θ hθ θ' (hA hθ') a]
    exact ENNReal.ofReal_ne_top

/-- **Continuity of the cost of the alternatives on a product model** [DK19, Lemma 27]: under
the hypotheses of `continuousOn_biInf_cost_pi`, if the alternatives to `i` are models of
`∏ a, S a`, then `(θ, w) ↦ D(θ, w, ¬i)` is continuous on `(∏ a, S a) ×ˢ univ`. -/
theorem continuousOn_altCost_pi
    (hν : ∀ θ ∈ univ.pi S, ∀ θ' ∈ univ.pi S, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a (θ a) (θ' a)))
    (hk : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k a p.1 p.2) (S a ×ˢ S a))
    (hk_compact : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ,
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, k a x' y ≤ r → y ∈ K)
    (h_alt : task.alt i ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → Θ₀) × (α → ℝ) ↦ task.altCost p.1 p.2 i) (univ.pi S ×ˢ univ) := by
  simp_rw [altCost_def]
  exact task.continuousOn_biInf_cost_pi hν hk hk_compact h_alt

/-- **Continuity of the value of the game on a product model** [DK19, Lemmas 27, 29]. For
finitely many answers, under the hypotheses of `continuousOn_biInf_cost_pi`, if the admissible
models are models of `∏ a, S a`, then the value `θ ↦ D(θ)` of the game is continuous on the
admissible models. -/
theorem continuousOn_gameValue_pi [Finite ℐ]
    (hν : ∀ θ ∈ univ.pi S, ∀ θ' ∈ univ.pi S, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a (θ a) (θ' a)))
    (hk : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k a p.1 p.2) (S a ×ˢ S a))
    (hk_compact : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ,
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, k a x' y ≤ r → y ∈ K)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.gameValue task.M := fun θ hθ ↦
  task.continuousWithinAt_gameValue subset_rfl hθ fun i w hw ↦
    ((task.continuousOn_altCost_pi hν hk hk_compact ((task.alt_subset_M i).trans hM)).mono
      (prod_mono hM (subset_univ _))) (θ, w) ⟨hθ, hw⟩

/-- **Continuity of the characteristic time on a product model** [DK19, Lemmas 27, 29]:
under the hypotheses of `continuousOn_gameValue_pi`, the characteristic time `θ ↦ T*(θ)` is
continuous on the admissible models. -/
theorem continuousOn_charTime_pi [Finite ℐ]
    (hν : ∀ θ ∈ univ.pi S, ∀ θ' ∈ univ.pi S, ∀ a,
      klDiv (task.ν θ a) (task.ν θ' a) = ENNReal.ofReal (k a (θ a) (θ' a)))
    (hk : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ k a p.1 p.2) (S a ×ˢ S a))
    (hk_compact : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ,
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, k a x' y ≤ r → y ∈ K)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.charTime task.M := fun θ hθ ↦
  task.continuousWithinAt_charTime subset_rfl hθ fun i w hw ↦
    ((task.continuousOn_altCost_pi hν hk hk_compact ((task.alt_subset_M i).trans hM)).mono
      (prod_mono hM (subset_univ _))) (θ, w) ⟨hθ, hw⟩

end IdentTask

end LMLExplore.Identification
