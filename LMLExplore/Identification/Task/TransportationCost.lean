/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Identification.Task.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.NNReal
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Transportation costs and the characteristic time of an identification task

An algorithm that samples the arms of the model `θ` with proportions `w` (an *allocation*)
collects, per round, the information `cost_θ(w, λ) = ∑ a, w a KL(ν_a(θ), ν_a(λ))` against the
model `λ`. To answer `i` with confidence it has to rule out every alternative `λ ∈ ¬i`, and the
cheapest of them costs `D(θ, w, ¬i) = inf_{λ ∈ ¬i} cost_θ(w, λ)` per round. This file defines
these *transportation costs* and the value of the *pure exploration game* built on them:
`D(θ, ¬i) = sup_{w ∈ Δ_K} D(θ, w, ¬i)`, `D(θ) = sup_{i ∈ i*(θ)} D(θ, ¬i)` and the
*characteristic time* `T*(θ) = D(θ)⁻¹`. The characteristic time is the constant of the lower bound
`E_θ[τ] ≥ T*(θ) kl(δ, 1 - δ)` of Garivier and Kaufmann (2016) for `δ`-correct algorithms, and of
the matching upper bounds of asymptotically optimal algorithms such as Track-and-Stop. Degenne and
Koolen (2019) extend these definitions to tasks with several correct answers.

Allocations are vectors `w : α → ℝ`; the allocations with nonnegative entries summing to `1` form
the probability simplex `simplex α` (`LMLExplore/Analysis/Convex/Simplex.lean`). The costs are
`ℝ≥0∞`-valued, so that models at infinite divergence and empty sets of alternatives need no special
treatment, and a negative entry of `w` counts as `0`.

## Main definitions

* `IdentTask.cost task w θ λ`: the transportation cost `∑ a, w a KL(ν_a(θ), ν_a(λ))`.
* `IdentTask.altCost task θ w i`: the cost `D(θ, w, ¬i)` of the alternatives to `i`.
* `IdentTask.answerValue task θ i`: the value `D(θ, ¬i)` of the game of the answer `i`.
* `IdentTask.gameValue task θ`: the value `D(θ)`, the supremum of `D(θ, ¬i)` over the correct
  answers.
* `IdentTask.charTime task θ`: the characteristic time `T*(θ) = D(θ)⁻¹`.
* `IdentTask.optAlloc task θ i`: the optimal allocations `w*(θ, ¬i)` of the answer `i`.

## Main statements

* `IdentTask.concaveOn_altCost`, `IdentTask.altCost_smul`, `IdentTask.monotone_altCost`: on
  nonnegative allocations, `w ↦ D(θ, w, ¬i)` is concave, positively homogeneous and monotone.
* `IdentTask.altCost_le_altCost_of_alt_subset`: `D(θ, w, ¬i)` is antitone in the set of
  alternatives.
* `IdentTask.cost_le_iSup_klDiv`: for an allocation, the transportation cost is at most the
  largest divergence between the arm laws.
* `IdentTask.exists_pos_mem_simplex_mul_cost_le`: mixing an allocation with the uniform one gives
  an allocation with positive entries that keeps a fraction `c < 1` of every transportation cost.
* `IdentTask.iSup_pos_iInf_cost_eq`: the supremum over the positive allocations of the cost of a
  set of models is its supremum over the simplex.
* `IdentTask.altCost_eq_biInf_of_subset_closure`: if the transportation cost is continuous in
  the alternative model, `D(θ, w, ¬i)` is also the infimum of the cost over any set between `¬i`
  and its closure.
* `IdentTask.mem_optAlloc_iff_isMaxOn`: the optimal allocations are the maximizers of
  `w ↦ D(θ, w, ¬i)` on the simplex.
* `IdentTask.convex_optAlloc`: the optimal allocations of an answer form a convex set.
* `IdentTask.answerValue_eq_of_altCost_eq_iInf`, `IdentTask.optAlloc_eq_of_altCost_eq_iInf`: if
  `D(θ, w, ¬i) = min_a w a c a` on the simplex for positive weights `c`, then
  `D(θ, ¬i) = (∑ a, (c a)⁻¹)⁻¹` and the only optimal allocation is proportional to `c⁻¹`.
* `IdentTask.altCost_eq_zero_of_mem_alt`, `IdentTask.answerValue_eq_zero_of_mem_alt`: the cost
  and the value of the answer `i` vanish at an alternative `θ ∈ ¬i`.
* `IdentTask.answerValue_eq_top_of_alt_eq_empty`: the value of an answer without alternatives is
  `∞`.
* `IdentTask.charTime_lt_top_iff`: `T*(θ) < ∞` iff some correct answer of `θ` has alternatives at
  positive cost for some allocation.
* `IdentTask.gameValue_eq_answerValue`: for a model with a single correct answer `i`,
  `D(θ) = D(θ, ¬i)`.
* `IdentTask.gameValue_eq_iSup_answerValue`: on an admissible model, `D(θ)` is the supremum of
  `D(θ, ¬i)` over all answers.
* `IdentTask.charTime_restrict_le`: restricting the admissible models can only decrease the
  characteristic time.
* `IdentTask.answerValue_restrict_setOf_klDiv_ne_top`: removing the models at infinite divergence
  from `θ` on some arm does not change `D(θ, ¬i)`.
* `IdentTask.cost_comap`, `IdentTask.altCost_le_altCost_comap`,
  `IdentTask.charTime_comap_le`: the costs of a pullback `task.comap f` are the costs of the images
  under `f`, so its cost of the alternatives is at least that of the task at the image and its
  characteristic time at most that of the task at the image.
* `IdentTask.altCost_comap_of_alt_subset_range`, `IdentTask.charTime_comap_of_alt_subset_range`:
  these are equalities when the range of `f` contains the alternatives.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} [Fintype α]

/-! ### Transportation costs -/

namespace IdentTask

variable {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} (task : IdentTask α Θ ℐ 𝓨)
  {θ θ' : Θ} {i j : ℐ} {w v : α → ℝ}

/-- The transportation cost `∑ a, w a KL(ν_a(θ), ν_a(θ'))` from the model `θ` to the model `θ'`
with the allocation `w`: the information against `θ'` collected per round by sampling the arms of
`θ` with proportions `w`. A negative entry of `w` counts as `0`. -/
noncomputable def cost (w : α → ℝ) (θ θ' : Θ) : ℝ≥0∞ :=
  ∑ a, ENNReal.ofReal (w a) * klDiv (task.ν θ a) (task.ν θ' a)

/-- The cost `D(θ, w, ¬i)` of the alternatives to the answer `i`: the smallest transportation
cost from `θ` to a model for which `i` is not correct. It is `∞` if there is no such model. -/
noncomputable def altCost (θ : Θ) (w : α → ℝ) (i : ℐ) : ℝ≥0∞ :=
  ⨅ θ' ∈ task.alt i, task.cost w θ θ'

/-- The value `D(θ, ¬i)` of the pure exploration game of the answer `i` at the model `θ`: the
supremum over the allocations of the cost of the alternatives to `i`. -/
noncomputable def answerValue (θ : Θ) (i : ℐ) : ℝ≥0∞ :=
  ⨆ w ∈ simplex α, task.altCost θ w i

/-- The value `D(θ) = sup_{i ∈ i*(θ)} D(θ, ¬i)` of the pure exploration game at the model `θ`, the
supremum over the correct answers of `θ`. -/
noncomputable def gameValue (θ : Θ) : ℝ≥0∞ :=
  ⨆ i ∈ task.correct θ, task.answerValue θ i

/-- The characteristic time `T*(θ) = D(θ)⁻¹` of the model `θ`. -/
noncomputable def charTime (θ : Θ) : ℝ≥0∞ := (task.gameValue θ)⁻¹

/-- The optimal allocations `w*(θ, ¬i)` of the answer `i` at the model `θ`: the allocations at
which the cost of the alternatives to `i` attains the value `D(θ, ¬i)`. -/
def optAlloc (θ : Θ) (i : ℐ) : Set (α → ℝ) :=
  {w | w ∈ simplex α ∧ task.altCost θ w i = task.answerValue θ i}

lemma cost_def (w : α → ℝ) (θ θ' : Θ) :
    task.cost w θ θ' = ∑ a, ENNReal.ofReal (w a) * klDiv (task.ν θ a) (task.ν θ' a) := (rfl)

lemma altCost_def (θ : Θ) (w : α → ℝ) (i : ℐ) :
    task.altCost θ w i = ⨅ θ' ∈ task.alt i, task.cost w θ θ' := (rfl)

lemma answerValue_def (θ : Θ) (i : ℐ) :
    task.answerValue θ i = ⨆ w ∈ simplex α, task.altCost θ w i := (rfl)

lemma gameValue_def (θ : Θ) : task.gameValue θ = ⨆ i ∈ task.correct θ, task.answerValue θ i :=
  (rfl)

lemma charTime_def (θ : Θ) : task.charTime θ = (task.gameValue θ)⁻¹ := (rfl)

@[simp]
lemma mem_optAlloc_iff :
    w ∈ task.optAlloc θ i ↔ w ∈ simplex α ∧ task.altCost θ w i = task.answerValue θ i := Iff.rfl

/-! #### The transportation cost -/

@[simp]
lemma cost_self (w : α → ℝ) (θ : Θ) : task.cost w θ θ = 0 := by
  simp [cost_def, klDiv_self]

@[simp]
lemma cost_zero (θ θ' : Θ) : task.cost 0 θ θ' = 0 := by
  simp [cost_def]

/-- The transportation cost is additive in nonnegative allocations. -/
lemma cost_add (hw : 0 ≤ w) (hv : 0 ≤ v) (θ θ' : Θ) :
    task.cost (w + v) θ θ' = task.cost w θ θ' + task.cost v θ θ' := by
  simp only [cost_def, Pi.add_apply, ← Finset.sum_add_distrib, ← add_mul]
  congr! 2 with a
  exact ENNReal.ofReal_add (hw a) (hv a)

/-- The transportation cost is positively homogeneous in the allocation. -/
lemma cost_smul (c : ℝ≥0) (w : α → ℝ) (θ θ' : Θ) :
    task.cost (c • w) θ θ' = c • task.cost w θ θ' := by
  simp only [cost_def, Pi.smul_apply, NNReal.smul_def, smul_eq_mul, ENNReal.smul_def,
    Finset.mul_sum, ← mul_assoc]
  congr! 2 with a
  rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]

lemma monotone_cost (θ θ' : Θ) : Monotone fun w ↦ task.cost w θ θ' := fun _ _ hwv ↦
  Finset.sum_le_sum fun a _ ↦ by gcongr; exact hwv a

/-- For an allocation `w` and `c < 1`, the mixture `c w + (1 - c) u` with the uniform allocation
`u` is an allocation with positive entries, at which every transportation cost is at least `c`
times its value at `w`. -/
lemma exists_pos_mem_simplex_mul_cost_le (hw : w ∈ simplex α) {c : ℝ≥0∞} (hc : c < 1) :
    ∃ w' ∈ simplex α, (∀ a, 0 < w' a) ∧ ∀ θ θ', c * task.cost w θ θ' ≤ task.cost w' θ θ' := by
  have : Nonempty α := nonempty_of_mem_simplex hw
  lift c to ℝ≥0 using hc.ne_top
  have hc1 : (c : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.1 hc
  set u : α → ℝ := fun _ ↦ (Fintype.card α : ℝ)⁻¹
  refine ⟨(c : ℝ) • w + (1 - (c : ℝ)) • u,
    convex_simplex α hw (uniform_mem_simplex α) c.2 (sub_nonneg.2 hc1.le) (add_sub_cancel _ _),
    fun a ↦ add_pos_of_nonneg_of_pos (mul_nonneg c.2 ((mem_simplex_iff.1 hw).1 a))
      (mul_pos (sub_pos.2 hc1) (by positivity)), fun θ θ' ↦ ?_⟩
  calc (c : ℝ≥0∞) * task.cost w θ θ' = task.cost (c • w) θ θ' := by
        rw [cost_smul, ENNReal.smul_def, smul_eq_mul]
    _ ≤ task.cost ((c : ℝ) • w + (1 - (c : ℝ)) • u) θ θ' := task.monotone_cost θ θ' fun a ↦ by
        simpa [u, NNReal.smul_def] using mul_nonneg (sub_pos.2 hc1).le (by positivity : 0 ≤ u a)

/-- The supremum of `w ↦ inf_{λ ∈ s} ∑ a, w a KL(ν_a(λ), ν_a(θ))` over the allocations with
positive entries is its supremum over the simplex, for every set `s` of models. -/
lemma iSup_pos_iInf_cost_eq (s : Set Θ) (θ : Θ) :
    ⨆ (w ∈ simplex α) (_ : ∀ a, 0 < w a), ⨅ θ' ∈ s, task.cost w θ' θ =
      ⨆ w ∈ simplex α, ⨅ θ' ∈ s, task.cost w θ' θ := by
  refine le_antisymm (iSup₂_mono fun w _ ↦ iSup_le fun _ ↦ le_rfl) (iSup₂_le fun w hw ↦ ?_)
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
  obtain ⟨w', hw', hpos, hle⟩ := task.exists_pos_mem_simplex_mul_cost_le hw hc
  refine le_iSup₂_of_le w' hw' (le_iSup_of_le hpos (le_iInf₂ fun θ' hθ' ↦ ?_))
  calc c * ⨅ θ' ∈ s, task.cost w θ' θ ≤ c * task.cost w θ' θ := by
        gcongr
        exact iInf₂_le θ' hθ'
    _ ≤ task.cost w' θ' θ := hle θ' θ

/-- For an allocation `w`, the transportation cost from `θ` to `θ'` is at most the largest
divergence `max_a KL(ν_a(θ), ν_a(θ'))` between the arm laws. -/
lemma cost_le_iSup_klDiv (hw : w ∈ simplex α) (θ θ' : Θ) :
    task.cost w θ θ' ≤ ⨆ a, klDiv (task.ν θ a) (task.ν θ' a) :=
  sum_ofReal_mul_le_iSup hw _

/-- An allocation that samples an arm `a` pays an infinite transportation cost to a model at
infinite divergence from `θ` on `a`. -/
lemma cost_eq_top_of_klDiv_eq_top {a : α} (hw : 0 < w a)
    (h : klDiv (task.ν θ a) (task.ν θ' a) = ∞) : task.cost w θ θ' = ∞ := by
  refine top_unique ?_
  calc ∞ = ENNReal.ofReal (w a) * klDiv (task.ν θ a) (task.ν θ' a) := by
        rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hw).ne']
    _ ≤ task.cost w θ θ' := by
        rw [cost_def]
        exact Finset.single_le_sum
          (f := fun b ↦ ENNReal.ofReal (w b) * klDiv (task.ν θ b) (task.ν θ' b))
          (fun _ _ ↦ zero_le) (Finset.mem_univ a)

/-! #### The cost of the alternatives -/

lemma altCost_le_cost (hθ' : θ' ∈ task.alt i) (w : α → ℝ) :
    task.altCost θ w i ≤ task.cost w θ θ' :=
  iInf₂_le θ' hθ'

/-- The cost of the alternatives to `i` vanishes at an alternative to `i`. -/
lemma altCost_eq_zero_of_mem_alt (hθ : θ ∈ task.alt i) (w : α → ℝ) : task.altCost θ w i = 0 :=
  nonpos_iff_eq_zero.1 <| (task.altCost_le_cost hθ w).trans_eq (task.cost_self w θ)

/-- The cost of the alternatives is antitone in the set of alternatives. -/
lemma altCost_le_altCost_of_alt_subset (h : task.alt i ⊆ task.alt j) (θ : Θ) (w : α → ℝ) :
    task.altCost θ w j ≤ task.altCost θ w i :=
  biInf_mono h

lemma monotone_altCost (θ : Θ) (i : ℐ) : Monotone fun w ↦ task.altCost θ w i := fun _ _ hwv ↦
  iInf₂_mono fun θ' _ ↦ task.monotone_cost θ θ' hwv

/-- The cost of the alternatives is positively homogeneous in the allocation. The scalar must be
nonzero: if `i` has no alternative, `D(θ, w, ¬i) = ∞` for every `w`. -/
lemma altCost_smul {c : ℝ≥0} (hc : c ≠ 0) (θ : Θ) (w : α → ℝ) (i : ℐ) :
    task.altCost θ (c • w) i = c • task.altCost θ w i := by
  have h0 : (c : ℝ≥0∞) ≠ 0 := by simpa using hc
  simp_rw [altCost_def, cost_smul, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_iInf_of_ne h0 ENNReal.coe_ne_top]

/-- The cost of the alternatives is concave in the allocation on the nonnegative allocations:
it is an infimum of costs, which are additive and positively homogeneous there. -/
theorem concaveOn_altCost (θ : Θ) (i : ℐ) :
    ConcaveOn ℝ≥0 (Set.Ici 0) fun w ↦ task.altCost θ w i := by
  refine ⟨NNReal.convex_iff.2 (convex_Ici 0), fun w hw v hv a b _ _ _ ↦ ?_⟩
  have hw' : 0 ≤ a • w := smul_nonneg a.2 hw
  have hv' : 0 ≤ b • v := smul_nonneg b.2 hv
  refine le_iInf₂ fun θ' hθ' ↦ ?_
  rw [task.cost_add hw' hv', task.cost_smul, task.cost_smul]
  gcongr <;> exact task.altCost_le_cost hθ' _

/-! #### Continuity in the alternative model -/

section Topology

variable [TopologicalSpace Θ] {s : Set Θ}

/-- The transportation cost is continuous in the alternative model on a set where each of the
divergences `KL(ν_a(θ), ν_a(λ))` is. -/
lemma continuousOn_cost (h : ∀ a, ContinuousOn (fun θ' ↦ klDiv (task.ν θ a) (task.ν θ' a)) s)
    (w : α → ℝ) : ContinuousOn (task.cost w θ) s := by
  refine (continuousOn_finsetSum _ fun a _ ↦ ?_).congr fun θ' _ ↦ task.cost_def w θ θ'
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn (h a)

/-- The cost of the alternatives to `i` is the infimum of the transportation cost over any set `s`
between these alternatives and their closure, on which the cost is continuous: alternatives can be
replaced by their limits. -/
theorem altCost_eq_biInf_of_subset_closure (h_alt : task.alt i ⊆ s)
    (h_closure : s ⊆ closure (task.alt i)) (hc : ContinuousOn (task.cost w θ) s) :
    task.altCost θ w i = ⨅ θ' ∈ s, task.cost w θ θ' := by
  refine le_antisymm (le_iInf₂ fun θ' hθ' ↦ ?_) (biInf_mono h_alt)
  have h_maps : Set.MapsTo (task.cost w θ) (task.alt i) (Set.Ici (task.altCost θ w i)) :=
    fun θ'' hθ'' ↦ task.altCost_le_cost hθ'' w
  simpa [closure_Ici] using ((hc θ' hθ').mono h_alt).mem_closure (h_closure hθ') h_maps

end Topology

/-! #### The value of the game and the characteristic time -/

lemma altCost_le_answerValue (hw : w ∈ simplex α) : task.altCost θ w i ≤ task.answerValue θ i :=
  le_iSup₂ (f := fun w (_ : w ∈ simplex α) ↦ task.altCost θ w i) w hw

lemma answerValue_le_gameValue (hi : i ∈ task.correct θ) :
    task.answerValue θ i ≤ task.gameValue θ :=
  le_iSup₂ (f := fun i (_ : i ∈ task.correct θ) ↦ task.answerValue θ i) i hi

/-- The value of the game of the answer `i` vanishes at an alternative to `i`. -/
lemma answerValue_eq_zero_of_mem_alt (hθ : θ ∈ task.alt i) : task.answerValue θ i = 0 := by
  simp [answerValue_def, task.altCost_eq_zero_of_mem_alt hθ]

/-- The value of the game of an answer without alternatives is `∞`. -/
lemma answerValue_eq_top_of_alt_eq_empty [Nonempty α] (h : task.alt i = ∅) (θ : Θ) :
    task.answerValue θ i = ∞ := by
  obtain ⟨w, hw⟩ := simplex_nonempty α
  refine top_unique ?_
  calc ∞ = task.altCost θ w i := by simp [altCost_def, h]
    _ ≤ task.answerValue θ i := task.altCost_le_answerValue hw

/-- The value of the game of the answer `i` is antitone in the set of alternatives. -/
lemma answerValue_le_answerValue_of_alt_subset (h : task.alt i ⊆ task.alt j) (θ : Θ) :
    task.answerValue θ j ≤ task.answerValue θ i :=
  iSup₂_mono fun w _ ↦ task.altCost_le_altCost_of_alt_subset h θ w

/-- The optimal allocations of an answer form a convex set: they are a superlevel set of the
concave function `w ↦ D(θ, w, ¬i)` on the simplex. -/
theorem convex_optAlloc (θ : Θ) (i : ℐ) : Convex ℝ (task.optAlloc θ i) := by
  have h : task.optAlloc θ i = {w ∈ simplex α | task.answerValue θ i ≤ task.altCost θ w i} := by
    ext w
    exact and_congr_right fun hw ↦ ⟨fun h ↦ h.ge, (task.altCost_le_answerValue hw).antisymm⟩
  rw [h, ← NNReal.convex_iff]
  exact ((task.concaveOn_altCost θ i).subset simplex_subset_nonneg
    (NNReal.convex_iff.2 (convex_simplex α))).convex_ge _

/-- The optimal allocations of the answer `i` at `θ` are the maximizers of the cost
`w ↦ D(θ, w, ¬i)` of the alternatives on the simplex. -/
lemma mem_optAlloc_iff_isMaxOn :
    w ∈ task.optAlloc θ i ↔ w ∈ simplex α ∧ IsMaxOn (task.altCost θ · i) (simplex α) w := by
  rw [mem_optAlloc_iff, isMaxOn_iff]
  refine and_congr_right fun hw ↦ ⟨fun h v hv ↦ h ▸ task.altCost_le_answerValue hv, fun h ↦ ?_⟩
  refine (task.altCost_le_answerValue hw).antisymm ?_
  rw [answerValue_def]
  exact iSup₂_le h

/-- **The game value of a weighted minimum.** If `D(θ, w, ¬i) = min_a w a c a` on the simplex, for
positive weights `c`, then `D(θ, ¬i) = (∑ a, (c a)⁻¹)⁻¹`. -/
lemma answerValue_eq_of_altCost_eq_iInf [Nonempty α] {c : α → ℝ} (hc : ∀ a, 0 < c a)
    (h : ∀ w ∈ simplex α, task.altCost θ w i = ⨅ a, ENNReal.ofReal (w a * c a)) :
    task.answerValue θ i = ENNReal.ofReal (∑ a, (c a)⁻¹)⁻¹ := by
  have hv := inv_div_sum_inv_mem_simplex hc
  rw [answerValue_def]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · obtain ⟨a, ha⟩ := exists_mul_le_inv_sum_inv hw hc
    rw [h w hw]
    exact (iInf_le _ a).trans (ENNReal.ofReal_le_ofReal ha)
  · refine le_of_eq_of_le ?_ (le_iSup₂ (f := fun w _ ↦ task.altCost θ w i) _ hv)
    rw [h _ hv, iInf_ofReal_inv_div_sum_inv_mul hc]

/-- **The optimal allocation of a weighted minimum.** If `D(θ, w, ¬i) = min_a w a c a` on the
simplex, for positive weights `c`, then the only optimal allocation is proportional to `c⁻¹`. -/
lemma optAlloc_eq_of_altCost_eq_iInf [Nonempty α] {c : α → ℝ} (hc : ∀ a, 0 < c a)
    (h : ∀ w ∈ simplex α, task.altCost θ w i = ⨅ a, ENNReal.ofReal (w a * c a)) :
    task.optAlloc θ i = {fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹} := by
  have hv := inv_div_sum_inv_mem_simplex hc
  ext v
  rw [mem_optAlloc_iff, Set.mem_singleton_iff, task.answerValue_eq_of_altCost_eq_iInf hc h]
  refine ⟨fun ⟨hv', hv_eq⟩ ↦ eq_inv_div_sum_inv_of_le_mul hv' hc fun a ↦ ?_, ?_⟩
  · rw [h v hv'] at hv_eq
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ((mem_simplex_iff.1 hv').1 a) (hc a).le)).1
      (hv_eq ▸ iInf_le _ a)
  · rintro rfl
    exact ⟨hv, by rw [h _ hv, iInf_ofReal_inv_div_sum_inv_mul hc]⟩

/-- On an admissible model, the value `D(θ)` of the game is the supremum of the values
`D(θ, ¬i)` over all answers: those of the incorrect answers vanish. -/
lemma gameValue_eq_iSup_answerValue (hθ : θ ∈ task.M) :
    task.gameValue θ = ⨆ i, task.answerValue θ i := by
  rw [gameValue_def]
  refine le_antisymm (iSup₂_le fun i _ ↦ le_iSup (task.answerValue θ ·) i) (iSup_le fun i ↦ ?_)
  by_cases hi : i ∈ task.correct θ
  · exact le_iSup₂ (f := fun i (_ : i ∈ task.correct θ) ↦ task.answerValue θ i) i hi
  · rw [task.answerValue_eq_zero_of_mem_alt (task.mem_alt_iff.2 ⟨hθ, hi⟩)]
    exact bot_le

/-- For a model with a single correct answer `i`, `D(θ) = D(θ, ¬i)`. -/
lemma gameValue_eq_answerValue (h : task.correct θ = {i}) :
    task.gameValue θ = task.answerValue θ i := by
  simp [gameValue_def, h]

/-- For a model with a single correct answer `i`, `T*(θ) = D(θ, ¬i)⁻¹`. -/
lemma charTime_eq_inv_answerValue (h : task.correct θ = {i}) :
    task.charTime θ = (task.answerValue θ i)⁻¹ := by
  rw [charTime_def, task.gameValue_eq_answerValue h]

lemma charTime_lt_top_iff_gameValue_pos : task.charTime θ < ∞ ↔ 0 < task.gameValue θ := by
  rw [charTime_def, ENNReal.inv_lt_top]

/-- The characteristic time of `θ` is finite iff some correct answer of `θ` has alternatives at
positive cost for some allocation. -/
theorem charTime_lt_top_iff : task.charTime θ < ∞ ↔
    ∃ i ∈ task.correct θ, ∃ w ∈ simplex α, 0 < task.altCost θ w i := by
  simp [charTime_lt_top_iff_gameValue_pos, gameValue_def, answerValue_def, lt_iSup_iff]

/-! #### Restriction of the admissible models -/

variable {S : Set Θ}

@[simp]
lemma cost_restrict : (task.restrict S).cost = task.cost := by
  ext w θ θ'
  simp [cost_def]

lemma altCost_restrict (θ : Θ) (w : α → ℝ) (i : ℐ) :
    (task.restrict S).altCost θ w i = ⨅ θ' ∈ task.alt i ∩ S, task.cost w θ θ' := by
  rw [altCost_def, alt_restrict, cost_restrict]

/-- Restricting the admissible models removes alternatives, so it can only increase their cost. -/
lemma altCost_le_altCost_restrict (S : Set Θ) (θ : Θ) (w : α → ℝ) (i : ℐ) :
    task.altCost θ w i ≤ (task.restrict S).altCost θ w i := by
  rw [altCost_restrict]
  exact biInf_mono Set.inter_subset_left

lemma answerValue_le_answerValue_restrict (S : Set Θ) (θ : Θ) (i : ℐ) :
    task.answerValue θ i ≤ (task.restrict S).answerValue θ i :=
  iSup₂_mono fun w _ ↦ task.altCost_le_altCost_restrict S θ w i

lemma gameValue_le_gameValue_restrict (S : Set Θ) (θ : Θ) :
    task.gameValue θ ≤ (task.restrict S).gameValue θ := by
  rw [gameValue_def, gameValue_def, correct_restrict]
  exact iSup₂_mono fun i _ ↦ task.answerValue_le_answerValue_restrict S θ i

/-- Restricting the admissible models can only decrease the characteristic time. -/
lemma charTime_restrict_le (S : Set Θ) (θ : Θ) :
    (task.restrict S).charTime θ ≤ task.charTime θ :=
  ENNReal.inv_le_inv.2 (task.gameValue_le_gameValue_restrict S θ)

/-- For an allocation with positive entries, removing the models at infinite divergence from `θ`
on some arm does not change the cost of the alternatives: they cost `∞`. -/
lemma altCost_restrict_setOf_klDiv_ne_top (hw : ∀ a, 0 < w a) (θ : Θ) (i : ℐ) :
    (task.restrict {θ' | ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞}).altCost θ w i =
      task.altCost θ w i := by
  refine le_antisymm ?_ (task.altCost_le_altCost_restrict _ θ w i)
  rw [altCost_restrict, task.altCost_def]
  refine le_iInf₂ fun θ' hθ' ↦ ?_
  by_cases hfin : ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞
  · exact iInf₂_le θ' ⟨hθ', hfin⟩
  · obtain ⟨a, ha⟩ := not_forall_not.1 hfin
    rw [task.cost_eq_top_of_klDiv_eq_top (hw a) ha]
    exact le_top

/-- Removing the models at infinite divergence from `θ` on some arm does not change the value
`D(θ, ¬i)`: the allocations with positive entries approach the value, and against them these
models cost `∞`. -/
lemma answerValue_restrict_setOf_klDiv_ne_top (θ : Θ) (i : ℐ) :
    (task.restrict {θ' | ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞}).answerValue θ i =
      task.answerValue θ i := by
  set S := {θ' | ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞}
  refine le_antisymm ?_ (task.answerValue_le_answerValue_restrict S θ i)
  rw [answerValue_def]
  refine iSup₂_le fun w hw ↦ ?_
  -- Compare `w` with the allocations `w' = t w + (1 - t) u`, for `u` uniform and `t < 1`.
  refine ENNReal.le_of_forall_lt_one_mul_le fun t ht ↦ ?_
  obtain ⟨w', hw', hpos, hle⟩ := (task.restrict S).exists_pos_mem_simplex_mul_cost_le hw ht
  calc t * (task.restrict S).altCost θ w i ≤ (task.restrict S).altCost θ w' i :=
        le_iInf₂ fun θ' hθ' ↦
          (mul_le_mul_right ((task.restrict S).altCost_le_cost hθ' w) t).trans (hle θ θ')
    _ = task.altCost θ w' i := task.altCost_restrict_setOf_klDiv_ne_top hpos θ i
    _ ≤ task.answerValue θ i := task.altCost_le_answerValue hw'

/-! #### Pullback along a map of models -/

variable {Θ' : Type*} {f : Θ' → Θ}

/-- The transportation cost between two models of a pullback is the cost between their images. -/
@[simp]
lemma cost_comap (w : α → ℝ) (θ θ' : Θ') :
    (task.comap f).cost w θ θ' = task.cost w (f θ) (f θ') := by
  simp [cost_def]

/-- The cost of the alternatives to `i` in a pullback is the infimum of the costs to the images
of the preimages of the alternatives to `i`. -/
lemma altCost_comap (θ : Θ') (w : α → ℝ) (i : ℐ) :
    (task.comap f).altCost θ w i = ⨅ θ' ∈ f ⁻¹' task.alt i, task.cost w (f θ) (f θ') := by
  simp only [altCost_def, alt_comap, cost_comap]

/-- The alternatives of a pullback are mapped into the alternatives of the task, so the cost of
the alternatives at `θ` is at least the cost of the alternatives of the task at `f θ`. -/
lemma altCost_le_altCost_comap (θ : Θ') (w : α → ℝ) (i : ℐ) :
    task.altCost (f θ) w i ≤ (task.comap f).altCost θ w i := by
  rw [altCost_comap, ← iInf_image (g := task.cost w (f θ))]
  exact biInf_mono (Set.image_preimage_subset f _)

/-- If every alternative to `i` is the image of a model under `f`, the cost of the alternatives
to `i` in the pullback is that of the task at the image. -/
lemma altCost_comap_of_alt_subset_range (h : task.alt i ⊆ Set.range f) (θ : Θ') (w : α → ℝ) :
    (task.comap f).altCost θ w i = task.altCost (f θ) w i := by
  rw [altCost_comap, ← iInf_image (g := task.cost w (f θ)), Set.image_preimage_eq_of_subset h,
    altCost_def]

/-- The value of the game of an answer in a pullback is at least that of the task at the image. -/
lemma answerValue_le_answerValue_comap (θ : Θ') (i : ℐ) :
    task.answerValue (f θ) i ≤ (task.comap f).answerValue θ i :=
  iSup₂_mono fun w _ ↦ task.altCost_le_altCost_comap θ w i

/-- If every alternative to `i` is the image of a model under `f`, the value of the game of `i`
in the pullback is that of the task at the image. -/
lemma answerValue_comap_of_alt_subset_range (h : task.alt i ⊆ Set.range f) (θ : Θ') :
    (task.comap f).answerValue θ i = task.answerValue (f θ) i := by
  simp only [answerValue_def, task.altCost_comap_of_alt_subset_range h]

/-- The value of the game of a pullback is at least that of the task at the image: the correct
answers are the same, and each has fewer alternatives. -/
lemma gameValue_le_gameValue_comap (θ : Θ') :
    task.gameValue (f θ) ≤ (task.comap f).gameValue θ := by
  rw [gameValue_def, gameValue_def, correct_comap]
  exact iSup₂_mono fun i _ ↦ task.answerValue_le_answerValue_comap θ i

/-- If, for every correct answer of `f θ`, every alternative is the image of a model under `f`,
the value of the game of the pullback at `θ` is that of the task at `f θ`. -/
lemma gameValue_comap_of_alt_subset_range {θ : Θ'}
    (h : ∀ i ∈ task.correct (f θ), task.alt i ⊆ Set.range f) :
    (task.comap f).gameValue θ = task.gameValue (f θ) := by
  rw [gameValue_def, gameValue_def, correct_comap]
  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ task.answerValue_comap_of_alt_subset_range (h i hi) θ

/-- The characteristic time of a pullback is at most that of the task at the image: the
pullback has fewer alternatives. -/
lemma charTime_comap_le (θ : Θ') : (task.comap f).charTime θ ≤ task.charTime (f θ) :=
  ENNReal.inv_le_inv.2 (task.gameValue_le_gameValue_comap θ)

/-- If, for every correct answer of `f θ`, every alternative is the image of a model under `f`,
the characteristic time of the pullback at `θ` is that of the task at `f θ`. -/
lemma charTime_comap_of_alt_subset_range {θ : Θ'}
    (h : ∀ i ∈ task.correct (f θ), task.alt i ⊆ Set.range f) :
    (task.comap f).charTime θ = task.charTime (f θ) := by
  rw [charTime_def, charTime_def, task.gameValue_comap_of_alt_subset_range h]

/-- If every alternative to `i` is the image of a model under `f`, the optimal allocations of `i`
in the pullback at `θ` are those of the task at `f θ`. -/
lemma optAlloc_comap_of_alt_subset_range (h : task.alt i ⊆ Set.range f) (θ : Θ') :
    (task.comap f).optAlloc θ i = task.optAlloc (f θ) i := by
  ext w
  simp only [mem_optAlloc_iff, task.altCost_comap_of_alt_subset_range h,
    task.answerValue_comap_of_alt_subset_range h]

end IdentTask

end LMLExplore.Identification
