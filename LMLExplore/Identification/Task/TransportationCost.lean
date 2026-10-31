/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

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
the set `simplex α`. It is stated directly on `α → ℝ`, with the topology and the order of that
space: Mathlib's set `stdSimplex` is deprecated, and its replacement `Convexity.StdSimplex` is a
type of finitely supported distributions, not a subset of `α → ℝ`. The costs are `ℝ≥0∞`-valued, so
that models at infinite divergence and empty sets of alternatives need no special treatment, and a
negative entry of `w` counts as `0`.

## Main definitions

* `LMLExplore.Identification.simplex α`: the allocations `w : α → ℝ`, nonnegative and summing
  to `1`.
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
* `IdentTask.convex_optAlloc`: the optimal allocations of an answer form a convex set.
* `IdentTask.altCost_eq_zero_of_mem_alt`, `IdentTask.answerValue_eq_zero_of_mem_alt`: the cost
  and the value of the answer `i` vanish at an alternative `θ ∈ ¬i`.
* `IdentTask.answerValue_eq_top_of_alt_eq_empty`: the value of an answer without alternatives is
  `∞`.
* `IdentTask.charTime_lt_top_iff`: `T*(θ) < ∞` iff some correct answer of `θ` has alternatives at
  positive cost for some allocation.
* `IdentTask.gameValue_eq_answerValue`: for a model with a single correct answer `i`,
  `D(θ) = D(θ, ¬i)`.
* `IdentTask.charTime_restrict_le`: restricting the admissible models can only decrease the
  characteristic time.

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

/-! ### Allocations -/

variable (α) in
/-- The allocations of samples to the arms `α`: vectors `w : α → ℝ` with nonnegative entries
summing to `1`. -/
def simplex : Set (α → ℝ) := {w | (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

@[simp]
lemma mem_simplex_iff {w : α → ℝ} : w ∈ simplex α ↔ (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := Iff.rfl

lemma simplex_subset_nonneg : simplex α ⊆ Set.Ici 0 := fun _ hw ↦ hw.1

variable (α) in
lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  classical
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨Pi.single a 1, fun b ↦ by by_cases h : b = a <;> simp [h], by simp⟩

variable (α) in
lemma convex_simplex : Convex ℝ (simplex α) := by
  intro w hw v hv a b ha hb hab
  refine ⟨fun x ↦ ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hw.1 x)) (mul_nonneg hb (hv.1 x))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hv.2, hab]

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

end IdentTask

end LMLExplore.Identification
