/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Topology.Semicontinuity.Berge

/-!
# `β`-optimal allocations and the `β`-characteristic time

Top Two sampling rules choose, at each round, between a *leader* (an estimate of the correct
answer) and a *challenger*, sampling the leader with a fixed probability `β ∈ (0, 1)`. In the long
run, the proportion of samples of the leader arm is `β`, so these algorithms can only reach the
best value of the pure exploration game among the allocations with that proportion:
`D_β(θ, ¬i) = sup {D(θ, w, ¬i) | w ∈ Δ_K, w_a = β}`, the *`β`-value* of the answer `i` with the
arm `a`. For tasks whose answers are arms, such as best arm identification, the leader of the
answer `i` is the arm `i` itself, and the *`β`-characteristic time* is
`T*_β(θ) = (sup_{i ∈ i*(θ)} D_β(θ, ¬i))⁻¹`.

Russo (2016) shows that `T*_β` is within a factor `max(β*/β, (1 - β*)/(1 - β))` of the
characteristic time `T*`, where `β*` is the proportion of the leader arm in an optimal allocation;
in particular `T*_{1/2}(θ) ≤ 2 T*(θ)` without knowledge of `β*`. This bounds the loss of Top Two
algorithms with `β = 1/2` with respect to the asymptotically optimal ones.

## Main definitions

* `IdentTask.betaAnswerValue task θ i a β`: the `β`-value `D_β(θ, ¬i)` of the answer `i` with the
  arm `a`, the supremum of `D(θ, w, ¬i)` over the allocations `w` with `w a = β`.
* `IdentTask.betaOptAlloc task θ i a β`: the `β`-optimal allocations, at which this supremum is
  attained.
* `IdentTask.betaGameValue task θ β`, `IdentTask.betaCharTime task θ β`: for a task whose answers
  are arms, the `β`-value `sup_{i ∈ i*(θ)} D_β(θ, ¬i)` of the game and the `β`-characteristic time
  `T*_β(θ)`, its inverse.

## Main statements

* `IdentTask.iSup_betaAnswerValue`: `D(θ, ¬i) = sup_β D_β(θ, ¬i)`.
* `IdentTask.betaAnswerValue_eq_answerValue_of_mem_optAlloc`: `D_β(θ, ¬i) = D(θ, ¬i)` for the
  proportion `β = w_a` of an optimal allocation `w`.
* `IdentTask.convex_betaOptAlloc`, `IdentTask.isCompact_betaOptAlloc`,
  `IdentTask.betaOptAlloc_nonempty`: the `β`-optimal allocations form a convex set; if
  `w ↦ D(θ, w, ¬i)` is upper semicontinuous, it is compact, and nonempty for `β ∈ [0, 1]`.
* `IdentTask.mul_answerValue_le_betaAnswerValue`: [R16, Lemma 3] if `w` is an optimal allocation
  and `c ≥ 0` satisfies `c w_a ≤ β` and `c (1 - w_a) ≤ 1 - β`, then
  `c D(θ, ¬i) ≤ D_β(θ, ¬i)`.
* `IdentTask.answerValue_le_two_mul_betaAnswerValue_half`: `D(θ, ¬i) ≤ 2 D_{1/2}(θ, ¬i)`.
* `IdentTask.gameValue_le_two_mul_betaGameValue_half`: `D(θ) ≤ 2 D_{1/2}(θ)`.
* `IdentTask.charTime_le_betaCharTime`, `IdentTask.betaCharTime_half_le_two_mul_charTime`:
  `T*(θ) ≤ T*_β(θ)` and `T*_{1/2}(θ) ≤ 2 T*(θ)`.
* `IdentTask.betaCharTime_le_inv_mul_charTime`: [R16, Lemma 3] for a model with a single correct
  answer, `T*_β(θ) ≤ c⁻¹ T*(θ)` under the conditions above.

## References

* [R16] D. Russo, *Simple Bayesian algorithms for best arm identification*, COLT 2016;
  Operations Research 68 (2020). Lemma 3 in the numbering of arXiv:1602.08448v4.
* [JDBdHK22] M. Jourdan, R. Degenne, D. Baudry, R. de Heide and E. Kaufmann, *Top two algorithms
  revisited*, NeurIPS 2022.
-/

public section

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} [Fintype α]

namespace IdentTask

variable {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} (task : IdentTask α Θ ℐ 𝓨)
  {θ : Θ} {i : ℐ} {a b : α} {β : ℝ} {w : α → ℝ}

/-! ### The `β`-value of an answer -/

/-- The `β`-value `D_β(θ, ¬i)` of the answer `i` with the arm `a` at the model `θ`: the supremum
of the cost `D(θ, w, ¬i)` of the alternatives to `i` over the allocations `w` that give the
proportion `β` to the arm `a`. It is `0` if no allocation has `w a = β`, for example if
`β ∉ [0, 1]`. -/
noncomputable def betaAnswerValue (θ : Θ) (i : ℐ) (a : α) (β : ℝ) : ℝ≥0∞ :=
  ⨆ w ∈ {w ∈ simplex α | w a = β}, task.altCost θ w i

/-- The `β`-optimal allocations of the answer `i` with the arm `a` at the model `θ`: the
allocations giving the proportion `β` to the arm `a` at which the cost of the alternatives to `i`
attains the `β`-value `D_β(θ, ¬i)`. -/
def betaOptAlloc (θ : Θ) (i : ℐ) (a : α) (β : ℝ) : Set (α → ℝ) :=
  {w | w ∈ simplex α ∧ w a = β ∧ task.altCost θ w i = task.betaAnswerValue θ i a β}

lemma betaAnswerValue_def (θ : Θ) (i : ℐ) (a : α) (β : ℝ) :
    task.betaAnswerValue θ i a β = ⨆ w ∈ {w ∈ simplex α | w a = β}, task.altCost θ w i := (rfl)

@[simp]
lemma mem_betaOptAlloc_iff : w ∈ task.betaOptAlloc θ i a β ↔
    w ∈ simplex α ∧ w a = β ∧ task.altCost θ w i = task.betaAnswerValue θ i a β := Iff.rfl

lemma altCost_le_betaAnswerValue (hw : w ∈ simplex α) (hwa : w a = β) :
    task.altCost θ w i ≤ task.betaAnswerValue θ i a β :=
  le_iSup₂ (f := fun w (_ : w ∈ {w ∈ simplex α | w a = β}) ↦ task.altCost θ w i) w
    (Set.mem_sep_iff.2 ⟨hw, hwa⟩)

lemma betaAnswerValue_le_answerValue (a : α) (β : ℝ) :
    task.betaAnswerValue θ i a β ≤ task.answerValue θ i :=
  iSup₂_le fun _ hw ↦ task.altCost_le_answerValue (Set.sep_subset _ _ hw)

/-- The value `D(θ, ¬i)` of the game of the answer `i` is the supremum over `β` of its `β`-values
with any arm `a`. -/
theorem iSup_betaAnswerValue (θ : Θ) (i : ℐ) (a : α) :
    ⨆ β, task.betaAnswerValue θ i a β = task.answerValue θ i := by
  refine (iSup_le fun β ↦ task.betaAnswerValue_le_answerValue a β).antisymm ?_
  rw [answerValue_def]
  exact iSup₂_le fun w hw ↦
    (task.altCost_le_betaAnswerValue hw rfl).trans (le_iSup (task.betaAnswerValue θ i a ·) (w a))

/-- The `β`-value of an answer vanishes at an alternative to this answer. -/
lemma betaAnswerValue_eq_zero_of_mem_alt (hθ : θ ∈ task.alt i) (a : α) (β : ℝ) :
    task.betaAnswerValue θ i a β = 0 := by
  simp [betaAnswerValue_def, task.altCost_eq_zero_of_mem_alt hθ]

/-- The `β`-value of the answer `i` is antitone in the set of alternatives. -/
lemma betaAnswerValue_le_betaAnswerValue_of_alt_subset {j : ℐ} (h : task.alt i ⊆ task.alt j)
    (θ : Θ) (a : α) (β : ℝ) : task.betaAnswerValue θ j a β ≤ task.betaAnswerValue θ i a β :=
  iSup₂_mono fun w _ ↦ task.altCost_le_altCost_of_alt_subset h θ w

/-- For the proportion `β = w_a` of the arm `a` in an optimal allocation `w`, the `β`-value of the
answer is its value: `D_β(θ, ¬i) = D(θ, ¬i)`. -/
lemma betaAnswerValue_eq_answerValue_of_mem_optAlloc (hw : w ∈ task.optAlloc θ i) (a : α) :
    task.betaAnswerValue θ i a (w a) = task.answerValue θ i := by
  obtain ⟨hw, hwv⟩ := task.mem_optAlloc_iff.1 hw
  exact (task.betaAnswerValue_le_answerValue a (w a)).antisymm
    (hwv.symm.trans_le (task.altCost_le_betaAnswerValue hw rfl))

/-- An optimal allocation `w` is `β`-optimal for the proportion `β = w_a` of each arm `a`. -/
lemma mem_betaOptAlloc_of_mem_optAlloc (hw : w ∈ task.optAlloc θ i) (a : α) :
    w ∈ task.betaOptAlloc θ i a (w a) := by
  have h := task.betaAnswerValue_eq_answerValue_of_mem_optAlloc hw a
  obtain ⟨hw, hwv⟩ := task.mem_optAlloc_iff.1 hw
  exact task.mem_betaOptAlloc_iff.2 ⟨hw, rfl, hwv.trans h.symm⟩

/-! ### The `β`-optimal allocations -/

/-- The `β`-optimal allocations are the maximizers of the cost `w ↦ D(θ, w, ¬i)` of the
alternatives on the allocations with `w a = β`. -/
lemma mem_betaOptAlloc_iff_isMaxOn : w ∈ task.betaOptAlloc θ i a β ↔
    w ∈ {w ∈ simplex α | w a = β} ∧
      IsMaxOn (task.altCost θ · i) {w ∈ simplex α | w a = β} w := by
  rw [mem_betaOptAlloc_iff, isMaxOn_iff, Set.mem_sep_iff, ← and_assoc]
  refine and_congr_right fun hw ↦ ⟨fun h v hv ↦ ?_, fun h ↦ ?_⟩
  · rw [Set.mem_sep_iff] at hv
    exact h ▸ task.altCost_le_betaAnswerValue hv.1 hv.2
  · exact (task.altCost_le_betaAnswerValue hw.1 hw.2).antisymm (iSup₂_le h)

/-- The `β`-optimal allocations form a convex set: they are a superlevel set of the concave
function `w ↦ D(θ, w, ¬i)` on the convex set of allocations with `w a = β`. -/
theorem convex_betaOptAlloc (θ : Θ) (i : ℐ) (a : α) (β : ℝ) :
    Convex ℝ (task.betaOptAlloc θ i a β) := by
  have h : task.betaOptAlloc θ i a β = {w ∈ {w ∈ simplex α | w a = β} |
      task.betaAnswerValue θ i a β ≤ task.altCost θ w i} := by
    ext w
    simp only [mem_betaOptAlloc_iff, Set.mem_sep_iff, and_assoc]
    exact and_congr_right fun hw ↦ and_congr_right fun hwa ↦
      ⟨fun h ↦ h.ge, (task.altCost_le_betaAnswerValue hw hwa).antisymm⟩
  rw [h, ← NNReal.convex_iff]
  exact ((task.concaveOn_altCost θ i).subset ((Set.sep_subset _ _).trans simplex_subset_nonneg)
    (NNReal.convex_iff.2 (convex_setOf_mem_simplex_apply_eq a β))).convex_ge _

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, the
`β`-optimal allocations form a compact set. -/
lemma isCompact_betaOptAlloc (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α))
    (a : α) (β : ℝ) : IsCompact (task.betaOptAlloc θ i a β) := by
  convert (h.mono (Set.sep_subset (simplex α) (· a = β))).isCompact_setOfPred_isMaxOn
    (isCompact_setOf_mem_simplex_apply_eq a β) using 1
  ext w
  exact task.mem_betaOptAlloc_iff_isMaxOn

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, a
`β`-optimal allocation exists for every `β ∈ [0, 1]`, as soon as there are two arms. -/
lemma betaOptAlloc_nonempty (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α))
    (hab : b ≠ a) (hβ : β ∈ Set.Icc 0 1) : (task.betaOptAlloc θ i a β).Nonempty := by
  have : Nonempty α := ⟨a⟩
  obtain ⟨w, hw⟩ := simplex_nonempty α
  obtain ⟨v, hv, hva, -⟩ := exists_mem_simplex_apply_eq_and_smul_le hw hab le_rfl
    (by simpa using hβ.1) (by simpa using hβ.2)
  obtain ⟨u, hu, hmax⟩ := (h.mono (Set.sep_subset (simplex α) (· a = β))).exists_isMaxOn
    ⟨v, Set.mem_sep_iff.2 ⟨hv, hva⟩⟩ (isCompact_setOf_mem_simplex_apply_eq a β)
  exact ⟨u, task.mem_betaOptAlloc_iff_isMaxOn.2 ⟨hu, hmax⟩⟩

/-! ### Comparison with the value of the game -/

/-- The cost of the alternatives at an allocation `w`, scaled by any `c ≥ 0` with `c w_a ≤ β` and
`c (1 - w_a) ≤ 1 - β`, is at most the `β`-value `D_β(θ, ¬i)`, as soon as there is an arm `b ≠ a`:
some allocation with proportion `β` for `a` dominates `c w`. -/
theorem mul_altCost_le_betaAnswerValue (hab : b ≠ a) {c : ℝ≥0} (hw : w ∈ simplex α)
    (hca : c * w a ≤ β) (hcb : c * (1 - w a) ≤ 1 - β) :
    c * task.altCost θ w i ≤ task.betaAnswerValue θ i a β := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  obtain ⟨v, hv, hva, hle⟩ := exists_mem_simplex_apply_eq_and_smul_le hw hab c.2 hca hcb
  calc (c : ℝ≥0∞) * task.altCost θ w i = task.altCost θ (c • w) i := by
        rw [task.altCost_smul hc, ENNReal.smul_def, smul_eq_mul]
    _ ≤ task.altCost θ v i := task.monotone_altCost θ i (by simpa [NNReal.smul_def] using hle)
    _ ≤ task.betaAnswerValue θ i a β := task.altCost_le_betaAnswerValue hv hva

/-- **Russo's comparison** [R16, Lemma 3]: if `w` is an optimal allocation of the answer `i` and
`c ≥ 0` satisfies `c w_a ≤ β` and `c (1 - w_a) ≤ 1 - β`, then `c D(θ, ¬i) ≤ D_β(θ, ¬i)`. For
`w_a, β ∈ (0, 1)` and `c = min(β / w_a, (1 - β) / (1 - w_a))`, this is Russo's form
`D(θ, ¬i) ≤ max(w_a / β, (1 - w_a) / (1 - β)) D_β(θ, ¬i)`. -/
theorem mul_answerValue_le_betaAnswerValue (hab : b ≠ a) {c : ℝ≥0} (hw : w ∈ task.optAlloc θ i)
    (hca : c * w a ≤ β) (hcb : c * (1 - w a) ≤ 1 - β) :
    c * task.answerValue θ i ≤ task.betaAnswerValue θ i a β := by
  obtain ⟨hw, hwv⟩ := task.mem_optAlloc_iff.1 hw
  rw [← hwv]
  exact task.mul_altCost_le_betaAnswerValue hab hw hca hcb

/-- [R16, Lemma 3] for `β = 1/2`: the `1/2`-value of an answer is at least half its value,
`D(θ, ¬i) ≤ 2 D_{1/2}(θ, ¬i)`, as soon as there is an arm `b ≠ a`. -/
theorem answerValue_le_two_mul_betaAnswerValue_half (hab : b ≠ a) (θ : Θ) (i : ℐ) :
    task.answerValue θ i ≤ 2 * task.betaAnswerValue θ i a (1 / 2) := by
  rw [answerValue_def]
  refine iSup₂_le fun w hw ↦ ?_
  have hw0 : 0 ≤ w a := (mem_simplex_iff.1 hw).1 a
  have hw1 : w a ≤ 1 := by simpa using (simplex_subset_Icc hw).2 a
  have h := task.mul_altCost_le_betaAnswerValue (θ := θ) (i := i) (β := 1 / 2) (c := 2⁻¹) hab hw
    (by push_cast; linarith) (by push_cast; linarith)
  calc task.altCost θ w i = 2 * (2⁻¹ * task.altCost θ w i) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * task.betaAnswerValue θ i a (1 / 2) := by
        gcongr
        simpa using h

/-! ### Tasks whose answers are arms -/

section ArmAnswers

variable (task : IdentTask α Θ α 𝓨)

/-- The `β`-value `sup_{i ∈ i*(θ)} D_β(θ, ¬i)` of the pure exploration game at the model `θ`, for
a task whose answers are arms: the arm with proportion `β` is the correct answer `i` itself. -/
noncomputable def betaGameValue (θ : Θ) (β : ℝ) : ℝ≥0∞ :=
  ⨆ i ∈ task.correct θ, task.betaAnswerValue θ i i β

/-- The `β`-characteristic time `T*_β(θ)` of the model `θ`, for a task whose answers are arms: the
inverse of the `β`-value of the game. -/
noncomputable def betaCharTime (θ : Θ) (β : ℝ) : ℝ≥0∞ := (task.betaGameValue θ β)⁻¹

lemma betaGameValue_def (θ : Θ) (β : ℝ) :
    task.betaGameValue θ β = ⨆ i ∈ task.correct θ, task.betaAnswerValue θ i i β := (rfl)

lemma betaCharTime_def (θ : Θ) (β : ℝ) : task.betaCharTime θ β = (task.betaGameValue θ β)⁻¹ :=
  (rfl)

lemma betaAnswerValue_le_betaGameValue {i : α} (hi : i ∈ task.correct θ) (β : ℝ) :
    task.betaAnswerValue θ i i β ≤ task.betaGameValue θ β :=
  le_iSup₂ (f := fun i (_ : i ∈ task.correct θ) ↦ task.betaAnswerValue θ i i β) i hi

/-- For a model with a single correct answer `i`, `D_β(θ) = D_β(θ, ¬i)`. -/
lemma betaGameValue_eq_betaAnswerValue {i : α} (h : task.correct θ = {i}) (β : ℝ) :
    task.betaGameValue θ β = task.betaAnswerValue θ i i β := by
  simp [betaGameValue_def, h]

/-- For a model with a single correct answer `i`, `T*_β(θ) = D_β(θ, ¬i)⁻¹`. -/
lemma betaCharTime_eq_inv_betaAnswerValue {i : α} (h : task.correct θ = {i}) (β : ℝ) :
    task.betaCharTime θ β = (task.betaAnswerValue θ i i β)⁻¹ := by
  rw [betaCharTime_def, task.betaGameValue_eq_betaAnswerValue h]

lemma betaGameValue_le_gameValue (θ : Θ) (β : ℝ) :
    task.betaGameValue θ β ≤ task.gameValue θ := by
  rw [betaGameValue_def, gameValue_def]
  exact iSup₂_mono fun i _ ↦ task.betaAnswerValue_le_answerValue i β

/-- Constraining the proportion of the correct answer can only increase the characteristic time:
`T*(θ) ≤ T*_β(θ)`. -/
lemma charTime_le_betaCharTime (θ : Θ) (β : ℝ) : task.charTime θ ≤ task.betaCharTime θ β := by
  rw [charTime_def, betaCharTime_def]
  exact ENNReal.inv_le_inv.2 (task.betaGameValue_le_gameValue θ β)

/-- [R16, Lemma 3] for `β = 1/2`: `D(θ) ≤ 2 D_{1/2}(θ)`, as soon as there are two arms. -/
theorem gameValue_le_two_mul_betaGameValue_half [Nontrivial α] (θ : Θ) :
    task.gameValue θ ≤ 2 * task.betaGameValue θ (1 / 2) := by
  rw [gameValue_def]
  refine iSup₂_le fun i hi ↦ ?_
  obtain ⟨b, hb⟩ := exists_ne i
  exact (task.answerValue_le_two_mul_betaAnswerValue_half hb θ i).trans
    (by gcongr; exact task.betaAnswerValue_le_betaGameValue hi (1 / 2))

/-- [R16, Lemma 3] for `β = 1/2`: `T*_{1/2}(θ) ≤ 2 T*(θ)`. Top Two algorithms with `β = 1/2` lose
at most a factor `2` with respect to the characteristic time. -/
theorem betaCharTime_half_le_two_mul_charTime [Nontrivial α] (θ : Θ) :
    task.betaCharTime θ (1 / 2) ≤ 2 * task.charTime θ := by
  have h : (2 * task.betaGameValue θ (1 / 2))⁻¹ ≤ task.charTime θ := by
    rw [charTime_def]
    exact ENNReal.inv_le_inv.2 (task.gameValue_le_two_mul_betaGameValue_half θ)
  rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)] at h
  calc task.betaCharTime θ (1 / 2) = 2 * (2⁻¹ * (task.betaGameValue θ (1 / 2))⁻¹) := by
        rw [betaCharTime_def, ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * task.charTime θ := by gcongr

/-- **Russo's comparison** [R16, Lemma 3] for the characteristic times: for a model with a single
correct answer `i`, an optimal allocation `w` of `i` and a nonzero `c` with `c w_i ≤ β` and
`c (1 - w_i) ≤ 1 - β`, `T*_β(θ) ≤ c⁻¹ T*(θ)`. For `w_i, β ∈ (0, 1)` and
`c = min(β / w_i, (1 - β) / (1 - w_i))`, this is Russo's form
`T*_β(θ) ≤ max(w_i / β, (1 - w_i) / (1 - β)) T*(θ)`. -/
theorem betaCharTime_le_inv_mul_charTime [Nontrivial α] {i : α} (h : task.correct θ = {i})
    {w : α → ℝ} (hw : w ∈ task.optAlloc θ i) {c : ℝ≥0} (hc : c ≠ 0) (hci : c * w i ≤ β)
    (hcb : c * (1 - w i) ≤ 1 - β) :
    task.betaCharTime θ β ≤ (c : ℝ≥0∞)⁻¹ * task.charTime θ := by
  obtain ⟨b, hb⟩ := exists_ne i
  rw [task.betaCharTime_eq_inv_betaAnswerValue h, task.charTime_eq_inv_answerValue h,
    ← ENNReal.mul_inv (Or.inl (by simpa using hc)) (Or.inl ENNReal.coe_ne_top)]
  exact ENNReal.inv_le_inv.2 (task.mul_answerValue_le_betaAnswerValue hb hw hci hcb)

end ArmAnswers

end IdentTask

end LMLExplore.Identification
