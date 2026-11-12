/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LMLExplore.Analysis.InnerProductSpace.LeastSquares
public import LMLExplore.Analysis.InnerProductSpace.OptimalDesign
public import LMLExplore.Bandits.LinearBandit.Basic

/-!
# Phased elimination with optimal designs

Phased elimination [LS, Algorithm 12] plays a stochastic linear bandit with a finite set of arms
`α` and features `φ : α → E` in phases `ℓ = 0, 1, …`. Phase `ℓ` starts with a set `S_ℓ` of
surviving arms, `S_0` being all arms, and a confidence width `ε_ℓ = 2⁻¹ ^ (ℓ + 1)`. It takes a
design `w` on `S_ℓ` whose G-value is at most the dimension `d` of `E` (for example a G-optimal
design, by the Kiefer–Wolfowitz theorem), plays each arm `a` of the support of `w` exactly
`T_ℓ(a) = ⌈c_ℓ w(a)⌉` times, where
`c_ℓ = 2 σ² d log (k (ℓ + 1) (ℓ + 2) / δ) / ε_ℓ²` and `k` is the number of arms, computes the
least-squares estimate `θ̂_ℓ` of the parameter from the rewards of the phase only, and keeps the
arms `a ∈ S_ℓ` with `⟪θ̂_ℓ, φ b - φ a⟫ ≤ 2 ε_ℓ` for every `b ∈ S_ℓ`. Because the actions of a
phase are fixed when it starts, its estimate is a least-squares estimate on a fixed design, and
`⟪φ b, V_ℓ⁺ φ b⟫ ≤ d / c_ℓ` on `S_ℓ` for the design operator `V_ℓ` of the phase.

The algorithm is deterministic. Its state is computed from the sequence of the rewards: the
survivors `survivors y ℓ` and the first round `phaseStart y ℓ` of phase `ℓ` only depend on the
rewards `y s` of the rounds `s < phaseStart y ℓ`, and the action `nextArm y n` of round `n` only
on the rewards of the rounds `s < n`.

## Main definitions

* `LMLExplore.Bandits.DesignSelection φ`: a choice, for every nonempty set `S` of arms, of a
  design on `S` whose image design has the features of `S` in the range of its design operator
  and G-value at most `d`; `Nonempty (DesignSelection φ)` holds by the Kiefer–Wolfowitz theorem.
* `LMLExplore.Bandits.PhasedElimination.allocation c w`, `PhasedElimination.schedule T`: the
  numbers of pulls `⌈c w(a)⌉` (at least `1` on the support of `w`) and a list of arms in which
  each arm `a` appears `T a` times.
* `PhasedElimination.survivors D σ2 δ y ℓ`, `PhasedElimination.phaseStart D σ2 δ y ℓ`,
  `PhasedElimination.estimate D σ2 δ y ℓ`: the survivors, the first round and the least-squares
  estimate of phase `ℓ` for the rewards `y`.
* `PhasedElimination.phaseIndex D σ2 δ y n`, `PhasedElimination.nextArm D σ2 δ y n`: the phase of
  round `n` and the arm played at round `n`.
* `LMLExplore.Bandits.phasedElimination D σ2 δ`: the algorithm.

## Main statements

* `PhasedElimination.phase_congr`, `PhasedElimination.nextArm_congr`: the state of a phase only
  depends on the rewards before the phase, and the action of round `n` on the rewards before `n`.
* `PhasedElimination.phaseStart_phaseIndex_le`, `PhasedElimination.lt_phaseStart_phaseIndex_succ`,
  `PhasedElimination.phaseIndex_eq_of_le_of_lt`: round `n` lies in phase `phaseIndex D σ2 δ y n`.
* `PhasedElimination.nextArm_phaseStart_add`, `PhasedElimination.nextArm_mem_survivors`: the arms
  of a phase are the arms of its schedule, which are survivors.
* `PhasedElimination.inner_moorePenroseInverse_designOp_schedule_le`: along the schedule of the
  allocation of a design `w` with scale `c > 0`, `⟪φ b, V'⁺ φ b⟫ ≤ ⟪φ b, V(w)⁺ φ b⟫ / c`; hence
  `PhasedElimination.inner_moorePenroseInverse_designOp_phaseArm_le`: the weighted norm
  `⟪φ b, V_ℓ⁺ φ b⟫` of a survivor is at most `d / c_ℓ`, and
  `PhasedElimination.mem_span_phaseArm`: the features of the survivors lie in the span of the
  features of the phase.
* `PhasedElimination.measurable_phase`, `PhasedElimination.measurable_nextArm`: the state of a
  phase and the action of a round depend measurably on the rewards.
* `PhasedElimination.action_ae_all_eq`: the run lemma, along a run the action of round `n` is
  `nextArm D σ2 δ (Y · ω) n`.

## Implementation notes

The book allocates `⌈c_ℓ w(a)⌉` pulls to each arm `a` of the support of `w`; here the allocation
is at least `1` on the support, which changes nothing when `c_ℓ > 0` and guarantees that every
phase has at least one round for all values of the parameters. The design is a parameter of the
algorithm (a `DesignSelection`), so that a design with few support points can be chosen; the
number of support points enters the regret only through an additive term.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 22 and Algorithm 12.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module Learning Convexity
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits

variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : α → E}

/-- A **design selection** for the features `φ : α → E`: for every nonempty set `S` of arms, a
design `design S` on the arms, supported in `S`, whose image design `(design S).map φ` has a
design operator `V` with the features of `S` in its range and `⟪φ b, V⁺ φ b⟫ ≤ d` for every
`b ∈ S`, where `d` is the dimension of `E`: its G-value is at most `d`. By the Kiefer–Wolfowitz
theorem, such designs exist (`DesignSelection.instNonempty`). -/
@[ext]
structure DesignSelection (φ : α → E) where
  /-- The design chosen on the set of arms `S`. -/
  design : Finset α → StdSimplex ℝ α
  /-- The design of a nonempty set of arms is supported in it. -/
  support_subset : ∀ S : Finset α, S.Nonempty → (design S).weights.support ⊆ S
  /-- The features of the arms of `S` lie in the range of the design operator. -/
  mem_range : ∀ S : Finset α, S.Nonempty → ∀ b ∈ S,
    φ b ∈ LinearMap.range (designOperator ((design S).map φ) : E →ₗ[ℝ] E)
  /-- The G-value of the design of `S` is at most the dimension of `E`. -/
  inner_moorePenroseInverse_le : ∀ S : Finset α, S.Nonempty → ∀ b ∈ S,
    ⟪φ b, (designOperator ((design S).map φ) : E →ₗ[ℝ] E).moorePenroseInverse (φ b)⟫_ℝ ≤
      finrank ℝ E

/-- Design selections exist, by the Kiefer–Wolfowitz theorem for finitely many arms
(`exists_design_map_inner_moorePenroseInverse_le_finrank`). -/
instance DesignSelection.instNonempty [Nonempty α] : Nonempty (DesignSelection φ) := by
  classical
  have h (S : Finset α) : ∃ w : StdSimplex ℝ α, S.Nonempty → w.weights.support ⊆ S ∧
      (∀ b ∈ S, φ b ∈ LinearMap.range (designOperator (w.map φ) : E →ₗ[ℝ] E)) ∧
      ∀ b ∈ S, ⟪φ b, (designOperator (w.map φ) : E →ₗ[ℝ] E).moorePenroseInverse (φ b)⟫_ℝ ≤
        finrank ℝ E := by
    by_cases hS : S.Nonempty
    · obtain ⟨w, hw, hr, hle⟩ := exists_design_map_inner_moorePenroseInverse_le_finrank φ hS
      exact ⟨w, fun _ ↦ ⟨hw, hr, fun b hb ↦ (hle b hb).trans
        (Nat.cast_le.2 (Submodule.finrank_le _))⟩⟩
    · exact ⟨.single (Classical.arbitrary α), fun h ↦ absurd h hS⟩
  choose w hw using h
  exact ⟨⟨w, fun S hS ↦ (hw S hS).1, fun S hS ↦ (hw S hS).2.1, fun S hS ↦ (hw S hS).2.2⟩⟩

namespace PhasedElimination

/-! ### Allocations and schedules -/

section Allocation

/-- The **allocation** of a phase with design `w` and scale `c`: `⌈c w(a)⌉` pulls of each arm `a`
of the support of `w`, at least one, and none of the arms outside the support. -/
noncomputable def allocation (c : ℝ) (w : StdSimplex ℝ α) (a : α) : ℕ :=
  if w.weights a = 0 then 0 else max 1 ⌈c * w.weights a⌉₊

variable {c : ℝ} {w : StdSimplex ℝ α} {a : α}

lemma allocation_def :
    allocation c w a = if w.weights a = 0 then 0 else max 1 ⌈c * w.weights a⌉₊ :=
  (rfl)

@[simp]
lemma allocation_eq_zero_iff : allocation c w a = 0 ↔ w.weights a = 0 := by
  by_cases ha : w.weights a = 0 <;> simp [allocation_def, ha]

/-- Each arm of the support is pulled at least `c w(a)` times. -/
lemma mul_le_allocation : c * w.weights a ≤ allocation c w a := by
  by_cases ha : w.weights a = 0
  · simp [ha]
  · simp only [allocation_def, ha, ite_false, Nat.cast_max]
    exact (Nat.le_ceil _).trans (le_max_right _ _)

/-- For `c ≥ 0`, each arm is pulled at most `c w(a) + 1` times. -/
lemma allocation_le (hc : 0 ≤ c) : (allocation c w a : ℝ) ≤ c * w.weights a + 1 := by
  have hca : 0 ≤ c * w.weights a := mul_nonneg hc (w.nonneg a)
  by_cases ha : w.weights a = 0
  · simp [allocation_def, ha]
  · simp only [allocation_def, ha, ite_false, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hca).le

/-- The total number of pulls of a phase is at most `c + #(support of w)` for `c ≥ 0`. -/
lemma sum_allocation_le [Fintype α] (hc : 0 ≤ c) :
    (∑ a, allocation c w a : ℝ) ≤ c + #w.weights.support := by
  have hsupp : ∑ a, (allocation c w a : ℝ) = ∑ a ∈ w.weights.support, (allocation c w a : ℝ) :=
    (sum_subset (subset_univ _) fun a _ ha ↦ by
      simp [allocation_eq_zero_iff.2 (Finsupp.notMem_support_iff.1 ha)]).symm
  have hw : ∑ a ∈ w.weights.support, w.weights a = 1 := by
    simpa [Finsupp.sum] using w.total
  calc ∑ a, (allocation c w a : ℝ)
      ≤ ∑ a ∈ w.weights.support, (c * w.weights a + 1) := by
        rw [hsupp]
        exact sum_le_sum fun a _ ↦ allocation_le hc
    _ = c + #w.weights.support := by
        rw [sum_add_distrib, ← mul_sum, hw, mul_one, sum_const, nsmul_eq_mul, mul_one]

end Allocation

section Schedule

variable [Fintype α]

/-- A **schedule** for the numbers of pulls `T`: a list of arms in which each arm `a` appears
`T a` times. -/
noncomputable def schedule (T : α → ℕ) : List α :=
  (∑ a, Multiset.replicate (T a) a).toList

variable {T : α → ℕ}

lemma coe_schedule (T : α → ℕ) : (schedule T : Multiset α) = ∑ a, Multiset.replicate (T a) a :=
  Multiset.coe_toList _

@[simp]
lemma count_schedule [DecidableEq α] (T : α → ℕ) (a : α) : (schedule T).count a = T a := by
  rw [← Multiset.coe_count, coe_schedule, Multiset.count_sum']
  simp [Multiset.count_replicate]

@[simp]
lemma length_schedule (T : α → ℕ) : (schedule T).length = ∑ a, T a := by
  rw [← Multiset.coe_card, coe_schedule, Multiset.card_sum]
  simp

lemma mem_schedule {a : α} : a ∈ schedule T ↔ T a ≠ 0 := by
  classical
  rw [← List.count_pos_iff, count_schedule, Nat.pos_iff_ne_zero]

/-- Summing a function along the positions of the schedule sums it over the arms, with
multiplicities `T`. -/
lemma sum_range_length_schedule {M : Type*} [AddCommMonoid M] (T : α → ℕ) (F : α → M)
    (a₀ : α) :
    ∑ j ∈ range (schedule T).length, F ((schedule T).getD j a₀) = ∑ a, T a • F a := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ F ((schedule T).getD j a₀))]
  simp only [Fin.is_lt, List.getD_eq_getElem, Fin.sum_univ_fun_getElem]
  rw [← Multiset.sum_coe, ← Multiset.map_coe, coe_schedule, Finset.sum_multiset_map_count,
    sum_subset (subset_univ _) fun a _ ha ↦ by
      rw [Multiset.count_eq_zero.2 fun h ↦ ha (Multiset.mem_toFinset.2 h), zero_smul]]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Multiset.count_sum']
  simp [Multiset.count_replicate]

/-- **The weighted norms along a schedule.** Let `c > 0` and `w` a design on the arms such that
`φ b` lies in the range of the design operator `V` of `w.map φ`. Along the schedule of the
allocation of `w` with scale `c`, which pulls each arm `a` at least `c w(a)` times, the
unregularized design operator `V'` of the features satisfies
`⟪φ b, V'⁺ φ b⟫ ≤ ⟪φ b, V⁺ φ b⟫ / c`. -/
theorem inner_moorePenroseInverse_designOp_schedule_le {c : ℝ} (hc : 0 < c)
    (w : StdSimplex ℝ α) (a₀ : α) {b : α}
    (hb : φ b ∈ LinearMap.range (designOperator (w.map φ) : E →ₗ[ℝ] E)) :
    ⟪φ b, (designOp 0 (fun j ↦ φ ((schedule (allocation c w)).getD j a₀))
        (schedule (allocation c w)).length : E →ₗ[ℝ] E).moorePenroseInverse (φ b)⟫_ℝ ≤
      ⟪φ b, (designOperator (w.map φ) : E →ₗ[ℝ] E).moorePenroseInverse (φ b)⟫_ℝ / c := by
  set V : E →ₗ[ℝ] E := (designOperator (w.map φ) : E →ₗ[ℝ] E)
  set u := V.moorePenroseInverse (φ b)
  -- `φ b = V u = ∑_a w a ⟪φ a, u⟫ φ a`
  have hVu : V u = φ b := V.isMoorePenroseInverse_moorePenroseInverse.apply_apply_of_mem_range hb
  have hVu' : ∑ a, (w.weights a * ⟪φ a, u⟫_ℝ) • φ a = φ b := by
    rw [← hVu]
    simp [V, designOperator_map, mul_smul]
  -- the coefficients `w a ⟪φ a, u⟫ / T a` of the positions of the schedule represent `φ b`
  set coef : α → ℝ := fun a ↦ w.weights a * ⟪φ a, u⟫_ℝ / allocation c w a
  have hrep : ∑ j ∈ range (schedule (allocation c w)).length,
      coef ((schedule (allocation c w)).getD j a₀) • φ ((schedule (allocation c w)).getD j a₀) =
        φ b := by
    rw [sum_range_length_schedule _ (fun a ↦ coef a • φ a), ← hVu']
    refine sum_congr rfl fun a _ ↦ ?_
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rcases eq_or_ne (allocation c w a) 0 with h0 | h0
    · simp [h0, allocation_eq_zero_iff.1 h0]
    · congr 1
      simp only [coef]
      field_simp
  -- its squared norm is at most `⟪u, V u⟫ / c = ⟪φ b, V⁺ φ b⟫ / c`
  refine (inner_moorePenroseInverse_designOp_le_sum_sq hrep).trans ?_
  rw [sum_range_length_schedule _ fun a ↦ coef a ^ 2]
  have hterm (a : α) : allocation c w a • coef a ^ 2 ≤ w.weights a * ⟪φ a, u⟫_ℝ ^ 2 / c := by
    rw [nsmul_eq_mul]
    rcases eq_or_ne (w.weights a) 0 with h0 | h0
    · simp [coef, h0]
    have hwpos : 0 < w.weights a := lt_of_le_of_ne (w.nonneg a) (Ne.symm h0)
    have hT : c * w.weights a ≤ allocation c w a := mul_le_allocation
    have hTpos : (0 : ℝ) < allocation c w a := lt_of_lt_of_le (mul_pos hc hwpos) hT
    calc (allocation c w a : ℝ) * coef a ^ 2
        = w.weights a * ⟪φ a, u⟫_ℝ ^ 2 * (w.weights a / allocation c w a) := by
          simp only [coef]
          field_simp
      _ ≤ w.weights a * ⟪φ a, u⟫_ℝ ^ 2 * (1 / c) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ hTpos hc]
          linarith
      _ = w.weights a * ⟪φ a, u⟫_ℝ ^ 2 / c := by ring
  calc ∑ a, allocation c w a • coef a ^ 2 ≤ ∑ a, w.weights a * ⟪φ a, u⟫_ℝ ^ 2 / c :=
        sum_le_sum fun a _ ↦ hterm a
    _ = ⟪φ b, u⟫_ℝ / c := by
        rw [← sum_div]
        congr 1
        rw [← hVu', sum_inner]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [real_inner_smul_left]
        ring

end Schedule

/-! ### The phases of the algorithm -/

variable [Fintype α] (D : DesignSelection φ) (σ2 : ℝ≥0) (δ : ℝ)

/-- The confidence **width** `ε_ℓ = 2⁻¹ ^ (ℓ + 1)` of phase `ℓ`. -/
noncomputable def width (ℓ : ℕ) : ℝ := 2⁻¹ ^ (ℓ + 1)

omit [Fintype α] in
lemma width_def (ℓ : ℕ) : width ℓ = 2⁻¹ ^ (ℓ + 1) := (rfl)

omit [Fintype α] in
lemma width_pos (ℓ : ℕ) : 0 < width ℓ := by
  rw [width_def]
  positivity

omit [Fintype α] in
lemma width_succ (ℓ : ℕ) : width (ℓ + 1) = width ℓ / 2 := by
  rw [width_def, width_def, pow_succ, div_eq_mul_inv]

/-- The **sample scale** `c_ℓ = 2 σ² d log (k (ℓ + 1) (ℓ + 2) / δ) / ε_ℓ²` of phase `ℓ`, in a
space of dimension `d` with `k` arms: the allocation of phase `ℓ` pulls each arm of the support of
the design `w` at least `c_ℓ w(a)` times. -/
noncomputable def scale (d k : ℕ) (σ2 : ℝ≥0) (δ : ℝ) (ℓ : ℕ) : ℝ :=
  2 * σ2 * d * log (k * ((ℓ + 1) * (ℓ + 2)) / δ) / width ℓ ^ 2

omit [Fintype α] in
lemma scale_def (d k : ℕ) (σ2 : ℝ≥0) (δ : ℝ) (ℓ : ℕ) :
    scale d k σ2 δ ℓ = 2 * σ2 * d * log (k * ((ℓ + 1) * (ℓ + 2)) / δ) / width ℓ ^ 2 :=
  (rfl)

/-- The **allocation of phase `ℓ`** with survivors `S`: the allocation of the design
`D.design S` with the sample scale of phase `ℓ`. -/
noncomputable def phaseAllocation (ℓ : ℕ) (S : Finset α) : α → ℕ :=
  allocation (scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ) (D.design S)

/-- The arm played at position `j` of phase `ℓ` with survivors `S`, following the schedule of the
allocation of the phase. -/
noncomputable def phaseArm (ℓ : ℕ) (S : Finset α) (j : ℕ) : α :=
  (schedule (phaseAllocation D σ2 δ ℓ S)).getD j (D.design S).nonempty.some

/-- The number of rounds of phase `ℓ` with survivors `S`. -/
noncomputable def phaseLength (ℓ : ℕ) (S : Finset α) : ℕ :=
  (schedule (phaseAllocation D σ2 δ ℓ S)).length

/-- The least-squares estimate of phase `ℓ` with survivors `S`, from the rewards `y j` of its
positions `j < phaseLength D σ2 δ ℓ S`, with the unregularized design of the phase. -/
noncomputable def phaseEstimate (ℓ : ℕ) (S : Finset α) (y : ℕ → ℝ) : E :=
  leastSquaresEstimate 0 (fun j ↦ φ (phaseArm D σ2 δ ℓ S j)) y (phaseLength D σ2 δ ℓ S)

variable {D σ2 δ}

lemma phaseAllocation_def (ℓ : ℕ) (S : Finset α) :
    phaseAllocation D σ2 δ ℓ S =
      allocation (scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ) (D.design S) :=
  (rfl)

lemma phaseArm_def (ℓ : ℕ) (S : Finset α) (j : ℕ) :
    phaseArm D σ2 δ ℓ S j =
      (schedule (phaseAllocation D σ2 δ ℓ S)).getD j (D.design S).nonempty.some :=
  (rfl)

lemma phaseLength_def (ℓ : ℕ) (S : Finset α) :
    phaseLength D σ2 δ ℓ S = (schedule (phaseAllocation D σ2 δ ℓ S)).length :=
  (rfl)

lemma phaseEstimate_def (ℓ : ℕ) (S : Finset α) (y : ℕ → ℝ) :
    phaseEstimate D σ2 δ ℓ S y =
      leastSquaresEstimate 0 (fun j ↦ φ (phaseArm D σ2 δ ℓ S j)) y (phaseLength D σ2 δ ℓ S) :=
  (rfl)

lemma phaseLength_eq_sum (ℓ : ℕ) (S : Finset α) :
    phaseLength D σ2 δ ℓ S = ∑ a, phaseAllocation D σ2 δ ℓ S a := by
  rw [phaseLength_def, length_schedule]

/-- Every phase has at least one round. -/
lemma phaseLength_pos (ℓ : ℕ) (S : Finset α) : 0 < phaseLength D σ2 δ ℓ S := by
  obtain ⟨a, ha⟩ := (D.design S).support_weights_nonempty
  rw [phaseLength_eq_sum]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ a))
  rw [Nat.pos_iff_ne_zero, phaseAllocation_def, Ne, allocation_eq_zero_iff]
  exact Finsupp.mem_support_iff.1 ha

/-- The arms of a phase lie in the support of its design. -/
lemma phaseArm_mem_support {ℓ : ℕ} {S : Finset α} {j : ℕ} (hj : j < phaseLength D σ2 δ ℓ S) :
    phaseArm D σ2 δ ℓ S j ∈ (D.design S).weights.support := by
  rw [phaseLength_def] at hj
  have hmem := mem_schedule.1 (List.getElem_mem hj)
  rw [phaseArm_def, List.getD_eq_getElem _ _ hj]
  generalize (schedule (phaseAllocation D σ2 δ ℓ S))[j] = a at hmem ⊢
  rw [phaseAllocation_def, Ne, allocation_eq_zero_iff] at hmem
  exact Finsupp.mem_support_iff.2 hmem

/-- The arms of a phase with nonempty survivors are survivors. -/
lemma phaseArm_mem {ℓ : ℕ} {S : Finset α} (hS : S.Nonempty) {j : ℕ}
    (hj : j < phaseLength D σ2 δ ℓ S) : phaseArm D σ2 δ ℓ S j ∈ S :=
  D.support_subset S hS (phaseArm_mem_support hj)

/-- The features of the survivors of a phase lie in the span of the features of its rounds. -/
lemma mem_span_phaseArm {ℓ : ℕ} {S : Finset α} (hS : S.Nonempty) {b : α} (hb : b ∈ S) :
    φ b ∈ Submodule.span ℝ
      ((fun j ↦ φ (phaseArm D σ2 δ ℓ S j)) '' Set.Iio (phaseLength D σ2 δ ℓ S)) := by
  classical
  have hb' := D.mem_range S hS b hb
  rw [range_designOperator] at hb'
  refine Submodule.span_mono ?_ hb'
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hv)
  -- the arm `a` of the support of the design appears in the schedule of the phase
  have hmem : a ∈ schedule (phaseAllocation D σ2 δ ℓ S) := by
    rw [mem_schedule, Ne, phaseAllocation_def, allocation_eq_zero_iff]
    exact Finsupp.mem_support_iff.1 ha
  obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 hmem
  refine ⟨j, Set.mem_Iio.2 (by rwa [phaseLength_def]), ?_⟩
  simp only [phaseArm_def, List.getD_eq_getElem _ _ hj, hja]

/-- Summing along the positions of a phase sums over the arms, with the multiplicities of the
allocation. -/
lemma sum_range_phaseLength {M : Type*} [AddCommMonoid M] (ℓ : ℕ) (S : Finset α) (F : α → M) :
    ∑ j ∈ range (phaseLength D σ2 δ ℓ S), F (phaseArm D σ2 δ ℓ S j) =
      ∑ a, phaseAllocation D σ2 δ ℓ S a • F a := by
  simp only [phaseLength_def, phaseArm_def]
  exact sum_range_length_schedule _ F _

/-- **The weighted norms of a phase.** If the sample scale `c_ℓ` is positive, then every survivor
`b ∈ S` satisfies `⟪φ b, V_ℓ⁺ φ b⟫ ≤ d / c_ℓ`, where `V_ℓ` is the unregularized design operator of
the features of the arms of the phase. -/
theorem inner_moorePenroseInverse_designOp_phaseArm_le {ℓ : ℕ} {S : Finset α}
    (hS : S.Nonempty) (hc : 0 < scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ) {b : α}
    (hb : b ∈ S) :
    ⟪φ b, (designOp 0 (fun j ↦ φ (phaseArm D σ2 δ ℓ S j)) (phaseLength D σ2 δ ℓ S) :
        E →ₗ[ℝ] E).moorePenroseInverse (φ b)⟫_ℝ ≤
      finrank ℝ E / scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ := by
  simp only [phaseArm_def, phaseLength_def, phaseAllocation_def]
  refine (inner_moorePenroseInverse_designOp_schedule_le hc _ _ (D.mem_range S hS b hb)).trans ?_
  gcongr
  exact D.inner_moorePenroseInverse_le S hS b hb

/-! ### The phases along a sequence of rewards -/

variable (φ) in
/-- **Elimination** at the end of phase `ℓ` with survivors `S` and estimate `θ`: the arms `a ∈ S`
with `⟪θ, φ b - φ a⟫ ≤ 2 ε_ℓ` for every `b ∈ S` survive. -/
noncomputable def eliminate (ℓ : ℕ) (S : Finset α) (θ : E) : Finset α :=
  {a ∈ S | ∀ b ∈ S, ⟪θ, φ b - φ a⟫_ℝ ≤ 2 * width ℓ}

omit [Fintype α] [FiniteDimensional ℝ E] in
lemma mem_eliminate {ℓ : ℕ} {S : Finset α} {θ : E} {a : α} :
    a ∈ eliminate φ ℓ S θ ↔ a ∈ S ∧ ∀ b ∈ S, ⟪θ, φ b - φ a⟫_ℝ ≤ 2 * width ℓ := by
  rw [eliminate, mem_filter]

omit [Fintype α] [FiniteDimensional ℝ E] in
/-- An arm of `S` maximizing `⟪θ, φ a⟫` survives the elimination, so the survivors of a nonempty
set are nonempty. -/
lemma eliminate_nonempty {ℓ : ℕ} {S : Finset α} (hS : S.Nonempty) (θ : E) :
    (eliminate φ ℓ S θ).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image S (fun a ↦ ⟪θ, φ a⟫_ℝ) hS
  refine ⟨a, mem_eliminate.2 ⟨ha, fun b hb ↦ ?_⟩⟩
  rw [inner_sub_right]
  linarith [hmax b hb, width_pos ℓ]

variable (D σ2 δ) in
/-- The survivors and the first round of phase `ℓ`, for the sequence of rewards `y`: phase `0`
starts at round `0` with all arms, and phase `ℓ + 1` starts when phase `ℓ` ends, with the arms that
survive the elimination with the estimate of phase `ℓ`, computed from the rewards of its rounds. -/
noncomputable def phase (y : ℕ → ℝ) : ℕ → Finset α × ℕ
  | 0 => (univ, 0)
  | ℓ + 1 =>
    (eliminate φ ℓ (phase y ℓ).1
        (phaseEstimate D σ2 δ ℓ (phase y ℓ).1 fun j ↦ y ((phase y ℓ).2 + j)),
      (phase y ℓ).2 + phaseLength D σ2 δ ℓ (phase y ℓ).1)

variable (D σ2 δ) in
/-- The **survivors** `S_ℓ` of phase `ℓ` for the sequence of rewards `y`. -/
noncomputable def survivors (y : ℕ → ℝ) (ℓ : ℕ) : Finset α := (phase D σ2 δ y ℓ).1

variable (D σ2 δ) in
/-- The first round `t_ℓ` of phase `ℓ` for the sequence of rewards `y`. -/
noncomputable def phaseStart (y : ℕ → ℝ) (ℓ : ℕ) : ℕ := (phase D σ2 δ y ℓ).2

variable (D σ2 δ) in
/-- The least-squares **estimate** `θ̂_ℓ` of phase `ℓ`, from the rewards of its rounds. -/
noncomputable def estimate (y : ℕ → ℝ) (ℓ : ℕ) : E :=
  phaseEstimate D σ2 δ ℓ (survivors D σ2 δ y ℓ) fun j ↦ y (phaseStart D σ2 δ y ℓ + j)

variable {y y' : ℕ → ℝ} {ℓ : ℕ}

lemma phase_eq (y : ℕ → ℝ) (ℓ : ℕ) :
    phase D σ2 δ y ℓ = (survivors D σ2 δ y ℓ, phaseStart D σ2 δ y ℓ) :=
  (rfl)

lemma estimate_def (y : ℕ → ℝ) (ℓ : ℕ) :
    estimate D σ2 δ y ℓ =
      phaseEstimate D σ2 δ ℓ (survivors D σ2 δ y ℓ) fun j ↦ y (phaseStart D σ2 δ y ℓ + j) :=
  (rfl)

@[simp]
lemma survivors_zero (y : ℕ → ℝ) : survivors D σ2 δ y 0 = univ := (rfl)

@[simp]
lemma phaseStart_zero (y : ℕ → ℝ) : phaseStart D σ2 δ y 0 = 0 := (rfl)

lemma survivors_succ (y : ℕ → ℝ) (ℓ : ℕ) :
    survivors D σ2 δ y (ℓ + 1) = eliminate φ ℓ (survivors D σ2 δ y ℓ) (estimate D σ2 δ y ℓ) :=
  (rfl)

lemma phaseStart_succ (y : ℕ → ℝ) (ℓ : ℕ) :
    phaseStart D σ2 δ y (ℓ + 1) =
      phaseStart D σ2 δ y ℓ + phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ) :=
  (rfl)

lemma phase_succ (y : ℕ → ℝ) (ℓ : ℕ) :
    phase D σ2 δ y (ℓ + 1) =
      (eliminate φ ℓ (phase D σ2 δ y ℓ).1
          (phaseEstimate D σ2 δ ℓ (phase D σ2 δ y ℓ).1 fun j ↦ y ((phase D σ2 δ y ℓ).2 + j)),
        (phase D σ2 δ y ℓ).2 + phaseLength D σ2 δ ℓ (phase D σ2 δ y ℓ).1) :=
  (rfl)

/-- The survivors of every phase are nonempty. -/
lemma survivors_nonempty (y : ℕ → ℝ) (ℓ : ℕ) : (survivors D σ2 δ y ℓ).Nonempty := by
  induction ℓ with
  | zero => exact univ_nonempty_iff.2 (D.design ∅).nonempty
  | succ ℓ ih =>
    rw [survivors_succ]
    exact eliminate_nonempty ih _

lemma survivors_succ_subset (y : ℕ → ℝ) (ℓ : ℕ) :
    survivors D σ2 δ y (ℓ + 1) ⊆ survivors D σ2 δ y ℓ := by
  intro a ha
  rw [survivors_succ] at ha
  exact (mem_eliminate.1 ha).1

lemma phaseStart_lt_phaseStart_succ (y : ℕ → ℝ) (ℓ : ℕ) :
    phaseStart D σ2 δ y ℓ < phaseStart D σ2 δ y (ℓ + 1) := by
  rw [phaseStart_succ]
  exact Nat.lt_add_of_pos_right (phaseLength_pos ℓ _)

lemma strictMono_phaseStart (y : ℕ → ℝ) : StrictMono (phaseStart D σ2 δ y) :=
  strictMono_nat_of_lt_succ (phaseStart_lt_phaseStart_succ y)

/-- Phase `ℓ` starts at round `ℓ` or later, since every phase has at least one round. -/
lemma le_phaseStart (y : ℕ → ℝ) (ℓ : ℕ) : ℓ ≤ phaseStart D σ2 δ y ℓ :=
  (strictMono_phaseStart y).le_apply

/-- **The state of a phase only depends on the rewards before it**: if `y` and `y'` agree before
round `t` and phase `ℓ` of `y` starts at or before `t`, the phases `ℓ` of `y` and `y'` agree. -/
theorem phase_congr {t : ℕ} (hyy' : ∀ s < t, y s = y' s) (hℓ : phaseStart D σ2 δ y ℓ ≤ t) :
    phase D σ2 δ y ℓ = phase D σ2 δ y' ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have hle := (phaseStart_lt_phaseStart_succ y ℓ).le.trans hℓ
    have h := ih hle
    rw [phase_succ, phase_succ, ← h, phaseEstimate_def, phaseEstimate_def,
      leastSquaresEstimate_congr (fun _ _ ↦ rfl) fun j hj ↦ hyy' _ ?_]
    rw [phaseStart_succ] at hℓ
    rw [phase_eq] at h ⊢
    simp only at hj ⊢
    lia

/-- If `y` and `y'` agree before round `t`, phase `ℓ` of `y` starts at or before `t` iff phase `ℓ`
of `y'` does. -/
lemma phaseStart_le_iff_of_eq {t : ℕ} (hyy' : ∀ s < t, y s = y' s) :
    phaseStart D σ2 δ y ℓ ≤ t ↔ phaseStart D σ2 δ y' ℓ ≤ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [phaseStart, ← phase_congr hyy' h]
  · rwa [phaseStart, phase_congr hyy' (by rwa [phaseStart, ← phase_congr (fun s hs ↦
      (hyy' s hs).symm) h])]

variable (D σ2 δ) in
/-- The **phase of round `n`** for the sequence of rewards `y`: the last phase `ℓ ≤ n` that starts
at or before `n`. -/
noncomputable def phaseIndex (y : ℕ → ℝ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ ↦ phaseStart D σ2 δ y ℓ ≤ n) n

variable (D σ2 δ) in
/-- The **arm played at round `n`** for the sequence of rewards `y`: the arm at the position of
round `n` in the schedule of its phase. -/
noncomputable def nextArm (y : ℕ → ℝ) (n : ℕ) : α :=
  phaseArm D σ2 δ (phaseIndex D σ2 δ y n) (survivors D σ2 δ y (phaseIndex D σ2 δ y n))
    (n - phaseStart D σ2 δ y (phaseIndex D σ2 δ y n))

variable {n : ℕ}

lemma phaseIndex_def (y : ℕ → ℝ) (n : ℕ) :
    phaseIndex D σ2 δ y n = Nat.findGreatest (fun ℓ ↦ phaseStart D σ2 δ y ℓ ≤ n) n :=
  (rfl)

lemma nextArm_def (y : ℕ → ℝ) (n : ℕ) :
    nextArm D σ2 δ y n =
      phaseArm D σ2 δ (phaseIndex D σ2 δ y n) (survivors D σ2 δ y (phaseIndex D σ2 δ y n))
        (n - phaseStart D σ2 δ y (phaseIndex D σ2 δ y n)) :=
  (rfl)

lemma phaseIndex_le (y : ℕ → ℝ) (n : ℕ) : phaseIndex D σ2 δ y n ≤ n :=
  Nat.findGreatest_le n

/-- Round `n` lies after the start of its phase. -/
lemma phaseStart_phaseIndex_le (y : ℕ → ℝ) (n : ℕ) :
    phaseStart D σ2 δ y (phaseIndex D σ2 δ y n) ≤ n :=
  Nat.findGreatest_spec (P := fun ℓ ↦ phaseStart D σ2 δ y ℓ ≤ n) (Nat.zero_le n) (by simp)

/-- Round `n` lies before the start of the phase after its phase. -/
lemma lt_phaseStart_phaseIndex_succ (y : ℕ → ℝ) (n : ℕ) :
    n < phaseStart D σ2 δ y (phaseIndex D σ2 δ y n + 1) := by
  by_contra h
  push Not at h
  have h1 : phaseIndex D σ2 δ y n + 1 ≤ n := (le_phaseStart y _).trans h
  have h2 := Nat.le_findGreatest (P := fun ℓ ↦ phaseStart D σ2 δ y ℓ ≤ n) h1 h
  rw [← phaseIndex_def] at h2
  lia

/-- Round `n` lies in phase `ℓ` iff `t_ℓ ≤ n < t_{ℓ+1}`. -/
lemma phaseIndex_eq_of_le_of_lt (h₁ : phaseStart D σ2 δ y ℓ ≤ n)
    (h₂ : n < phaseStart D σ2 δ y (ℓ + 1)) : phaseIndex D σ2 δ y n = ℓ := by
  have hmono := (strictMono_phaseStart (D := D) (σ2 := σ2) (δ := δ) y).monotone
  have h₃ := phaseStart_phaseIndex_le (D := D) (σ2 := σ2) (δ := δ) y n
  have h₄ := lt_phaseStart_phaseIndex_succ (D := D) (σ2 := σ2) (δ := δ) y n
  rcases lt_trichotomy (phaseIndex D σ2 δ y n) ℓ with h | h | h
  · have := hmono (Nat.succ_le_of_lt h)
    lia
  · exact h
  · have := hmono (Nat.succ_le_of_lt h)
    lia

/-- The phase of round `n` only depends on the rewards before `n`. -/
lemma phaseIndex_congr (hyy' : ∀ s < n, y s = y' s) :
    phaseIndex D σ2 δ y n = phaseIndex D σ2 δ y' n := by
  simp_rw [phaseIndex_def, phaseStart_le_iff_of_eq hyy']

/-- **The action of round `n` only depends on the rewards before `n`.** -/
theorem nextArm_congr (hyy' : ∀ s < n, y s = y' s) :
    nextArm D σ2 δ y n = nextArm D σ2 δ y' n := by
  have h := phase_congr hyy' (phaseStart_phaseIndex_le (D := D) (σ2 := σ2) (δ := δ) y n)
  rw [nextArm_def, nextArm_def, ← phaseIndex_congr hyy', survivors, phaseStart, h]
  rfl

/-- The rounds of phase `ℓ` play the arms of its schedule. -/
lemma nextArm_phaseStart_add {j : ℕ}
    (hj : j < phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ)) :
    nextArm D σ2 δ y (phaseStart D σ2 δ y ℓ + j) = phaseArm D σ2 δ ℓ (survivors D σ2 δ y ℓ) j := by
  have hidx : phaseIndex D σ2 δ y (phaseStart D σ2 δ y ℓ + j) = ℓ :=
    phaseIndex_eq_of_le_of_lt (Nat.le_add_right _ _) (by rw [phaseStart_succ]; lia)
  rw [nextArm_def, hidx, Nat.add_sub_cancel_left]

/-- The arm of round `n` survives the phases up to the phase of `n`. -/
lemma nextArm_mem_survivors (y : ℕ → ℝ) (n : ℕ) :
    nextArm D σ2 δ y n ∈ survivors D σ2 δ y (phaseIndex D σ2 δ y n) := by
  rw [nextArm_def]
  refine phaseArm_mem (survivors_nonempty y _) ?_
  have h₁ := phaseStart_phaseIndex_le (D := D) (σ2 := σ2) (δ := δ) y n
  have h₂ := lt_phaseStart_phaseIndex_succ (D := D) (σ2 := σ2) (δ := δ) y n
  rw [phaseStart_succ] at h₂
  lia

/-! ### Measurability -/

/-- The state of phase `ℓ` depends measurably on the sequence of rewards. -/
theorem measurable_phase (ℓ : ℕ) : Measurable fun y : ℕ → ℝ ↦ phase D σ2 δ y ℓ := by
  induction ℓ with
  | zero => exact measurable_const
  | succ ℓ ih =>
    -- the state of phase `ℓ + 1` is a function of the rewards and of the countable state of
    -- phase `ℓ`, measurable in the rewards for each fixed state
    let F : (ℕ → ℝ) × (Finset α × ℕ) → Finset α × ℕ := fun q ↦
      (eliminate φ ℓ q.2.1 (phaseEstimate D σ2 δ ℓ q.2.1 fun j ↦ q.1 (q.2.2 + j)),
        q.2.2 + phaseLength D σ2 δ ℓ q.2.1)
    have hF : Measurable F := by
      refine measurable_from_prod_countable_left fun p ↦
        Measurable.prodMk ?_ (measurable_const' fun _ _ ↦ rfl)
      refine measurable_finset_iff.2 fun a ↦ ?_
      simp only [mem_eliminate]
      refine measurable_const.and (Measurable.forall fun b ↦ measurable_const.imp ?_)
      refine measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)
      simp only [phaseEstimate_def, leastSquaresEstimate_eq_sum, sum_inner, real_inner_smul_left]
      exact Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply _).mul_const _
    have heq : (fun y ↦ phase D σ2 δ y (ℓ + 1)) = F ∘ fun y ↦ (y, phase D σ2 δ y ℓ) :=
      funext fun y ↦ phase_succ y ℓ
    rw [heq]
    exact hF.comp (measurable_id.prodMk ih)

/-- The phase of round `n` depends measurably on the sequence of rewards. -/
theorem measurable_phaseIndex (n : ℕ) : Measurable fun y : ℕ → ℝ ↦ phaseIndex D σ2 δ y n :=
  measurable_findGreatest fun k _ ↦ measurable_phase k (MeasurableSet.of_discrete (s :=
    {p : Finset α × ℕ | p.2 ≤ n}))

/-- The arm of round `n` depends measurably on the sequence of rewards. -/
theorem measurable_nextArm [MeasurableSpace α] (n : ℕ) :
    Measurable fun y : ℕ → ℝ ↦ nextArm D σ2 δ y n := by
  let G : (ℕ → ℝ) × ℕ → α := fun q ↦
    phaseArm D σ2 δ q.2 (survivors D σ2 δ q.1 q.2) (n - phaseStart D σ2 δ q.1 q.2)
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun ℓ ↦ ?_
    have heq : (fun y ↦ G (y, ℓ)) =
        (fun p : Finset α × ℕ ↦ phaseArm D σ2 δ ℓ p.1 (n - p.2)) ∘ fun y ↦ phase D σ2 δ y ℓ :=
      funext fun y ↦ rfl
    rw [heq]
    exact (measurable_of_countable _).comp (measurable_phase ℓ)
  have heq : (fun y ↦ nextArm D σ2 δ y n) = G ∘ fun y ↦ (y, phaseIndex D σ2 δ y n) :=
    funext fun y ↦ nextArm_def y n
  rw [heq]
  exact hG.comp (measurable_id.prodMk (measurable_phaseIndex n))

end PhasedElimination

/-! ### The algorithm -/

section Algorithm

variable [Fintype α] [MeasurableSpace α] {𝓞 : Type*} [MeasurableSpace 𝓞]
  {D : DesignSelection φ} {σ2 : ℝ≥0} {δ : ℝ}

variable (D σ2 δ) in
/-- **Phased elimination with optimal designs** [LS, Algorithm 12] for the design selection `D`,
the variance proxy `σ2` and the confidence level `δ`: the deterministic algorithm playing at round
`n` the arm `PhasedElimination.nextArm D σ2 δ y n` for the rewards `y` of the history. It ignores
the contexts. -/
noncomputable def phasedElimination : Algorithm 𝓞 α ℝ :=
  Algorithm.deterministic (fun n p ↦ PhasedElimination.nextArm D σ2 δ (histReward p.1) n)
    fun n ↦ (PhasedElimination.measurable_nextArm n).comp
      ((measurable_histReward n).comp measurable_fst)

lemma phasedElimination_eq_deterministic :
    phasedElimination (𝓞 := 𝓞) D σ2 δ =
      Algorithm.deterministic (fun n p ↦ PhasedElimination.nextArm D σ2 δ (histReward p.1) n)
        fun n ↦ (PhasedElimination.measurable_nextArm n).comp
          ((measurable_histReward n).comp measurable_fst) :=
  (rfl)

@[simp]
lemma phasedElimination_policy (n : ℕ) :
    (phasedElimination (𝓞 := 𝓞) D σ2 δ).policy n =
      Kernel.deterministic (fun p : Hist 𝓞 α ℝ n × 𝓞 ↦
        PhasedElimination.nextArm D σ2 δ (histReward p.1) n)
        ((PhasedElimination.measurable_nextArm n).comp
          ((measurable_histReward n).comp measurable_fst)) := by
  rw [phasedElimination_eq_deterministic, Algorithm.deterministic_policy]

instance : (phasedElimination (𝓞 := 𝓞) D σ2 δ).IsDeterministic where
  exists_nextAction n := ⟨_, _, phasedElimination_policy n⟩

namespace PhasedElimination

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment 𝓞 α ℝ} {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **The run lemma of phased elimination**: along a run, the action of round `n` is almost surely
the arm `nextArm D σ2 δ y n` for the rewards `y = (Y · ω)` of the run. -/
lemma action_ae_all_eq [MeasurableSingletonClass α] [SFinite P]
    (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 δ) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = nextArm D σ2 δ (fun s ↦ Y s ω) n := by
  rw [phasedElimination_eq_deterministic] at h
  filter_upwards [h.action_ae_all_eq_deterministic] with ω hω n
  rw [hω n]
  exact nextArm_congr fun s hs ↦ histReward_history hs ω

end PhasedElimination

end Algorithm


end LMLExplore.Bandits
