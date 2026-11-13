/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import LMLExplore.Order.Iterate
public import LMLExplore.Topology.MetricSpace.Contracting
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Abstract dynamic programming

Let `E` be an ordered real vector space with an order unit `e`, normed by the order-unit norm
(`∀ x, orderUnitNorm e x = ‖x‖`), such as `ι → ℝ` with `ι` finite and `e = 1`
(`orderUnitNorm_one_eq_norm`). Let `T d : E → E`, for `d` in a type `D` of *decisions*, be maps
satisfying Blackwell's conditions with a common modulus `γ < 1`, and let `B : E → E` be their
*uniform supremum* (`IsUniformSup`): `T d x ≤ B x` for every `d`, and for every `x` and `ε > 0`
some decision `d` is *`ε`-greedy* for `x`, `B x - ε • e ≤ T d x`. The supremum need not be
attained; a decision `d` with `T d x = B x` is *greedy* for `x`, and an attained maximum
(`B x` the greatest element of `{T d x | d : D}`) is the case where every `x` has a greedy
decision.

For a Markov decision process, `E` is a space of bounded value functions, `T d` is the evaluation
operator `v ↦ r_d + γ P_d v` of a deterministic stationary policy `d` and `B` is the Bellman
optimality operator, whose value at `v` is the supremum over the actions at every state of
`r(s, a) + γ ∫ v dP(s, a)`. The results of this file then say that the optimal value is the least
upper bound of the values of the policies, and the value of a greedy policy when one exists, and
that policy iteration and modified policy iteration (with value iteration as the case of a single
evaluation step) converge geometrically to it, the latter when started from `x 0 ≤ B (x 0)`. They
only use monotonicity and Blackwell's conditions (`IsBlackwell`), following Bertsekas's abstract
dynamic programming. The fixed point of `B` is taken as a hypothesis; completeness of `E` is only
assumed to give the maps `T d` their fixed points, in `isLUB_iUnion_fixedPoints`. Dropping
attainment costs an Archimedean step, `le_of_forall_sub_smul_le`, which needs the closedness of the
lower intervals `Set.Iic x` and the compatibility of the order with scalars (`PosSMulMono`).

## Main definitions

* `LMLExplore.IsUniformSup e T B`: `B` is the uniform supremum of the maps `T d`.
* `LMLExplore.IsPolicyIteration T B d v`: `v k` is the fixed point of `T (d k)` and `d (k + 1)` is
  greedy for `v k`.
* `LMLExplore.IsModifiedPolicyIteration T B m d x`: `d k` is greedy for `x k` and
  `x (k + 1) = (T (d k))^[m k + 1] (x k)`.

## Main statements

* `LMLExplore.IsBlackwell.contractingWith`: a map satisfying Blackwell's conditions with modulus
  `γ < 1` is a `γ`-contraction, and `LMLExplore.IsBlackwell.of_isUniformSup` says that `B`
  satisfies them (`LMLExplore.IsBlackwell.of_isGreatest_range` for an attained maximum).
* `LMLExplore.IsUniformSup.isLUB_range`: `B x` is the least upper bound of the values `T d x`, so
  `B` is determined by the maps `T d` (`LMLExplore.IsUniformSup.unique`).
* `LMLExplore.IsBlackwell.le_of_map_le`, `LMLExplore.IsBlackwell.le_of_le_map`: if `T x ≤ x` then
  the fixed point of `T` is below `x`, and if `x ≤ T x` it is above;
  `LMLExplore.IsBlackwell.sub_smul_le_of_sub_smul_le_map`: if `x - ε • e ≤ T x` it is above
  `x - (ε / (1 - γ)) • e`.
* `LMLExplore.isLUB_iUnion_fixedPoints`: the fixed point of `B` is the least upper bound of the
  fixed points of the maps `T d`; `LMLExplore.mem_upperBounds_iUnion_fixedPoints`: it is above
  them.
* `LMLExplore.isGreatest_iUnion_fixedPoints`: when a decision is greedy for it, the fixed point of
  `B` is the greatest fixed point of the maps `T d`; `LMLExplore.isFixedPt_of_map_eq`: it is the
  fixed point of every decision greedy for it.
* `LMLExplore.IsUniformSup.exists_map_eq`: with finitely many decisions, every `x` has a greedy
  decision.
* `LMLExplore.map_le_of_le_map`, `LMLExplore.IsPolicyIteration.map_le`: policy improvement; the
  values `v k` of policy iteration satisfy `v k ≤ B (v k) ≤ v (k + 1)`.
* `LMLExplore.IsPolicyIteration.iterate_le`, `LMLExplore.IsPolicyIteration.le_of_isFixedPt`,
  `LMLExplore.IsPolicyIteration.norm_sub_le`: `B^[k] (v 0) ≤ v k ≤ x` for the fixed point `x` of
  `B`, hence `‖v k - x‖ ≤ γ ^ k * ‖v 0 - x‖`.
* `LMLExplore.IsPolicyIteration.exists_le_card_eq`: with finitely many decisions, policy iteration
  reaches the fixed point of `B` after at most `Nat.card D` improvements.
* `LMLExplore.IsModifiedPolicyIteration.iterate_le`,
  `LMLExplore.IsModifiedPolicyIteration.le_of_isFixedPt`,
  `LMLExplore.IsModifiedPolicyIteration.norm_sub_le`: the same bounds for modified policy iteration
  started from `x 0 ≤ B (x 0)`.

The results on policy iteration and modified policy iteration assume no attainment beyond the
greedy decisions that the runs record: they assume `T d x ≤ B x` for every decision `d` and, where
needed, that `B` is monotone or satisfies Blackwell's conditions. A uniform supremum satisfies
`T d x ≤ B x` (`IsUniformSup.le`) and, with closed lower intervals and `PosSMulMono`, a uniform
supremum of maps satisfying Blackwell's conditions satisfies them, hence is monotone
(`IsBlackwell.of_isUniformSup`). Taking these properties of `B` as hypotheses keeps policy
improvement, finite termination of policy iteration and the results on modified policy iteration
available on spaces without closed lower intervals, where the Archimedean step is not available;
the comparison of policy iteration with the fixed point of `B`
(`IsPolicyIteration.le_of_isFixedPt`, `IsPolicyIteration.norm_sub_le`) still needs closed lower
intervals.

## References

* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
* [D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd edition, 2022][Ber22], Chapter 2
* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.4–6.5
-/

public section

open Set Function Filter Topology NNReal

namespace LMLExplore

variable {E D : Type*}

/-! ### Uniform suprema -/

section UniformSup

variable [AddCommGroup E] [PartialOrder E] [Module ℝ E]

/-- `B` is the *uniform supremum* of the maps `T d` for the unit `e`: `T d x ≤ B x` for every
decision `d`, and for every `x` and `ε > 0` some decision `d` is *`ε`-greedy* for `x`,
`B x - ε • e ≤ T d x`. The supremum need not be attained. -/
structure IsUniformSup (e : E) (T : D → E → E) (B : E → E) : Prop where
  le (d : D) (x : E) : T d x ≤ B x
  exists_sub_smul_le (x : E) (ε : ℝ) (hε : 0 < ε) : ∃ d, B x - ε • e ≤ T d x

/-- An attained maximum is a uniform supremum: if `B x` is the greatest of the values `T d x`, a
decision greedy for `x` is `ε`-greedy for every `ε > 0`. -/
lemma IsUniformSup.of_isGreatest_range [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : 0 ≤ e) {T : D → E → E} {B : E → E} (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) :
    IsUniformSup e T B where
  le d x := (hB x).2 ⟨d, rfl⟩
  exists_sub_smul_le x ε hε := by
    obtain ⟨d, hd⟩ := (hB x).1
    exact ⟨d, hd.symm ▸ sub_le_self _ (smul_nonneg hε.le he)⟩

end UniformSup

/-! ### Blackwell's conditions for an attained maximum -/

section Blackwell

variable [AddCommGroup E] [PartialOrder E] [Module ℝ E] {e : E} {γ : ℝ≥0}

/-- The maximum of maps satisfying Blackwell's conditions with modulus `γ` satisfies them, when it
is attained: `B x` is the greatest of the values `T d x`. Unlike `IsBlackwell.of_isUniformSup`, this
needs no approximation step. -/
lemma IsBlackwell.of_isGreatest_range [IsOrderedAddMonoid E] {T : D → E → E} {B : E → E}
    (hT : ∀ d, IsBlackwell e γ (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) :
    IsBlackwell e γ B where
  monotone x y hxy := by
    obtain ⟨d, hd⟩ := (hB x).1
    rw [← hd]
    exact ((hT d).monotone hxy).trans ((hB y).2 ⟨d, rfl⟩)
  map_add_smul_le x c hc := by
    obtain ⟨d, hd⟩ := (hB (x + c • e)).1
    rw [← hd]
    refine ((hT d).map_add_smul_le x c hc).trans ?_
    gcongr
    exact (hB x).2 ⟨d, rfl⟩

end Blackwell

/-! ### Greedy decisions, policy iteration and modified policy iteration -/

section Order

variable {T : D → E → E} {B : E → E} {x : E}

/-- A decision greedy for a fixed point of `B` has it as fixed point. -/
lemma isFixedPt_of_map_eq (hx : IsFixedPt B x) {d : D} (hd : T d x = B x) :
    IsFixedPt (T d) x :=
  hd.trans hx

/-- `v` is a run of *policy iteration* with decisions `d`: `v k` is the fixed point of `T (d k)`,
and `d (k + 1)` is greedy for `v k`. -/
structure IsPolicyIteration (T : D → E → E) (B : E → E) (d : ℕ → D) (v : ℕ → E) : Prop where
  isFixedPt (k : ℕ) : IsFixedPt (T (d k)) (v k)
  map_eq (k : ℕ) : T (d (k + 1)) (v k) = B (v k)

/-- `x` is a run of *modified policy iteration* with decisions `d` and numbers of evaluation steps
`m + 1`: `d k` is greedy for `x k` and `x (k + 1) = (T (d k))^[m k + 1] (x k)`. For `m = 0` it is
value iteration, `x (k + 1) = B (x k)`. -/
structure IsModifiedPolicyIteration (T : D → E → E) (B : E → E) (m : ℕ → ℕ) (d : ℕ → D)
    (x : ℕ → E) : Prop where
  map_eq (k : ℕ) : T (d k) (x k) = B (x k)
  eq_iterate (k : ℕ) : x (k + 1) = (T (d k))^[m k + 1] (x k)

variable [Preorder E]

/-- A fixed point `x` of a map `T d` is below `B x` when `T d x ≤ B x` for every decision `d`, for
instance when `B` is the uniform supremum of the `T d`. -/
lemma le_map_of_isFixedPt (hB : ∀ d, T d x ≤ B x) {d : D} (hx : IsFixedPt (T d) x) : x ≤ B x :=
  hx.symm.le.trans (hB d)

/-- Each value of policy iteration is below its image by `B`, when `T d x ≤ B x` for every
decision `d` and every `x`. -/
lemma IsPolicyIteration.le_map (hB : ∀ d x, T d x ≤ B x) {d : ℕ → D} {v : ℕ → E}
    (h : IsPolicyIteration T B d v) (k : ℕ) : v k ≤ B (v k) :=
  le_map_of_isFixedPt (fun d ↦ hB d (v k)) (h.isFixedPt k)

namespace IsModifiedPolicyIteration

variable {m : ℕ → ℕ} {d : ℕ → D} {u : ℕ → E}

/-- Modified policy iteration started below its image by `B` stays below its image by `B`, when
`T d x ≤ B x` for every decision `d` and every `x`. -/
theorem le_map (hT : ∀ d, Monotone (T d)) (hB : ∀ d x, T d x ≤ B x)
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) : u k ≤ B (u k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    -- With `f = T (d k)`, `u k ≤ f (u k)`, so the iterates of `f` at `u k` are nondecreasing.
    have hmono := (hT (d k)).monotone_iterate_of_le_map (ih.trans_eq (h.map_eq k).symm)
    calc u (k + 1) = (T (d k))^[m k + 1] (u k) := h.eq_iterate k
      _ ≤ (T (d k))^[m k + 1 + 1] (u k) := hmono (Nat.le_succ _)
      _ = T (d k) (u (k + 1)) := by rw [iterate_succ_apply', h.eq_iterate k]
      _ ≤ B (u (k + 1)) := hB (d k) _

/-- Each value of modified policy iteration started below its image by `B` is above the image by
`B` of the previous one. -/
theorem map_le (hT : ∀ d, Monotone (T d)) (hB : ∀ d x, T d x ≤ B x)
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) :
    B (u k) ≤ u (k + 1) := by
  have hmono :=
    (hT (d k)).monotone_iterate_of_le_map ((h.le_map hT hB h₀ k).trans_eq (h.map_eq k).symm)
  calc B (u k) = (T (d k))^[1] (u k) := by rw [iterate_one, h.map_eq k]
    _ ≤ (T (d k))^[m k + 1] (u k) := hmono (Nat.le_add_left 1 (m k))
    _ = u (k + 1) := (h.eq_iterate k).symm

/-- The values of modified policy iteration started below their image by a monotone `B` are above
the iterates of `B`: `B^[k] (u 0) ≤ u k`. With closed lower intervals and `PosSMulMono`, a uniform
supremum of maps satisfying Blackwell's conditions is monotone (`IsBlackwell.of_isUniformSup`). -/
theorem iterate_le (hT : ∀ d, Monotone (T d)) (hB : ∀ d x, T d x ≤ B x) (hBm : Monotone B)
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) : B^[k] (u 0) ≤ u k :=
  hBm.iterate_le_of_map_le_succ (h.map_le hT hB h₀) k

end IsModifiedPolicyIteration

end Order

section Normed

variable [NormedAddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E] {e : E}
  {γ : ℝ≥0}

/-! ### Contraction and comparison -/

namespace IsBlackwell

variable {T : E → E}

/-- A map satisfying Blackwell's conditions with modulus `γ < 1` is a `γ`-contraction for the
order-unit norm. -/
lemma contractingWith (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsBlackwell e γ T)
    (hγ : γ < 1) : ContractingWith γ T :=
  ⟨hγ, hT.lipschitzWith hnorm⟩

/-- If `T` satisfies Blackwell's conditions with modulus `γ` and has the fixed point `y`, a sequence
`u` below `y` with `T (u k) ≤ u (k + 1)` for all `k` satisfies `‖u k - y‖ ≤ γ ^ k * ‖u 0 - y‖`,
so it converges to `y` geometrically when `γ < 1`. -/
theorem norm_sub_le_of_map_le_succ (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsBlackwell e γ T) {y : E} (hy : IsFixedPt T y) {u : ℕ → E} (hu : ∀ k, u k ≤ y)
    (hsucc : ∀ k, T (u k) ≤ u (k + 1)) (k : ℕ) : ‖u k - y‖ ≤ γ ^ k * ‖u 0 - y‖ := by
  -- `T^[k] (u 0) ≤ u k ≤ y`, and `T^[k]` is `γ ^ k`-Lipschitz with fixed point `y`.
  have hle : T^[k] (u 0) ≤ u k := hT.monotone.iterate_le_of_map_le_succ hsucc k
  calc ‖u k - y‖ = orderUnitNorm e (y - u k) := by rw [hnorm, norm_sub_rev]
    _ ≤ orderUnitNorm e (y - T^[k] (u 0)) :=
      orderUnitNorm_le_orderUnitNorm_of_nonneg (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm)
        (sub_nonneg.2 (hu k)) (sub_le_sub_left hle y)
    _ = dist (T^[k] y) (T^[k] (u 0)) := by rw [hnorm, iterate_fixed hy, dist_eq_norm]
    _ ≤ γ ^ k * dist y (u 0) := by
      simpa using ((hT.lipschitzWith hnorm).iterate k).dist_le_mul y (u 0)
    _ = γ ^ k * ‖u 0 - y‖ := by rw [dist_comm, dist_eq_norm]

variable {x y : E}

/-- If `T` satisfies Blackwell's conditions with modulus `γ < 1` and `T x ≤ x`, then the fixed
point of `T` is below `x`. -/
theorem le_of_map_le [ClosedIicTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsBlackwell e γ T) (hγ : γ < 1) (hy : IsFixedPt T y) (h : T x ≤ x) : y ≤ x :=
  le_of_tendsto' ((hT.contractingWith hnorm hγ).tendsto_iterate_of_isFixedPt hy x) fun n ↦ by
    simpa using hT.monotone.antitone_iterate_of_map_le h (Nat.zero_le n)

/-- If `T` satisfies Blackwell's conditions with modulus `γ < 1` and `x ≤ T x`, then the fixed
point of `T` is above `x`. -/
theorem le_of_le_map [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsBlackwell e γ T) (hγ : γ < 1) (hy : IsFixedPt T y) (h : x ≤ T x) : x ≤ y :=
  ge_of_tendsto' ((hT.contractingWith hnorm hγ).tendsto_iterate_of_isFixedPt hy x) fun n ↦ by
    simpa using hT.monotone.monotone_iterate_of_le_map h (Nat.zero_le n)

/-- If `T` satisfies Blackwell's conditions with modulus `γ < 1` and `x - ε • e ≤ T x` with
`ε ≥ 0`, then the fixed point of `T` is above `x - (ε / (1 - γ)) • e`. For a decision `ε`-greedy for
the fixed point `x` of the uniform supremum `B` of maps `T d`, this bounds the loss of following the
decision by `ε / (1 - γ)`. The case `ε = 0` is `IsBlackwell.le_of_le_map`. -/
theorem sub_smul_le_of_sub_smul_le_map [ClosedIciTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsBlackwell e γ T) (hγ : γ < 1)
    (hy : IsFixedPt T y) {ε : ℝ} (hε : 0 ≤ ε) (h : x - ε • e ≤ T x) :
    x - (ε / (1 - γ)) • e ≤ y := by
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  set c := ε / (1 - γ)
  have hεc : ε + γ * c = c := by simp only [c]; field_simp; ring
  refine hT.le_of_le_map hnorm hγ hy ?_
  -- Blackwell's condition at `x - c • e` gives `T x ≤ T (x - c • e) + (γ * c) • e`.
  have hle := hT.map_add_smul_le (x - c • e) c (div_nonneg hε hγ'.le)
  rw [sub_add_cancel] at hle
  calc x - c • e = x - ε • e - (γ * c) • e := by rw [sub_sub, ← add_smul, hεc]
    _ ≤ T x - (γ * c) • e := sub_le_sub_right h _
    _ ≤ T (x - c • e) := sub_le_iff_le_add.2 hle

/-- The uniform supremum of maps satisfying Blackwell's conditions with modulus `γ` satisfies
them. -/
theorem of_isUniformSup [PosSMulMono ℝ E] [ClosedIicTopology E] {T : D → E → E} {B : E → E}
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d))
    (hB : IsUniformSup e T B) : IsBlackwell e γ B where
  monotone x y hxy := le_of_forall_sub_smul_le hnorm fun ε hε ↦ by
    obtain ⟨d, hd⟩ := hB.exists_sub_smul_le x ε hε
    exact hd.trans (((hT d).monotone hxy).trans (hB.le d y))
  map_add_smul_le x c hc := le_of_forall_sub_smul_le hnorm fun ε hε ↦ by
    obtain ⟨d, hd⟩ := hB.exists_sub_smul_le (x + c • e) ε hε
    exact hd.trans (((hT d).map_add_smul_le x c hc).trans (add_le_add (hB.le d x) le_rfl))

end IsBlackwell

/-! ### Optimality of greedy decisions -/

variable {T : D → E → E} {B : E → E} {x : E}

/-- A uniform supremum is the pointwise least upper bound: `B x` is the least upper bound of the
values `T d x`. -/
theorem IsUniformSup.isLUB_range [PosSMulMono ℝ E] [ClosedIicTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hB : IsUniformSup e T B) (x : E) :
    IsLUB (range fun d ↦ T d x) (B x) := by
  refine ⟨forall_mem_range.2 fun d ↦ hB.le d x, fun b hb ↦ ?_⟩
  refine le_of_forall_sub_smul_le hnorm fun ε hε ↦ ?_
  obtain ⟨d, hd⟩ := hB.exists_sub_smul_le x ε hε
  exact hd.trans (hb ⟨d, rfl⟩)

/-- The uniform supremum of the maps `T d` is unique. -/
theorem IsUniformSup.unique [PosSMulMono ℝ E] [ClosedIicTopology E] {B' : E → E}
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hB : IsUniformSup e T B) (hB' : IsUniformSup e T B') :
    B = B' :=
  funext fun x ↦ (hB.isLUB_range hnorm x).unique (hB'.isLUB_range hnorm x)

/-- **Existence of greedy decisions**: with finitely many decisions, a uniform supremum is
attained, so every `x` has a greedy decision. -/
theorem IsUniformSup.exists_map_eq [Finite D] [PosSMulMono ℝ E] [ClosedIicTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hB : IsUniformSup e T B) (x : E) :
    ∃ d, T d x = B x := by
  obtain ⟨d₀, -⟩ := hB.exists_sub_smul_le x 1 one_pos
  have := Nonempty.intro d₀
  by_contra! h
  -- Each decision `d` is not `ε d`-greedy for some `ε d > 0`, so no decision is `ε`-greedy for
  -- the least of the `ε d`.
  have hε (d : D) : ∃ ε : ℝ, 0 < ε ∧ ¬B x - ε • e ≤ T d x := by
    by_contra! hd
    exact h d ((hB.le d x).antisymm (le_of_forall_sub_smul_le hnorm hd))
  choose ε hε_pos hε using hε
  obtain ⟨d₁, hd₁⟩ := Finite.exists_min ε
  obtain ⟨d, hd⟩ := hB.exists_sub_smul_le x (ε d₁) (hε_pos d₁)
  refine hε d (le_trans ?_ hd)
  have he := (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm).nonneg
  exact sub_le_sub_left (smul_le_smul_of_nonneg_right (hd₁ d) he) _

/-- The fixed point `x` of `B` is above the fixed points of the maps `T d` when `T d x ≤ B x` for
every decision `d`, for instance when `B` is the uniform supremum of the `T d`. -/
theorem mem_upperBounds_iUnion_fixedPoints [ClosedIicTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ d, T d x ≤ B x) (hx : IsFixedPt B x) : x ∈ upperBounds (⋃ d, fixedPoints (T d)) := by
  intro y hy
  obtain ⟨d, hy⟩ := mem_iUnion.1 hy
  exact (hT d).le_of_map_le hnorm hγ hy ((hB d).trans_eq hx)

/-- **Optimality without attainment**: the fixed point of the uniform supremum `B` of maps `T d`
satisfying Blackwell's conditions with modulus `γ < 1` is the least upper bound of the fixed points
of the maps `T d`, which need not be attained. -/
theorem isLUB_iUnion_fixedPoints [CompleteSpace E] [PosSMulMono ℝ E] [ClosedIicTopology E]
    [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hB : IsUniformSup e T B)
    (hx : IsFixedPt B x) : IsLUB (⋃ d, fixedPoints (T d)) x := by
  refine ⟨mem_upperBounds_iUnion_fixedPoints hnorm hT hγ (fun d ↦ hB.le d x) hx,
    fun b hb ↦ le_of_forall_sub_smul_le hnorm fun ε hε ↦ ?_⟩
  -- The fixed point of a decision `ε * (1 - γ)`-greedy for `x` is above `x - ε • e`.
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  obtain ⟨d, hd⟩ := hB.exists_sub_smul_le x (ε * (1 - γ)) (mul_pos hε hγ')
  have hfix := ((hT d).contractingWith hnorm hγ).fixedPoint_isFixedPt
  refine le_trans ?_ (hb (mem_iUnion.2 ⟨d, hfix⟩))
  have := (hT d).sub_smul_le_of_sub_smul_le_map hnorm hγ hfix (mul_pos hε hγ').le
    (hx.eq ▸ hd)
  rwa [mul_div_cancel_right₀ _ hγ'.ne'] at this

/-- **Optimality of greedy decisions**: if `T d x ≤ B x` for every decision `d`, the fixed point
`x` of `B` is the greatest fixed point of the maps `T d` as soon as some decision `d` is greedy for
it, and it is then the fixed point of `T d` (`isFixedPt_of_map_eq`). -/
theorem isGreatest_iUnion_fixedPoints [ClosedIicTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ d, T d x ≤ B x) (hx : IsFixedPt B x) {d : D} (hd : T d x = B x) :
    IsGreatest (⋃ d, fixedPoints (T d)) x :=
  ⟨mem_iUnion.2 ⟨d, isFixedPt_of_map_eq hx hd⟩,
    mem_upperBounds_iUnion_fixedPoints hnorm hT hγ hB hx⟩

/-- **Policy improvement**: if `x ≤ B x` and the decision `d` is greedy for `x`, then the fixed
point of `T d` is above `B x`. -/
theorem map_le_of_le_map [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hx : x ≤ B x) {d : D} (hd : T d x = B x)
    {y : E} (hy : IsFixedPt (T d) y) : B x ≤ y :=
  (hT d).le_of_le_map hnorm hγ hy (hd.symm.le.trans ((hT d).monotone hx))

/-! ### Convergence of policy iteration -/

namespace IsPolicyIteration

variable {d : ℕ → D} {v : ℕ → E}

/-- **Policy improvement**: each value of policy iteration is above the image by `B` of the
previous one. -/
theorem map_le [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hB : ∀ d x, T d x ≤ B x)
    (h : IsPolicyIteration T B d v) (k : ℕ) : B (v k) ≤ v (k + 1) :=
  map_le_of_le_map hnorm hT hγ (h.le_map hB k) (h.map_eq k) (h.isFixedPt (k + 1))

/-- The values of policy iteration are nondecreasing. -/
theorem monotone [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hB : ∀ d x, T d x ≤ B x)
    (h : IsPolicyIteration T B d v) : Monotone v :=
  monotone_nat_of_le_succ fun k ↦ (h.le_map hB k).trans (h.map_le hnorm hT hγ hB k)

/-- The values of policy iteration are above the iterates of a monotone `B`:
`B^[k] (v 0) ≤ v k`. -/
theorem iterate_le [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hB : ∀ d x, T d x ≤ B x)
    (hBm : Monotone B) (h : IsPolicyIteration T B d v) (k : ℕ) : B^[k] (v 0) ≤ v k :=
  hBm.iterate_le_of_map_le_succ (h.map_le hnorm hT hγ hB) k

/-- The values of policy iteration are below the fixed point `x` of `B`, when `T d x ≤ B x` for
every decision `d`. -/
theorem le_of_isFixedPt [ClosedIicTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1) (hB : ∀ d, T d x ≤ B x)
    (h : IsPolicyIteration T B d v) (hx : IsFixedPt B x) (k : ℕ) : v k ≤ x :=
  mem_upperBounds_iUnion_fixedPoints hnorm hT hγ hB hx (mem_iUnion.2 ⟨d k, h.isFixedPt k⟩)

/-- **Convergence of policy iteration**: `‖v k - x‖ ≤ γ ^ k * ‖v 0 - x‖`, where `x` is the fixed
point of `B`. -/
theorem norm_sub_le [ClosedIicTopology E] [ClosedIciTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ d x, T d x ≤ B x) (hBb : IsBlackwell e γ B) (h : IsPolicyIteration T B d v)
    (hx : IsFixedPt B x) (k : ℕ) : ‖v k - x‖ ≤ γ ^ k * ‖v 0 - x‖ :=
  hBb.norm_sub_le_of_map_le_succ hnorm hx (h.le_of_isFixedPt hnorm hT hγ (fun d ↦ hB d x) hx)
    (h.map_le hnorm hT hγ hB) k

/-- **Finite termination of policy iteration**: with finitely many decisions, policy iteration
reaches the fixed point of `B` after at most `Nat.card D` improvements. -/
theorem exists_le_card_eq [Finite D] [ClosedIciTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ d x, T d x ≤ B x) (hBb : IsBlackwell e γ B) (h : IsPolicyIteration T B d v)
    (hx : IsFixedPt B x) : ∃ k ≤ Nat.card D, v k = x := by
  have hBc := hBb.contractingWith hnorm hγ
  have hmono := h.monotone hnorm hT hγ hB
  by_contra! hne
  -- Before reaching `x`, the values increase strictly, since a repeated value is a fixed point of
  -- `B`. So `d 0, …, d (Nat.card D)` are distinct, which is impossible.
  have hlt i j (hij : i < j) (hj : j ≤ Nat.card D) : v i < v j := by
    refine lt_of_lt_of_le (lt_of_le_of_ne (hmono i.le_succ) fun heq ↦ hne i (by omega) ?_)
      (hmono hij)
    exact hBc.fixedPoint_unique'
      (le_antisymm ((h.map_le hnorm hT hγ hB i).trans heq.ge) (h.le_map hB i)) hx
  have := Fintype.ofFinite D
  obtain ⟨i, j, hij, hd⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card D + 1) ↦ d i) (by rw [Fintype.card_fin, Nat.card_eq_fintype_card]; omega)
  have hv : v i = v j := ((hT (d i)).contractingWith hnorm hγ).fixedPoint_unique' (h.isFixedPt i)
    (by rw [hd]; exact h.isFixedPt j)
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hij' | hij'
  · exact (hlt i j hij' (by omega)).ne hv
  · exact (hlt j i hij' (by omega)).ne hv.symm

end IsPolicyIteration

/-! ### Convergence of modified policy iteration -/

namespace IsModifiedPolicyIteration

variable {m : ℕ → ℕ} {d : ℕ → D} {u : ℕ → E}

/-- The values of modified policy iteration started below their image by `B` are below the fixed
point of `B`, when `B` satisfies Blackwell's conditions with modulus `γ < 1`. -/
theorem le_of_isFixedPt [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, Monotone (T d)) (hγ : γ < 1) (hB : ∀ d x, T d x ≤ B x) (hBb : IsBlackwell e γ B)
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (hx : IsFixedPt B x)
    (k : ℕ) : u k ≤ x :=
  hBb.le_of_le_map hnorm hγ hx (h.le_map hT hB h₀ k)

/-- **Convergence of modified policy iteration**: started from `u 0 ≤ B (u 0)`, the values of
modified policy iteration satisfy `‖u k - x‖ ≤ γ ^ k * ‖u 0 - x‖`, where `x` is the fixed point of
`B`. -/
theorem norm_sub_le [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, Monotone (T d)) (hγ : γ < 1) (hB : ∀ d x, T d x ≤ B x) (hBb : IsBlackwell e γ B)
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (hx : IsFixedPt B x)
    (k : ℕ) : ‖u k - x‖ ≤ γ ^ k * ‖u 0 - x‖ :=
  hBb.norm_sub_le_of_map_le_succ hnorm hx (h.le_of_isFixedPt hnorm hT hγ hB hBb h₀ hx)
    (h.map_le hT hB h₀) k

end IsModifiedPolicyIteration

end Normed

end LMLExplore
