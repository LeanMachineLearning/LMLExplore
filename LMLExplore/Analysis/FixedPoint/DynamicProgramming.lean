/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import LMLExplore.Order.Bounds.Basic
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
maximum, attained at every point: `B x` is the greatest element of `{T d x | d : D}`. A decision
`d` with `T d x = B x` is *greedy* for `x`.

For a Markov decision process, `E` is a space of bounded value functions, `T d` is the evaluation
operator `v ↦ r_d + γ P_d v` of a deterministic stationary policy `d` and `B` is the Bellman
optimality operator, whose value at `v` is attained by the policy choosing at every state an action
maximizing `r(s, a) + γ ∫ v dP(s, a)`. The results of this file then say that the optimal value is
the value of a greedy policy, and that policy iteration and modified policy iteration (with value
iteration as the case of a single evaluation step) converge geometrically to it, the latter when
started from `x 0 ≤ B (x 0)`. They only use monotonicity and Blackwell's conditions (`IsBlackwell`),
following Bertsekas's abstract dynamic programming. The fixed point of `B` is taken as a
hypothesis, so completeness of `E` is not assumed.

## Main definitions

* `LMLExplore.IsPolicyIteration T B d v`: `v k` is the fixed point of `T (d k)` and `d (k + 1)` is
  greedy for `v k`.
* `LMLExplore.IsModifiedPolicyIteration T B m d x`: `d k` is greedy for `x k` and
  `x (k + 1) = (T (d k))^[m k + 1] (x k)`.

## Main statements

* `LMLExplore.IsBlackwell.contractingWith`: a map satisfying Blackwell's conditions with modulus
  `γ < 1` is a `γ`-contraction, and `LMLExplore.IsBlackwell.of_isGreatest_range` says that `B`
  satisfies them.
* `LMLExplore.IsBlackwell.le_of_map_le`, `LMLExplore.IsBlackwell.le_of_le_map`: if `T x ≤ x` then
  the fixed point of `T` is below `x`, and if `x ≤ T x` it is above.
* `LMLExplore.isGreatest_iUnion_fixedPoints`: the fixed point of `B` is the greatest fixed point of
  the maps `T d`; `LMLExplore.isFixedPt_of_map_eq`: it is the fixed point of every decision greedy
  for it.
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

## References

* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
* [D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd edition, 2022][Ber22], Chapter 2
* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.4–6.5
-/

public section

open Set Function Filter Topology NNReal

namespace LMLExplore

variable {E D : Type*}

/-! ### Blackwell's conditions -/

section Blackwell

variable [AddCommGroup E] [PartialOrder E] [Module ℝ E] {e : E} {γ : ℝ≥0}

/-- The maximum of maps satisfying Blackwell's conditions with modulus `γ` satisfies them, when it
is attained: `B x` is the greatest of the values `T d x`. -/
lemma IsBlackwell.of_isGreatest_range [IsOrderedAddMonoid E] {T : D → E → E} {B : E → E}
    (hT : ∀ d, IsBlackwell e γ (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) :
    IsBlackwell e γ B where
  monotone := Monotone.of_isGreatest_range (fun d ↦ (hT d).monotone) hB
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

/-- A fixed point of a map `T d` is below its image by the maximum `B` of the maps `T d`. -/
lemma le_map_of_isFixedPt (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) {d : D}
    (hx : IsFixedPt (T d) x) : x ≤ B x :=
  hx.symm.le.trans ((hB x).2 ⟨d, rfl⟩)

/-- Each value of policy iteration is below its image by `B`. -/
lemma IsPolicyIteration.le_map (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) {d : ℕ → D}
    {v : ℕ → E} (h : IsPolicyIteration T B d v) (k : ℕ) : v k ≤ B (v k) :=
  le_map_of_isFixedPt hB (h.isFixedPt k)

namespace IsModifiedPolicyIteration

variable {m : ℕ → ℕ} {d : ℕ → D} {u : ℕ → E}

/-- Modified policy iteration started below its image by `B` stays below its image by `B`. -/
theorem le_map (hT : ∀ d, Monotone (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x))
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) : u k ≤ B (u k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    -- With `f = T (d k)`, `u k ≤ f (u k)`, so the iterates of `f` at `u k` are nondecreasing.
    have hmono := (hT (d k)).monotone_iterate_of_le_map (ih.trans_eq (h.map_eq k).symm)
    calc u (k + 1) = (T (d k))^[m k + 1] (u k) := h.eq_iterate k
      _ ≤ (T (d k))^[m k + 1 + 1] (u k) := hmono (Nat.le_succ _)
      _ = T (d k) (u (k + 1)) := by rw [iterate_succ_apply', h.eq_iterate k]
      _ ≤ B (u (k + 1)) := (hB _).2 ⟨d k, rfl⟩

/-- Each value of modified policy iteration started below its image by `B` is above the image by
`B` of the previous one. -/
theorem map_le (hT : ∀ d, Monotone (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x))
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) :
    B (u k) ≤ u (k + 1) := by
  have hmono :=
    (hT (d k)).monotone_iterate_of_le_map ((h.le_map hT hB h₀ k).trans_eq (h.map_eq k).symm)
  calc B (u k) = (T (d k))^[1] (u k) := by rw [iterate_one, h.map_eq k]
    _ ≤ (T (d k))^[m k + 1] (u k) := hmono (Nat.le_add_left 1 (m k))
    _ = u (k + 1) := (h.eq_iterate k).symm

/-- The values of modified policy iteration started below their image by `B` are above the
iterates of `B`: `B^[k] (u 0) ≤ u k`. -/
theorem iterate_le (hT : ∀ d, Monotone (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x))
    (h : IsModifiedPolicyIteration T B m d u) (h₀ : u 0 ≤ B (u 0)) (k : ℕ) : B^[k] (u 0) ≤ u k :=
  (Monotone.of_isGreatest_range hT hB).iterate_le_of_map_le_succ (h.map_le hT hB h₀) k

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

end IsBlackwell

/-! ### Optimality of greedy decisions -/

variable {T : D → E → E} {B : E → E} {x : E}

/-- **Optimality of greedy decisions**: the fixed point of the maximum `B` of maps `T d` satisfying
Blackwell's conditions with modulus `γ < 1` is the greatest fixed point of the maps `T d`. It is
attained by every decision greedy for it (`isFixedPt_of_map_eq`). -/
theorem isGreatest_iUnion_fixedPoints [ClosedIicTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (hx : IsFixedPt B x) :
    IsGreatest (⋃ d, fixedPoints (T d)) x := by
  obtain ⟨d, hd⟩ := (hB x).1
  refine ⟨mem_iUnion.2 ⟨d, isFixedPt_of_map_eq hx hd⟩, fun y hy ↦ ?_⟩
  obtain ⟨d', hy⟩ := mem_iUnion.1 hy
  exact (hT d').le_of_map_le hnorm hγ hy (((hB x).2 ⟨d', rfl⟩).trans_eq hx)

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
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v) (k : ℕ) :
    B (v k) ≤ v (k + 1) :=
  map_le_of_le_map hnorm hT hγ (h.le_map hB k) (h.map_eq k) (h.isFixedPt (k + 1))

/-- The values of policy iteration are nondecreasing. -/
theorem monotone [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v) :
    Monotone v :=
  monotone_nat_of_le_succ fun k ↦ (h.le_map hB k).trans (h.map_le hnorm hT hγ hB k)

/-- The values of policy iteration are above the iterates of `B`: `B^[k] (v 0) ≤ v k`. -/
theorem iterate_le [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v) (k : ℕ) :
    B^[k] (v 0) ≤ v k :=
  (IsBlackwell.of_isGreatest_range hT hB).monotone.iterate_le_of_map_le_succ
    (h.map_le hnorm hT hγ hB) k

/-- The values of policy iteration are below the fixed point of `B`. -/
theorem le_of_isFixedPt [ClosedIicTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v)
    (hx : IsFixedPt B x) (k : ℕ) : v k ≤ x :=
  (isGreatest_iUnion_fixedPoints hnorm hT hγ hB hx).2 (mem_iUnion.2 ⟨d k, h.isFixedPt k⟩)

/-- **Convergence of policy iteration**: `‖v k - x‖ ≤ γ ^ k * ‖v 0 - x‖`, where `x` is the fixed
point of `B`. -/
theorem norm_sub_le [ClosedIicTopology E] [ClosedIciTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v)
    (hx : IsFixedPt B x) (k : ℕ) : ‖v k - x‖ ≤ γ ^ k * ‖v 0 - x‖ :=
  (IsBlackwell.of_isGreatest_range hT hB).norm_sub_le_of_map_le_succ hnorm hx
    (h.le_of_isFixedPt hnorm hT hγ hB hx) (h.map_le hnorm hT hγ hB) k

/-- **Finite termination of policy iteration**: with finitely many decisions, policy iteration
reaches the fixed point of `B` after at most `Nat.card D` improvements. -/
theorem exists_le_card_eq [Finite D] [ClosedIciTopology E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsPolicyIteration T B d v)
    (hx : IsFixedPt B x) : ∃ k ≤ Nat.card D, v k = x := by
  have hBc := (IsBlackwell.of_isGreatest_range hT hB).contractingWith hnorm hγ
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
point of `B`. -/
theorem le_of_isFixedPt [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsModifiedPolicyIteration T B m d u)
    (h₀ : u 0 ≤ B (u 0)) (hx : IsFixedPt B x) (k : ℕ) : u k ≤ x :=
  (IsBlackwell.of_isGreatest_range hT hB).le_of_le_map hnorm hγ hx
    (h.le_map (fun d ↦ (hT d).monotone) hB h₀ k)

/-- **Convergence of modified policy iteration**: started from `u 0 ≤ B (u 0)`, the values of
modified policy iteration satisfy `‖u k - x‖ ≤ γ ^ k * ‖u 0 - x‖`, where `x` is the fixed point of
`B`. -/
theorem norm_sub_le [ClosedIciTopology E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : ∀ d, IsBlackwell e γ (T d)) (hγ : γ < 1)
    (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) (h : IsModifiedPolicyIteration T B m d u)
    (h₀ : u 0 ≤ B (u 0)) (hx : IsFixedPt B x) (k : ℕ) : ‖u k - x‖ ≤ γ ^ k * ‖u 0 - x‖ :=
  (IsBlackwell.of_isGreatest_range hT hB).norm_sub_le_of_map_le_succ hnorm hx
    (h.le_of_isFixedPt hnorm hT hγ hB h₀ hx) (h.map_le (fun d ↦ (hT d).monotone) hB h₀) k

end IsModifiedPolicyIteration

end Normed

end LMLExplore
