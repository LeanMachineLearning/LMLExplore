/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Log

/-!
# The tree of the hard instances of episodic MDPs

The hard instances of the minimax lower bounds for episodic MDPs [DMKV21, Theorems 7 and 9]
place, besides three special states, the remaining `n` states on an `A`-ary tree: from the root,
an agent walks down the tree by choosing one of the `A` actions at each internal node, and the
leaves lead to the special states. This file develops the combinatorics of that tree, on natural
numbers.

The nodes are `0, …, n - 1`, numbered in the breadth-first order of the infinite `A`-ary tree:
the parent of the node `j + 1` is `j / A`, so that the children of the node `j` are the nodes
`A * j + k + 1` for `k < A`. The first `∑_{i < D} A ^ i` nodes are those of depth less than `D`.

* `depth A j`, the depth of the node `j`, increases by one from a node to each of its children
  (`depth_mul_add_add_one`), and is characterized by
  `∑_{i < D} A ^ i ≤ j ↔ D ≤ depth A j` (`sum_pow_le_iff_le_depth`).
* `height A n = ⌈log_A ((A - 1) n + 1)⌉`, the number of levels of the tree with `n` nodes, is
  characterized by `height A n ≤ D ↔ n ≤ ∑_{i < D} A ^ i` (`height_le_iff`). Every node has depth
  less than `height A n` (`depth_lt_height`), and the full tree of depth `d`, with
  `n = ∑_{i < d} A ^ i = (A ^ d - 1) / (A - 1)` nodes, has height `d` (`height_sum_pow`).
* `child A n j k` is the node reached from `j` by the action `k < A`: the child `A * j + k + 1`
  when it is a node of the tree, and the first child `A * j + 1` otherwise, so that in a tree that
  is not full every action leads somewhere (`child_lt`, `depth_child`).
* `leaves A n`, the nodes without children, make up at least half of the tree
  (`le_two_mul_card_leaves`).
* `walk A n acts m` is the node reached from the root by the actions `acts 0, …, acts (m - 1)`;
  every node `j` is reached by a walk of `depth A j` steps through internal nodes
  (`exists_walk`).

This development is adapted from the formalization `Essakine2026Tight`
(`github.com/RemyDegenne/Essakine2026Tight`, file `Essakine2026Tight/EV2026/HardTree.lean`, by
Rémy Degenne, Apache 2.0) of [EV26], whose lower bound uses these trees for every number of
states `S ≥ 6` and not only for full trees.

## References

* [DMKV21] O. D. Domingues, P. Ménard, E. Kaufmann and M. Valko, *Episodic reinforcement learning
  in finite MDPs: minimax lower bounds revisited*, ALT 2021, arXiv:2010.03531.
* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open Finset

namespace LMLExplore.ReinforcementLearning.HardTree

variable {A n j k D : ℕ}

/-! ### Depths -/

/-- The depth of the node `j` of the breadth-first `A`-ary tree, in which the parent of the node
`j + 1` is `j / A`. -/
def depth (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => depth A (j / A) + 1
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self j A)

@[simp]
lemma depth_zero (A : ℕ) : depth A 0 = 0 := by
  rw [depth]

lemma depth_add_one (A j : ℕ) : depth A (j + 1) = depth A (j / A) + 1 := by
  rw [depth]

/-- The child `A * j + k + 1` of the node `j`, for `k < A`, has depth one more than `j`. -/
lemma depth_mul_add_add_one (j : ℕ) (hk : k < A) : depth A (A * j + k + 1) = depth A j + 1 := by
  rw [depth_add_one, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hk, add_zero]

/-- The nodes of depth at least `D` are numbered at least `∑_{i < D} A ^ i`. -/
lemma sum_pow_le_of_le_depth (h : D ≤ depth A j) : ∑ i ∈ range D, A ^ i ≤ j := by
  induction D generalizing j with
  | zero => simp
  | succ D ih =>
    obtain _ | j := j
    · simp at h
    rw [depth_add_one] at h
    have := Nat.mul_le_mul_left A (ih (j := j / A) (by omega))
    have := Nat.mul_div_le j A
    rw [geom_sum_succ]
    omega

/-- The node `j` is numbered less than `∑_{i ≤ depth A j} A ^ i`. -/
lemma lt_sum_pow_depth_add_one (hA : 0 < A) (j : ℕ) :
    j < ∑ i ∈ range (depth A j + 1), A ^ i := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain _ | j := j
    · simp
    have h : j / A + 1 ≤ ∑ i ∈ range (depth A (j / A) + 1), A ^ i :=
      ih (j / A) (Nat.lt_succ_of_le (Nat.div_le_self j A))
    have := Nat.mul_le_mul_left A h
    have : j < A * (j / A + 1) := Nat.lt_mul_div_succ j hA
    rw [depth_add_one, geom_sum_succ]
    omega

/-- The node `j` has depth at least `D` if and only if it is numbered at least
`∑_{i < D} A ^ i`: the nodes of depth less than `D` are the first `∑_{i < D} A ^ i` nodes. -/
theorem sum_pow_le_iff_le_depth (hA : 0 < A) : ∑ i ∈ range D, A ^ i ≤ j ↔ D ≤ depth A j := by
  refine ⟨fun h ↦ ?_, sum_pow_le_of_le_depth⟩
  by_contra! hD
  have := lt_sum_pow_depth_add_one hA j
  have : ∑ i ∈ range (depth A j + 1), A ^ i ≤ ∑ i ∈ range D, A ^ i :=
    sum_le_sum_of_subset (range_subset_range.2 hD)
  omega

/-! ### The height of a tree -/

/-- The number of levels `⌈log_A ((A - 1) n + 1)⌉` of the breadth-first `A`-ary tree with the
nodes `0, …, n - 1`: the least `D` with `n ≤ ∑_{i < D} A ^ i` (`height_le_iff`). -/
def height (A n : ℕ) : ℕ := Nat.clog A ((A - 1) * n + 1)

lemma height_def (A n : ℕ) : height A n = Nat.clog A ((A - 1) * n + 1) :=
  (rfl)

/-- The tree with `n` nodes has at most `D` levels if and only if the first `D` levels of the
infinite tree contain `n` nodes. -/
theorem height_le_iff (hA : 1 < A) : height A n ≤ D ↔ n ≤ ∑ i ∈ range D, A ^ i := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  rw [height_def, Nat.clog_le_iff_le_pow hA, ← geom_sum_mul_add, Nat.add_sub_cancel, mul_comm,
    add_le_add_iff_right, Nat.mul_le_mul_right_iff (by omega)]

lemma le_sum_pow_height (hA : 1 < A) (n : ℕ) : n ≤ ∑ i ∈ range (height A n), A ^ i :=
  (height_le_iff hA).1 le_rfl

lemma lt_height_iff (hA : 1 < A) : D < height A n ↔ ∑ i ∈ range D, A ^ i < n := by
  simpa only [not_le] using (height_le_iff hA).not

/-- The full tree of depth `d`, with `∑_{i < d} A ^ i = (A ^ d - 1) / (A - 1)` nodes, has `d`
levels. -/
theorem height_sum_pow (hA : 1 < A) (d : ℕ) : height A (∑ i ∈ range d, A ^ i) = d := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  rw [height_def, Nat.add_sub_cancel, mul_comm, geom_sum_mul_add, Nat.clog_pow _ _ hA]

/-- A tree with at least two nodes has at least two levels. -/
lemma two_le_height (hA : 1 < A) (hn : 2 ≤ n) : 2 ≤ height A n :=
  (lt_height_iff (D := 1) hA).2 (by simp; omega)

/-- Every node of the tree with `n` nodes has depth less than its height. -/
theorem depth_lt_height (hA : 1 < A) (hj : j < n) : depth A j < height A n := by
  by_contra! h
  have := sum_pow_le_of_le_depth h
  have := le_sum_pow_height hA n
  omega

/-! ### Children and leaves -/

/-- The node reached from the node `j` of the tree with `n` nodes by the action `k`: its child
`A * j + k + 1` if it is a node of the tree, and its first child `A * j + 1` otherwise. -/
def child (A n j k : ℕ) : ℕ := if A * j + k + 1 < n then A * j + k + 1 else A * j + 1

lemma child_of_lt (h : A * j + k + 1 < n) : child A n j k = A * j + k + 1 := by
  simp [child, h]

lemma child_of_not_lt (h : ¬ A * j + k + 1 < n) : child A n j k = A * j + 1 := by
  simp [child, h]

/-- From an internal node `j`, every action leads to a node of the tree. -/
lemma child_lt (hj : A * j + 1 < n) : child A n j k < n := by
  unfold child
  split_ifs <;> omega

lemma depth_child (hk : k < A) : depth A (child A n j k) = depth A j + 1 := by
  unfold child
  split_ifs
  · exact depth_mul_add_add_one j hk
  · exact depth_mul_add_add_one j (k := 0) (by omega)

/-- The leaves of the tree with the nodes `0, …, n - 1`: the nodes without children. -/
def leaves (A n : ℕ) : Finset ℕ := (range n).filter fun j ↦ n ≤ A * j + 1

@[simp]
lemma mem_leaves : j ∈ leaves A n ↔ j < n ∧ n ≤ A * j + 1 := by
  simp [leaves]

/-- At least half of the nodes of a tree of arity at least `2` are leaves. -/
theorem le_two_mul_card_leaves (hA : 2 ≤ A) (n : ℕ) : n ≤ 2 * #(leaves A n) := by
  have hsub : Ico (n / 2) n ⊆ leaves A n := by
    intro j hj
    rw [mem_Ico] at hj
    rw [mem_leaves]
    have : 2 * j ≤ A * j := Nat.mul_le_mul_right j hA
    omega
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

/-! ### Walks from the root -/

/-- The node of the tree with `n` nodes reached from the root by the actions
`acts 0, …, acts (m - 1)`. -/
def walk (A n : ℕ) (acts : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => child A n (walk A n acts m) (acts m)

@[simp]
lemma walk_zero (acts : ℕ → ℕ) : walk A n acts 0 = 0 :=
  (rfl)

@[simp]
lemma walk_add_one (acts : ℕ → ℕ) (m : ℕ) :
    walk A n acts (m + 1) = child A n (walk A n acts m) (acts m) :=
  (rfl)

/-- A walk by actions in `{0, …, A - 1}` reaches a node of depth `m` after `m` steps. -/
lemma depth_walk {acts : ℕ → ℕ} (hacts : ∀ m, acts m < A) (m : ℕ) :
    depth A (walk A n acts m) = m := by
  induction m with
  | zero => simp
  | succ m ih => rw [walk_add_one, depth_child (hacts m), ih]

/-- The first `D` steps of a walk do not depend on its action at the step `D`. -/
lemma walk_update_of_le {acts : ℕ → ℕ} {m : ℕ} (x : ℕ) (hm : m ≤ D) :
    walk A n (Function.update acts D x) m = walk A n acts m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [walk_add_one, walk_add_one, ih (by omega), Function.update_of_ne (by omega)]

/-- Every node `j` of the tree with `n` nodes is reached from the root by a walk of `depth A j`
steps through internal nodes. -/
theorem exists_walk (hA : 0 < A) (hj : j < n) :
    ∃ acts : ℕ → ℕ, (∀ m, acts m < A) ∧ walk A n acts (depth A j) = j ∧
      ∀ m < depth A j, A * walk A n acts m + 1 < n := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain _ | j := j
    · exact ⟨fun _ ↦ 0, fun _ ↦ hA, by simp, by simp⟩
    -- extend the walk to the parent `j / A` by the action `j % A`
    have hdiv : j / A ≤ j := Nat.div_le_self j A
    obtain ⟨acts, hacts, hwalk, hint⟩ := ih (j / A) (by omega) (by omega)
    have hj' : A * (j / A) + j % A + 1 = j + 1 := by
      have := Nat.div_add_mod j A
      omega
    refine ⟨Function.update acts (depth A (j / A)) (j % A), fun m ↦ ?_, ?_, fun m hm ↦ ?_⟩
    · rcases eq_or_ne m (depth A (j / A)) with rfl | h
      · rw [Function.update_self]
        exact Nat.mod_lt _ hA
      · rw [Function.update_of_ne h]
        exact hacts m
    · rw [depth_add_one, walk_add_one, walk_update_of_le _ le_rfl, hwalk, Function.update_self,
        child_of_lt (by omega), hj']
    · rw [depth_add_one] at hm
      rcases Nat.lt_or_ge m (depth A (j / A)) with h | h
      · rw [walk_update_of_le _ h.le]
        exact hint m h
      · rw [show m = depth A (j / A) by omega, walk_update_of_le _ le_rfl, hwalk]
        have := Nat.mul_div_le j A
        omega

end LMLExplore.ReinforcementLearning.HardTree
