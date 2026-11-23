/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Basic
public import LMLExplore.Data.Nat.Nth

/-!
# Operations on online learners

The reductions of online learning [Ora, Chapters 12–14] build learners from other learners: they
restart copies of a learner, run learners coordinatewise, add the plays of several learners,
transform the plays of a learner, feed a learner surrogate losses computed from its own plays,
and hide from a learner the rounds without feedback. This file
defines these operations on `OnlineLearner`, computes their runs, and transfers regret guarantees
(`OnlineLearner.HasRegretBound`) through them.

* `A.restart s` plays from round `s` on as a fresh copy of `A` started at round `s`: its play of
  round `s + t` is the play of round `t` of `A` against the contexts and feedback shifted by `s`
  (`run_restart_add`). Its regret on the interval of rounds `[s, s + τ)` is therefore the regret
  after `τ` rounds of `A` on the shifted feedback (`intervalRegret_run_restart`), and a regret
  guarantee of `A` bounds the interval regrets of its restarts
  (`HasRegretBound.intervalRegret_run_restart_le`). This is how the strongly adaptive algorithms
  of [Ora, Chapter 14] use black-box learners.
* `OnlineLearner.pi A`, for a family of learners `A i` sharing the contexts, plays the family of
  their plays and feeds the coordinate `g i` of the feedback to `A i` (`run_pi`). For losses that
  are sums of losses of the coordinates, such as linear losses on `ι → ℝ`, its regret is the sum of
  the regrets of the coordinates (`regret_run_pi`, `HasRegretBound.pi`): this is how AdaGrad
  [Ora, Section 4.2.4] and coordinatewise coin betting [Ora, Section 13.3] are built from
  one-dimensional learners.
* `OnlineLearner.sum A`, for a finite family of learners receiving the same feedback, plays the sum
  of their plays (`run_sum`). For linear losses, its regret against `∑ i, v i` is the sum of the
  regrets of the learners `A i` against `v i` (`regret_run_sum`, `regret_run_sum_le`)
  [Ora, Theorem 13.11].
* `A.map f` plays the images by `f` of the plays of `A` (`run_map`). For a translation
  `f = (x₀ + ·)` and linear losses, the regret against `u` is the regret of `A` against `u - x₀`
  (`regret_run_map_add_left`, `HasRegretBound.map_add_left`) [Ora, Proposition 13.10].
* `A.withContext` plays the context of each round together with the play of `A`
  (`run_withContext`). Its closed-loop runs are those of `A` with feedback functions that read the
  contexts (`closedLoopFeedback_withContext`), so `A.withContext.reduce f φ` is a reduction whose
  output map and surrogate feedback depend on the context of the round, as in the sleeping-experts
  reduction of [Ora, Section 12.2].
* `A.reduce f φ`, the **black-box reduction** to `A` with the output map `f` and the surrogate
  feedback `φ`, plays `f (z t)` when `A` plays `z t`, and feeds `A` the surrogate `φ (z t) (g t)`
  of its own feedback `g t` (`play_reduce`). The plays of `A` are those of its closed-loop run
  (`run_reduce`), so a per-round comparison of the losses of `f z` and of the surrogate losses of
  `z` transfers the regret guarantees of `A` to the reduction (`regret_run_reduce_le`,
  `HasRegretBound.reduce`). The constrained learners of [Ora, Section 12.1] are of this form.
* `A.skipZero`, for feedback in a type with a zero, plays as `A` run on the rounds of nonzero
  feedback only: its play of round `t` is the play of `A` from the `count (g · ≠ 0) t` rounds of
  nonzero feedback before `t`, the `i`-th of which is `nth (g · ≠ 0) i` (`run_skipZero`). For
  losses that vanish for the zero feedback, its regret is the regret of `A` on this subsequence of
  rounds (`regret_run_skipZero`), so a regret guarantee of `A` in the horizon becomes one in the
  number of rounds of nonzero feedback (`HasRegretBound.skipZero`) [Ora, Section 13.2.1].

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.restart A s`: `A` restarted at round `s`.
* `LMLExplore.OnlineLearning.OnlineLearner.pi A`: the coordinatewise product of a family of
  learners.
* `LMLExplore.OnlineLearning.OnlineLearner.sum A`: the sum of the plays of a finite family of
  learners.
* `LMLExplore.OnlineLearning.OnlineLearner.map A f`: the images by `f` of the plays of `A`.
* `LMLExplore.OnlineLearning.OnlineLearner.withContext A`: the plays of `A` paired with the
  contexts.
* `LMLExplore.OnlineLearning.OnlineLearner.reduce A f φ`: the black-box reduction to `A` with the
  output map `f` and the surrogate feedback `φ`.
* `LMLExplore.OnlineLearning.OnlineLearner.skipZero A`: `A` skipping the rounds with zero
  feedback.

## Main statements

* `OnlineLearner.intervalRegret_run_restart`: the regret of a learner restarted at round `s` on the
  rounds `[s, s + τ)` is the regret after `τ` rounds of the learner on the shifted feedback.
* `OnlineLearner.HasRegretBound.pi`: the regret guarantee of a coordinatewise product.
* `OnlineLearner.regret_run_sum_le`: the regret of a sum of learners is at most the sum of their
  regret bounds, for every decomposition of the comparator.
* `OnlineLearner.HasRegretBound.map_add_left`: the regret guarantee of a translated learner.
* `OnlineLearner.HasRegretBound.reduce`: the regret guarantee of a reduction.
* `OnlineLearner.HasRegretBound.skipZero`: the regret guarantee of a learner skipping the rounds
  with zero feedback.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

namespace OnlineLearner

variable {C G X Y : Type*}

section Restart

variable (A : OnlineLearner C G X)

/-- Plays of equal rounds from histories with equal entries are equal. -/
private lemma play_congr {t t' : ℕ} (ht : t = t') {h : Fin t → C × G} {h' : Fin t' → C × G}
    (hh : ∀ (i : ℕ) (hi : i < t), h ⟨i, hi⟩ = h' ⟨i, ht ▸ hi⟩) (c : C) :
    A.play t h c = A.play t' h' c := by
  subst ht
  congr
  exact funext fun i ↦ hh i i.isLt

/-- The learner `A` **restarted at round `s`**: from round `s` on, it plays as a fresh copy of `A`
started at round `s`, from the contexts and feedback of the rounds `s, s + 1, …` only; before
round `s`, it plays as `A` at its first round, from the current context. -/
def restart (s : ℕ) : OnlineLearner C G X where
  play t h c :=
    if hst : s ≤ t then A.play (t - s) (fun i ↦ h ⟨s + i, by omega⟩) c else A.play 0 Fin.elim0 c

/-- From round `s` on, the play of `A` restarted at round `s` is the play of `A` from the history
of the rounds `s, s + 1, …`. -/
@[simp]
lemma play_restart_of_le {s t : ℕ} (hst : s ≤ t) (h : Fin t → C × G) (c : C) :
    (A.restart s).play t h c = A.play (t - s) (fun i ↦ h ⟨s + i, by omega⟩) c := by
  simp [restart, hst]

/-- Before round `s`, the play of `A` restarted at round `s` is the first play of `A` from the
current context. -/
@[simp]
lemma play_restart_of_lt {s t : ℕ} (hts : t < s) (h : Fin t → C × G) (c : C) :
    (A.restart s).play t h c = A.play 0 Fin.elim0 c := by
  simp [restart, Nat.not_le.mpr hts]

/-- From round `s` on, the plays of `A` restarted at round `s` are the plays of `A` against the
contexts and feedback shifted by `s`. -/
lemma run_restart_add (s : ℕ) (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    (A.restart s).run c g (s + t) = A.run (fun r ↦ c (s + r)) (fun r ↦ g (s + r)) t := by
  rw [run_def, run_def, A.play_restart_of_le (Nat.le_add_right s t)]
  exact A.play_congr (Nat.add_sub_cancel_left ..) (fun _ _ ↦ rfl) _

/-- Before round `s`, the plays of `A` restarted at round `s` are the first play of `A` from the
current context. -/
lemma run_restart_of_lt {s t : ℕ} (hts : t < s) (c : ℕ → C) (g : ℕ → G) :
    (A.restart s).run c g t = A.play 0 Fin.elim0 (c t) := by
  rw [run_def, A.play_restart_of_lt hts]

/-- A learner restarted at round `0` is the learner itself. -/
@[simp]
lemma restart_zero : A.restart 0 = A := by
  ext t h c
  rw [A.play_restart_of_le (Nat.zero_le t)]
  exact A.play_congr (Nat.sub_zero t) (fun _ _ ↦ by simp) c

variable {L : G → X → ℝ} {c : ℕ → C} {g : ℕ → G}

/-- **Regret of a restarted learner.** The regret of `A` restarted at round `s` on the rounds
`[s, s + τ)` is the regret after `τ` rounds of `A` against the contexts and feedback shifted by
`s`. -/
lemma intervalRegret_run_restart (L : G → X → ℝ) (s : ℕ) (c : ℕ → C) (g : ℕ → G) (u : X)
    (τ : ℕ) :
    intervalRegret (fun t ↦ L (g t)) ((A.restart s).run c g) u s τ =
      regret (fun t ↦ L (g (s + t))) (A.run (fun t ↦ c (s + t)) (fun t ↦ g (s + t))) u τ := by
  rw [intervalRegret_eq_regret]
  simp only [run_restart_add]

variable {A} {adm : C → G → Prop} {U : Set X} {B : ℕ → (ℕ → C) → (ℕ → G) → X → ℝ}

/-- A regret guarantee of `A` bounds the regret of `A` restarted at round `s` on the rounds
`[s, s + τ)` by the bound of `τ` rounds on the shifted contexts and feedback. -/
lemma HasRegretBound.intervalRegret_run_restart_le (hA : A.HasRegretBound L adm U B) (s : ℕ)
    {τ : ℕ} (hg : ∀ t < τ, adm (c (s + t)) (g (s + t))) {u : X} (hu : u ∈ U) :
    intervalRegret (fun t ↦ L (g t)) ((A.restart s).run c g) u s τ ≤
      B τ (fun t ↦ c (s + t)) (fun t ↦ g (s + t)) u := by
  rw [intervalRegret_run_restart]
  exact hA.regret_le hg hu

end Restart

section Pi

variable {ι : Type*} {G X : ι → Type*}

/-- The **coordinatewise product** of a family of learners `A i` sharing the contexts: it plays the
family of the plays of the learners, and feeds the coordinate `g i` of each feedback to `A i`. -/
def pi (A : ∀ i, OnlineLearner C (G i) (X i)) : OnlineLearner C (∀ i, G i) (∀ i, X i) where
  play t h c i := (A i).play t (fun s ↦ ((h s).1, (h s).2 i)) c

variable (A : ∀ i, OnlineLearner C (G i) (X i))

/-- The play of the coordinatewise product is the family of the plays of the learners from the
coordinates of the history. -/
@[simp]
lemma play_pi (t : ℕ) (h : Fin t → C × ∀ i, G i) (c : C) (i : ι) :
    (pi A).play t h c i = (A i).play t (fun s ↦ ((h s).1, (h s).2 i)) c := (rfl)

/-- The plays of the coordinatewise product are the plays of the learners against the coordinates
of the feedback. -/
@[simp]
lemma run_pi (c : ℕ → C) (g : ℕ → ∀ i, G i) (t : ℕ) (i : ι) :
    (pi A).run c g t i = (A i).run c (fun s ↦ g s i) t := by
  rw [run_def, run_def]
  rfl

variable [Fintype ι]

/-- **Regret of a coordinatewise product.** For losses that are sums `∑ i, L i (g i) (x i)` of
losses of the coordinates, the regret of the coordinatewise product against `u` is the sum of the
regrets of the learners `A i` against `u i`. -/
lemma regret_run_pi (L : ∀ i, G i → X i → ℝ) (c : ℕ → C) (g : ℕ → ∀ i, G i) (u : ∀ i, X i)
    (n : ℕ) :
    regret (fun t x ↦ ∑ i, L i (g t i) (x i)) ((pi A).run c g) u n =
      ∑ i, regret (fun t ↦ L i (g t i)) ((A i).run c fun s ↦ g s i) (u i) n := by
  simp only [regret_def, run_pi, ← sum_sub_distrib]
  exact sum_comm

variable {A} {L : ∀ i, G i → X i → ℝ} {adm : ∀ i, C → G i → Prop} {U : ∀ i, Set (X i)}
  {B : ∀ i, ℕ → (ℕ → C) → (ℕ → G i) → X i → ℝ}

/-- **Regret guarantee of a coordinatewise product.** If each learner `A i` has the regret bound
`B i` for the losses `L i`, then their coordinatewise product has the regret bound
`∑ i, B i n c (fun t ↦ g t i) (u i)` for the losses `∑ i, L i (g i) (x i)`, the feedback whose
coordinates are admissible and the comparators in the product of the sets `U i`. -/
theorem HasRegretBound.pi (hA : ∀ i, (A i).HasRegretBound (L i) (adm i) (U i) (B i)) :
    (pi A).HasRegretBound (fun g x ↦ ∑ i, L i (g i) (x i)) (fun c g ↦ ∀ i, adm i c (g i))
      (Set.univ.pi U) (fun n c g u ↦ ∑ i, B i n c (fun t ↦ g t i) (u i)) := by
  refine hasRegretBound_iff.mpr fun c g n hg u hu ↦ ?_
  rw [regret_run_pi]
  exact sum_le_sum fun i _ ↦
    (hA i).regret_le (fun t ht ↦ hg t ht i) (Set.mem_univ_pi.mp hu i)

end Pi

section Sum

variable {ι : Type*} [Fintype ι] [AddCommMonoid X]

/-- The **sum** of a finite family of learners receiving the same contexts and feedback: it plays
the sum of their plays. -/
protected def sum (A : ι → OnlineLearner C G X) : OnlineLearner C G X where
  play t h c := ∑ i, (A i).play t h c

variable (A : ι → OnlineLearner C G X)

/-- The play of the sum of learners is the sum of their plays. -/
@[simp]
lemma play_sum (t : ℕ) (h : Fin t → C × G) (c : C) :
    (OnlineLearner.sum A).play t h c = ∑ i, (A i).play t h c := (rfl)

/-- The plays of the sum of learners are the sums of their plays. -/
@[simp]
lemma run_sum (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    (OnlineLearner.sum A).run c g t = ∑ i, (A i).run c g t := by
  simp only [run_def]
  rfl

variable {F : Type*} [FunLike F X ℝ] [AddMonoidHomClass F X ℝ] (A : ι → OnlineLearner C F X)

/-- **Regret of a sum of learners** [Ora, Theorem 13.11]. For linear losses, the regret of the sum
of learners against `∑ i, v i` is the sum of the regrets of the learners `A i` against `v i`. -/
lemma regret_run_sum (c : ℕ → C) (y : ℕ → F) (v : ι → X) (n : ℕ) :
    regret (fun t ↦ y t) ((OnlineLearner.sum A).run c y) (∑ i, v i) n =
      ∑ i, regret (fun t ↦ y t) ((A i).run c y) (v i) n := by
  simp only [regret_def, run_sum, map_sum, ← sum_sub_distrib]
  exact sum_comm

variable {A} {adm : C → F → Prop} {U : ι → Set X} {B : ι → ℕ → (ℕ → C) → (ℕ → F) → X → ℝ}

/-- **Regret guarantee of a sum of learners** [Ora, Theorem 13.11]. If each learner `A i` has the
regret bound `B i` for linear losses against the comparators in `U i`, then for every
decomposition `∑ i, v i` of the comparator with `v i ∈ U i`, the regret of the sum of the learners
against `∑ i, v i` is at most `∑ i, B i n c y (v i)`. [Ora] states an equality with the minimum
over the decompositions; the regret is at most this infimum. -/
theorem regret_run_sum_le (hA : ∀ i, (A i).HasRegretBound (fun y x ↦ y x) adm (U i) (B i))
    {c : ℕ → C} {y : ℕ → F} {n : ℕ} (hy : ∀ t < n, adm (c t) (y t)) {v : ι → X}
    (hv : ∀ i, v i ∈ U i) :
    regret (fun t ↦ y t) ((OnlineLearner.sum A).run c y) (∑ i, v i) n ≤
      ∑ i, B i n c y (v i) := by
  rw [regret_run_sum]
  exact sum_le_sum fun i _ ↦ (hA i).regret_le hy (hv i)

end Sum

section Map

variable (A : OnlineLearner C G X)

/-- The learner playing the images by `f` of the plays of `A`. -/
def map (f : X → Y) : OnlineLearner C G Y where
  play t h c := f (A.play t h c)

/-- The play of `A.map f` is the image by `f` of the play of `A`. -/
@[simp]
lemma play_map (f : X → Y) (t : ℕ) (h : Fin t → C × G) (c : C) :
    (A.map f).play t h c = f (A.play t h c) := (rfl)

/-- The plays of `A.map f` are the images by `f` of the plays of `A`. -/
@[simp]
lemma run_map (f : X → Y) (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    (A.map f).run c g t = f (A.run c g t) := by
  rw [run_def, run_def]
  rfl

@[simp]
lemma map_id : A.map id = A := (rfl)

@[simp]
lemma map_map {Z : Type*} (f : X → Y) (f' : Y → Z) : (A.map f).map f' = A.map (f' ∘ f) := (rfl)

/-- The regret of `A.map f` against `f v` is the regret of `A` against `v` for the losses composed
with `f`. -/
lemma regret_run_map (L : G → Y → ℝ) (f : X → Y) (c : ℕ → C) (g : ℕ → G) (v : X) (n : ℕ) :
    regret (fun t ↦ L (g t)) ((A.map f).run c g) (f v) n =
      regret (fun t x ↦ L (g t) (f x)) (A.run c g) v n := by
  simp [regret_def]

variable {X : Type*} [AddCommGroup X] {F : Type*} [FunLike F X ℝ] [AddMonoidHomClass F X ℝ]
  (A : OnlineLearner C F X)

/-- **Regret of a translated learner.** For linear losses, the regret of the learner playing
`x₀ + x t` against `u` is the regret of the learner playing `x t` against `u - x₀`. -/
lemma regret_run_map_add_left (x₀ : X) (c : ℕ → C) (y : ℕ → F) (u : X) (n : ℕ) :
    regret (fun t ↦ y t) ((A.map (x₀ + ·)).run c y) u n =
      regret (fun t ↦ y t) (A.run c y) (u - x₀) n := by
  simp only [regret_eq_sum_apply_sub, run_map]
  exact sum_congr rfl fun t _ ↦ by
    congr 1
    abel

variable {A} {adm : C → F → Prop} {U : Set X} {B : ℕ → (ℕ → C) → (ℕ → F) → X → ℝ}

/-- **Regret guarantee of a translated learner** [Ora, Proposition 13.10]. If `A` has the regret
bound `B` for linear losses against the comparators in `U`, then the learner playing `x₀ + x t`
has the regret bound `B n c y (u - x₀)` against the comparators `u` with `u - x₀ ∈ U`. -/
theorem HasRegretBound.map_add_left (hA : A.HasRegretBound (fun y x ↦ y x) adm U B) (x₀ : X) :
    (A.map (x₀ + ·)).HasRegretBound (fun y x ↦ y x) adm ((· - x₀) ⁻¹' U)
      (fun n c y u ↦ B n c y (u - x₀)) := by
  refine hasRegretBound_iff.mpr fun c y n hy u hu ↦ ?_
  rw [regret_run_map_add_left]
  exact hA.regret_le hy hu

end Map

section WithContext

variable (A : OnlineLearner C G X)

/-- The learner playing the context of each round together with the play of `A`. Reductions built
on `A.withContext` see the context of the round in their output map and surrogate feedback. -/
def withContext : OnlineLearner C G (C × X) where
  play t h c := (c, A.play t h c)

/-- The play of `A.withContext` is the context of the round paired with the play of `A`. -/
@[simp]
lemma play_withContext (t : ℕ) (h : Fin t → C × G) (c : C) :
    A.withContext.play t h c = (c, A.play t h c) := (rfl)

/-- The plays of `A.withContext` are the contexts paired with the plays of `A`. -/
@[simp]
lemma run_withContext (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    A.withContext.run c g t = (c t, A.run c g t) := by
  rw [run_def, run_def, play_withContext]

/-- The closed-loop feedback of `A.withContext` for the feedback functions `φ` is the closed-loop
feedback of `A` for the feedback functions `z ↦ φ t (c t, z)`. -/
@[simp]
lemma closedLoopFeedback_withContext (c : ℕ → C) (φ : ℕ → C × X → G) :
    A.withContext.closedLoopFeedback c φ = A.closedLoopFeedback c fun t z ↦ φ t (c t, z) := by
  refine A.closedLoopFeedback_unique fun t ↦ ?_
  rw [closedLoopFeedback_eq, run_withContext]

end WithContext

section Reduce

variable {G' : Type*} (A : OnlineLearner C G X)

/-- The play of round `t` of `A` inside `A.reduce f φ`, from the history `h` of the contexts and
outer feedback of the rounds `s < t` and the context `c` of round `t`: `A` receives at each round
`s < t` the feedback `φ z (h s).2`, for its own play `z` of round `s`. By recursion on `t`. -/
private def reducePlay (φ : X → G' → G) (t : ℕ) (h : Fin t → C × G') (c : C) : X :=
  A.play t (fun s ↦ ((h s).1, φ (reducePlay φ s (fun r ↦ h (Fin.castLE s.isLt.le r)) (h s).1)
    (h s).2)) c
termination_by t
decreasing_by exact s.isLt

/-- The **black-box reduction** to the learner `A` with the output map `f` and the surrogate
feedback `φ` [Ora, Chapter 12]: the learner `A` plays `z t`, the reduction plays `f (z t)`, receives
the feedback `g t` of its play, and feeds `A` the surrogate feedback `φ (z t) (g t)`. The
surrogate may depend on the play of `A`, so the plays of `A` are those of its closed-loop run for
the feedback functions `z ↦ φ z (g t)` (`run_reduce`). The constrained learners of
[Ora, Section 12.1] are of this form, with `f` a projection onto the feasible set. -/
def reduce (f : X → Y) (φ : X → G' → G) : OnlineLearner C G' Y where
  play t h c := f (reducePlay A φ t h c)

private lemma play_reduce_eq_reducePlay (f : X → Y) (φ : X → G' → G) (t : ℕ)
    (h : Fin t → C × G') (c : C) : (A.reduce f φ).play t h c = f (reducePlay A φ t h c) := (rfl)

/-- The play of the reduction from the history `h` and the context `c` of round `t` is the image
by `f` of the play of `A` from the contexts of `h` and the surrogate feedback of the rounds
`s < t`, computed from the plays of `A` inside the reduction, which are those of `A.reduce id φ`
on the truncated histories. -/
lemma play_reduce (f : X → Y) (φ : X → G' → G) (t : ℕ) (h : Fin t → C × G') (c : C) :
    (A.reduce f φ).play t h c = f (A.play t (fun s ↦ ((h s).1,
      φ ((A.reduce id φ).play s (fun r ↦ h (Fin.castLE s.isLt.le r)) (h s).1) (h s).2)) c) := by
  simp only [play_reduce_eq_reducePlay, id]
  rw [reducePlay]

/-- The plays of `A` inside the reduction, from the history of a run, are the closed-loop plays
of `A`. -/
private lemma reducePlay_eq_run (φ : X → G' → G) (c : ℕ → C) (g : ℕ → G') (t : ℕ) :
    reducePlay A φ t (fun s ↦ (c s, g s)) (c t) =
      A.run c (A.closedLoopFeedback c fun s z ↦ φ z (g s)) t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [reducePlay, run_def]
    congr 1
    funext s
    rw [closedLoopFeedback_eq, ← ih s s.isLt]
    simp only [Fin.val_castLE]

/-- The plays of the reduction `A.reduce f φ` are the images by `f` of the plays of the closed-loop
run of `A` in which the feedback of round `t` is `φ z (g t)` for the play `z` of round `t`. -/
@[simp]
lemma run_reduce (f : X → Y) (φ : X → G' → G) (c : ℕ → C) (g : ℕ → G') (t : ℕ) :
    (A.reduce f φ).run c g t = f (A.run c (A.closedLoopFeedback c fun s z ↦ φ z (g s)) t) := by
  rw [run_def, play_reduce_eq_reducePlay, reducePlay_eq_run]

/-- **Regret of a reduction.** If at every round `t < n` and for every play `z` of `A`, the regret
increment of `f z` for the loss `L' (g t)` against `u` is at most the regret increment of `z` for
the surrogate loss `L (φ z (g t))` against `u`, then the regret of the reduction against `u` is at
most the regret of the closed-loop run of `A` on the surrogate feedback. -/
lemma regret_run_reduce_le (L : G → X → ℝ) (L' : G' → X → ℝ) (f : X → X) (φ : X → G' → G)
    (c : ℕ → C) (g : ℕ → G') (u : X) (n : ℕ)
    (hφ : ∀ t < n, ∀ z, L' (g t) (f z) - L' (g t) u ≤ L (φ z (g t)) z - L (φ z (g t)) u) :
    regret (fun t ↦ L' (g t)) ((A.reduce f φ).run c g) u n ≤
      regret (fun t ↦ L (A.closedLoopFeedback c (fun s z ↦ φ z (g s)) t))
        (A.run c (A.closedLoopFeedback c fun s z ↦ φ z (g s))) u n := by
  simp only [regret_def, run_reduce]
  refine sum_le_sum fun t ht ↦ ?_
  rw [closedLoopFeedback_eq]
  exact hφ t (mem_range.mp ht) _

variable {A} {L : G → X → ℝ} {adm : C → G → Prop} {U : Set X}
  {B : ℕ → (ℕ → C) → (ℕ → G) → X → ℝ}

/-- **Regret guarantee of a reduction.** Let `A` have the regret bound `B` for the losses `L`, the
admissible feedback `adm` and the comparators `U`. Let the surrogate feedback of every admissible
outer feedback be admissible, and let the regret increment of `f z` for the outer loss be at most
the regret increment of `z` for the surrogate loss, against every comparator of `U' ⊆ U`. Then the
reduction has the regret bound `B` at the surrogate feedback of its closed-loop run, against the
comparators of `U'`. -/
theorem HasRegretBound.reduce (hA : A.HasRegretBound L adm U B) {L' : G' → X → ℝ}
    {adm' : C → G' → Prop} {U' : Set X} {f : X → X} {φ : X → G' → G} (hU : U' ⊆ U)
    (hadm : ∀ c g z, adm' c g → adm c (φ z g))
    (hφ : ∀ c g z, adm' c g → ∀ u ∈ U', L' g (f z) - L' g u ≤ L (φ z g) z - L (φ z g) u) :
    (A.reduce f φ).HasRegretBound L' adm' U'
      (fun n c g u ↦ B n c (A.closedLoopFeedback c fun s z ↦ φ z (g s)) u) := by
  refine hasRegretBound_iff.mpr fun c g n hg u hu ↦ ?_
  refine (A.regret_run_reduce_le L L' f φ c g u n fun t ht z ↦ hφ _ _ z (hg t ht) u hu).trans ?_
  refine hA.regret_le (fun t ht ↦ ?_) (hU hu)
  rw [closedLoopFeedback_eq]
  exact hadm _ _ _ (hg t ht)

end Reduce

section SkipZero

open Nat

variable [Zero G] [DecidableEq G] (A : OnlineLearner C G X)

/-- The feedback of a history of `t` rounds as a sequence, extended by `0` after round `t`. -/
private noncomputable def histFeedback {t : ℕ} (h : Fin t → C × G) (s : ℕ) : G :=
  if hs : s < t then (h ⟨s, hs⟩).2 else 0

/-- The learner `A` **skipping the rounds with zero feedback** [Ora, Section 13.2.1]: it plays as
`A` run on the rounds whose feedback is nonzero only. At round `t`, with `k` rounds of nonzero
feedback before `t`, it plays the play of round `k` of `A` from the contexts and feedback of these
`k` rounds and the current context (`run_skipZero`). The rounds with zero feedback are invisible
to `A`: for linear losses, they contribute nothing to the regret, and the regret of `A.skipZero`
is the regret of `A` on the subsequence of rounds of nonzero feedback (`regret_run_skipZero`,
`HasRegretBound.skipZero`). -/
noncomputable def skipZero : OnlineLearner C G X where
  play t h c := A.play (count (histFeedback h · ≠ 0) t)
    (fun i ↦ h ⟨nth (histFeedback h · ≠ 0) i, nth_lt_of_lt_count i.isLt⟩) c

/-- **The plays of the learner skipping the rounds with zero feedback.** Its play of round `t` is
the play of `A` from the contexts and feedback of the `count (g · ≠ 0) t` rounds `s < t` of
nonzero feedback, the `i`-th of which is `nth (g · ≠ 0) i`, and from the context of round `t`. -/
lemma run_skipZero (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    A.skipZero.run c g t = A.play (count (g · ≠ 0) t)
      (fun i ↦ (c (nth (g · ≠ 0) i), g (nth (g · ≠ 0) i))) (c t) := by
  -- before round `t`, the feedback of the history is `g`
  have h_eq : ∀ s < t, histFeedback (fun s : Fin t ↦ (c s, g s)) s ≠ 0 ↔ g s ≠ 0 := fun s hs ↦ by
    simp [histFeedback, hs]
  have h_count := count_eq_count_of_forall_lt_iff h_eq
  rw [run_def]
  exact A.play_congr h_count
    (fun i hi ↦ by simp [nth_eq_nth_of_forall_lt_iff h_eq (h_count ▸ hi)]) (c t)

/-- At its `k`-th round of nonzero feedback, the learner skipping the rounds with zero feedback
plays the play of round `k` of `A` against the subsequences of the contexts and feedback of the
rounds of nonzero feedback. -/
lemma run_skipZero_nth (c : ℕ → C) (g : ℕ → G) {k n : ℕ} (hk : k < count (g · ≠ 0) n) :
    A.skipZero.run c g (nth (g · ≠ 0) k) =
      A.run (fun i ↦ c (nth (g · ≠ 0) i)) (fun i ↦ g (nth (g · ≠ 0) i)) k := by
  rw [run_skipZero, run_def]
  exact A.play_congr (count_nth_of_lt_count hk) (fun _ _ ↦ rfl) _

variable (L : G → X → ℝ)

/-- **Regret of the learner skipping the rounds with zero feedback.** For losses `L` that vanish
for the zero feedback, such as linear losses, the regret of `A.skipZero` after `n` rounds is the
regret of `A` after the `count (g · ≠ 0) n` rounds of nonzero feedback before `n`, against the
subsequences of the contexts and feedback of these rounds. -/
lemma regret_run_skipZero (hL : ∀ x, L 0 x = 0) (c : ℕ → C) (g : ℕ → G) (u : X) (n : ℕ) :
    regret (fun t ↦ L (g t)) (A.skipZero.run c g) u n =
      regret (fun k ↦ L (g (nth (g · ≠ 0) k)))
        (A.run (fun i ↦ c (nth (g · ≠ 0) i)) (fun i ↦ g (nth (g · ≠ 0) i))) u
        (count (g · ≠ 0) n) := by
  simp only [regret_def]
  -- the rounds of zero feedback contribute nothing, and the others are indexed by `nth`
  rw [← sum_filter_of_ne (p := fun t ↦ g t ≠ 0) fun t _ ht h0 ↦ ht (by simp [h0, hL])]
  refine sum_bij' (fun t _ ↦ count (g · ≠ 0) t) (fun k _ ↦ nth (g · ≠ 0) k) (fun t ht ↦ ?_)
    (fun k hk ↦ ?_) (fun t ht ↦ ?_) (fun k hk ↦ ?_) fun t ht ↦ ?_
  · obtain ⟨htn, hgt⟩ := mem_filter.mp ht
    exact mem_range.mpr (count_strict_mono hgt (mem_range.mp htn))
  · have hk := mem_range.mp hk
    exact mem_filter.mpr ⟨mem_range.mpr (nth_lt_of_lt_count hk), nth_mem_of_lt_count hk⟩
  · exact nth_count (mem_filter.mp ht).2
  · exact count_nth_of_lt_count (mem_range.mp hk)
  · obtain ⟨htn, hgt⟩ := mem_filter.mp ht
    rw [← run_skipZero_nth A c g (count_strict_mono hgt (mem_range.mp htn)), nth_count hgt]

variable {A L} {adm : C → G → Prop} {U : Set X} {B : ℕ → (ℕ → C) → (ℕ → G) → X → ℝ}

/-- **Regret guarantee of the learner skipping the rounds with zero feedback** [Ora,
Section 13.2.1]. For losses `L` that vanish for the zero feedback, if `A` has the regret bound `B`,
then `A.skipZero` has the regret bound `B` evaluated at the number `count (g · ≠ 0) n` of rounds of
nonzero feedback before `n`, and at the subsequences of the contexts and feedback of these rounds.
For a bound in the horizon, this replaces the horizon by the number of rounds of nonzero
feedback. -/
theorem HasRegretBound.skipZero (hA : A.HasRegretBound L adm U B) (hL : ∀ x, L 0 x = 0) :
    A.skipZero.HasRegretBound L adm U (fun n c g u ↦ B (count (g · ≠ 0) n)
      (fun i ↦ c (nth (g · ≠ 0) i)) (fun i ↦ g (nth (g · ≠ 0) i)) u) := by
  refine hasRegretBound_iff.mpr fun c g n hg u hu ↦ ?_
  rw [regret_run_skipZero A L hL]
  exact hA.regret_le (fun k hk ↦ hg _ (nth_lt_of_lt_count hk)) hu

end SkipZero

end OnlineLearner

end LMLExplore.OnlineLearning
