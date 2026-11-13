/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Basic

/-!
# Operations on online learners

The reductions of online learning [Ora, Chapters 12–14] build learners from other learners: they
restart copies of a learner, run learners coordinatewise, add the plays of several learners, and
transform the plays of a learner. This file defines these operations on `OnlineLearner`, computes
their runs, and transfers regret guarantees (`OnlineLearner.HasRegretBound`) through them.

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

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.restart A s`: `A` restarted at round `s`.
* `LMLExplore.OnlineLearning.OnlineLearner.pi A`: the coordinatewise product of a family of
  learners.
* `LMLExplore.OnlineLearning.OnlineLearner.sum A`: the sum of the plays of a finite family of
  learners.
* `LMLExplore.OnlineLearning.OnlineLearner.map A f`: the images by `f` of the plays of `A`.

## Main statements

* `OnlineLearner.intervalRegret_run_restart`: the regret of a learner restarted at round `s` on the
  rounds `[s, s + τ)` is the regret after `τ` rounds of the learner on the shifted feedback.
* `OnlineLearner.HasRegretBound.pi`: the regret guarantee of a coordinatewise product.
* `OnlineLearner.regret_run_sum_le`: the regret of a sum of learners is at most the sum of their
  regret bounds, for every decomposition of the comparator.
* `OnlineLearner.HasRegretBound.map_add_left`: the regret guarantee of a translated learner.

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
  exact funext fun i ↦ hh i i.2

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

end OnlineLearner

end LMLExplore.OnlineLearning
