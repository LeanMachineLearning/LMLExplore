/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.OnlineLearning.Regret

/-!
# Online learners

A deterministic online learner plays, at each round `t = 0, 1, …`, a point of a type `X`. Before
its play it sees a context in a type `C` (the set of active experts, a hint, …), and after its play
it receives a feedback in a type `G` (a loss function, a subgradient, a coin outcome, …). The play
of round `t` is a function of the contexts and feedback of the rounds `s < t` and of the context of
round `t`: an `OnlineLearner C G X` is this function. This file defines learners, their runs and a
predicate for their regret guarantees [Ora, Chapter 1]. The structures of the reductions of
[Ora, Chapters 12–14] compose learners; the operations that they use are in
`LMLExplore.OnlineLearning.Learner.Operations`.

* The **run** `A.run c g` of a learner against sequences of contexts `c` and feedback `g` is the
  sequence of its plays. The play of round `t` depends only on the contexts of the rounds `s ≤ t`
  and on the feedback of the rounds `s < t` (`run_congr`), and a learner is determined by its runs
  when `G` is nonempty (`ext_run`).
* In the **closed-loop run**, the feedback of round `t` is a given function `φ t` of the play of
  round `t`, as for the surrogate losses of a reduction, or the subgradients of convex losses at
  the plays. The feedback sequence `A.closedLoopFeedback c φ` is defined by recursion on the
  rounds; it is the unique sequence `g` with `g t = φ t (A.run c g t)` for every `t`
  (`closedLoopFeedback_eq`, `closedLoopFeedback_unique`), and the closed-loop plays are the run
  `A.run c (A.closedLoopFeedback c φ)`.
* A **regret guarantee** `A.HasRegretBound L adm U B` says that, against every sequence of
  feedback whose first `n` values are admissible (`adm`) for their contexts, the regret after `n`
  rounds of the plays of `A` for the losses `L (g t)` against every comparator `u ∈ U` is at most
  `B n c g u` (`HasRegretBound.regret_le`). Since the bound holds for every sequence of feedback,
  it holds in particular for the feedback `A.closedLoopFeedback c φ` of the closed-loop runs, that
  is, against adaptive adversaries.

The learners of this file are deterministic and use no measurability: LML's
`Learning.Algorithm.deterministic` is the measurable counterpart, used for stochastic environments.

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner C G X`: a causal online learner.
* `LMLExplore.OnlineLearning.OnlineLearner.run A c g`: the plays of `A` against the contexts `c`
  and the feedback `g`.
* `LMLExplore.OnlineLearning.OnlineLearner.closedLoopFeedback A c φ`: the feedback of the
  closed-loop run, in which the feedback of round `t` is `φ t` of the play of round `t`.
* `LMLExplore.OnlineLearning.OnlineLearner.HasRegretBound A L adm U B`: the regret guarantee.

## Main statements

* `OnlineLearner.run_congr`: causality of the runs.
* `OnlineLearner.ext_run`: a learner with nonempty feedback type is determined by its runs.
* `OnlineLearner.closedLoopFeedback_eq`, `OnlineLearner.eq_closedLoopFeedback_of_forall_lt`,
  `OnlineLearner.closedLoopFeedback_unique`: the closed-loop feedback is the unique fixed point of
  `g ↦ fun t ↦ φ t (A.run c g t)`, also on a finite horizon.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

namespace LMLExplore.OnlineLearning

/-- A causal deterministic **online learner** with contexts in `C`, feedback in `G` and plays in
`X`: the play `A.play t h c` of round `t`, from the history `h` of the contexts and feedback of the
rounds `s < t` and the context `c` of round `t`. The context of a round is revealed before the
play (for example the set of active experts, or a hint), and the feedback after it (for example a
loss function, or a subgradient of the loss at the play). -/
@[ext]
structure OnlineLearner (C G X : Type*) where
  /-- The play of round `t`, from the contexts and feedback of the rounds `s < t` and the context
  of round `t`. -/
  play : (t : ℕ) → (Fin t → C × G) → C → X

namespace OnlineLearner

variable {C G X : Type*} (A : OnlineLearner C G X)

section Run

/-- The **run** of the learner `A` against the contexts `c` and the feedback `g`: the play of
round `t` is the play of `A` from the contexts and feedback of the rounds `s < t` and the context
of round `t`. -/
def run (c : ℕ → C) (g : ℕ → G) (t : ℕ) : X :=
  A.play t (fun s ↦ (c s, g s)) (c t)

lemma run_def (c : ℕ → C) (g : ℕ → G) (t : ℕ) :
    A.run c g t = A.play t (fun s ↦ (c s, g s)) (c t) := (rfl)

/-- The first play of a run depends only on the first context. -/
lemma run_zero (c : ℕ → C) (g : ℕ → G) : A.run c g 0 = A.play 0 Fin.elim0 (c 0) := by
  rw [run_def]
  congr
  exact funext fun s ↦ s.elim0

/-- **Causality** of the runs: the play of round `t` depends only on the contexts of the rounds
`s ≤ t` and on the feedback of the rounds `s < t`. -/
lemma run_congr {c c' : ℕ → C} {g g' : ℕ → G} {t : ℕ} (hc : ∀ s ≤ t, c s = c' s)
    (hg : ∀ s < t, g s = g' s) : A.run c g t = A.run c' g' t := by
  rw [run_def, run_def, hc t le_rfl]
  congr
  exact funext fun s ↦ by rw [hc s s.2.le, hg s s.2]

/-- The play of round `t` does not depend on the feedback of the rounds `s ≥ t`. -/
lemma run_congr_feedback (c : ℕ → C) {g g' : ℕ → G} {t : ℕ} (hg : ∀ s < t, g s = g' s) :
    A.run c g t = A.run c g' t :=
  A.run_congr (fun _ _ ↦ rfl) hg

/-- Every play of a learner from a history and a context is the play of round `t` of a run: the
run against sequences extending the history, with the context `c₀` at round `t`. -/
lemma exists_run_eq_play [Nonempty G] (t : ℕ) (h : Fin t → C × G) (c₀ : C) :
    ∃ (c : ℕ → C) (g : ℕ → G), ∀ B : OnlineLearner C G X, B.run c g t = B.play t h c₀ := by
  classical
  obtain ⟨g₀⟩ := ‹Nonempty G›
  refine ⟨fun s ↦ if hs : s < t then (h ⟨s, hs⟩).1 else c₀,
    fun s ↦ if hs : s < t then (h ⟨s, hs⟩).2 else g₀, fun B ↦ ?_⟩
  simp only [run_def, lt_irrefl, dite_false]
  congr
  exact funext fun s ↦ by simp [s.2]

/-- A learner with a nonempty type of feedback is determined by its runs. -/
lemma ext_run [Nonempty G] {A B : OnlineLearner C G X}
    (h : ∀ (c : ℕ → C) (g : ℕ → G) (t : ℕ), A.run c g t = B.run c g t) : A = B := by
  ext t hist c₀
  obtain ⟨c, g, hcg⟩ := exists_run_eq_play t hist c₀
  rw [← hcg A, ← hcg B, h]

end Run

section ClosedLoop

/-- The feedback of the **closed-loop run** of the learner `A` against the contexts `c` with the
feedback functions `φ`: the feedback of round `t` is `φ t` applied to the play of round `t`, which
is the play of `A` from the contexts and the closed-loop feedback of the rounds `s < t` and the
context of round `t`. The closed-loop plays are `A.run c (A.closedLoopFeedback c φ)`
(`closedLoopFeedback_eq`). -/
def closedLoopFeedback (c : ℕ → C) (φ : ℕ → X → G) (t : ℕ) : G :=
  φ t (A.play t (fun s ↦ (c s, closedLoopFeedback c φ s)) (c t))
termination_by t
decreasing_by exact s.isLt

/-- The feedback of round `t` of the closed-loop run is `φ t` applied to the play of round `t`. -/
lemma closedLoopFeedback_eq (c : ℕ → C) (φ : ℕ → X → G) (t : ℕ) :
    A.closedLoopFeedback c φ t = φ t (A.run c (A.closedLoopFeedback c φ) t) := by
  rw [closedLoopFeedback, run_def]

/-- **Uniqueness of the closed-loop feedback on a finite horizon.** A sequence `g` whose value at
each round `t < n` is `φ t` applied to the play of round `t` of the run against `g` agrees with the
closed-loop feedback on the rounds `t < n`. -/
lemma eq_closedLoopFeedback_of_forall_lt {c : ℕ → C} {φ : ℕ → X → G} {g : ℕ → G} {n : ℕ}
    (hg : ∀ t < n, g t = φ t (A.run c g t)) {t : ℕ} (ht : t < n) :
    g t = A.closedLoopFeedback c φ t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [hg t ht, closedLoopFeedback_eq,
      A.run_congr_feedback c fun s hs ↦ ih s hs (hs.trans ht)]

/-- **Uniqueness of the closed-loop feedback.** The closed-loop feedback is the unique sequence `g`
whose value at each round is `φ t` applied to the play of round `t` of the run against `g`. -/
lemma closedLoopFeedback_unique {c : ℕ → C} {φ : ℕ → X → G} {g : ℕ → G}
    (hg : ∀ t, g t = φ t (A.run c g t)) : g = A.closedLoopFeedback c φ :=
  funext fun t ↦ A.eq_closedLoopFeedback_of_forall_lt (n := t + 1) (fun s _ ↦ hg s) t.lt_succ_self

/-- The closed-loop feedback of the rounds `t < n` depends only on the contexts and on the feedback
functions of the rounds `t < n`. -/
lemma closedLoopFeedback_congr {c c' : ℕ → C} {φ φ' : ℕ → X → G} {n : ℕ}
    (hc : ∀ t < n, c t = c' t) (hφ : ∀ t < n, φ t = φ' t) {t : ℕ} (ht : t < n) :
    A.closedLoopFeedback c φ t = A.closedLoopFeedback c' φ' t := by
  refine A.eq_closedLoopFeedback_of_forall_lt (fun s hs ↦ ?_) ht
  rw [closedLoopFeedback_eq, hφ s hs,
    A.run_congr (fun r hr ↦ hc r (hr.trans_lt hs)) fun _ _ ↦ rfl]

end ClosedLoop

section HasRegretBound

/-- The learner `A` has the **regret bound** `B` for the losses `L`, the admissible feedback `adm`
and the comparators `U`: for all contexts `c`, feedback `g` and horizons `n` such that the feedback
`g t` of each round `t < n` is admissible for the context `c t`, the regret after `n` rounds of the
plays of `A` for the losses `L (g t)` against every comparator `u ∈ U` is at most `B n c g u`.

For online linear optimization, the feedback is a linear loss `y t` and `L y x = y x`; for
prediction with expert advice, it is the vector of the losses of the experts. The bound may depend
on the horizon, on the contexts and feedback, and on the comparator. -/
def HasRegretBound (L : G → X → ℝ) (adm : C → G → Prop) (U : Set X)
    (B : ℕ → (ℕ → C) → (ℕ → G) → X → ℝ) : Prop :=
  ∀ (c : ℕ → C) (g : ℕ → G) (n : ℕ), (∀ t < n, adm (c t) (g t)) →
    ∀ u ∈ U, regret (fun t ↦ L (g t)) (A.run c g) u n ≤ B n c g u

variable {A} {L : G → X → ℝ} {adm adm' : C → G → Prop} {U U' : Set X}
  {B B' : ℕ → (ℕ → C) → (ℕ → G) → X → ℝ}

lemma hasRegretBound_iff : A.HasRegretBound L adm U B ↔
    ∀ (c : ℕ → C) (g : ℕ → G) (n : ℕ), (∀ t < n, adm (c t) (g t)) →
      ∀ u ∈ U, regret (fun t ↦ L (g t)) (A.run c g) u n ≤ B n c g u := Iff.rfl

/-- The regret inequality of a regret guarantee. It applies to every run, in particular to the
closed-loop runs, with `g = A.closedLoopFeedback c φ`. -/
lemma HasRegretBound.regret_le (hA : A.HasRegretBound L adm U B) {c : ℕ → C} {g : ℕ → G} {n : ℕ}
    (hg : ∀ t < n, adm (c t) (g t)) {u : X} (hu : u ∈ U) :
    regret (fun t ↦ L (g t)) (A.run c g) u n ≤ B n c g u :=
  hA c g n hg u hu

/-- A regret guarantee holds for fewer admissible feedback, fewer comparators and larger bounds. -/
lemma HasRegretBound.mono (hA : A.HasRegretBound L adm U B)
    (hadm : ∀ c g, adm' c g → adm c g) (hU : U' ⊆ U)
    (hB : ∀ n c g u, (∀ t < n, adm' (c t) (g t)) → u ∈ U' → B n c g u ≤ B' n c g u) :
    A.HasRegretBound L adm' U' B' := fun c g n hg u hu ↦
  (hA.regret_le (fun t ht ↦ hadm _ _ (hg t ht)) (hU hu)).trans (hB n c g u hg hu)

end HasRegretBound

end OnlineLearner

end LMLExplore.OnlineLearning
