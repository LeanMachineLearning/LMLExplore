/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.FTRL.Basic
public import LMLExplore.OnlineLearning.Learner.Basic

/-!
# The FTRL learner

Follow the regularized leader is specified in `LMLExplore.OnlineLearning.FTRL.Basic` by the
predicate `IsFTRLPlay` on its plays, and its regret bounds take the plays as hypotheses. This file
constructs the algorithm as an online learner (`OnlineLearner`) for online linear optimization: the
learner `OnlineLearner.ftrl K F η x₀` plays at round `t` a minimizer over `K` of the FTRL objective
`b ↦ η t * ∑ s < t, y s b + F b` of the past linear losses, chosen among the minimizers when there
is one, and the default point `x₀` when there is none.

* Its plays are FTRL plays at every round where a minimizer exists (`isFTRLPlay_run_ftrl`), in
  particular at every round when `K` is compact and nonempty and `F` is continuous on `K`
  (`isFTRLPlay_run_ftrl_of_isCompact`).
* With a strongly convex potential and positive nonincreasing learning rates, it has the anytime
  regret bound of [Ora, Corollary 7.6]
  `(F u - F (x 0)) / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2` against every `u ∈ K`, for every
  sequence of linear losses (`hasRegretBound_ftrl_of_strongConvexOn`).

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.ftrl K F η x₀`: the FTRL learner.

## Main statements

* `OnlineLearner.isFTRLPlay_run_ftrl`: the plays of the FTRL learner are FTRL plays.
* `OnlineLearner.hasRegretBound_ftrl_of_strongConvexOn`: the regret guarantee of the FTRL
  learner with a strongly convex potential.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

namespace OnlineLearner

variable {C E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ}
  {η : ℕ → ℝ} {x₀ : E}

open Classical in
/-- The **FTRL learner** on `K` with potential `F`, learning rates `η` and default play `x₀`, for
online linear optimization: at round `t`, it plays a minimizer over `K` of the FTRL objective
`b ↦ η t * ∑ s < t, y s b + F b` of the past linear losses `y s` when one exists, and `x₀`
otherwise. It ignores the contexts. -/
noncomputable def ftrl (K : Set E) (F : E → ℝ) (η : ℕ → ℝ) (x₀ : E) :
    OnlineLearner C (E →L[ℝ] ℝ) E where
  play t h _ :=
    if hx : ∃ x ∈ K, IsMinOn (fun b ↦ η t * ∑ s, (h s).2 b + F b) K x then hx.choose else x₀

open Classical in
/-- The play of the FTRL learner: a minimizer over `K` of the FTRL objective of the history when
one exists, and `x₀` otherwise. -/
lemma play_ftrl (t : ℕ) (h : Fin t → C × (E →L[ℝ] ℝ)) (c : C) :
    (ftrl K F η x₀).play t h c =
      if hx : ∃ x ∈ K, IsMinOn (fun b ↦ η t * ∑ s, (h s).2 b + F b) K x then hx.choose
      else x₀ := (rfl)

/-- When the FTRL objective of the history has a minimizer over `K`, the FTRL learner plays one. -/
lemma play_ftrl_of_exists {t : ℕ} {h : Fin t → C × (E →L[ℝ] ℝ)}
    (hx : ∃ x ∈ K, IsMinOn (fun b ↦ η t * ∑ s, (h s).2 b + F b) K x) (c : C) :
    (ftrl K F η x₀).play t h c ∈ K ∧
      IsMinOn (fun b ↦ η t * ∑ s, (h s).2 b + F b) K ((ftrl K F η x₀).play t h c) := by
  simp only [play_ftrl, hx, dite_true]
  exact hx.choose_spec

/-- When the FTRL objective of the history has no minimizer over `K`, the FTRL learner plays the
default point `x₀`. -/
lemma play_ftrl_of_not_exists {t : ℕ} {h : Fin t → C × (E →L[ℝ] ℝ)}
    (hx : ¬ ∃ x ∈ K, IsMinOn (fun b ↦ η t * ∑ s, (h s).2 b + F b) K x) (c : C) :
    (ftrl K F η x₀).play t h c = x₀ := by
  simp [play_ftrl, hx]

/-- **The FTRL learner plays FTRL.** At every round where the FTRL objective has a minimizer over
`K`, the play of the FTRL learner is a play of FTRL (`IsFTRLPlay`). -/
theorem isFTRLPlay_run_ftrl (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) {t : ℕ}
    (h : ∃ x, IsFTRLPlay K F (η t) y t x) :
    IsFTRLPlay K F (η t) y t ((ftrl K F η x₀).run c y t) := by
  have h_obj : (fun b ↦ η t * ∑ s : Fin t, y s b + F b) =
      fun b ↦ η t * ∑ s ∈ range t, y s b + F b := by
    funext b
    rw [Fin.sum_univ_eq_sum_range (fun s ↦ y s b) t]
  obtain ⟨x, hx⟩ := h
  obtain ⟨hmem, hmin⟩ := play_ftrl_of_exists (x₀ := x₀) (h := fun s ↦ (c s, y s))
    ⟨x, hx.mem, by rw [h_obj]; exact hx.isMinOn⟩ (c t)
  rw [h_obj] at hmin
  rw [run_def]
  exact ⟨hmem, hmin⟩

/-- On a nonempty compact set `K`, with a potential `F` continuous on `K`, every play of the FTRL
learner is a play of FTRL. -/
theorem isFTRLPlay_run_ftrl_of_isCompact (hK : IsCompact K) (hK_ne : K.Nonempty)
    (hF : ContinuousOn F K) (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    IsFTRLPlay K F (η t) y t ((ftrl K F η x₀).run c y t) :=
  isFTRLPlay_run_ftrl c y <| by
    obtain ⟨a, ha⟩ := exists_ftrl hK hK_ne hF (η t) y
    exact ⟨a t, ha t⟩

/-- **Regret guarantee of the FTRL learner** [Ora, Corollary 7.6]. Let `K` be compact, let the
potential `F` be continuous on `K` and `m`-strongly convex on `K` (so that `K` is convex) for the
norm of `E` with `m > 0`, and let the learning rates `η t > 0` be nonincreasing. Then for every
sequence of linear losses `y`, every horizon `n` and every `u ∈ K`, the plays `x` of the FTRL
learner satisfy
`∑ t < n, y t (x t - u) ≤ (F u - F (x 0)) / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`,
where `x 0` minimizes `F` over `K` and `‖y t‖` is the dual norm. -/
theorem hasRegretBound_ftrl_of_strongConvexOn (hK : IsCompact K) (hF_cont : ContinuousOn F K)
    {m : ℝ} (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) :
    (ftrl (C := C) K F η x₀).HasRegretBound (fun y x ↦ y x) (fun _ _ ↦ True) K
      (fun n c y u ↦ (F u - F ((ftrl K F η x₀).run c y 0)) / η (n - 1) +
        ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2) := by
  refine hasRegretBound_iff.mpr fun c y n _ u hu ↦ ?_
  have ha (t : ℕ) := isFTRLPlay_run_ftrl_of_isCompact (η := η) (x₀ := x₀) hK ⟨u, hu⟩ hF_cont c y t
  rw [regret_eq_sum_apply_sub]
  exact ftrl_regret_le_of_strongConvexOn_of_antitone hF hm hη hη_anti y _ (ha 0)
    (fun t _ ↦ ha t) hu

end OnlineLearner

end LMLExplore.OnlineLearning
