/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Basic.ENNReal.BigOperators
public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Topology.Sion
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# The pure exploration game in minimax form

The value `D(θ, ¬i) = sup_{w ∈ Δ_K} inf_{λ ∈ ¬i} ∑ a, w a KL(ν_a(θ), ν_a(λ))` of the answer `i`
at the model `θ` is the value of a zero-sum game in which the allocation player moves first: it
chooses proportions `w` of samples of the arms, then the alternative player chooses a model
`λ ∈ ¬i` for which `i` is not correct, and the payoff is the transportation cost. The game has a
value: the alternative player may move first, if it is allowed to randomize over finitely many
alternatives, against which the best response of the allocation player is a single arm. For every
model `θ` and answer `i`,
`D(θ, ¬i) = inf_q max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]`,
where `q` ranges over the finitely supported probability distributions on `¬i` (Mathlib's
`Convexity.StdSimplex ℝ Θ`, with support in `¬i`) [DK19, Lemma 2; DKM19, Section 2].

This is the form in which the game is played by the sampling rules that solve it with online
learners, and in which the lower bound of tasks with multiple correct answers uses it: a
distribution `q` on the alternatives with `E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < c` for all arms `a`,
for each `c > D(θ, ¬i)`, makes all the arms uninformative at once.

The divergences are `ℝ≥0∞`-valued, and no finiteness is assumed. The proof applies von Neumann's
minimax theorem on the simplex (`LMLExplore.iSup_simplex_iInf_ofReal_dotProduct`) to the
alternatives at finite divergence from `θ` on every arm, which have the same value
(`IdentTask.answerValue_restrict_setOf_klDiv_ne_top`, in
`LMLExplore/Identification/Task/TransportationCost.lean`): an allocation with positive entries
pays an infinite cost against every other alternative.

## Main statements

* `IdentTask.answerValue_le_iSup_sum_klDiv`: weak duality, `D(θ, ¬i)` is at most
  `max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]` for every finitely supported distribution `q` on `¬i`.
* `IdentTask.answerValue_eq_iInf_iSup_sum_klDiv`: the minimax form of `D(θ, ¬i)`
  [DK19, Lemma 2].
* `IdentTask.exists_forall_sum_klDiv_lt_of_answerValue_lt`: for `c > D(θ, ¬i)`, some finitely
  supported distribution `q` on `¬i` has `E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < c` for every arm `a`.
* `IdentTask.inv_charTime_eq_iSup_iInf_iSup_sum_klDiv`: the characteristic time of a task with
  several correct answers, `T*(θ)⁻¹ = sup_{i ∈ i*(θ)} D(θ, ¬i)`, with each `D(θ, ¬i)` in minimax
  form.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Convexity

open scoped ENNReal NNReal

namespace LMLExplore.Identification

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ}

/-- **Weak duality.** The value `D(θ, ¬i)` is at most `max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]` for
every finitely supported distribution `q` on the alternatives to `i`: against the mixture `q`, an
allocation `w` collects `∑ a, w a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]`, at least the cost of the
cheapest alternative. -/
lemma answerValue_le_iSup_sum_klDiv {q : StdSimplex ℝ Θ} (hq : ↑q.weights.support ⊆ task.alt i) :
    task.answerValue θ i ≤
      ⨆ a, q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a) := by
  rw [answerValue_def]
  refine iSup₂_le fun w hw ↦ ?_
  have hq1 : ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun θ' _ ↦ q.weights_nonneg θ', ← ENNReal.ofReal_one,
      ← q.total, Finsupp.sum]
  calc task.altCost θ w i
      = ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') * task.altCost θ w i := by
        rw [← Finset.sum_mul, hq1, one_mul]
    _ ≤ ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') * task.cost w θ θ' :=
        Finset.sum_le_sum fun θ' hθ' ↦ by gcongr; exact task.altCost_le_cost (hq hθ') w
    _ = ∑ a, ENNReal.ofReal (w a) * q.weights.sum fun θ' r ↦
          ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a) := by
        simp only [cost_def, Finsupp.sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr! 2 with a _ θ' _
        exact mul_left_comm _ _ _
    _ ≤ _ := sum_ofReal_mul_le_iSup hw _

/-- The minimax inequality `inf_q max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] ≤ D(θ, ¬i)` when all the
alternatives to `i` are at finite divergence from `θ` on every arm: von Neumann's minimax theorem
on the simplex, for the convex set of the vectors `(E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))])_a`. -/
private lemma iInf_iSup_sum_klDiv_le_of_ne_top [Nonempty α]
    (hfin : ∀ θ' ∈ task.alt i, ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    ⨅ (q : StdSimplex ℝ Θ) (_ : ↑q.weights.support ⊆ task.alt i),
      ⨆ a, (q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a)) ≤
      task.answerValue θ i := by
  classical
  -- The vectors of divergences of the alternatives, and the convex set of their mixtures.
  set p : Θ → α → ℝ := fun θ' a ↦ (klDiv (task.ν θ a) (task.ν θ' a)).toReal
  set Q : Set (Θ →₀ ℝ) :=
    {q | 0 ≤ q ∧ ↑q.support ⊆ task.alt i ∧ q.sum (fun _ r ↦ r) = 1}
  set Y := Finsupp.linearCombination ℝ p '' Q
  have hmix {q : Θ →₀ ℝ} (hq : q ∈ Q) (a : α) :
      ENNReal.ofReal (Finsupp.linearCombination ℝ p q a) =
        q.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Finsupp.sum]
    simp_rw [Pi.smul_apply, smul_eq_mul]
    exact ENNReal.ofReal_sum_mul_toReal (fun θ' _ ↦ hq.1 θ') fun θ' hθ' ↦ hfin θ' (hq.2.1 hθ') a
  have hsingle (θ' : Θ) (hθ' : θ' ∈ task.alt i) : p θ' ∈ Y := by
    refine ⟨Finsupp.single θ' 1, ⟨Finsupp.single_nonneg.2 zero_le_one, ?_, ?_⟩, ?_⟩
    · exact (Finset.coe_subset.2 Finsupp.support_single_subset).trans (by simpa using hθ')
    · exact Finsupp.sum_single_index rfl
    · simp
  calc ⨅ (q : StdSimplex ℝ Θ) (_ : ↑q.weights.support ⊆ task.alt i),
        ⨆ a, (q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a))
      ≤ ⨅ y ∈ Y, ⨆ a, ENNReal.ofReal (y a) := by
        refine le_iInf₂ fun y ⟨q, hq, hy⟩ ↦ ?_
        subst hy
        exact iInf₂_le_of_le ⟨q, hq.1, hq.2.2⟩ hq.2.1 (by simp_rw [hmix hq]; rfl)
    _ = ⨆ w ∈ simplex α, ⨅ y ∈ Y, ENNReal.ofReal (w ⬝ᵥ y) :=
        (iSup_simplex_iInf_ofReal_dotProduct
          ((convex_setOf_nonneg_support_subset_sum_eq_one _).linear_image _)).symm
    _ ≤ task.answerValue θ i := by
        rw [answerValue_def]
        refine iSup₂_mono fun w hw ↦ ?_
        rw [altCost_def]
        refine le_iInf₂ fun θ' hθ' ↦ iInf₂_le_of_le _ (hsingle θ' hθ') ?_
        rw [dotProduct, cost_def]
        exact (ENNReal.ofReal_sum_mul_toReal (fun a _ ↦ (mem_simplex_iff.1 hw).1 a)
          fun a _ ↦ hfin θ' hθ' a).le

/-- **The pure exploration game in minimax form** [DK19, Lemma 2]. The value `D(θ, ¬i)` of the
answer `i` at the model `θ` is `inf_q max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]`, where `q` ranges over
the finitely supported probability distributions on the alternatives to `i`: the allocation player
and the alternative player can move in either order. ([DK19, Lemma 2] moreover restricts `q` to at
most `K` atoms.) -/
theorem answerValue_eq_iInf_iSup_sum_klDiv [Nonempty α] (θ : Θ) (i : ℐ) :
    task.answerValue θ i = ⨅ (q : StdSimplex ℝ Θ) (_ : ↑q.weights.support ⊆ task.alt i),
      ⨆ a, q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a) := by
  refine le_antisymm (le_iInf₂ fun q hq ↦ task.answerValue_le_iSup_sum_klDiv hq) ?_
  set S := {θ' | ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞}
  calc _ ≤ ⨅ (q : StdSimplex ℝ Θ) (_ : ↑q.weights.support ⊆ (task.restrict S).alt i),
        ⨆ a, q.weights.sum fun θ' r ↦
          ENNReal.ofReal r * klDiv ((task.restrict S).ν θ a) ((task.restrict S).ν θ' a) := by
        rw [alt_restrict, ν_restrict]
        exact biInf_mono fun q hq ↦ hq.trans Set.inter_subset_left
    _ ≤ (task.restrict S).answerValue θ i := by
        refine (task.restrict S).iInf_iSup_sum_klDiv_le_of_ne_top fun θ' hθ' ↦ ?_
        rw [alt_restrict] at hθ'
        simpa only [ν_restrict, S, Set.mem_ofPred_eq] using hθ'.2
    _ = task.answerValue θ i := task.answerValue_restrict_setOf_klDiv_ne_top θ i

/-- For `c > D(θ, ¬i)`, some finitely supported distribution `q` on the alternatives to `i`
satisfies `E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < c` for every arm `a`. -/
theorem exists_forall_sum_klDiv_lt_of_answerValue_lt [Nonempty α] {c : ℝ≥0∞}
    (h : task.answerValue θ i < c) :
    ∃ q : StdSimplex ℝ Θ, ↑q.weights.support ⊆ task.alt i ∧
      ∀ a, (q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a)) < c := by
  rw [task.answerValue_eq_iInf_iSup_sum_klDiv θ i] at h
  simp only [iInf_lt_iff, exists_prop] at h
  obtain ⟨q, hq, hc⟩ := h
  exact ⟨q, hq, fun a ↦ (le_iSup (fun a ↦ q.weights.sum fun θ' r ↦
    ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a)) a).trans_lt hc⟩

/-- **The characteristic time of a task with several correct answers** [DK19, Lemma 2]:
`T*(θ)⁻¹ = sup_{i ∈ i*(θ)} inf_q max_a E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))]`, where for each correct
answer `i`, `q` ranges over the finitely supported probability distributions on the alternatives
to `i`. -/
theorem inv_charTime_eq_iSup_iInf_iSup_sum_klDiv [Nonempty α] (θ : Θ) :
    (task.charTime θ)⁻¹ = ⨆ i ∈ task.correct θ,
      ⨅ (q : StdSimplex ℝ Θ) (_ : ↑q.weights.support ⊆ task.alt i),
        ⨆ a, q.weights.sum fun θ' r ↦ ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a) := by
  simp_rw [charTime_def, inv_inv, gameValue_def, task.answerValue_eq_iInf_iSup_sum_klDiv θ]

end IdentTask

end LMLExplore.Identification
