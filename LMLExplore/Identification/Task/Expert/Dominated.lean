/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.Expert.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import LMLExplore.EValues.BipolarRate.Universal
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Experts that determine `D*` at every dominated model

For an identification task, write `D*(θ, ¬i)` for the rate of the designs of the laws of the arms
at the model `θ` against the laws of the arms at the alternatives to the answer `i`. Let the
observation space `𝓨` be countably generated and `ρ a` an s-finite measure for every arm `a`. One
sequence of experts determines `D*` at every model `θ` whose laws of the arms are dominated,
`task.ν θ a ≪ ρ a` for every arm `a`, for every answer `i`
(`LMLExplore.Identification.IdentTask.DeterminesDesignRate`) [EVR26, Note 55, Lemma 6; Note 49,
Lemma 1]. Run with these experts, the algorithm of [EVR26, Note 49] attains `D*` at every
admissible dominated model with a single correct answer [EVR26, Note 49, Theorem 3]; that algorithm
is not constructed in this file.

For an answer `i` and a design `s ≠ 0`, the laws of the table of `s` at the alternatives to `i`
form a null for i.i.d. tables, and at a model whose laws of the arms are dominated by the measures
`ρ a` the law of the table of `s` is dominated by the finite measure
`designLaw (fun a ↦ (ρ a).toFinite) s`. Countably many bounded bets on `m` tables of `s` have
normalized means of supremum the bipolar rate of the table of `s` at every such model
(`ProbabilityTheory.exists_iSup_integral_div_eq_bipolarRate`), and a bet on `m` tables of `s` is
a function of one table of the design `m • s` (`ProbabilityTheory.designBlockEquiv`), hence an
expert of shape `m • s`. The rate of the designs is the supremum over `s` of the bipolar rate of
the table of `s` per observation (`ProbabilityTheory.designRate_eq_iSup_bipolarRate`), so these
experts, for all answers and all designs, determine `D*`.

## Main statements

* `IdentTask.exists_isExpert_determinesDesignRate_of_absolutelyContinuous`, in the namespace
  `LMLExplore.Identification`: one sequence of experts determines `D*` at every dominated model,
  for every answer.

## Implementation notes

The statement and proof are adapted from `EValuesResearch/Results/DesignExpertsExist.lean`
(commit `cb8238f`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 49, *An identification algorithm that attains `D*` at every
  instance*, Lemma 1 and Theorem 3, and Note 55, *Classes that are not dominated: attaining the
  rate and `D*` with one procedure*, Lemma 6.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨)

/-- **Experts for the dominated models** [EVR26, Note 55, Lemma 6; Note 49, Lemma 1]. Let the
observation space be countably generated and `ρ a` an s-finite measure for every arm `a`. Some
sequence of experts determines `D*` at every model `θ`, admissible or not, whose laws of the arms
are dominated, `task.ν θ a ≪ ρ a` for every arm `a`, for every answer `i`. -/
theorem exists_isExpert_determinesDesignRate_of_absolutelyContinuous [Nonempty α] [Countable ℐ]
    [Nonempty ℐ] [MeasurableSpace.CountablyGenerated 𝓨] (ρ : α → Measure 𝓨)
    [∀ a, SFinite (ρ a)] :
    ∃ (j : ℕ → ℐ) (S : ℕ → α → ℕ) (g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ),
      (∀ e, task.IsExpert (j e) (S e) (g e)) ∧
        ∀ θ, (∀ a, task.ν θ a ≪ ρ a) → ∀ i, task.DeterminesDesignRate j S g θ i := by
  -- the block bets for the tables of each design `s` against the alternatives to each answer `i`
  have key (i : ℐ) (s : α → ℕ) := by
    have : SFinite (designLaw (fun a ↦ (ρ a).toFinite) s) := by
      rw [designLaw_def]
      infer_instance
    exact exists_iSup_integral_div_eq_bipolarRate
      (task.designLaw_univ_le_one_of_mem_image (task.alt i) s)
      (designLaw (fun a ↦ (ρ a).toFinite) s)
  choose len h hlen hhm hhb hhe hrate using key
  -- the bet `h i s l` on `len i s l` tables of `s`, as a function of one table of `len i s l • s`
  let G (i : ℐ) (s : α → ℕ) (l : ℕ) : ((Σ a, Fin ((len i s l • s) a)) → 𝓨) → ℝ :=
    fun y ↦ h i s l ((designBlockEquiv s (len i s l)).symm y)
  have hmp (θ : Θ) (i : ℐ) (s : α → ℕ) (l : ℕ) :=
    (measurePreserving_designBlockEquiv (fun a ↦ task.ν θ a) s (len i s l)).symm
      (designBlockEquiv s (len i s l))
  have hG (i : ℐ) (s : α → ℕ) (hs : s ≠ 0) (l : ℕ) : task.IsExpert i (len i s l • s) (G i s l) := by
    refine ⟨smul_ne_zero (Nat.one_le_iff_ne_zero.1 (hlen i s l)) hs,
      (hhm i s l).comp (MeasurableEquiv.measurable _), (hhb i s l).imp fun c hc y ↦ hc _,
      fun θ' hθ' ↦ ?_⟩
    refine ((hmp θ' i s l).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun x ↦ ENNReal.ofReal (Real.exp (h i s l x)))).trans_le ?_
    exact (hhe i s l).lintegral_le_one (pi_mem_sampleNull ⟨_, ⟨θ', hθ', rfl⟩, rfl⟩)
  -- the value of that expert at `θ` is the normalized mean of the bet, per observation of `s`
  have hvalue (θ : Θ) (i : ℐ) (s : α → ℕ) (l : ℕ) : task.expertValue (len i s l • s) (G i s l) θ =
      (∫ x, h i s l x ∂Measure.pi fun _ : Fin (len i s l) ↦ designLaw (fun a ↦ task.ν θ a) s) /
        len i s l / (∑ a, s a : ℕ) := by
    rw [expertValue_def, (hmp θ i s l).integral_comp' (h i s l), div_div]
    simp [Finset.mul_sum]
  obtain ⟨j, S, g, hg, hrange⟩ := exists_isExpert_range_eq_insert (Classical.arbitrary ℐ)
    (fun k : ℐ × {s : α → ℕ // s ≠ 0} × ℕ ↦ hG k.1 k.2.1.val k.2.1.property k.2.2)
  refine ⟨j, S, g, hg, fun θ hθ i ↦ (task.determinesDesignRate_iff_forall_lt hg).2 fun t ht ↦ ?_⟩
  -- a design `s ≠ 0` whose tables have a bipolar rate above `t |s|`
  obtain ⟨s, hs, hts⟩ := exists_ne_zero_mul_lt_bipolarRate_of_lt_designRate _
    (task.isProbabilityMeasure_of_mem_image _) ht
  -- the laws of the tables at `θ` are dominated, so the block bets reach the bipolar rate
  have hac : designLaw (fun a ↦ task.ν θ a) s ≪ designLaw (fun a ↦ (ρ a).toFinite) s := by
    rw [designLaw_def, designLaw_def]
    exact Measure.AbsolutelyContinuous.pi fun p ↦ (hθ p.1).trans (absolutelyContinuous_toFinite _)
  rw [← hrate i s _ hac] at hts
  obtain ⟨l, hl⟩ := lt_iSup_iff.1 hts
  rw [EReal.coe_lt_coe_iff] at hl
  obtain ⟨e, hje, he⟩ :=
    exists_eq_expertValue_of_range_eq_insert hrange ((i, ⟨s, hs⟩, l) : ℐ × _ × ℕ)
  refine ⟨e, hje, ?_⟩
  have hN : (0 : ℝ) < ∑ a, s a := by exact_mod_cast Fintype.sum_pos (pos_iff_ne_zero.2 hs)
  rw [he, hvalue, lt_div_iff₀ (by exact_mod_cast hN), mul_comm]
  exact_mod_cast hl

end LMLExplore.Identification.IdentTask
