/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.Expert.Basic
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.EVariable

/-!
# Experts that determine `D*` at countably many models

For an identification task, write `D*(θ, ¬i)` for the rate of the designs of the laws of the arms
at the model `θ` against the laws of the arms at the alternatives to the answer `i`. For every
countable set of pairs `(θ, i)` of a model and an answer, some sequence of experts determines `D*`
at `θ` for `i` for every pair of the set
(`LMLExplore.Identification.IdentTask.DeterminesDesignRate`), with no condition on the observation
space and no domination [EVR26, Note 55, Section 2]. `D*` is
the supremum over the designs `n` of the value of `n` per observation, and in the value of each
design bounded e-variables suffice: if `q` is below the value of the design `n ≠ 0` at `θ` against
the alternatives to `i`, some expert `(i, n, g)` has `q < ∫ g dθ^(n)`, the truncated logarithm of
the mixture of an e-variable with the constant `1`
(`ProbabilityTheory.IsEVar.exists_bounded_lt_integral_of_lt_eintegral_log`). Taking one such
expert for each pair, each design and each rational `q` gives countably many experts, a sequence
of experts by `LMLExplore.Identification.IdentTask.exists_isExpert_range_eq_insert`.

## Main statements

* `LMLExplore.Identification.IdentTask.exists_isExpert_lt_integral_of_lt_designValue`: bounded
  e-variables suffice in the value of a design.
* `LMLExplore.Identification.IdentTask.exists_isExpert_determinesDesignRate_of_countable`: one
  sequence of experts determines `D*` at the pairs of a countable set.
* `LMLExplore.Identification.IdentTask.exists_isExpert_determinesDesignRate`: one sequence of
  experts determines `D*` at one model for one answer.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/DesignExpertsExist.lean`
(commit `cb8238f`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 55, *Classes that are not dominated: attaining the rate and `D*`
  with one procedure*, Section 2, "For a single instance, and for countable sets".
-/

public section

open MeasureTheory ProbabilityTheory

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨)

/-- **Bounded e-variables suffice in the value of a design** [EVR26, Note 55, Section 2]. If `q`
is below the value of a design `n ≠ 0` at the model `θ` against the alternatives to the answer
`i`, some expert `(i, n, g)` has mean `∫ g dθ^(n)` above `q`. -/
theorem exists_isExpert_lt_integral_of_lt_designValue {θ : Θ} {i : ℐ} {n : α → ℕ} (hn : n ≠ 0)
    {q : ℝ} (hq : (q : EReal) <
      designValue (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) n) :
    ∃ g, task.IsExpert i n g ∧ q < ∫ y, g y ∂designLaw (fun a ↦ task.ν θ a) n := by
  rw [designValue_def, lt_maxEPower_iff] at hq
  obtain ⟨X, hX, hqX⟩ := hq
  have hS : ∀ P ∈ (fun ν ↦ designLaw ν n) '' ((fun θ' a ↦ task.ν θ' a) '' task.alt i),
      P Set.univ ≤ 1 := by
    rintro _ ⟨_, ⟨θ', -, rfl⟩, rfl⟩
    exact prob_le_one
  obtain ⟨N, f, hfm, hfN, hfS, hfq⟩ := hX.exists_bounded_lt_integral_of_lt_eintegral_log _ hS hqX
  exact ⟨f, ⟨hn, hfm, ⟨N, hfN⟩, fun θ' hθ' ↦ hfS _ ⟨_, ⟨θ', hθ', rfl⟩, rfl⟩⟩, hfq⟩

/-- **Experts for countably many models** [EVR26, Note 55, Section 2]. For every countable set `T`
of pairs of a model and an answer, some sequence of experts determines `D*` at `θ` for `i` for
every `(θ, i) ∈ T`. The observation space is any measurable space, and the laws of the arms need
not be dominated. -/
theorem exists_isExpert_determinesDesignRate_of_countable [Nonempty α] [Nonempty ℐ]
    {T : Set (Θ × ℐ)} (hT : T.Countable) :
    ∃ (j : ℕ → ℐ) (S : ℕ → α → ℕ) (g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ),
      (∀ e, task.IsExpert (j e) (S e) (g e)) ∧
        ∀ p ∈ T, task.DeterminesDesignRate j S g p.1 p.2 := by
  have : Countable T := hT.to_subtype
  -- for each pair, each design `n ≠ 0` and each rational `q` below its value, an expert above `q`
  have key (p : Θ × ℐ) (n : α → ℕ) (hn : n ≠ 0) (q : ℚ) : ∃ f, task.IsExpert p.2 n f ∧
      (((q : ℝ) : EReal) <
          designValue (fun a ↦ task.ν p.1 a) ((fun θ' a ↦ task.ν θ' a) '' task.alt p.2) n →
        (q : ℝ) < ∫ y, f y ∂designLaw (fun a ↦ task.ν p.1 a) n) := by
    by_cases hq : ((q : ℝ) : EReal) <
      designValue (fun a ↦ task.ν p.1 a) ((fun θ' a ↦ task.ν θ' a) '' task.alt p.2) n
    · obtain ⟨f, hf, hfq⟩ := task.exists_isExpert_lt_integral_of_lt_designValue hn hq
      exact ⟨f, hf, fun _ ↦ hfq⟩
    · exact ⟨0, task.isExpert_zero _ hn, fun h ↦ absurd h hq⟩
  choose G hG hGq using key
  obtain ⟨j, S, g, hg, hrange⟩ := exists_isExpert_range_eq_insert (Classical.arbitrary ℐ)
    (fun k : T × {n : α → ℕ // n ≠ 0} × ℚ ↦ hG k.1.val k.2.1.val k.2.1.property k.2.2)
  refine ⟨j, S, g, hg, fun p hp ↦ (task.determinesDesignRate_iff_forall_lt hg).2 fun t ht ↦ ?_⟩
  -- a design `n ≠ 0` whose value exceeds `t |n|`
  obtain ⟨n, hn, htn⟩ : ∃ n : α → ℕ, n ≠ 0 ∧ (((∑ a, n a : ℕ) * t : ℝ) : EReal) <
      designValue (fun a ↦ task.ν p.1 a) ((fun θ' a ↦ task.ν θ' a) '' task.alt p.2) n := by
    have hΛ : ∀ ν ∈ (fun θ' a ↦ task.ν θ' a) '' task.alt p.2, ∀ a, ν a Set.univ ≤ 1 := by
      rintro _ ⟨θ', -, rfl⟩ a
      exact prob_le_one
    rw [designRate_def] at ht
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 ht
    rcases eq_or_ne n 0 with rfl | hn0
    · have h1 : (0 : ℝ) < ((∑ a, (1 : α → ℕ) a : ℕ) : ℝ) := by
        exact_mod_cast Fintype.sum_pos (pos_iff_ne_zero.2 (one_ne_zero : (1 : α → ℕ) ≠ 0))
      refine ⟨1, one_ne_zero, lt_of_lt_of_le ?_ (designValue_nonneg _ hΛ 1)⟩
      simp only [Pi.zero_apply, Finset.sum_const_zero, Nat.cast_zero, EReal.div_zero] at hn
      exact EReal.coe_neg'.2 (mul_neg_of_pos_of_neg h1 (EReal.coe_neg'.1 hn))
    · exact ⟨n, hn0, (EReal.coe_lt_div_natCast_iff
        (Fintype.sum_pos (pos_iff_ne_zero.2 hn0))).1 hn⟩
  have hN : (0 : ℝ) < ∑ a, n a := by exact_mod_cast Fintype.sum_pos (pos_iff_ne_zero.2 hn)
  obtain ⟨q, htq, hq⟩ := EReal.lt_iff_exists_rat_btwn.1 htn
  obtain ⟨e, he⟩ : (p.2, task.expertValue n (G p n hn q)) ∈
      Set.range (fun e ↦ (j e, task.expertValue (S e) (g e))) :=
    hrange ▸ Set.mem_insert_of_mem _ ⟨(⟨p, hp⟩, ⟨n, hn⟩, q), rfl⟩
  simp only [Prod.mk.injEq] at he
  refine ⟨e, he.1, ?_⟩
  rw [he.2, expertValue_def, lt_div_iff₀ (by exact_mod_cast hN), mul_comm]
  exact_mod_cast (EReal.coe_lt_coe_iff.1 htq).trans (hGq _ _ _ _ hq)

/-- **Experts for one model** [EVR26, Note 55, Section 2]. For every model `θ` and every answer
`i`, some sequence of experts determines `D*` at `θ` for `i`. The observation space is any
measurable space. -/
theorem exists_isExpert_determinesDesignRate [Nonempty α] (θ : Θ) (i : ℐ) :
    ∃ (j : ℕ → ℐ) (S : ℕ → α → ℕ) (g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ),
      (∀ e, task.IsExpert (j e) (S e) (g e)) ∧ task.DeterminesDesignRate j S g θ i := by
  have : Nonempty ℐ := ⟨i⟩
  obtain ⟨j, S, g, hg, h⟩ :=
    task.exists_isExpert_determinesDesignRate_of_countable (Set.countable_singleton (θ, i))
  exact ⟨j, S, g, hg, h _ rfl⟩

end LMLExplore.Identification.IdentTask
