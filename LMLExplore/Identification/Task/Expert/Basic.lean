/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
public import LMLExplore.Identification.Task.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Inv
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# Experts for an identification task

An identification task (`LMLExplore.Identification.IdentTask`) has finitely many arms `a : α`,
observations in a measurable space `𝓨`, models `θ` with laws `task.ν θ a` of the arms, and
correct answers. Write `D*(θ, ¬i)` for the rate of the designs `ProbabilityTheory.designRate` of
the laws of the arms at `θ` against the laws of the arms at the alternatives `task.alt i` to the
answer `i`. A *block* of shape `S : α → ℕ` is `S a` observations of each arm `a`, the table
`(Σ a, Fin (S a)) → 𝓨` of the design `S`, of law `θ^(S) = designLaw (fun a ↦ task.ν θ a) S`
under the model `θ`.

An *expert* for the answer `j` is a shape `S ≠ 0` and a bounded measurable function `g` of the
blocks of that shape such that `∫ exp g dλ^(S) ≤ 1` for every alternative `λ` to `j`: `exp g` is
an e-variable of one block against the alternatives to `j`. Its *value* at a model `θ` is
`∫ g dθ^(S) / |S|`, with `|S| = ∑ a, S a`, the expected logarithm of that e-variable per
observation. It is at most `D*(θ, ¬j)` at every model `θ`, since `exp g` is one of the
e-variables in the value of the design `S`, and at most `0` at the alternatives to `j`. A sequence
of experts *determines `D*` at `θ` for the answer `i`* if the values at `θ` of its experts of the
answer `i` have supremum `D*(θ, ¬i)` [EVR26, Note 55, Definition 4]. An algorithm that runs the
experts of a sequence on fresh blocks and bets with the best of them attains `D*` at every
admissible model with a single correct answer at which the sequence determines `D*`
[EVR26, Note 55, Theorem 5]; that algorithm is not constructed in this file.

## Main definitions

* `LMLExplore.Identification.IdentTask.IsExpert task j S g`: `(j, S, g)` is an expert for the
  task `task`.
* `LMLExplore.Identification.IdentTask.expertValue task S g θ`: the value `∫ g dθ^(S) / |S|` of
  the function `g` of the blocks of shape `S` at the model `θ`.
* `LMLExplore.Identification.IdentTask.DeterminesDesignRate task j S g θ i`: the values at `θ` of
  the experts `(j e, S e, g e)` of the answer `i`, `e : ℕ`, have supremum `D*(θ, ¬i)`.

## Main statements

* `LMLExplore.Identification.IdentTask.IsExpert.expertValue_le_designRate`: the value of an expert
  of the answer `j` is at most `D*(θ, ¬j)` at every model `θ`.
* `LMLExplore.Identification.IdentTask.IsExpert.expertValue_nonpos`: the value of an expert of the
  answer `j` is at most `0` at the alternatives to `j`.
* `LMLExplore.Identification.IdentTask.determinesDesignRate_iff_forall_lt`: a sequence of experts
  determines `D*` at `θ` for `i` exactly when every real below `D*(θ, ¬i)` is below the value at
  `θ` of one of its experts of the answer `i`.
* `LMLExplore.Identification.IdentTask.exists_isExpert_range_eq_insert`: a countable family of
  experts, with a zero expert `(i₀, 1, 0)` added, is a sequence of experts with the same answers
  and values.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/DesignExperts.lean` and
`EValuesResearch/Results/DesignExpertsExist.lean` (commit `cb8238f`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. The value at the alternatives
to `j` is bounded through the entropy bound `ProbabilityTheory.designValue_le_sum_mul_klDiv` at
the model itself, a form of Jensen's inequality.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 55, *Classes that are not dominated: attaining the rate and `D*`
  with one procedure*, Definition 4 and Theorem 5.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨)

/-! ### Experts and their values -/

/-- An *expert* for the answer `j` [EVR26, Note 55, Definition 4]: a block shape `S ≠ 0` and a
bounded measurable function `g` of the tables of the design `S` such that
`∫ exp g dλ^(S) ≤ 1` for every alternative `λ` to `j`, where `λ^(S)` is the law
`designLaw (fun a ↦ task.ν λ a) S` of the table at `λ`. -/
structure IsExpert (j : ℐ) (S : α → ℕ) (g : ((Σ a, Fin (S a)) → 𝓨) → ℝ) : Prop where
  /-- The block shape is not zero. -/
  shape_ne_zero : S ≠ 0
  /-- The function is measurable. -/
  measurable : Measurable g
  /-- The function is bounded. -/
  bounded : ∃ c, ∀ y, |g y| ≤ c
  /-- The exponential of the function has mean at most `1` under the law of the table at every
  alternative to the answer. -/
  lintegral_exp_le_one : ∀ θ ∈ task.alt j,
    ∫⁻ y, ENNReal.ofReal (Real.exp (g y)) ∂designLaw (fun a ↦ task.ν θ a) S ≤ 1

/-- The value of the function `g` of the tables of the design `S` at the model `θ`: its mean under
the law of the table at `θ`, per observation, `∫ g dθ^(S) / |S|` with `|S| = ∑ a, S a`
[EVR26, Note 55, Definition 4]. -/
noncomputable def expertValue (S : α → ℕ) (g : ((Σ a, Fin (S a)) → 𝓨) → ℝ) (θ : Θ) : ℝ :=
  (∫ y, g y ∂designLaw (fun a ↦ task.ν θ a) S) / (∑ a, S a : ℕ)

/-- The value of `g` at `θ` is its mean under the law of the table at `θ` divided by `∑ a, S a`. -/
theorem expertValue_def (S : α → ℕ) (g : ((Σ a, Fin (S a)) → 𝓨) → ℝ) (θ : Θ) :
    task.expertValue S g θ = (∫ y, g y ∂designLaw (fun a ↦ task.ν θ a) S) / (∑ a, S a : ℕ) :=
  (rfl)

/-- The sequence of experts `(j e, S e, g e)`, `e : ℕ`, *determines `D*` at the model `θ` for the
answer `i`*: the values at `θ` of its experts of the answer `i` have supremum the rate of the
designs of the laws of the arms at `θ` against the laws of the arms at the alternatives to `i`
[EVR26, Note 55, Definition 4]. -/
structure DeterminesDesignRate (j : ℕ → ℐ) (S : ℕ → α → ℕ)
    (g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ) (θ : Θ) (i : ℐ) : Prop where
  /-- The values at `θ` of the experts of the answer `i` have supremum `D*`. -/
  iSup_eq : ⨆ (e : ℕ) (_ : j e = i), (task.expertValue (S e) (g e) θ : EReal) =
    designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i)

omit [Fintype α] in
/-- The laws of the arms at the models of a set `s` are probability measures. -/
theorem isProbabilityMeasure_of_mem_image (s : Set Θ) :
    ∀ ν ∈ (fun θ' a ↦ task.ν θ' a) '' s, ∀ a, IsProbabilityMeasure (ν a) := by
  rintro _ ⟨θ', -, rfl⟩ a
  infer_instance

/-- The laws of the tables of a design `n` at the models of a set `s` have mass at most `1`. -/
theorem designLaw_univ_le_one_of_mem_image (s : Set Θ) (n : α → ℕ) :
    ∀ P ∈ (fun ν ↦ designLaw ν n) '' ((fun θ' a ↦ task.ν θ' a) '' s), P Set.univ ≤ 1 := by
  rintro _ ⟨_, ⟨θ', -, rfl⟩, rfl⟩
  exact prob_le_one

variable {task} {θ : Θ} {i : ℐ}

section Expert

variable {j : ℐ} {S : α → ℕ} {g : ((Σ a, Fin (S a)) → 𝓨) → ℝ}

/-- The function of an expert is integrable under the law of the table at every model. -/
theorem IsExpert.integrable (hg : task.IsExpert j S g) (θ : Θ) :
    Integrable g (designLaw (fun a ↦ task.ν θ a) S) := by
  obtain ⟨c, hc⟩ := hg.bounded
  exact .of_bound hg.measurable.aestronglyMeasurable c
    (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hc y)

/-- The exponential of the function of an expert of the answer `j` is an e-variable of one table
for the laws of the table at the alternatives to `j`. -/
theorem IsExpert.isEVar (hg : task.IsExpert j S g) :
    IsEVar (fun y ↦ ENNReal.ofReal (Real.exp (g y)))
      ((fun ν ↦ designLaw ν S) '' ((fun θ' a ↦ task.ν θ' a) '' task.alt j)) := by
  refine ⟨ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg.measurable), ?_⟩
  rintro _ ⟨_, ⟨θ', hθ', rfl⟩, rfl⟩
  exact hg.lintegral_exp_le_one θ' hθ'

/-- The mean of the function of an expert of the answer `j` under the law of the table at `θ` is
at most the value of its design against the alternatives to `j`: the exponential of the function
is one of the e-variables in that value. -/
theorem IsExpert.integral_le_designValue (hg : task.IsExpert j S g) (θ : Θ) :
    ((∫ y, g y ∂designLaw (fun a ↦ task.ν θ a) S : ℝ) : EReal) ≤
      designValue (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt j) S := by
  rw [designValue_def, ← eintegral_eq_integral (hg.integrable θ)]
  simp_rw [← ENNReal.log_ofReal_exp (g _)]
  exact hg.isEVar.eintegral_log_le_maxEPower _

/-- **The value of an expert is at most `D*`** [EVR26, Note 55, Section 2]. At every model `θ`,
the value of an expert of the answer `j` is at most the rate of the designs of the laws of the arms
at `θ` against the laws of the arms at the alternatives to `j`. -/
theorem IsExpert.expertValue_le_designRate (hg : task.IsExpert j S g) (θ : Θ) :
    (task.expertValue S g θ : EReal) ≤
      designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt j) := by
  have hN : 0 < ∑ a, S a := Fintype.sum_pos (pos_iff_ne_zero.2 hg.shape_ne_zero)
  refine (EReal.coe_le_div_natCast_iff hN).2 ?_ |>.trans (designValue_div_le_designRate _ _ S)
  rw [expertValue_def, mul_div_cancel₀ _ (by positivity)]
  exact hg.integral_le_designValue θ

/-- **The value of an expert at an alternative is at most `0`** [EVR26, Note 55, Section 2]. At an
alternative `θ` to the answer `j`, the laws of the arms at `θ` are among the instances that the
expert bets against, so the mean of its function under the law of the table at `θ` is at most
`0`. -/
theorem IsExpert.expertValue_nonpos (hg : task.IsExpert j S g) (hθ : θ ∈ task.alt j) :
    task.expertValue S g θ ≤ 0 := by
  have h := (hg.integral_le_designValue θ).trans
    (designValue_le_sum_mul_klDiv (Set.mem_image_of_mem (fun θ' a ↦ task.ν θ' a) hθ) S)
  simp only [klDiv_self, mul_zero, Finset.sum_const_zero, EReal.coe_ennreal_zero] at h
  exact div_nonpos_of_nonpos_of_nonneg (EReal.coe_nonpos.1 h) (Nat.cast_nonneg _)

/-- The function `0` of the tables of a design `S ≠ 0` is an expert for every answer. With the
shape `1`, one observation of each arm, this is the *zero expert* `(j, 1, 0)`. -/
theorem isExpert_zero (task : IdentTask α Θ ℐ 𝓨) (j : ℐ) (hS : S ≠ 0) :
    task.IsExpert j S 0 where
  shape_ne_zero := hS
  measurable := measurable_const
  bounded := ⟨0, fun _ ↦ by simp⟩
  lintegral_exp_le_one θ _ := by simp

/-- The value of the function `0` is `0` at every model. -/
@[simp]
theorem expertValue_zero (task : IdentTask α Θ ℐ 𝓨) (S : α → ℕ) (θ : Θ) :
    task.expertValue S 0 θ = 0 := by
  simp [expertValue_def]

end Expert

/-! ### Sequences of experts that determine `D*` -/

section Sequence

variable {j : ℕ → ℐ} {S : ℕ → α → ℕ} {g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ}

/-- A sequence of experts determines `D*` at `θ` for the answer `i` exactly when every real below
`D*(θ, ¬i)` is below the value at `θ` of one of its experts of the answer `i`: the values are at
most `D*`. -/
theorem determinesDesignRate_iff_forall_lt (hg : ∀ e, task.IsExpert (j e) (S e) (g e)) :
    task.DeterminesDesignRate j S g θ i ↔ ∀ t : ℝ,
      (t : EReal) < designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) →
        ∃ e, j e = i ∧ t < task.expertValue (S e) (g e) θ := by
  refine ⟨fun h t ht ↦ ?_, fun h ↦ ⟨le_antisymm
    (iSup₂_le fun e he ↦ he ▸ (hg e).expertValue_le_designRate θ) ?_⟩⟩
  · rw [← h.iSup_eq] at ht
    obtain ⟨e, he⟩ := lt_iSup_iff.1 ht
    obtain ⟨hei, he⟩ := lt_iSup_iff.1 he
    exact ⟨e, hei, EReal.coe_lt_coe_iff.1 he⟩
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc not_top_lt
  | coe t =>
    obtain ⟨e, he, ht⟩ := h t hc
    exact (EReal.coe_le_coe_iff.2 ht.le).trans
      (le_iSup₂_of_le (f := fun e (_ : j e = i) ↦ (task.expertValue (S e) (g e) θ : EReal)) e he
        le_rfl)

/-- **A countable family of experts is a sequence of experts** [EVR26, Note 55, Section 2]. The
experts `(jj k, SS k, gg k)` of a countable family, possibly empty, together with the zero expert
`(i₀, 1, 0)`, are the experts of a sequence `(j e, S e, g e)`, `e : ℕ`: the pairs of the answer and
the values at every model of the experts of the sequence are those of the family and `(i₀, 0)`. -/
theorem exists_isExpert_range_eq_insert [Nonempty α] {ι : Type*} [Countable ι] (i₀ : ℐ)
    {jj : ι → ℐ} {SS : ι → α → ℕ} {gg : (k : ι) → ((Σ a, Fin (SS k a)) → 𝓨) → ℝ}
    (hgg : ∀ k, task.IsExpert (jj k) (SS k) (gg k)) :
    ∃ (j : ℕ → ℐ) (S : ℕ → α → ℕ) (g : (e : ℕ) → ((Σ a, Fin (S e a)) → 𝓨) → ℝ),
      (∀ e, task.IsExpert (j e) (S e) (g e)) ∧
        Set.range (fun e ↦ (j e, task.expertValue (S e) (g e))) =
          insert (i₀, 0) (Set.range fun k ↦ (jj k, task.expertValue (SS k) (gg k))) := by
  -- the family indexed by `Option ι`, with the zero expert at `none`
  let J : Option ι → ℐ := fun o ↦ o.elim i₀ jj
  let S' : Option ι → α → ℕ := fun o ↦ o.elim 1 SS
  let G : (o : Option ι) → ((Σ a, Fin (S' o a)) → 𝓨) → ℝ := fun o ↦
    match o with
    | none => 0
    | some k => gg k
  have hG (o : Option ι) : task.IsExpert (J o) (S' o) (G o) := by
    cases o with
    | none => exact isExpert_zero task i₀ one_ne_zero
    | some k => exact hgg k
  obtain ⟨φ, hφ⟩ := exists_surjective_nat (Option ι)
  refine ⟨fun e ↦ J (φ e), fun e ↦ S' (φ e), fun e ↦ G (φ e), fun e ↦ hG (φ e), ?_⟩
  have h := hφ.range_comp fun o ↦ (J o, task.expertValue (S' o) (G o))
  rw [Function.comp_def] at h
  rw [h, Option.range_eq]
  congr 2
  exact funext fun θ ↦ expertValue_zero task 1 θ

/-- In a sequence of experts whose answers and values are those of a family together with the zero
expert, as given by `exists_isExpert_range_eq_insert`, every expert `(jj k, SS k, gg k)` of the
family has the answer and the values of some expert of the sequence. -/
theorem exists_eq_expertValue_of_range_eq_insert {ι : Type*} {i₀ : ℐ} {jj : ι → ℐ}
    {SS : ι → α → ℕ} {gg : (k : ι) → ((Σ a, Fin (SS k a)) → 𝓨) → ℝ}
    (hrange : Set.range (fun e ↦ (j e, task.expertValue (S e) (g e))) =
      insert (i₀, 0) (Set.range fun k ↦ (jj k, task.expertValue (SS k) (gg k)))) (k : ι) :
    ∃ e, j e = jj k ∧ task.expertValue (S e) (g e) = task.expertValue (SS k) (gg k) := by
  obtain ⟨e, he⟩ : (jj k, task.expertValue (SS k) (gg k)) ∈
      Set.range (fun e ↦ (j e, task.expertValue (S e) (g e))) :=
    hrange ▸ Set.mem_insert_of_mem _ ⟨k, rfl⟩
  exact ⟨e, Prod.mk.inj he⟩

end Sequence

end LMLExplore.Identification.IdentTask
