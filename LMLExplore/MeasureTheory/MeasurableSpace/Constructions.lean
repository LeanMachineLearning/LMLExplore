/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of evaluations, initial segments of tuples and finite dependence

## Main statements

* `MeasureTheory.measurable_div_apply`: for a finite type `α` with measurable singletons and
  `c : α → G`, the function `(p, b) ↦ c b / p b` on `(α → G) × α` is measurable.
* `MeasureTheory.measurable_eval_apply`: for a countable type `α` with measurable singletons,
  evaluating row `i` of a table `x : ι → α → β` at `a : α` is measurable in the pair `(x, a)`.
* `MeasureTheory.measurable_finInit`: the map `Fin.init` dropping the last entry of a tuple of
  length `n + 1` is measurable.
* `DependsOn.measurable_of_countable`: a function of a family of countable variables with
  measurable singletons that only depends on finitely many of them is measurable.
-/

public section

namespace MeasureTheory

variable {α G : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α] [Div G]
  [MeasurableSpace G] [MeasurableDiv G]

/-- For a finite type `α` with measurable singletons and `c : α → G`, the function
`(p, b) ↦ c b / p b` on `(α → G) × α` is measurable. Evaluated at the weights and the action of a
round of a bandit algorithm, it is an inverse-weighted function of the action. -/
lemma measurable_div_apply (c : α → G) :
    Measurable fun z : (α → G) × α ↦ c z.2 / z.1 z.2 :=
  measurable_from_prod_countable_left fun b ↦
    (measurable_const_div (c b)).comp (measurable_pi_apply b)

omit [Finite α] in
/-- For a countable type `α` with measurable singletons, evaluating row `i` of a table
`x : ι → α → β` at `a : α` is a measurable function of the pair `(x, a)`. In the table model of a
stochastic bandit, it reads the reward of the action of round `i` from row `i` of the table. -/
lemma measurable_eval_apply [Countable α] {ι β : Type*} [MeasurableSpace β] (i : ι) :
    Measurable fun p : (ι → α → β) × α ↦ p.1 i p.2 :=
  measurable_from_prod_countable_left fun a ↦ (measurable_pi_apply a).comp (measurable_pi_apply i)

/-- The map `Fin.init` dropping the last entry of a tuple of length `n + 1` is measurable. On the
histories of a sequential learning problem, it maps the history of the first `n + 1` rounds to
that of the first `n` rounds. -/
@[fun_prop]
lemma measurable_finInit {n : ℕ} {β : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (β i)] :
    Measurable (Fin.init : ((i : Fin (n + 1)) → β i) → (i : Fin n) → β i.castSucc) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- A function of a family of countable variables with measurable singletons that only depends on
finitely many of them is measurable: it factors through the restriction to these variables, whose
domain is countable. For example, a statistic of the first `N` rows of an array of samples with
finitely many keys and countably many values is a measurable function of the array. -/
lemma _root_.DependsOn.measurable_of_countable {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, Countable (X i)] [∀ i, MeasurableSingletonClass (X i)]
    {γ : Type*} [MeasurableSpace γ] {f : (Π i, X i) → γ} {s : Set ι} (hs : s.Finite)
    (hf : DependsOn f s) : Measurable f := by
  rcases isEmpty_or_nonempty (Π i, X i) with h | ⟨⟨x⟩⟩
  · exact Subsingleton.measurable
  have : Nonempty γ := ⟨f x⟩
  have : Finite s := hs.to_subtype
  obtain ⟨g, rfl⟩ := dependsOn_iff_exists_comp.1 hf
  exact (_root_.measurable_of_countable g).comp (Measurable.of_eval fun i ↦ measurable_pi_apply _)

end MeasureTheory
