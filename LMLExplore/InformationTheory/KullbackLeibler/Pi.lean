/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.EValues.Product
public import Statlib.EValues.RIPr
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Superadditivity of the relative entropy over the marginals of a product

The relative entropy from a law to a product law is at least the sum of the relative entropies of
its marginals to the factors. For two factors, this is the value of Statlib's
`maxUtility_fst_add_maxUtility_snd_le` for singleton nulls, where the maximal expected logarithm
of an e-variable is the relative entropy (`maxUtility_singleton_eq_klDiv`); for finitely many
factors, it follows by induction on the number of coordinates, after enumerating them.

## Main statements

* `InformationTheory.klDiv_fst_add_klDiv_snd_le`: the relative entropy to a product law is at
  least the sum of the relative entropies of the two marginals.
* `InformationTheory.sum_klDiv_map_eval_le`: the relative entropy from a law on a finite product
  `∀ i, 𝓧 i` to a product law `Measure.pi P` is at least the sum of the relative entropies of its
  marginals to the factors `P i`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

/-- The relative entropy to a product law is at least the sum of the relative entropies of the
two marginals. -/
lemma klDiv_fst_add_klDiv_snd_le (R : Measure (𝓧 × 𝓨)) [IsProbabilityMeasure R] (P : Measure 𝓧)
    (P' : Measure 𝓨) [IsProbabilityMeasure P] [IsProbabilityMeasure P'] :
    klDiv R.fst P + klDiv R.snd P' ≤ klDiv R (P.prod P') := by
  have h := maxUtility_fst_add_maxUtility_snd_le R (S := {P}) (T := {P'}) (by simp) (by simp)
  rwa [Set.image2_singleton, maxUtility_singleton_eq_klDiv, maxUtility_singleton_eq_klDiv,
    maxUtility_singleton_eq_klDiv, ← EReal.coe_ennreal_add,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h

/-- The case of `Fin n` of `sum_klDiv_map_eval_le`, by induction on `n`. -/
private lemma sum_klDiv_map_eval_le_fin {n : ℕ} {𝓧 : Fin n → Type*} [∀ j, MeasurableSpace (𝓧 j)]
    (P : ∀ j, Measure (𝓧 j)) [∀ j, IsProbabilityMeasure (P j)] (μ : Measure (∀ j, 𝓧 j))
    [IsProbabilityMeasure μ] :
    ∑ j, klDiv (μ.map fun x ↦ x j) (P j) ≤ klDiv μ (Measure.pi P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove 𝓧 0
    set R := μ.map e
    set P' := Measure.pi fun j : Fin n ↦ P ((0 : Fin (n + 1)).succAbove j)
    -- `e` splits off the first coordinate and carries `Measure.pi P` to a product law
    have hKL : klDiv R ((P 0).prod P') = klDiv μ (Measure.pi P) := by
      rw [← (measurePreserving_piFinSuccAbove P 0).map_eq]
      exact klDiv_map_measurableEmbedding _ _ e.measurableEmbedding
    have hfst : R.fst = μ.map fun x ↦ x 0 := by
      -- the first component of `e x` is `x 0` by definition of `piFinSuccAbove`
      have h : Prod.fst ∘ e = fun x ↦ x 0 := rfl
      rw [Measure.fst, Measure.map_map measurable_fst e.measurable, h]
    have hmarg (j : Fin n) :
        R.snd.map (fun x ↦ x j) = μ.map fun x ↦ x ((0 : Fin (n + 1)).succAbove j) := by
      -- the second component of `e x` is `x ∘ succAbove 0` by definition of `piFinSuccAbove`
      have h : ((fun x ↦ x j) ∘ Prod.snd) ∘ e = fun x ↦ x ((0 : Fin (n + 1)).succAbove j) := rfl
      rw [Measure.snd, Measure.map_map (measurable_pi_apply j) measurable_snd,
        Measure.map_map ((measurable_pi_apply j).comp measurable_snd) e.measurable, h]
    calc ∑ j, klDiv (μ.map fun x ↦ x j) (P j)
    _ = klDiv R.fst (P 0) +
        ∑ j : Fin n, klDiv (R.snd.map fun x ↦ x j) (P ((0 : Fin (n + 1)).succAbove j)) := by
      rw [Fin.sum_univ_succAbove _ 0, hfst]
      simp_rw [hmarg]
    _ ≤ klDiv R.fst (P 0) + klDiv R.snd P' := by
      gcongr
      exact ih _ R.snd
    _ ≤ klDiv R ((P 0).prod P') := klDiv_fst_add_klDiv_snd_le R _ _
    _ = klDiv μ (Measure.pi P) := hKL

/-- The relative entropy from a law on a finite product `∀ i, 𝓧 i` to a product law
`Measure.pi P` is at least the sum of the relative entropies of its marginals to the factors
`P i`. -/
lemma sum_klDiv_map_eval_le {ι : Type*} [Fintype ι] {𝓧 : ι → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] (P : ∀ i, Measure (𝓧 i)) [∀ i, IsProbabilityMeasure (P i)]
    (μ : Measure (∀ i, 𝓧 i)) [IsProbabilityMeasure μ] :
    ∑ i, klDiv (μ.map fun x ↦ x i) (P i) ≤ klDiv μ (Measure.pi P) := by
  -- transport to `Fin n` along an enumeration of `ι`
  set e := (Fintype.equivFin ι).symm
  set ψ := MeasurableEquiv.piCongrLeft 𝓧 e
  set ν := μ.map ψ.symm
  have hν : ν.map ψ = μ := by
    rw [Measure.map_map ψ.measurable ψ.symm.measurable, ψ.self_comp_symm, Measure.map_id]
  have hKL : klDiv ν (Measure.pi fun a ↦ P (e a)) = klDiv μ (Measure.pi P) := by
    rw [← (measurePreserving_piCongrLeft P e).map_eq, ← klDiv_map_measurableEmbedding _ _
      ψ.measurableEmbedding, hν]
  have hmarg (a : Fin (Fintype.card ι)) : ν.map (fun x ↦ x a) = μ.map fun x ↦ x (e a) := by
    -- `ψ.symm x a = x (e a)` by definition of `piCongrLeft`
    have h : (fun x ↦ x a) ∘ ψ.symm = fun x ↦ x (e a) := rfl
    rw [Measure.map_map (measurable_pi_apply a) ψ.symm.measurable, h]
  calc ∑ i, klDiv (μ.map fun x ↦ x i) (P i)
  _ = ∑ a, klDiv (ν.map fun x ↦ x a) (P (e a)) := by
    rw [← e.sum_comp]
    simp_rw [hmarg]
  _ ≤ klDiv ν (Measure.pi fun a ↦ P (e a)) := sum_klDiv_map_eval_le_fin _ ν
  _ = klDiv μ (Measure.pi P) := hKL

end InformationTheory
