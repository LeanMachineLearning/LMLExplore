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
factors, it follows by induction on the number of coordinates.

## Main statements

* `InformationTheory.klDiv_fst_add_klDiv_snd_le`: the relative entropy to a product law is at
  least the sum of the relative entropies of the two marginals.
* `InformationTheory.sum_klDiv_map_eval_le`: the relative entropy from a law on `Fin n → 𝓧` to a
  product law `Measure.pi P` is at least the sum of the relative entropies of its marginals to the
  factors `P j`.
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
  have h := maxUtility_fst_add_maxUtility_snd_le R (S := {P}) (T := {P'})
    (fun μ hμ ↦ by rw [Set.mem_singleton_iff.1 hμ]; infer_instance)
    (fun μ hμ ↦ by rw [Set.mem_singleton_iff.1 hμ]; infer_instance)
  rwa [Set.image2_singleton, maxUtility_singleton_eq_klDiv, maxUtility_singleton_eq_klDiv,
    maxUtility_singleton_eq_klDiv, ← EReal.coe_ennreal_add,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h

/-- The relative entropy from a law on `Fin n → 𝓧` to a product law `Measure.pi P` is at least the
sum of the relative entropies of its marginals to the factors `P j`. -/
lemma sum_klDiv_map_eval_le {n : ℕ} (P : Fin n → Measure 𝓧) [∀ j, IsProbabilityMeasure (P j)]
    (μ : Measure (Fin n → 𝓧)) [IsProbabilityMeasure μ] :
    ∑ j, klDiv (μ.map fun x ↦ x j) (P j) ≤ klDiv μ (Measure.pi P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ 𝓧) 0
    set R := μ.map e
    -- `e` splits off the first coordinate and carries `Measure.pi P` to a product law
    have hpi : (Measure.pi P).map e = (P 0).prod (Measure.pi fun j : Fin n ↦ P j.succ) := by
      rw [(measurePreserving_piFinSuccAbove P 0).map_eq]
      simp
    have hKL : klDiv R ((P 0).prod (Measure.pi fun j : Fin n ↦ P j.succ)) =
        klDiv μ (Measure.pi P) := by
      rw [← hpi]
      exact klDiv_map_measurableEmbedding _ _ e.measurableEmbedding
    have hfst : R.fst = μ.map fun x ↦ x 0 := by
      have h : Prod.fst ∘ e = fun x ↦ x 0 := by
        ext x
        simp [e, MeasurableEquiv.piFinSuccAbove_apply]
      rw [Measure.fst, Measure.map_map measurable_fst e.measurable, h]
    have hsnd : R.snd = μ.map fun x j ↦ x j.succ := by
      have h : Prod.snd ∘ e = fun x j ↦ x j.succ := by
        ext x j
        simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      rw [Measure.snd, Measure.map_map measurable_snd e.measurable, h]
    have hmarg (j : Fin n) : R.snd.map (fun x ↦ x j) = μ.map fun x ↦ x j.succ := by
      rw [hsnd, Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def]
    calc ∑ j, klDiv (μ.map fun x ↦ x j) (P j)
    _ = klDiv R.fst (P 0) + ∑ j : Fin n, klDiv (R.snd.map fun x ↦ x j) (P j.succ) := by
      rw [Fin.sum_univ_succ, hfst]
      simp_rw [hmarg]
    _ ≤ klDiv R.fst (P 0) + klDiv R.snd (Measure.pi fun j : Fin n ↦ P j.succ) := by
      gcongr
      exact ih _ R.snd
    _ ≤ klDiv R ((P 0).prod (Measure.pi fun j : Fin n ↦ P j.succ)) :=
      klDiv_fst_add_klDiv_snd_le R _ _
    _ = klDiv μ (Measure.pi P) := hKL

end InformationTheory
