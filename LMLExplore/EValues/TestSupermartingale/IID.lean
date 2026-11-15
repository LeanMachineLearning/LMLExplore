/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess
public import LMLExplore.EValues.TestSupermartingale
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Probability.ProductMeasure

/-!
# Products of i.i.d. copies of an e-variable

Let `e` be an e-variable for a null `S` of probability measures on `𝓧`. Evaluated along a
sequence `ω : ℕ → 𝓧`, the products `∏ i ≤ n, e (ω i)` of copies of `e` form a test
supermartingale, hence an e-process, for the i.i.d. null `{P ^ ℕ | P ∈ S}` and the filtration
`Filtration.piLE`, whose time `n` has seen the observations `ω 0, …, ω n`. This is the i.i.d.
instance of the wealth processes `ProbabilityTheory.isTestSupermartingale_mul_prod`: under
`P ^ ℕ`, the factor `e (ω (n + 1))` is independent of the past and has expectation at most `1`.

## Main statements

* `ProbabilityTheory.IsEVar.isTestSupermartingale_prod_piLE`: the products of copies of an
  e-variable form a test supermartingale for the i.i.d. null.
* `ProbabilityTheory.IsEVar.isEProcess_prod_piLE`: they form an e-process for the i.i.d. null.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S : Set (Measure 𝓧)} {e : 𝓧 → ℝ≥0∞}

/-- **Products of copies of an e-variable form a test supermartingale.** If `e` is an e-variable
for a null `S` of probability measures, the products `∏ i ≤ n, e (ω i)` form a test
supermartingale for the i.i.d. null `{P ^ ℕ | P ∈ S}` and `Filtration.piLE`. -/
theorem IsEVar.isTestSupermartingale_prod_piLE (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (he : IsEVar e S) :
    IsTestSupermartingale (fun n ω ↦ ∏ i : Fin (n + 1), e (ω i))
      (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S) := by
  set T := (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S
  have h0 : ∀ P ∈ T, ∫⁻ ω, e (ω 0) ∂P ≤ 1 := by
    rintro _ ⟨P, hP, rfl⟩
    have := hS P hP
    rw [(measurePreserving_eval_infinitePi (fun _ ↦ P) 0).lintegral_comp he.measurable]
    exact he.lintegral_le_one hP
  have hF : ∀ k, IsCondEVar (fun ω : ℕ → 𝓧 ↦ e (ω (k + 1))) (Filtration.piLE k) T := by
    refine fun k ↦ ⟨he.measurable.comp (measurable_pi_apply _), ?_⟩
    rintro _ ⟨P, hP, rfl⟩ s hs
    have := hS P hP
    rw [setLIntegral_comp_eval_succ P he.measurable k hs]
    exact mul_le_of_le_one_right' (he.lintegral_le_one hP)
  have hM := isTestSupermartingale_mul_prod (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
    (he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) h0
    (fun k ↦ he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) hF
  convert hM using 3 with n ω
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ e (ω i)), Finset.prod_range_succ', mul_comm]
  simp only [Function.comp_apply]

/-- **Products of copies of an e-variable form an e-process.** If `e` is an e-variable for a null
`S` of probability measures, the products `∏ i ≤ n, e (ω i)` form an e-process for the i.i.d.
null `{P ^ ℕ | P ∈ S}` and `Filtration.piLE`. -/
theorem IsEVar.isEProcess_prod_piLE (hS : ∀ P ∈ S, IsProbabilityMeasure P) (he : IsEVar e S) :
    IsEProcess (fun n ω ↦ ∏ i : Fin (n + 1), e (ω i))
      (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S) :=
  (he.isTestSupermartingale_prod_piLE hS).isEProcess <| by
    rintro _ ⟨P, hP, rfl⟩
    have := hS P hP
    infer_instance

end ProbabilityTheory
