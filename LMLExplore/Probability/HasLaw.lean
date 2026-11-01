/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# Functions of random variables with a given law

For a random variable `Y` with law `ν` and a function `T` that is almost everywhere measurable for
`ν`, the random variable `T (Y)` has the law of `T` under `ν`. Applied to a family of independent
random variables with law `ν`, the variables `T (X i)` are independent.

## Main statements

* `ProbabilityTheory.HasLaw.identDistrib_comp`: if `Y` has law `ν`, then `T (Y)` under `P` and `T`
  under `ν` are identically distributed.
* `ProbabilityTheory.iIndepFun.comp_subtype_of_hasLaw`: for independent random variables `X i` with
  law `ν` for `i ∈ s`, the variables `T (X i)`, `i ∈ s`, are independent.
-/

public section

namespace ProbabilityTheory

open MeasureTheory

variable {Ω ι 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {ν : Measure 𝓧} {T : 𝓧 → 𝓨} {Y : Ω → 𝓧}
  {X : ι → Ω → 𝓧} {s : Finset ι}

/-- For a random variable `Y` with law `ν` and a function `T` almost everywhere measurable for `ν`,
the random variable `T (Y)` under `P` has the law of `T` under `ν`. -/
lemma HasLaw.identDistrib_comp (hT : AEMeasurable T ν) (hY : HasLaw Y ν P) :
    IdentDistrib (fun ω ↦ T (Y ω)) T P ν :=
  ((hasLaw_map hT).fun_comp hY).identDistrib (hasLaw_map hT)

/-- For random variables `X i` with law `ν` for `i ∈ s`, independent as a family, and a function
`T` almost everywhere measurable for `ν`, the variables `T (X i)`, `i ∈ s`, are independent. -/
lemma iIndepFun.comp_subtype_of_hasLaw (h_indep : iIndepFun X P) (hT : AEMeasurable T ν)
    (hX : ∀ i ∈ s, HasLaw (X i) ν P) :
    iIndepFun (fun i : s ↦ fun ω ↦ T (X i ω)) P :=
  (h_indep.precomp Subtype.val_injective).comp₀ (fun _ ↦ T) (fun i ↦ (hX i i.2).aemeasurable)
    fun i ↦ (hX i i.2).map_eq ▸ hT

end ProbabilityTheory
