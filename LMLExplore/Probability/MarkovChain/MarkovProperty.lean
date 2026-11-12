/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Kernel.Operator
public import Mathlib.Probability.HasCondDistrib
public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# The one-step Markov property for bounded measurable functions

Let `X` be the coordinate process on path space `ℕ → α` under the law `markovChainLaw ν κ` of the
homogeneous Markov chain with initial law `ν` and transition kernel `κ`, with its natural filtration
`MeasureTheory.Filtration.piLE`. This file states the Markov property in terms of the action
`κ.integralCLM` of `κ` on bounded measurable functions.

## Main statements

* `ProbabilityTheory.Kernel.integral_eval_markovChainKernel`: started from `x`, the mean of
  `g (X n)` is `κ ^ n g x`.
* `ProbabilityTheory.Kernel.markovChainKernel_map_prodMk_eval_zero`: started from `x`, the chain
  is at `x` at time `0`, in the form of a joint law: the pair `(X 0, X)` has law
  `(Kernel.id ×ₖ κ.markovChainKernel) x`. Unlike an almost sure equality `X 0 = x`, this needs no
  measurable singletons.
* `ProbabilityTheory.Kernel.markovChainKernel_map_shift`: started from `x`, the path shifted by one
  step is the chain started from the law `κ x`.
* `MeasureTheory.Measure.hasCondDistrib_eval_succ_markovChainLaw`: given `X 0, …, X n`, the next
  state `X (n + 1)` has conditional law `κ (X n)`.
* `MeasureTheory.Measure.condExp_eval_succ_markovChainLaw`: the Markov property in the form
  `E[g (X (n + 1)) | X 0, …, X n] = ∫ g dκ (X n)`.
-/

public section

open MeasureTheory LMLExplore TauCeti.Probability
open scoped ENNReal lp

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]

/-- Started from `x`, the chain is at time `n` distributed as `(κ ^ n) x`
(`ProbabilityTheory.Kernel.markovChainKernel_map_eval`), so that the mean of `g` at time `n` is
the action of `κ ^ n` on `g` at `x`. -/
theorem integral_eval_markovChainKernel (g : boundedMeasurable α) (n : ℕ) (x : α) :
    ∫ y, (g : ℓ^∞(α, ℝ)) (y n) ∂κ.markovChainKernel x =
      ((κ ^ n).integralCLM g : ℓ^∞(α, ℝ)) x := by
  rw [integralCLM_apply, ← markovChainKernel_map_eval, Kernel.map_apply _ (measurable_pi_apply n),
    integral_map (measurable_pi_apply n).aemeasurable
      (boundedMeasurable.measurable g).aestronglyMeasurable]

/-- Started from `x`, the chain is at `x` at time `0`: the pair `(X 0, X)` has the law of `(x, X)`.
This is the joint-law form of `X 0 = x` almost surely, which would need measurable singletons. It
is the Markov property `Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd` at time `0`
from a Dirac initial law. -/
theorem markovChainKernel_map_prodMk_eval_zero :
    κ.markovChainKernel.map (fun z ↦ (z 0, z)) = Kernel.id ×ₖ κ.markovChainKernel := by
  ext x : 1
  have h := Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd (Measure.dirac x) κ 0
  simp only [Function.iterate_zero, id_eq] at h
  have hpre : (markovChainLaw (Measure.dirac x) κ).map (fun z (i : Fin 1) ↦ z i.1) =
      Measure.dirac (fun _ ↦ x) := by
    have hc : (fun (z : ℕ → α) (i : Fin 1) ↦ z i.1) = (fun a _ ↦ a) ∘ fun z ↦ z 0 := by
      funext z i
      rw [Fin.fin_one_eq_zero i]
      rfl
    have hm : Measurable fun (a : α) (_ : Fin 1) ↦ a := Measurable.of_eval fun _ ↦ measurable_id
    rw [hc, ← Measure.map_map hm (measurable_pi_apply 0), markovChainLaw_map_eval_zero,
      Measure.map_dirac' hm]
  rw [hpre, Measure.compProd_eq_comp_prod, Measure.dirac_bind (Kernel.measurable _),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, Kernel.comap_apply,
    markovChainKernel_apply] at h
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    markovChainKernel_apply]
  have h2 := congrArg (Measure.map fun p : (Fin 1 → α) × (ℕ → α) ↦ (p.1 0, p.2)) h
  rwa [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    at h2

/-- Started from `x`, the path shifted by one step is the chain started from the law `κ x`
(`Measure.markovChainLaw_map_shift_iterate` at `n = 1`, from a Dirac initial law). -/
theorem markovChainKernel_map_shift :
    κ.markovChainKernel.map (shift α) = κ.markovChainKernel ∘ₖ κ := by
  ext x : 1
  rw [Kernel.map_apply _ measurable_shift, markovChainKernel_apply,
    ← Function.iterate_one (shift α), Measure.markovChainLaw_map_shift_iterate, pow_one,
    Measure.dirac_bind (Kernel.measurable _), Kernel.comp_apply, Measure.markovChainLaw_eq_comp]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open ProbabilityTheory Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  {ν : Measure α} [IsProbabilityMeasure ν]

/-- The next state of the chain has conditional law `κ` from the last state, given the prefix of
the path: the conditional-distribution form of
`TauCeti.Probability.markovChainLaw_map_prefix_succ_eq_compProd`. -/
theorem hasCondDistrib_eval_succ_markovChainLaw (n : ℕ) :
    HasCondDistrib (fun ω : ℕ → α ↦ ω (n + 1)) (fun ω (i : Fin (n + 1)) ↦ ω i)
      (κ.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _))
      (markovChainLaw ν κ) where
  aemeasurable := by fun_prop
  map_eq := markovChainLaw_map_prefix_succ_eq_compProd ν κ n

/-- **The Markov property** in the one-step form: given the history `X 0, …, X n`, the conditional
expectation of `g (X (n + 1))` is `∫ g dκ (X n)`, for bounded measurable `g`. -/
theorem condExp_eval_succ_markovChainLaw (g : boundedMeasurable α) (n : ℕ) :
    (markovChainLaw ν κ)[fun ω ↦ (g : ℓ^∞(α, ℝ)) (ω (n + 1)) | Filtration.piLE n]
      =ᵐ[markovChainLaw ν κ] fun ω ↦ (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω n) := by
  -- the Markov property at time `n` for the function `y ↦ g (y 1)` of the future path
  have hint : Integrable (fun y : ℕ → α ↦ (g : ℓ^∞(α, ℝ)) (y 1))
      (markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ) :=
    (boundedMeasurable.integrable g _).comp_measurable (measurable_pi_apply 1)
  have h := condExp_shift_iterate_markovChainLaw ν κ n hint
  simp only [shift_iterate_apply, add_comm 1 n] at h
  refine h.trans (.of_forall fun ω ↦ ?_)
  simpa [Kernel.markovChainKernel_apply] using integral_eval_markovChainKernel (κ := κ) g 1 (ω n)

end MeasureTheory.Measure
