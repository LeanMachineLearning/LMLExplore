/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.Probability.Distributions.Bernoulli

/-!
# Gaussian and Bernoulli bandits

A stochastic bandit with arms `α` is a Markov kernel `ν : Kernel α ℝ`: pulling arm `a` returns a
reward with law `ν a`, and the mean of arm `a` is `(ν a)[id]`. This file defines the two standard
instances [LS, Chapter 4]:

* `LMLExplore.Bandits.gaussianBandit μ σ2`: arm `a` has law `𝒩(μ a, σ2)`;
* `LMLExplore.Bandits.bernoulliBandit p`: arm `a` has law `Ber((1 : ℝ), 0, p a)` on `{0, 1}`.

We compute their means and show that they satisfy the noise assumptions of the regret analyses:
Gaussian arms are `σ2`-sub-Gaussian, Bernoulli arms are bounded in `[0, 1]` and
`1 / 4`-sub-Gaussian. We also compute the relative entropy between the arms of two Gaussian bandits
with the same variance [LS, Theorem 14.1], the quantity that enters the lower bounds.

The arm type only needs to be countable with measurable singletons, so that every function on it
is measurable.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory

open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace LMLExplore.Bandits

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

section Gaussian

variable {μ : α → ℝ} {σ2 : ℝ≥0}

/-- The Gaussian bandit with means `μ` and variance `σ2`: arm `a` has law `𝒩(μ a, σ2)`. -/
noncomputable def gaussianBandit (μ : α → ℝ) (σ2 : ℝ≥0) : Kernel α ℝ :=
  Kernel.ofFunOfCountable fun a ↦ gaussianReal (μ a) σ2

@[simp]
lemma gaussianBandit_apply (μ : α → ℝ) (σ2 : ℝ≥0) (a : α) :
    gaussianBandit μ σ2 a = gaussianReal (μ a) σ2 :=
  (rfl)

instance (μ : α → ℝ) (σ2 : ℝ≥0) : IsMarkovKernel (gaussianBandit μ σ2) :=
  ⟨fun a ↦ by rw [gaussianBandit_apply]; infer_instance⟩

/-- The mean of arm `a` of the Gaussian bandit with means `μ` is `μ a`. -/
lemma integral_id_gaussianBandit (μ : α → ℝ) (σ2 : ℝ≥0) (a : α) :
    (gaussianBandit μ σ2 a)[id] = μ a := by
  simp

/-- The arms of the Gaussian bandit with variance `σ2` are `σ2`-sub-Gaussian. -/
lemma hasSubgaussianMGF_gaussianBandit (μ : α → ℝ) (σ2 : ℝ≥0) (a : α) :
    HasSubgaussianMGF (fun x ↦ x - (gaussianBandit μ σ2 a)[id]) σ2 (gaussianBandit μ σ2 a) := by
  rw [integral_id_gaussianBandit, gaussianBandit_apply]
  exact hasSubgaussianMGF_sub_of_hasLaw_gaussianReal HasLaw.id

/-- The relative entropy between arm `a` of two Gaussian bandits with the same nonzero variance
`σ2` is `(μ a - μ' a) ^ 2 / (2 σ2)` [LS, Theorem 14.1]. -/
lemma klDiv_gaussianBandit (μ μ' : α → ℝ) (hσ2 : σ2 ≠ 0) (a : α) :
    klDiv (gaussianBandit μ σ2 a) (gaussianBandit μ' σ2 a) =
      ENNReal.ofReal ((μ a - μ' a) ^ 2 / (2 * σ2)) := by
  rw [gaussianBandit_apply, gaussianBandit_apply, klDiv_gaussianReal_gaussianReal_same_var hσ2]

end Gaussian

section Bernoulli

variable {p : α → I}

/-- The Bernoulli bandit with means `p`: arm `a` has law `Ber((1 : ℝ), 0, p a)`, which gives
reward `1` with probability `p a` and reward `0` otherwise. -/
noncomputable def bernoulliBandit (p : α → I) : Kernel α ℝ :=
  Kernel.ofFunOfCountable fun a ↦ Ber((1 : ℝ), 0, p a)

@[simp]
lemma bernoulliBandit_apply (p : α → I) (a : α) : bernoulliBandit p a = Ber((1 : ℝ), 0, p a) :=
  (rfl)

instance (p : α → I) : IsMarkovKernel (bernoulliBandit p) :=
  ⟨fun a ↦ by rw [bernoulliBandit_apply]; infer_instance⟩

/-- The mean of arm `a` of the Bernoulli bandit with means `p` is `p a`. -/
lemma integral_id_bernoulliBandit (p : α → I) (a : α) : (bernoulliBandit p a)[id] = (p a : ℝ) := by
  simp

/-- The rewards of the Bernoulli bandit lie in `[0, 1]` almost surely. -/
lemma ae_mem_Icc_bernoulliBandit (p : α → I) (a : α) :
    ∀ᵐ x ∂(bernoulliBandit p a), x ∈ Set.Icc 0 1 := by
  simpa using ae_mem_Icc_bernoulliMeasure (p a)

/-- The arms of the Bernoulli bandit are `1 / 4`-sub-Gaussian. -/
lemma hasSubgaussianMGF_bernoulliBandit (p : α → I) (a : α) :
    HasSubgaussianMGF (fun x ↦ x - (bernoulliBandit p a)[id]) (1 / 4) (bernoulliBandit p a) := by
  rw [integral_id_bernoulliBandit, bernoulliBandit_apply]
  exact hasSubgaussianMGF_bernoulliMeasure (p a)

end Bernoulli

end LMLExplore.Bandits
