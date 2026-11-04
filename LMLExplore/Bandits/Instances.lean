/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.Probability.Distributions.ExponentialFamily.Bernoulli
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian
public import LMLExplore.Probability.Distributions.Bernoulli
public import LMLExplore.Probability.Kernel.Basic
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Gaussian and Bernoulli bandits

A stochastic bandit with arms `α` is a Markov kernel `ν : Kernel α ℝ`: pulling arm `a` returns a
reward with law `ν a`, and the mean of arm `a` is `(ν a)[id]`. This file defines the standard
instances [LS, Chapter 4]:

* `LMLExplore.Bandits.gaussianBandit μ σ2`: arm `a` has law `𝒩(μ a, σ2)`;
* `LMLExplore.Bandits.gaussianMeanVarBandit θ`: arm `a` has law `𝒩((θ a).1, (θ a).2)`, with a mean
  and a variance for each arm, the model of Gaussian arms with unknown variances;
* `LMLExplore.Bandits.bernoulliBandit p`: arm `a` has law `Ber((1 : ℝ), 0, p a)` on `{0, 1}`.

We compute their means and show that they satisfy the noise assumptions of the regret analyses:
the arms of `gaussianBandit μ σ2` are `σ2`-sub-Gaussian, Bernoulli arms are bounded in `[0, 1]`
and `1 / 4`-sub-Gaussian. We also compute the relative entropy between the arms of two Gaussian
bandits with the same variance [LS, Theorem 14.1], the quantity that enters the lower bounds, and
identify it with the divergence of the exponential family of `𝒩(0, σ2)`
(`LMLExplore.Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv`), and the relative entropy
between the arms of two Bernoulli bandits with means in `(0, 1)` with the divergence of the
exponential family of a Bernoulli law
(`LMLExplore.Bandits.klDiv_bernoulliBandit_eq_ofReal_expFamilyDiv`). For the Gaussian bandit with
unknown variances we compute the mean and the variance of each arm, and identify
`gaussianBandit μ σ2` with `gaussianMeanVarBandit fun a ↦ (μ a, σ2)`
(`LMLExplore.Bandits.gaussianBandit_eq_gaussianMeanVarBandit`).

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
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

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

/-- The arm laws of a Gaussian bandit with variance `σ2 ≠ 0` are members of the exponential family
of `𝒩(0, σ2)`: the relative entropy between arm `a` of two Gaussian bandits is the divergence
`d(μ a, μ' a)` of the family. -/
lemma klDiv_gaussianBandit_eq_ofReal_expFamilyDiv (hσ2 : σ2 ≠ 0) (μ μ' : α → ℝ) (a : α) :
    klDiv (gaussianBandit μ σ2 a) (gaussianBandit μ' σ2 a) =
      ENNReal.ofReal ((gaussianReal 0 σ2).expFamilyDiv id (μ a) (μ' a)) := by
  rw [klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2]

end Gaussian

section GaussianMeanVar

/-- The Gaussian bandit with means and variances `θ`: arm `a` has law `𝒩((θ a).1, (θ a).2)`. This
is the model of Gaussian arms with unknown variances, whose parameter `θ a` is the pair of the
mean and the variance of the arm `a`. -/
noncomputable def gaussianMeanVarBandit (θ : α → ℝ × ℝ≥0) : Kernel α ℝ :=
  Kernel.ofFunOfCountable fun a ↦ gaussianReal (θ a).1 (θ a).2

@[simp]
lemma gaussianMeanVarBandit_apply (θ : α → ℝ × ℝ≥0) (a : α) :
    gaussianMeanVarBandit θ a = gaussianReal (θ a).1 (θ a).2 :=
  (rfl)

instance (θ : α → ℝ × ℝ≥0) : IsMarkovKernel (gaussianMeanVarBandit θ) :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

/-- The mean of arm `a` of the Gaussian bandit with means and variances `θ` is `(θ a).1`. -/
lemma integral_id_gaussianMeanVarBandit (θ : α → ℝ × ℝ≥0) (a : α) :
    (gaussianMeanVarBandit θ a)[id] = (θ a).1 := by
  simp

/-- The variance of arm `a` of the Gaussian bandit with means and variances `θ` is `(θ a).2`. -/
lemma variance_id_gaussianMeanVarBandit (θ : α → ℝ × ℝ≥0) (a : α) :
    Var[id; gaussianMeanVarBandit θ a] = (θ a).2 := by
  simp [variance_id_gaussianReal]

/-- The Gaussian bandit with means `μ` and common variance `σ2` is the Gaussian bandit with means
and variances `(μ a, σ2)`. -/
lemma gaussianBandit_eq_gaussianMeanVarBandit (μ : α → ℝ) (σ2 : ℝ≥0) :
    gaussianBandit μ σ2 = gaussianMeanVarBandit fun a ↦ (μ a, σ2) :=
  Kernel.ext fun a ↦ by simp

end GaussianMeanVar

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
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

/-- The mean of arm `a` of the Bernoulli bandit with means `p` is `p a`. -/
lemma integral_id_bernoulliBandit (p : α → I) (a : α) : (bernoulliBandit p a)[id] = (p a : ℝ) := by
  simp

/-- The rewards of the Bernoulli bandit lie in `[0, 1]` almost surely. -/
lemma ae_mem_Icc_bernoulliBandit (p : α → I) (a : α) :
    ∀ᵐ x ∂(bernoulliBandit p a), x ∈ Set.Icc 0 1 := by
  simpa using ae_mem_uIcc_bernoulliMeasure 1 0 (p a)

/-- The arms of the Bernoulli bandit are `1 / 4`-sub-Gaussian. -/
lemma hasSubgaussianMGF_bernoulliBandit (p : α → I) (a : α) :
    HasSubgaussianMGF (fun x ↦ x - (bernoulliBandit p a)[id]) (1 / 4) (bernoulliBandit p a) := by
  have hc : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  rw [integral_id_bernoulliBandit, bernoulliBandit_apply, ← hc]
  simpa using hasSubgaussianMGF_bernoulliMeasure 1 0 (p a)

/-- The arm laws of a Bernoulli bandit with means in `(0, 1)` are members of the exponential family
of `Ber((1 : ℝ), 0, sigmoid η₀)`: the relative entropy between arm `a` of two Bernoulli bandits is
the divergence `d(p a, p' a)` of the family, the binary relative entropy. -/
lemma klDiv_bernoulliBandit_eq_ofReal_expFamilyDiv (η₀ : ℝ) {p p' : α → I} {a : α}
    (hp : (p a : ℝ) ∈ Set.Ioo 0 1) (hp' : (p' a : ℝ) ∈ Set.Ioo 0 1) :
    klDiv (bernoulliBandit p a) (bernoulliBandit p' a) =
      ENNReal.ofReal (Ber((1 : ℝ), 0, unitInterval.sigmoid η₀).expFamilyDiv id (p a) (p' a)) := by
  rw [bernoulliBandit_apply, bernoulliBandit_apply, klDiv_bernoulliMeasure,
    expFamilyDiv_bernoulliMeasure_sigmoid η₀ hp hp', klBer_eq_ofReal_klBerReal
      (Set.Ioo_subset_Icc_self hp) (Set.Ioo_subset_Icc_self hp') (klBer_ne_top hp')]

end Bernoulli

end LMLExplore.Bandits
