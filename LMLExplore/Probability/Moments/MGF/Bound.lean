/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.SubExponential
public import LMLExplore.Probability.Kernel.Condexp
public import LMLExplore.Probability.Moments.MGF.Dominated
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Moment generating functions bounded by `exp ψ`, conditionally

For a real random variable `X`, a function `ψ : ℝ → ℝ` and a set `Λ ⊆ ℝ` of parameters, `X` has
its moment generating function bounded by `exp ψ` on `Λ` if `E[exp (t X)] ≤ exp (ψ t)` for every
`t ∈ Λ`. Sub-Gaussian variables are the case `ψ t = c t ^ 2 / 2` on `ℝ`, sub-exponential variables
the case `ψ t = V t ^ 2 / 2` on `{t | b |t| ≤ 1}`, and a variable dominated by a variable `Y` on a
set `Λ` in the sense of `LMLExplore.MGFDominatedOn` is the case of the cumulant generating function
of `Y` on the parameters of `Λ` where it is finite. One definition with a free `ψ` lets the
exponential supermartingales, and the time-uniform deviation bounds built from them, be proved
once for all these classes (see `LMLExplore.Probability.Martingale.MGFBound`).

As for Mathlib's sub-Gaussian variables, the bound comes in three versions:
* the kernel version `ProbabilityTheory.Kernel.HasMGFBound X ψ Λ κ ν`: `exp (t X)` is
  `κ ∘ₘ ν`-integrable for every `t ∈ Λ`, and for `ν`-almost every `ω'`, for every `t ∈ Λ`,
  `exp (t X)` is `κ ω'`-integrable and `mgf X (κ ω') t ≤ exp (ψ t)`;
* the conditional version `LMLExplore.HasCondMGFBound m hm X ψ Λ μ` given a σ-algebra `m`, the
  kernel version for `condExpKernel μ m` and `μ.trim hm`;
* the unconditional version `LMLExplore.HasMGFBound X ψ Λ μ`, equivalent to the kernel version
  for a constant kernel on a point.

The bound holds for `ν`-almost every `ω'` simultaneously for all `t ∈ Λ`, and the integrability
under each `κ ω'` is part of the definition: for the sub-Gaussian and sub-exponential classes it
follows from the integrability under `κ ∘ₘ ν` by convexity in `t`, but not for a general `Λ`. This
is what allows the parameter `t` to be a random variable measurable with respect to the
conditioning σ-algebra (`LMLExplore.HasCondMGFBound.lintegral_mul_exp_le`), as for the predictable
weights of an exponential supermartingale.

## Main definitions

* `ProbabilityTheory.Kernel.HasMGFBound X ψ Λ κ ν`: the kernel version.
* `LMLExplore.HasCondMGFBound m hm X ψ Λ μ`: the conditional version.
* `LMLExplore.HasMGFBound X ψ Λ μ`: the unconditional version.

## Main statements

* `LMLExplore.HasCondMGFBound.ae_condExp_le`: `E[exp (t X) | m] ≤ exp (ψ t)` almost surely, for
  `t ∈ Λ`.
* `LMLExplore.HasCondMGFBound.lintegral_mul_exp_le`: for an `m`-measurable parameter `s` with
  values in `Λ` and an `m`-measurable weight `g ≥ 0`,
  `∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (ψ ∘ s)`.
* `LMLExplore.HasCondMGFBound.mono`, `LMLExplore.HasCondMGFBound.neg`,
  `LMLExplore.HasCondMGFBound.add_const`: monotonicity in `Λ` and `ψ`, negation, and translation;
  likewise for the kernel and unconditional versions, together with measurability
  (`aestronglyMeasurable`) and the bound on the cumulant generating function (`cgf_le`).
* `LMLExplore.HasMGFBound.hasCondMGFBound_of_indep`: for a variable independent of `m`, the
  unconditional bound gives the conditional one.
* `LMLExplore.hasCondMGFBound_iff_hasCondSubgaussianMGF`,
  `LMLExplore.hasCondMGFBound_iff_hasCondSubexponentialMGF`: Mathlib's conditionally sub-Gaussian
  and LML's conditionally sub-exponential variables are instances; similarly for the kernel
  versions (`ProbabilityTheory.Kernel.hasMGFBound_iff_hasSubgaussianMGF`, …) and the
  unconditional ones (`LMLExplore.hasMGFBound_iff_hasSubgaussianMGF`,
  `LMLExplore.hasMGFBound_iff_hasSubexponentialMGF`).
* `LMLExplore.mgfDominatedOn_iff_hasMGFBound`: domination by `Y` on `Λ` is the bound by the
  cumulant generating function of `Y` on `Λ`.
* `ProbabilityTheory.HasCondSubgaussianMGF.hasCondMGFBound_cgf_gaussianReal`: if `X - a` is
  conditionally `c`-sub-Gaussian, the moment generating function of `X` is conditionally bounded
  by that of the Gaussian law of mean `a` and variance `c`.
* `ProbabilityTheory.HasSubgaussianMGF.mgfDominatedOn_gaussianReal`: if `X - a` is
  `c`-sub-Gaussian, then `X` is dominated on `ℝ` by the Gaussian law of mean `a` and variance `c`.

## References

* The definitions follow the pattern of Mathlib's `ProbabilityTheory.Kernel.HasSubgaussianMGF`
  and `ProbabilityTheory.HasCondSubgaussianMGF`.
* The proof of `LMLExplore.HasCondMGFBound.lintegral_mul_exp_le` generalizes the sub-Gaussian case
  adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Moments/SubGaussian.lean`).
* S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probability Surveys 17 (2020), 257–317 (conditions on the
  cumulant generating function by an arbitrary function `ψ`).
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {ψ ψ' : ℝ → ℝ} {Λ Λ' : Set ℝ} {t : ℝ}

/-- A real random variable `X` has its moment generating function bounded by `exp ψ` on the set
of parameters `Λ`, with respect to a kernel `κ` and a measure `ν`, if `exp (t * X)` is
`κ ∘ₘ ν`-integrable for every `t ∈ Λ`, and for `ν`-almost every `ω'`, simultaneously for every
`t ∈ Λ`, `exp (t * X)` is `κ ω'`-integrable and `mgf X (κ ω') t ≤ exp (ψ t)`. -/
structure HasMGFBound (X : Ω → ℝ) (ψ : ℝ → ℝ) (Λ : Set ℝ) (κ : Kernel Ω' Ω)
    (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul ⦃t : ℝ⦄ (ht : t ∈ Λ) : Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  ae_forall_integrable_exp_mul :
    ∀ᵐ ω' ∂ν, ∀ t ∈ Λ, Integrable (fun ω ↦ exp (t * X ω)) (κ ω')
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t ∈ Λ, mgf X (κ ω') t ≤ exp (ψ t)

namespace HasMGFBound

/-- A variable whose moment generating function is bounded at a nonzero parameter is almost
everywhere strongly measurable. -/
lemma aestronglyMeasurable (h : HasMGFBound X ψ Λ κ ν) (ht : t ∈ Λ) (ht0 : t ≠ 0) :
    AEStronglyMeasurable X (κ ∘ₘ ν) :=
  (aemeasurable_of_aemeasurable_exp_mul ht0
    (h.integrable_exp_mul ht).1.aemeasurable).aestronglyMeasurable

/-- The bound on the cumulant generating function: `cgf X (κ ω') t ≤ ψ t` for `ν`-almost every
`ω'` and every `t ∈ Λ`. -/
lemma cgf_le [IsMarkovKernel κ] (h : HasMGFBound X ψ Λ κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t ∈ Λ, cgf X (κ ω') t ≤ ψ t := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' hmgf hint t ht
  rw [cgf, log_le_iff_le_exp (mgf_pos (hint t ht))]
  exact hmgf t ht

/-- The bound is monotone: it holds on a smaller set of parameters, for a larger `ψ`. -/
lemma mono (h : HasMGFBound X ψ Λ κ ν) (hΛ : Λ' ⊆ Λ) (hψ : ∀ t ∈ Λ', ψ t ≤ ψ' t) :
    HasMGFBound X ψ' Λ' κ ν where
  integrable_exp_mul _ ht := h.integrable_exp_mul (hΛ ht)
  ae_forall_integrable_exp_mul := by
    filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hω t ht using hω t (hΛ ht)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω' hω t ht
    exact (hω t (hΛ ht)).trans (exp_le_exp.2 (hψ t ht))

/-- If the moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of `-X` is
bounded by `exp (ψ ∘ Neg.neg)` on `-Λ`. -/
lemma neg (h : HasMGFBound X ψ Λ κ ν) : HasMGFBound (-X) (fun t ↦ ψ (-t)) (-Λ) κ ν where
  integrable_exp_mul t ht := by
    simpa [mul_neg, ← neg_mul] using h.integrable_exp_mul (Set.mem_neg.1 ht)
  ae_forall_integrable_exp_mul := by
    filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hω t ht
    simpa [mul_neg, ← neg_mul] using hω (-t) (Set.mem_neg.1 ht)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω' hω t ht
    rw [mgf_neg]
    exact hω (-t) (Set.mem_neg.1 ht)

/-- If the moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of `X + a` is
bounded by `exp (ψ t + t a)`. -/
lemma add_const (h : HasMGFBound X ψ Λ κ ν) (a : ℝ) :
    HasMGFBound (fun ω ↦ X ω + a) (fun t ↦ ψ t + t * a) Λ κ ν where
  integrable_exp_mul t ht := by
    simpa [mul_add, exp_add] using (h.integrable_exp_mul ht).mul_const (exp (t * a))
  ae_forall_integrable_exp_mul := by
    filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hω t ht
    simpa [mul_add, exp_add] using (hω t ht).mul_const (exp (t * a))
  mgf_le := by
    filter_upwards [h.mgf_le] with ω' hω t ht
    rw [mgf_add_const, exp_add]
    exact mul_le_mul_of_nonneg_right (hω t ht) (exp_pos _).le

end HasMGFBound

variable {c : ℝ≥0} {V b : ℝ}

/-- `X` is sub-Gaussian with parameter `c` with respect to `κ` and `ν` iff its moment
generating function is bounded by `exp (c t ^ 2 / 2)` on `ℝ`. -/
lemma hasMGFBound_iff_hasSubgaussianMGF :
    HasMGFBound X (fun t ↦ c * t ^ 2 / 2) Set.univ κ ν ↔ HasSubgaussianMGF X c κ ν :=
  ⟨fun h ↦ ⟨fun t ↦ h.integrable_exp_mul (Set.mem_univ t), by
      filter_upwards [h.mgf_le] with ω' hω t using hω t (Set.mem_univ t)⟩,
    fun h ↦ ⟨fun t _ ↦ h.integrable_exp_mul t, by
      filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hω t _ using hω t, by
      filter_upwards [h.mgf_le] with ω' hω t _ using hω t⟩⟩

/-- `X` is sub-exponential with parameters `(V, b)` with respect to `κ` and `ν` iff its moment
generating function is bounded by `exp (V t ^ 2 / 2)` on `{t | b |t| ≤ 1}`. -/
lemma hasMGFBound_iff_hasSubexponentialMGF :
    HasMGFBound X (fun t ↦ V * t ^ 2 / 2) {t | b * |t| ≤ 1} κ ν ↔
      HasSubexponentialMGF X V b κ ν :=
  ⟨fun h ↦ ⟨fun _ ht ↦ h.integrable_exp_mul ht, h.mgf_le⟩,
    fun h ↦ ⟨fun t ht ↦ h.integrable_exp_mul t ht, h.ae_forall_integrable_exp_mul, h.mgf_le⟩⟩

end ProbabilityTheory.Kernel

namespace LMLExplore

section Conditional

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {ψ ψ' : ℝ → ℝ} {Λ Λ' : Set ℝ} {t : ℝ}

variable (m hm) in
/-- A real random variable `X` has its moment generating function conditionally bounded by
`exp ψ` on the set of parameters `Λ` given the σ-algebra `m` if `exp (t * X)` is `μ`-integrable
for every `t ∈ Λ`, and almost surely, simultaneously for every `t ∈ Λ`, `exp (t * X)` is
integrable under the conditional expectation kernel and the moment generating function of `X`
conditioned on `m` is at most `exp (ψ t)`.

It is defined as `Kernel.HasMGFBound` for the conditional expectation kernel `condExpKernel μ m`
and the restriction `μ.trim hm` of `μ` to `m`. -/
def HasCondMGFBound (X : Ω → ℝ) (ψ : ℝ → ℝ) (Λ : Set ℝ) (μ : Measure Ω := by volume_tac)
    [IsFiniteMeasure μ] : Prop :=
  Kernel.HasMGFBound X ψ Λ (condExpKernel μ m) (μ.trim hm)

/-- The defining property of `HasCondMGFBound`: the kernel bound for the conditional expectation
kernel. -/
lemma hasCondMGFBound_iff_kernel :
    HasCondMGFBound m hm X ψ Λ μ ↔ Kernel.HasMGFBound X ψ Λ (condExpKernel μ m) (μ.trim hm) :=
  (Iff.rfl)

namespace HasCondMGFBound

/-- `exp (t * X)` is integrable for every `t ∈ Λ`. -/
lemma integrable_exp_mul (h : HasCondMGFBound m hm X ψ Λ μ) (ht : t ∈ Λ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ (hasCondMGFBound_iff_kernel.1 h).integrable_exp_mul ht

/-- The conditional moment generating function bound on the restriction of `μ` to `m`:
`E[exp (t X) | m] ≤ exp (ψ t)` for `t ∈ Λ`. -/
lemma ae_trim_condExp_le (h : HasCondMGFBound m hm X ψ Λ μ) (ht : t ∈ Λ) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (ψ t) := by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul ht)
  filter_upwards [(hasCondMGFBound_iff_kernel.1 h).mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t ht

/-- The conditional moment generating function bound `E[exp (t X) | m] ≤ exp (ψ t)` almost
surely, for `t ∈ Λ`. -/
lemma ae_condExp_le (h : HasCondMGFBound m hm X ψ Λ μ) (ht : t ∈ Λ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (ψ t) :=
  ae_of_ae_trim hm (h.ae_trim_condExp_le ht)

/-- A variable whose conditional moment generating function is bounded at a nonzero parameter is
almost everywhere strongly measurable. -/
lemma aestronglyMeasurable (h : HasCondMGFBound m hm X ψ Λ μ) (ht : t ∈ Λ) (ht0 : t ≠ 0) :
    AEStronglyMeasurable X μ :=
  (aemeasurable_of_aemeasurable_exp_mul ht0
    (h.integrable_exp_mul ht).1.aemeasurable).aestronglyMeasurable

/-- The bound on the conditional cumulant generating function: on the restriction of `μ` to `m`,
almost surely `cgf X (condExpKernel μ m ω') t ≤ ψ t` for every `t ∈ Λ`. -/
lemma cgf_le (h : HasCondMGFBound m hm X ψ Λ μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t ∈ Λ, cgf X (condExpKernel μ m ω') t ≤ ψ t :=
  (hasCondMGFBound_iff_kernel.1 h).cgf_le

/-- The conditional bound is monotone: it holds on a smaller set of parameters, for a larger
`ψ`. -/
lemma mono (h : HasCondMGFBound m hm X ψ Λ μ) (hΛ : Λ' ⊆ Λ) (hψ : ∀ t ∈ Λ', ψ t ≤ ψ' t) :
    HasCondMGFBound m hm X ψ' Λ' μ :=
  hasCondMGFBound_iff_kernel.2 ((hasCondMGFBound_iff_kernel.1 h).mono hΛ hψ)

/-- If the conditional moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of
`-X` is bounded by `exp (ψ ∘ Neg.neg)` on `-Λ`. -/
lemma neg (h : HasCondMGFBound m hm X ψ Λ μ) :
    HasCondMGFBound m hm (-X) (fun t ↦ ψ (-t)) (-Λ) μ :=
  hasCondMGFBound_iff_kernel.2 (hasCondMGFBound_iff_kernel.1 h).neg

/-- If the conditional moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of
`X + a` is bounded by `exp (ψ t + t a)`. -/
lemma add_const (h : HasCondMGFBound m hm X ψ Λ μ) (a : ℝ) :
    HasCondMGFBound m hm (fun ω ↦ X ω + a) (fun t ↦ ψ t + t * a) Λ μ :=
  hasCondMGFBound_iff_kernel.2 ((hasCondMGFBound_iff_kernel.1 h).add_const a)

/-- **Conditional moment bound at a random parameter.** If `X` is measurable with conditional
moment generating function bounded by `exp ψ` on `Λ` given `m`, then for every `m`-measurable
parameter `s` with values in `Λ` almost surely and every `m`-measurable `g ≥ 0`,
`∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (ψ ∘ s)`. -/
theorem lintegral_mul_exp_le (h : HasCondMGFBound m hm X ψ Λ μ) (hX : Measurable X)
    {s : Ω → ℝ} (hs : Measurable[m] s) (hsΛ : ∀ᵐ ω ∂μ, s ω ∈ Λ) {g : Ω → ℝ≥0∞}
    (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (exp (s ω * X ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (exp (ψ (s ω))) ∂μ := by
  have hΦ : Measurable
      (fun p : (ℝ≥0∞ × ℝ) × Ω ↦ p.1.1 * ENNReal.ofReal (exp (p.1.2 * X p.2))) := by
    fun_prop
  rw [lintegral_comp_condExpKernel hm (hg.prodMk hs) hΦ]
  refine lintegral_mono_ae ?_
  have h' := hasCondMGFBound_iff_kernel.1 h
  filter_upwards [ae_of_ae_trim hm h'.mgf_le, ae_of_ae_trim hm h'.ae_forall_integrable_exp_mul,
    hsΛ] with ω hmgf hint hsω
  rw [lintegral_const_mul _ (by fun_prop)]
  gcongr
  rw [← ofReal_integral_eq_lintegral_ofReal (hint (s ω) hsω)
    (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (hmgf (s ω) hsω)

end HasCondMGFBound

variable {c : ℝ≥0} {V b : ℝ}

/-- `X` is conditionally sub-Gaussian with parameter `c` given `m` iff its conditional moment
generating function is bounded by `exp (c t ^ 2 / 2)` on `ℝ`. -/
lemma hasCondMGFBound_iff_hasCondSubgaussianMGF :
    HasCondMGFBound m hm X (fun t ↦ c * t ^ 2 / 2) Set.univ μ ↔
      HasCondSubgaussianMGF m hm X c μ :=
  hasCondMGFBound_iff_kernel.trans Kernel.hasMGFBound_iff_hasSubgaussianMGF

/-- `X` is conditionally sub-exponential with parameters `(V, b)` given `m` iff its conditional
moment generating function is bounded by `exp (V t ^ 2 / 2)` on `{t | b |t| ≤ 1}`. -/
lemma hasCondMGFBound_iff_hasCondSubexponentialMGF :
    HasCondMGFBound m hm X (fun t ↦ V * t ^ 2 / 2) {t | b * |t| ≤ 1} μ ↔
      HasCondSubexponentialMGF m hm X V b μ :=
  hasCondMGFBound_iff_kernel.trans Kernel.hasMGFBound_iff_hasSubexponentialMGF

end Conditional

/-- If `X - a` is conditionally `c`-sub-Gaussian given `m`, then the conditional moment generating
function of `X` is bounded by that of the Gaussian law of mean `a` and variance `c`. -/
lemma _root_.ProbabilityTheory.HasCondSubgaussianMGF.hasCondMGFBound_cgf_gaussianReal
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {a : ℝ} {c : ℝ≥0}
    (h : HasCondSubgaussianMGF m hm (fun ω ↦ X ω - a) c μ) :
    HasCondMGFBound m hm X (cgf id (gaussianReal a c)) Set.univ μ := by
  have h' := (hasCondMGFBound_iff_hasCondSubgaussianMGF.2 h).add_const a
  simp only [sub_add_cancel] at h'
  refine h'.mono subset_rfl fun t _ ↦ le_of_eq ?_
  rw [cgf_gaussianReal HasLaw.id]
  ring

section Unconditional

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {X : Ω → ℝ} {ψ ψ' : ℝ → ℝ} {Λ Λ' : Set ℝ} {t : ℝ}

/-- A real random variable `X` has its moment generating function bounded by `exp ψ` on the set
of parameters `Λ` under `μ` if for every `t ∈ Λ`, `exp (t * X)` is `μ`-integrable and
`mgf X μ t ≤ exp (ψ t)`.

This is `Kernel.HasMGFBound X ψ Λ (Kernel.const Unit μ) (Measure.dirac ())`, as proved in
`hasMGFBound_iff_kernel`. -/
structure HasMGFBound (X : Ω → ℝ) (ψ : ℝ → ℝ) (Λ : Set ℝ) (μ : Measure Ω := by volume_tac) :
    Prop where
  integrable_exp_mul ⦃t : ℝ⦄ (ht : t ∈ Λ) : Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le ⦃t : ℝ⦄ (ht : t ∈ Λ) : mgf X μ t ≤ exp (ψ t)

/-- The unconditional bound is the kernel bound for a constant kernel on a point. -/
lemma hasMGFBound_iff_kernel :
    HasMGFBound X ψ Λ μ ↔ Kernel.HasMGFBound X ψ Λ (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun h ↦ ⟨by simpa using h.integrable_exp_mul, by simpa using h.integrable_exp_mul,
      by simpa using h.mgf_le⟩,
    fun h ↦ ⟨by simpa using h.integrable_exp_mul, by simpa using h.mgf_le⟩⟩

namespace HasMGFBound

/-- A variable whose moment generating function is bounded at a nonzero parameter is almost
everywhere strongly measurable. -/
lemma aestronglyMeasurable (h : HasMGFBound X ψ Λ μ) (ht : t ∈ Λ) (ht0 : t ≠ 0) :
    AEStronglyMeasurable X μ :=
  (aemeasurable_of_aemeasurable_exp_mul ht0
    (h.integrable_exp_mul ht).1.aemeasurable).aestronglyMeasurable

/-- The bound on the cumulant generating function: `cgf X μ t ≤ ψ t` for every `t ∈ Λ`. -/
lemma cgf_le [NeZero μ] (h : HasMGFBound X ψ Λ μ) (ht : t ∈ Λ) : cgf X μ t ≤ ψ t := by
  rw [cgf, log_le_iff_le_exp (mgf_pos' (NeZero.ne μ) (h.integrable_exp_mul ht))]
  exact h.mgf_le ht

/-- The bound is monotone: it holds on a smaller set of parameters, for a larger `ψ`. -/
lemma mono (h : HasMGFBound X ψ Λ μ) (hΛ : Λ' ⊆ Λ) (hψ : ∀ t ∈ Λ', ψ t ≤ ψ' t) :
    HasMGFBound X ψ' Λ' μ :=
  hasMGFBound_iff_kernel.2 ((hasMGFBound_iff_kernel.1 h).mono hΛ hψ)

/-- If the moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of `-X` is
bounded by `exp (ψ ∘ Neg.neg)` on `-Λ`. -/
lemma neg (h : HasMGFBound X ψ Λ μ) : HasMGFBound (-X) (fun t ↦ ψ (-t)) (-Λ) μ :=
  hasMGFBound_iff_kernel.2 (hasMGFBound_iff_kernel.1 h).neg

/-- If the moment generating function of `X` is bounded by `exp ψ` on `Λ`, that of `X + a` is
bounded by `exp (ψ t + t a)`. -/
lemma add_const (h : HasMGFBound X ψ Λ μ) (a : ℝ) :
    HasMGFBound (fun ω ↦ X ω + a) (fun t ↦ ψ t + t * a) Λ μ :=
  hasMGFBound_iff_kernel.2 ((hasMGFBound_iff_kernel.1 h).add_const a)

end HasMGFBound

section SubgaussianSubexponential

variable {c : ℝ≥0} {V b : ℝ}

/-- `X` is sub-Gaussian with parameter `c` under `μ` iff its moment generating function is
bounded by `exp (c t ^ 2 / 2)` on `ℝ`. -/
lemma hasMGFBound_iff_hasSubgaussianMGF :
    HasMGFBound X (fun t ↦ c * t ^ 2 / 2) Set.univ μ ↔ HasSubgaussianMGF X c μ :=
  ⟨fun h ↦ ⟨fun t ↦ h.integrable_exp_mul (Set.mem_univ t), fun t ↦ h.mgf_le (Set.mem_univ t)⟩,
    fun h ↦ ⟨fun t _ ↦ h.integrable_exp_mul t, fun t _ ↦ h.mgf_le t⟩⟩

/-- `X` is sub-exponential with parameters `(V, b)` under `μ` iff its moment generating function
is bounded by `exp (V t ^ 2 / 2)` on `{t | b |t| ≤ 1}`. -/
lemma hasMGFBound_iff_hasSubexponentialMGF :
    HasMGFBound X (fun t ↦ V * t ^ 2 / 2) {t | b * |t| ≤ 1} μ ↔ HasSubexponentialMGF X V b μ :=
  ⟨fun h ↦ ⟨fun _ ht ↦ h.integrable_exp_mul ht, fun _ ht ↦ h.mgf_le ht⟩,
    fun h ↦ ⟨fun t ht ↦ h.integrable_exp_mul t ht, fun t ht ↦ h.mgf_le t ht⟩⟩

end SubgaussianSubexponential

variable {P : Measure Ω} {Q : Measure Ω'} [NeZero Q] {Y : Ω' → ℝ}

/-- `X` under `P` is dominated by `Y` under `Q` on `Λ` iff its moment generating function is
bounded by `exp (cgf Y Q)` on the parameters of `Λ` at which `exp (t * Y)` is `Q`-integrable. -/
lemma mgfDominatedOn_iff_hasMGFBound :
    MGFDominatedOn X P Y Q Λ ↔ HasMGFBound X (cgf Y Q) (Λ ∩ integrableExpSet Y Q) P :=
  ⟨fun h ↦ ⟨fun _ ht ↦ h.integrable_exp_mul ht.1 ht.2,
      fun _ ht ↦ (exp_cgf ht.2).symm ▸ h.mgf_le ht.1 ht.2⟩,
    fun h ↦ ⟨fun _ ht hY ↦ h.integrable_exp_mul ⟨ht, hY⟩,
      fun _ ht hY ↦ exp_cgf hY ▸ h.mgf_le ⟨ht, hY⟩⟩⟩

/-- If `X - a` is `c`-sub-Gaussian under `P`, then `X` is dominated on `ℝ` by the Gaussian law of
mean `a` and variance `c`. -/
lemma _root_.ProbabilityTheory.HasSubgaussianMGF.mgfDominatedOn_gaussianReal {a : ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω ↦ X ω - a) c P) :
    MGFDominatedOn X P id (gaussianReal a c) Set.univ := by
  rw [mgfDominatedOn_iff_hasMGFBound]
  have h' := (hasMGFBound_iff_hasSubgaussianMGF.2 h).add_const a
  simp only [sub_add_cancel] at h'
  refine h'.mono Set.inter_subset_left fun t _ ↦ le_of_eq ?_
  rw [cgf_gaussianReal HasLaw.id]
  ring

end Unconditional

section Indep

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {ψ : ℝ → ℝ} {Λ : Set ℝ}

/-- **Independence gives the conditional bound.** If `X` is measurable, independent of the
σ-algebra `m`, and its moment generating function is bounded by `exp ψ` on `Λ`, then its
conditional moment generating function given `m` is bounded by `exp ψ` on `Λ`. -/
theorem HasMGFBound.hasCondMGFBound_of_indep (h : HasMGFBound X ψ Λ μ) (hX : Measurable X)
    (h_indep : Indep (MeasurableSpace.comap X inferInstance) m μ) :
    HasCondMGFBound m hm X ψ Λ μ := by
  have h_map := ae_trim_map_condExpKernel_eq_of_indep (hm := hm) hX h_indep
  have h_int (ν : Measure Ω) {t : ℝ} : Integrable (fun ω ↦ exp (t * X ω)) ν ↔
      Integrable (fun x ↦ exp (t * x)) (ν.map X) :=
    (integrable_map_measure (g := fun x ↦ exp (t * x))
      (by fun_prop : Measurable fun x : ℝ ↦ exp (t * x)).aestronglyMeasurable
      hX.aemeasurable).symm
  refine hasCondMGFBound_iff_kernel.2 ⟨fun t ht ↦ ?_, ?_, ?_⟩
  · rw [condExpKernel_comp_trim]
    exact h.integrable_exp_mul ht
  · filter_upwards [h_map] with ω hω t ht
    rw [h_int, hω, ← h_int]
    exact h.integrable_exp_mul ht
  · filter_upwards [h_map] with ω hω t ht
    rw [← mgf_id_map hX.aemeasurable, hω, mgf_id_map hX.aemeasurable]
    exact h.mgf_le ht

end Indep

end LMLExplore
