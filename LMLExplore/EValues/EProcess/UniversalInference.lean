/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Confidence.Sequence
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.EValues.TestSupermartingale.LikelihoodRatio
public import LMLExplore.EValues.TestSupermartingale.Predictor
public import LMLExplore.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Statlib.Testing.Sequential.Basic

/-!
# Universal inference

Universal inference [WRB20] tests a composite null `S` with no regularity conditions: it divides
the likelihood of an alternative fitted *out of sample* by the maximal likelihood of the null
*in sample*. Let every member `P` of the null be locally dominated by a reference measure `μ`,
`P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n)` for every `n`, let `Q` be a probability measure, for instance
the law of a sequential predictor (Mathlib's `ProbabilityTheory.Kernel.trajMeasure` of its
prediction kernels), with density `q n` with respect to `μ` on `ℱ n`, and let `ℓ n` be
`ℱ n`-measurable and `μ`-almost everywhere at least the density of every member of the null on
`ℱ n`, for instance a null maximum likelihood. Then `q n / ℓ n` is an e-process for `S`
[WRB20, Theorem 9; RW, Proposition 7.18]: under each member `P` it is dominated by the likelihood
ratio process of `Q` against `P`, a test supermartingale for `P`.

No i.i.d. assumption, no parametrization of the null and no absolute continuity of `Q` are
needed; `ℓ n` need not be a maximum, only an upper envelope of the densities of the null. For
i.i.d. nulls on `ℕ → 𝓧`, the density of every member on the observations so far is the product
of its one-observation densities (Statlib's `ProbabilityTheory.rnDeriv_trim_piLE_infinitePi`),
and an envelope of these products suffices.

The e-process gives the anytime-valid p-value of [WRB20, Theorem 10] and, inverted over
parameters, the universal confidence sequence of [WRB20, Theorem 11]. Its fixed-time ancestor is
the split likelihood ratio e-variable [RW, Theorem 5.1; WRB20, Theorem 1]: an alternative density
fitted on one block of data, independent of a second block, evaluated on the second block and
divided by an envelope of the null densities of the second block.

## Main statements

* `ProbabilityTheory.isEProcess_rnDeriv_trim_div`: **universal inference**, the ratio `q n / ℓ n`
  is an e-process [WRB20, Theorem 9; RW, Proposition 7.18].
* `ProbabilityTheory.isEProcess_rnDeriv_trim_div_infinitePi`: the same for an i.i.d. null, with an
  envelope of the products of the densities of the observations.
* `ProbabilityTheory.isPProcess_inv_partialSups_rnDeriv_trim_div`: the anytime-valid p-value
  [WRB20, Theorem 10].
* `ProbabilityTheory.isConfSeq_rnDeriv_trim_div`: the universal confidence sequence
  [WRB20, Theorem 11].
* `ProbabilityTheory.isEVar_div_comp_of_indepFun`: the split likelihood ratio is an e-variable
  [RW, Theorem 5.1; WRB20, Theorem 1].

## Implementation notes

The split likelihood ratio is one round of a sequential predictor (`ProbabilityTheory.HasCondLaw`):
given the first block, the conditional law of the second block is its law, by independence, and
the fitted alternative divided by the envelope is a sub-probability density against it.

## References

* [WRB20] L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, PNAS 117 (2020),
  arXiv:1912.11436.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6.
-/

public section

open MeasureTheory Set Filtration
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {μ Q : Measure Ω}

/-! ### The universal inference e-process -/

section EProcess

variable {S : Set (Measure Ω)} {ℓ : ℕ → Ω → ℝ≥0∞}

/-- **Universal inference** [WRB20, Theorem 9; RW, Proposition 7.18]. Let every member `P` of a
null of probability measures be locally dominated by `μ`, let `Q` be a measure with `Q univ ≤ 1`
(the law of the alternative, for instance of a sequential predictor), and let `ℓ n` be
`ℱ n`-measurable and `μ`-almost everywhere at least the density of every member of the null on
`ℱ n` (for instance a null maximum likelihood). Then the ratio of the density of `Q` with respect
to `μ` on `ℱ n` to `ℓ n` is an e-process for the null. -/
theorem isEProcess_rnDeriv_trim_div (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    [SigmaFiniteFiltration μ ℱ] (hSμ : ∀ P ∈ S, ∀ n, P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n))
    (hQ : Q univ ≤ 1) (hℓ : Adapted ℱ ℓ)
    (hle : ∀ P ∈ S, ∀ n, (P.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ≤ᵐ[μ] ℓ n) :
    IsEProcess (fun n ω ↦ (Q.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ω / ℓ n ω) ℱ S := by
  have : IsFiniteMeasure Q := ⟨hQ.trans_lt ENNReal.one_lt_top⟩
  have hE : Adapted ℱ fun n ω ↦ (Q.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ω / ℓ n ω :=
    fun n ↦ (Measure.measurable_rnDeriv _ _).div (hℓ n)
  refine isEProcess_iff_forall_singleton.2 ⟨hE, fun P hP ↦ ?_⟩
  have := hS P hP
  -- under `P`, the ratio is dominated by the likelihood ratio process of `Q` against `P`
  refine ((isTestSupermartingale_rnDeriv_trim (P := P) (ℱ := ℱ) hQ).isEProcess
    (by rintro _ rfl; infer_instance)).mono_ae hE ?_
  intro n
  rw [quasiSure_singleton]
  refine ae_le_of_ae_le_trim (hm := ℱ.le n) (Measure.rnDeriv_div_ae_le_rnDeriv (hSμ P hP n) ?_)
  -- the envelope holds almost surely for `μ` on `ℱ n`
  exact (StronglyMeasurable.ae_le_trim_iff (ℱ.le n)
    (Measure.measurable_rnDeriv _ _).stronglyMeasurable (hℓ n).stronglyMeasurable).2 (hle P hP n)

/-- **The anytime-valid p-value of universal inference** [WRB20, Theorem 10]. Under the
hypotheses of `ProbabilityTheory.isEProcess_rnDeriv_trim_div`, the inverse of the running maximum
of the universal inference e-process is a p-process: under every member of the null, the
probability that it is ever at most `α` is at most `α`. -/
theorem isPProcess_inv_partialSups_rnDeriv_trim_div (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    [SigmaFiniteFiltration μ ℱ] (hSμ : ∀ P ∈ S, ∀ n, P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n))
    (hQ : Q univ ≤ 1) (hℓ : Adapted ℱ ℓ)
    (hle : ∀ P ∈ S, ∀ n, (P.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ≤ᵐ[μ] ℓ n) :
    IsPProcess (fun n ω ↦ (partialSups
      (fun k ω ↦ (Q.trim (ℱ.le k)).rnDeriv (μ.trim (ℱ.le k)) ω / ℓ k ω) n ω)⁻¹) ℱ S :=
  (isEProcess_rnDeriv_trim_div hS hSμ hQ hℓ hle).isPProcess_inv_partialSups

end EProcess

/-- **The universal confidence sequence** [WRB20, Theorem 11]. For a family of nulls `S θ` of
probability measures locally dominated by `μ`, a measure `Q` with `Q univ ≤ 1` and, for each
parameter `θ`, an adapted envelope `ℓ θ n` of the densities of the members of `S θ` on `ℱ n`, the
parameters whose universal inference e-value is below `α⁻¹` form a confidence sequence at level
`α`. For a parametric model `S θ = {P θ}`, `ℓ θ n` may be the density of `P θ` itself. -/
theorem isConfSeq_rnDeriv_trim_div {Θ : Type*} {S : Θ → Set (Measure Ω)}
    (hS : ∀ θ, ∀ P ∈ S θ, IsProbabilityMeasure P) [SigmaFiniteFiltration μ ℱ]
    (hSμ : ∀ θ, ∀ P ∈ S θ, ∀ n, P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n)) (hQ : Q univ ≤ 1)
    {ℓ : Θ → ℕ → Ω → ℝ≥0∞} (hℓ : ∀ θ, Adapted ℱ (ℓ θ))
    (hle : ∀ θ, ∀ P ∈ S θ, ∀ n, (P.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ≤ᵐ[μ] ℓ θ n)
    (α : ℝ≥0∞) :
    IsConfSeq
      (fun n ω ↦ {θ | (Q.trim (ℱ.le n)).rnDeriv (μ.trim (ℱ.le n)) ω / ℓ θ n ω < α⁻¹}) ℱ S α :=
  isConfSeq_of_isEProcess
    (fun θ ↦ isEProcess_rnDeriv_trim_div (hS θ) (hSμ θ) hQ (hℓ θ) (hle θ)) α

/-! ### I.i.d. nulls -/

section IID

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)} {ν : Measure 𝓧}
  {Q : Measure (ℕ → 𝓧)} {ℓ : ℕ → (ℕ → 𝓧) → ℝ≥0∞}

/-- **Universal inference for an i.i.d. null** [WRB20, Theorem 9; RW, Proposition 7.18]. On
`ℕ → 𝓧` with the filtration `Filtration.piLE` of the observations so far, let `S₁` be a set of
laws on `𝓧` absolutely continuous with respect to a probability measure `ν`, and let `ℓ n` be
adapted and, `ν^ℕ`-almost surely, at least the likelihood `∏ i ≤ n, (P.rnDeriv ν) (ω i)` of every
`P ∈ S₁` (for instance the likelihood at a null maximum likelihood estimate). Then, for every
measure `Q` with `Q univ ≤ 1`, the ratio of the density of `Q` with respect to `ν^ℕ` on the
observations so far to `ℓ n` is an e-process for the i.i.d. null `{P^ℕ | P ∈ S₁}`. -/
theorem isEProcess_rnDeriv_trim_div_infinitePi [IsProbabilityMeasure ν]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hS₁ν : ∀ P ∈ S₁, P ≪ ν) (hQ : Q univ ≤ 1)
    (hℓ : Adapted (piLE (X := fun _ : ℕ ↦ 𝓧)) ℓ)
    (hle : ∀ P ∈ S₁, ∀ n, (fun ω ↦ ∏ i ∈ Finset.Iic n, P.rnDeriv ν (ω i))
      ≤ᵐ[Measure.infinitePi fun _ : ℕ ↦ ν] ℓ n) :
    IsEProcess (fun n ω ↦ (Q.trim ((piLE (X := fun _ : ℕ ↦ 𝓧)).le n)).rnDeriv
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim ((piLE (X := fun _ : ℕ ↦ 𝓧)).le n)) ω / ℓ n ω)
      piLE (iidNull S₁) := by
  refine isEProcess_rnDeriv_trim_div (isProbabilityMeasure_of_mem_iidNull hS₁)
    (forall_mem_iidNull.2 fun P hP n ↦ ?_) hQ hℓ (forall_mem_iidNull.2 fun P hP n ↦ ?_)
  · have := hS₁ P hP
    exact absolutelyContinuous_trim_piLE_infinitePi (hS₁ν P hP) n
  · have := hS₁ P hP
    -- the density of `P^ℕ` on the observations so far is the product of the densities of `P`
    filter_upwards [ae_of_ae_trim _ (rnDeriv_trim_piLE_infinitePi (μ := P) (ν := ν) n),
      hle P hP n] with ω h1 h2
    exact h1.le.trans h2

end IID

/-! ### The split likelihood ratio -/

section Split

variable {𝓨 𝓩 : Type*} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩} {S : Set (Measure Ω)}
  {D₀ : Ω → 𝓨} {D₁ : Ω → 𝓩} {ν : Measure 𝓨}

/-- **The split likelihood ratio is an e-variable** [RW, Theorem 5.1; WRB20, Theorem 1].
Let the data be split into two blocks `D₀` and `D₁`, independent under every member of a null of
probability measures, with the law of `D₀` absolutely continuous with respect to a σ-finite
measure `ν`. Let `q z` be a sub-probability density with respect to `ν`, the alternative fitted on
the value `z` of `D₁`, and let `ℓ` be `ν`-almost everywhere at least the density of the law of
`D₀` under every member of the null (for instance the likelihood at a null maximum likelihood
estimate computed on `D₀`). Then `q D₁ D₀ / ℓ D₀` is an e-variable for the null. -/
theorem isEVar_div_comp_of_indepFun [SigmaFinite ν] (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hD₀ : Measurable D₀) (hD₁ : Measurable D₁) (hind : ∀ P ∈ S, IndepFun D₀ D₁ P)
    (hSν : ∀ P ∈ S, P.map D₀ ≪ ν) {ℓ : 𝓨 → ℝ≥0∞} (hℓ : Measurable ℓ)
    (hle : ∀ P ∈ S, (P.map D₀).rnDeriv ν ≤ᵐ[ν] ℓ) {q : 𝓩 → 𝓨 → ℝ≥0∞}
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ z, ∫⁻ y, q z y ∂ν ≤ 1) :
    IsEVar (fun ω ↦ q (D₁ ω) (D₀ ω) / ℓ (D₀ ω)) S := by
  refine ⟨(hq.comp (hD₁.prodMk hD₀)).div (hℓ.comp hD₀), fun P hP ↦ ?_⟩
  have := hS P hP
  -- the prediction fitted on `D₁`, a function of `D₁` and of the value of `D₀`
  let r : Ω → 𝓨 → ℝ≥0∞ := fun ω y ↦ q (D₁ ω) y / ℓ y
  have hr : Measurable[(m𝓩.comap D₁).prod m𝓨] (Function.uncurry r) := by
    let : MeasurableSpace Ω := m𝓩.comap D₁
    exact (hq.comp (((comap_measurable D₁).comp measurable_fst).prodMk measurable_snd)).div
      (hℓ.comp measurable_snd)
  -- given `D₁`, the conditional law of `D₀` is its law
  have hlaw : HasCondLaw D₀ (fun _ ↦ P.map D₀) (m𝓩.comap D₁) P :=
    hasCondLaw_of_indep hD₁.comap_le ((IndepFun_iff_Indep _ _ _).1 (hind P hP))
      ⟨hD₀.aemeasurable, rfl⟩
  -- and the prediction is a sub-probability density against this law
  have hr1 (ω : Ω) : ∫⁻ y, r ω y ∂(P.map D₀) ≤ 1 := by
    rw [← lintegral_rnDeriv_mul (hSν P hP) (f := r ω) (hq.of_uncurry_left.div hℓ).aemeasurable]
    refine (lintegral_mono_ae ?_).trans (hq1 (D₁ ω))
    filter_upwards [hle P hP] with y hy
    calc (P.map D₀).rnDeriv ν y * (q (D₁ ω) y / ℓ y)
        ≤ ℓ y * (q (D₁ ω) y / ℓ y) := by gcongr
      _ ≤ q (D₁ ω) y := ENNReal.mul_div_le
  exact ((hlaw.isCondEVar_comp hD₁.comap_le hD₀ hr (ae_of_all _ hr1)).isEVar
    (by simp)).lintegral_le_one (mem_singleton P)

end Split

end ProbabilityTheory
