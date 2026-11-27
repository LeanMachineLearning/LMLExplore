/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.ProductMeasure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
import LMLExplore.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.RadonNikodym
import Statlib.Divergence.KullbackLeibler.Basic
import TauCeti.Probability.StrongLaw

/-!
# Mixtures of i.i.d. laws over a Kullback–Leibler support dominate an exponential density

Let `ν` be a finite measure on the measures on `𝓧` that charges only probability measures (a
prior), and `Q` a probability measure such that `ν` charges every Kullback–Leibler neighbourhood
`{R | klDiv Q R ≤ ε}` of `Q`. The mixtures `∫ R ^ n ν(dR)` of the i.i.d. laws, that is
`ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R`, then lose at most a subexponential factor against
the i.i.d. law `Q ^ n`: this is Barron's argument for the consistency of posterior distributions
[Bar88], [BSW99].

* **The mixture dominates an exponential density.** On a countably generated space, there are
  `c > 0` and an integrable `g` with `∫ g ∂Q ≥ -ε` such that the mixture dominates the measure of
  density `c exp (∑ i, g (y i))` with respect to `Q ^ n`, for every `n`. Take a measurable set `B`
  of alternatives of positive `ν`-measure at relative entropy at most `ε` from `Q`, a version of
  the densities `dR / dQ` that is measurable in both variables (Mathlib's `Kernel.rnDeriv`, which
  needs the countable generation), `c = ν B` and `g` the average over `B` of their logarithms, and
  apply Jensen's inequality to `R ↦ ∏ i, (dR / dQ) (y i)`.
* **Functions of bounded mean under the mixtures grow subexponentially.** If the functions `ψ n`
  of `n` observations have mean at most `C < ∞` under the mixtures, then almost surely under the
  i.i.d. law of `Q`, `ψ n ≤ exp (n ε)` at the first `n` observations for all large `n`. On a
  countably generated space, this follows from the domination by Markov's inequality, the
  Borel–Cantelli lemma and the strong law of large numbers for `g`. On a general space, the
  functions `ψ n` factor through `x ↦ (i ↦ φ (x i))` for one measurable `φ : 𝓧 → ℕ → Bool`
  (`MeasurableSpace.exists_measurable_forall_eq_measurable_comp_piMap`), whose target is
  countably generated; the image of the mixture under this map is the mixture of the images, and
  the relative entropy decreases under `φ` (`InformationTheory.klDiv_map_le`), so the image of
  `ν` charges every Kullback–Leibler neighbourhood of the image of `Q`.

## Main statements

* `ProbabilityTheory.exists_lintegral_mul_le_lintegral_bind`: on a countably generated space, the
  mixture `∫ R ^ n ν(dR)` dominates `c exp (∑ i, g (y i))` times `Q ^ n`, with `∫ g ∂Q ≥ -ε`.
* `ProbabilityTheory.ae_eventually_le_exp_of_lintegral_bind_le`: functions of bounded mean under
  the mixtures are eventually at most `exp (n ε)`, almost surely under the i.i.d. law of `Q`.

## Implementation notes

The countable generation in `exists_lintegral_mul_le_lintegral_bind` provides the jointly
measurable densities `Kernel.rnDeriv`; the subexponential growth needs none, as it concerns only
countably many functions. The statements and proofs are adapted from
`EValuesResearch/Results/Numeraire.lean`, `EValuesResearch/Results/NumeraireBarronAux.lean` and
`EValuesResearch/Results/NumeraireTrimAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, where they are steps of the proof of [EVR26, Note 14,
Theorem (2)], rewritten on the API of LMLExplore.

## References

* [Bar88] A. R. Barron, *The exponential convergence of posterior probabilities with implications
  for Bayes estimators of density functions*, Technical report, Department of Statistics,
  University of Illinois at Urbana-Champaign, 1988.
* [BSW99] A. Barron, M. J. Schervish and L. Wasserman, *The consistency of posterior distributions
  in nonparametric problems*, Annals of Statistics 27 (1999), 536–561.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 14, *Asymptotic log-optimality of the mixture numeraire*,
  Theorem (2).
-/

public section

open MeasureTheory Filter InformationTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### The domination of the mixture on a countably generated space -/

section CountablyGenerated

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}

/-- The kernel from the measures on `𝓨` to `𝓨` that sends a probability measure to itself and
every other measure to `0`. -/
private noncomputable def probKernel (𝓨 : Type*) [MeasurableSpace 𝓨] :
    Kernel (Measure 𝓨) 𝓨 where
  toFun R := if R .univ = 1 then R else 0
  measurable' := Measurable.ite (Measure.measurable_coe .univ (measurableSet_singleton 1))
    measurable_id measurable_const

/-- The value of `probKernel 𝓨` at a measure `R`: `R` itself if `R` has mass `1`, else `0`. -/
private lemma probKernel_def (R : Measure 𝓨) :
    probKernel 𝓨 R = if R .univ = 1 then R else 0 := (rfl)

/-- `probKernel 𝓨` sends a probability measure to itself. -/
private lemma probKernel_apply (R : Measure 𝓨) [IsProbabilityMeasure R] : probKernel 𝓨 R = R := by
  simp [probKernel_def]

/-- `probKernel 𝓨` is a finite kernel. -/
private instance isFiniteKernel_probKernel : IsFiniteKernel (probKernel 𝓨) :=
  ⟨⟨1, ENNReal.one_lt_top, fun R ↦ by
    rw [probKernel_def]
    split_ifs with h
    · exact h.le
    · simp⟩⟩

/-- **The mixture dominates an exponential density** [Bar88], [BSW99], on a countably generated
space. If `ν` charges every Kullback–Leibler neighbourhood of `Q`, there are `c > 0` and an
integrable `g` with `∫ g ∂Q ≥ -ε` such that, for every `n`, the mixture `∫ R ^ n ν(dR)` dominates
the measure of density `c exp (∑ i, g (y i))` with respect to `Q ^ n`, in the form of an
inequality between the integrals of every measurable `ψ ≥ 0`. Take a measurable set `B` of
probability measures of positive `ν`-measure at relative entropy at most `ε` from `Q`, `c = ν B`,
and for `g` the average over `B` of the logarithm of a jointly measurable version `r` of the
densities `dR / dQ`, and apply Jensen's inequality
(`MeasureTheory.ofReal_measureReal_mul_exp_average_le_lintegral`) to `R ↦ ∏ i, r R (y i)`. The
countable generation of `𝓨` makes the densities jointly measurable. -/
lemma exists_lintegral_mul_le_lintegral_bind [MeasurableSpace.CountablyGenerated 𝓨]
    (Q : Measure 𝓨) [IsProbabilityMeasure Q] (ν : Measure (Measure 𝓨)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ R ∂ν, IsProbabilityMeasure R)
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {R | klDiv Q R ≤ ε} ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : 𝓨 → ℝ, Measurable g ∧ Integrable g Q ∧ -ε ≤ ∫ y, g y ∂Q ∧
      ∀ (n : ℕ) (ψ : (Fin n → 𝓨) → ℝ≥0∞), Measurable ψ →
        ∫⁻ y, ψ y * ENNReal.ofReal (c * Real.exp (∑ i, g (y i))) ∂Measure.pi (fun _ ↦ Q) ≤
          ∫⁻ y, ψ y ∂ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R := by
  -- a measurable set `B` of alternatives of positive mass, at relative entropy at most `ε`
  set P : Set (Measure 𝓨) := {R | IsProbabilityMeasure R}
  have hPm : MeasurableSet P := ProbabilityMeasure.measurableSet_isProbabilityMeasure
  have hKLm : Measurable fun R ↦ klDiv Q (probKernel 𝓨 R) := by
    simpa only [Kernel.const_apply] using measurable_klDiv (Kernel.const (Measure 𝓨) Q)
      (probKernel 𝓨)
  set B : Set (Measure 𝓨) := P ∩ {R | klDiv Q (probKernel 𝓨 R) ≤ ENNReal.ofReal ε}
  have hBm : MeasurableSet B := hPm.inter (measurableSet_le hKLm measurable_const)
  have hB (R : Measure 𝓨) (hR : R ∈ B) :
      IsProbabilityMeasure R ∧ klDiv Q R ≤ ENNReal.ofReal ε := by
    have : IsProbabilityMeasure R := hR.1
    refine ⟨this, ?_⟩
    have h := hR.2
    rwa [Set.mem_ofPred_eq, probKernel_apply] at h
  have hνB : ν B ≠ 0 := by
    intro h0
    refine hν_supp _ (ENNReal.ofReal_pos.2 hε)
      (measure_mono_null (fun R hR ↦ ?_) (measure_union_null h0 (ae_iff.1 hν)))
    by_cases h : IsProbabilityMeasure R
    · refine Or.inl ⟨h, ?_⟩
      rw [Set.mem_ofPred_eq, probKernel_apply]
      exact hR
    · exact Or.inr h
  set π := ν.restrict B
  set c := ν.real B
  have hc : 0 < c := ENNReal.toReal_pos hνB (measure_ne_top _ _)
  have hπ : π.real .univ = c := by
    simp only [π, c, measureReal_def, Measure.restrict_apply_univ]
  -- a jointly measurable version `r` of the densities, and its logarithm `ℓ`
  set r := Kernel.rnDeriv (probKernel 𝓨) (Kernel.const (Measure 𝓨) Q)
  have hrm : Measurable fun p : Measure 𝓨 × 𝓨 ↦ r p.1 p.2 := Kernel.measurable_rnDeriv _ _
  have hrle (R : Measure 𝓨) [IsProbabilityMeasure R] : Q.withDensity (r R) ≤ R := by
    refine Measure.le_iff.2 fun s hs ↦ ?_
    rw [withDensity_apply _ hs]
    have h := Kernel.setLIntegral_rnDeriv_le (κ := probKernel 𝓨)
      (η := Kernel.const (Measure 𝓨) Q) (a := R) hs
    rwa [Kernel.const_apply, probKernel_apply] at h
  have hrae (R : Measure 𝓨) [IsProbabilityMeasure R] : r R =ᵐ[Q] R.rnDeriv Q := by
    have h := Kernel.rnDeriv_eq_rnDeriv_measure (κ := probKernel 𝓨)
      (η := Kernel.const (Measure 𝓨) Q) (a := R)
    rwa [Kernel.const_apply, probKernel_apply] at h
  set ℓ : Measure 𝓨 × 𝓨 → ℝ := fun p ↦ Real.log (r p.1 p.2).toReal
  have hℓm : Measurable ℓ := Real.measurable_log.comp (ENNReal.measurable_toReal.comp hrm)
  -- the logarithm of the density of a member of `B`
  have hfacts (R : Measure 𝓨) (hR : R ∈ B) : Integrable (fun y ↦ ℓ (R, y)) Q ∧
      -ε ≤ ∫ y, ℓ (R, y) ∂Q ∧ ∫ y, |ℓ (R, y)| ∂Q ≤ ε + 2 ∧ ∀ᵐ y ∂Q, r R y ≠ 0 := by
    obtain ⟨hRp, hKL⟩ := hB R hR
    obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL)
    have hKLε : (klDiv Q R).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hKL
    have hKLeq : (klDiv Q R).toReal = ∫ y, llr Q R y ∂Q :=
      toReal_klDiv_of_measure_eq hac (by simp)
    have hℓ : (fun y ↦ ℓ (R, y)) =ᵐ[Q] fun y ↦ -llr Q R y := by
      filter_upwards [hrae R, neg_llr hac] with y h1 h2
      simp only [ℓ, h1]
      exact h2.symm
    refine ⟨hllr.neg.congr hℓ.symm, ?_, ?_, ?_⟩
    · rw [integral_congr_ae hℓ, integral_neg, ← hKLeq]
      linarith
    · have habs := integral_abs_llr_le hac hllr
      rw [← hKLeq, probReal_univ] at habs
      rw [integral_congr_ae (g := fun y ↦ |llr Q R y|) (hℓ.mono fun y h ↦ by
        dsimp only at h ⊢
        rw [h, abs_neg])]
      linarith
    · filter_upwards [hrae R, Measure.rnDeriv_pos' hac] with y h1 h2
      rw [h1]
      exact h2.ne'
  -- `ℓ` is integrable on `B × 𝓨`
  have hint : Integrable ℓ (π.prod Q) := by
    rw [integrable_prod_iff hℓm.aestronglyMeasurable]
    refine ⟨(ae_restrict_mem hBm).mono fun R hR ↦ (hfacts R hR).1, ?_⟩
    refine Integrable.of_bound
      (hℓm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      (ε + 2) ((ae_restrict_mem hBm).mono fun R hR ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    simpa only [Real.norm_eq_abs] using (hfacts R hR).2.2.1
  -- the function `g`, the average over `B` of `ℓ`
  set g : 𝓨 → ℝ := fun y ↦ c⁻¹ * ∫ R, ℓ (R, y) ∂π
  have hgm : Measurable g :=
    (hℓm.stronglyMeasurable.integral_prod_left' (μ := π)).measurable.const_mul _
  have hgi : Integrable g Q := hint.integral_prod_right.const_mul _
  have hgε : -ε ≤ ∫ y, g y ∂Q := by
    have hlow : -ε * c ≤ ∫ R, ∫ y, ℓ (R, y) ∂Q ∂π := by
      calc -ε * c = ∫ _, -ε ∂π := by rw [integral_const, hπ, smul_eq_mul, mul_comm]
      _ ≤ ∫ R, ∫ y, ℓ (R, y) ∂Q ∂π := integral_mono_ae (integrable_const _)
          hint.integral_prod_left ((ae_restrict_mem hBm).mono fun R hR ↦ (hfacts R hR).2.1)
    simp only [g]
    rw [integral_const_mul, ← integral_integral_swap hint, ← div_le_iff₀' (inv_pos.2 hc),
      div_eq_mul_inv, inv_inv]
    linarith
  refine ⟨c, hc, g, hgm, hgi, hgε, fun n ψ hψ ↦ ?_⟩
  -- the products of the densities over the coordinates
  set ρ : Measure 𝓨 → (Fin n → 𝓨) → ℝ≥0∞ := fun R y ↦ ∏ i, r R (y i)
  have hρm : Measurable fun p : Measure 𝓨 × (Fin n → 𝓨) ↦ ρ p.1 p.2 :=
    Finset.measurable_prod _ fun i _ ↦
      hrm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hρle (R : Measure 𝓨) (hR : R ∈ B) :
      ∫⁻ y, ψ y * ρ R y ∂Measure.pi (fun _ : Fin n ↦ Q) ≤
        ∫⁻ y, ψ y ∂Measure.pi (fun _ : Fin n ↦ R) := by
    have := (hB R hR).1
    have hrRm : Measurable (r R) := Kernel.measurable_rnDeriv_right _ _ R
    have hρRm : Measurable (ρ R) :=
      Finset.measurable_prod _ fun i _ ↦ hrRm.comp (measurable_pi_apply i)
    calc ∫⁻ y, ψ y * ρ R y ∂Measure.pi (fun _ : Fin n ↦ Q)
    _ = ∫⁻ y, ψ y ∂(Measure.pi fun _ : Fin n ↦ Q).withDensity (ρ R) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hρRm hψ]
      exact lintegral_congr fun y ↦ mul_comm _ _
    _ ≤ ∫⁻ y, ψ y ∂Measure.pi fun _ : Fin n ↦ R :=
      lintegral_mono' (Measure.withDensity_prod_le_pi (fun _ ↦ hrRm) fun _ ↦ hrle R) le_rfl
  -- the coordinates at which the densities are positive and their logarithms integrable
  have hgood : ∀ᵐ y ∂Q, (∀ᵐ R ∂π, r R y ≠ 0) ∧ Integrable (fun R ↦ ℓ (R, y)) π := by
    have hset : MeasurableSet {p : Measure 𝓨 × 𝓨 | r p.1 p.2 ≠ 0} :=
      hrm (measurableSet_singleton 0).compl
    have h1 : ∀ᵐ y ∂Q, ∀ᵐ R ∂π, r R y ≠ 0 := by
      rw [← Measure.ae_ae_comm hset]
      exact (ae_restrict_mem hBm).mono fun R hR ↦ (hfacts R hR).2.2.2
    filter_upwards [h1, ((integrable_prod_iff' hℓm.aestronglyMeasurable).1 hint).1]
      with y hy1 hy2 using ⟨hy1, hy2⟩
  -- Jensen's inequality at these coordinates
  have hjensen : ∀ᵐ y ∂Measure.pi (fun _ : Fin n ↦ Q),
      ENNReal.ofReal (c * Real.exp (∑ i, g (y i))) ≤ ∫⁻ R, ρ R y ∂π := by
    filter_upwards [ae_all_iff.2 fun i : Fin n ↦
      (Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ Q)).eventually hgood] with y hy
    set H : Measure 𝓨 → ℝ := fun R ↦ ∑ i, ℓ (R, y i)
    have hHi : Integrable H π := integrable_finsetSum _ fun i _ ↦ (hy i).2
    have hρH : ∀ᵐ R ∂π, ENNReal.ofReal (Real.exp (H R)) ≤ ρ R y := by
      filter_upwards [ae_all_iff.2 fun i ↦ (hy i).1] with R hR
      simp only [H, ρ, ℓ]
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
      refine Finset.prod_le_prod fun i _ ↦ ?_
      rcases eq_or_ne (r R (y i)) ∞ with htop | htop
      · exact htop ▸ le_top
      rw [Real.exp_log (ENNReal.toReal_pos (hR i) htop), ENNReal.ofReal_toReal htop]
    have hHavg : ⨍ R, H R ∂π = ∑ i, g (y i) := by
      simp only [H, g]
      rw [average_eq, hπ, integral_finsetSum _ fun i _ ↦ (hy i).2, smul_eq_mul, Finset.mul_sum]
    calc ENNReal.ofReal (c * Real.exp (∑ i, g (y i)))
    _ = ENNReal.ofReal (π.real .univ * Real.exp (⨍ R, H R ∂π)) := by rw [hπ, hHavg]
    _ ≤ ∫⁻ R, ENNReal.ofReal (Real.exp (H R)) ∂π :=
      ofReal_measureReal_mul_exp_average_le_lintegral hHi
    _ ≤ ∫⁻ R, ρ R y ∂π := lintegral_mono_ae hρH
  -- conclusion
  calc ∫⁻ y, ψ y * ENNReal.ofReal (c * Real.exp (∑ i, g (y i))) ∂Measure.pi (fun _ ↦ Q)
  _ ≤ ∫⁻ y, ψ y * ∫⁻ R, ρ R y ∂π ∂Measure.pi (fun _ ↦ Q) :=
    lintegral_mono_ae (hjensen.mono fun y hy ↦ by gcongr)
  _ = ∫⁻ y, ∫⁻ R, ψ y * ρ R y ∂π ∂Measure.pi (fun _ ↦ Q) := lintegral_congr fun y ↦
    (lintegral_const_mul _ (hρm.comp (measurable_id.prodMk measurable_const))).symm
  _ = ∫⁻ R, ∫⁻ y, ψ y * ρ R y ∂Measure.pi (fun _ ↦ Q) ∂π :=
    lintegral_lintegral_swap ((hψ.comp measurable_fst).mul
      (hρm.comp measurable_swap)).aemeasurable
  _ ≤ ∫⁻ R, ∫⁻ y, ψ y ∂Measure.pi (fun _ : Fin n ↦ R) ∂π :=
    lintegral_mono_ae ((ae_restrict_mem hBm).mono fun R hR ↦ hρle R hR)
  _ ≤ ∫⁻ R, ∫⁻ y, ψ y ∂Measure.pi (fun _ : Fin n ↦ R) ∂ν :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  _ = ∫⁻ y, ψ y ∂ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R :=
    (Measure.lintegral_bind (Measure.aemeasurable_pi_self (hν.mono fun _ _ ↦ inferInstance))
      hψ.aemeasurable).symm

/-- `ae_eventually_le_exp_of_lintegral_bind_le` on a countably generated space: the domination of
the mixture (`exists_lintegral_mul_le_lintegral_bind`), Markov's inequality, the Borel–Cantelli
lemma and the strong law of large numbers. -/
private lemma ae_eventually_le_exp_of_lintegral_bind_le_of_countablyGenerated
    [MeasurableSpace.CountablyGenerated 𝓨]
    (Q : Measure 𝓨) [IsProbabilityMeasure Q] (ν : Measure (Measure 𝓨)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ R ∂ν, IsProbabilityMeasure R)
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {R | klDiv Q R ≤ ε} ≠ 0)
    {ψ : (n : ℕ) → (Fin n → 𝓨) → ℝ≥0∞} (hψ : ∀ n, Measurable (ψ n)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hψC : ∀ n, ∫⁻ y, ψ n y ∂(ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R) ≤ C) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ᶠ n : ℕ in atTop,
      ψ n (initSeg n ω) ≤ ENNReal.ofReal (Real.exp (n * ε)) := by
  obtain ⟨c, hc, g, hgm, hgi, hgε, hdom⟩ :=
    exists_lintegral_mul_le_lintegral_bind Q ν hν hν_supp (by positivity : (0 : ℝ) < ε / 4)
  set h : (n : ℕ) → (Fin n → 𝓨) → ℝ≥0∞ := fun n y ↦
    ENNReal.ofReal (c * Real.exp (∑ i, g (y i)))
  have hhm (n : ℕ) : Measurable (h n) := ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun i _ ↦ hgm.comp (measurable_pi_apply i))))
  -- the strong law of large numbers for `g`
  have hlt : -(3 * ε / 8) < ∫ y, g y ∂Q := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * |Real.log c| / ε)
  -- Markov's inequality and the Borel–Cantelli lemma for `ψ n * h n`
  filter_upwards [ae_eventually_lt_exp_of_lintegral_le Q (F := fun n y ↦ ψ n y * h n y)
      (fun n ↦ ((hψ n).mul (hhm n)).aemeasurable) hC
      (fun n ↦ (hdom n (ψ n) (hψ n)).trans (hψC n)) (half_pos hε),
    TauCeti.Probability.strong_law_ae_infinitePi Q hgi] with ω hω1 hω2
  filter_upwards [hω1, hω2.eventually (lt_mem_nhds hlt), eventually_ge_atTop (N + 1)]
    with n hn1 hn2 hn3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos N).trans_le hn3
  rw [smul_eq_mul, lt_inv_mul_iff₀ hn0] at hn2
  -- `h n ≥ exp (-n ε / 2)` at the first `n` observations
  have hlogc : -(n * ε / 8) ≤ Real.log c := by
    have hNn : (N : ℝ) < n := by exact_mod_cast (Nat.lt_succ_self N).trans_le hn3
    have := (div_lt_iff₀ hε).1 (hN.trans hNn)
    have habs := neg_abs_le (Real.log c)
    nlinarith
  have hh : ENNReal.ofReal (Real.exp (-(n * (ε / 2)))) ≤ h n (initSeg n ω) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hsumg : ∑ i, g (initSeg n ω i) = ∑ i ∈ Finset.range n, g (ω i) :=
      by simpa only [initSeg_apply] using Fin.sum_univ_eq_sum_range (fun i ↦ g (ω i)) n
    rw [hsumg, ← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  -- conclusion
  have hexp : ENNReal.ofReal (Real.exp (-(n * (ε / 2)))) *
      ENNReal.ofReal (Real.exp (n * (ε / 2))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc ψ n (initSeg n ω)
  _ = ψ n (initSeg n ω) * ENNReal.ofReal (Real.exp (-(n * (ε / 2)))) *
      ENNReal.ofReal (Real.exp (n * (ε / 2))) := by rw [mul_assoc, hexp, mul_one]
  _ ≤ ENNReal.ofReal (Real.exp (n * (ε / 2))) * ENNReal.ofReal (Real.exp (n * (ε / 2))) := by
    gcongr
    calc ψ n (initSeg n ω) * ENNReal.ofReal (Real.exp (-(n * (ε / 2))))
    _ ≤ ψ n (initSeg n ω) * h n (initSeg n ω) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (n * (ε / 2))) := hn1.le
  _ = ENNReal.ofReal (Real.exp (n * ε)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf

end CountablyGenerated

/-! ### Subexponential growth on a general space -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- **Functions of bounded mean under the mixtures grow subexponentially** [Bar88], [BSW99]. If
`ν` charges every Kullback–Leibler neighbourhood of `Q`, and the functions `ψ n` of `n`
observations have mean at most `C < ∞` under the mixtures `∫ R ^ n ν(dR)`, then for every
`ε > 0`, almost surely under the i.i.d. law of `Q`, `ψ n ≤ exp (n ε)` at the first `n`
observations for all large `n`. No assumption is made on `𝓧`: the `ψ n` factor through Boolean
coordinates `x ↦ (i ↦ φ (x i))` of the observations, which reduces the statement to the countably
generated space `ℕ → Bool`, where it follows from the domination of the mixture
(`exists_lintegral_mul_le_lintegral_bind`), Markov's inequality, the Borel–Cantelli lemma and the
strong law of large numbers. -/
theorem ae_eventually_le_exp_of_lintegral_bind_le (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν] (hν : ∀ᵐ R ∂ν, IsProbabilityMeasure R)
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {R | klDiv Q R ≤ ε} ≠ 0)
    {ψ : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞} (hψ : ∀ n, Measurable (ψ n)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hψC : ∀ n, ∫⁻ y, ψ n y ∂(ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R) ≤ C) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ᶠ n : ℕ in atTop,
      ψ n (initSeg n ω) ≤ ENNReal.ofReal (Real.exp (n * ε)) := by
  -- the functions factor through Boolean coordinates
  obtain ⟨φ, hφ, ψ', hψ', hψψ'⟩ :=
    MeasurableSpace.exists_measurable_forall_eq_measurable_comp_piMap hψ
  -- the images of the alternatives under `φ`
  have hmap : Measurable fun R : Measure 𝓧 ↦ R.map φ := Measure.measurable_map φ hφ
  set ν' : Measure (Measure (ℕ → Bool)) := ν.map fun R ↦ R.map φ
  have hν' : ∀ᵐ R ∂ν', IsProbabilityMeasure R :=
    (ae_map_iff hmap.aemeasurable ProbabilityMeasure.measurableSet_isProbabilityMeasure).2
      (hν.mono fun _ _ ↦ inferInstance)
  have hν'_supp (δ : ℝ≥0∞) (hδ : 0 < δ) : ν' {R | klDiv (Q.map φ) R ≤ δ} ≠ 0 := by
    intro h0
    have h1 : ν ((fun R ↦ R.map φ) ⁻¹' {R' | klDiv (Q.map φ) R' ≤ δ}) = 0 :=
      nonpos_iff_eq_zero.1 (h0 ▸ Measure.le_map_apply hmap.aemeasurable _)
    refine hν_supp δ hδ (measure_mono_null (fun R hR ↦ ?_) (measure_union_null h1 (ae_iff.1 hν)))
    by_cases hp : IsProbabilityMeasure R
    · exact Or.inl ((klDiv_map_le Q R hφ).trans hR)
    · exact Or.inr hp
  -- the means of the factors under the mixtures of the images
  have hbound (n : ℕ) :
      ∫⁻ y, ψ' n y ∂(ν'.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R) ≤ C := by
    have hκ' : AEMeasurable (fun R : Measure (ℕ → Bool) ↦ Measure.pi fun _ : Fin n ↦ R) ν' :=
      Measure.aemeasurable_pi_self (hν'.mono fun _ _ ↦ inferInstance)
    have hΦ : Measurable fun (x : Fin n → 𝓧) (i : Fin n) ↦ φ (x i) :=
      .of_eval fun i ↦ hφ.comp (measurable_pi_apply i)
    calc ∫⁻ y, ψ' n y ∂(ν'.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R)
    _ = ∫⁻ R, ∫⁻ y, ψ' n y ∂Measure.pi (fun _ : Fin n ↦ R) ∂ν' :=
      Measure.lintegral_bind hκ' (hψ' n).aemeasurable
    _ = ∫⁻ R, ∫⁻ y, ψ' n y ∂Measure.pi (fun _ : Fin n ↦ R.map φ) ∂ν :=
      lintegral_map' ((Measure.measurable_lintegral (hψ' n)).comp_aemeasurable hκ')
        hmap.aemeasurable
    _ = ∫⁻ R, ∫⁻ x, ψ n x ∂Measure.pi (fun _ : Fin n ↦ R) ∂ν := by
      refine lintegral_congr_ae (hν.mono fun R hR ↦ ?_)
      have hpi : (Measure.pi fun _ : Fin n ↦ R).map (fun x i ↦ φ (x i)) =
          Measure.pi fun _ : Fin n ↦ R.map φ := Measure.pi_map_pi fun _ ↦ hφ.aemeasurable
      dsimp only
      rw [← hpi, lintegral_map (hψ' n) hΦ]
      exact lintegral_congr fun x ↦ (congr_fun (hψψ' n) x).symm
    _ = ∫⁻ x, ψ n x ∂(ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R) :=
      (Measure.lintegral_bind (Measure.aemeasurable_pi_self (hν.mono fun _ _ ↦ inferInstance))
        (hψ n).aemeasurable).symm
    _ ≤ C := hψC n
  -- the bound on the images, pulled back to the observations
  have h1 := ae_eventually_le_exp_of_lintegral_bind_le_of_countablyGenerated (Q.map φ) ν' hν'
    hν'_supp hψ' hC hbound hε
  filter_upwards [Measure.ae_of_ae_infinitePi_map (fun _ : ℕ ↦ Q) (fun _ ↦ hφ) h1] with ω hω
  filter_upwards [hω] with n hn
  have hseg : (fun i ↦ φ (initSeg n ω i)) = initSeg n fun i ↦ φ (ω i) :=
    funext fun i ↦ by simp only [initSeg_apply]
  rw [congr_fun (hψψ' n) (initSeg n ω), Function.comp_apply, hseg]
  exact hn

end ProbabilityTheory
