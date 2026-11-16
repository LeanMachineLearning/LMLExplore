/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.Probability.ProductMeasure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.EProcess
import LMLExplore.EValues.BipolarRate.Numeraire
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
import LMLExplore.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.RadonNikodym
import Statlib.Divergence.KullbackLeibler.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.StrongLaw

/-!
# The numeraires against a mixture of i.i.d. alternatives grow at the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null), and `ν` a finite measure on the
measures on `𝓧` that charges only probability measures (a prior on the alternatives). The
observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`. Write `W n` for Statlib's `numeraire` of the `n`-sample null
`{P ^ n | P ∈ S₁}` under the mixture `∫ Q' ^ n ν(dQ')`, that is `ν.bind fun Q' ↦ Q' ^ n`: the
log-optimal `n`-sample e-variable against the mixture of the i.i.d. alternatives. If `ν` charges
every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}` of a law `Q₁`, then almost surely
under the i.i.d. law of `Q₁`, `(1/n) log (W n)`, at the first `n` observations, tends to the
bipolar rate `bipolarRate Q₁ S₁`, also when it is infinite [EVR26, Note 14]. This is the
asymptotic log-optimality of the mixture numeraires that [RW, Chapter 6] conjectures, with the
rate `bipolarRate Q₁ S₁` of [RR26]: one sequence of `n`-sample e-variables, which does not depend
on `Q₁`, grows at the optimal rate of every alternative in the Kullback–Leibler support of `ν`.
Nothing is assumed on `𝓧`, and nothing on `S₁` besides that its members are probability
measures.

The upper bound holds for every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`). For the lower bound, it is enough that
`W` keeps up with every sequence of `n`-sample e-variables `M n`: almost surely,
`log (M n) ≤ log (W n) + n ε` for all large `n`, for every `ε > 0`
(`ProbabilityTheory.ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le`).

* **The ratio to the mixture numeraire.** `M n / W n` has mean at most the mass of `ν` under the
  mixture, by the defining property of the numeraire.
* **The mixture dominates an exponential density.** On a countably generated space, there are
  `c > 0` and an integrable `g` with `∫ g ∂Q₁ ≥ -ε` such that the mixture dominates the measure
  of density `c exp (∑ i, g (x i))` with respect to `Q₁ ^ n`, for every `n`. Take a measurable
  set `B` of alternatives of positive `ν`-measure at relative entropy at most `ε` from `Q₁`, a
  version of the densities `dQ' / dQ₁` that is measurable in both variables (Mathlib's
  `Kernel.rnDeriv`, which needs the countable generation), `c = ν B` and `g` the average over `B`
  of their logarithms, and apply Jensen's inequality to `Q' ↦ ∏ i, (dQ' / dQ₁) (x i)`. Markov's
  inequality, the Borel–Cantelli lemma and the strong law of large numbers for `g` then give
  `M n / W n ≤ exp (n ε)` for all large `n`, almost surely.
* **A general space.** Countably many measurable functions of the observations, here the ratios
  `M n / W n`, factor through `x ↦ (i ↦ φ (x i))` for one measurable `φ : 𝓧 → ℕ → Bool`
  (`MeasurableSpace.exists_measurable_forall_eq_measurable_comp_piMap`), whose target is
  countably generated. The image of the mixture under this map is the mixture of the images, and
  the relative entropy decreases under `φ` (`InformationTheory.klDiv_map_le`), so the image of
  `ν` charges every Kullback–Leibler neighbourhood of the image of `Q₁`, and the domination
  applies to the images.

## Main statements

* `ProbabilityTheory.ae_tendsto_log_numeraire_bind_div_bipolarRate`: the logarithm of the
  numeraire against the mixture, divided by `n`, tends to the bipolar rate almost surely.
* `ProbabilityTheory.ae_eventually_log_le_log_numeraire_bind_add`: the numeraire against the
  mixture keeps up with every sequence of `n`-sample e-variables, up to a factor `exp (n ε)`.

## Implementation notes

The mixture is `ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q'`, with `ν` a finite measure on
`Measure 𝓧` such that almost every `Q'` is a probability measure. No measurability of
`Q' ↦ Measure.pi fun _ : Fin n ↦ Q'` is assumed: it is almost everywhere measurable
(`MeasureTheory.Measure.aemeasurable_pi`), which makes the bind the mixture. The neighbourhoods
`{Q' | klDiv Q₁ Q' ≤ ε}` need not be measurable; `ν` of them is an outer measure.

The statements and proofs are adapted from `EValuesResearch/Results/Numeraire.lean`,
`EValuesResearch/Results/NumeraireBarronAux.lean` and
`EValuesResearch/Results/NumeraireTrimAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, which formalize [EVR26, Note 14, Theorem (2)], rewritten on the
API of LMLExplore. There the comparison of the mixture numeraire with every sequence of bets is
proved on the images under `φ` directly; here it goes through a lemma on a countably generated
space, applied to the images.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Chapter 6.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
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

/-- `probKernel 𝓨` sends a probability measure to itself. -/
private lemma probKernel_apply (R : Measure 𝓨) [IsProbabilityMeasure R] : probKernel 𝓨 R = R := by
  change (if R .univ = 1 then R else 0) = R
  simp

/-- `probKernel 𝓨` is a finite kernel. -/
private instance isFiniteKernel_probKernel : IsFiniteKernel (probKernel 𝓨) :=
  ⟨⟨1, ENNReal.one_lt_top, fun R ↦ by
    change (if R .univ = 1 then R else 0) .univ ≤ 1
    split_ifs with h
    · exact h.le
    · simp⟩⟩

/-- **The mixture dominates an exponential density**, on a countably generated space. If `ν`
charges every Kullback–Leibler neighbourhood of `Q`, there are `c > 0` and an integrable `g` with
`∫ g ∂Q ≥ -ε` such that, for every `n`, the mixture `∫ R ^ n ν(dR)` dominates the measure of
density `c exp (∑ i, g (y i))` with respect to `Q ^ n`, in the form of an inequality between the
integrals of every measurable `ψ ≥ 0`. Take a measurable set `B` of probability measures of
positive `ν`-measure at relative entropy at most `ε` from `Q`, `c = ν B`, and for `g` the average
over `B` of the logarithm of a jointly measurable version `r` of the densities `dR / dQ`, and
apply Jensen's inequality, through `exp t ≥ exp a (1 + t - a)`, to `R ↦ ∏ i, r R (y i)`. -/
private lemma exists_lintegral_mul_le_lintegral_bind [MeasurableSpace.CountablyGenerated 𝓨]
    (Q : Measure 𝓨) [IsProbabilityMeasure Q] (ν : Measure (Measure 𝓨)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ R ∂ν, IsProbabilityMeasure R)
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {R | klDiv Q R ≤ ε} ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : 𝓨 → ℝ, Measurable g ∧ Integrable g Q ∧ -ε ≤ ∫ y, g y ∂Q ∧
      ∀ (n : ℕ) (ψ : (Fin n → 𝓨) → ℝ≥0∞), Measurable ψ →
        ∫⁻ y, ψ y * ENNReal.ofReal (c * Real.exp (∑ i, g (y i))) ∂Measure.pi (fun _ ↦ Q) ≤
          ∫⁻ y, ψ y ∂ν.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R := by
  -- a measurable set `B` of alternatives of positive mass, at relative entropy at most `ε`
  set P : Set (Measure 𝓨) := {R | R .univ = 1}
  have hPm : MeasurableSet P := Measure.measurable_coe .univ (measurableSet_singleton 1)
  have hKLm : Measurable fun R ↦ klDiv Q (probKernel 𝓨 R) := by
    simpa only [Kernel.const_apply] using measurable_klDiv (Kernel.const (Measure 𝓨) Q)
      (probKernel 𝓨)
  set B : Set (Measure 𝓨) := P ∩ {R | klDiv Q (probKernel 𝓨 R) ≤ ENNReal.ofReal ε}
  have hBm : MeasurableSet B := hPm.inter (measurableSet_le hKLm measurable_const)
  have hB (R : Measure 𝓨) (hR : R ∈ B) :
      IsProbabilityMeasure R ∧ klDiv Q R ≤ ENNReal.ofReal ε := by
    have : IsProbabilityMeasure R := ⟨hR.1⟩
    refine ⟨this, ?_⟩
    have h := hR.2
    rwa [Set.mem_ofPred_eq, probKernel_apply] at h
  have hνB : ν B ≠ 0 := by
    have hnull : ν Pᶜ = 0 := measure_mono_null (t := {R | ¬ IsProbabilityMeasure R})
      (fun R (hR : R ∈ Pᶜ) (h : IsProbabilityMeasure R) ↦ hR h.measure_univ) (ae_iff.1 hν)
    intro h0
    refine hν_supp _ (ENNReal.ofReal_pos.2 hε)
      (measure_mono_null (fun R hR ↦ ?_) (measure_union_null h0 hnull))
    by_cases h : R .univ = 1
    · have : IsProbabilityMeasure R := ⟨h⟩
      refine Or.inl ⟨h, ?_⟩
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
    have : IsFiniteMeasure (Q.withDensity (r R)) := isFiniteMeasure_of_le R (hrle R)
    have hrRm : Measurable (r R) := Kernel.measurable_rnDeriv_right _ _ R
    have hρRm : Measurable (ρ R) :=
      Finset.measurable_prod _ fun i _ ↦ hrRm.comp (measurable_pi_apply i)
    calc ∫⁻ y, ψ y * ρ R y ∂Measure.pi (fun _ : Fin n ↦ Q)
    _ = ∫⁻ y, ψ y ∂(Measure.pi fun _ : Fin n ↦ Q).withDensity (ρ R) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hρRm hψ]
      exact lintegral_congr fun y ↦ mul_comm _ _
    _ = ∫⁻ y, ψ y ∂Measure.pi fun _ : Fin n ↦ Q.withDensity (r R) := by
      rw [TauCeti.pi_withDensity (fun _ ↦ Q) fun _ ↦ hrRm]
    _ ≤ ∫⁻ y, ψ y ∂Measure.pi fun _ : Fin n ↦ R :=
      lintegral_mono' (Measure.pi_mono fun _ ↦ hrle R) le_rfl
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
    set a := ∑ i, g (y i)
    have hHint : ∫ R, H R ∂π = c * a := by
      simp only [H, a, g]
      rw [integral_finsetSum _ fun i _ ↦ (hy i).2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    calc ENNReal.ofReal (c * Real.exp a)
    _ = ENNReal.ofReal (∫ R, Real.exp a * (1 + (H R - a)) ∂π) := by
      have h : ∫ R, (1 + (H R - a)) ∂π = c := by
        have h' : ∫ R, (1 + (H R - a)) ∂π = ∫ _, (1 - a) ∂π + ∫ R, H R ∂π := by
          rw [← integral_add (integrable_const _) hHi]
          exact integral_congr_ae (ae_of_all _ fun R ↦ by ring)
        rw [h', integral_const, hπ, hHint, smul_eq_mul]
        ring
      rw [integral_const_mul, h, mul_comm]
    _ ≤ ∫⁻ R, ENNReal.ofReal (Real.exp a * (1 + (H R - a))) ∂π :=
      TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal
    _ ≤ ∫⁻ R, ENNReal.ofReal (Real.exp (H R)) ∂π := lintegral_mono fun R ↦ by
      refine ENNReal.ofReal_le_ofReal ?_
      calc Real.exp a * (1 + (H R - a)) ≤ Real.exp a * Real.exp (H R - a) := by
            gcongr
            linarith [Real.add_one_le_exp (H R - a)]
      _ = Real.exp (H R) := by rw [← Real.exp_add, add_sub_cancel]
    _ ≤ ∫⁻ R, ρ R y ∂π := lintegral_mono_ae hρH
  -- conclusion
  have hκ : AEMeasurable (fun R : Measure 𝓨 ↦ Measure.pi fun _ : Fin n ↦ R) ν :=
    Measure.aemeasurable_pi (κ := fun _ R ↦ R) (fun _ ↦ measurable_id) fun _ ↦
      hν.mono fun R hR ↦ inferInstance
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
    (Measure.lintegral_bind hκ hψ.aemeasurable).symm

/-- **Functions of bounded mean under the mixtures grow subexponentially**, on a countably
generated space. If `ν` charges every Kullback–Leibler neighbourhood of `Q`, and the functions
`ψ n` of `n` observations have mean at most `C < ∞` under the mixtures `∫ R ^ n ν(dR)`, then for
every `ε > 0`, almost surely under the i.i.d. law of `Q`, `ψ n ≤ exp (n ε)` at the first `n`
observations for all large `n`: the domination of the mixture, Markov's inequality, the
Borel–Cantelli lemma and the strong law of large numbers. -/
private lemma ae_eventually_le_exp_of_lintegral_bind_le [MeasurableSpace.CountablyGenerated 𝓨]
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
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q)
  set h : (n : ℕ) → (Fin n → 𝓨) → ℝ≥0∞ := fun n y ↦
    ENNReal.ofReal (c * Real.exp (∑ i, g (y i)))
  have hhm (n : ℕ) : Measurable (h n) := ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun i _ ↦ hgm.comp (measurable_pi_apply i))))
  -- Markov's inequality and the Borel–Cantelli lemma for `ψ n * h n`
  set A : ℕ → Set (ℕ → 𝓨) := fun n ↦
    {ω | ENNReal.ofReal (Real.exp (n * (ε / 2))) ≤ ψ n (initSeg n ω) * h n (initSeg n ω)}
  have hA (n : ℕ) : μ (A n) ≤ C * ENNReal.ofReal (Real.exp (-(ε / 2))) ^ n := by
    have hm : Measurable fun y ↦ ψ n y * h n y := (hψ n).mul (hhm n)
    calc μ (A n) ≤ (∫⁻ ω, ψ n (initSeg n ω) * h n (initSeg n ω) ∂μ) /
          ENNReal.ofReal (Real.exp (n * (ε / 2))) :=
        meas_ge_le_lintegral_div (hm.comp (measurable_initSeg n)).aemeasurable
          (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (Real.exp (n * (ε / 2))) := by
      gcongr
      rw [(measurePreserving_initSeg Q n).lintegral_comp hm]
      exact (hdom n (ψ n) (hψ n)).trans (hψC n)
    _ = C * ENNReal.ofReal (Real.exp (-(ε / 2))) ^ n := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
        ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
      ring_nf
  have hsum : ∑' n, μ (A n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hA)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 ?_).ne')
    rw [ENNReal.ofReal_lt_one]
    exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 (half_pos hε))
  -- the strong law of large numbers for `g`
  have hlt : -(3 * ε / 8) < ∫ y, g y ∂Q := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * |Real.log c| / ε)
  filter_upwards [ae_eventually_notMem hsum, TauCeti.Probability.strong_law_ae_infinitePi Q hgi]
    with ω hω1 hω2
  filter_upwards [hω1, hω2.eventually (lt_mem_nhds hlt), eventually_ge_atTop (N + 1)]
    with n hn1 hn2 hn3
  simp only [A, Set.mem_ofPred_eq, not_le] at hn1
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

/-! ### The numeraires against a mixture -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The numeraire against a mixture keeps up with every sequence of `n`-sample e-variables.**
Let `ν` be a finite measure on the measures on `𝓧` that charges only probability measures and
every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}` of `Q₁`. For every sequence of
e-variables `M n` for the `n`-fold products of the members of `S₁` and every `ε > 0`, almost
surely under the i.i.d. law of `Q₁`, eventually `log (M n) ≤ log (W n) + n ε` at the first `n`
observations, where `W n` is Statlib's `numeraire` of the `n`-sample null under the mixture
`∫ Q' ^ n ν(dQ')` [EVR26, Note 14]. The ratio `M n / W n` has mean at most `ν univ` under the
mixture; its factorization through Boolean coordinates of the observations reduces the statement
to a countably generated space, where the domination of the mixture by an exponential density
bounds the ratio by `exp (n ε)`. The members of `S₁` need only be finite measures. If `Q₁` is
not a probability measure, its i.i.d. law is `0` and the statement holds trivially. -/
theorem ae_eventually_log_le_log_numeraire_bind_add (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0)
    {M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hM : ∀ n, IsEVar (M n) ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (M n (initSeg n ω)) ≤ ENNReal.log (numeraire
        (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  set W : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞ := fun n ↦ numeraire
    (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)
  -- the ratios to the mixture numeraires factor through Boolean coordinates
  obtain ⟨φ, hφ, ψ, hψ, hMW⟩ := MeasurableSpace.exists_measurable_forall_eq_measurable_comp_piMap
    (f := fun n x ↦ M n x / W n x) fun n ↦ (hM n).measurable.div (measurable_numeraire _ _)
  -- the images of the alternatives under `φ`
  have hmap : Measurable fun Q' : Measure 𝓧 ↦ Q'.map φ := Measure.measurable_map φ hφ
  set ν' : Measure (Measure (ℕ → Bool)) := ν.map fun Q' ↦ Q'.map φ
  have hν' : ∀ᵐ R ∂ν', IsProbabilityMeasure R := by
    have hPm : MeasurableSet {R : Measure (ℕ → Bool) | IsProbabilityMeasure R} := by
      convert Measure.measurable_coe (α := ℕ → Bool) .univ (measurableSet_singleton 1) using 1
      ext R
      simp [isProbabilityMeasure_iff]
    exact (ae_map_iff hmap.aemeasurable hPm).2 (hν.mono fun _ _ ↦ inferInstance)
  have hν'_supp (δ : ℝ≥0∞) (hδ : 0 < δ) : ν' {R | klDiv (Q₁.map φ) R ≤ δ} ≠ 0 := by
    intro h0
    have h1 : ν ((fun Q' ↦ Q'.map φ) ⁻¹' {R | klDiv (Q₁.map φ) R ≤ δ}) = 0 :=
      nonpos_iff_eq_zero.1 (h0 ▸ Measure.le_map_apply hmap.aemeasurable _)
    refine hν_supp δ hδ (measure_mono_null (fun Q' hQ' ↦ ?_) (measure_union_null h1 (ae_iff.1 hν)))
    by_cases hp : IsProbabilityMeasure Q'
    · exact Or.inl ((klDiv_map_le Q₁ Q' hφ).trans hQ')
    · exact Or.inr hp
  -- the means of the factors under the mixtures of the images
  have hbound (n : ℕ) :
      ∫⁻ y, ψ n y ∂(ν'.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R) ≤ ν .univ := by
    have hκ : AEMeasurable (fun Q' : Measure 𝓧 ↦ Measure.pi fun _ : Fin n ↦ Q') ν :=
      Measure.aemeasurable_pi (κ := fun _ R ↦ R) (fun _ ↦ measurable_id) fun _ ↦
        hν.mono fun _ _ ↦ inferInstance
    have hκ' : AEMeasurable (fun R : Measure (ℕ → Bool) ↦ Measure.pi fun _ : Fin n ↦ R) ν' :=
      Measure.aemeasurable_pi (κ := fun _ R ↦ R) (fun _ ↦ measurable_id) fun _ ↦
        hν'.mono fun _ _ ↦ inferInstance
    have hΦ : Measurable fun (x : Fin n → 𝓧) (i : Fin n) ↦ φ (x i) :=
      .of_eval fun i ↦ hφ.comp (measurable_pi_apply i)
    calc ∫⁻ y, ψ n y ∂(ν'.bind fun R ↦ Measure.pi fun _ : Fin n ↦ R)
    _ = ∫⁻ R, ∫⁻ y, ψ n y ∂Measure.pi (fun _ : Fin n ↦ R) ∂ν' :=
      Measure.lintegral_bind hκ' (hψ n).aemeasurable
    _ = ∫⁻ Q', ∫⁻ y, ψ n y ∂Measure.pi (fun _ : Fin n ↦ Q'.map φ) ∂ν :=
      lintegral_map' ((Measure.measurable_lintegral (hψ n)).comp_aemeasurable hκ')
        hmap.aemeasurable
    _ = ∫⁻ Q', ∫⁻ x, M n x / W n x ∂Measure.pi (fun _ : Fin n ↦ Q') ∂ν := by
      refine lintegral_congr_ae (hν.mono fun Q' hQ' ↦ ?_)
      have hpi : (Measure.pi fun _ : Fin n ↦ Q').map (fun x i ↦ φ (x i)) =
          Measure.pi fun _ : Fin n ↦ Q'.map φ := Measure.pi_map_pi fun _ ↦ hφ.aemeasurable
      dsimp only
      rw [← hpi, lintegral_map (hψ n) hΦ]
      exact lintegral_congr fun x ↦ (congr_fun (hMW n) x).symm
    _ = ∫⁻ x, M n x / W n x ∂(ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') :=
      (Measure.lintegral_bind hκ
        ((hM n).measurable.div (measurable_numeraire _ _)).aemeasurable).symm
    _ ≤ (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') .univ :=
      lintegral_div_numeraire_le_measure_univ _ (isFiniteMeasure_of_mem_image_pi hS₁ n) (hM n)
    _ = ν .univ := by
      rw [Measure.bind_apply .univ hκ, ← lintegral_one]
      exact lintegral_congr_ae (hν.mono fun Q' hQ' ↦ measure_univ)
  -- the bound on the images, pulled back to the observations
  have h1 := ae_eventually_le_exp_of_lintegral_bind_le (Q₁.map φ) ν' hν' hν'_supp hψ
    (measure_ne_top ν .univ) hbound hε
  have heq : (Measure.infinitePi fun _ : ℕ ↦ Q₁).map (fun (ω : ℕ → 𝓧) i ↦ φ (ω i)) =
      Measure.infinitePi fun _ : ℕ ↦ Q₁.map φ := Measure.infinitePi_map_pi _ fun _ ↦ hφ
  rw [← heq] at h1
  have hΦ : Measurable fun (ω : ℕ → 𝓧) i ↦ φ (ω i) :=
    .of_eval fun i ↦ hφ.comp (measurable_pi_apply i)
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h1] with ω hω
  filter_upwards [hω] with n hn
  refine ENNReal.log_le_log_add_of_div_le ?_
  have hseg : (fun i ↦ φ (initSeg n ω i)) = initSeg n fun i ↦ φ (ω i) :=
    funext fun i ↦ by simp only [initSeg_apply]
  rw [congr_fun (hMW n) (initSeg n ω), Function.comp_apply, hseg]
  exact hn

/-- **The numeraires against a mixture of i.i.d. alternatives grow at the bipolar rate, almost
surely.** Let `ν` be a finite measure on the measures on `𝓧` that charges only probability
measures and every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}`, `ε > 0`, of `Q₁`.
Almost surely under the i.i.d. law of `Q₁`, the logarithm of the numeraire of the `n`-sample null
under the mixture `∫ Q' ^ n ν(dQ')`, at the first `n` observations, divided by `n`, tends to
`bipolarRate Q₁ S₁`, also when the bipolar rate is infinite [EVR26, Note 14]: the asymptotic
log-optimality of the mixture numeraires that [RW, Chapter 6] conjectures, with the rate
`bipolarRate Q₁ S₁` of [RR26]. The upper bound holds for every sequence of `n`-sample
e-variables (`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`), and the lower bound follows
from the comparison with every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_eventually_log_le_log_numeraire_bind_add`). No assumption is made on `𝓧`.
If `Q₁` is not a probability measure, its i.i.d. law is `0` and the statement holds trivially. -/
theorem ae_tendsto_log_numeraire_bind_div_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  have := nonempty_of_isProbabilityMeasure Q₁
  filter_upwards [ae_limsup_log_div_le_bipolarRate Q₁ hS₁ fun n ↦ isEVar_numeraire _ _,
    ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le Q₁ hS₁
      (T := fun n ω ↦ numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω))
      fun F hF hFn h_null ε hε ↦ by
        choose G hG hFG using fun n ↦
          exists_isEVar_eq_comp_initSeg hS₁ (hF n) (hFn n) fun P hP ↦ h_null P hP n
        filter_upwards [ae_eventually_log_le_log_numeraire_bind_add Q₁
          (fun P hP ↦ have := hS₁ P hP; inferInstance) ν hν hν_supp hG hε] with ω hω
        filter_upwards [hω] with n hn
        rw [hFG n]
        exact hn]
    with ω hsup hinf
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

end ProbabilityTheory
