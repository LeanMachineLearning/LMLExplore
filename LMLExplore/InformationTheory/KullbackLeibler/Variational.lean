/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import Statlib.EValues.RIPr
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The Donsker–Varadhan inequality for the logarithm of a nonnegative function

For probability measures `μ ≪ ν` and a nonnegative function `f`,
`∫ log f dμ ≤ log ∫ f dν + KL(μ ‖ ν)`, with the expected logarithm in `EReal` and the integral of
`f` a lower integral. This is the Donsker–Varadhan (Gibbs) inequality written for `f = exp g`, with
no integrability: both sides may be infinite. It bounds an expected logarithm under `μ` by an
expectation under a reference law `ν`, at the price of the relative entropy.

The proof uses Statlib's variational form of the relative entropy, the largest expected logarithm
of an e-variable for the simple null `{ν}` (`ProbabilityTheory.maxUtility_singleton_eq_klDiv`):
when `0 < ∫ f dν < ∞`, the function `f / ∫ f dν` is such an e-variable.

Applied to the logarithm of the likelihood ratio on a finite set `F` of atoms charged by both
laws, Tau Ceti's real form of the Donsker–Varadhan inequality
(`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`) bounds the relative entropy from below
by the contribution of these atoms: `∑_{j ∈ F} Q {j} log (Q {j} / P {j}) - log 2 ≤ KL(Q ‖ P)`.

## Main statements

* `InformationTheory.eintegral_log_le_log_lintegral_add_klDiv`: for `μ ≪ ν`,
  `∫ᵉ log f dμ ≤ log (∫⁻ f dν) + klDiv μ ν`.
* `InformationTheory.ofReal_sum_mul_log_sub_log_two_le_klDiv`: for probability measures `Q` and
  `P` and a finite set `F` of points charged by both,
  `∑_{j ∈ F} Q {j} log (Q {j} / P {j}) - log 2 ≤ KL(Q ‖ P)`.

## Implementation notes

The statement is adapted from the lemma of the same name in
`EValuesResearch/Results/Numeraire.lean` (commit `9eee1f2`) of the paper project
`RemyDegenne/evalues_research`, which assumes `klDiv μ ν ≠ ∞` and a measurable `f` and proves it
through the density `dμ/dν` for the regret of the mixture numeraires [EVR26, Note 14]; here it
assumes `μ ≪ ν` and an almost everywhere measurable `f`.

## References

* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process
  expectations for large time. IV*, Comm. Pure Appl. Math. 36 (1983), 183–212.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 14, *Asymptotic log-optimality of the mixture numeraire*.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- **The Donsker–Varadhan inequality** for the logarithm of a nonnegative function: for
probability measures `μ ≪ ν` and an almost everywhere measurable `f`,
`∫ log f dμ ≤ log ∫ f dν + KL(μ ‖ ν)`. Both sides may be infinite. Without `μ ≪ ν`, the relative
entropy is infinite and so is the right side, unless `f = 0` almost everywhere under `ν`, where
the bound may fail. -/
theorem eintegral_log_le_log_lintegral_add_klDiv {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫ᵉ x, ENNReal.log (f x) ∂μ ≤ ENNReal.log (∫⁻ x, f x ∂ν) + klDiv μ ν := by
  -- replace `f` by a measurable version
  rw [eintegral_congr_ae ((hμν.ae_eq hf.ae_eq_mk).mono fun x hx ↦ by rw [hx]),
    lintegral_congr_ae hf.ae_eq_mk]
  set g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  set c := ∫⁻ x, g x ∂ν
  rcases eq_or_ne c 0 with h0 | h0
  · -- `g = 0` almost everywhere under `ν`, hence under `μ`
    have h : ∀ᵐ x ∂μ, ENNReal.log (g x) = ⊥ :=
      (hμν.ae_eq ((lintegral_eq_zero_iff hg).1 h0)).mono fun x hx ↦ by simp [hx]
    rw [eintegral_congr_ae h, eintegral_const, measure_univ]
    simp
  rcases eq_or_ne c ∞ with htop | htop
  · rw [htop, ENNReal.log_top, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
    exact le_top
  -- `g / c` is an e-variable for `{ν}`, whose largest expected logarithm is `klDiv μ ν`
  have hX : IsEVar (fun x ↦ g x / c) {ν} := ⟨hg.div_const c, fun P hP ↦ by
    simp_rw [Set.mem_singleton_iff.1 hP, div_eq_mul_inv]
    rw [lintegral_mul_const _ hg, ENNReal.mul_inv_cancel h0 htop]⟩
  have hKL : ∫ᵉ x, ENNReal.log (g x / c) ∂μ ≤ klDiv μ ν := by
    simpa [logUtility_apply, maxUtility_singleton_eq_klDiv] using
      hX.eintegral_le_maxUtility μ logUtility
  have hc : ∫ᵉ _, ENNReal.log c ∂μ = ENNReal.log c := by simp
  calc ∫ᵉ x, ENNReal.log (g x) ∂μ
  _ = ∫ᵉ x, ENNReal.log (g x / c) + ENNReal.log c ∂μ :=
    eintegral_congr fun x ↦ by rw [← ENNReal.log_mul_add, ENNReal.div_mul_cancel h0 htop]
  _ = ∫ᵉ x, ENNReal.log (g x / c) ∂μ + ENNReal.log c := by
    rw [eintegral_add' (by fun_prop) aemeasurable_const (by simpa [hc] using htop)
      (by simpa [hc] using h0), hc]
  _ ≤ klDiv μ ν + ENNReal.log c := by gcongr
  _ = ENNReal.log c + klDiv μ ν := add_comm _ _

/-- **The Donsker–Varadhan bound on a finite block of atoms.** For probability measures `Q` and
`P` on a measurable space with measurable singletons and a finite set `F` of points charged by both,
`∑_{j ∈ F} Q {j} log (Q {j} / P {j}) - log 2 ≤ KL(Q ‖ P)`. -/
theorem ofReal_sum_mul_log_sub_log_two_le_klDiv [MeasurableSingletonClass α]
    (Q P : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (F : Finset α)
    (hQ : ∀ j ∈ F, 0 < Q.real {j}) (hP : ∀ j ∈ F, 0 < P.real {j}) :
    ENNReal.ofReal (∑ j ∈ F, Q.real {j} * Real.log (Q.real {j} / P.real {j}) - Real.log 2) ≤
      klDiv Q P := by
  classical
  set q : α → ℝ := fun j ↦ Q.real {j} with hq_def
  set p : α → ℝ := fun j ↦ P.real {j} with hp_def
  -- the logarithm of the likelihood ratio on the points of `F`
  set f : α → ℝ := fun x ↦ ∑ j ∈ F, ({j} : Set α).indicator (fun _ ↦ Real.log (q j / p j)) x
    with hf_def
  have hsingle (c : α → ℝ) (x : α) :
      ∑ j ∈ F, ({j} : Set α).indicator (fun _ ↦ c j) x = if x ∈ F then c x else 0 := by
    split_ifs with hx
    · rw [Finset.sum_eq_single x (fun j _ hj ↦ Set.indicator_of_notMem
        (by simpa using Ne.symm hj) _) (fun h ↦ absurd hx h)]
      simp
    · exact Finset.sum_eq_zero fun j hj ↦ Set.indicator_of_notMem
        (by rintro rfl; exact hx hj) _
  have hint_ind (μ : Measure α) [IsFiniteMeasure μ] (c : α → ℝ) :
      Integrable (fun x ↦ ∑ j ∈ F, ({j} : Set α).indicator (fun _ ↦ c j) x) μ :=
    integrable_finsetSum _ fun j _ ↦ (integrable_const _).indicator (measurableSet_singleton j)
  have hexpf (x : α) : Real.exp (f x) =
      1 + ∑ j ∈ F, ({j} : Set α).indicator (fun _ ↦ q j / p j - 1) x := by
    simp only [hf_def]
    rw [hsingle, hsingle]
    split_ifs with hx
    · rw [Real.exp_log (div_pos (hQ x hx) (hP x hx))]; ring
    · simp
  have hexpi : Integrable (fun x ↦ Real.exp (f x)) P := by
    simp_rw [hexpf]
    exact (integrable_const 1).add (hint_ind _ _)
  have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv (μ := Q) (ν := P)
    (hint_ind _ _) hexpi
  have hIf : ∫ x, f x ∂Q = ∑ j ∈ F, q j * Real.log (q j / p j) := by
    rw [hf_def, integral_finsetSum _ fun j _ ↦
      (integrable_const _).indicator (measurableSet_singleton j)]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [integral_indicator_const _ (measurableSet_singleton j), smul_eq_mul]
  have hIe : ∫ x, Real.exp (f x) ∂P ≤ 2 := by
    simp_rw [hexpf]
    rw [integral_add (integrable_const 1) (hint_ind _ _), integral_const, probReal_univ,
      one_smul, integral_finsetSum _ fun j _ ↦
        (integrable_const _).indicator (measurableSet_singleton j)]
    have hsum : ∑ j ∈ F, ∫ x, ({j} : Set α).indicator (fun _ ↦ q j / p j - 1) x ∂P
        ≤ ∑ j ∈ F, Q.real {j} := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      rw [integral_indicator_const _ (measurableSet_singleton j), smul_eq_mul, mul_sub,
        mul_div_cancel₀ _ (hP j hj).ne', mul_one]
      linarith [hP j hj]
    have hF : ∑ j ∈ F, Q.real {j} ≤ 1 := by
      rw [← measureReal_biUnion_finset (fun i _ j _ hij ↦ Set.disjoint_singleton.2 hij)
        (fun j _ ↦ measurableSet_singleton j)]
      exact measureReal_le_one
    linarith
  have hIe0 : 0 < ∫ x, Real.exp (f x) ∂P := integral_exp_pos hexpi
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hDV
  rw [hIf]
  have := Real.log_le_log hIe0 hIe
  linarith


end InformationTheory
