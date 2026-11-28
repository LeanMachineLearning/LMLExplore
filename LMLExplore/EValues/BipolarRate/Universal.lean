/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Probability.Process.Filtration
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.Data.EReal.Basic
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.EValues.EProcess.Closure
import LMLExplore.EValues.EProcess.LevelStoppingTime
import LMLExplore.EValues.Null.PrefixBet
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Probability.Process.LevelCrossing
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# One e-process at the bipolar rate for every dominated alternative

Let `S₁` be a set of probability measures on a countably generated measurable space `𝓧` (the
null), and `ρ` an s-finite measure on `𝓧`. The observations are the coordinates of `ℕ → 𝓧`, with
the i.i.d. laws `Measure.infinitePi fun _ ↦ P` and the filtration `Filtration.piLT` of the
observations, whose time `n` has seen `n` observations. There is a single e-process `E` for the
i.i.d. null, nondecreasing in time, such
that for every probability measure `Q₁ ≪ ρ`, almost surely under the i.i.d. law of `Q₁`,
`(1/n) log (E n)` tends to the bipolar rate `bipolarRate Q₁ S₁` of Ram and Ramdas [RR26], the
optimal growth rate of e-processes against the i.i.d. null. No e-process grows faster
(`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`), so this one is asymptotically
optimal against all the alternatives dominated by `ρ` at once: a countable family of laws, the
laws with a density with respect to a given σ-finite measure, or all laws on a countable space.
Nothing is assumed on the null beyond its members being probability measures.

The tests that threshold this e-process are at the rate too. The first time `τ α` at which `E`
reaches `α⁻¹` is a sequential test of level `α`
(`ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter`), and for every probability
measure `Q₁ ≪ ρ`, under the i.i.d. law of `Q₁`, `τ α / log (1/α)` tends to
`1 / bipolarRate Q₁ S₁` as `α → 0`, almost surely and in expectation. No sequential test of level
`α` makes fewer than `log (1/α) / bipolarRate Q₁ S₁` observations in expectation
(`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`), so these tests are
first-order optimal at every alternative dominated by `ρ` at once. The limits are in `ℝ≥0∞`, with
`1 / 0 = ∞` and `1 / ∞ = 0`, so they hold also where the bipolar rate is `0` or `∞`.

The first step is a statement of its own: countably many bounded functions `g i` of blocks of
`len i` observations, each the logarithm of an e-variable for the `len i`-sample null, determine
the bipolar rate of every probability measure `Q ≪ ρ` as the supremum of their normalized means
`(∫ g i ∂Q ^ len i) / len i`. It holds for every null of measures of mass at most one.

## Main statements

* `ProbabilityTheory.exists_iSup_integral_div_eq_bipolarRate`: countably many bounded block bets
  whose normalized means have supremum the bipolar rate of every alternative `Q ≪ ρ`.
* `ProbabilityTheory.exists_isEProcess_ae_tendsto_log_div_bipolarRate`: one nondecreasing
  e-process for the i.i.d. null grows at the bipolar rate of every alternative `Q₁ ≪ ρ`, almost
  surely.
* `ProbabilityTheory.exists_isEProcess_tendsto_hittingAfter_div_log`: one nondecreasing e-process
  for the i.i.d. null whose tests `τ α` have `τ α / log (1/α)` tending to `1 / bipolarRate Q₁ S₁`,
  almost surely and in expectation, for every alternative `Q₁ ≪ ρ`.

## Implementation notes

The proof of the growth has three steps.

* **A countable family that determines the bipolar rate.** For `m` observations and `N : ℕ`,
  consider the measurable functions `f` of `m` observations with `|f| ≤ N` and
  `∫ exp f ∂P ^ m ≤ 1` for every `P ∈ S₁`: the logarithms of bounded e-variables. A sequence of
  them that is dense in `L¹` of the finite measure `ρ.toFinite ^ m`, which is separable since `𝓧`
  is countably generated, approximates the mean under `Q₁ ^ m` of each of them, for every
  `Q₁ ≪ ρ`, by dominated convergence. Mixing an e-variable with a constant and truncating its
  logarithm shows that these means determine the bipolar rate: for every `t < bipolarRate Q₁ S₁`,
  one member `g` of the countable family, on `m` observations, has `t m < ∫ g ∂Q₁ ^ m`.
  Conversely `∫ g ∂Q₁ ^ m` is the expected logarithm of the e-variable `exp g`, at most
  `maxLogGrowth Q₁ S₁ m`, so the supremum of the normalized means is the bipolar rate
  (`ProbabilityTheory.exists_iSup_integral_div_eq_bipolarRate`).
* **Products over blocks.** For such a `g` on blocks of `m` observations, the product
  `seqBlockProd m (exp ∘ g) k` of `exp g` over the first `k` consecutive blocks is an e-variable
  for the i.i.d. null, as the blocks are independent (`ProbabilityTheory.isEVar_seqBlockProd`),
  and its logarithm divided by `k` tends to `∫ g ∂Q₁ ^ m` almost surely, by the strong law of
  large numbers along the blocks (`ProbabilityTheory.strong_law_ae_seqBlock`).
* **The mixture.** The e-process at time `n` is the sum, over the members `g i` of the family
  and the numbers `k` of blocks of `g i` that fit in the first `n` observations, of these
  products, with weights `2⁻¹ ^ (i + 1) / ((k + 1) (k + 2))`. Each term is held from the time its
  blocks are observed on, which makes the process nondecreasing, and the sum of all the terms has
  expectation at most `1` under the null, so the value at every stopping time is an e-variable:
  the mixture is a mixture of held bets (`ProbabilityTheory.isEProcess_tsum_ite_le_mul`).
  The weight of the number of blocks costs `o(n)` in the logarithm, which gives the lower bound
  on the growth; the upper bound is
  `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`.

The limits of the tests take each bound from a general result, except the last one.

* **Almost surely.** Every family of nested tests of level `α` has
  `liminf τ α / log (1/α) ≥ 1 / bipolarRate Q₁ S₁`
  (`ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div_log`), and the tests that
  threshold a process growing at the rate have `limsup τ α / log (1/α) ≤ 1 / bipolarRate Q₁ S₁`
  (`ProbabilityTheory.limsup_toENNReal_hittingAfter_div_log_le`).
* **In expectation, from below.** Every test of level `α` makes at least
  `log (1/α) / bipolarRate Q₁ S₁` observations in expectation
  (`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`).
* **In expectation, from above.** For `0 < c < bipolarRate Q₁ S₁`, some member `g i` of the
  family has `c * len i < ∫ g i ∂Q₁ ^ len i`; let `δ > 0` be half the margin. The weight of `k`
  blocks costs at most `δ k` plus a constant in the logarithm, so the mixture reaches `α⁻¹` at the
  latest at `len i` times the first time the random walk of the values of `g i - δ` on the blocks
  reaches `log (1/α)` plus a constant. Its increments are bounded above and have mean
  `∫ g i ∂Q₁ ^ len i - δ > c * len i`, and Wald's bound on first passage times
  (`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`) gives
  `limsup 𝔼[τ α] / log (1/α) ≤ 1 / c`.

The statements on the e-process are the theorem of [EVR26, Note 13]
(`results/13-universal-eprocess.md` there), which states the limits of the tests when
`0 < bipolarRate Q₁ S₁ < ∞`. The note builds the e-process from the running maxima of the block
products, passed through an adjuster, and Ville's inequality; the proof here uses the mixture over
the number of blocks instead, which needs neither. The statement of the growth and its proof are
adapted from `EValuesResearch/Results/UniversalEProcess.lean` (commit `a1002bc`) in the paper
project `RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. The statement of the
first step, with the supremum and for nulls of measures of mass at most one, and the statement of
the tests and its proof, are adapted from `EValuesResearch/Results/UniversalTests.lean` (commit
`83205cb`) in the same project, rewritten on the API of LMLExplore.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 13, *One e-process at the bipolar rate for every dominated
  alternative*, Theorem and the first step of its proof.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### A countable family of bounded log-e-variables that determines the bipolar rate -/

/-- The logarithms of the `m`-sample e-variables for the i.i.d. laws of `S₁` that are bounded by
`N` in absolute value. -/
private def boundedLogEVarSet (S₁ : Set (Measure 𝓧)) (m N : ℕ) : Set ((Fin m → 𝓧) → ℝ) :=
  {f | Measurable f ∧ (∀ x, |f x| ≤ N) ∧
    ∀ P ∈ S₁, ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂Measure.pi (fun _ : Fin m ↦ P) ≤ 1}

/-- The constant `0` is the logarithm of the e-variable `1`. -/
private lemma zero_mem_boundedLogEVarSet (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (m N : ℕ) :
    (0 : (Fin m → 𝓧) → ℝ) ∈ boundedLogEVarSet S₁ m N := by
  refine ⟨measurable_const, fun _ ↦ by simp, fun P hP ↦ ?_⟩
  simpa using measure_univ_le_one_of_mem_sampleNull hS₁ m _ (pi_mem_sampleNull hP)

/-- **A countable dense family.** On a countably generated space, for an s-finite `ρ`, a sequence
in `boundedLogEVarSet S₁ m N` approximates the mean under `Q ^ m` of every member, for every
probability measure `Q ≪ ρ`. It is dense in `L¹` of the finite measure `ρ.toFinite ^ m`, which is
separable. -/
private lemma exists_seq_boundedLogEVarSet [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ρ : Measure 𝓧) [SFinite ρ] (m N : ℕ) :
    ∃ u : ℕ → (Fin m → 𝓧) → ℝ, (∀ j, u j ∈ boundedLogEVarSet S₁ m N) ∧
      ∀ Q : Measure 𝓧, IsProbabilityMeasure Q → Q ≪ ρ →
        ∀ f ∈ boundedLogEVarSet S₁ m N, ∀ c : ℝ, c < ∫ x, f x ∂Measure.pi (fun _ : Fin m ↦ Q) →
          ∃ j, c < ∫ x, u j x ∂Measure.pi (fun _ : Fin m ↦ Q) := by
  set ν := Measure.pi (fun _ : Fin m ↦ ρ.toFinite)
  set T := boundedLogEVarSet S₁ m N
  set A : Set (Lp ℝ 1 ν) := {v | ∃ f ∈ T, (v : (Fin m → 𝓧) → ℝ) =ᵐ[ν] f}
  have hA : Nonempty A := ⟨⟨0, 0, zero_mem_boundedLogEVarSet hS₁ m N, Lp.coeFn_zero _ _ _⟩⟩
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq A
  choose u hu hvu using fun j ↦ (v j).property
  refine ⟨u, hu, fun Q hQ hQρ f hf c hc ↦ ?_⟩
  have hfm : MemLp f 1 ν := MemLp.of_bound hf.1.aestronglyMeasurable N
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hf.2.1 x)
  set a : A := ⟨hfm.toLp f, f, hf, hfm.coeFn_toLp⟩
  choose js hjs using fun l : ℕ ↦ hv.exists_dist_lt a (Nat.one_div_pos_of_nat (n := l))
  have hlim : Tendsto (fun l ↦ ((v (js l) : A) : Lp ℝ 1 ν)) atTop (𝓝 (a : Lp ℝ 1 ν)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun l ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm, ← Subtype.dist_eq]
    exact (hjs l).le
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hae : ∀ᵐ x ∂ν, Tendsto (fun i ↦ u (js (ns i)) x) atTop (𝓝 (f x)) := by
    filter_upwards [hns, ae_all_iff.2 hvu, hfm.coeFn_toLp] with x hx hxu hxf
    simp only [a] at hx
    rw [hxf] at hx
    simpa only [hxu] using hx
  have hac : Measure.pi (fun _ : Fin m ↦ Q) ≪ ν :=
    Measure.AbsolutelyContinuous.pi fun _ ↦ hQρ.trans (absolutelyContinuous_toFinite ρ)
  have hint := tendsto_integral_of_dominated_convergence (μ := Measure.pi fun _ : Fin m ↦ Q)
    (fun _ ↦ (N : ℝ)) (fun i ↦ (hu _).1.aestronglyMeasurable) (integrable_const _)
    (fun i ↦ ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using (hu _).2.1 x)
    (hac.ae_le hae)
  obtain ⟨i, hi⟩ := (hint.eventually (lt_mem_nhds hc)).exists
  exact ⟨_, hi⟩

/-- **Truncation.** If an `m`-sample e-variable has expected logarithm larger than `c` under
`Q ^ m`, so has a member of `boundedLogEVarSet S₁ m N` for some `N`, by
`IsEVar.exists_bounded_lt_integral_of_lt_eintegral_log`. -/
private lemma exists_mem_boundedLogEVarSet_lt_integral (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) {m : ℕ}
    {E : (Fin m → 𝓧) → ℝ≥0∞} (hE : IsEVar E (sampleNull S₁ m))
    {c : ℝ} (hc : (c : EReal) < ∫ᵉ x, ENNReal.log (E x) ∂Measure.pi (fun _ : Fin m ↦ Q)) :
    ∃ N : ℕ, ∃ f ∈ boundedLogEVarSet S₁ m N, c < ∫ x, f x ∂Measure.pi (fun _ : Fin m ↦ Q) := by
  obtain ⟨N, f, hfm, hfN, hfP, hcf⟩ := hE.exists_bounded_lt_integral_of_lt_eintegral_log _
    (measure_univ_le_one_of_mem_sampleNull hS₁ m) hc
  exact ⟨⌈N⌉₊, f, ⟨hfm, fun x ↦ (hfN x).trans (Nat.le_ceil N),
    fun P hP ↦ hfP _ (pi_mem_sampleNull hP)⟩, hcf⟩

/-- An exponent below the bipolar rate is beaten by the expected logarithm of an e-variable of
some number of observations. -/
private lemma exists_isEVar_lt_eintegral_of_lt_bipolarRate {Q : Measure 𝓧} {t : ℝ}
    (ht : (t : EReal) < bipolarRate Q S₁) :
    ∃ m : ℕ, ∃ E : (Fin (m + 1) → 𝓧) → ℝ≥0∞,
      IsEVar E (sampleNull S₁ (m + 1)) ∧
      ((t * (m + 1) : ℝ) : EReal) <
        ∫ᵉ x, ENNReal.log (E x) ∂Measure.pi (fun _ : Fin (m + 1) ↦ Q) := by
  rw [bipolarRate_def] at ht
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 ht
  have hm0 : (0 : EReal) < ((m + 1 : ℕ) : EReal) := by exact_mod_cast Nat.succ_pos m
  rw [EReal.lt_div_iff hm0 (EReal.natCast_ne_top _)] at hm
  rw [maxLogGrowth_def] at hm
  obtain ⟨E, hEv, hE'⟩ := lt_maxEPower_iff.1 hm
  refine ⟨m, E, hEv, ?_⟩
  have h1 : ((t * (m + 1) : ℝ) : EReal) = (t : EReal) * ((m + 1 : ℕ) : EReal) := by
    rw [EReal.coe_mul]
    norm_cast
  rw [h1]
  exact hE'

/-- **Block bets that determine the bipolar rate.** On a countably generated space, for a null
`S₁` of measures of mass at most one and an s-finite measure `ρ`, there are bounded measurable
functions `g i` of blocks of `len i ≥ 1` observations, with `∫ exp (g i) ∂P ^ len i ≤ 1` for every
`P ∈ S₁` (that is, `exp (g i)` is an e-variable for the `len i`-sample null), such that for every
probability measure `Q ≪ ρ` the supremum over `i` of the normalized means
`(∫ g i ∂Q ^ len i) / len i` is the bipolar rate `bipolarRate Q S₁`. Each normalized mean is at
most the rate by the definition of `maxLogGrowth`; the family, chosen without `Q`, reaches it at
every `Q ≪ ρ` at once. This is the first step of the proof of the theorem of [EVR26, Note 13]. -/
theorem exists_iSup_integral_div_eq_bipolarRate [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ (len : ℕ → ℕ) (g : (i : ℕ) → (Fin (len i) → 𝓧) → ℝ), (∀ i, 1 ≤ len i) ∧
      (∀ i, Measurable (g i)) ∧ (∀ i, ∃ C, ∀ x, |g i x| ≤ C) ∧
      (∀ i, IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) (sampleNull S₁ (len i))) ∧
      ∀ (Q : Measure 𝓧) [IsProbabilityMeasure Q], Q ≪ ρ →
        ⨆ i, (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q)) / len i : ℝ) : EReal) =
          bipolarRate Q S₁ := by
  choose u hu hdense using fun p : ℕ × ℕ ↦ exists_seq_boundedLogEVarSet hS₁ ρ (p.1 + 1) p.2
  let e : ℕ ≃ (ℕ × ℕ) × ℕ := (Denumerable.eqv _).symm
  have hge (i : ℕ) : IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (u (e i).1 (e i).2 x)))
      (sampleNull S₁ ((e i).1.1 + 1)) :=
    ⟨ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hu _ _).1),
      forall_mem_sampleNull.2 (hu _ _).2.2⟩
  refine ⟨fun i ↦ (e i).1.1 + 1, fun i ↦ u (e i).1 (e i).2, fun i ↦ Nat.le_add_left 1 _,
    fun i ↦ (hu _ _).1, fun i ↦ ⟨_, (hu _ _).2.1⟩, hge, fun Q _ hQρ ↦
      le_antisymm (iSup_le fun i ↦ integral_div_le_bipolarRate (Nat.succ_ne_zero _)
        (.of_bound (hu _ _).1.aestronglyMeasurable _ (ae_of_all _ fun x ↦ by
          simpa [Real.norm_eq_abs] using (hu _ _).2.1 x)) (hge i)) ?_⟩
  -- every exponent `t` below the bipolar rate is beaten by a member of the family
  refine EReal.ge_of_forall_gt_iff_ge.1 fun t ht ↦ ?_
  obtain ⟨m, E, hE, hEt⟩ := exists_isEVar_lt_eintegral_of_lt_bipolarRate ht
  obtain ⟨N, f, hf, hft⟩ := exists_mem_boundedLogEVarSet_lt_integral Q hS₁ hE hEt
  obtain ⟨j, hj⟩ := hdense (m, N) Q inferInstance hQρ f hf _ hft
  refine le_iSup_of_le (e.symm ((m, N), j)) ?_
  -- `e (e.symm ((m, N), j))` occurs both in the integrand and in the type `Fin (_ + 1) → 𝓧` of
  -- its argument, so rewriting it with `Equiv.apply_symm_apply` gives an ill-typed motive; we
  -- generalize it to a variable and substitute instead.
  beta_reduce
  generalize hp : e (e.symm ((m, N), j)) = p
  rw [Equiv.apply_symm_apply] at hp
  subst hp
  rw [EReal.coe_le_coe_iff, le_div_iff₀ (by positivity)]
  push_cast
  exact hj.le

/-! ### Products of an exponential over consecutive blocks -/

/-- The product of `exp g` over the first `k` blocks of `m` observations is the exponential of the
sum of `g` over them. -/
private lemma seqBlockProd_ofReal_exp {m : ℕ} (g : (Fin m → 𝓧) → ℝ) (k : ℕ) (ω : ℕ → 𝓧) :
    seqBlockProd m (fun x ↦ ENNReal.ofReal (Real.exp (g x))) k ω =
      ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range k, g (seqBlock m j ω))) := by
  rw [seqBlockProd_def, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (Real.exp_pos _).le]

/-! ### The weights of the numbers of blocks

The weight of `k` blocks in the mixture is `coverWeight (k + 1) = 1 / ((k + 1) (k + 2))`, the
weight of the covering mixture of `AlmostSure.lean`. -/

/-- The logarithm of the weight of `n / L` blocks, divided by `n`, tends to `0`. -/
private lemma tendsto_log_coverWeight_div (L : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log (coverWeight (n / L + 1)) / n) atTop (𝓝 0) := by
  have hlog2 : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 2) / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp, pow_one, one_mul]
    ring_nf
  have hlow := hlog2.const_mul (-2)
  rw [mul_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ ?_)
  · have hk : ((n / L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n L
    have hge : 1 / ((n : ℝ) + 2) ^ 2 ≤ coverWeight (n / L + 1) := by
      rw [coverWeight_def]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith [(Nat.cast_nonneg (n / L) : (0 : ℝ) ≤ (n / L : ℕ))]
    have hlog : -(2 * Real.log ((n : ℝ) + 2)) ≤ Real.log (coverWeight (n / L + 1)) := by
      calc -(2 * Real.log ((n : ℝ) + 2)) = Real.log (1 / ((n : ℝ) + 2) ^ 2) := by
            rw [one_div, Real.log_inv, Real.log_pow]
            push_cast
            ring
      _ ≤ Real.log (coverWeight (n / L + 1)) := Real.log_le_log (by positivity) hge
    rw [mul_div_assoc', neg_mul]
    exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
  · refine div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos (coverWeight_pos (Nat.succ_pos _)).le ?_) (Nat.cast_nonneg n)
    rw [coverWeight_def]
    rw [div_le_one (by positivity)]
    push_cast
    nlinarith [(Nat.cast_nonneg (n / L) : (0 : ℝ) ≤ (n / L : ℕ))]

/-! ### The mixture over the family and the numbers of blocks -/

/-- The term of the mixture for the function `g i` on blocks of `len i` observations, played on
`k` blocks: the product of `exp (g i)` over the blocks, with weight
`2⁻¹ ^ (i + 1) * coverWeight (k + 1)`. -/
private noncomputable def blockMixtureTerm (len : ℕ → ℕ) (g : (i : ℕ) → (Fin (len i) → 𝓧) → ℝ)
    (i k : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  2⁻¹ ^ (i + 1) * (ENNReal.ofReal (coverWeight (k + 1)) *
    seqBlockProd (len i) (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) k ω)

/-- **The mixture over the family and the numbers of blocks**: at time `n`, the sum of the terms
for all `(i, k)` with `k * len i ≤ n`, that is, whose blocks are among the first `n` observations.
Each term is held from the time its blocks are observed on, which makes the process
nondecreasing. -/
private noncomputable def blockMixture (len : ℕ → ℕ) (g : (i : ℕ) → (Fin (len i) → 𝓧) → ℝ)
    (n : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑' i, ∑' k, if k * len i ≤ n then blockMixtureTerm len g i k ω else 0

variable {len : ℕ → ℕ} {g : (i : ℕ) → (Fin (len i) → 𝓧) → ℝ}

/-- The mixture is nondecreasing in time. -/
private lemma monotone_blockMixture : Monotone (blockMixture len g) :=
  fun n n' hnn' ω ↦ tsum_le_tsum fun i ↦ tsum_le_tsum fun k ↦ by
    by_cases h : k * len i ≤ n
    · rw [ite_eq_left h, ite_eq_left (h.trans hnn')]
    · rw [ite_eq_right h]
      exact zero_le

/-- **The mixture is an e-process.** It holds each product over blocks from the time its blocks
are observed on, and the weights sum to at most `1`, so it is a mixture of held bets
(`ProbabilityTheory.isEProcess_tsum_ite_le_mul`); each product over blocks is a bet for the
i.i.d. null (`ProbabilityTheory.isEVar_seqBlockProd`). -/
private lemma isEProcess_blockMixture (hg : ∀ i, Measurable (g i))
    (hge : ∀ i, IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) (sampleNull S₁ (len i))) :
    IsEProcess (blockMixture len g) (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁) := by
  have hw : ∑' p : ℕ × ℕ, (2⁻¹ : ℝ≥0∞) ^ (p.1 + 1) * ENNReal.ofReal (coverWeight (p.2 + 1)) ≤ 1 :=
    calc ∑' p : ℕ × ℕ, (2⁻¹ : ℝ≥0∞) ^ (p.1 + 1) * ENNReal.ofReal (coverWeight (p.2 + 1))
    _ = ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * ∑' k : ℕ, ENNReal.ofReal (coverWeight (k + 1)) := by
      rw [tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * 1 := tsum_le_tsum fun i ↦ by
      gcongr
      exact tsum_ofReal_coverWeight_succ_le_one
    _ = 1 := by simp only [mul_one, ENNReal.tsum_geometric_two_add_one]
  have h := isEProcess_tsum_ite_le_mul (ℱ := Filtration.piLT (X := fun _ : ℕ ↦ 𝓧))
    (t := fun p : ℕ × ℕ ↦ p.2 * len p.1)
    (E := fun p ↦ seqBlockProd (len p.1) (fun x ↦ ENNReal.ofReal (Real.exp (g p.1 x))) p.2)
    (fun p ↦ Filtration.measurable_piLT_of_dependsOn (measurable_seqBlockProd
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg p.1))) p.2)
      (dependsOn_seqBlockProd _ p.2))
    (fun p ↦ isEVar_seqBlockProd (hge p.1) p.2) hw
  convert h using 2 with n
  ext ω
  simp only [tsum_prod', blockMixture, blockMixtureTerm, mul_assoc]

/-- The weight of `n / L` blocks costs `o(n)`: if the averages `s k / k` tend to `μ`, then
`(s (n / L) + log (c * coverWeight (n / L + 1))) / n` tends to `μ / L`, for `c > 0` and `L ≥ 1`. -/
private lemma tendsto_add_log_coverWeight_div {s : ℕ → ℝ} {μ c : ℝ} {L : ℕ} (hL : 1 ≤ L)
    (hc : 0 < c) (hs : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹ * s k) atTop (𝓝 μ)) :
    Tendsto (fun n : ℕ ↦ (s (n / L) + Real.log (c * coverWeight (n / L + 1))) / n) atTop
      (𝓝 (μ / L)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hkn : Tendsto (fun n : ℕ ↦ n / L) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have h1 : Tendsto (fun n : ℕ ↦ ((n / L : ℕ) : ℝ)⁻¹ * s (n / L)) atTop (𝓝 μ) := hs.comp hkn
  have h2 : Tendsto (fun n : ℕ ↦ ((n / L : ℕ) : ℝ) / n) atTop (𝓝 (1 / L)) := by
    have hdiv : Tendsto (fun n : ℕ ↦ (n : ℝ) / L) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const hL0
    have := (tendsto_nat_floor_div_atTop.comp hdiv).mul_const (1 / (L : ℝ))
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    simp only [Function.comp, Nat.floor_div_eq_div]
    field_simp
  have h3 : Tendsto (fun n : ℕ ↦ Real.log c / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := (h2.mul h1).add (h3.add (tendsto_log_coverWeight_div L))
  have heq : 1 / (L : ℝ) * μ + (0 + 0) = μ / L := by ring
  rw [heq] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop L] with n hn
  have hk0 : ((n / L : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ n / L := (Nat.one_le_div_iff (by omega)).2 hn
    positivity
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 1 ≤ n := hL.trans hn
    positivity
  rw [Real.log_mul hc.ne' (coverWeight_pos (Nat.succ_pos _)).ne']
  field_simp

/-- Each term of the mixture whose blocks are among the first `n` observations is at most the
mixture at time `n`. -/
private lemma blockMixtureTerm_le_blockMixture {i k n : ℕ} (h : k * len i ≤ n) (ω : ℕ → 𝓧) :
    blockMixtureTerm len g i k ω ≤ blockMixture len g n ω :=
  calc blockMixtureTerm len g i k ω
  _ = if k * len i ≤ n then blockMixtureTerm len g i k ω else 0 := (ite_eq_left h).symm
  _ ≤ ∑' k, if k * len i ≤ n then blockMixtureTerm len g i k ω else 0 :=
    le_tsum (fun k ↦ if k * len i ≤ n then blockMixtureTerm len g i k ω else 0) k
  _ ≤ blockMixture len g n ω :=
    le_tsum (fun i ↦ ∑' k, if k * len i ≤ n then blockMixtureTerm len g i k ω else 0) i

/-- The term of `k` blocks of `g i` is the exponential of the sum of `g i` over the blocks plus
the logarithm of its weight. -/
private lemma ofReal_exp_eq_blockMixtureTerm (i k : ℕ) (ω : ℕ → 𝓧) :
    ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range k, g i (seqBlock (len i) j ω) +
        Real.log (2⁻¹ ^ (i + 1) * coverWeight (k + 1)))) = blockMixtureTerm len g i k ω := by
  have hw := coverWeight_pos (Nat.succ_pos k)
  simp only [blockMixtureTerm, seqBlockProd_ofReal_exp]
  rw [Real.exp_add, Real.exp_log (mul_pos (by positivity) hw), mul_comm,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow, mul_assoc]

/-- **Growth of the mixture.** Almost surely under the i.i.d. law of `Q`, the mixture grows at
least at the rate `∫ g i ∂Q ^ len i / len i` of each member of the family, by the strong law of
large numbers along the blocks. -/
private lemma le_liminf_log_blockMixture (Q : Measure 𝓧) [IsProbabilityMeasure Q] {i : ℕ}
    (hlen : 1 ≤ len i) (hg : Measurable (g i)) {C : ℝ} (hgC : ∀ x, |g i x| ≤ C) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q)) / len i : ℝ) : EReal) ≤
        liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop := by
  have hint : Integrable (g i) (Measure.pi fun _ : Fin (len i) ↦ Q) :=
    .of_bound hg.aestronglyMeasurable C (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hgC x)
  filter_upwards [strong_law_ae_seqBlock Q hint] with ω hω
  -- the logarithm of the term of `n / len i` blocks of `g i`
  set r : ℕ → ℝ := fun n ↦ ∑ j ∈ Finset.range (n / len i), g i (seqBlock (len i) j ω) +
    Real.log (2⁻¹ ^ (i + 1) * coverWeight (n / len i + 1))
  have hbound (n : ℕ) : ENNReal.ofReal (Real.exp (r n)) ≤ blockMixture len g n ω :=
    (ofReal_exp_eq_blockMixtureTerm i (n / len i) ω).trans_le
      (blockMixtureTerm_le_blockMixture (Nat.div_mul_le_self n (len i)) ω)
  have hle : ∀ᶠ n : ℕ in atTop,
      ((r n / n : ℝ) : EReal) ≤ ENNReal.log (blockMixture len g n ω) / (n : EReal) := by
    refine Eventually.of_forall fun n ↦ ?_
    rw [EReal.coe_div, EReal.coe_natCast]
    refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast Nat.zero_le n) ?_
    calc (r n : EReal) = ENNReal.log (ENNReal.ofReal (Real.exp (r n))) := by
          rw [ENNReal.log_ofReal_exp]
    _ ≤ ENNReal.log (blockMixture len g n ω) := ENNReal.log_le_log (hbound n)
  -- `r n / n` tends to `∫ g i / len i`, by the strong law along blocks
  have hlim := tendsto_add_log_coverWeight_div hlen (by positivity : (0 : ℝ) < 2⁻¹ ^ (i + 1))
    (by simpa only [smul_eq_mul] using hω)
  calc (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q)) / len i : ℝ) : EReal)
  _ = liminf (fun n : ℕ ↦ ((r n / n : ℝ) : EReal)) atTop :=
        ((continuous_coe_real_ereal.tendsto _).comp hlim).liminf_eq.symm
  _ ≤ liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop :=
    liminf_le_liminf hle

/-- **Growth of the mixture at the bipolar rate.** If the normalized means of the family have
supremum the bipolar rate of `Q₁`, then almost surely under the i.i.d. law of `Q₁`,
`(1/n) log` of the mixture tends to the bipolar rate: each member of the family bounds the
`liminf` from below, and no e-process grows faster
(`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`). -/
private lemma ae_tendsto_log_blockMixture_div (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hlen : ∀ i, 1 ≤ len i) (hg : ∀ i, Measurable (g i)) (hgC : ∀ i, ∃ C, ∀ x, |g i x| ≤ C)
    (hge : ∀ i, IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) (sampleNull S₁ (len i)))
    (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hsup : ⨆ i, (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q₁)) / len i : ℝ) : EReal) =
      bipolarRate Q₁ S₁) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  have hE := isEProcess_blockMixture (S₁ := S₁) hg hge
  -- the lower bound, from each member of the family
  have hlow : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ i,
      (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q₁)) / len i : ℝ) : EReal) ≤
        liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop :=
    ae_all_iff.2 fun i ↦ le_liminf_log_blockMixture Q₁ (hlen i) (hg i) (hgC i).choose_spec
  -- the upper bound holds for every e-process
  filter_upwards [hE.ae_limsup_log_div_le_bipolarRate Q₁ hS₁, hlow] with ω hωup hωlow
  refine tendsto_of_le_liminf_of_limsup_le ?_ hωup
  rw [← hsup]
  exact iSup_le hωlow

/-! ### The universal e-process -/

/-- **One e-process at the bipolar rate for every dominated alternative.** For a countably
generated space, a null `S₁` of probability measures and an s-finite measure `ρ`, there is one
e-process `E` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT` of
the observations, nondecreasing in time, such that for every probability measure `Q₁ ≪ ρ`,
almost surely under the i.i.d. law of `Q₁`, `(1/n) log (E n)` tends to the bipolar rate
`bipolarRate Q₁ S₁`; at time `n`, `E n` is a function of the first `n` observations. This is the
theorem of [EVR26, Note 13]. -/
theorem exists_isEProcess_ae_tendsto_log_div_bipolarRate [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ E : ℕ → (ℕ → 𝓧) → ℝ≥0∞,
      IsEProcess E (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁) ∧ Monotone E ∧
      ∀ (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁], Q₁ ≪ ρ →
        ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
          Tendsto (fun n : ℕ ↦ ENNReal.log (E n ω) / (n : EReal)) atTop
            (𝓝 (bipolarRate Q₁ S₁)) := by
  obtain ⟨len, g, hlen, hgm, hgb, hge, hsup⟩ :=
    exists_iSup_integral_div_eq_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) ρ
  exact ⟨blockMixture len g, isEProcess_blockMixture hgm hge, monotone_blockMixture,
    fun Q₁ _ hQ₁ρ ↦ ae_tendsto_log_blockMixture_div hS₁ hlen hgm hgb hge Q₁ (hsup Q₁ hQ₁ρ)⟩

/-! ### The expected time of the tests -/

/-- The logarithm of the weight `2⁻¹ ^ (i + 1) * coverWeight (k + 1)` of `k` blocks of `g i` is
at least `-((i + 1) log 2 + 2 δ + 2 log (2 / δ)) - δ k`, for every `δ > 0`: the weight costs at
most `δ` per block, up to a constant. -/
private lemma neg_sub_le_log_weight {δ : ℝ} (hδ : 0 < δ) (i k : ℕ) :
    -((i + 1) * Real.log 2 + (2 * δ + 2 * Real.log (2 / δ))) - δ * k ≤
      Real.log (2⁻¹ ^ (i + 1) * coverWeight (k + 1)) := by
  have hw := coverWeight_pos (Nat.succ_pos k)
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  have hcw : coverWeight (k + 1) = (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹ := by
    rw [coverWeight_def, one_div]
    push_cast
    ring_nf
  rw [Real.log_mul (by positivity) hw.ne', Real.log_pow, Real.log_inv, hcw, Real.log_inv,
    Real.log_mul hk1.ne' hk2.ne']
  have hA : Real.log (k + 1) ≤ Real.log (k + 2) := Real.log_le_log hk1 (by linarith)
  have hB : Real.log (k + 2) = Real.log (δ * (k + 2) / 2) + Real.log (2 / δ) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hC : Real.log (δ * (k + 2) / 2) ≤ δ * (k + 2) / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  push_cast
  nlinarith

/-- **The expected time of the tests, from one block bet.** Let `g i` be a member of the family
with `c * len i < ∫ g i ∂Q₁ ^ len i`, for some `c > 0`. The first time `τ α` at which the mixture
reaches `α⁻¹` satisfies `limsup_{α → 0} 𝔼[τ α] / log (1/α) ≤ 1 / c` under the i.i.d. law of
`Q₁`. With `δ` half of the margin `∫ g i ∂Q₁ ^ len i - c * len i`, the mixture reaches `α⁻¹`
at the latest at `len i` times the first time the random walk of the values of `g i - δ` on the
blocks reaches `log (1/α)` plus a constant. This walk has increments bounded above and of mean
`∫ g i ∂Q₁ ^ len i - δ`, and Wald's bound on first passage times concludes
(`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`). -/
private lemma limsup_lintegral_hittingAfter_blockMixture_div_log_le (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] {i : ℕ} (hlen : 1 ≤ len i) (hg : Measurable (g i)) {C : ℝ}
    (hgC : ∀ x, |g i x| ≤ C) {c : ℝ} (hc : 0 < c)
    (hci : c * len i < ∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q₁)) :
    limsup (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) ≤
      ENNReal.ofReal c⁻¹ := by
  set m := len i
  set μ := ∫ x, g i x ∂Measure.pi (fun _ : Fin m ↦ Q₁)
  set δ := (μ - c * m) / 2 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    linarith
  set a := μ - δ with ha
  have hca : c * m < a := by
    rw [ha, hδ]
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hlen
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) hca
  set A := (i + 1) * Real.log 2 + (2 * δ + 2 * Real.log (2 / δ))
  -- the random walk of the values of `g i - δ` on the blocks
  set Y : ℕ → (ℕ → 𝓧) → ℝ := fun j ω ↦ g i (seqBlock m j ω) - δ
  have hYi : iIndepFun Y (Measure.infinitePi fun _ : ℕ ↦ Q₁) :=
    (iIndepFun_seqBlock (fun _ : ℕ ↦ Q₁) m).comp (fun _ x ↦ g i x - δ)
      (fun _ ↦ hg.sub_const δ)
  have hYm : ∀ j, Measurable (Y j) := fun j ↦ (hg.comp (measurable_seqBlock m j)).sub_const δ
  have hYa : ∀ j, a ≤ ∫ ω, Y j ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
    intro j
    have hint : Integrable (fun ω ↦ g i (seqBlock m j ω)) (Measure.infinitePi fun _ : ℕ ↦ Q₁) :=
      .of_bound (hg.comp (measurable_seqBlock m j)).aestronglyMeasurable C
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact hgC _)
    -- the `j`-th block has the law `Q₁ ^ m`
    have hmp := measurePreserving_seqBlock (fun _ : ℕ ↦ Q₁) m j
    simp only [Y]
    rw [integral_sub hint (integrable_const δ), ← integral_map
      (measurable_seqBlock m j).aemeasurable (hmp.map_eq ▸ hg.aestronglyMeasurable), hmp.map_eq,
      integral_const, probReal_univ, one_smul]
  have hYC : ∀ j, ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), Y j ω ≤ C := fun j ↦
    ae_of_all _ fun ω ↦ by
      simp only [Y]
      linarith [le_abs_self (g i (seqBlock m j ω)), hgC (seqBlock m j ω)]
  refine ENNReal.limsup_div_toENNReal_log_inv_le (K := ENNReal.ofReal (m * (A + C) / a))
    ENNReal.ofReal_ne_top fun α hα0 hα1 ↦ ?_
  set L := (ENNReal.log α⁻¹).toReal with hL
  have hlogtop : ENNReal.log α⁻¹ ≠ ⊤ := by simpa using hα0.ne'
  have hLL : (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal L := EReal.toENNReal_of_ne_top hlogtop
  have hL0 : 0 ≤ L := EReal.toReal_nonneg
    (ENNReal.zero_lt_log_iff.2 (ENNReal.one_lt_inv.2 hα1)).le
  -- the pathwise bound by the first time the walk reaches `L + A`
  have hpath : ∀ ω, ENat.toENNReal (hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0 ω) ≤
      m * ENat.toENNReal (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, Y j ω)
        (Set.Ici (L + A)) 0 ω) := by
    intro ω
    set N := hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, Y j ω) (Set.Ici (L + A)) 0 ω
      with hN
    rcases eq_or_ne N ⊤ with hNt | hNt
    · have h1 : ENat.toENNReal N = ⊤ := ENat.toENNReal_eq_top.2 hNt
      rw [h1, ENNReal.mul_top (by positivity)]
      exact le_top
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hNt
    have hmem := hittingAfter_mem_set_of_ne_top hNt
    rw [← hN, ← hk] at hmem
    replace hmem : L + A ≤ ∑ j ∈ Finset.range k, Y j ω := hmem
    have hle : hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0 ω ≤ (k * m : ℕ) := by
      refine hittingAfter_le_of_mem (Nat.zero_le _) ?_
      rw [Set.mem_Ici, ← ENNReal.log_le_log_iff]
      refine (EReal.le_coe_toReal hlogtop).trans ?_
      refine le_trans ?_ (ENNReal.log_le_log (blockMixtureTerm_le_blockMixture le_rfl ω))
      rw [← ofReal_exp_eq_blockMixtureTerm, ENNReal.log_ofReal_exp, EReal.coe_le_coe_iff]
      have hsum : ∑ j ∈ Finset.range k, Y j ω =
          ∑ j ∈ Finset.range k, g i (seqBlock m j ω) - δ * k := by
        simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      have hw := neg_sub_le_log_weight hδ0 i k
      rw [hsum] at hmem
      rw [← hL]
      linarith
    calc ENat.toENNReal (hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0 ω)
    _ ≤ ENat.toENNReal ((k * m : ℕ) : ℕ∞) := ENat.toENNReal_le.2 hle
    _ = m * ENat.toENNReal N := by
      have h2 : ENat.toENNReal N = k := by
        rw [← hk]
        exact ENat.toENNReal_coe k
      rw [h2, ENat.toENNReal_coe]
      push_cast
      ring
  have hwald := hYi.lintegral_hittingAfter_sum_le hYm ha0 hYa hYC (L + A)
  calc ∫⁻ ω, ENat.toENNReal (hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0 ω)
      ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  _ ≤ ∫⁻ ω, m * ENat.toENNReal (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, Y j ω)
        (Set.Ici (L + A)) 0 ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := lintegral_mono hpath
  _ = m * ∫⁻ ω, ENat.toENNReal (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, Y j ω)
        (Set.Ici (L + A)) 0 ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) :=
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m)
  _ ≤ m * ENNReal.ofReal ((L + A + C) / a) := by gcongr
  _ = ENNReal.ofReal (m * (A + C) / a + L * (m / a)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  _ ≤ ENNReal.ofReal (m * (A + C) / a) + ENNReal.ofReal (L * (m / a)) := ENNReal.ofReal_add_le
  _ ≤ ENNReal.ofReal (m * (A + C) / a) + (ENNReal.log α⁻¹).toENNReal * ENNReal.ofReal c⁻¹ := by
    rw [hLL, ← ENNReal.ofReal_mul hL0]
    gcongr
    rw [div_le_iff₀ ha0, inv_mul_eq_div, le_div_iff₀ hc]
    linarith

/-! ### The tests at the bipolar rate -/

/-- **Tests at the bipolar rate for every dominated alternative.** For a countably generated
space, a null `S₁` of probability measures and an s-finite measure `ρ`, there is one e-process
`E` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT` of the
observations, nondecreasing in time, whose tests are at the rate of every alternative dominated by
`ρ`. The first time `τ α = hittingAfter E (Set.Ici α⁻¹) 0` at which `E` reaches `α⁻¹` is a
sequential test of level `α` (`IsEProcess.isLevelStoppingTime_hittingAfter`), and for every
probability measure `Q₁ ≪ ρ`, under the i.i.d. law of `Q₁`, `τ α / log (1/α)` tends to
`1 / bipolarRate Q₁ S₁` as `α → 0`, almost surely and in expectation. No sequential test of level
`α` makes fewer than `log (1/α) / bipolarRate Q₁ S₁` observations in expectation
(`toENNReal_log_inv_div_bipolarRate_le_lintegral`), so these tests are first-order optimal at
every `Q₁ ≪ ρ` at once. This is the theorem of [EVR26, Note 13], which states the limits when
`0 < bipolarRate Q₁ S₁ < ∞`; in `ℝ≥0∞`, with `1 / 0 = ∞` and `1 / ∞ = 0`, they hold at every
`Q₁ ≪ ρ`. -/
theorem exists_isEProcess_tendsto_hittingAfter_div_log [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ E : ℕ → (ℕ → 𝓧) → ℝ≥0∞,
      IsEProcess E (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁) ∧ Monotone E ∧
      ∀ (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁], Q₁ ≪ ρ →
        (∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
          Tendsto (fun α : ℝ≥0∞ ↦ ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) /
              (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
            (𝓝 (bipolarRate Q₁ S₁).toENNReal⁻¹)) ∧
        Tendsto (fun α : ℝ≥0∞ ↦
            (∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω)
              ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) / (ENNReal.log α⁻¹).toENNReal)
          (𝓝[>] 0) (𝓝 (bipolarRate Q₁ S₁).toENNReal⁻¹) := by
  obtain ⟨len, g, hlen, hgm, hgb, hge, hsup⟩ :=
    exists_iSup_integral_div_eq_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) ρ
  have hE := isEProcess_blockMixture (S₁ := S₁) hgm hge
  refine ⟨blockMixture len g, hE, monotone_blockMixture, fun Q₁ _ hQ₁ρ ↦ ⟨?_, ?_⟩⟩
  · -- almost surely: from below for every family of nested tests, from above by the growth
    have hlow := ae_inv_toENNReal_bipolarRate_le_liminf_div_log Q₁ hS₁
      (τ := fun α ↦ hittingAfter (blockMixture len g) (Set.Ici α⁻¹) 0) zero_lt_one
      (fun α _ ↦ hE.isLevelStoppingTime_hittingAfter α)
      (fun ω α _ β _ hαβ ↦ hittingAfter_apply_anti _ 0 ω
        (Set.Ici_subset_Ici.2 (ENNReal.inv_le_inv.2 hαβ)))
    filter_upwards [hlow, ae_tendsto_log_blockMixture_div hS₁ hlen hgm hgb hge Q₁
      (hsup Q₁ hQ₁ρ)] with ω hωl hωg
    exact tendsto_of_le_liminf_of_limsup_le hωl
      (limsup_toENNReal_hittingAfter_div_log_le hωg.liminf_eq.ge)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- in expectation, from below: for every test of level `α`
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ≥0∞) < 1)] with α ⟨hα0, hα1⟩
    have h := toENNReal_log_inv_div_bipolarRate_le_lintegral Q₁ hS₁
      (hE.isLevelStoppingTime_hittingAfter α)
    set B := (ENNReal.log α⁻¹).toENNReal
    have hB0 : B ≠ 0 :=
      EReal.toENNReal_ne_zero_iff.2 (ENNReal.zero_lt_log_iff.2 (ENNReal.one_lt_inv.2 hα1))
    have hBtop : B ≠ ⊤ := by simpa [B] using hα0.ne'
    calc (bipolarRate Q₁ S₁).toENNReal⁻¹
    _ = B / (bipolarRate Q₁ S₁).toENNReal / B := by
      rw [div_eq_mul_inv B, mul_comm B, ENNReal.mul_div_cancel_right hB0 hBtop]
    _ ≤ _ := ENNReal.div_le_div_right h B
  · -- in expectation, from above: for every rate `c` below the bipolar rate, by one block bet
    refine EReal.le_inv_toENNReal_iff.2 fun c hc hcd ↦ ?_
    rw [← hsup Q₁ hQ₁ρ] at hcd
    obtain ⟨i, hi⟩ := lt_iSup_iff.1 hcd
    rw [EReal.coe_lt_coe_iff, lt_div_iff₀ (by exact_mod_cast hlen i)] at hi
    exact limsup_lintegral_hittingAfter_blockMixture_div_log_le Q₁ (hlen i) (hgm i)
      (hgb i).choose_spec hc hi

end ProbabilityTheory
