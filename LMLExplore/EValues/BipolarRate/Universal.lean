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
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Analysis.SpecialFunctions.Log.TruncLog
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.Null.PrefixBet
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
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

## Main statements

* `ProbabilityTheory.exists_isEProcess_ae_tendsto_log_div_bipolarRate`: one nondecreasing
  e-process for the i.i.d. null grows at the bipolar rate of every alternative `Q₁ ≪ ρ`, almost
  surely.

## Implementation notes

The proof has three steps.

* **A countable family that determines the bipolar rate.** For `m` observations and `N : ℕ`,
  consider the measurable functions `f` of `m` observations with `|f| ≤ N` and
  `∫ exp f ∂P ^ m ≤ 1` for every `P ∈ S₁`: the logarithms of bounded e-variables. A sequence of
  them that is dense in `L¹` of the finite measure `ρ.toFinite ^ m`, which is separable since `𝓧`
  is countably generated, approximates the mean under `Q₁ ^ m` of each of them, for every
  `Q₁ ≪ ρ`, by dominated convergence. Mixing an e-variable with a constant and truncating its
  logarithm shows that these means determine the bipolar rate: for every `t < bipolarRate Q₁ S₁`,
  one member `g` of the countable family, on `m` observations, has `t m < ∫ g ∂Q₁ ^ m`.
* **Products over blocks.** For such a `g` on blocks of `m` observations, the product
  `seqBlockProd m (exp ∘ g) k` of `exp g` over the first `k` consecutive blocks is an e-variable
  for the i.i.d. null, as the blocks are independent (`ProbabilityTheory.isEVar_seqBlockProd`),
  and its logarithm divided by `k` tends to `∫ g ∂Q₁ ^ m` almost surely, by the strong law of
  large numbers along the blocks (`ProbabilityTheory.strong_law_ae_seqBlock`).
* **The mixture.** The e-process at time `n` is the sum, over the members `g i` of the family
  and the numbers `k` of blocks of `g i` that fit in the first `n` observations, of these
  products, with weights `2⁻¹ ^ (i + 1) / ((k + 1) (k + 2))`. Each term is held from the time its
  blocks are observed on, which makes the process nondecreasing, and the sum of all the terms has
  expectation at most `1` under the null, so the value at every stopping time is an e-variable.
  The weight of the number of blocks costs `o(n)` in the logarithm, which gives the lower bound
  on the growth; the upper bound is
  `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`.

The statement is the theorem of [EVR26, Note 13] (`results/13-universal-eprocess.md` there). The
note builds the e-process from the running maxima of the block products, passed through an
adjuster, and Ville's inequality; the proof here uses the mixture over the number of blocks
instead, which needs neither. The statement and its proof are adapted from
`EValuesResearch/Results/UniversalEProcess.lean` (commit `a1002bc`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 13, *One e-process at the bipolar rate for every dominated
  alternative*, Theorem.
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
private lemma zero_mem_boundedLogEVarSet (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (m N : ℕ) :
    (0 : (Fin m → 𝓧) → ℝ) ∈ boundedLogEVarSet S₁ m N := by
  refine ⟨measurable_const, fun _ ↦ by simp, fun P hP ↦ ?_⟩
  have := hS₁ P hP
  simp

/-- **A countable dense family.** On a countably generated space, for an s-finite `ρ`, a sequence
in `boundedLogEVarSet S₁ m N` approximates the mean under `Q ^ m` of every member, for every
probability measure `Q ≪ ρ`. It is dense in `L¹` of the finite measure `ρ.toFinite ^ m`, which is
separable. -/
private lemma exists_seq_boundedLogEVarSet [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] (m N : ℕ) :
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
  choose u hu hvu using fun j ↦ (v j).2
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

/-- For `a > 0`, some `ε ∈ (0, 1)` has `log (1 - ε) = -a`. -/
private lemma exists_log_one_sub_eq_neg {a : ℝ} (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ Real.log (1 - ε) = -a := by
  refine ⟨1 - Real.exp (-a), ?_, by linarith [Real.exp_pos (-a)],
    by rw [sub_sub_cancel, Real.log_exp]⟩
  have : Real.exp (-a) < 1 := by simpa using Real.exp_lt_exp.2 (show -a < 0 by linarith)
  linarith

/-- **Truncation.** If an `m`-sample e-variable has expected logarithm larger than `c` under
`Q ^ m`, so has the truncated logarithm of its mixture with a constant, which is bounded. -/
private lemma exists_mem_boundedLogEVarSet_lt_integral (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {m : ℕ}
    {E : (Fin m → 𝓧) → ℝ≥0∞} (hE : IsEVar E (sampleNull S₁ m))
    {c : ℝ} (hc : (c : EReal) < ∫ᵉ x, ENNReal.log (E x) ∂Measure.pi (fun _ : Fin m ↦ Q)) :
    ∃ N : ℕ, ∃ f ∈ boundedLogEVarSet S₁ m N, c < ∫ x, f x ∂Measure.pi (fun _ : Fin m ↦ Q) := by
  obtain ⟨c', hcc', hc'⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  rw [EReal.coe_lt_coe_iff] at hcc'
  set η := c' - c with hη
  have hη0 : 0 < η := by linarith
  obtain ⟨ε, hε0, hε1, hlogε⟩ := exists_log_one_sub_eq_neg (half_pos hη0)
  set μ := Measure.pi (fun _ : Fin m ↦ Q)
  -- truncate the logarithm at a level `k`, by monotone convergence
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((c + η / 2 : ℝ) : EReal) < ∫ᵉ x, min (ENNReal.log (E x)) k ∂μ := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have h' := hc'.le.trans (eintegral_le_of_forall_min_le
      (ENNReal.measurable_log.comp hE.measurable) h)
    rw [EReal.coe_le_coe_iff] at h'
    linarith
  -- mix with the constant `ε`, which bounds the logarithm below
  set F : (Fin m → 𝓧) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε
  set f : (Fin m → 𝓧) → ℝ := fun x ↦ ENNReal.truncLog k (F x)
  have hF0 : ∀ x, F x ≠ 0 := fun x ↦ by simp [F, hε0]
  have hlogε0 : Real.log ε ≤ k := (Real.log_nonpos hε0.le hε1.le).trans (Nat.cast_nonneg k)
  set N := ⌈max (k : ℝ) (-Real.log ε)⌉₊
  have hfb : ∀ x, |f x| ≤ N := by
    intro x
    have h1 := ENNReal.truncLog_le (c := k) (hF0 x)
    have h2 := ENNReal.log_le_truncLog hε0 (le_add_self : ENNReal.ofReal ε ≤ F x) hlogε0
    have h3 := Nat.le_ceil (max (k : ℝ) (-Real.log ε))
    have h4 := le_max_left (k : ℝ) (-Real.log ε)
    have h5 := le_max_right (k : ℝ) (-Real.log ε)
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hfm : Measurable f :=
    (ENNReal.measurable_truncLog _).comp ((measurable_const.mul hE.measurable).add measurable_const)
  have hint : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable _
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hfb x)
  refine ⟨N, f, ⟨hfm, hfb, fun P hP ↦ ?_⟩, ?_⟩
  · calc ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂Measure.pi (fun _ : Fin m ↦ P)
    _ ≤ ∫⁻ x, F x ∂Measure.pi (fun _ : Fin m ↦ P) :=
      lintegral_mono fun x ↦ ENNReal.ofReal_exp_truncLog_le (hF0 x)
    _ ≤ 1 := (hE.ofReal_one_sub_mul_add_ofReal
      (measure_univ_le_one_of_mem_sampleNull (fun P hP ↦ (hS₁ P hP).measure_univ.le) m) hε0.le
        hε1.le).lintegral_le_one (pi_mem_sampleNull hP)
  · have h : ((c + η / 2 : ℝ) : EReal) < ((∫ x, f x ∂μ - Real.log (1 - ε) : ℝ) : EReal) :=
      hk.trans_le (eintegral_min_log_le_integral_truncLog_sub hε0 hε1 k hint)
    rw [EReal.coe_lt_coe_iff, hlogε] at h
    linarith

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

/-- **A countable family that determines the bipolar rate.** On a countably generated space, for
an s-finite `ρ`, there are bounded functions `g i` of `len i` observations, the logarithms of
e-variables for the null of `len i`-samples, such that every exponent `t` below the bipolar rate
of a probability measure `Q ≪ ρ` is beaten by some `∫ g i ∂Q ^ len i / len i`. -/
private lemma exists_rateFamily [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ (len : ℕ → ℕ) (g : (i : ℕ) → (Fin (len i) → 𝓧) → ℝ), (∀ i, 1 ≤ len i) ∧
      (∀ i, Measurable (g i)) ∧ (∀ i, ∃ C, ∀ x, |g i x| ≤ C) ∧
      (∀ i, IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) (sampleNull S₁ (len i))) ∧
      ∀ Q : Measure 𝓧, IsProbabilityMeasure Q → Q ≪ ρ → ∀ t : ℝ, (t : EReal) < bipolarRate Q S₁ →
        ∃ i, t * len i < ∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q) := by
  choose u hu hdense using fun p : ℕ × ℕ ↦ exists_seq_boundedLogEVarSet hS₁ ρ (p.1 + 1) p.2
  let e : ℕ ≃ (ℕ × ℕ) × ℕ := (Denumerable.eqv _).symm
  refine ⟨fun i ↦ (e i).1.1 + 1, fun i ↦ u (e i).1 (e i).2, fun i ↦ Nat.le_add_left 1 _,
    fun i ↦ (hu _ _).1, fun i ↦ ⟨_, (hu _ _).2.1⟩,
    fun i ↦ ⟨ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hu _ _).1),
      forall_mem_sampleNull.2 (hu _ _).2.2⟩, fun Q hQ hQρ t ht ↦ ?_⟩
  obtain ⟨m, E, hE, hEt⟩ := exists_isEVar_lt_eintegral_of_lt_bipolarRate ht
  obtain ⟨N, f, hf, hft⟩ := exists_mem_boundedLogEVarSet_lt_integral Q hS₁ hE hEt
  obtain ⟨j, hj⟩ := hdense (m, N) Q hQ hQρ f hf _ hft
  refine ⟨e.symm ((m, N), j), ?_⟩
  -- `e (e.symm ((m, N), j))` occurs both in the integrand and in the type `Fin (_ + 1) → 𝓧` of
  -- its argument, so rewriting it with `Equiv.apply_symm_apply` gives an ill-typed motive; we
  -- generalize it to a variable and substitute instead.
  beta_reduce
  generalize hp : e (e.symm ((m, N), j)) = p
  rw [Equiv.apply_symm_apply] at hp
  subst hp
  push_cast
  exact hj

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

/-- The mixture is at most the sum of all its terms. -/
private lemma blockMixture_le_tsum (n : ℕ) (ω : ℕ → 𝓧) :
    blockMixture len g n ω ≤ ∑' i, ∑' k, blockMixtureTerm len g i k ω :=
  tsum_le_tsum fun i ↦ tsum_le_tsum fun k ↦ by
    by_cases h : k * len i ≤ n
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact zero_le

/-- The terms of the mixture are measurable. -/
private lemma measurable_blockMixtureTerm (hg : ∀ i, Measurable (g i)) (i k : ℕ) :
    Measurable (blockMixtureTerm len g i k) :=
  measurable_const.mul (measurable_const.mul (measurable_seqBlockProd
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg i))) k))

/-- The mixture is measurable. -/
private lemma measurable_blockMixture (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    Measurable (blockMixture len g n) :=
  Measurable.tsum fun i ↦ Measurable.tsum fun k ↦
    Measurable.ite (MeasurableSet.const _) (measurable_blockMixtureTerm hg i k) measurable_const

/-- The mixture at time `n` is a function of the first `n` observations. -/
private lemma dependsOn_blockMixture (n : ℕ) : DependsOn (blockMixture len g n) (Set.Iio n) := by
  intro ω ω' h
  refine tsum_congr fun i ↦ tsum_congr fun k ↦ ?_
  by_cases hk : k * len i ≤ n
  · rw [ite_eq_left hk, ite_eq_left hk, blockMixtureTerm, blockMixtureTerm,
      dependsOn_seqBlockProd _ k fun j hj ↦ h j (lt_of_lt_of_le hj hk)]
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- The sum of all the terms of the mixture is an e-variable for the i.i.d. null: a countable
mixture, over the family and over the numbers of blocks, of products over blocks. -/
private lemma isEVar_tsum_blockMixtureTerm
    (hg : ∀ i, IsEVar (fun x ↦ ENNReal.ofReal (Real.exp (g i x))) (sampleNull S₁ (len i))) :
    IsEVar (fun ω ↦ ∑' i, ∑' k, blockMixtureTerm len g i k ω) (iidNull S₁) := by
  have h := isEVar_tsum_mul (w := fun i ↦ (2⁻¹ : ℝ≥0∞) ^ (i + 1))
    (fun i ↦ isEVar_tsum_mul (fun k ↦ isEVar_seqBlockProd (hg i) k)
      tsum_ofReal_coverWeight_succ_le_one)
    ENNReal.tsum_geometric_two_add_one.le
  simpa only [blockMixtureTerm, ENNReal.tsum_mul_left] using h

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
  have hbound : ∀ n, ENNReal.ofReal (Real.exp (r n)) ≤ blockMixture len g n ω := by
    intro n
    have hw := coverWeight_pos (Nat.succ_pos (n / len i))
    have hterm : ENNReal.ofReal (Real.exp (r n)) = blockMixtureTerm len g i (n / len i) ω := by
      simp only [r, blockMixtureTerm, seqBlockProd_ofReal_exp]
      rw [Real.exp_add, Real.exp_log (mul_pos (by positivity) hw), mul_comm,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow, mul_assoc]
    rw [hterm]
    calc blockMixtureTerm len g i (n / len i) ω
    _ = if n / len i * len i ≤ n then blockMixtureTerm len g i (n / len i) ω else 0 :=
      (ite_eq_left (Nat.div_mul_le_self n (len i))).symm
    _ ≤ ∑' k, if k * len i ≤ n then blockMixtureTerm len g i k ω else 0 :=
      le_tsum (fun k ↦ if k * len i ≤ n then blockMixtureTerm len g i k ω else 0) (n / len i)
    _ ≤ blockMixture len g n ω :=
      le_tsum (fun i ↦ ∑' k, if k * len i ≤ n then blockMixtureTerm len g i k ω else 0) i
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

/-! ### The universal e-process -/

/-- **One e-process at the bipolar rate for every dominated alternative.** For a countably
generated space, a null `S₁` of probability measures and an s-finite measure `ρ`, there is one
e-process `E` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT` of
the observations, nondecreasing in time, such that for every `Q₁ ≪ ρ`, almost surely under the
i.i.d. law of `Q₁`, `(1/n) log (E n)` tends to the bipolar rate `bipolarRate Q₁ S₁`; at time `n`,
`E n` is a function of the first `n` observations. If `Q₁` is not a probability measure, its
i.i.d. law is `0` and the convergence holds trivially. This is the theorem of [EVR26, Note 13]. -/
theorem exists_isEProcess_ae_tendsto_log_div_bipolarRate [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ E : ℕ → (ℕ → 𝓧) → ℝ≥0∞,
      IsEProcess E (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁) ∧ Monotone E ∧
      ∀ Q₁ : Measure 𝓧, Q₁ ≪ ρ → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
        Tendsto (fun n : ℕ ↦ ENNReal.log (E n ω) / (n : EReal)) atTop
          (𝓝 (bipolarRate Q₁ S₁)) := by
  obtain ⟨len, g, hlen, hgm, hgb, hge, hrate⟩ := exists_rateFamily hS₁ ρ
  -- the sum of all the terms is an e-variable, and bounds the mixture at every time
  have hT := isEVar_tsum_blockMixtureTerm hge
  have hE : IsEProcess (blockMixture len g) (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧))
      (iidNull S₁) := by
    refine IsEProcess.of_lintegral_le_one (fun n ↦ Filtration.measurable_piLT_of_dependsOn
      (measurable_blockMixture hgm n) (dependsOn_blockMixture n)) ?_
    rintro τ - _ - _ hμ
    exact (lintegral_mono fun ω ↦ blockMixture_le_tsum _ ω).trans (hT.lintegral_le_one hμ)
  refine ⟨blockMixture len g, hE, monotone_blockMixture, fun Q₁ hQ₁ρ ↦ ?_⟩
  by_cases hQ₁ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0)
      hQ₁]
  -- the lower bound, from each member of the family
  have hlow : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ i,
      (((∫ x, g i x ∂Measure.pi (fun _ : Fin (len i) ↦ Q₁)) / len i : ℝ) : EReal) ≤
        liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop :=
    ae_all_iff.2 fun i ↦
      le_liminf_log_blockMixture Q₁ (hlen i) (hgm i) (hgb i).choose_spec
  -- the upper bound holds for every e-process
  filter_upwards [hE.ae_limsup_log_div_le_bipolarRate Q₁ hS₁, hlow] with ω hωup hωlow
  refine tendsto_of_le_liminf_of_limsup_le (EReal.ge_of_forall_gt_iff_ge.1 fun t ht ↦ ?_) hωup
  obtain ⟨i, hi⟩ := hrate Q₁ hQ₁ hQ₁ρ t ht
  have hL : (0 : ℝ) < len i := by exact_mod_cast hlen i
  refine le_trans ?_ (hωlow i)
  rw [EReal.coe_le_coe_iff, le_div_iff₀ hL]
  exact hi.le

end ProbabilityTheory
