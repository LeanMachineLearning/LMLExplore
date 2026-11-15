/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Probability.ProductMeasure
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.MeasureTheory.MeasurableSpace.CountablyGenerated
import LMLExplore.Probability.ProductMeasure
import LMLExplore.Probability.Process.Filtration
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.StrongLaw
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import Statlib.ForMathlib.Probability.Process.Filtration
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.Process.PathLaw.Shift

/-!
# One e-process at the bipolar rate for every dominated alternative

Let `S₁` be a set of probability measures on a countably generated measurable space `𝓧` (the
null), and `ρ` an s-finite measure on `𝓧`. The observations are the coordinates of `ℕ → 𝓧`, with
the i.i.d. laws `Measure.infinitePi fun _ ↦ P` and the filtration `Filtration.piLE` of the
observations. There is a single e-process `E` for the i.i.d. null, nondecreasing in time, such
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
* **Products over blocks.** For such a `g` on blocks of `m` observations, the product of
  `exp g` over the first `k` consecutive blocks has expectation at most `1` under the null, as
  the blocks are independent, and its logarithm divided by `k` tends to `∫ g ∂Q₁ ^ m` almost
  surely, by the strong law of large numbers.
* **The mixture.** The e-process at time `n` is the sum, over the members `g i` of the family
  and the numbers `k` of blocks of `g i` that fit in the first `n` observations, of these
  products, with weights `2⁻¹ ^ (i + 1) / ((k + 1) (k + 2))`. Each term is held from the time its
  blocks are observed on, which makes the process nondecreasing, and the sum of all the terms has
  expectation at most `1` under the null, so the value at every stopping time is an e-variable.
  The weight of the number of blocks costs `o(n)` in the logarithm, which gives the lower bound
  on the growth; the upper bound is
  `ProbabilityTheory.ae_limsup_log_div_le_bipolarRate_of_dependsOn`.

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
open TauCeti.Probability (shift shift_iterate_apply shift_iterate_eq_reindex
  measurable_shift_iterate)
open scoped ENNReal Topology

/-! ### The truncated logarithm, and monotone convergence for truncations -/

namespace ENNReal

/-- The logarithm truncated above at `c`, as a real number. -/
private noncomputable def truncLog (c : ℝ) (x : ℝ≥0∞) : ℝ := (min (ENNReal.log x) c).toReal

/-- The truncated logarithm is measurable. -/
private lemma measurable_truncLog (c : ℝ) : Measurable (truncLog c) :=
  measurable_ereal_toReal.comp (ENNReal.measurable_log.min measurable_const)

/-- The truncated logarithm of a positive finite number. -/
private lemma truncLog_of_ne {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) (htop : x ≠ ∞) :
    truncLog c x = min (Real.log x.toReal) c := by
  rw [truncLog, ENNReal.log_pos_real h0 htop, ← EReal.coe_strictMono.monotone.map_min,
    EReal.toReal_coe]

/-- The truncated logarithm of `∞` is the truncation level. -/
private lemma truncLog_top (c : ℝ) : truncLog c ∞ = c := by simp [truncLog]

/-- The truncated logarithm is at most the truncation level. -/
private lemma truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) : truncLog c x ≤ c := by
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
  · rw [truncLog_of_ne h0 htop]
    exact min_le_right _ _

/-- The truncated logarithm of `x ≥ δ` is at least `log δ`, if `log δ ≤ c`. -/
private lemma log_le_truncLog {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x)
    (hc : Real.log δ ≤ c) : Real.log δ ≤ truncLog c x := by
  have h0 : x ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) hx).ne'
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
    exact hc
  · rw [truncLog_of_ne h0 htop]
    exact le_min (Real.log_le_log hδ ((ENNReal.ofReal_le_iff_le_toReal htop).1 hx)) hc

/-- The exponential of the truncated logarithm of `x` is at most `x`. -/
private lemma ofReal_exp_truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) :
    ENNReal.ofReal (Real.exp (truncLog c x)) ≤ x := by
  by_cases htop : x = ∞
  · rw [htop]
    exact le_top
  · rw [truncLog_of_ne h0 htop]
    calc ENNReal.ofReal (Real.exp (min (Real.log x.toReal) c))
    _ ≤ ENNReal.ofReal (Real.exp (Real.log x.toReal)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _))
    _ = x := by
      rw [Real.exp_log (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop]

/-- Mixing with a constant: `min (log x) c ≤ truncLog c ((1 - ε) x + ε) - log (1 - ε)`. -/
private lemma min_log_le_truncLog_sub {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (x : ℝ≥0∞) :
    min (ENNReal.log x) c ≤
      ((truncLog c (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε) - Real.log (1 - ε) : ℝ) :
        EReal) := by
  have hlog : Real.log (1 - ε) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  by_cases h0 : x = 0
  · simp [h0]
  by_cases htop : x = ∞
  · have : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε = ∞ := by
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne', top_add]
    rw [this, truncLog_top]
    exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.2 (by linarith))
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε0).ne'
  have hV0 : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ 0 := by simp [hε']
  have hVtop : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop, ENNReal.ofReal_ne_top⟩
  have hVreal : (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε).toReal =
      (1 - ε) * x.toReal + ε := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε0.le]
  rw [truncLog_of_ne hV0 hVtop, hVreal, ENNReal.log_pos_real h0 htop,
    ← EReal.coe_strictMono.monotone.map_min, EReal.coe_le_coe_iff]
  have hx : 0 < x.toReal := ENNReal.toReal_pos h0 htop
  have hL : Real.log (1 - ε) + Real.log x.toReal ≤ Real.log ((1 - ε) * x.toReal + ε) := by
    rw [← Real.log_mul (by linarith) hx.ne']
    exact Real.log_le_log (_root_.mul_pos (by linarith) hx) (by linarith)
  rw [← min_sub_sub_right]
  exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))

end ENNReal

namespace MeasureTheory

/-- **Monotone convergence for truncations.** If the extended integrals of the truncations
`min f k`, `k ∈ ℕ`, are at most `D`, so is the extended integral of `f`. -/
private theorem eintegral_le_of_forall_min_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → EReal} (hf : Measurable f) {D : EReal}
    (h : ∀ k : ℕ, ∫ᵉ x, min (f x) k ∂μ ≤ D) : ∫ᵉ x, f x ∂μ ≤ D := by
  have hmono : Monotone EReal.toENNReal := fun _ _ h ↦ EReal.toENNReal_le_toENNReal h
  have hpos (k : ℕ) (x : Ω) : (min (f x) k).toENNReal = min (f x).toENNReal k := by
    rw [hmono.map_min, show ((k : EReal)) = ((k : ℝ≥0∞) : EReal) by simp, EReal.toENNReal_coe]
  have hneg (k : ℕ) (x : Ω) : (-min (f x) k).toENNReal = (-f x).toENNReal := by
    by_cases hk : f x ≤ k
    · rw [min_eq_left hk]
    · rw [not_le] at hk
      have hk0 : (0 : EReal) ≤ k := by exact_mod_cast Nat.zero_le k
      rw [min_eq_right hk.le, EReal.toENNReal_of_nonpos (by simp),
        EReal.toENNReal_of_nonpos (by simpa using hk0.trans hk.le)]
  have h' (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, (-f x).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤ D := by
    have := h k
    simp only [eintegral, hpos, hneg] at this
    exact this
  have hm (k : ℕ) : Measurable fun x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    (measurable_ereal_toENNReal.comp hf).min measurable_const
  have hmono' : Monotone fun (k : ℕ) x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    fun k k' hkk' x ↦ min_le_min_left _ (by exact_mod_cast hkk')
  have hsup : ∫⁻ x, (f x).toENNReal ∂μ = ⨆ k : ℕ, ∫⁻ x, min (f x).toENNReal k ∂μ := by
    rw [← lintegral_iSup hm hmono']
    refine lintegral_congr fun x ↦ le_antisymm ?_ (iSup_le fun k ↦ min_le_left _ _)
    by_cases hx : (f x).toENNReal = ∞
    · simp [hx, ENNReal.iSup_natCast]
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le k (min_eq_left hk.le).ge
  rw [eintegral, hsup]
  set b := ∫⁻ x, (-f x).toENNReal ∂μ
  by_cases hb : b = ∞
  · rw [hb, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hb' : (b : EReal) ≠ ⊤ := by simpa using hb
  have hb'' : (b : EReal) ≠ ⊥ := by simp
  rw [EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')]
  have hk (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) ≤ D + b :=
    (EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')).1 (h' k)
  have hD : 0 ≤ D + b := (EReal.coe_ennreal_nonneg _).trans (hk 0)
  rw [← EReal.coe_toENNReal hD] at hk ⊢
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2
    (iSup_le fun k ↦ EReal.coe_ennreal_le_coe_ennreal_iff.1 (hk k))

/-! ### Observations and shifts -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

open ProbabilityTheory in
/-- Under an i.i.d. law, the first `t` terms are independent of the terms after them. -/
private lemma indepFun_initSeg_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    IndepFun (initSeg t) ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).indepFun_set (Set.Iio t) (Set.Ici t)
    (Set.disjoint_left.2 fun i (hi : i < t) (hi' : t ≤ i) ↦ (not_lt.2 hi') hi)
    (fun i ↦ measurable_pi_apply i)
  rw [shift_iterate_eq_reindex, initSeg_def]
  exact h.comp (φ := fun (y : Set.Iio t → 𝓧) (i : Fin t) ↦ y ⟨i, i.2⟩)
    (ψ := fun (y : Set.Ici t → 𝓧) (i : ℕ) ↦ y ⟨i + t, Nat.le_add_left t i⟩)
    (by fun_prop) (by fun_prop)

end MeasureTheory

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

/-- **Truncation.** If an `m`-sample e-variable has expected logarithm larger than `c` under
`Q ^ m`, so has the truncated logarithm of its mixture with a constant, which is bounded. -/
private lemma exists_mem_boundedLogEVarSet_lt_integral (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {m : ℕ}
    {E : (Fin m → 𝓧) → ℝ≥0∞} (hE : IsEVar E ((fun P ↦ Measure.pi fun _ : Fin m ↦ P) '' S₁))
    {c : ℝ} (hc : (c : EReal) < ∫ᵉ x, ENNReal.log (E x) ∂Measure.pi (fun _ : Fin m ↦ Q)) :
    ∃ N : ℕ, ∃ f ∈ boundedLogEVarSet S₁ m N, c < ∫ x, f x ∂Measure.pi (fun _ : Fin m ↦ Q) := by
  obtain ⟨c', hcc', hc'⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  rw [EReal.coe_lt_coe_iff] at hcc'
  set η := c' - c with hη
  have hη0 : 0 < η := by linarith
  set ε := 1 - Real.exp (-(η / 2)) with hε
  have hε0 : 0 < ε := by
    have : Real.exp (-(η / 2)) < 1 := by
      simpa using Real.exp_lt_exp.2 (show -(η / 2) < 0 by linarith)
    linarith
  have hε1 : ε < 1 := by
    have := Real.exp_pos (-(η / 2))
    linarith
  have hlogε : Real.log (1 - ε) = -(η / 2) := by rw [hε, sub_sub_cancel, Real.log_exp]
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
  · have := hS₁ P hP
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂Measure.pi (fun _ : Fin m ↦ P)
    _ ≤ ∫⁻ x, F x ∂Measure.pi (fun _ : Fin m ↦ P) :=
      lintegral_mono fun x ↦ ENNReal.ofReal_exp_truncLog_le (hF0 x)
    _ = ENNReal.ofReal (1 - ε) * ∫⁻ x, E x ∂Measure.pi (fun _ : Fin m ↦ P) +
        ENNReal.ofReal ε := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hE.measurable,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 - ε) * 1 + ENNReal.ofReal ε := by
      gcongr
      simpa using hE.lintegral_le_measure_univ _ ⟨P, hP, rfl⟩
    _ = 1 := by rw [mul_one, ← ENNReal.ofReal_add (by linarith) hε0.le]; simp
  · have hle : ∫ᵉ x, min (ENNReal.log (E x)) k ∂μ ≤
        ((∫ x, f x ∂μ - Real.log (1 - ε) : ℝ) : EReal) := by
      calc ∫ᵉ x, min (ENNReal.log (E x)) k ∂μ
      _ ≤ ∫ᵉ x, ((f x - Real.log (1 - ε) : ℝ) : EReal) ∂μ := eintegral_mono fun x ↦ by
        have := ENNReal.min_log_le_truncLog_sub hε0 hε1 (k : ℝ) (E x)
        rwa [EReal.coe_natCast] at this
      _ = ((∫ x, (f x - Real.log (1 - ε)) ∂μ : ℝ) : EReal) :=
        eintegral_eq_integral (hint.sub (integrable_const _))
      _ = ((∫ x, f x ∂μ - Real.log (1 - ε) : ℝ) : EReal) := by
        rw [integral_sub hint (integrable_const _), integral_const]
        simp
    have h := hk.trans_le hle
    rw [EReal.coe_lt_coe_iff, hlogε] at h
    linarith

/-- An exponent below the bipolar rate is beaten by the expected logarithm of an e-variable of
some number of observations. -/
private lemma exists_isEVar_lt_eintegral_of_lt_bipolarRate {Q : Measure 𝓧} {t : ℝ}
    (ht : (t : EReal) < bipolarRate Q S₁) :
    ∃ m : ℕ, ∃ E : (Fin (m + 1) → 𝓧) → ℝ≥0∞,
      IsEVar E ((fun P ↦ Measure.pi fun _ : Fin (m + 1) ↦ P) '' S₁) ∧
      ((t * (m + 1) : ℝ) : EReal) <
        ∫ᵉ x, ENNReal.log (E x) ∂Measure.pi (fun _ : Fin (m + 1) ↦ Q) := by
  rw [bipolarRate_def] at ht
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 ht
  have hm0 : (0 : EReal) < ((m + 1 : ℕ) : EReal) := by exact_mod_cast Nat.succ_pos m
  rw [EReal.lt_div_iff hm0 (EReal.natCast_ne_top _)] at hm
  simp only [maxLogGrowth_def, maxUtility] at hm
  obtain ⟨E, hE⟩ := lt_iSup_iff.1 hm
  obtain ⟨hEv, hE'⟩ := lt_iSup_iff.1 hE
  refine ⟨m, E, hEv, ?_⟩
  have h1 : ((t * (m + 1) : ℝ) : EReal) = (t : EReal) * ((m + 1 : ℕ) : EReal) := by
    rw [EReal.coe_mul]
    norm_cast
  rw [h1]
  exact hE'

/-- **A countable family that determines the bipolar rate.** On a countably generated space, for
an s-finite `ρ`, there are bounded functions `g i` of the first `len i` observations, with
`∫ exp (g i) ≤ 1` under the i.i.d. law of every member of the null, such that every exponent
`t` below the bipolar rate of a probability measure `Q ≪ ρ` is beaten by some
`∫ g i ∂Q^∞ / len i`. -/
private lemma exists_rateFamily [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ (len : ℕ → ℕ) (g : ℕ → (ℕ → 𝓧) → ℝ), (∀ i, 1 ≤ len i) ∧ (∀ i, Measurable (g i)) ∧
      (∀ i, DependsOn (g i) (Set.Iio (len i))) ∧ (∀ i, ∃ C, ∀ ω, |g i ω| ≤ C) ∧
      (∀ i, ∀ P ∈ S₁, ∫⁻ ω, ENNReal.ofReal (Real.exp (g i ω))
        ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1) ∧
      ∀ Q : Measure 𝓧, IsProbabilityMeasure Q → Q ≪ ρ → ∀ t : ℝ, (t : EReal) < bipolarRate Q S₁ →
        ∃ i, t * len i < ∫ ω, g i ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q) := by
  choose u hu hdense using fun p : ℕ × ℕ ↦ exists_seq_boundedLogEVarSet hS₁ ρ (p.1 + 1) p.2
  let e : ℕ ≃ (ℕ × ℕ) × ℕ := (Denumerable.eqv _).symm
  refine ⟨fun i ↦ (e i).1.1 + 1, fun i ω ↦ u (e i).1 (e i).2 (initSeg _ ω),
    fun i ↦ Nat.le_add_left 1 _, fun i ↦ (hu _ _).1.comp (measurable_initSeg _),
    fun i ↦ dependsOn_comp_initSeg _, fun i ↦ ⟨_, fun ω ↦ (hu _ _).2.1 _⟩, fun i P hP ↦ ?_,
    fun Q hQ hQρ t ht ↦ ?_⟩
  · have := hS₁ P hP
    have hm : Measurable fun x ↦ ENNReal.ofReal (Real.exp (u (e i).1 (e i).2 x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hu _ _).1)
    rw [(measurePreserving_initSeg P _).lintegral_comp hm]
    exact (hu _ _).2.2 P hP
  · obtain ⟨m, E, hE, hEt⟩ := exists_isEVar_lt_eintegral_of_lt_bipolarRate ht
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
    rw [← integral_map (measurable_initSeg _).aemeasurable (hu _ _).1.aestronglyMeasurable,
      (measurePreserving_initSeg Q _).map_eq]
    push_cast
    exact hj

/-! ### Sums of a function over consecutive blocks -/

/-- The sum of `g` over the first `k` consecutive blocks of `L` observations: block `l` is the
sequence shifted by `L * l`. -/
private noncomputable def blockSum (L : ℕ) (g : (ℕ → 𝓧) → ℝ) (k : ℕ) (ω : ℕ → 𝓧) : ℝ :=
  ∑ l ∈ Finset.range k, g ((shift 𝓧)^[L * l] ω)

/-- The sum over no block is `0`. -/
private lemma blockSum_zero (L : ℕ) (g : (ℕ → 𝓧) → ℝ) (ω : ℕ → 𝓧) : blockSum L g 0 ω = 0 := by
  simp [blockSum]

/-- The sum over `k + 1` blocks is the value on the first block plus the sum over the next `k`
blocks. -/
private lemma blockSum_succ (L : ℕ) (g : (ℕ → 𝓧) → ℝ) (k : ℕ) (ω : ℕ → 𝓧) :
    blockSum L g (k + 1) ω = g ω + blockSum L g k ((shift 𝓧)^[L] ω) := by
  simp only [blockSum]
  rw [Finset.sum_range_succ', add_comm, Nat.mul_zero, Function.iterate_zero_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Function.iterate_add_apply, Nat.mul_succ]

/-- The block sums of a measurable function are measurable. -/
private lemma measurable_blockSum {g : (ℕ → 𝓧) → ℝ} (hg : Measurable g) (L k : ℕ) :
    Measurable (blockSum L g k) :=
  Finset.measurable_sum _ fun _ _ ↦ hg.comp (measurable_shift_iterate _)

/-- A function of the first `L` observations, played on the sequence shifted by `a`, is a
function of the first `a + L` observations. -/
private lemma dependsOn_comp_shift_iterate {β : Type*} {L : ℕ} {g : (ℕ → 𝓧) → β}
    (hg : DependsOn g (Set.Iio L)) (a : ℕ) :
    DependsOn (g ∘ (shift 𝓧)^[a]) (Set.Iio (a + L)) := by
  intro ω ω' h
  refine hg fun i hi ↦ ?_
  simp only [shift_iterate_apply]
  exact h _ (by simp only [Set.mem_Iio] at hi ⊢; omega)

/-- The sums of a function of the first `L` observations over `k` blocks of `L` observations are
functions of the first `L * k` observations. -/
private lemma dependsOn_blockSum {L : ℕ} {g : (ℕ → 𝓧) → ℝ} (hg : DependsOn g (Set.Iio L))
    (k : ℕ) : DependsOn (blockSum L g k) (Set.Iio (L * k)) := by
  intro ω ω' h
  refine Finset.sum_congr rfl fun l hl ↦ dependsOn_comp_shift_iterate hg (L * l) fun i hi ↦
    h i (Set.mem_Iio.2 (lt_of_lt_of_le (Set.mem_Iio.1 hi) ?_))
  rw [← Nat.mul_succ]
  exact Nat.mul_le_mul_left _ (Finset.mem_range.1 hl)

/-- If `exp g` has expectation at most `1` under the i.i.d. law of `P`, so has the exponential of
its block sums, as the blocks are independent. -/
private lemma lintegral_exp_blockSum_le_one (P : Measure 𝓧) [IsProbabilityMeasure P] {L : ℕ}
    {g : (ℕ → 𝓧) → ℝ} (hg : Measurable g) (hgL : DependsOn g (Set.Iio L))
    (hP : ∫⁻ ω, ENNReal.ofReal (Real.exp (g ω)) ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (blockSum L g k ω))
      ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  induction k with
  | zero => simp [blockSum_zero]
  | succ k ih =>
    have hexp : ∀ ω, ENNReal.ofReal (Real.exp (blockSum L g (k + 1) ω)) =
        ENNReal.ofReal (Real.exp (g ω)) *
          ENNReal.ofReal (Real.exp (blockSum L g k ((shift 𝓧)^[L] ω))) := fun ω ↦ by
      rw [blockSum_succ, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp_rw [hexp]
    rw [lintegral_mul_comp_shift_iterate P (f := fun ω ↦ ENNReal.ofReal (Real.exp (g ω)))
      (g := fun ω ↦ ENNReal.ofReal (Real.exp (blockSum L g k ω)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg))
      (fun ω ω' h ↦ by simp only [hgL h])
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_blockSum hg L k)))]
    calc _ ≤ (1 : ℝ≥0∞) * 1 := mul_le_mul' hP ih
    _ = 1 := one_mul 1

/-- **The strong law of large numbers along blocks.** For a bounded measurable function `g` of the
first `L` observations, `blockSum L g k / k` tends to `∫ g` almost surely under an i.i.d. law. -/
private lemma ae_tendsto_blockSum (Q : Measure 𝓧) [IsProbabilityMeasure Q] {L : ℕ}
    {g : (ℕ → 𝓧) → ℝ} (hg : Measurable g) (hgL : DependsOn g (Set.Iio L)) {C : ℝ}
    (hgC : ∀ ω, |g ω| ≤ C) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹ * blockSum L g k ω)
      atTop (𝓝 (∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q))) := by
  have := nonempty_of_isProbabilityMeasure Q
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q)
  set X : ℕ → (ℕ → 𝓧) → ℝ := fun l ω ↦ g ((shift 𝓧)^[L * l] ω)
  have hX0 : X 0 = g := by
    funext ω
    simp [X]
  have hint : Integrable (X 0) μ := by
    rw [hX0]
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hgC ω)
  -- an earlier block is a function of the observations before a later one
  have hlt : ∀ a b, a < b → IndepFun (X a) (X b) μ := by
    intro a b hab
    have hXa : DependsOn (X a) (Set.Iio (L * b)) := by
      refine (dependsOn_comp_shift_iterate hgL (L * a)).mono (Set.Iio_subset_Iio ?_)
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hab
    obtain ⟨φ, hφ, hφeq⟩ := exists_measurable_eq_comp_initSeg
      (hg.comp (measurable_shift_iterate (L * a))) hXa
    have ha : X a = φ ∘ initSeg (L * b) := hφeq
    have hb : X b = g ∘ (shift 𝓧)^[L * b] := rfl
    rw [ha, hb]
    exact (indepFun_initSeg_shift_iterate Q (L * b)).comp hφ hg
  have hindep : Pairwise fun a b ↦ IndepFun (X a) (X b) μ := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact hlt a b h
    · exact (hlt b a h).symm
  have hident : ∀ l, IdentDistrib (X l) (X 0) μ μ := by
    intro l
    have hsh : IdentDistrib ((shift 𝓧)^[L * l]) ((shift 𝓧)^[L * 0]) μ μ :=
      ⟨(measurable_shift_iterate _).aemeasurable, (measurable_shift_iterate _).aemeasurable, by
        rw [(measurePreserving_shift_iterate Q _).map_eq,
          (measurePreserving_shift_iterate Q _).map_eq]⟩
    exact hsh.comp hg
  filter_upwards [strong_law_ae X hint hindep hident] with ω hω
  rw [hX0] at hω
  simp only [smul_eq_mul] at hω
  exact hω

/-! ### The weights of the numbers of blocks

The weight of `k` blocks in the mixture is `coverWeight (k + 1) = 1 / ((k + 1) (k + 2))`, the
weight of the covering mixture of `AlmostSure.lean`. -/

/-- The weights of the numbers of blocks are positive. -/
private lemma coverWeight_succ_pos (k : ℕ) : 0 < coverWeight (k + 1) := by
  rw [coverWeight_def]
  positivity

/-- The weights of all the numbers of blocks add up to at most `1`. -/
private lemma tsum_ofReal_coverWeight_succ_le_one :
    ∑' k : ℕ, ENNReal.ofReal (coverWeight (k + 1)) ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ (coverWeight_succ_pos k).le]
  exact ENNReal.ofReal_le_one.2 (sum_coverWeight_le_one n)

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
  · refine div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (coverWeight_succ_pos _).le ?_)
      (Nat.cast_nonneg n)
    rw [coverWeight_def]
    rw [div_le_one (by positivity)]
    push_cast
    nlinarith [(Nat.cast_nonneg (n / L) : (0 : ℝ) ≤ (n / L : ℕ))]

/-! ### The mixture over the family and the numbers of blocks -/

/-- The term of the mixture for the function `g i` on blocks of `len i` observations, played on
`k` blocks: the product of `exp (g i)` over the blocks, with weight
`2⁻¹ ^ (i + 1) * coverWeight (k + 1)`. -/
private noncomputable def blockMixtureTerm (len : ℕ → ℕ) (g : ℕ → (ℕ → 𝓧) → ℝ) (i k : ℕ)
    (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  2⁻¹ ^ (i + 1) * ENNReal.ofReal (coverWeight (k + 1)) *
    ENNReal.ofReal (Real.exp (blockSum (len i) (g i) k ω))

/-- **The mixture over the family and the numbers of blocks**: at time `n`, the sum of the terms
for all `(i, k)` with `len i * k ≤ n`, that is, whose blocks are among the first `n` observations.
Each term is held from the time its blocks are observed on, which makes the process
nondecreasing. -/
private noncomputable def blockMixture (len : ℕ → ℕ) (g : ℕ → (ℕ → 𝓧) → ℝ) (n : ℕ)
    (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑' i, ∑' k, if len i * k ≤ n then blockMixtureTerm len g i k ω else 0

variable {len : ℕ → ℕ} {g : ℕ → (ℕ → 𝓧) → ℝ}

/-- The mixture is nondecreasing in time. -/
private lemma monotone_blockMixture : Monotone (blockMixture len g) :=
  fun n n' hnn' ω ↦ tsum_le_tsum fun i ↦ tsum_le_tsum fun k ↦ by
    by_cases h : len i * k ≤ n
    · rw [ite_eq_left h, ite_eq_left (h.trans hnn')]
    · rw [ite_eq_right h]
      exact zero_le

/-- The mixture is at most the sum of all its terms. -/
private lemma blockMixture_le_tsum (n : ℕ) (ω : ℕ → 𝓧) :
    blockMixture len g n ω ≤ ∑' i, ∑' k, blockMixtureTerm len g i k ω :=
  tsum_le_tsum fun i ↦ tsum_le_tsum fun k ↦ by
    by_cases h : len i * k ≤ n
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact zero_le

/-- The terms of the mixture are measurable. -/
private lemma measurable_blockMixtureTerm (hg : ∀ i, Measurable (g i)) (i k : ℕ) :
    Measurable (blockMixtureTerm len g i k) :=
  measurable_const.mul
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_blockSum (hg i) _ k)))

/-- The mixture is measurable. -/
private lemma measurable_blockMixture (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    Measurable (blockMixture len g n) :=
  Measurable.tsum fun i ↦ Measurable.tsum fun k ↦
    Measurable.ite (MeasurableSet.const _) (measurable_blockMixtureTerm hg i k) measurable_const

/-- The mixture at time `n` is a function of the first `n` observations. -/
private lemma dependsOn_blockMixture (hgd : ∀ i, DependsOn (g i) (Set.Iio (len i))) (n : ℕ) :
    DependsOn (blockMixture len g n) (Set.Iio n) := by
  intro ω ω' h
  refine tsum_congr fun i ↦ tsum_congr fun k ↦ ?_
  by_cases hk : len i * k ≤ n
  · rw [ite_eq_left hk, ite_eq_left hk, blockMixtureTerm, blockMixtureTerm,
      dependsOn_blockSum (hgd i) k fun j hj ↦ h j (lt_of_lt_of_le hj hk)]
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- Under the i.i.d. law of a member of the null, the sum of all the terms of the mixture has
expectation at most `1`. -/
private lemma lintegral_tsum_blockMixtureTerm_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hg : ∀ i, Measurable (g i)) (hgd : ∀ i, DependsOn (g i) (Set.Iio (len i)))
    (hP : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (g i ω)) ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1) :
    ∫⁻ ω, ∑' i, ∑' k, blockMixtureTerm len g i k ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  calc ∫⁻ ω, ∑' i, ∑' k, blockMixtureTerm len g i k ω ∂μ
  _ = ∑' i, ∑' k, ∫⁻ ω, blockMixtureTerm len g i k ω ∂μ := by
    rw [lintegral_tsum fun i ↦
      (Measurable.tsum fun k ↦ measurable_blockMixtureTerm hg i k).aemeasurable]
    exact tsum_congr fun i ↦
      lintegral_tsum fun k ↦ (measurable_blockMixtureTerm hg i k).aemeasurable
  _ = ∑' i, ∑' k, 2⁻¹ ^ (i + 1) * ENNReal.ofReal (coverWeight (k + 1)) *
      ∫⁻ ω, ENNReal.ofReal (Real.exp (blockSum (len i) (g i) k ω)) ∂μ := by
    refine tsum_congr fun i ↦ tsum_congr fun k ↦ ?_
    exact lintegral_const_mul _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_blockSum (hg i) _ k)))
  _ ≤ ∑' i, ∑' k, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * ENNReal.ofReal (coverWeight (k + 1)) :=
    tsum_le_tsum fun i ↦ tsum_le_tsum fun k ↦
      mul_le_of_le_one_right' (lintegral_exp_blockSum_le_one P (hg i) (hgd i) (hP i) k)
  _ = ∑' i, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * ∑' k : ℕ, ENNReal.ofReal (coverWeight (k + 1)) := by
    simp_rw [ENNReal.tsum_mul_left]
  _ ≤ ∑' i, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * 1 :=
    tsum_le_tsum fun i ↦ by gcongr; exact tsum_ofReal_coverWeight_succ_le_one
  _ = 1 := by
    simp_rw [mul_one, pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)

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
  rw [Real.log_mul hc.ne' (coverWeight_succ_pos _).ne']
  field_simp

/-- **Growth of the mixture.** Almost surely under the i.i.d. law of `Q`, the mixture grows at
least at the rate `∫ g i ∂Q^∞ / len i` of each member of the family. -/
private lemma le_liminf_log_blockMixture (Q : Measure 𝓧) [IsProbabilityMeasure Q] {i : ℕ}
    (hlen : 1 ≤ len i) (hg : Measurable (g i)) (hgd : DependsOn (g i) (Set.Iio (len i)))
    {C : ℝ} (hgC : ∀ ω, |g i ω| ≤ C) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      (((∫ ω, g i ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q)) / len i : ℝ) : EReal) ≤
        liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop := by
  filter_upwards [ae_tendsto_blockSum Q hg hgd hgC] with ω hω
  set L := len i with hL
  -- the logarithm of the term of `n / L` blocks of `g i`
  set r : ℕ → ℝ := fun n ↦
    blockSum L (g i) (n / L) ω + Real.log (2⁻¹ ^ (i + 1) * coverWeight (n / L + 1))
  have hbound : ∀ n, ENNReal.ofReal (Real.exp (r n)) ≤ blockMixture len g n ω := by
    intro n
    have hw := coverWeight_succ_pos (n / L)
    have hterm : ENNReal.ofReal (Real.exp (r n)) = blockMixtureTerm len g i (n / L) ω := by
      simp only [r, blockMixtureTerm]
      rw [Real.exp_add, Real.exp_log (mul_pos (by positivity) hw), mul_comm,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow, L]
    rw [hterm]
    calc blockMixtureTerm len g i (n / L) ω
    _ = if len i * (n / L) ≤ n then blockMixtureTerm len g i (n / L) ω else 0 :=
      (ite_eq_left (Nat.mul_div_le n L)).symm
    _ ≤ ∑' k, if len i * k ≤ n then blockMixtureTerm len g i k ω else 0 :=
      le_tsum (fun k ↦ if len i * k ≤ n then blockMixtureTerm len g i k ω else 0) (n / L)
    _ ≤ blockMixture len g n ω :=
      le_tsum (fun i ↦ ∑' k, if len i * k ≤ n then blockMixtureTerm len g i k ω else 0) i
  have hle : ∀ᶠ n : ℕ in atTop,
      ((r n / n : ℝ) : EReal) ≤ ENNReal.log (blockMixture len g n ω) / (n : EReal) := by
    refine Eventually.of_forall fun n ↦ ?_
    rw [EReal.coe_div, EReal.coe_natCast]
    refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast Nat.zero_le n) ?_
    calc (r n : EReal) = ENNReal.log (ENNReal.ofReal (Real.exp (r n))) := by
          rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    _ ≤ ENNReal.log (blockMixture len g n ω) := ENNReal.log_le_log (hbound n)
  -- `r n / n` tends to `∫ g i / L`, by the strong law along blocks
  have hlim := tendsto_add_log_coverWeight_div hlen (by positivity : (0 : ℝ) < 2⁻¹ ^ (i + 1)) hω
  calc (((∫ ω, g i ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q)) / L : ℝ) : EReal)
  _ = liminf (fun n : ℕ ↦ ((r n / n : ℝ) : EReal)) atTop :=
        ((continuous_coe_real_ereal.tendsto _).comp hlim).liminf_eq.symm
  _ ≤ liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop :=
    liminf_le_liminf hle

/-! ### The universal e-process -/

/-- **One e-process at the bipolar rate for every dominated alternative.** For a countably
generated space, a null `S₁` of probability measures and an s-finite measure `ρ`, there is one
e-process `E` for the i.i.d. laws of the members of `S₁`, in the filtration of the observations,
nondecreasing in time, such that for every `Q₁ ≪ ρ`, almost surely under the i.i.d. law of `Q₁`,
`(1/n) log (E n)` tends to the bipolar rate `bipolarRate Q₁ S₁`. If `Q₁` is not a probability
measure, its i.i.d. law is `0` and the convergence holds trivially. This is the theorem of
[EVR26, Note 13]. -/
theorem exists_isEProcess_ae_tendsto_log_div_bipolarRate [MeasurableSpace.CountablyGenerated 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ρ : Measure 𝓧) [SFinite ρ] :
    ∃ E : ℕ → (ℕ → 𝓧) → ℝ≥0∞,
      IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
        ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁) ∧ Monotone E ∧
      ∀ Q₁ : Measure 𝓧, Q₁ ≪ ρ → ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
        Tendsto (fun n : ℕ ↦ ENNReal.log (E n ω) / (n : EReal)) atTop
          (𝓝 (bipolarRate Q₁ S₁)) := by
  obtain ⟨len, g, hlen, hgm, hgd, hgb, hgnull, hrate⟩ := exists_rateFamily hS₁ ρ
  have hEm : ∀ n, Measurable (blockMixture len g n) := measurable_blockMixture hgm
  have hEd : ∀ n, DependsOn (blockMixture len g n) (Set.Iio n) := dependsOn_blockMixture hgd
  -- the sum of all the terms has expectation at most `1` under the null
  have hEnull : ∀ P ∈ S₁, ∀ τ : (ℕ → 𝓧) → ℕ,
      ∫⁻ ω, blockMixture len g (τ ω) ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
    intro P hP τ
    have := hS₁ P hP
    exact (lintegral_mono fun ω ↦ blockMixture_le_tsum _ ω).trans
      (lintegral_tsum_blockMixtureTerm_le_one P hgm hgd fun i ↦ hgnull i P hP)
  refine ⟨blockMixture len g, IsEProcess.of_lintegral_le_one ?_
    (fun n ↦ Filtration.measurable_piLE_of_dependsOn (hEm n)
      ((hEd n).mono (Set.Iio_subset_Iio n.le_succ))) ?_, monotone_blockMixture,
    fun Q₁ hQ₁ρ ↦ ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    infer_instance
  · rintro τ - _ ⟨P, hP, rfl⟩
    exact hEnull P hP τ
  by_cases hQ₁ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0)
      hQ₁]
  -- the lower bound, from each member of the family
  have hlow : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ i,
      (((∫ ω, g i ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) / len i : ℝ) : EReal) ≤
        liminf (fun n : ℕ ↦ ENNReal.log (blockMixture len g n ω) / (n : EReal)) atTop :=
    ae_all_iff.2 fun i ↦
      le_liminf_log_blockMixture Q₁ (hlen i) (hgm i) (hgd i) (hgb i).choose_spec
  -- the upper bound holds for every e-process
  filter_upwards [ae_limsup_log_div_le_bipolarRate_of_dependsOn Q₁ hS₁ hEm hEd
    (fun P hP n ↦ hEnull P hP fun _ ↦ n), hlow] with ω hωup hωlow
  refine tendsto_of_le_liminf_of_limsup_le (EReal.ge_of_forall_gt_iff_ge.1 fun t ht ↦ ?_) hωup
  obtain ⟨i, hi⟩ := hrate Q₁ hQ₁ hQ₁ρ t ht
  have hL : (0 : ℝ) < len i := by exact_mod_cast hlen i
  refine le_trans ?_ (hωlow i)
  rw [EReal.coe_le_coe_iff, le_div_iff₀ hL]
  exact hi.le

end ProbabilityTheory
