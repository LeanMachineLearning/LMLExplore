/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.TestSupermartingale.IID
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Probability.ProductMeasure
import LMLExplore.Probability.Process.Filtration
import LMLExplore.Probability.Process.HittingTime
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# Sequential tests whose expected number of observations attains the bipolar rate

Let `S₁` be a set of measures on `𝓧` (the null) and `Q₁` a measure on `𝓧` (the alternative). The
observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws `Measure.infinitePi fun _ ↦ P`
and the filtration `Filtration.piLE`, so that `τ + 1` observations have been made at a time `τ`. A
sequential test of level `α` is a stopping time `τ` with values in `WithTop ℕ` that is finite with
probability at most `α` under the i.i.d. law of every member of the null
(`ProbabilityTheory.IsLevelStoppingTime`, for the null of these i.i.d. laws).

Every such test makes at least `log (1/α) / d` observations in expectation under the i.i.d. law
of `Q₁`, where `d = bipolarRate Q₁ S₁` [EVR26, Note 01]. This file proves that the bound is
attained to first order as `α → 0` [EVR26, Note 01]: for every real `d' > 0` below `d` there are
sequential tests `τ α` of every level `α` with
`limsup_{α → 0} 𝔼[τ α + 1] / log (1/α) ≤ 1 / d'`. The bipolar rate may be infinite, and nothing
is assumed of `S₁` or `Q₁`.

The tests bet on successive blocks of `m` observations. Since `d' < d`, some `m`-sample
e-variable has an expected logarithm above `m d'` under `Q₁ ^ m`; mixed with a small constant and
with its logarithm truncated above, it gives a bet `exp v` on `m` observations whose expectation is
at most `1` under the `m`-fold products of the members of the null, with `v` bounded above and of
mean `a > m d'` under `Q₁ ^ m`. The test `τ α` stops as soon as the product of the bets over the
complete blocks reaches `α⁻¹`.

* **Level.** The blocks of an i.i.d. sequence are i.i.d., so the products of the bets over blocks
  form an e-process along the blocks, and Ville's inequality bounds the probability that they ever
  reach `α⁻¹` by `α` (`ProbabilityTheory.measure_exists_le_seqBlockProd_le`).
* **Expected number of observations.** The test stops at the latest at the end of the block where
  the sum of the values of `v` on the blocks first reaches `log (1/α)`. By Wald's argument for
  increments bounded above by `C`, the expected number of these blocks is at most
  `(log (1/α) + C) / a` (`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`), so that
  `𝔼[τ α + 1] / log (1/α) ≤ (m / a) (1 + C / log (1/α))`, which tends to `m / a < 1 / d'`.

## Main statements

* `ProbabilityTheory.exists_isLevelStoppingTime_limsup_lintegral_div_log_le`: for every real
  `0 < d' < bipolarRate Q₁ S₁`, sequential tests `τ α` of every level `α` with
  `limsup_{α → 0} 𝔼[τ α + 1] / log (1/α) ≤ 1 / d'`.

## Implementation notes

The monotone convergence of the extended integrals of the truncations `min f k` is
`MeasureTheory.eintegral_le_of_forall_min_le`. The statements and proofs are adapted
from `EValuesResearch/Results/Numeraire.lean` and `EValuesResearch/Results/NumeraireAux.lean`
(commit `dd4072f`) in the paper project `RemyDegenne/evalues_research`, which formalize
[EVR26, Note 01], rewritten on the API of LMLExplore: the tests are Mathlib's hitting times
`hittingAfter`, their level is Ville's inequality for e-processes, and the bound on their expected
number of observations is Wald's.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### A bounded bet on a block of observations -/

/-- **A bounded bet with a large expected logarithm.** For a real `L` below the bipolar rate there
are a block length `m ≠ 0` and a measurable `v` on `m` observations, bounded above, such that the
bet `exp v` has expectation at most `1` under the `m`-fold product of every member of the null
that is a probability measure, and `v` has expectation above `m L` under `Q₁ ^ m`. The bet is an
`m`-sample e-variable of expected logarithm above `m L`, mixed with a small constant, with its
logarithm truncated above. -/
private lemma exists_bounded_bet (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁] {L : ℝ}
    (hL : (L : EReal) < bipolarRate Q₁ S₁) :
    ∃ m ≠ 0, ∃ v : (Fin m → 𝓧) → ℝ, Measurable v ∧ (∃ C, ∀ x, v x ≤ C) ∧
      (∀ P ∈ S₁, IsProbabilityMeasure P →
        ∫⁻ x, ENNReal.ofReal (Real.exp (v x)) ∂Measure.pi (fun _ : Fin m ↦ P) ≤ 1) ∧
      m * L < ∫ x, v x ∂Measure.pi fun _ : Fin m ↦ Q₁ := by
  rw [bipolarRate_def] at hL
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hL
  set m := k + 1
  refine ⟨m, k.succ_ne_zero, ?_⟩
  set μQ := Measure.pi fun _ : Fin m ↦ Q₁
  have hk' : ((m * L : ℝ) : EReal) < maxLogGrowth Q₁ S₁ m :=
    (EReal.coe_lt_div_natCast_iff k.succ_pos).1 hk
  -- an `m`-sample e-variable `Y` with expected logarithm above a real `L' > m L`
  obtain ⟨L', hL'1, hL'2⟩ := EReal.lt_iff_exists_real_btwn.1 hk'
  rw [maxLogGrowth_def] at hL'2
  obtain ⟨Y, hYe, hYL⟩ := lt_maxEPower_iff.1 hL'2
  rw [EReal.coe_lt_coe_iff] at hL'1
  -- mixed with a constant, at the cost `θ` in expected logarithm
  set θ := (L' - m * L) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hδ0 : 0 < 1 - Real.exp (-θ) := sub_pos.2 (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hθ0))
  set W : (Fin m → 𝓧) → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (Real.exp (-θ)) * Y x + ENNReal.ofReal (1 - Real.exp (-θ))
  have hWm : Measurable W := (measurable_const.mul hYe.measurable).add measurable_const
  have hWδ (x : Fin m → 𝓧) : ENNReal.ofReal (1 - Real.exp (-θ)) ≤ W x := le_add_self
  have hW0 (x : Fin m → 𝓧) : W x ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ0) (hWδ x)).ne'
  have hWL : (((m * L + θ) : ℝ) : EReal) < ∫ᵉ x, ENNReal.log (W x) ∂μQ := by
    have hpt (x : Fin m → 𝓧) : ENNReal.log (Y x) + ((-θ : ℝ) : EReal) ≤ ENNReal.log (W x) := by
      calc ENNReal.log (Y x) + ((-θ : ℝ) : EReal)
      _ = ENNReal.log (ENNReal.ofReal (Real.exp (-θ)) * Y x) := by
        rw [ENNReal.log_mul_add, ENNReal.log_ofReal_exp, add_comm]
      _ ≤ ENNReal.log (W x) := ENNReal.log_le_log le_self_add
    have hc : ∫ᵉ _, ((-θ : ℝ) : EReal) ∂μQ = ((-θ : ℝ) : EReal) := by
      rw [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
    calc (((m * L + θ) : ℝ) : EReal)
    _ = ((L' + -θ : ℝ) : EReal) := by
      congr 1
      rw [hθ]
      ring
    _ < ∫ᵉ x, ENNReal.log (Y x) ∂μQ + ((-θ : ℝ) : EReal) := by
      rw [EReal.coe_add]
      exact EReal.add_lt_add_right_coe hYL _
    _ = ∫ᵉ x, ENNReal.log (Y x) + ((-θ : ℝ) : EReal) ∂μQ := by
      rw [eintegral_add' (f := fun x ↦ ENNReal.log (Y x)) (g := fun _ ↦ ((-θ : ℝ) : EReal))
        (ENNReal.measurable_log.comp hYe.measurable).aemeasurable aemeasurable_const
        (by rw [hc]; exact EReal.coe_ne_top _) (by rw [hc]; exact EReal.coe_ne_bot _), hc]
    _ ≤ ∫ᵉ x, ENNReal.log (W x) ∂μQ := eintegral_mono hpt
  -- and with its logarithm truncated at a level `c` where its mean still exceeds `m L`
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((m * L : ℝ) : EReal) <
      ∫ᵉ x, min (ENNReal.log (W x)) (c : EReal) ∂μQ := by
    by_contra! h
    exact (hWL.trans_le (eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hWm)
      h)).not_ge (EReal.coe_le_coe_iff.2 (by linarith))
  set v : (Fin m → 𝓧) → ℝ := fun x ↦ (min (ENNReal.log (W x)) (c : EReal)).toReal
  have hv (x : Fin m → 𝓧) : (v x : EReal) = min (ENNReal.log (W x)) (c : EReal) :=
    EReal.coe_toReal (ne_top_of_le_ne_top (EReal.natCast_ne_top c) (min_le_right _ _))
      (by simp [hW0 x, EReal.natCast_ne_bot])
  have hvm : Measurable v :=
    measurable_ereal_toReal.comp ((ENNReal.measurable_log.comp hWm).min measurable_const)
  refine ⟨v, hvm, ⟨c, fun x ↦ EReal.coe_le_coe_iff.1 ((hv x).trans_le (min_le_right _ _))⟩,
    fun P hP hPp ↦ ?_, ?_⟩
  · -- the bet `exp v` is at most `W`, whose expectation under the null is at most `1`
    have hY1 : ∫⁻ x, Y x ∂Measure.pi (fun _ : Fin m ↦ P) ≤ 1 := by
      exact hYe.lintegral_le_one (pi_mem_sampleNull hP)
    have hexp (x : Fin m → 𝓧) : ENNReal.ofReal (Real.exp (v x)) ≤ W x := by
      rw [← ENNReal.log_le_log_iff, ENNReal.log_ofReal_exp, hv x]
      exact min_le_left _ _
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (v x)) ∂Measure.pi (fun _ : Fin m ↦ P)
    _ ≤ ∫⁻ x, W x ∂Measure.pi (fun _ : Fin m ↦ P) := lintegral_mono hexp
    _ = ENNReal.ofReal (Real.exp (-θ)) * ∫⁻ x, Y x ∂Measure.pi (fun _ : Fin m ↦ P) +
        ENNReal.ofReal (1 - Real.exp (-θ)) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hYe.measurable,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (Real.exp (-θ)) * 1 + ENNReal.ofReal (1 - Real.exp (-θ)) := by gcongr
    _ = 1 := by
      rw [mul_one, ← ENNReal.ofReal_add (Real.exp_pos _).le hδ0.le, add_sub_cancel,
        ENNReal.ofReal_one]
  · -- `v` lies between `log (1 - exp (-θ))` and `c`, and its mean exceeds `m L`
    have hvi : Integrable v μQ := by
      refine Integrable.of_mem_Icc (Real.log (1 - Real.exp (-θ))) c hvm.aemeasurable
        (ae_of_all _ fun x ↦ ⟨?_, ?_⟩) <;> rw [← EReal.coe_le_coe_iff, hv x]
      · refine le_min ?_ ?_
        · rw [← ENNReal.log_ofReal_of_pos hδ0]
          exact ENNReal.log_le_log (hWδ x)
        · exact (EReal.coe_le_coe_iff.2 (Real.log_nonpos hδ0.le
            (by linarith [Real.exp_pos (-θ)]))).trans (by exact_mod_cast Nat.zero_le c)
      · rw [EReal.coe_natCast]
        exact min_le_right _ _
    rw [eintegral_congr fun x ↦ (hv x).symm, eintegral_eq_integral hvi,
      EReal.coe_lt_coe_iff] at hc
    exact hc

/-! ### The sequential tests -/

/-- The test that stops when the product of the bets over the complete blocks reaches `c > 1`
makes at most `m` times as many observations as the number of blocks over which the product of the
bets first reaches `c`. -/
private lemma toENNReal_hittingAfter_add_one_le {m : ℕ} (hm : m ≠ 0) (V : (Fin m → 𝓧) → ℝ≥0∞)
    {c : ℝ≥0∞} (hc : 1 < c) (ω : ℕ → 𝓧) :
    ENat.toENNReal (hittingAfter (fun n ω ↦ seqBlockProd m V ((n + 1) / m) ω) (Set.Ici c) 0 ω) +
        1 ≤ m * ENat.toENNReal (hittingAfter (seqBlockProd m V) (Set.Ici c) 0 ω) := by
  set N : ℕ∞ := hittingAfter (seqBlockProd m V) (Set.Ici c) 0 ω with hN
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENat.toENNReal_top, ENNReal.mul_top (by exact_mod_cast hm)]
    exact le_top
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hNtop
  have hck : c ≤ seqBlockProd m V k ω := by
    have h := hittingAfter_mem_set_of_ne_top (u := seqBlockProd m V) (s := Set.Ici c) (n := 0)
      (ω := ω) hNtop
    rwa [← hN, ← hk] at h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (hck.trans_eq (seqBlockProd_zero m V ω)).not_gt hc
  have hmk : 1 ≤ m * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm hk0)
  -- at the time `m k - 1`, the product over the complete blocks is the product over `k` blocks
  have hτ : hittingAfter (fun n ω ↦ seqBlockProd m V ((n + 1) / m) ω) (Set.Ici c) 0 ω ≤
      WithTop.some (m * k - 1) := by
    refine hittingAfter_le_of_mem (Nat.zero_le _) ?_
    rw [Set.mem_Ici, Nat.sub_add_cancel hmk, Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm)]
    exact hck
  rw [← hk, ENat.toENNReal_coe]
  calc ENat.toENNReal (hittingAfter (fun n ω ↦ seqBlockProd m V ((n + 1) / m) ω) (Set.Ici c) 0 ω)
      + 1
  _ ≤ ((m * k - 1 : ℕ) : ℝ≥0∞) + 1 := by
    gcongr
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.2 hτ
  _ = ((m * k - 1 + 1 : ℕ) : ℝ≥0∞) := by rw [Nat.cast_add, Nat.cast_one]
  _ = m * k := by rw [Nat.sub_add_cancel hmk, Nat.cast_mul]

/-- **Expected number of observations of a block test.** Let `v` be a measurable function on `m`
observations, bounded above by `C`, of mean `a > 0` under `Q₁ ^ m`. Under the i.i.d. law of
`Q₁`, the test that stops when the product of the bets `exp v` over the complete blocks reaches
`c = exp b > 1` makes at most `m (b + C) / a` observations in expectation: by Wald's bound, the
sum of the values of `v` over the blocks reaches `b` after at most `(b + C) / a` blocks in
expectation. -/
private lemma lintegral_hittingAfter_add_one_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    {m : ℕ} (hm : m ≠ 0) {v : (Fin m → 𝓧) → ℝ} (hv : Measurable v) {C : ℝ} (hvC : ∀ x, v x ≤ C)
    (ha : 0 < ∫ x, v x ∂Measure.pi fun _ : Fin m ↦ Q₁) {c : ℝ≥0∞} (hc : 1 < c) {b : ℝ}
    (hcb : ENNReal.log c = b) :
    ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω ↦ seqBlockProd m
        (fun x ↦ ENNReal.ofReal (Real.exp (v x))) ((n + 1) / m) ω) (Set.Ici c) 0 ω) + 1
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      m * ENNReal.ofReal ((b + C) / ∫ x, v x ∂Measure.pi fun _ : Fin m ↦ Q₁) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set V : (Fin m → 𝓧) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (v x))
  -- the sums of the values of `v` over blocks
  set S : ℕ → (ℕ → 𝓧) → ℝ := fun k ω ↦ ∑ j ∈ Finset.range k, v (seqBlock m j ω)
  -- the product of the bets over `k` blocks reaches `c` when the sum of `v` reaches `b`
  have hN (ω : ℕ → 𝓧) : hittingAfter (seqBlockProd m V) (Set.Ici c) 0 ω =
      hittingAfter S (Set.Ici b) 0 ω := by
    refine hittingAfter_apply_congr fun k _ ↦ ?_
    rw [Set.mem_Ici, Set.mem_Ici, ← ENNReal.log_le_log_iff, seqBlockProd_def,
      ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
      ENNReal.log_ofReal_exp, hcb, EReal.coe_le_coe_iff]
  -- Wald's bound for the number of blocks over which the sum of `v` reaches `b`
  have hWald := iIndepFun.lintegral_hittingAfter_sum_le (μ := μ)
    (X := fun j ω ↦ v (seqBlock m j ω))
    ((iIndepFun_seqBlock (fun _ ↦ Q₁) m).comp (fun _ ↦ v) fun _ ↦ hv)
    (fun j ↦ hv.comp (measurable_seqBlock m j)) ha (fun j ↦ ?_)
    (fun j ↦ ae_of_all _ fun ω ↦ hvC _) b
  swap
  · have h := measurePreserving_seqBlock (fun _ : ℕ ↦ Q₁) m j
    refine le_of_eq ?_
    rw [← integral_map (measurable_seqBlock m j).aemeasurable
      (by rw [h.map_eq]; exact hv.aestronglyMeasurable), h.map_eq]
  calc ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω ↦ seqBlockProd m V ((n + 1) / m) ω)
      (Set.Ici c) 0 ω) + 1 ∂μ
  _ ≤ ∫⁻ ω, m * ENat.toENNReal (hittingAfter (seqBlockProd m V) (Set.Ici c) 0 ω) ∂μ :=
    lintegral_mono fun ω ↦ toENNReal_hittingAfter_add_one_le hm V hc ω
  _ = m * ∫⁻ ω, ENat.toENNReal (hittingAfter S (Set.Ici b) 0 ω) ∂μ := by
    simp_rw [hN]
    rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m)]
  _ ≤ m * ENNReal.ofReal ((b + C) / ∫ x, v x ∂Measure.pi fun _ : Fin m ↦ Q₁) := by gcongr

/-- **Sequential tests attain the bipolar rate to first order.** For every real `d' > 0` below the
bipolar rate of `Q₁` against `S₁`, there are sequential tests `τ α` of every level `α` for the
i.i.d. laws of the members of the null, stopping times of `Filtration.piLE` with
`P^ℕ (τ α < ∞) ≤ α` for every member `P` of the null,
whose expected numbers of observations `𝔼[τ α + 1]` under the i.i.d. law of `Q₁` satisfy
`limsup_{α → 0} 𝔼[τ α + 1] / log (1/α) ≤ 1 / d'` [EVR26, Note 01]. With the lower bound
`log (1/α) / d ≤ 𝔼[τ + 1]` for every test of level `α`, where `d` is the bipolar rate, the
optimal expected number of observations is `log (1/α) / d` to first order. The tests bet on
successive blocks of `m` observations and stop when the product of the bets reaches `α⁻¹`. The
bipolar rate may be infinite. Neither `Q₁` nor the members of `S₁` need be probability measures:
the i.i.d. law of a measure that is not one is `0`. -/
theorem exists_isLevelStoppingTime_limsup_lintegral_div_log_le (Q₁ : Measure 𝓧) {d' : ℝ}
    (hd' : 0 < d') (hd'd : (d' : EReal) < bipolarRate Q₁ S₁) :
    ∃ τ : ℝ≥0∞ → (ℕ → 𝓧) → WithTop ℕ,
      (∀ α, IsLevelStoppingTime (τ α) (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
        (iidNull S₁) α) ∧
      limsup (fun α ↦ (∫⁻ ω, ENat.toENNReal (τ α ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) /
        (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) ≤ ENNReal.ofReal d'⁻¹ := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · -- the i.i.d. law of `Q₁` is `0`: never stop
    refine ⟨fun _ _ ↦ ⊤, fun α ↦ ⟨fun i ↦ by simp, fun P _ ↦ by simp⟩, ?_⟩
    simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0) hQ]
  obtain ⟨m, hm, v, hv, ⟨C₀, hvC₀⟩, hvP, hmv⟩ := exists_bounded_bet Q₁ hd'd
  set C := max C₀ 0
  have hvC (x : Fin m → 𝓧) : v x ≤ C := (hvC₀ x).trans (le_max_left _ _)
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set a := ∫ x, v x ∂Measure.pi fun _ : Fin m ↦ Q₁
  have ha : 0 < a := (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hd').trans hmv
  set V : (Fin m → 𝓧) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (v x))
  have hVm : Measurable V := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hv)
  -- the product of the bets over the complete blocks among the first `n + 1` observations
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦ seqBlockProd m V ((n + 1) / m) ω
  have hE : Adapted (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) E := fun n ↦
    Filtration.measurable_piLE_of_dependsOn (measurable_seqBlockProd hVm _)
      ((dependsOn_seqBlockProd V _).mono (Set.Iio_subset_Iio (Nat.div_mul_le_self _ _)))
  refine ⟨fun α ↦ hittingAfter E (Set.Ici α⁻¹) 0, fun α ↦
    ⟨hE.isStoppingTime_hittingAfter measurableSet_Ici, ?_⟩, ?_⟩
  · -- the level, by Ville's inequality
    rw [iidNull_def]
    rintro _ ⟨P, hP, rfl⟩
    by_cases hP' : IsProbabilityMeasure P
    swap
    · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ P) (i := 0)
        hP']
    refine (measure_mono fun ω hω ↦ ?_).trans
      ((measure_exists_le_seqBlockProd_le P hVm (hvP P hP hP') α⁻¹).trans_eq (inv_inv α))
    obtain ⟨n, -, hn⟩ := hittingAfter_lt_top_iff.1 hω
    exact ⟨_, hn⟩
  -- the expected number of observations, for `α ∈ (0, 1)`
  set B : ℝ≥0∞ → ℝ≥0∞ := fun α ↦ (ENNReal.log α⁻¹).toENNReal
  have hbound : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0∞),
      (∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) + 1 ∂μ) / B α ≤
        ENNReal.ofReal (m / a) * (1 + ENNReal.ofReal C / B α) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with α ⟨hα0, hα1⟩
    have hlog_top : ENNReal.log α⁻¹ ≠ ⊤ := by simpa using hα0.ne'
    have hlog_bot : ENNReal.log α⁻¹ ≠ ⊥ := by simpa using hα1.ne_top
    set b := (ENNReal.log α⁻¹).toReal
    have hb : (b : EReal) = ENNReal.log α⁻¹ := EReal.coe_toReal hlog_top hlog_bot
    have hb0 : 0 < b := by
      rw [← EReal.coe_lt_coe_iff, hb, EReal.coe_zero, ENNReal.zero_lt_log_iff]
      exact ENNReal.one_lt_inv.2 hα1
    have hBb : B α = ENNReal.ofReal b := EReal.toENNReal_of_ne_top hlog_top
    have hexp := lintegral_hittingAfter_add_one_le Q₁ hm hv hvC ha (ENNReal.one_lt_inv.2 hα1)
      hb.symm
    have hB0 : B α ≠ 0 := by rw [hBb]; exact (ENNReal.ofReal_pos.2 hb0).ne'
    have hBtop : B α ≠ ⊤ := by rw [hBb]; exact ENNReal.ofReal_ne_top
    calc (∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) + 1 ∂μ) / B α
    _ ≤ m * ENNReal.ofReal ((b + C) / a) / B α := by gcongr
    _ = ENNReal.ofReal (m / a) * (B α + ENNReal.ofReal C) / B α := by
      rw [hBb, ← ENNReal.ofReal_add hb0.le (le_max_right _ _), ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    _ = ENNReal.ofReal (m / a) * ((B α + ENNReal.ofReal C) / B α) := mul_div_assoc _ _ _
    _ = ENNReal.ofReal (m / a) * (1 + ENNReal.ofReal C / B α) := by
      rw [ENNReal.add_div, ENNReal.div_self hB0 hBtop]
  -- the bound tends to `m / a` as `α → 0`
  have hB : Tendsto B (𝓝[>] 0) (𝓝 ⊤) := by
    have h : Continuous B :=
      EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp continuous_inv)
    simpa [B] using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun α ↦ ENNReal.ofReal (m / a) * (1 + ENNReal.ofReal C / B α)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (m / a))) := by
    have h := ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul (tendsto_inv_iff.2 hB) (.inr ENNReal.ofReal_ne_top)))
      (.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (m / a)) (b := 1 + ENNReal.ofReal C * ⊤⁻¹)
    simpa [div_eq_mul_inv] using h
  calc limsup (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) + 1 ∂μ) /
      B α) (𝓝[>] 0)
  _ ≤ limsup (fun α ↦ ENNReal.ofReal (m / a) * (1 + ENNReal.ofReal C / B α)) (𝓝[>] 0) :=
    limsup_le_limsup hbound
  _ = ENNReal.ofReal (m / a) := hlim.limsup_eq
  _ ≤ ENNReal.ofReal d'⁻¹ := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ ha, ← div_eq_inv_mul, le_div_iff₀ hd']
    linarith

end ProbabilityTheory
