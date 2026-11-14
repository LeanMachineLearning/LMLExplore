/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
public import LMLExplore.Probability.Process.StoppedValueLimsup
public import LMLExplore.Probability.Process.Stopping
public import Mathlib.Probability.Martingale.Convergence

/-!
# Convergence and optional stopping of supermartingales in `ℝ≥0∞`

An `ℝ≥0∞`-valued supermartingale `M` with finite initial expectation under a finite measure
converges almost surely, and its limit `limsup M` is almost surely finite with
`∫⁻ limsup M ≤ ∫⁻ M 0` [RW, Fact 7.5]. This is what gives a meaning to the value of `M` at a
stopping time that may be infinite:
`ProbabilityTheory.stoppedValueLimsup M τ` is `M (τ ω) ω` where `τ ω` is finite and
`limsup (M · ω)` where `τ ω = ⊤` [RRLK; RLKR23, (1.2)]
(`LMLExplore/Probability/Process/StoppedValueLimsup.lean`).

The optional stopping theorem then holds at arbitrary stopping times, with no condition beyond a
finite measure and finite initial expectation [RW, Fact 7.5; ShSVV11, Theorem 1]: for
stopping times `σ ≤ τ` and every `s` measurable for the σ-algebra of `σ`,
`∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P`. In particular
the value of a test supermartingale at any stopping time is an e-variable, which is what makes
test supermartingales valid under optional stopping and the starting point of e-processes.
Mathlib's `MeasureTheory.Submartingale.expected_stoppedValue_mono` is the case of bounded stopping
times for integrable real processes.

## Main statements

* `ProbabilityTheory.IsENNSupermartingale.ae_tendsto_limsup`: almost sure convergence.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_limsup_le`: the limit closes the
  supermartingale, `∫⁻ ω in s, limsup M ω ≤ ∫⁻ ω in s, M n ω` for `ℱ n`-measurable `s`.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_stoppedProcess_le`: optional stopping for
  stopped processes at a fixed time.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_stoppedValueLimsup_le`: optional stopping at
  arbitrary stopping times `σ ≤ τ`.
* `ProbabilityTheory.IsTestSupermartingale.isEVar_stoppedValueLimsup`: the value of a test
  supermartingale at any stopping time is an e-variable.

## Implementation notes

Stopped processes are first compared at a fixed time
(`ProbabilityTheory.IsENNSupermartingale.setLIntegral_stoppedProcess_le`), which needs no
integrability at all; Fatou's lemma passes to the limit where `σ` is bounded, and the events
`{σ ≤ k}` exhaust `{σ < ⊤}`. Almost sure convergence comes from Mathlib's martingale convergence
theorem `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`, applied to the real
supermartingale `(M n).toReal`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [ShSVV11] G. Shafer, A. Shen, N. Vereshchagin and V. Vovk, *Test martingales, Bayes factors and
  p-values*, Statist. Sci. 26 (2011), arXiv:0912.4269.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167.
* [RLKR23] J. Ruf, M. Larsson, W. M. Koolen and A. Ramdas, *A composite generalization of Ville's
  martingale theorem using e-processes*, Electron. J. Probab. 28 (2023), arXiv:2203.04485.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {P : Measure Ω} {M : ℕ → Ω → ℝ≥0∞} {σ τ : Ω → WithTop ℕ}

/-! ### Almost sure convergence -/

namespace IsENNSupermartingale

/-- An `ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite measure
converges almost surely, to its `limsup` [RW, Fact 7.5]. -/
theorem ae_tendsto_limsup (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (limsup (fun n ↦ M n ω) atTop)) := by
  have hbdd : ⨆ n, eLpNorm ((-fun n ω ↦ (M n ω).toReal) n) 1 P < ∞ := by
    refine (iSup_le fun n ↦ ?_).trans_lt h0.lt_top
    rw [eLpNorm_one_eq_lintegral_eNorm]
    · refine (lintegral_mono fun ω ↦ ?_).trans (hM.lintegral_le hP n.zero_le)
      rw [Pi.neg_apply, Pi.neg_apply, eNorm_neg, Real.eNorm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    · exact (hM.measurable n).ennreal_toReal.neg.aestronglyMeasurable
  filter_upwards [(hM.supermartingale_toReal hP h0).neg.exists_ae_tendsto_of_bdd hbdd,
    hM.ae_lt_top hP h0] with ω ⟨c, hc⟩ hfin
  have hlim : Tendsto (fun n ↦ M n ω) atTop (𝓝 (ENNReal.ofReal (-c))) := by
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hc.neg).congr fun n ↦ ?_
    simp [ENNReal.ofReal_toReal (hfin n).ne]
  rwa [hlim.limsup_eq]

/-! ### Optional stopping -/

/-- In `WithTop ℕ`, a value strictly above `n` is at least `n + 1`. -/
private lemma coe_add_one_le_of_coe_lt {n : ℕ} {x : WithTop ℕ} (h : (n : WithTop ℕ) < x) :
    ((n + 1 : ℕ) : WithTop ℕ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe x => exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt (WithTop.coe_lt_coe.1 h))

/-- One step of the stopped process: its set integrals over `ℱ n`-measurable sets do not increase
from time `n` to time `n + 1`. -/
private lemma setLIntegral_stoppedProcess_succ_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    (hτ : IsStoppingTime ℱ τ) (n : ℕ) {t : Set Ω} (ht : MeasurableSet[ℱ n] t) :
    ∫⁻ ω in t, MeasureTheory.stoppedProcess M τ (n + 1) ω ∂P ≤
      ∫⁻ ω in t, MeasureTheory.stoppedProcess M τ n ω ∂P := by
  have hC := hτ.measurableSet_gt n
  have htC := ℱ.le n _ (ht.inter hC)
  rw [← lintegral_inter_add_sdiff _ t (ℱ.le n _ hC),
    ← lintegral_inter_add_sdiff (fun ω ↦ MeasureTheory.stoppedProcess M τ n ω) t (ℱ.le n _ hC)]
  refine add_le_add ?_ (setLIntegral_congr_fun (ℱ.le n _ (ht.diff hC)) fun ω hω ↦ ?_).le
  · rw [setLIntegral_congr_fun htC fun ω hω ↦ stoppedProcess_eq_of_le (i := n + 1)
        (coe_add_one_le_of_coe_lt hω.2),
      setLIntegral_congr_fun htC fun ω hω ↦ stoppedProcess_eq_of_le (i := n) hω.2.le]
    exact hM.setLIntegral_succ_le P hP n _ (ht.inter hC)
  · have hτn : τ ω ≤ n := not_lt.1 hω.2
    rw [stoppedProcess_eq_of_ge (i := n) hτn,
      stoppedProcess_eq_of_ge (i := n + 1) (hτn.trans (WithTop.coe_le_coe.2 n.le_succ))]

/-- **Optional stopping for stopped processes.** For stopping times `σ ≤ τ` and every set `s`
measurable for the σ-algebra of `σ`, the set integral over `s` of the process stopped at `τ` is
at most that of the process stopped at `σ`, at every time. No integrability is needed. -/
theorem setLIntegral_stoppedProcess_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, MeasureTheory.stoppedProcess M τ n ω ∂P ≤
      ∫⁻ ω in s, MeasureTheory.stoppedProcess M σ n ω ∂P := by
  induction n generalizing s with
  | zero =>
    refine (setLIntegral_congr_fun (hσ.measurableSpace_le s hs) fun ω _ ↦ ?_).le
    rw [stoppedProcess_eq_of_le (i := 0) bot_le, stoppedProcess_eq_of_le (i := 0) bot_le]
  | succ n ih =>
    have hsm := hσ.measurableSpace_le s hs
    have hB := ℱ.le n _ (hσ.measurableSet_le n)
    rw [← lintegral_inter_add_sdiff _ s hB,
      ← lintegral_inter_add_sdiff (fun ω ↦ MeasureTheory.stoppedProcess M σ (n + 1) ω) s hB]
    refine add_le_add ?_ (setLIntegral_congr_fun (hsm.diff hB) fun ω hω ↦ ?_).le
    · calc ∫⁻ ω in s ∩ {ω | σ ω ≤ n}, MeasureTheory.stoppedProcess M τ (n + 1) ω ∂P
          ≤ ∫⁻ ω in s ∩ {ω | σ ω ≤ n}, MeasureTheory.stoppedProcess M τ n ω ∂P :=
            setLIntegral_stoppedProcess_succ_le hM hP hτ n (((hσ.measurableSet s).1 hs).2 n)
        _ ≤ ∫⁻ ω in s ∩ {ω | σ ω ≤ n}, MeasureTheory.stoppedProcess M σ n ω ∂P :=
            ih (hs.inter (hσ.measurableSet_le' n))
        _ = ∫⁻ ω in s ∩ {ω | σ ω ≤ n}, MeasureTheory.stoppedProcess M σ (n + 1) ω ∂P :=
            setLIntegral_congr_fun (hsm.inter hB) fun ω hω ↦ by
              rw [stoppedProcess_eq_of_ge (i := n) hω.2, stoppedProcess_eq_of_ge (i := n + 1)
                (hω.2.trans (WithTop.coe_le_coe.2 n.le_succ))]
    · have hσn : ¬σ ω ≤ WithTop.some n := hω.2
      have hσn' : WithTop.some (n + 1) ≤ σ ω := coe_add_one_le_of_coe_lt (not_le.1 hσn)
      rw [stoppedProcess_eq_of_le (i := n + 1) (hσn'.trans (hστ ω)),
        stoppedProcess_eq_of_le (i := n + 1) hσn']

/-- Optional stopping where the smaller stopping time is bounded. -/
private lemma setLIntegral_stoppedValueLimsup_le_of_le_const (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {N : ℕ} (hσN : ∀ ω, σ ω ≤ N) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P := by
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ MeasureTheory.stoppedProcess M τ n ω) atTop
      (𝓝 (stoppedValueLimsup M τ ω)) := by
    filter_upwards [hM.ae_tendsto_limsup hP h0] with ω hω
    exact tendsto_stoppedProcess_stoppedValueLimsup fun _ ↦ hω
  have hmeas (n : ℕ) : Measurable (MeasureTheory.stoppedProcess M τ n) := by
    rw [stoppedProcess_eq_stoppedValue]
    exact measurable_stoppedValue_of_countable hM.measurable
      (measurable_const.min hτ.measurable')
  calc ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P
      = ∫⁻ ω in s, liminf (fun n ↦ MeasureTheory.stoppedProcess M τ n ω) atTop ∂P :=
        lintegral_congr_ae (ae_restrict_of_ae (hlim.mono fun ω hω ↦ hω.liminf_eq.symm))
    _ ≤ liminf (fun n ↦ ∫⁻ ω in s, MeasureTheory.stoppedProcess M τ n ω ∂P) atTop :=
        lintegral_liminf_le' fun n ↦ (hmeas n).aemeasurable
    _ ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P := by
      refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
      filter_upwards [eventually_ge_atTop N] with n hn
      refine (hM.setLIntegral_stoppedProcess_le hP hσ hτ hστ n hs).trans_eq ?_
      exact setLIntegral_congr_fun (hσ.measurableSpace_le s hs) fun ω _ ↦
        stoppedProcess_eq_stoppedValueLimsup ((hσN ω).trans (WithTop.coe_le_coe.2 hn))

/-- **Optional stopping at arbitrary stopping times** [RW, Fact 7.5; ShSVV11, Theorem 1]. For an
`ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite measure, stopping
times `σ ≤ τ` with values in `WithTop ℕ` and every set `s` measurable for the σ-algebra of `σ`,
`∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P`. -/
theorem setLIntegral_stoppedValueLimsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P := by
  have hsm := hσ.measurableSpace_le s hs
  have hT : MeasurableSet {ω | σ ω = ⊤} := hσ.measurable' (measurableSet_singleton ⊤)
  rw [← lintegral_inter_add_sdiff _ s hT, ← lintegral_inter_add_sdiff (stoppedValueLimsup M σ) s hT]
  refine add_le_add (setLIntegral_congr_fun (hsm.inter hT) fun ω hω ↦ ?_).le ?_
  · -- where `σ` is infinite, so is `τ`
    rw [stoppedValueLimsup_of_eq_top (top_unique (hω.2 ▸ hστ ω)), stoppedValueLimsup_of_eq_top hω.2]
  -- exhaust `{σ < ⊤}` by the events `{σ ≤ k}`, on which `σ` is the bounded time `min σ k`
  have hU : s \ {ω | σ ω = ⊤} = ⋃ k : ℕ, s ∩ {ω | σ ω ≤ k} := by
    ext ω
    simp only [Set.mem_sdiff, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    refine ⟨fun ⟨hs, hne⟩ ↦ ?_, fun ⟨k, hs, hk⟩ ↦ ⟨hs, ne_top_of_le_ne_top WithTop.coe_ne_top hk⟩⟩
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
    exact ⟨k, hs, hk ▸ le_rfl⟩
  have hdir : Directed (· ⊆ ·) fun k : ℕ ↦ s ∩ {ω | σ ω ≤ k} :=
    Monotone.directed_le fun i j hij ω hω ↦ ⟨hω.1, hω.2.trans (WithTop.coe_le_coe.2 hij)⟩
  rw [hU, setLIntegral_iUnion_of_directed _ hdir, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_mono fun k ↦ ?_
  have hk : MeasurableSet[(hσ.min_const k).measurableSpace] (s ∩ {ω | σ ω ≤ k}) :=
    (hσ.measurableSet_inter_le_const_iff s k).1 (hs.inter (hσ.measurableSet_le' k))
  calc ∫⁻ ω in s ∩ {ω | σ ω ≤ k}, stoppedValueLimsup M τ ω ∂P
      ≤ ∫⁻ ω in s ∩ {ω | σ ω ≤ k}, stoppedValueLimsup M (fun ω ↦ min (σ ω) k) ω ∂P :=
        setLIntegral_stoppedValueLimsup_le_of_le_const hM hP h0 (hσ.min_const k) hτ
          (fun ω ↦ (min_le_left _ _).trans (hστ ω)) (fun ω ↦ min_le_right _ _) hk
    _ = ∫⁻ ω in s ∩ {ω | σ ω ≤ k}, stoppedValueLimsup M σ ω ∂P :=
        setLIntegral_congr_fun (hsm.inter (ℱ.le k _ (hσ.measurableSet_le k))) fun ω hω ↦
          stoppedValueLimsup_congr (min_eq_left hω.2)

/-- Optional stopping from time `0`: `∫⁻ stoppedValueLimsup M τ ≤ ∫⁻ M 0` at every stopping
time. -/
theorem lintegral_stoppedValueLimsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (hτ : IsStoppingTime ℱ τ) :
    ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω, M 0 ω ∂P := by
  have := hM.setLIntegral_stoppedValueLimsup_le hP h0 (isStoppingTime_const ℱ 0) hτ
    (fun ω ↦ bot_le) MeasurableSet.univ
  rwa [stoppedValueLimsup_const, Measure.restrict_univ] at this

/-- The almost sure limit closes the supermartingale: for every `ℱ n`-measurable `s`,
`∫⁻ ω in s, limsup M ω ≤ ∫⁻ ω in s, M n ω`. -/
theorem setLIntegral_limsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {n : ℕ} {s : Set Ω}
    (hs : MeasurableSet[ℱ n] s) :
    ∫⁻ ω in s, limsup (fun k ↦ M k ω) atTop ∂P ≤ ∫⁻ ω in s, M n ω ∂P := by
  have hs' : MeasurableSet[(isStoppingTime_const ℱ n).measurableSpace] s := by
    rwa [IsStoppingTime.measurableSpace_const]
  have := hM.setLIntegral_stoppedValueLimsup_le hP h0 (isStoppingTime_const ℱ n)
    (isStoppingTime_top ℱ) (fun _ ↦ le_top) hs'
  rwa [stoppedValueLimsup_const, stoppedValueLimsup_top] at this

/-- The almost sure limit has expectation at most `∫⁻ M 0`. -/
theorem lintegral_limsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∫⁻ ω, limsup (fun n ↦ M n ω) atTop ∂P ≤ ∫⁻ ω, M 0 ω ∂P := by
  simpa using hM.setLIntegral_limsup_le hP h0 (n := 0) MeasurableSet.univ

/-- The almost sure limit is almost surely finite. -/
theorem ae_limsup_lt_top (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) : ∀ᵐ ω ∂P, limsup (fun n ↦ M n ω) atTop < ∞ :=
  MeasureTheory.ae_lt_top (Measurable.limsup hM.measurable)
    ((hM.lintegral_limsup_le hP h0).trans_lt h0.lt_top).ne

end IsENNSupermartingale

/-! ### Test supermartingales -/

namespace IsTestSupermartingale

variable (hM : IsTestSupermartingale M ℱ S)
include hM

/-- A test supermartingale converges almost surely, under every finite member of the null. -/
theorem ae_tendsto_limsup (hP : P ∈ S) [IsFiniteMeasure P] :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (limsup (fun n ↦ M n ω) atTop)) :=
  hM.toIsENNSupermartingale.ae_tendsto_limsup hP (hM.lintegral_zero_ne_top hP)

/-- The almost sure limit of a test supermartingale is almost surely finite. -/
theorem ae_limsup_lt_top (hP : P ∈ S) [IsFiniteMeasure P] :
    ∀ᵐ ω ∂P, limsup (fun n ↦ M n ω) atTop < ∞ :=
  hM.toIsENNSupermartingale.ae_limsup_lt_top hP (hM.lintegral_zero_ne_top hP)

/-- Optional stopping for test supermartingales at arbitrary stopping times `σ ≤ τ`. -/
theorem setLIntegral_stoppedValueLimsup_le (hP : P ∈ S) [IsFiniteMeasure P]
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P :=
  hM.toIsENNSupermartingale.setLIntegral_stoppedValueLimsup_le hP (hM.lintegral_zero_ne_top hP)
    hσ hτ hστ hs

/-- The value of a test supermartingale at any stopping time has expectation at most `1`. -/
theorem lintegral_stoppedValueLimsup_le_one (hP : P ∈ S) [IsFiniteMeasure P]
    (hτ : IsStoppingTime ℱ τ) : ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ 1 :=
  (hM.toIsENNSupermartingale.lintegral_stoppedValueLimsup_le hP (hM.lintegral_zero_ne_top hP)
    hτ).trans (hM.lintegral_zero_le P hP)

/-- The value of a test supermartingale at any stopping time, with values in `WithTop ℕ`, is an
e-variable for a null of probability measures. -/
theorem isEVar_stoppedValueLimsup (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hτ : IsStoppingTime ℱ τ) : IsEVar (stoppedValueLimsup M τ) S :=
  IsEVar.of_lintegral_le_one hS (measurable_stoppedValueLimsup hM.measurable hτ.measurable')
    fun P hP ↦ have := hS P hP; hM.lintegral_stoppedValueLimsup_le_one hP hτ

end IsTestSupermartingale

end ProbabilityTheory
