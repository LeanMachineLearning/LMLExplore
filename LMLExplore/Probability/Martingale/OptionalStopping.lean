/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
public import LMLExplore.Probability.Process.Stopping
public import LMLExplore.Probability.Process.StoppedValue
public import Mathlib.Probability.Martingale.Convergence

/-!
# Convergence and optional stopping of `ℝ≥0∞`-valued supermartingales

An `ℝ≥0∞`-valued supermartingale (`ProbabilityTheory.IsENNSupermartingale`) with finite initial
expectation under a finite measure converges almost surely, to a limit that is almost surely
finite and whose set integrals are bounded by those of the process. Optional stopping then holds
at every pair of stopping times `σ ≤ τ` with values in `WithTop ℕ`, unbounded and possibly infinite:
the value of the process at a random time is `MeasureTheory.stoppedValueLimsup`, its `limsup` where
the time is infinite, and
`∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P` for every set `s`
measurable for the σ-algebra at `σ` [RW, Fact 7.5; ShSVV11]. For a test supermartingale for a null
of probability measures, the value at every stopping time is therefore an e-variable; this is the
validity of test supermartingales at stopping times on which e-processes and anytime-valid tests
rest.

For stopping times bounded by a constant, optional stopping needs neither the finiteness of the
initial expectation nor the convergence of the process, and holds for every `ℝ≥0∞`-valued
supermartingale. Mathlib's `MeasureTheory.Submartingale.expected_stoppedValue_mono` is the real
version for bounded stopping times, under integrability. Convergence is derived from Mathlib's
`MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd` through the real values of the process.

## Main statements

* `ProbabilityTheory.IsENNSupermartingale.ae_tendsto_limsup`,
  `ProbabilityTheory.IsENNSupermartingale.ae_limsup_lt_top`: almost sure convergence, to an almost
  surely finite limit.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_limsup_le`: the set integrals of the limit
  over `ℱ n`-measurable sets are at most those of `M n`.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_stoppedValueLimsup_le_of_le_const`: optional
  stopping for bounded stopping times, for every `ℝ≥0∞`-valued supermartingale.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_stoppedValueLimsup_le`: optional stopping for
  arbitrary stopping times with values in `WithTop ℕ`.
* `ProbabilityTheory.IsTestSupermartingale.lintegral_limsup_le_one`: the almost sure limit of a
  test supermartingale has expectation at most `1`.
* `ProbabilityTheory.IsTestSupermartingale.lintegral_stoppedValueLimsup_le_one`,
  `ProbabilityTheory.IsTestSupermartingale.isEVar_stoppedValueLimsup`: a test supermartingale has
  expectation at most `1` at every stopping time, where its value is an e-variable.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [ShSVV11] G. Shafer, A. Shen, N. Vereshchagin and V. Vovk, *Test martingales, Bayes factors and
  p-values*, Statist. Sci. 26 (2011), arXiv:0912.4269.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {P : Measure Ω} {M : ℕ → Ω → ℝ≥0∞} {σ τ : Ω → WithTop ℕ} {s : Set Ω}

/-- The interpolating times `max a (min b k)` move from `k` to `k + 1` where `a ≤ k < b`. -/
private lemma max_min_succ_of_le_of_lt {a b : WithTop ℕ} {k : ℕ} (ha : a ≤ k)
    (hb : (k : WithTop ℕ) < b) :
    max a (min b ↑(k + 1)) = ↑(k + 1) ∧ max a (min b k) = k := by
  have hb' : ((k + 1 : ℕ) : WithTop ℕ) ≤ b := ENat.natCast_add_one_le_iff.2 hb
  rw [min_eq_right hb', min_eq_right hb.le, max_eq_right (ha.trans (by simp)), max_eq_right ha]
  exact ⟨rfl, rfl⟩

/-- The interpolating times `max a (min b k)` do not move from `k` to `k + 1` outside
`a ≤ k < b`. -/
private lemma max_min_succ_eq {a b : WithTop ℕ} {k : ℕ} (h : ¬(a ≤ k ∧ (k : WithTop ℕ) < b)) :
    max a (min b ↑(k + 1)) = max a (min b k) := by
  rcases not_and_or.1 h with h | h
  · rw [not_le] at h
    have h' : ((k + 1 : ℕ) : WithTop ℕ) ≤ a := ENat.natCast_add_one_le_iff.2 h
    rw [max_eq_left ((min_le_right _ _).trans h'), max_eq_left ((min_le_right _ _).trans h.le)]
  · rw [not_lt] at h
    rw [min_eq_left (h.trans (by simp)), min_eq_left h]

namespace IsENNSupermartingale

/-- An `ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite measure
converges almost surely to a finite limit. -/
private theorem ae_exists_tendsto (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ c < ∞, Tendsto (fun n ↦ M n ω) atTop (𝓝 c) := by
  have hsub : Submartingale (fun n ω ↦ -(M n ω).toReal) ℱ P :=
    (hM.supermartingale_toReal hP h0).neg
  have hbdd : ⨆ n, eLpNorm (fun ω ↦ -(M n ω).toReal) 1 P < ∞ := by
    refine (iSup_le fun n ↦ ?_).trans_lt h0.lt_top
    rw [eLpNorm_one_eq_lintegral_eNorm (hsub.integrable n).aestronglyMeasurable]
    refine (lintegral_mono fun ω ↦ ?_).trans (hM.lintegral_le hP n.zero_le)
    rw [eNorm_neg, Real.eNorm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  filter_upwards [hsub.exists_ae_tendsto_of_bdd hbdd, hM.ae_lt_top hP h0] with ω ⟨c, hc⟩ hω
  refine ⟨ENNReal.ofReal (-c), ENNReal.ofReal_lt_top, ?_⟩
  refine ((ENNReal.continuous_ofReal.tendsto _).comp (by simpa using hc.neg)).congr fun n ↦ ?_
  exact ENNReal.ofReal_toReal (hω n).ne

/-- An `ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite measure
converges almost surely, so that its `limsup` is its limit [RW, Fact 7.5]. -/
theorem ae_tendsto_limsup (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (limsup (fun n ↦ M n ω) atTop)) := by
  filter_upwards [hM.ae_exists_tendsto hP h0] with ω ⟨c, _, hc⟩
  rwa [hc.limsup_eq]

/-- The almost sure limit of an `ℝ≥0∞`-valued supermartingale with finite initial expectation
under a finite measure is almost surely finite. -/
theorem ae_limsup_lt_top (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) : ∀ᵐ ω ∂P, limsup (fun n ↦ M n ω) atTop < ∞ := by
  filter_upwards [hM.ae_exists_tendsto hP h0] with ω ⟨c, hc_lt, hc⟩
  rwa [hc.limsup_eq]

/-- **Optional stopping for bounded stopping times.** For stopping times `σ ≤ τ ≤ N` and a set `s`
measurable for the σ-algebra at `σ`, the set integral over `s` of an `ℝ≥0∞`-valued
supermartingale at `τ` is at most its set integral at `σ`. No integrability is needed. -/
theorem setLIntegral_stoppedValueLimsup_le_of_le_const (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {N : ℕ}
    (hτN : ∀ ω, τ ω ≤ N) (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P := by
  -- The times `max σ (min τ k)` run from `σ` at `k = 0` to `τ` at `k = N`, and move from `k` to
  -- `k + 1` exactly on the `ℱ k`-measurable event `σ ≤ k < τ`.
  set g : ℕ → Ω → ℝ≥0∞ := fun k ↦ stoppedValueLimsup M fun ω ↦ max (σ ω) (min (τ ω) k)
  have hs' : MeasurableSet s := hσ.measurableSpace_le s hs
  have hstep (k : ℕ) : ∫⁻ ω in s, g (k + 1) ω ∂P ≤ ∫⁻ ω in s, g k ω ∂P := by
    set A := {ω | σ ω ≤ k} ∩ {ω | (k : WithTop ℕ) < τ ω}
    have hAk : MeasurableSet[ℱ k] A :=
      (hσ.measurableSet_le_natCast k).inter (hτ.measurableSet_natCast_lt k)
    have hA : MeasurableSet A := ℱ.le k _ hAk
    have hsA : MeasurableSet[ℱ k] (s ∩ A) := by
      have hsk := ((hσ.measurableSet s).1 hs).2 k
      rw [← Nat.cast_withTop] at hsk
      rw [← inter_assoc]
      exact hsk.inter (hτ.measurableSet_natCast_lt k)
    have hg_succ : EqOn (g (k + 1)) (M (k + 1)) (s ∩ A) := fun ω hω ↦
      stoppedValueLimsup_of_eq_natCast (max_min_succ_of_le_of_lt hω.2.1 hω.2.2).1
    have hg : EqOn (g k) (M k) (s ∩ A) := fun ω hω ↦
      stoppedValueLimsup_of_eq_natCast (max_min_succ_of_le_of_lt hω.2.1 hω.2.2).2
    have hg_diff : EqOn (g (k + 1)) (g k) (s \ A) := fun ω hω ↦ by
      exact stoppedValueLimsup_congr (max_min_succ_eq hω.2)
    rw [← lintegral_inter_add_sdiff _ s hA, ← lintegral_inter_add_sdiff (g k) s hA,
      setLIntegral_congr_fun (hs'.inter hA) hg_succ, setLIntegral_congr_fun (hs'.inter hA) hg,
      setLIntegral_congr_fun (hs'.diff hA) hg_diff]
    exact add_le_add_left (hM.setLIntegral_succ_le P hP k _ hsA) _
  have hg0 : g 0 = stoppedValueLimsup M σ := by simp [g]
  have hgN : g N = stoppedValueLimsup M τ := by
    simp only [g, min_eq_left (hτN _), max_eq_right (hστ _)]
  rw [← hg0, ← hgN]
  exact antitone_nat_of_succ_le (f := fun k ↦ ∫⁻ ω in s, g k ω ∂P) hstep N.zero_le

/-- **Optional stopping.** For an `ℝ≥0∞`-valued supermartingale with finite initial expectation
under a finite measure, stopping times `σ ≤ τ` with values in `WithTop ℕ` and a set `s`
measurable for the σ-algebra at `σ`, the set integral over `s` of the process at `τ` is at most
its set integral at `σ`, the value at an infinite time being the almost sure limit
[RW, Fact 7.5]. -/
theorem setLIntegral_stoppedValueLimsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P := by
  have hs' : MeasurableSet s := hσ.measurableSpace_le s hs
  have htop : MeasurableSet {ω | σ ω = ⊤} := hσ.measurableSet_eq_top
  rw [← lintegral_inter_add_sdiff _ s htop,
    ← lintegral_inter_add_sdiff (stoppedValueLimsup M σ) s htop]
  -- Where `σ` is infinite, so is `τ`, and the two values agree.
  refine add_le_add (setLIntegral_congr_fun (hs'.inter htop) fun ω hω ↦ ?_).le ?_
  · rw [stoppedValueLimsup_of_eq_top (top_le_iff.1 (hω.2 ▸ hστ ω)),
      stoppedValueLimsup_of_eq_top hω.2]
  -- Where `σ` is finite, apply the bounded case to `min σ N ≤ min τ N` on `s ∩ {σ ≤ N}`, and let
  -- `N` tend to infinity with Fatou's lemma.
  set F : ℕ → Ω → ℝ≥0∞ := fun N ↦
    (s ∩ {ω | σ ω ≤ N}).indicator (stoppedValueLimsup M fun ω ↦ min (τ ω) N)
  have hsN (N : ℕ) : MeasurableSet (s ∩ {ω | σ ω ≤ N}) :=
    hs'.inter (ℱ.le N _ (hσ.measurableSet_le_natCast N))
  have hsub (N : ℕ) : s ∩ {ω | σ ω ≤ N} ⊆ s \ {ω | σ ω = ⊤} := fun _ hω ↦
    ⟨hω.1, ne_top_of_le_ne_top (WithTop.natCast_ne_top N) hω.2⟩
  have hF_meas (N : ℕ) : Measurable (F N) :=
    (measurable_stoppedValueLimsup hM.measurable
      (hτ.min_natCast N).measurable').indicator (hsN N)
  have hF_le (N : ℕ) :
      ∫⁻ ω, F N ω ∂P ≤ ∫⁻ ω in s \ {ω | σ ω = ⊤}, stoppedValueLimsup M σ ω ∂P := by
    rw [lintegral_indicator (hsN N)]
    calc _ ≤ ∫⁻ ω in s ∩ {ω | σ ω ≤ N}, stoppedValueLimsup M (fun ω ↦ min (σ ω) N) ω ∂P := by
          have h := hM.setLIntegral_stoppedValueLimsup_le_of_le_const hP (hσ.min_const N)
            (hτ.min_const N) (fun ω ↦ min_le_min_right _ (hστ ω))
            (fun ω ↦ (min_le_right _ _).trans_eq (Nat.cast_withTop N).symm)
            ((hσ.measurableSet_inter_le_const_iff s N).1 (hs.inter (hσ.measurableSet_le' N)))
          rwa [← Nat.cast_withTop] at h
      _ = ∫⁻ ω in s ∩ {ω | σ ω ≤ N}, stoppedValueLimsup M σ ω ∂P :=
          setLIntegral_congr_fun (hsN N) fun ω hω ↦
            stoppedValueLimsup_congr (min_eq_left hω.2)
      _ ≤ _ := lintegral_mono_set (hsub N)
  have hF_tendsto : ∀ᵐ ω ∂P, Tendsto (fun N ↦ F N ω) atTop
      (𝓝 ((s \ {ω | σ ω = ⊤}).indicator (stoppedValueLimsup M τ) ω)) := by
    filter_upwards [hM.ae_tendsto_limsup hP h0] with ω hω
    by_cases hωs : ω ∈ s \ {ω | σ ω = ⊤}
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hωs.2
      rw [indicator_of_mem hωs]
      refine (tendsto_stoppedValueLimsup_min hω).congr' ?_
      filter_upwards [eventually_ge_atTop a] with N hN
      have hσN : σ ω ≤ N := by rw [← ha, Nat.cast_withTop, WithTop.coe_le_coe]; exact hN
      exact (indicator_of_mem (⟨hωs.1, hσN⟩ : ω ∈ s ∩ {ω | σ ω ≤ N}) _).symm
    · rw [indicator_of_notMem hωs]
      exact tendsto_const_nhds.congr fun N ↦
        (indicator_of_notMem (fun h ↦ hωs (hsub N h)) _).symm
  calc ∫⁻ ω in s \ {ω | σ ω = ⊤}, stoppedValueLimsup M τ ω ∂P
      = ∫⁻ ω, liminf (fun N ↦ F N ω) atTop ∂P := by
        rw [← lintegral_indicator (hs'.diff htop)]
        exact lintegral_congr_ae (hF_tendsto.mono fun ω hω ↦ hω.liminf_eq.symm)
    _ ≤ liminf (fun N ↦ ∫⁻ ω, F N ω ∂P) atTop := lintegral_liminf_le hF_meas
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hF_le)

/-- Optional stopping at a single stopping time: the expectation of an `ℝ≥0∞`-valued
supermartingale with finite initial expectation under a finite measure, at a stopping time with
values in `WithTop ℕ`, is at most its initial expectation. -/
theorem lintegral_stoppedValueLimsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (hτ : IsStoppingTime ℱ τ) :
    ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω, M 0 ω ∂P := by
  have h := hM.setLIntegral_stoppedValueLimsup_le hP h0 (σ := fun _ ↦ ((0 : ℕ) : WithTop ℕ))
    (isStoppingTime_natCast 0) hτ (fun _ ↦ by simp) MeasurableSet.univ
  rwa [stoppedValueLimsup_const, Measure.restrict_univ] at h

/-- The set integrals of the almost sure limit of an `ℝ≥0∞`-valued supermartingale with finite
initial expectation under a finite measure, over an `ℱ n`-measurable set, are at most those of
`M n`. -/
theorem setLIntegral_limsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {n : ℕ} (hs : MeasurableSet[ℱ n] s) :
    ∫⁻ ω in s, limsup (fun k ↦ M k ω) atTop ∂P ≤ ∫⁻ ω in s, M n ω ∂P := by
  have hσ : IsStoppingTime ℱ fun _ ↦ (n : WithTop ℕ) := isStoppingTime_natCast n
  have h := hM.setLIntegral_stoppedValueLimsup_le hP h0 (τ := fun _ ↦ ⊤) hσ (fun _ ↦ by simp)
    (fun _ ↦ le_top) (hσ.le_measurableSpace_of_const_le (fun _ ↦ (Nat.cast_withTop n).ge) s hs)
  rwa [stoppedValueLimsup_const, stoppedValueLimsup_top] at h

/-- The expectation of the almost sure limit of an `ℝ≥0∞`-valued supermartingale with finite
initial expectation under a finite measure is at most its initial expectation. -/
theorem lintegral_limsup_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∫⁻ ω, limsup (fun n ↦ M n ω) atTop ∂P ≤ ∫⁻ ω, M 0 ω ∂P := by
  simpa using hM.setLIntegral_limsup_le hP h0 (n := 0) MeasurableSet.univ

end IsENNSupermartingale

namespace IsTestSupermartingale

/-- A test supermartingale converges almost surely under every finite member of the null, so that
its `limsup` is its limit [RW, Fact 7.5]. -/
theorem ae_tendsto_limsup (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P] :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (limsup (fun n ↦ M n ω) atTop)) :=
  hM.toIsENNSupermartingale.ae_tendsto_limsup hP
    (hM.lintegral_zero_ne_top hP)

/-- The almost sure limit of a test supermartingale is almost surely finite under every finite
member of the null. -/
theorem ae_limsup_lt_top (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P] :
    ∀ᵐ ω ∂P, limsup (fun n ↦ M n ω) atTop < ∞ :=
  hM.toIsENNSupermartingale.ae_limsup_lt_top hP
    (hM.lintegral_zero_ne_top hP)

/-- The set integrals of the almost sure limit of a test supermartingale, over an `ℱ n`-measurable
set, are at most those of `M n`, under every finite member of the null. -/
theorem setLIntegral_limsup_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    {n : ℕ} (hs : MeasurableSet[ℱ n] s) :
    ∫⁻ ω in s, limsup (fun k ↦ M k ω) atTop ∂P ≤ ∫⁻ ω in s, M n ω ∂P :=
  hM.toIsENNSupermartingale.setLIntegral_limsup_le hP (hM.lintegral_zero_ne_top hP) hs

/-- The expectation of the almost sure limit of a test supermartingale is at most its initial
expectation, under every finite member of the null. -/
theorem lintegral_limsup_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P] :
    ∫⁻ ω, limsup (fun n ↦ M n ω) atTop ∂P ≤ ∫⁻ ω, M 0 ω ∂P :=
  hM.toIsENNSupermartingale.lintegral_limsup_le hP (hM.lintegral_zero_ne_top hP)

/-- The expectation of the almost sure limit of a test supermartingale is at most `1`, under every
finite member of the null. -/
theorem lintegral_limsup_le_one (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] : ∫⁻ ω, limsup (fun n ↦ M n ω) atTop ∂P ≤ 1 :=
  (hM.lintegral_limsup_le hP).trans (hM.lintegral_zero_le P hP)

/-- **Optional stopping for test supermartingales.** For stopping times `σ ≤ τ` with values in
`WithTop ℕ`, a set `s` measurable for the σ-algebra at `σ` and a finite member `P` of the null,
the set integral over `s` of a test supermartingale at `τ` is at most its set integral at `σ`
[RW, Fact 7.5]. -/
theorem setLIntegral_stoppedValueLimsup_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ)
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω in s, stoppedValueLimsup M σ ω ∂P :=
  hM.toIsENNSupermartingale.setLIntegral_stoppedValueLimsup_le hP
    (hM.lintegral_zero_ne_top hP) hσ hτ hστ hs

/-- The expectation of a test supermartingale at a stopping time with values in `WithTop ℕ` is at
most its initial expectation, under every finite member of the null. -/
theorem lintegral_stoppedValueLimsup_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ) :
    ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω, M 0 ω ∂P :=
  hM.toIsENNSupermartingale.lintegral_stoppedValueLimsup_le hP
    (hM.lintegral_zero_ne_top hP) hτ

/-- The expectation of a test supermartingale at a stopping time with values in `WithTop ℕ` is at
most `1`, under every finite member of the null. -/
theorem lintegral_stoppedValueLimsup_le_one (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ) : ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ 1 :=
  (hM.lintegral_stoppedValueLimsup_le hP hτ).trans (hM.lintegral_zero_le P hP)

/-- The value of a test supermartingale for a null of probability measures at a stopping time
with values in `WithTop ℕ` is an e-variable. -/
theorem isEVar_stoppedValueLimsup (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hM : IsTestSupermartingale M ℱ S) (hτ : IsStoppingTime ℱ τ) :
    IsEVar (stoppedValueLimsup M τ) S :=
  IsEVar.of_lintegral_le_one hS (measurable_stoppedValueLimsup hM.measurable hτ.measurable')
    fun P hP ↦ have := hS P hP; hM.lintegral_stoppedValueLimsup_le_one hP hτ

end IsTestSupermartingale

end ProbabilityTheory
