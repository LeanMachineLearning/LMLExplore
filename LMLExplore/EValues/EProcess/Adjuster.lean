/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.SequentialTest
import LMLExplore.Analysis.SumIntegralComparisons
import LMLExplore.EValues.TestSupermartingale.Finite

/-!
# Filtrations and adjusters

An e-process is valid at the stopping times of its filtration, and only those: averaging an
e-process for a filtration `ℱ` with one for a coarser filtration `𝒢 ≤ ℱ` need not give an
e-process for `ℱ`, since an e-process for `𝒢` need not be one for `ℱ`. Choe and Ramdas [CR26]
show how evidence moves to a finer filtration.

* **p-lifting** [CR26, Lemma 1, Theorem 1]. A bound on the probability of events adapted to `𝒢`,
  read at every stopping time of `𝒢`, is a bound on the probability of their union, which does not
  depend on the filtration (`MeasureTheory.forall_isStoppingTime_measure_le_iff_of_le`). So a
  p-process or a sequential test for `𝒢` is one for every finer filtration `ℱ`, at no cost
  (`ProbabilityTheory.IsPProcess.mono_filtration` and
  `ProbabilityTheory.IsSequentialTest.mono_filtration`, in `EValues/EProcess/SequentialTest`).
* **e-lifting** [CR26, Theorem 2]. An **adjuster** is a function `A : ℝ≥0∞ → ℝ≥0∞`, monotone on
  `[1, ∞]`, with `∫₁^∞ A x / x ^ 2 dx ≤ 1` [ShSVV11; DdRSSVV11]. The substitution `p = x⁻¹` makes
  `p ↦ A p⁻¹` a p-to-e calibrator, and conversely. For an e-process `E` for `𝒢`, the inverse of
  `max 1 (⨆ k ≤ n, E k)` is a p-process for `𝒢`, hence for `ℱ`, and the calibrator turns it into
  `A (max 1 (⨆ k ≤ n, E k))`: the adjusted running maximum is an e-process for `ℱ`. The case
  `𝒢 = ℱ` is the classical adjustment of the running maximum of a test supermartingale
  [ShSVV11, Theorem 4; DdRSSVV11, Theorem 1].
* **Only adjusters lift** [CR26, Theorem 3]. Conversely, a function monotone on `[1, ∞]` that
  turns the running maximum of every test supermartingale into a variable of expectation at most
  `1` is an adjuster. The test martingale on `Fin K` that multiplies its value by
  `(K - n) / (K - n - 1)` at time `n` until it falls to `0` has a running maximum whose adjusted
  expectation is an upper Riemann sum of `p ↦ A p⁻¹` on `[1 / K, 1]`; letting `K → ∞` bounds
  `∫₀¹ A p⁻¹ dp`. So adjusters are exactly the e-lifters.

## Main definitions

* `ProbabilityTheory.IsAdjuster A`: `A` is an adjuster.

## Main statements

* `ProbabilityTheory.isAdjuster_iff_isPToECalibrator`: adjusters and p-to-e calibrators
  correspond through `p = x⁻¹` [CR26, §2.4].
* `ProbabilityTheory.IsEProcess.isEProcess_comp_max_iSup`: e-lifting [CR26, Theorem 2].
* `ProbabilityTheory.IsTestSupermartingale.isEProcess_comp_max_iSup`,
  `ProbabilityTheory.IsTestSupermartingale.exists_isTestSupermartingale_ae_le_comp_max_iSup`: the
  adjusted running maximum of a test supermartingale is an e-process, dominated by a test
  supermartingale under each member of the null [ShSVV11, Theorem 4; DdRSSVV11, Theorem 1].
* `ProbabilityTheory.IsEProcess.lintegral_iSup_comp_max_le_one`: the supremum over time of an
  adjusted e-process has expectation at most `1` [RRLK, Lemma 3].
* `ProbabilityTheory.isAdjuster_of_forall_lintegral_le_one`,
  `ProbabilityTheory.isAdjuster_iff_forall_isEProcess`: only adjusters lift e-processes, and
  adjusters are exactly the e-lifters [CR26, Theorem 3].

## Implementation notes

Stopping times take values in `ℕ`, as in `ProbabilityTheory.IsEProcess` and
`ProbabilityTheory.IsPProcess`. Since an adjuster is only constrained on `[1, ∞]`, it is applied to
`max 1` of the running maximum; [CR26] instead sets the adjusted process to `1` at time `0`. The
converse and the characterization quantify over the probability spaces in `Type`, which contains
the finite spaces of the construction.

## References

* [CR26] Y. J. Choe and A. Ramdas, *Combining evidence across filtrations*, arXiv:2402.09698v5,
  to appear in J. R. Stat. Soc. Ser. B: Lemma 1, Theorems 1–3, §2.4.
* [DdRSSVV11] A. P. Dawid, S. de Rooij, G. Shafer, A. Shen, N. Vereshchagin and V. Vovk, *Insuring
  against loss of evidence in game-theoretic probability*, Statist. Probab. Lett. 81 (2011):
  Theorem 1.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemma 3.
* [ShSVV11] G. Shafer, A. Shen, N. Vereshchagin and V. Vovk, *Test martingales, Bayes factors and
  p-values*, Statist. Sci. 26 (2011), arXiv:0912.4269: Theorem 4.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {P : Measure Ω} {p E M : ℕ → Ω → ℝ≥0∞} {φ : ℕ → Ω → ℝ≥0∞} {α : ℝ≥0∞} {A : ℝ≥0∞ → ℝ≥0∞}

/-! ### Adjusters -/

/-- An **adjuster** [CR26, (11); ShSVV11; DdRSSVV11] is a function `A : ℝ≥0∞ → ℝ≥0∞`,
monotone on `[1, ∞]`, with `∫₁^∞ A x / x ^ 2 dx ≤ 1`. Its values below `1` play no role: an
adjuster is applied to `max 1` of the running maximum of an e-process. -/
structure IsAdjuster (A : ℝ≥0∞ → ℝ≥0∞) : Prop where
  monotoneOn : MonotoneOn A (Ici 1)
  lintegral_le_one : ∫⁻ x in Ioi (1 : ℝ), A (ENNReal.ofReal x) / ENNReal.ofReal (x ^ 2) ≤ 1

/-- **Adjusters and calibrators** [CR26, §2.4]. A function `A` is an adjuster exactly when
`p ↦ A p⁻¹`, on `[0, 1]` and zero on `(1, ∞]`, is a p-to-e calibrator: the change of variables
`p = x⁻¹` exchanges the two integral conditions. -/
theorem isAdjuster_iff_isPToECalibrator :
    IsAdjuster A ↔ IsPToECalibrator ((Iic 1).indicator fun p ↦ A p⁻¹) := by
  refine ⟨fun hA ↦ ⟨hA.monotoneOn.antitone_indicator_Iic_comp_inv,
    fun x hx ↦ indicator_of_notMem (not_le.2 hx) _,
    (setLIntegral_indicator_Iic_comp_inv A).trans_le hA.lintegral_le_one⟩, fun hf ↦
    ⟨fun x hx y hy hxy ↦ ?_,
      (setLIntegral_indicator_Iic_comp_inv A).symm.trans_le hf.lintegral_le_one⟩⟩
  have h := hf.antitone (ENNReal.inv_le_inv.2 hxy)
  rwa [indicator_of_mem (mem_Iic.2 (ENNReal.inv_le_one.2 hx)),
    indicator_of_mem (mem_Iic.2 (ENNReal.inv_le_one.2 hy)), inv_inv, inv_inv] at h

/-- A p-to-e calibrator `f` gives the adjuster `x ↦ f x⁻¹` [CR26, §2.4]. -/
theorem IsPToECalibrator.isAdjuster_comp_inv {f : ℝ≥0∞ → ℝ≥0∞} (hf : IsPToECalibrator f) :
    IsAdjuster fun x ↦ f x⁻¹ := by
  refine isAdjuster_iff_isPToECalibrator.2 ?_
  convert hf using 1
  ext p
  by_cases hp : p ≤ 1
  · simp [indicator_of_mem (mem_Iic.2 hp)]
  · simp [indicator_of_notMem (show p ∉ Iic 1 from hp), hf.eq_zero_of_one_lt p (not_le.1 hp)]

/-! ### Lifting e-processes -/

/-- The inverse of `max 1` of the running maximum of an e-process is a p-process: below the level
`1` its events are those of the p-process `(⨆ k ≤ n, E k)⁻¹`. -/
private lemma IsEProcess.isPProcess_inv_max_one_iSup (hS : ∀ P ∈ S, P univ ≤ 1)
    (hE : IsEProcess E ℱ S) : IsPProcess (fun n ω ↦ (max 1 (⨆ k ≤ n, E k ω))⁻¹) ℱ S := by
  have hp := hE.isPProcess_inv_iSup
  refine isPProcess_iff_measure_exists_le_le.2 ⟨fun n ↦ (measurable_const.max
    (Measurable.iSup fun k ↦ Measurable.iSup fun hk ↦
      (hE.adapted k).mono (ℱ.mono hk) le_rfl)).inv, fun P hP α ↦ ?_⟩
  rcases le_or_gt 1 α with hα | hα
  · exact (measure_mono (subset_univ _)).trans ((hS P hP).trans hα)
  refine (hp.measure_exists_le_le hP α).trans' (measure_mono fun ω ⟨n, hn⟩ ↦ ⟨n, ?_⟩)
  have h1 : 1 < max 1 (⨆ k ≤ n, E k ω) := ENNReal.inv_lt_one.1 (hn.trans_lt hα)
  rwa [max_eq_right (lt_max_iff.1 h1 |>.resolve_left (lt_irrefl 1)).le] at hn

/-- **e-lifting** [CR26, Theorem 2]. For an adjuster `A`, a null of measures of mass at most one
and filtrations `𝒢 ≤ ℱ`, the adjusted running maximum `A (max 1 (⨆ k ≤ n, E k))` of an e-process `E`
for the coarser filtration `𝒢` is an e-process for the finer filtration `ℱ`. -/
theorem IsEProcess.isEProcess_comp_max_iSup (hA : IsAdjuster A)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hE : IsEProcess E 𝒢 S) (h𝒢ℱ : 𝒢 ≤ ℱ) :
    IsEProcess (fun n ω ↦ A (max 1 (⨆ k ≤ n, E k ω))) ℱ S := by
  -- the inverse of `max 1 (⨆ k ≤ n, E k)` is a p-process for `𝒢`, hence for `ℱ`, and the
  -- calibrator of `A` turns it into the adjusted running maximum
  have h := ((hE.isPProcess_inv_max_one_iSup hS).mono_filtration h𝒢ℱ).isEProcess_comp
    (isAdjuster_iff_isPToECalibrator.1 hA) hS
  have h_eq : (fun n ω ↦ A (max 1 (⨆ k ≤ n, E k ω))) =
      fun n ω ↦ (Iic 1).indicator (fun p ↦ A p⁻¹) (max 1 (⨆ k ≤ n, E k ω))⁻¹ := by
    ext n ω
    rw [indicator_of_mem (mem_Iic.2 (ENNReal.inv_le_one.2 (le_max_left _ _))), inv_inv]
  rwa [h_eq]

/-- **Adjusted suprema of e-processes** [RRLK, Lemma 3]. For an adjuster `A` and a null of
measures of mass at most one, the supremum over time `⨆ n, A (max 1 (E n))` of an e-process `E`
adjusted by `A` has expectation at most `1` under every member of the null, although the supremum
of `E` itself need not (`ProbabilityTheory.exists_isEProcess_one_lt_lintegral_iSup`). -/
theorem IsEProcess.lintegral_iSup_comp_max_le_one (hA : IsAdjuster A)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hE : IsEProcess E ℱ S) (hP : P ∈ S) :
    ∫⁻ ω, ⨆ n, A (max 1 (E n ω)) ∂P ≤ 1 := by
  -- the adjusted running maxima are e-processes, and they increase to the adjusted supremum
  have h := hE.isEProcess_comp_max_iSup hA hS le_rfl
  have hA_mono : Monotone fun x ↦ A (max 1 x) := fun x y hxy ↦ hA.monotoneOn
    (mem_Ici.2 (le_max_left _ _)) (mem_Ici.2 (le_max_left _ _)) (max_le_max_left _ hxy)
  calc ∫⁻ ω, ⨆ n, A (max 1 (E n ω)) ∂P
      ≤ ∫⁻ ω, ⨆ n, A (max 1 (⨆ k ≤ n, E k ω)) ∂P :=
        lintegral_mono fun ω ↦ iSup_mono fun n ↦ hA_mono (le_iSup₂_of_le n le_rfl le_rfl)
    _ = ⨆ n, ∫⁻ ω, A (max 1 (⨆ k ≤ n, E k ω)) ∂P :=
        lintegral_iSup h.measurable fun m n hmn ω ↦
          hA_mono (biSup_mono fun k hk ↦ hk.trans hmn)
    _ ≤ 1 := iSup_le fun n ↦ (h.isEVar n).lintegral_le_one hP

/-- **Adjusting the running maximum of a test supermartingale** [ShSVV11, Theorem 4;
DdRSSVV11, Theorem 1]: for an adjuster `A` and a null of measures of mass at most one, the
adjusted running maximum `A (max 1 (⨆ k ≤ n, M k))` of a test supermartingale is an e-process.
This is the case `𝒢 = ℱ` of e-lifting. -/
theorem IsTestSupermartingale.isEProcess_comp_max_iSup (hA : IsAdjuster A)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hM : IsTestSupermartingale M ℱ S) :
    IsEProcess (fun n ω ↦ A (max 1 (⨆ k ≤ n, M k ω))) ℱ S :=
  (hM.isEProcess hS).isEProcess_comp_max_iSup hA hS le_rfl

/-- **The game-theoretic form of adjusters** [CR26, (26); ShSVV11, Theorem 4]: for an adjuster
`A`, a test supermartingale `M` for a null `S` and a probability measure `P ∈ S`, the adjusted
running maximum `A (max 1 (⨆ k ≤ n, M k))` is dominated, `P`-almost surely at every time, by a
test supermartingale for `P`. -/
theorem IsTestSupermartingale.exists_isTestSupermartingale_ae_le_comp_max_iSup
    (hA : IsAdjuster A) (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsProbabilityMeasure P] :
    ∃ M', IsTestSupermartingale M' ℱ {P} ∧
      ∀ n, (fun ω ↦ A (max 1 (⨆ k ≤ n, M k ω))) ≤ᵐ[P] M' n :=
  ((hM.anti_set (singleton_subset_iff.2 hP)).isEProcess_comp_max_iSup hA
    (by simp)).exists_isTestSupermartingale_ae_le (mem_singleton P)

/-! ### The converse: only adjusters lift e-processes -/

/-- **A test martingale with a prescribed running maximum.** On `Fin K` with the uniform law,
the Doob martingale of `K` times the indicator of the last point, for the filtration that reveals
at time `n` the outcome `j` if `j < n` and only that `j ≥ n` otherwise, is a test supermartingale
whose value at the time `j` on the outcome `j` is at least `((K - j) / K)⁻¹`: a discrete form of
`1 / U` for `U` uniform on `[0, 1]`. -/
private lemma exists_isTestSupermartingale_fin {K : ℕ} (hK : 0 < K) :
    ∃ (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (Fin K))) (M : ℕ → Fin K → ℝ≥0∞),
      IsTestSupermartingale M ℱ {∑ j : Fin K, (K : ℝ≥0∞)⁻¹ • Measure.dirac j} ∧
      ∀ j : Fin K, (((K - j : ℕ) : ℝ≥0∞) / K)⁻¹ ≤ M j j := by
  classical
  have hK0 : (K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hK.ne'
  set last : Fin K := ⟨K - 1, by omega⟩
  set info : ℕ → Fin K → ℕ := fun n j ↦ min (j : ℕ) n
  have hinfo : ∀ t j j', info (t + 1) j = info (t + 1) j' → info t j = info t j' := by
    intro t j j' h
    simp only [info] at h ⊢
    omega
  set Z : Fin K → ℝ≥0∞ := fun j ↦ if j = last then (K : ℝ≥0∞) else 0
  have hZ : ∑ j, (K : ℝ≥0∞)⁻¹ * Z j ≤ 1 := by
    simp [Z, ENNReal.inv_mul_cancel hK0 (ENNReal.natCast_ne_top K)]
  refine ⟨_, _, (isTestMartingale_fiberAvg (w := fun _ ↦ (K : ℝ≥0∞)⁻¹)
    (fun _ ↦ ENNReal.inv_ne_top.2 hK0) info hinfo Z hZ).isTestSupermartingale, fun j ↦ ?_⟩
  -- the fiber of `j` at time `j` is the set of outcomes `j' ≥ j`
  have h_fiber (j' : Fin K) : info j j' = info j j ↔ j ≤ j' := by
    simp only [info, Fin.le_def]
    omega
  have h_num : (∑ j', if info j j' = info j j then (K : ℝ≥0∞)⁻¹ * Z j' else 0) = 1 := by
    have hl : info j last = info j j := (h_fiber last).2 (Fin.le_def.2 (by simp only [last]; omega))
    rw [Finset.sum_eq_single last (fun j' _ hj' ↦ by simp [Z, hj']) (by simp)]
    simp [hl, Z, ENNReal.inv_mul_cancel hK0 (ENNReal.natCast_ne_top K)]
  have h_den : (∑ j', if info j j' = info j j then (K : ℝ≥0∞)⁻¹ else 0) =
      ((K - j : ℕ) : ℝ≥0∞) / K := by
    simp_rw [h_fiber]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    congr 2
    rw [show Finset.univ.filter (fun j' : Fin K ↦ j ≤ j') = Finset.Ici j by ext; simp,
      Fin.card_Ici]
  rw [fiberAvg_def, h_num, h_den, one_div]

/-- **Only adjusters lift e-processes** [CR26, Theorem 3]. A function `A`, monotone on `[1, ∞]`,
such that the adjusted running maximum `A (max 1 (⨆ k ≤ n, M k))` of every test supermartingale
`M` for a probability measure has expectation at most `1` at every time, is an adjuster. -/
theorem isAdjuster_of_forall_lintegral_le_one (hA : MonotoneOn A (Ici 1))
    (h : ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (ℱ : Filtration ℕ mΩ) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ M : ℕ → Ω → ℝ≥0∞, IsTestSupermartingale M ℱ {P} →
        ∀ n, ∫⁻ ω, A (max 1 (⨆ k ≤ n, M k ω)) ∂P ≤ 1) :
    IsAdjuster A := by
  have hC := hA.antitone_indicator_Iic_comp_inv
  refine isAdjuster_iff_isPToECalibrator.2 ⟨hC, fun x hx ↦ indicator_of_notMem (not_le.2 hx) _, ?_⟩
  -- the integral over `(0, 1]` is the supremum of the integrals over `(1 / (k + 1), 1]`
  have h_union : Ioc (0 : ℝ) 1 = ⋃ k : ℕ, Ioc (((k + 1 : ℕ) : ℝ))⁻¹ 1 := by
    ext u
    simp only [mem_Ioc, mem_iUnion]
    refine ⟨fun ⟨hu0, hu1⟩ ↦ ?_, fun ⟨k, hk, hu1⟩ ↦ ⟨(by positivity : (0 : ℝ) < _).trans hk, hu1⟩⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hu0
    exact ⟨k, by simpa using hk, hu1⟩
  have h_dir : Directed (· ⊆ ·) fun k : ℕ ↦ Ioc (((k + 1 : ℕ) : ℝ))⁻¹ 1 :=
    Monotone.directed_le fun a b hab ↦ Ioc_subset_Ioc_left
      (inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hab))
  rw [← setLIntegral_congr Ioc_ae_eq_Icc, h_union, setLIntegral_iUnion_of_directed _ h_dir]
  refine iSup_le fun k ↦ ?_
  -- the adjusted running maximum of the test martingale of `exists_isTestSupermartingale_fin` is
  -- an upper Riemann sum of `p ↦ A p⁻¹` on `[1 / (k + 1), 1]`
  obtain ⟨ℱ, M, hM, hMj⟩ := exists_isTestSupermartingale_fin (K := k + 1) k.succ_pos
  have hP : IsProbabilityMeasure (∑ j : Fin (k + 1), ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac j) :=
    ⟨by simpa using ENNReal.mul_inv_cancel (a := (k : ℝ≥0∞) + 1) (by positivity) (by simp)⟩
  refine (Antitone.setLIntegral_Ioc_le_sum hC k.succ_pos).trans (le_trans ?_ (h _ _ ℱ _ hP M hM k))
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  gcongr
  have hj : ((k + 1 - j : ℕ) : ℝ≥0∞) / (k + 1 : ℕ) ≤ 1 :=
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.sub_le _ _)
  rw [indicator_of_mem (mem_Iic.2 hj)]
  exact hA (mem_Ici.2 (ENNReal.one_le_inv.2 hj)) (mem_Ici.2 (le_max_left _ _))
    ((hMj j).trans ((le_iSup₂_of_le (f := fun i (_ : i ≤ k) ↦ M i j) (j : ℕ)
      (Nat.lt_succ_iff.1 j.2) le_rfl).trans (le_max_right _ _)))

/-- **The characterization of adjusters as e-lifters** [CR26, Theorem 3]. A function `A`, monotone
on `[1, ∞]`, is an adjuster exactly when, for every pair of filtrations `𝒢 ≤ ℱ` and every null of
probability measures, it turns the running maximum `max 1 (⨆ k ≤ n, E k)` of every e-process `E`
for `𝒢` into an e-process for `ℱ`. -/
theorem isAdjuster_iff_forall_isEProcess :
    IsAdjuster A ↔ MonotoneOn A (Ici 1) ∧
      ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (𝒢 ℱ : Filtration ℕ mΩ), 𝒢 ≤ ℱ →
        ∀ S : Set (Measure Ω), (∀ P ∈ S, IsProbabilityMeasure P) →
          ∀ E : ℕ → Ω → ℝ≥0∞, IsEProcess E 𝒢 S →
            IsEProcess (fun n ω ↦ A (max 1 (⨆ k ≤ n, E k ω))) ℱ S := by
  refine ⟨fun hA ↦ ⟨hA.monotoneOn, fun Ω mΩ 𝒢 ℱ h𝒢ℱ S hS E hE ↦
    hE.isEProcess_comp_max_iSup hA (fun P hP ↦ (hS P hP).measure_univ.le) h𝒢ℱ⟩, fun ⟨hA, h⟩ ↦
    isAdjuster_of_forall_lintegral_le_one hA fun Ω mΩ ℱ P hP M hM n ↦ ?_⟩
  have hS : ∀ Q ∈ ({P} : Set (Measure Ω)), IsProbabilityMeasure Q := by simpa using hP
  exact ((h Ω mΩ ℱ ℱ le_rfl {P} hS M
    (hM.isEProcess fun Q hQ ↦ (hS Q hQ).measure_univ.le)).isEVar n).lintegral_le_one
    (mem_singleton P)

end ProbabilityTheory
