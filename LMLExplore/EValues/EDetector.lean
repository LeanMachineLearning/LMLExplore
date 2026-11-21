/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Probability.Martingale.OptionalStopping
public import LMLExplore.MeasureTheory.Integral.Lebesgue.ENat
public import Mathlib.Algebra.Order.Ring.Finset

/-!
# E-detectors and sequential change detection

In sequential change detection, observations follow a pre-change law until an unknown time and
another law afterwards, and a detection rule is a stopping time `τ` at which an alarm is raised.
Under a pre-change law the alarm is false, and the expected time `∫⁻ τ` to a false alarm (the
average run length) should be large. An **e-detector** for a pre-change null `S` and a filtration
`ℱ` is an adapted `ℝ≥0∞`-valued process `M` whose expectation at every stopping time `τ` is at
most the expected value of `τ` itself, under every member of the null [SRR24, Definition 2.2]:
where an e-process has at most one unit of expected evidence in total, an e-detector gains at
most one unit per observation. The first time an e-detector reaches `α⁻¹` has expected value at
least `α⁻¹` under every pre-change law [SRR24, Theorem 2.4]: thresholding an e-detector at
`α⁻¹` controls the average run length at `α⁻¹`, as thresholding an e-process controls the
probability of a false rejection at `α`.

E-detectors are built from **e-processes from a time `j`** [SRR24, Definition 2.5], the
e-processes that test whether the observations from time `j` on are explained by the null: their
value at every stopping time `τ ≥ j` is a conditional e-variable given `ℱ j`. The
**Shiryaev–Roberts** e-detector `n ↦ ∑ j < n, Λ j n` and the **CUSUM** e-detector
`n ↦ max_{j < n} Λ j n` of a family of e-processes `Λ j` from time `j` are e-detectors
[SRR24, Definition 2.6]: the term of index `j` bets on a change after the first `j` observations.
For `ℱ (k + 1)`-measurable conditional e-variables `F k` given `ℱ k`, for instance the likelihood
ratios of a post-change alternative to a pre-change law at each observation, the products
`∏ k ∈ [j, n), F k` are e-processes from time `j`, and their Shiryaev–Roberts and CUSUM
e-detectors are the classical procedures, with the recursions `R (n + 1) = (R n + 1) * F n` and
`W (n + 1) = max (W n) 1 * F n`.

The null is an arbitrary set of measures, with no dominating measure, and the filtration is
arbitrary. The definitions ask their bounds at the stopping times that are finite everywhere; the
bound of an e-detector extends to every stopping time, with the value `stoppedValueLimsup` at
infinity, and the alarm time at `α⁻¹` is such a stopping time.

## Main definitions

* `ProbabilityTheory.IsEDetector M ℱ S`: `M` is an e-detector for the null `S` and the filtration
  `ℱ`.
* `ProbabilityTheory.IsEProcessFrom E j ℱ S`: `E` is an e-process from time `j`.
* `ProbabilityTheory.shiryaevRoberts Λ`, `ProbabilityTheory.cusum Λ`: the Shiryaev–Roberts and
  CUSUM processes of a family `Λ` of processes indexed by their starting times.

## Main statements

* `ProbabilityTheory.IsEDetector.lintegral_stoppedValueLimsup_le`: the bound of an e-detector at
  every stopping time with values in `WithTop ℕ`.
* `ProbabilityTheory.IsEDetector.inv_mul_le_lintegral_hittingAfter`,
  `ProbabilityTheory.IsEDetector.inv_le_lintegral_hittingAfter`: the first time an e-detector
  reaches `α⁻¹` has expectation at least `α⁻¹` under every pre-change probability measure
  [SRR24, Theorem 2.4].
* `ProbabilityTheory.convex_isEDetector`: the e-detectors for a null form a convex set, the case
  of finite mixtures of [SRR24, Proposition 2.3].
* `ProbabilityTheory.IsEProcessFrom.isEProcess`: an e-process from time `0` is an e-process.
* `ProbabilityTheory.IsENNSupermartingale.isEProcessFrom`,
  `ProbabilityTheory.isEProcessFrom_prod_Ico`: a supermartingale under every member of the null
  whose value at time `j` is a conditional e-variable given `ℱ j` is an e-process from time `j`;
  in particular so are the products of conditional e-variables from time `j` on.
* `ProbabilityTheory.isEDetector_shiryaevRoberts`, `ProbabilityTheory.isEDetector_cusum`: the
  Shiryaev–Roberts and CUSUM processes of e-processes from each time are e-detectors
  [SRR24, Definition 2.6].
* `ProbabilityTheory.shiryaevRoberts_prod_Ico_succ`, `ProbabilityTheory.cusum_prod_Ico_succ`: the
  recursions of the Shiryaev–Roberts and CUSUM processes of products.

## Implementation notes

[SRR24, Definition 2.5] asks an e-process from time `j` (their `e_{j+1}`-process, with
observations indexed from `1`) to be `1` up to time `j` and to have conditional expectation at
most `1` given `ℱ j` at every stopping time. Only its values from time `j` on enter the
Shiryaev–Roberts and CUSUM processes, so `ProbabilityTheory.IsEProcessFrom` constrains only the
stopping times `τ ≥ j`, and its value at time `j` need not be `1`.

## References

* [SRR24] J. Shin, A. Ramdas and A. Rinaldo, *E-detectors: a nonparametric framework for
  sequential change detection*, New England J. Statist. Data Sci. 2 (2024), arXiv:2203.03532v4,
  §2.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {M N E F : ℕ → Ω → ℝ≥0∞} {Λ : ℕ → ℕ → Ω → ℝ≥0∞} {j : ℕ}

/-! ### E-detectors -/

/-- `M : ℕ → Ω → ℝ≥0∞` is an **e-detector** for the pre-change null `S` and the filtration `ℱ`: it
is adapted and, for every stopping time `τ` that is finite everywhere and every `P ∈ S`, its
expectation at `τ` is at most the expectation of `τ` [SRR24, Definition 2.2]. -/
structure IsEDetector (M : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Prop where
  adapted : Adapted ℱ M
  lintegral_le : ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → (∀ ω, τ ω ≠ ⊤) →
    ∀ P ∈ S, ∫⁻ ω, stoppedValue M τ ω ∂P ≤ ∫⁻ ω, ENat.toENNReal (τ ω) ∂P

namespace IsEDetector

/-- Each value of an e-detector is measurable. -/
theorem measurable (hM : IsEDetector M ℱ S) (n : ℕ) : Measurable (M n) :=
  hM.adapted.measurable

/-- An e-detector for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hM : IsEDetector M ℱ T) : IsEDetector M ℱ S :=
  ⟨hM.adapted, fun τ hτ hτ_top P hP ↦ hM.lintegral_le τ hτ hτ_top P (hST hP)⟩

/-- **Domination.** An adapted process quasi-surely at most an e-detector at every time is an
e-detector. -/
theorem mono_ae (hM : IsEDetector M ℱ S) (hN : Adapted ℱ N)
    (hNM : ∀ n, N n ≤ᶠ[quasiSure S] M n) : IsEDetector N ℱ S := by
  refine ⟨hN, fun τ hτ hτ_top P hP ↦
    (lintegral_mono_ae ?_).trans (hM.lintegral_le τ hτ hτ_top P hP)⟩
  filter_upwards [ae_all_iff.2 fun n ↦ ae_of_eventually_quasiSure (hNM n) hP] with ω hω
    using hω _

/-- **Domination.** An adapted process that is at most an e-detector is an e-detector. -/
theorem mono (hM : IsEDetector M ℱ S) (hN : Adapted ℱ N) (hNM : N ≤ M) : IsEDetector N ℱ S :=
  hM.mono_ae hN fun n ↦ .of_forall (hNM n)

/-- An e-detector vanishes at time `0`, almost surely under every member of the null. -/
theorem apply_zero_ae_eq_zero (hM : IsEDetector M ℱ S) (hP : P ∈ S) : M 0 =ᵐ[P] 0 := by
  -- `ℕ∞` is by definition `WithTop ℕ`, so the time `((0 : ℕ) : WithTop ℕ)` is `(0 : ℕ∞)`
  have h : ∫⁻ ω, stoppedValue M (fun _ ↦ ((0 : ℕ) : WithTop ℕ)) ω ∂P ≤
      ∫⁻ _, ENat.toENNReal (0 : ℕ∞) ∂P :=
    hM.lintegral_le _ (isStoppingTime_natCast 0) (fun _ ↦ WithTop.natCast_ne_top 0) P hP
  rw [stoppedValue_natCast, ENat.toENNReal_zero, lintegral_zero, nonpos_iff_eq_zero] at h
  exact (lintegral_eq_zero_iff (hM.measurable 0)).1 h

/-- The bound of an e-detector at every stopping time `τ` with values in `WithTop ℕ`, with the value
`stoppedValueLimsup M τ` where `τ` is infinite: the expectation of `M` at `τ` is at most the
expectation of `τ`. -/
theorem lintegral_stoppedValueLimsup_le (hM : IsEDetector M ℱ S) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (hP : P ∈ S) :
    ∫⁻ ω, stoppedValueLimsup M τ ω ∂P ≤ ∫⁻ ω, ENat.toENNReal (τ ω) ∂P := by
  by_cases htop : P {ω | τ ω = ⊤} = 0
  · -- `τ` is almost surely finite: the bound at the truncations `min τ N`, and Fatou's lemma
    have hN (N : ℕ) : ∫⁻ ω, stoppedValue M (fun ω ↦ min (τ ω) N) ω ∂P ≤
        ∫⁻ ω, ENat.toENNReal (τ ω) ∂P :=
      (hM.lintegral_le _ (hτ.min_natCast N)
        (fun ω ↦ WithTop.ne_top_of_le_natCast (min_le_right _ _)) P hP).trans
        (lintegral_mono fun ω ↦ ENat.toENNReal_le.2 (min_le_left _ _))
    refine lintegral_le_of_tendsto_of_eventually_le (l := atTop)
      (f := fun (N : ℕ) ↦ stoppedValue M (fun ω ↦ min (τ ω) N))
      (fun N ↦ (measurable_stoppedValue_of_countable hM.measurable
        (hτ.min_natCast N).measurable').aemeasurable) ?_ (.of_forall hN)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 htop] with ω hω
    have hk : ((τ ω).untopA : WithTop ℕ) = τ ω := WithTop.natCast_untopA hω
    rw [stoppedValueLimsup_of_eq_natCast hk.symm]
    refine tendsto_const_nhds.congr' ?_
    -- from `N ≥ τ ω` on, the truncation `min τ N` is `τ`
    filter_upwards [eventually_ge_atTop (τ ω).untopA] with N hkN
    rw [stoppedValue, min_eq_left (by rw [← hk]; exact Nat.cast_le.2 hkN)]
  · -- `τ` is infinite with positive probability, so its expectation is infinite
    rw [lintegral_toENNReal_eq_top_of_measure_ne_zero hτ.measurable_enat.aemeasurable htop]
    exact le_top

/-- **Average run length** [SRR24, Theorem 2.4]. The first time `hittingAfter M (Ici α⁻¹) 0` at
which an e-detector reaches `α⁻¹` has expectation at least `α⁻¹ * P univ` under every member `P`
of the null, at every level `α`. [SRR24] searches from time `1`; since an e-detector vanishes at
time `0` almost surely (`ProbabilityTheory.IsEDetector.apply_zero_ae_eq_zero`), this gives the
same time almost surely for `α ≠ ∞`. -/
theorem inv_mul_le_lintegral_hittingAfter (hM : IsEDetector M ℱ S) (hP : P ∈ S) (α : ℝ≥0∞) :
    α⁻¹ * P univ ≤ ∫⁻ ω, ENat.toENNReal (hittingAfter M (Ici α⁻¹) 0 ω) ∂P := by
  set τ := hittingAfter M (Ici α⁻¹) 0
  have hτ : IsStoppingTime ℱ τ := hM.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  by_cases htop : P {ω | τ ω = ⊤} = 0
  · -- almost surely, the alarm is raised and the process is at least `α⁻¹` at the alarm time
    refine le_trans ?_ (hM.lintegral_stoppedValueLimsup_le hτ hP)
    rw [← lintegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 htop] with ω hω
    rw [stoppedValueLimsup_eq_stoppedValue hω]
    exact hittingAfter_mem_set_of_ne_top hω
  · -- the alarm is never raised with positive probability, so the expected alarm time is infinite
    rw [lintegral_toENNReal_eq_top_of_measure_ne_zero hτ.measurable_enat.aemeasurable htop]
    exact le_top

/-- **Average run length** [SRR24, Theorem 2.4]. The first time at which an e-detector reaches
`α⁻¹` has expectation at least `α⁻¹` under every pre-change probability measure. -/
theorem inv_le_lintegral_hittingAfter (hM : IsEDetector M ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (α : ℝ≥0∞) :
    α⁻¹ ≤ ∫⁻ ω, ENat.toENNReal (hittingAfter M (Ici α⁻¹) 0 ω) ∂P := by
  simpa using hM.inv_mul_le_lintegral_hittingAfter hP α

end IsEDetector

/-- The e-detectors for a null form a convex set: a convex combination `a • M + b • N`, with
`a + b = 1`, of two e-detectors is an e-detector. This is the case of finite mixtures of
[SRR24, Proposition 2.3]. -/
theorem convex_isEDetector (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Convex ℝ≥0∞ {M : ℕ → Ω → ℝ≥0∞ | IsEDetector M ℱ S} := by
  intro M hM N hN a b _ _ hab
  refine ⟨fun n ↦ ((hM.adapted n).const_smul a).add ((hN.adapted n).const_smul b),
    fun τ hτ hτ_top P hP ↦ ?_⟩
  have hMτ := measurable_stoppedValue_of_countable hM.measurable hτ.measurable'
  have hNτ := measurable_stoppedValue_of_countable hN.measurable hτ.measurable'
  -- the stopped value of `a • M + b • N` is `a • stoppedValue M τ + b • stoppedValue N τ`, by
  -- definition of `stoppedValue`
  have h_eq : stoppedValue (a • M + b • N) τ =
      fun ω ↦ a * stoppedValue M τ ω + b * stoppedValue N τ ω := rfl
  rw [h_eq, lintegral_add_left (hMτ.const_mul a), lintegral_const_mul a hMτ,
    lintegral_const_mul b hNτ]
  calc a * ∫⁻ ω, stoppedValue M τ ω ∂P + b * ∫⁻ ω, stoppedValue N τ ω ∂P
      ≤ a * ∫⁻ ω, ENat.toENNReal (τ ω) ∂P + b * ∫⁻ ω, ENat.toENNReal (τ ω) ∂P := by
        gcongr a * ?_ + b * ?_
        exacts [hM.lintegral_le τ hτ hτ_top P hP, hN.lintegral_le τ hτ hτ_top P hP]
    _ = ∫⁻ ω, ENat.toENNReal (τ ω) ∂P := by rw [← add_mul, hab, one_mul]

/-! ### E-processes from a time -/

/-- `E : ℕ → Ω → ℝ≥0∞` is an **e-process from time `j`** for the null `S` and the filtration `ℱ`:
it is adapted and, for every stopping time `τ ≥ j` that is finite everywhere, its value
`stoppedValue E τ` at `τ` is a conditional e-variable given `ℱ j` [SRR24, Definition 2.5]. -/
structure IsEProcessFrom (E : ℕ → Ω → ℝ≥0∞) (j : ℕ) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ E
  isCondEVar_stoppedValue : ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → (∀ ω, τ ω ≠ ⊤) →
    (∀ ω, (j : WithTop ℕ) ≤ τ ω) → IsCondEVar (stoppedValue E τ) (ℱ j) S

namespace IsEProcessFrom

/-- Each value of an e-process from a time is measurable. -/
theorem measurable (hE : IsEProcessFrom E j ℱ S) (n : ℕ) : Measurable (E n) :=
  hE.adapted.measurable

/-- An e-process from time `j` has set integral at most `P s` at every stopping time `τ` that is
finite everywhere, over every `ℱ j`-measurable set `s` on which `j ≤ τ`. -/
theorem setLIntegral_le (hE : IsEProcessFrom E j ℱ S) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) (hP : P ∈ S) {s : Set Ω}
    (hs : MeasurableSet[ℱ j] s) (hsτ : s ⊆ {ω | (j : WithTop ℕ) ≤ τ ω}) :
    ∫⁻ ω in s, stoppedValue E τ ω ∂P ≤ P s := by
  -- on `s`, `τ` agrees with the stopping time `max τ j ≥ j`
  have hτj : IsStoppingTime ℱ fun ω ↦ max (τ ω) j := hτ.max (isStoppingTime_natCast j)
  have hτj_top (ω : Ω) : max (τ ω) j ≠ ⊤ := max_ne_top (hτ_top ω) (WithTop.natCast_ne_top j)
  refine le_of_eq_of_le (setLIntegral_congr_fun (ℱ.le j _ hs) fun ω hω ↦ ?_)
    ((hE.isCondEVar_stoppedValue _ hτj hτj_top fun _ ↦ le_max_right _ _).setLIntegral_le P hP s
      hs)
  rw [stoppedValue, stoppedValue, max_eq_left (hsτ hω)]

/-- An e-process from time `j` for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hE : IsEProcessFrom E j ℱ T) : IsEProcessFrom E j ℱ S :=
  ⟨hE.adapted, fun τ hτ hτ_top hjτ ↦ (hE.isCondEVar_stoppedValue τ hτ hτ_top hjτ).anti_set hST⟩

/-- **Domination.** An adapted process quasi-surely at most an e-process from time `j` at every
time is an e-process from time `j`. -/
theorem mono_ae (hE : IsEProcessFrom E j ℱ S) (hF : Adapted ℱ F)
    (hFE : ∀ n, F n ≤ᶠ[quasiSure S] E n) : IsEProcessFrom F j ℱ S := by
  refine ⟨hF, fun τ hτ hτ_top hjτ ↦ ⟨measurable_stoppedValue_of_countable
    (fun _ ↦ hF.measurable) hτ.measurable', fun P hP s hs ↦ ?_⟩⟩
  refine (lintegral_mono_ae (ae_restrict_of_ae ?_)).trans
    ((hE.isCondEVar_stoppedValue τ hτ hτ_top hjτ).setLIntegral_le P hP s hs)
  filter_upwards [ae_all_iff.2 fun n ↦ ae_of_eventually_quasiSure (hFE n) hP] with ω hω
    using hω _

/-- **Domination.** An adapted process that is at most an e-process from time `j` is an e-process
from time `j`. -/
theorem mono (hE : IsEProcessFrom E j ℱ S) (hF : Adapted ℱ F) (hFE : F ≤ E) :
    IsEProcessFrom F j ℱ S :=
  hE.mono_ae hF fun n ↦ .of_forall (hFE n)

/-- An e-process from time `0`, for a null of measures of mass at most `1`, is an e-process. -/
theorem isEProcess (hS : ∀ P ∈ S, P univ ≤ 1) (hE : IsEProcessFrom E 0 ℱ S) :
    IsEProcess E ℱ S :=
  .of_lintegral_le_one hE.adapted fun τ hτ N hτN P hP ↦ by
    simpa using (hE.setLIntegral_le hτ
      (fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)) hP MeasurableSet.univ
      fun ω _ ↦ by simp).trans (hS P hP)

end IsEProcessFrom

/-- A supermartingale under every member of the null whose value at time `j` is a conditional
e-variable given `ℱ j` is an e-process from time `j`. -/
theorem IsENNSupermartingale.isEProcessFrom (hM : IsENNSupermartingale M ℱ S)
    (hj : IsCondEVar (M j) (ℱ j) S) : IsEProcessFrom M j ℱ S :=
  ⟨hM.adapted, fun _ hτ hτ_top hjτ ↦ ⟨measurable_stoppedValue_of_countable
    (fun _ ↦ hM.adapted.measurable) hτ.measurable', fun P hP _ hs ↦
    (hM.setLIntegral_stoppedValue_le hP hτ hτ_top hjτ hs).trans (hj.setLIntegral_le P hP _ hs)⟩⟩

/-- **Products from a time.** For factors `F k`, `k ≥ j`, that are `ℱ (k + 1)`-measurable
conditional e-variables given `ℱ k`, for instance likelihood ratios of the observations, the
products `n ↦ ∏ k ∈ [j, n), F k` form an e-process from time `j`. -/
theorem isEProcessFrom_prod_Ico (j : ℕ) (hF_meas : ∀ k, j ≤ k → Measurable[ℱ (k + 1)] (F k))
    (hF : ∀ k, j ≤ k → IsCondEVar (F k) (ℱ k) S) :
    IsEProcessFrom (fun n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) j ℱ S := by
  have hadapted : Adapted ℱ fun n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω := fun n ↦
    Finset.measurable_fun_prod _ fun k hk ↦
      (hF_meas k (Finset.mem_Ico.1 hk).1).mono (ℱ.mono (Finset.mem_Ico.1 hk).2) le_rfl
  -- each step from `n ≥ j` multiplies the `ℱ n`-measurable product by the factor `F n`
  have hM : IsENNSupermartingale (fun n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) ℱ S := by
    refine ⟨hadapted, fun P hP n s hs ↦ ?_⟩
    by_cases hjn : j ≤ n
    · simp_rw [Finset.prod_Ico_succ_top hjn]
      exact (hF n hjn).setLIntegral_mul_le (ℱ.le n) hP (hadapted n) hs
    · rw [Finset.Ico_eq_empty_of_le (by omega : n + 1 ≤ j),
        Finset.Ico_eq_empty_of_le (by omega : n ≤ j)]
  refine hM.isEProcessFrom ?_
  simp only [Finset.Ico_self, Finset.prod_empty]
  exact isCondEVar_one

/-! ### The Shiryaev–Roberts and CUSUM e-detectors -/

/-- The **Shiryaev–Roberts** process `n ↦ ∑ j < n, Λ j n` of a family of processes `Λ j` indexed
by their starting times: at time `n`, the sum over the `n` possible change times before `n`
[SRR24, Definition 2.6]. -/
noncomputable def shiryaevRoberts (Λ : ℕ → ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range n, Λ j n ω

/-- The **CUSUM** process `n ↦ max_{j < n} Λ j n` of a family of processes `Λ j` indexed by their
starting times, `0` at time `0` [SRR24, Definition 2.6]. -/
noncomputable def cusum (Λ : ℕ → ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (Finset.range n).sup fun j ↦ Λ j n ω

/-- The value of the Shiryaev–Roberts process at time `n`. -/
theorem shiryaevRoberts_apply (Λ : ℕ → ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    shiryaevRoberts Λ n ω = ∑ j ∈ Finset.range n, Λ j n ω := by
  rw [shiryaevRoberts]

/-- The value of the CUSUM process at time `n`. -/
theorem cusum_apply (Λ : ℕ → ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    cusum Λ n ω = (Finset.range n).sup fun j ↦ Λ j n ω := by
  rw [cusum]

/-- The Shiryaev–Roberts process vanishes at time `0`. -/
@[simp]
theorem shiryaevRoberts_zero (Λ : ℕ → ℕ → Ω → ℝ≥0∞) : shiryaevRoberts Λ 0 = 0 := by
  ext ω
  simp [shiryaevRoberts_apply]

/-- The CUSUM process vanishes at time `0`. -/
@[simp]
theorem cusum_zero (Λ : ℕ → ℕ → Ω → ℝ≥0∞) : cusum Λ 0 = 0 := by
  ext ω
  simp [cusum_apply]

/-- The CUSUM process is at most the Shiryaev–Roberts process. -/
theorem cusum_le_shiryaevRoberts (Λ : ℕ → ℕ → Ω → ℝ≥0∞) : cusum Λ ≤ shiryaevRoberts Λ :=
  fun n ω ↦ Finset.sup_le fun _ hj ↦
    Finset.single_le_sum (f := fun j ↦ Λ j n ω) (fun _ _ ↦ zero_le) hj

/-- The Shiryaev–Roberts process of adapted processes is adapted. -/
theorem adapted_shiryaevRoberts (hΛ : ∀ j, Adapted ℱ (Λ j)) : Adapted ℱ (shiryaevRoberts Λ) :=
  fun n ↦ Finset.measurable_sum _ fun j _ ↦ hΛ j n

/-- The CUSUM process of adapted processes is adapted. -/
theorem adapted_cusum (hΛ : ∀ j, Adapted ℱ (Λ j)) : Adapted ℱ (cusum Λ) := by
  intro n
  have h : cusum Λ n = (Finset.range n).sup fun j ↦ Λ j n := by
    ext ω
    rw [cusum_apply, Finset.sup_apply]
  rw [h]
  exact Finset.sup_induction measurable_const (fun _ h₁ _ h₂ ↦ h₁.sup h₂) fun j _ ↦ hΛ j n

/-- **The Shiryaev–Roberts e-detector** [SRR24, Definition 2.6]. For e-processes `Λ j` from each
time `j`, the Shiryaev–Roberts process `n ↦ ∑ j < n, Λ j n` is an e-detector. -/
theorem isEDetector_shiryaevRoberts (hΛ : ∀ j, IsEProcessFrom (Λ j) j ℱ S) :
    IsEDetector (shiryaevRoberts Λ) ℱ S := by
  refine ⟨adapted_shiryaevRoberts fun j ↦ (hΛ j).adapted, fun τ' hτ' hτ_top P hP ↦ ?_⟩
  -- `τ'` is finite, so it is the cast of the time `τ` with values in `ℕ`
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top hτ_top
  have hτ_meas : Measurable τ := by
    simpa only [WithTop.untopA_natCast] using hτ'.measurable'.untopA
  simp only [stoppedValue_natCast]
  -- the sum over `j < τ` is the sum over all `j` of the restrictions to `{j < τ}`
  have hset (j : ℕ) : MeasurableSet[ℱ j] {ω | j < τ ω} := by
    simpa using hτ'.measurableSet_natCast_lt j
  have hsum (g : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
      ∑ j ∈ Finset.range (τ ω), g j ω = ∑' j, {ω | j < τ ω}.indicator (g j) ω := by
    rw [tsum_eq_sum (s := Finset.range (τ ω)) fun j hj ↦
      indicator_of_notMem (by simpa using hj) _]
    exact Finset.sum_congr rfl fun j hj ↦ (indicator_of_mem (by simpa using hj) _).symm
  have hmeas (j : ℕ) : MeasurableSet {ω | j < τ ω} := ℱ.le j _ (hset j)
  calc ∫⁻ ω, shiryaevRoberts Λ (τ ω) ω ∂P
      = ∫⁻ ω, ∑' j, {ω | j < τ ω}.indicator (fun ω ↦ Λ j (τ ω) ω) ω ∂P :=
        lintegral_congr fun ω ↦ hsum (fun j ω ↦ Λ j (τ ω) ω) ω
    _ = ∑' j, ∫⁻ ω in {ω | j < τ ω}, Λ j (τ ω) ω ∂P := by
        rw [lintegral_tsum fun j ↦ ((measurable_apply_of_countable (hΛ j).measurable
          hτ_meas).indicator (hmeas j)).aemeasurable]
        exact tsum_congr fun j ↦ lintegral_indicator (hmeas j) _
    _ ≤ ∑' j, P {ω | j < τ ω} := tsum_le_tsum fun j ↦ by
        simpa only [stoppedValue_natCast] using
          (hΛ j).setLIntegral_le hτ' hτ_top hP (hset j)
            fun _ hω ↦ mem_ofPred.2 (Nat.cast_le.2 (mem_ofPred.1 hω).le)
    _ = ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P := by
        -- the tail-sum formula for the expectation of `τ`
        simpa using (lintegral_toENNReal_eq_tsum_measure_lt (μ := P) (f := fun ω ↦ (τ ω : ℕ∞))
          ((measurable_of_countable _).comp hτ_meas).aemeasurable).symm

/-- **The CUSUM e-detector** [SRR24, Definition 2.6]. For e-processes `Λ j` from each time `j`, the
CUSUM process `n ↦ max_{j < n} Λ j n` is an e-detector. -/
theorem isEDetector_cusum (hΛ : ∀ j, IsEProcessFrom (Λ j) j ℱ S) : IsEDetector (cusum Λ) ℱ S :=
  (isEDetector_shiryaevRoberts hΛ).mono (adapted_cusum fun j ↦ (hΛ j).adapted)
    (cusum_le_shiryaevRoberts Λ)

/-- **The Shiryaev–Roberts recursion.** For the products `∏ k ∈ [j, n), F k`, the
Shiryaev–Roberts process satisfies `R (n + 1) = (R n + 1) * F n`. -/
theorem shiryaevRoberts_prod_Ico_succ (F : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    shiryaevRoberts (fun j n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) (n + 1) ω =
      (shiryaevRoberts (fun j n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) n ω + 1) * F n ω := by
  simp only [shiryaevRoberts_apply, Finset.sum_range_succ, Nat.Ico_succ_singleton,
    Finset.prod_singleton, add_mul, one_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦
    Finset.prod_Ico_succ_top (Finset.mem_range.1 hj).le _

/-- **The CUSUM recursion.** For the products `∏ k ∈ [j, n), F k`, the CUSUM process satisfies
`W (n + 1) = max (W n) 1 * F n`. -/
theorem cusum_prod_Ico_succ (F : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    cusum (fun j n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) (n + 1) ω =
      max (cusum (fun j n ω ↦ ∏ k ∈ Finset.Ico j n, F k ω) n ω) 1 * F n ω := by
  rw [cusum_apply, cusum_apply, Finset.range_add_one, Finset.sup_insert, Nat.Ico_succ_singleton,
    Finset.prod_singleton, max_mul, one_mul, Finset.sup_mul₀, max_comm]
  congr 1
  exact Finset.sup_congr rfl fun j hj ↦ Finset.prod_Ico_succ_top (Finset.mem_range.1 hj).le _

end ProbabilityTheory
