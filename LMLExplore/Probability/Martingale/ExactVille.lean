/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.Centering
public import LMLExplore.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.HittingTime

/-!
# The exact Ville identity

For an `ℝ≥0∞`-valued supermartingale `M` (`ProbabilityTheory.IsENNSupermartingale`) with finite
initial expectation under a finite measure `P`, a level `b`, and the first time `T` after `m` at
which `b ≤ M n`, the exact Ville identity [dlP+26, Theorem 1] decomposes the initial wealth
exactly: for every horizon `N ≥ m` and every `ℱ m`-measurable set `s`,
$$\int_s M_m = b\,P(s\cap\{T\le N\}) + \int_{s\cap\{T\le N\}}(M_T-b)
  + \int_s\sum_{m\le k<T\wedge N}\big(M_k-\mathbb E[M_{k+1}\mid\mathcal F_k]\big)
  + \int_{s\cap\{T>N\}}M_N,$$
the four terms being the level reached, the overshoot, the predictable decrease and the
remainder. The decrease is read off Mathlib's `MeasureTheory.predictablePart` of the real
values `(M n).toReal`: it is `A m - A (T ∧ N)` for `A` that predictable part, the value at
`T ∧ N` of the almost surely nondecreasing process `D n = ofReal (A m - A n)`. Letting the
horizon tend to infinity gives the identity without horizon [dlP+26, Theorem 4], with the
overshoot over `{T < ∞}`, the decrease up to `T` (read with `MeasureTheory.stoppedValueLimsup`)
and the remainder `⨅ N ≥ m, ∫⁻ ω in s ∩ {N < T}, M N ω ∂P`, the limit of the remainders.

All terms are nonnegative: dropping overshoot, decrease and remainder gives Ville's inequality
[Vil39; RW, Fact 7.6], with equality exactly when the three vanish. From time `m` on `s`, it
gives the extended Ville inequality [WR23, Theorem 4.1] for every `ℝ≥0∞`-valued supermartingale,
with no integrability condition:
`P (s ∩ {∃ n ≥ m, c ≤ M n}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c`. Ville's inequality for test
supermartingales, `P {∃ n, α⁻¹ ≤ M n} ≤ α`, is the time-uniform validity of the test that
rejects the null as soon as the evidence exceeds `α⁻¹`.

## Main statements

* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_add_stoppedValueLimsup`: exact optional
  stopping at a bounded stopping time `τ ≥ m`: `∫⁻ ω in s, M m ω ∂P` is the integral of `M` at
  `τ` plus that of the decrease up to `τ`.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_exact_ville_horizon`,
  `ProbabilityTheory.IsENNSupermartingale.lintegral_zero_eq_exact_ville_horizon`: the exact Ville
  identity with a horizon [dlP+26, Theorem 1].
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_exact_ville`,
  `ProbabilityTheory.IsENNSupermartingale.lintegral_zero_eq_exact_ville`: the exact Ville identity
  without horizon [dlP+26, Theorem 4].
* `ProbabilityTheory.IsENNSupermartingale.mul_measure_inter_eq_setLIntegral_iff`: equality in
  Ville's inequality holds exactly when overshoot, decrease and remainder vanish.
* `ProbabilityTheory.IsENNSupermartingale.measure_inter_exists_le_le`: the extended Ville
  inequality from time `m` [WR23, Theorem 4.1].
* `ProbabilityTheory.IsENNSupermartingale.measure_exists_le_le`,
  `ProbabilityTheory.IsTestSupermartingale.measure_exists_le_le`,
  `ProbabilityTheory.IsTestSupermartingale.measure_exists_inv_le_le`: Ville's inequality.

## References

* [dlP+26] V. H. de la Peña, M. J. Klass, V. H. de la Peña, A. Ly, A. Neishloss and Y. Lin, *The
  exact Ville identity*, 2026.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [Vil39] J. Ville, *Étude critique de la notion de collectif*, Gauthier-Villars, 1939.
* [WR23] H. Wang and A. Ramdas, *The extended Ville's inequality for nonintegrable nonnegative
  supermartingales*, arXiv:2304.01163.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {P : Measure Ω} {M : ℕ → Ω → ℝ≥0∞} {s : Set Ω} {m N : ℕ}

namespace IsENNSupermartingale

/-- **Exact optional stopping in `ℝ≥0∞`.** For an `ℝ≥0∞`-valued supermartingale with finite initial
expectation under a finite measure, a stopping time `m ≤ τ ≤ N` and an `ℱ m`-measurable set `s`,
the integral of `M m` over `s` is that of `M` at `τ` plus that of the decrease from `m` to `τ`,
the value at `τ` of `n ↦ ofReal (A m - A n)` for `A` the predictable part of the real values of
`M`. -/
theorem setLIntegral_eq_add_stoppedValueLimsup (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hmτ : ∀ ω, (m : WithTop ℕ) ≤ τ ω) (hτN : ∀ ω, τ ω ≤ N) (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P = ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) τ ω ∂P := by
  set g : ℕ → Ω → ℝ := fun n ω ↦ (M n ω).toReal
  set A := predictablePart g ℱ P
  have hsup : Supermartingale g ℱ P := hM.supermartingale_toReal hP h0
  have hA_int (n : ℕ) : Integrable (A n) P :=
    integrable_finsetSum' _ fun _ _ ↦ integrable_condExp
  have hτN' (ω : Ω) : τ ω ≤ (N : ℕ) := by simpa using hτN ω
  have hτ_top (ω : Ω) : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτN' ω)
  -- The untopped value of `τ` is between `m` and `N`.
  have hτ_ge (ω : Ω) : m ≤ (τ ω).untopA :=
    (WithTop.le_untopA_iff (hτ_top ω)).2 (by simpa using hmτ ω)
  have hint_g : Integrable (stoppedValue g τ) P := integrable_stoppedValue ℕ hτ hsup.integrable hτN'
  have hint_A : Integrable (stoppedValue A τ) P := integrable_stoppedValue ℕ hτ hA_int hτN'
  -- The real identity of the Doob decomposition between the constant time `m` and `τ`.
  have hreal := setIntegral_stoppedValue_sub_eq_predictablePart hsup.integrable
    (isStoppingTime_const ℱ m) hτ (fun ω ↦ by simpa using hmτ ω) hτN'
    (by rwa [IsStoppingTime.measurableSpace_const])
  simp only [stoppedValue_const] at hreal
  rw [integral_sub hint_g.integrableOn (hsup.integrable m).integrableOn,
    integral_sub hint_A.integrableOn (hA_int m).integrableOn] at hreal
  have hfin := hM.ae_lt_top hP h0
  -- Each lower integral is the `ofReal` of the integral of its real counterpart.
  have h₁ : ∫⁻ ω in s, M m ω ∂P = ENNReal.ofReal (∫ ω in s, g m ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hsup.integrable m).integrableOn
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hfin] with ω hω using (ENNReal.ofReal_toReal (hω m).ne).symm
  have h₂ : ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P =
      ENNReal.ofReal (∫ ω in s, stoppedValue g τ ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_g.integrableOn
      (ae_of_all _ fun _ ↦ by simp [stoppedValue, g])]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hfin] with ω hω
    rw [stoppedValueLimsup_eq_stoppedValue (hτ_top ω)]
    simp only [stoppedValue, g]
    exact (ENNReal.ofReal_toReal (hω _).ne).symm
  -- The predictable part of a supermartingale is antitone, and `m ≤ τ`.
  have hnonneg : 0 ≤ᵐ[P.restrict s] fun ω ↦ A m ω - stoppedValue A τ ω := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hsup.antitone_predictablePart] with ω hω
    exact sub_nonneg.2 (hω (hτ_ge ω))
  have h₃ : ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal (A m ω - A n ω)) τ ω ∂P =
      ENNReal.ofReal (∫ ω in s, A m ω - stoppedValue A τ ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun ω ↦ A m ω - stoppedValue A τ ω)
      ((hA_int m).sub hint_A).integrableOn hnonneg]
    refine lintegral_congr fun ω ↦ ?_
    rw [stoppedValueLimsup_eq_stoppedValue (hτ_top ω)]
    simp [stoppedValue]
  rw [h₁, h₂, h₃, ← ENNReal.ofReal_add (integral_nonneg fun ω ↦ by simp [stoppedValue, g])
    (setIntegral_nonneg_of_ae_restrict hnonneg)]
  congr 1
  rw [integral_sub (hA_int m).integrableOn hint_A.integrableOn]
  linarith

/-- Splitting at the horizon: for a stopping time `T ≥ m` and `N ≥ m`, the value at `min T N` is
the value at `T` on `{T ≤ N}` and `M N` on `{N < T}`. -/
private theorem setLIntegral_eq_add_add_of_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T)
    (hmT : ∀ ω, (m : WithTop ℕ) ≤ T ω) (hmN : m ≤ N) (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P = ∫⁻ ω in s ∩ {ω | T ω ≤ N}, stoppedValueLimsup M T ω ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) (fun ω ↦ min (T ω) N) ω ∂P +
      ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P := by
  have hs' : MeasurableSet s := ℱ.le m _ hs
  have hTN : MeasurableSet {ω | T ω ≤ N} := ℱ.le N _ (hT.measurableSet_le_natCast N)
  have hNT : MeasurableSet {ω | (N : WithTop ℕ) < T ω} :=
    ℱ.le N _ (hT.measurableSet_natCast_lt N)
  have hdiff : s \ {ω | T ω ≤ N} = s ∩ {ω | (N : WithTop ℕ) < T ω} := by
    ext ω
    simp [not_le]
  rw [hM.setLIntegral_eq_add_stoppedValueLimsup hP h0 (hT.min_natCast N)
    (fun ω ↦ le_min (hmT ω) (by exact_mod_cast hmN)) (fun ω ↦ min_le_right _ _) hs,
    ← lintegral_inter_add_sdiff _ s hTN, hdiff,
    setLIntegral_congr_fun (f := stoppedValueLimsup M fun ω ↦ min (T ω) N)
      (g := stoppedValueLimsup M T) (hs'.inter hTN)
      (fun ω hω ↦ stoppedValueLimsup_congr (min_eq_left hω.2)),
    setLIntegral_congr_fun (f := stoppedValueLimsup M fun ω ↦ min (T ω) N) (g := M N)
      (hs'.inter hNT) (fun ω hω ↦ stoppedValueLimsup_of_eq_natCast (min_eq_right hω.2.le)),
    add_right_comm]

/-- A hitting time after `m` is at least `m`, at the cast `(m : WithTop ℕ)`. -/
private theorem natCast_le_hittingAfter (t : Set ℝ≥0∞) (ω : Ω) :
    (m : WithTop ℕ) ≤ hittingAfter M t m ω := by
  simpa using le_hittingAfter (u := M) (s := t) (n := m) ω

/-- On a set where the hitting time `T` of `[b, ∞]` is finite, `M` at `T` is `b` plus the
overshoot `M T - b`. -/
private theorem setLIntegral_stoppedValueLimsup_hittingAfter (b : ℝ≥0∞) {t : Set Ω}
    (ht : MeasurableSet t) (htT : t ⊆ {ω | hittingAfter M (Ici b) m ω ≠ ⊤}) :
    ∫⁻ ω in t, stoppedValueLimsup M (hittingAfter M (Ici b) m) ω ∂P =
      b * P t + ∫⁻ ω in t, (stoppedValueLimsup M (hittingAfter M (Ici b) m) ω - b) ∂P := by
  rw [← setLIntegral_const, ← lintegral_add_left measurable_const]
  refine setLIntegral_congr_fun ht fun ω hω ↦ ?_
  have hb : b ≤ stoppedValueLimsup M (hittingAfter M (Ici b) m) ω := by
    rw [stoppedValueLimsup_eq_stoppedValue (htT hω)]
    exact hittingAfter_mem_set_of_ne_top (htT hω)
  exact (add_tsub_cancel_of_le hb).symm

/-- **The exact Ville identity** [dlP+26, Theorem 1], from time `m` on an `ℱ m`-measurable set
`s`. For an `ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite
measure, a level `b`, the first time `T` after `m` at which `b ≤ M n`, and a horizon `N ≥ m`, the
integral of `M m` over `s` is the sum of the level reached `b * P (s ∩ {T ≤ N})`, the overshoot
`M T - b` over `s ∩ {T ≤ N}`, the predictable decrease up to `T ∧ N` (with `A` the predictable
part of the real values of `M`, the sum over `m ≤ k < T ∧ N` of `M k - E[M (k + 1) | ℱ k]`) and the
remainder `M N` over `s ∩ {N < T}`. -/
theorem setLIntegral_eq_exact_ville_horizon (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) (hmN : m ≤ N)
    (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P =
      b * P (s ∩ {ω | hittingAfter M (Ici b) m ω ≤ N}) +
      ∫⁻ ω in s ∩ {ω | hittingAfter M (Ici b) m ω ≤ N},
        (stoppedValueLimsup M (hittingAfter M (Ici b) m) ω - b) ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω))
        (fun ω ↦ min (hittingAfter M (Ici b) m ω) N) ω ∂P +
      ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < hittingAfter M (Ici b) m ω}, M N ω ∂P := by
  have hT : IsStoppingTime ℱ (hittingAfter M (Ici b) m) :=
    hM.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  rw [hM.setLIntegral_eq_add_add_of_le hP h0 hT (natCast_le_hittingAfter (Ici b))
    hmN hs,
    setLIntegral_stoppedValueLimsup_hittingAfter b
      ((ℱ.le m _ hs).inter (ℱ.le N _ (hT.measurableSet_le_natCast N)))
      (fun ω hω ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) hω.2)]

/-- **The exact Ville identity** [dlP+26, Theorem 1]. For an `ℝ≥0∞`-valued supermartingale with
finite initial expectation under a finite measure, a level `b`, the first time `T` at which
`b ≤ M n`, and a horizon `N`, the initial expectation is the sum of the level reached
`b * P {T ≤ N}`, the overshoot `M T - b` over `{T ≤ N}`, the predictable decrease
`-A (T ∧ N)` (with `A` the predictable part of the real values of `M`, the sum over `k < T ∧ N`
of `M k - E[M (k + 1) | ℱ k]`) and the remainder `M N` over `{N < T}`. -/
theorem lintegral_zero_eq_exact_ville_horizon (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) (N : ℕ) :
    ∫⁻ ω, M 0 ω ∂P =
      b * P {ω | hittingAfter M (Ici b) 0 ω ≤ N} +
      ∫⁻ ω in {ω | hittingAfter M (Ici b) 0 ω ≤ N},
        (stoppedValueLimsup M (hittingAfter M (Ici b) 0) ω - b) ∂P +
      ∫⁻ ω, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (-predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω))
        (fun ω ↦ min (hittingAfter M (Ici b) 0 ω) N) ω ∂P +
      ∫⁻ ω in {ω | (N : WithTop ℕ) < hittingAfter M (Ici b) 0 ω}, M N ω ∂P := by
  simpa using hM.setLIntegral_eq_exact_ville_horizon hP h0 b N.zero_le MeasurableSet.univ

/-- The remainders `∫⁻ ω in s ∩ {N < T}, M N ω ∂P` are nonincreasing after time `m`, hence
converge to their infimum over `N ≥ m`. -/
private theorem tendsto_setLIntegral_natCast_lt (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) (hs : MeasurableSet[ℱ m] s) :
    Tendsto (fun N : ℕ ↦ ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P) atTop
      (𝓝 (⨅ N ≥ m, ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P)) := by
  set r : ℕ → ℝ≥0∞ := fun N ↦ ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P
  have hr_succ (N : ℕ) (hN : m ≤ N) : r (N + 1) ≤ r N := by
    refine (lintegral_mono_set (inter_subset_inter_right _ fun ω hω ↦ ?_)).trans
      (hM.setLIntegral_succ_le P hP N _ ((ℱ.mono hN _ hs).inter (hT.measurableSet_natCast_lt N)))
    rw [mem_ofPred_eq] at hω ⊢
    exact lt_trans (by exact_mod_cast N.lt_succ_self) hω
  rw [iInf_ge_eq_iInf_nat_add, ← tendsto_add_atTop_iff_nat m]
  refine tendsto_atTop_iInf (antitone_nat_of_succ_le fun k ↦ ?_)
  simpa [add_right_comm] using hr_succ (k + m) (Nat.le_add_left m k)

/-- Letting the horizon tend to infinity: for a stopping time `T ≥ m`, the integral of `M m` over
`s` is that of `M` at `T` over `s ∩ {T ≠ ⊤}`, plus the decrease up to `T`, plus the limit of the
remainders. -/
private theorem setLIntegral_eq_add_add_iInf (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T)
    (hmT : ∀ ω, (m : WithTop ℕ) ≤ T ω) (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P = ∫⁻ ω in s ∩ {ω | T ω ≠ ⊤}, stoppedValueLimsup M T ω ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) T ω ∂P +
      ⨅ N ≥ m, ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P := by
  set A := predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P
  set D : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ENNReal.ofReal (A m ω - A n ω)
  have hs' : MeasurableSet s := ℱ.le m _ hs
  -- The integrals of `M T` over `s ∩ {T ≤ N}` increase to its integral over `s ∩ {T ≠ ⊤}`.
  have ha : Tendsto (fun N : ℕ ↦ ∫⁻ ω in s ∩ {ω | T ω ≤ N}, stoppedValueLimsup M T ω ∂P) atTop
      (𝓝 (∫⁻ ω in s ∩ {ω | T ω ≠ ⊤}, stoppedValueLimsup M T ω ∂P)) := by
    have hmeas (N : ℕ) : MeasurableSet (s ∩ {ω | T ω ≤ N}) :=
      hs'.inter (ℱ.le N _ (hT.measurableSet_le_natCast N))
    have hU : ⋃ N : ℕ, s ∩ {ω | T ω ≤ N} = s ∩ {ω | T ω ≠ ⊤} := by
      rw [← inter_iUnion]
      congr 1
      ext ω
      simp only [mem_iUnion, mem_ofPred_eq]
      refine ⟨fun ⟨N, hN⟩ ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) hN, fun h ↦ ?_⟩
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
      exact ⟨t, by simp [← ht]⟩
    simp_rw [← withDensity_apply _ (hmeas _)]
    rw [← withDensity_apply _ (hU ▸ MeasurableSet.iUnion hmeas), ← hU]
    exact tendsto_measure_iUnion_atTop fun N N' h ↦
      inter_subset_inter_right _ fun ω (hω : T ω ≤ N) ↦ hω.trans (by exact_mod_cast h)
  -- The decrease process is almost surely nondecreasing, and its values at `min T N` increase to
  -- its value at `T`.
  have hDmeas (n : ℕ) : Measurable (D n) :=
    ENNReal.measurable_ofReal.comp
      ((((stronglyAdapted_predictablePart' m).mono (ℱ.le m)).measurable).sub
        (((stronglyAdapted_predictablePart' n).mono (ℱ.le n)).measurable))
  have hDmono : ∀ᵐ ω ∂P, Monotone (D · ω) := by
    filter_upwards [(hM.supermartingale_toReal hP h0).antitone_predictablePart] with ω hω
    exact fun n n' h ↦ ENNReal.ofReal_le_ofReal (sub_le_sub_left (hω h) _)
  have hd : Tendsto (fun N : ℕ ↦ ∫⁻ ω in s, stoppedValueLimsup D (fun ω ↦ min (T ω) N) ω ∂P)
      atTop (𝓝 (∫⁻ ω in s, stoppedValueLimsup D T ω ∂P)) := by
    have hmin_top (ω : Ω) (N : ℕ) : min (T ω) N ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (min_le_right _ _)
    refine lintegral_tendsto_of_tendsto_of_monotone (fun N ↦ (measurable_stoppedValueLimsup hDmeas
      (hT.min_natCast N).measurable').aemeasurable) (ae_restrict_of_ae ?_) (ae_restrict_of_ae ?_)
    · filter_upwards [hDmono] with ω hω N N' h
      dsimp only
      rw [stoppedValueLimsup_eq_stoppedValue (τ := fun ω ↦ min (T ω) N) (hmin_top ω N),
        stoppedValueLimsup_eq_stoppedValue (τ := fun ω ↦ min (T ω) N') (hmin_top ω N')]
      exact hω (WithTop.untopA_mono (hmin_top ω N') (min_le_min_left _ (by exact_mod_cast h)))
    · filter_upwards [hDmono] with ω hω
      refine tendsto_stoppedValueLimsup_min ?_
      have h := tendsto_atTop_iSup hω
      rwa [h.limsup_eq]
  have hr := hM.tendsto_setLIntegral_natCast_lt hP hT hs
  -- The finite-horizon identities pass to the limit.
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) ((ha.add hd).add hr)
  filter_upwards [eventually_ge_atTop m] with N hN
  exact hM.setLIntegral_eq_add_add_of_le hP h0 hT hmT hN hs

/-- **The exact Ville identity without horizon** [dlP+26, Theorem 4], from time `m` on an
`ℱ m`-measurable set `s`. For an `ℝ≥0∞`-valued supermartingale with finite initial expectation
under a finite measure, a level `b` and the first time `T` after `m` at which `b ≤ M n`, the
integral of `M m` over `s` is the sum of the level reached `b * P (s ∩ {T < ∞})`, the overshoot
`M T - b` over `s ∩ {T < ∞}`, the predictable decrease up to `T`, and the limit
`⨅ N ≥ m, ∫⁻ ω in s ∩ {N < T}, M N ω ∂P` of the remainders. -/
theorem setLIntegral_eq_exact_ville (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P =
      b * P (s ∩ {ω | hittingAfter M (Ici b) m ω ≠ ⊤}) +
      ∫⁻ ω in s ∩ {ω | hittingAfter M (Ici b) m ω ≠ ⊤},
        (stoppedValueLimsup M (hittingAfter M (Ici b) m) ω - b) ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) (hittingAfter M (Ici b) m) ω ∂P +
      ⨅ N ≥ m, ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < hittingAfter M (Ici b) m ω}, M N ω ∂P := by
  have hT : IsStoppingTime ℱ (hittingAfter M (Ici b) m) :=
    hM.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  have hTtop : MeasurableSet {ω | hittingAfter M (Ici b) m ω ≠ ⊤} := by
    exact (hT.measurable' (measurableSet_singleton ⊤)).compl
  rw [hM.setLIntegral_eq_add_add_iInf hP h0 hT (natCast_le_hittingAfter (Ici b)) hs,
    setLIntegral_stoppedValueLimsup_hittingAfter b ((ℱ.le m _ hs).inter hTtop)
      inter_subset_right]

/-- **The exact Ville identity without horizon** [dlP+26, Theorem 4]. For an `ℝ≥0∞`-valued
supermartingale with finite initial expectation under a finite measure, a level `b` and the
first time `T` at which `b ≤ M n`, the initial expectation is the sum of the level reached
`b * P {T < ∞}`, the overshoot `M T - b` over `{T < ∞}`, the predictable decrease `-A T` (with `A`
the predictable part of the real values of `M`), and the limit `⨅ N, ∫⁻ ω in {N < T}, M N ω ∂P` of
the remainders. -/
theorem lintegral_zero_eq_exact_ville (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) :
    ∫⁻ ω, M 0 ω ∂P =
      b * P {ω | hittingAfter M (Ici b) 0 ω ≠ ⊤} +
      ∫⁻ ω in {ω | hittingAfter M (Ici b) 0 ω ≠ ⊤},
        (stoppedValueLimsup M (hittingAfter M (Ici b) 0) ω - b) ∂P +
      ∫⁻ ω, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (-predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) (hittingAfter M (Ici b) 0) ω ∂P +
      ⨅ N : ℕ, ∫⁻ ω in {ω | (N : WithTop ℕ) < hittingAfter M (Ici b) 0 ω}, M N ω ∂P := by
  simpa using hM.setLIntegral_eq_exact_ville (m := 0) hP h0 b MeasurableSet.univ

/-- **Equality in Ville's inequality.** For an `ℝ≥0∞`-valued supermartingale with finite initial
expectation under a finite measure, a level `b` and the first time `T` after `m` at which
`b ≤ M n`, the bound `b * P (s ∩ {T < ∞}) ≤ ∫⁻ ω in s, M m ω ∂P` is an equality exactly when the
overshoot, the predictable decrease and the remainder of the exact Ville identity vanish. -/
theorem mul_measure_inter_eq_setLIntegral_iff (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) (hs : MeasurableSet[ℱ m] s) :
    b * P (s ∩ {ω | hittingAfter M (Ici b) m ω ≠ ⊤}) = ∫⁻ ω in s, M m ω ∂P ↔
      ∫⁻ ω in s ∩ {ω | hittingAfter M (Ici b) m ω ≠ ⊤},
        (stoppedValueLimsup M (hittingAfter M (Ici b) m) ω - b) ∂P = 0 ∧
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) (hittingAfter M (Ici b) m) ω ∂P = 0 ∧
      ⨅ N ≥ m, ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < hittingAfter M (Ici b) m ω}, M N ω ∂P = 0 := by
  have hfin : ∫⁻ ω in s, M m ω ∂P ≠ ∞ :=
    ((setLIntegral_le_lintegral s _).trans (hM.lintegral_le hP m.zero_le)).trans_lt h0.lt_top |>.ne
  rw [hM.setLIntegral_eq_exact_ville hP h0 b hs, add_assoc, add_assoc] at hfin ⊢
  conv_lhs => lhs; rw [← add_zero (b * _)]
  rw [ENNReal.add_right_inj (ENNReal.add_ne_top.1 hfin).1, eq_comm, add_eq_zero, add_eq_zero]

/-- Ville's maximal inequality from time `m`, for an `ℝ≥0∞`-valued supermartingale with finite
initial expectation: the exact Ville identity without its overshoot, decrease and remainder. -/
private theorem mul_measure_inter_exists_le_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) (b : ℝ≥0∞) (hs : MeasurableSet[ℱ m] s) :
    b * P (s ∩ {ω | ∃ n ≥ m, b ≤ M n ω}) ≤ ∫⁻ ω in s, M m ω ∂P := by
  have hset : {ω | ∃ n ≥ m, b ≤ M n ω} = {ω | hittingAfter M (Ici b) m ω ≠ ⊤} := by
    ext ω
    simp [hittingAfter_eq_top_iff]
  rw [hset, hM.setLIntegral_eq_exact_ville hP h0 b hs, add_assoc, add_assoc]
  exact le_self_add

/-- Ville's maximal inequality from time `m` on an `ℱ m`-measurable set `u` on which `M m ≤ c`,
for every `ℝ≥0∞`-valued supermartingale under a finite measure, with no integrability condition:
the process equal to `c` before time `m` and to `M` on `u` from time `m` on has finite initial
expectation. -/
private theorem mul_measure_inter_exists_le_le_of_le (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) [IsFiniteMeasure P] {c : ℝ≥0∞} (hc : c ≠ ∞) {u : Set Ω}
    (hu : MeasurableSet[ℱ m] u) (hMu : ∀ ω ∈ u, M m ω ≤ c) :
    c * P (u ∩ {ω | ∃ n ≥ m, c ≤ M n ω}) ≤ ∫⁻ ω in u, M m ω ∂P := by
  set M' : ℕ → Ω → ℝ≥0∞ := fun n ↦ if n < m then fun _ ↦ c else u.indicator (M n)
  have hM'_le (n : ℕ) (hn : n ≤ m) (ω : Ω) : M' n ω ≤ c := by
    rcases hn.lt_or_eq with hn | rfl
    · simp [M', hn]
    · by_cases hω : ω ∈ u
      · simpa [M', indicator_of_mem hω] using hMu ω hω
      · simp [M', indicator_of_notMem hω]
  have hM' : IsENNSupermartingale M' ℱ {P} := by
    refine ⟨fun n ↦ ?_, fun Q hQ n v hv ↦ ?_⟩
    · by_cases hn : n < m
      · simp [M', hn]
      · simpa [M', hn] using (hM.adapted n).indicator (ℱ.mono (not_lt.1 hn) _ hu)
    rw [mem_singleton_iff] at hQ
    subst hQ
    by_cases hnm : n < m
    · calc ∫⁻ ω in v, M' (n + 1) ω ∂Q ≤ ∫⁻ ω in v, c ∂Q :=
            lintegral_mono fun ω ↦ hM'_le (n + 1) hnm ω
        _ = ∫⁻ ω in v, M' n ω ∂Q := by simp [M', hnm]
    · have hn : ¬n + 1 < m := by omega
      simp only [M', hn, hnm, ite_false]
      rw [setLIntegral_indicator (ℱ.le m _ hu), setLIntegral_indicator (ℱ.le m _ hu)]
      exact hM.setLIntegral_succ_le Q hP n _ ((ℱ.mono (not_lt.1 hnm) _ hu).inter hv)
  have h0' : ∫⁻ ω, M' 0 ω ∂P ≠ ∞ := by
    refine ((lintegral_mono (hM'_le 0 m.zero_le)).trans_lt ?_).ne
    rw [lintegral_const]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top P univ)
  -- On `u`, `M'` agrees with `M` from time `m` on.
  have hE : u ∩ {ω | ∃ n ≥ m, c ≤ M' n ω} = u ∩ {ω | ∃ n ≥ m, c ≤ M n ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun hω ↦ exists_congr fun n ↦ and_congr_right fun hn ↦ ?_
    simp [M', not_lt.2 hn, indicator_of_mem hω]
  have hM'm : ∫⁻ ω in u, M' m ω ∂P = ∫⁻ ω in u, M m ω ∂P := by
    simp only [M', lt_irrefl, ite_false]
    rw [setLIntegral_indicator (ℱ.le m _ hu), inter_self]
  simpa only [hE, hM'm] using hM'.mul_measure_inter_exists_le_le (mem_singleton P) h0' c hu

/-- **The extended Ville inequality** [WR23, Theorem 4.1]. For every `ℝ≥0∞`-valued
supermartingale under a finite measure, with no integrability condition, every time `m`, every
`ℱ m`-measurable set `s` and every level `0 < c < ∞`,
`P (s ∩ {∃ n ≥ m, c ≤ M n}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c`. -/
theorem measure_inter_exists_le_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (hs : MeasurableSet[ℱ m] s) :
    P (s ∩ {ω | ∃ n ≥ m, c ≤ M n ω}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c := by
  rw [ENNReal.le_div_iff_mul_le (.inl hc0) (.inl hc), mul_comm]
  set E := {ω | ∃ n ≥ m, c ≤ M n ω}
  set t := {ω | M m ω < c}
  have ht : MeasurableSet[ℱ m] t := measurableSet_lt (hM.adapted m) measurable_const
  have hmax := hM.mul_measure_inter_exists_le_le_of_le hP hc (hs.inter ht) fun ω hω ↦ hω.2.le
  -- On `s \ t`, `c ≤ M m`, so that the event holds at time `m` and `min (M m) c = c`.
  have hs' : MeasurableSet s := ℱ.le m _ hs
  have ht' : MeasurableSet t := ℱ.le m _ ht
  calc c * P (s ∩ E) ≤ c * (P (s ∩ t ∩ E) + P (s \ t)) := by
        refine mul_le_mul_right ((measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)) c
        by_cases h : ω ∈ t
        · exact Or.inl ⟨⟨hω.1, h⟩, hω.2⟩
        · exact Or.inr ⟨hω.1, h⟩
    _ = c * P (s ∩ t ∩ E) + ∫⁻ ω in s \ t, c ∂P := by rw [mul_add, setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ ω in s ∩ t, M m ω ∂P + ∫⁻ ω in s \ t, c ∂P := by gcongr
    _ = ∫⁻ ω in s ∩ t, min (M m ω) c ∂P + ∫⁻ ω in s \ t, min (M m ω) c ∂P := by
        congr 1
        · exact setLIntegral_congr_fun (hs'.inter ht') fun ω hω ↦ (min_eq_left hω.2.le).symm
        · exact setLIntegral_congr_fun (hs'.diff ht') fun ω hω ↦
            (min_eq_right (not_lt.1 hω.2)).symm
    _ = ∫⁻ ω in s, min (M m ω) c ∂P := lintegral_inter_add_sdiff _ s ht'

/-- **Ville's inequality** [Vil39; RW, Fact 7.6]. For every `ℝ≥0∞`-valued supermartingale under a
finite measure, with no integrability condition, and every level `0 < c < ∞`, the probability
that the process ever reaches `c` is at most `(∫⁻ ω, M 0 ω ∂P) / c`. -/
theorem measure_exists_le_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    P {ω | ∃ n, c ≤ M n ω} ≤ (∫⁻ ω, M 0 ω ∂P) / c := by
  have h := hM.measure_inter_exists_le_le (m := 0) hP hc0 hc MeasurableSet.univ
  simp only [univ_inter, ge_iff_le, zero_le, true_and, Measure.restrict_univ] at h
  exact h.trans (ENNReal.div_le_div_right (lintegral_mono fun ω ↦ min_le_left _ _) c)

end IsENNSupermartingale

namespace IsTestSupermartingale

/-- **Ville's inequality** for test supermartingales [Vil39; RW, Fact 7.6]: under every finite
member of the null, the probability that the process ever reaches a level `c ≠ 0` is at most
`(∫⁻ ω, M 0 ω ∂P) / c`. -/
theorem measure_exists_le_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) [IsFiniteMeasure P]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    P {ω | ∃ n, c ≤ M n ω} ≤ (∫⁻ ω, M 0 ω ∂P) / c := by
  rcases eq_or_ne c ∞ with rfl | hc
  · refine (measure_eq_zero_iff_ae_notMem.2 ?_).trans_le zero_le
    filter_upwards [hM.ae_lt_top hP] with ω hω ⟨n, hn⟩
    exact (hω n).not_ge hn
  · exact hM.toIsENNSupermartingale.measure_exists_le_le hP hc0 hc

/-- **Ville's inequality** for test supermartingales, at level `α` [RW, Fact 7.6]: under every
finite member of the null, the test that rejects as soon as the process reaches `α⁻¹` has type I
error at most `α`, uniformly over time. -/
theorem measure_exists_inv_le_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (α : ℝ≥0∞) : P {ω | ∃ n, α⁻¹ ≤ M n ω} ≤ α := by
  rcases eq_or_ne α ∞ with rfl | hα
  · exact le_top
  refine (hM.measure_exists_le_le hP (ENNReal.inv_ne_zero.2 hα)).trans ?_
  rw [div_eq_mul_inv, inv_inv]
  exact mul_le_of_le_one_left zero_le (hM.lintegral_zero_le P hP)

end IsTestSupermartingale

end ProbabilityTheory
