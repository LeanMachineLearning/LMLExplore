/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.Centering
public import LMLExplore.Probability.Martingale.OptionalStopping

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
`P (s ∩ {∃ n ≥ m, c ≤ M n}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c`. Restricting to the
`ℱ m`-measurable sets `s ∩ {k⁻¹ < M m}`, of finite measure, it holds under every measure, finite
or not. Its case `m = 0`, `s = univ` is Ville's inequality, whose case `ENNReal.ofReal ∘ f` is
Ville's inequality for real nonnegative supermartingales,
`MeasureTheory.Supermartingale.measure_exists_le_le`. Ville's inequality for
test supermartingales, `P {∃ n, α⁻¹ ≤ M n} ≤ α`, is the time-uniform validity of the test that
rejects the null as soon as the evidence exceeds `α⁻¹`.

## Main statements

* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_add_stoppedValueLimsup`: exact optional
  stopping at a bounded stopping time `τ ≥ m`: `∫⁻ ω in s, M m ω ∂P` is the integral of `M` at
  `τ` plus that of the decrease up to `τ`.
* `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_add_stoppedValueLimsup_min`,
  `ProbabilityTheory.IsENNSupermartingale.setLIntegral_eq_add_stoppedValueLimsup_add_iInf`: exact
  optional stopping at any stopping time `T ≥ m`, with a horizon `N` and without one.
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
  exact Ville identity with applications to e-values*, arXiv:2607.04620v2.
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
  have hτ_top (ω : Ω) : τ ω ≠ ⊤ := WithTop.ne_top_of_le_natCast (hτN ω)
  -- The untopped value of `τ` is between `m` and `N`.
  have hτ_ge (ω : Ω) : m ≤ (τ ω).untopA :=
    (WithTop.le_untopA_iff (hτ_top ω)).2 (by simpa using hmτ ω)
  have hint_g : Integrable (stoppedValue g τ) P := integrable_stoppedValue ℕ hτ hsup.integrable hτN
  have hint_A : Integrable (stoppedValue A τ) P := integrable_stoppedValue ℕ hτ hA_int hτN
  -- The real identity of the Doob decomposition between the constant time `m` and `τ`.
  have hreal := setIntegral_stoppedValue_sub_eq_predictablePart hsup.integrable
    (isStoppingTime_const ℱ m) hτ (fun ω ↦ by simpa using hmτ ω) hτN
    (by rwa [IsStoppingTime.measurableSpace_const])
  simp only [stoppedValue_const] at hreal
  rw [integral_sub hint_g.integrableOn (hsup.integrable m).integrableOn,
    integral_sub hint_A.integrableOn (hA_int m).integrableOn] at hreal
  have hfin := hM.ae_lt_top hP h0
  -- Each lower integral is the `ofReal` of the integral of its real counterpart.
  have h₁ : ∫⁻ ω in s, M m ω ∂P = ENNReal.ofReal (∫ ω in s, g m ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hsup.integrable m).integrableOn
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
    exact lintegral_congr_ae
      (ae_restrict_of_ae (ofReal_toReal_ae_eq (hfin.mono fun _ h ↦ h m)).symm)
  have h₂ : ∫⁻ ω in s, stoppedValueLimsup M τ ω ∂P =
      ENNReal.ofReal (∫ ω in s, stoppedValue g τ ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_g.integrableOn
      (ae_of_all _ fun _ ↦ by simp [stoppedValue, g])]
    rw [funext fun ω ↦ stoppedValueLimsup_eq_stoppedValue (hτ_top ω)]
    exact lintegral_congr_ae
      (ae_restrict_of_ae (ofReal_toReal_ae_eq (hfin.mono fun _ h ↦ h _)).symm)
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

/-- **Exact optional stopping in `ℝ≥0∞` with a horizon.** For an `ℝ≥0∞`-valued supermartingale with
finite initial expectation under a finite measure, a stopping time `T ≥ m`, a horizon `N ≥ m` and
an `ℱ m`-measurable set `s`, the integral of `M m` over `s` is that of `M` at `T` over
`s ∩ {T ≤ N}`, plus that of the decrease from `m` to `T ∧ N` (the value at `T ∧ N` of
`n ↦ ofReal (A m - A n)` for `A` the predictable part of the real values of `M`), plus that of
`M N` over `s ∩ {N < T}`. -/
theorem setLIntegral_eq_add_stoppedValueLimsup_min (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {T : Ω → WithTop ℕ}
    (hT : IsStoppingTime ℱ T) (hmT : ∀ ω, (m : WithTop ℕ) ≤ T ω) (hmN : m ≤ N)
    (hs : MeasurableSet[ℱ m] s) :
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

/-- The hitting time after `m` of `[b, ∞]` by an `ℝ≥0∞`-valued supermartingale is a stopping
time. -/
private theorem isStoppingTime_hittingAfter_Ici (hM : IsENNSupermartingale M ℱ S) (b : ℝ≥0∞) :
    IsStoppingTime ℱ (hittingAfter M (Ici b) m) :=
  hM.adapted.isStoppingTime_hittingAfter measurableSet_Ici

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
  have hT := hM.isStoppingTime_hittingAfter_Ici (m := m) b
  rw [hM.setLIntegral_eq_add_stoppedValueLimsup_min hP h0 hT
    (fun ω ↦ (Nat.cast_withTop m).trans_le (le_hittingAfter ω)) hmN hs,
    setLIntegral_stoppedValueLimsup_hittingAfter b
      ((ℱ.le m _ hs).inter (ℱ.le N _ (hT.measurableSet_le_natCast N)))
      (fun ω hω ↦ WithTop.ne_top_of_le_natCast hω.2)]

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

/-- **Exact optional stopping in `ℝ≥0∞` without horizon.** For an `ℝ≥0∞`-valued supermartingale
with finite initial expectation under a finite measure, a stopping time `T ≥ m` (possibly
infinite) and an `ℱ m`-measurable set `s`, the integral of `M m` over `s` is that of `M` at `T`
over `s ∩ {T ≠ ⊤}`, plus that of the decrease from `m` to `T` (the value at `T`, read with
`MeasureTheory.stoppedValueLimsup`, of `n ↦ ofReal (A m - A n)` for `A` the predictable part of
the real values of `M`), plus the limit `⨅ N ≥ m, ∫⁻ ω in s ∩ {N < T}, M N ω ∂P` of the
remainders. -/
theorem setLIntegral_eq_add_stoppedValueLimsup_add_iInf (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) {T : Ω → WithTop ℕ}
    (hT : IsStoppingTime ℱ T) (hmT : ∀ ω, (m : WithTop ℕ) ≤ T ω) (hs : MeasurableSet[ℱ m] s) :
    ∫⁻ ω in s, M m ω ∂P = ∫⁻ ω in s ∩ {ω | T ω ≠ ⊤}, stoppedValueLimsup M T ω ∂P +
      ∫⁻ ω in s, stoppedValueLimsup (fun n ω ↦ ENNReal.ofReal
        (predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P m ω -
          predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P n ω)) T ω ∂P +
      ⨅ N ≥ m, ∫⁻ ω in s ∩ {ω | (N : WithTop ℕ) < T ω}, M N ω ∂P := by
  set A := predictablePart (fun n ω ↦ (M n ω).toReal) ℱ P
  set D : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ENNReal.ofReal (A m ω - A n ω)
  have ha := tendsto_setLIntegral_inter_le_natCast (μ := P) (stoppedValueLimsup M T)
    (ℱ.le m _ hs) hT.measurable'
  -- The decrease process is almost surely nondecreasing, and its values at `min T N` increase to
  -- its value at `T`.
  have hDmeas (n : ℕ) : Measurable (D n) :=
    ENNReal.measurable_ofReal.comp
      ((((stronglyAdapted_predictablePart' m).mono (ℱ.le m)).measurable).sub
        (((stronglyAdapted_predictablePart' n).mono (ℱ.le n)).measurable))
  have hDmono : ∀ᵐ ω ∂P, Monotone (D · ω) := by
    filter_upwards [(hM.supermartingale_toReal hP h0).antitone_predictablePart] with ω hω
    exact fun n n' h ↦ ENNReal.ofReal_le_ofReal (sub_le_sub_left (hω h) _)
  have hd := tendsto_lintegral_stoppedValueLimsup_min (μ := P.restrict s) hDmeas
    (ae_restrict_of_ae hDmono) hT.measurable'
  have hr := hM.tendsto_setLIntegral_natCast_lt hP hT hs
  -- The finite-horizon identities pass to the limit.
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) ((ha.add hd).add hr)
  filter_upwards [eventually_ge_atTop m] with N hN
  exact hM.setLIntegral_eq_add_stoppedValueLimsup_min hP h0 hT hmT hN hs

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
  have hT := hM.isStoppingTime_hittingAfter_Ici (m := m) b
  have hTtop : MeasurableSet {ω | hittingAfter M (Ici b) m ω ≠ ⊤} := by
    exact (hT.measurable' (measurableSet_singleton ⊤)).compl
  rw [hM.setLIntegral_eq_add_stoppedValueLimsup_add_iInf hP h0 hT
      (fun ω ↦ (Nat.cast_withTop m).trans_le (le_hittingAfter ω)) hs,
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

/-- The extended Ville inequality under a finite measure. -/
private theorem measure_inter_exists_le_le_of_isFiniteMeasure (hM : IsENNSupermartingale M ℱ S)
    (hP : P ∈ S) [IsFiniteMeasure P] {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hs : MeasurableSet[ℱ m] s) :
    P (s ∩ {ω | ∃ n ≥ m, c ≤ M n ω}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c := by
  -- `M` capped at `c` is a supermartingale with finite initial expectation reaching `c` exactly
  -- when `M` does.
  have hMc := hM.inf (M := M) (N := fun _ _ ↦ c) ⟨fun _ ↦ measurable_const, fun _ _ _ _ _ ↦ le_rfl⟩
  have h0 : ∫⁻ ω, (M ⊓ fun _ _ ↦ c) 0 ω ∂P ≠ ∞ := by
    refine ((lintegral_mono fun ω ↦ inf_le_right).trans_lt ?_).ne
    rw [lintegral_const]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top P univ)
  rw [ENNReal.le_div_iff_mul_le (.inl hc0) (.inl hc), mul_comm]
  simpa only [Pi.inf_apply, le_inf_iff, le_refl, and_true] using
    hMc.mul_measure_inter_exists_le_le hP h0 c hs

/-- **The extended Ville inequality** [WR23, Theorem 4.1]. For every `ℝ≥0∞`-valued
supermartingale under any measure, with no integrability condition, every time `m`, every
`ℱ m`-measurable set `s` and every level `0 < c < ∞`,
`P (s ∩ {∃ n ≥ m, c ≤ M n}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c`. -/
theorem measure_inter_exists_le_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (hs : MeasurableSet[ℱ m] s) :
    P (s ∩ {ω | ∃ n ≥ m, c ≤ M n ω}) ≤ (∫⁻ ω in s, min (M m ω) c ∂P) / c := by
  set E := {ω | ∃ n ≥ m, c ≤ M n ω}
  set R := ∫⁻ ω in s, min (M m ω) c ∂P
  rcases eq_or_ne R ∞ with hR | hR
  · rw [hR, ENNReal.top_div_of_ne_top hc]
    exact le_top
  -- The bound holds under the restriction of `P` to each set `B k = s ∩ {k⁻¹ < M m}`, which is
  -- `ℱ m`-measurable and of finite measure by Markov's inequality. Under that restriction, `M`
  -- with the value `∞` before time `m` is a supermartingale.
  set B : ℕ → Set Ω := fun k ↦ s ∩ {ω | (k : ℝ≥0∞)⁻¹ < M m ω}
  have hB (k : ℕ) : MeasurableSet[ℱ m] (B k) := hs.inter (measurableSet_lt measurable_const
    (hM.adapted m))
  have hbound (k : ℕ) : P (B k ∩ E) ≤ R / c := by
    set a := min (k : ℝ≥0∞)⁻¹ c
    have ha0 : a ≠ 0 := (lt_min (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k))
      (pos_iff_ne_zero.2 hc0)).ne'
    have ha : a ≠ ∞ := ((min_le_right _ _).trans_lt hc.lt_top).ne
    have : IsFiniteMeasure (P.restrict (B k)) := isFiniteMeasure_restrict.2 <| by
      refine (lt_of_le_of_lt ?_ ((meas_ge_le_lintegral_div
        ((hM.measurable m).min measurable_const).aemeasurable ha0 ha).trans_lt
        (ENNReal.div_lt_top hR ha0))).ne
      rw [Measure.restrict_apply' (ℱ.le m _ hs)]
      exact measure_mono fun ω hω ↦ ⟨show a ≤ _ from min_le_min hω.2.le le_rfl, hω.1⟩
    set M' : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ if n < m then ∞ else M n ω
    have hM' : IsENNSupermartingale M' ℱ {P.restrict (B k)} := hM.ite_top_restrict hP (hB k)
    have hE' : {ω | ∃ n ≥ m, c ≤ M' n ω} = E := by
      ext ω
      exact exists_congr fun n ↦ and_congr_right fun hn ↦ by simp [M', not_lt.2 hn]
    have h := hM'.measure_inter_exists_le_le_of_isFiniteMeasure (m := m) (mem_singleton _) hc0 hc
      MeasurableSet.univ
    rw [univ_inter, hE', Measure.restrict_univ, Measure.restrict_apply' (ℱ.le m _ (hB k))] at h
    simp only [M', lt_self_iff_false, ↓reduceIte] at h
    rw [inter_comm]
    exact h.trans (ENNReal.div_le_div_right (lintegral_mono_set inter_subset_left) c)
  -- On `Z = s ∩ {M m = 0}`, the process vanishes almost surely from time `m` on.
  set Z := s ∩ {ω | M m ω = 0}
  have hZE : P (Z ∩ E) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hM.ae_eq_zero_of_eq_zero hP] with ω hω ⟨hωZ, n, hn, hcn⟩
    exact hc0 (nonpos_iff_eq_zero.1 (hcn.trans_eq (hω m hωZ.2 n hn)))
  -- The sets `B k` increase to `s` off `Z`.
  have hcover : s ∩ E ⊆ (⋃ k, B k ∩ E) ∪ Z ∩ E := by
    rintro ω ⟨hωs, hωE⟩
    rcases eq_or_ne (M m ω) 0 with h0 | h0
    · exact Or.inr ⟨⟨hωs, h0⟩, hωE⟩
    · obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt h0
      exact Or.inl (mem_iUnion.2 ⟨k, ⟨hωs, hk⟩, hωE⟩)
  have hmono : Monotone fun k ↦ B k ∩ E := fun i j hij ↦ inter_subset_inter_left _
    (inter_subset_inter_right _ fun ω (hω : (i : ℝ≥0∞)⁻¹ < M m ω) ↦
      (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hij)).trans_lt hω)
  calc P (s ∩ E) ≤ P (⋃ k, B k ∩ E) + P (Z ∩ E) :=
        (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ R / c := by
        rw [hZE, add_zero, hmono.measure_iUnion]
        exact iSup_le hbound

/-- **Ville's inequality** [Vil39; RW, Fact 7.6]. For every `ℝ≥0∞`-valued supermartingale under
any measure, with no integrability condition, and every level `0 < c < ∞`, the measure of the
event that the process ever reaches `c` is at most `(∫⁻ ω, M 0 ω ∂P) / c`. -/
theorem measure_exists_le_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    P {ω | ∃ n, c ≤ M n ω} ≤ (∫⁻ ω, M 0 ω ∂P) / c := by
  have h := hM.measure_inter_exists_le_le (m := 0) hP hc0 hc MeasurableSet.univ
  simp only [univ_inter, ge_iff_le, zero_le, true_and, Measure.restrict_univ] at h
  exact h.trans (ENNReal.div_le_div_right (lintegral_mono fun ω ↦ min_le_left _ _) c)

end IsENNSupermartingale

namespace IsTestSupermartingale

/-- **Ville's inequality** for test supermartingales [Vil39; RW, Fact 7.6]: under every member
of the null, the measure of the event that the process ever reaches a level `c ≠ 0` is at most
`(∫⁻ ω, M 0 ω ∂P) / c`. -/
theorem measure_exists_le_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    P {ω | ∃ n, c ≤ M n ω} ≤ (∫⁻ ω, M 0 ω ∂P) / c := by
  rcases eq_or_ne c ∞ with rfl | hc
  · refine (measure_eq_zero_iff_ae_notMem.2 ?_).trans_le zero_le
    filter_upwards [hM.ae_lt_top hP] with ω hω ⟨n, hn⟩
    exact (hω n).not_ge hn
  · exact hM.toIsENNSupermartingale.measure_exists_le_le hP hc0 hc

/-- **Ville's inequality** for test supermartingales, at level `α` [RW, Fact 7.6]: under every
member of the null, the test that rejects as soon as the process reaches `α⁻¹` has type I error at
most `α`, uniformly over time. -/
theorem measure_exists_inv_le_le (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    (α : ℝ≥0∞) : P {ω | ∃ n, α⁻¹ ≤ M n ω} ≤ α := by
  rcases eq_or_ne α ∞ with rfl | hα
  · exact le_top
  refine (hM.measure_exists_le_le hP (ENNReal.inv_ne_zero.2 hα)).trans ?_
  rw [div_eq_mul_inv, inv_inv]
  exact mul_le_of_le_one_left zero_le (hM.lintegral_zero_le P hP)

end IsTestSupermartingale

end ProbabilityTheory
