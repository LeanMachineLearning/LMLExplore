/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Sets of measures that are separable for the total variation distance

A set of measures `𝒬` is *separable for the total variation distance*
(`MeasureTheory.IsTVSeparable`) when a countable subset of `𝒬` is dense in it for `tvDist`.
Separability and domination are close conditions:

* on any measurable space, a nonempty separable set of probability measures is dominated by one
  probability measure, a countable mixture of a dense sequence
  (`MeasureTheory.IsTVSeparable.exists_isProbabilityMeasure_absolutelyContinuous`);
* on a countably generated space, the probability measures dominated by an s-finite measure form a
  separable set (`MeasureTheory.isTVSeparable_setOf_absolutelyContinuous`): their densities lie in
  `L¹` of a finite measure equivalent to it, which is separable, and the total variation distance
  is at most twice the `L¹` distance of the densities.

So on a countably generated space a set of probability measures is separable for the total
variation distance exactly when it is dominated by one s-finite measure. On other spaces domination
does not imply separability: on `{0, 1}^I` with `I` uncountable, the laws with density
`2 * 𝟙{x i = 1}` with respect to the product of fair bits are at distance `1` from each other.

## Main definitions

* `MeasureTheory.IsTVSeparable 𝒬`: some countable subset of `𝒬` is dense in `𝒬` for `tvDist`.

## Main statements

* `MeasureTheory.IsTVSeparable.mono`: a subset of a separable set of finite measures is separable.
* `MeasureTheory.IsTVSeparable.exists_isProbabilityMeasure_absolutelyContinuous`: separability
  implies domination.
* `MeasureTheory.isTVSeparable_setOf_absolutelyContinuous`: on a countably generated space,
  domination implies separability.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X} {𝒬 𝒬' : Set (Measure X)}

/-- A set of measures is **separable for the total variation distance** when some countable subset
of it is dense in it for `tvDist`. -/
def IsTVSeparable (𝒬 : Set (Measure X)) : Prop :=
  ∃ D ⊆ 𝒬, D.Countable ∧ ∀ Q ∈ 𝒬, ∀ ε > 0, ∃ R ∈ D, tvDist Q R < ε

/-- The empty set is separable. -/
lemma isTVSeparable_empty : IsTVSeparable (∅ : Set (Measure X)) :=
  ⟨∅, subset_rfl, countable_empty, fun _ h ↦ absurd h (notMem_empty _)⟩

/-- A countable set of measures is separable: it is dense in itself. -/
lemma _root_.Set.Countable.isTVSeparable (h : 𝒬.Countable) : IsTVSeparable 𝒬 :=
  ⟨𝒬, subset_rfl, h, fun Q hQ _ hε ↦ ⟨Q, hQ, by rwa [tvDist_self]⟩⟩

/-- **A subset of a separable set of finite measures is separable.** For each member `R` of a
countable dense subset and each `k`, keep one member of the subset at distance less than
`1 / (k + 1)` of `R`, when there is one. -/
lemma IsTVSeparable.mono (h : IsTVSeparable 𝒬) (hfin : ∀ Q ∈ 𝒬, IsFiniteMeasure Q)
    (h𝒬' : 𝒬' ⊆ 𝒬) : IsTVSeparable 𝒬' := by
  classical
  obtain ⟨D, hD𝒬, hDc, hdense⟩ := h
  have : Countable D := hDc.to_subtype
  -- a member of `𝒬'` near `R`, at precision `1 / (k + 1)`, when there is one
  let near : D × ℕ → Option (Measure X) := fun p ↦
    if hp : ∃ Q ∈ 𝒬', tvDist Q p.1 < 1 / (p.2 + 1) then some hp.choose else none
  refine ⟨{Q | ∃ p, near p = some Q}, ?_, ?_, fun Q hQ ε hε ↦ ?_⟩
  · rintro Q ⟨p, hp⟩
    simp only [near] at hp
    split_ifs at hp with h
    exact Option.some_injective _ hp ▸ h.choose_spec.1
  · exact ((countable_range near).preimage (Option.some_injective _))
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨R, hRD, hQR⟩ := hdense Q (h𝒬' hQ) _ (Nat.one_div_pos_of_nat (n := k))
    have hex : ∃ Q ∈ 𝒬', tvDist Q R < 1 / (k + 1) := ⟨Q, hQ, hQR⟩
    have hnear : near (⟨R, hRD⟩, k) = some hex.choose := dite_eq_left hex
    refine ⟨hex.choose, ⟨_, hnear⟩, ?_⟩
    have : IsFiniteMeasure R := hfin R (hD𝒬 hRD)
    calc tvDist Q hex.choose ≤ tvDist Q R + tvDist R hex.choose := tvDist_triangle _ _ _
      _ < 1 / (k + 1) + 1 / (k + 1) := by
        rw [tvDist_comm R]; exact add_lt_add hQR hex.choose_spec.2
      _ < ε / 2 + ε / 2 := add_lt_add hk hk
      _ = ε := add_halves ε

/-- **Separability implies domination.** A nonempty set of probability measures that is separable
for the total variation distance is dominated by one probability measure: the mixture
`∑ k, 2^{-(k+1)} R k` of a dense sequence `R`. A set of mass zero for the mixture has mass zero
for each `R k`, hence mass less than every `ε` for every member of the set. -/
theorem IsTVSeparable.exists_isProbabilityMeasure_absolutelyContinuous (h : IsTVSeparable 𝒬)
    (hprob : ∀ Q ∈ 𝒬, IsProbabilityMeasure Q) (hne : 𝒬.Nonempty) :
    ∃ ρ : Measure X, IsProbabilityMeasure ρ ∧ ∀ Q ∈ 𝒬, Q ≪ ρ := by
  obtain ⟨D, hD𝒬, hDc, hdense⟩ := h
  obtain ⟨Q₀, hQ₀⟩ := hne
  obtain ⟨R₀, hR₀, -⟩ := hdense Q₀ hQ₀ 1 one_pos
  obtain ⟨R, rfl⟩ := hDc.exists_eq_range ⟨R₀, hR₀⟩
  have hRprob (k : ℕ) : IsProbabilityMeasure (R k) := hprob _ (hD𝒬 ⟨k, rfl⟩)
  let ρ : Measure X := Measure.sum fun k ↦ (2⁻¹ : ℝ≥0∞) ^ (k + 1) • R k
  have hcoef (k : ℕ) : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2
    ENNReal.ofNat_ne_top)
  refine ⟨ρ, ⟨?_⟩, fun Q hQ ↦ Measure.AbsolutelyContinuous.mk fun s hs hρs ↦ ?_⟩
  · rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  · -- each `R k` gives `s` mass zero
    have hR0 (k : ℕ) : R k s = 0 := by
      rw [Measure.sum_apply _ hs, tsum_eq_zero_iff] at hρs
      simpa [smul_apply, hcoef k] using hρs k
    have := hprob Q hQ
    -- `Q s` is less than every `ε > 0`
    have hle : Q.real s ≤ 0 := by
      refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hdense Q hQ ε hε
      have habs := abs_measureReal_sub_measureReal_le_tvDist_div_two
        (by simp : Q Set.univ = R k Set.univ) hs
      have hRk : (R k).real s = 0 := by simp [measureReal_def, hR0 k]
      rw [hRk, sub_zero, abs_of_nonneg measureReal_nonneg] at habs
      linarith
    exact (measureReal_eq_zero_iff (measure_ne_top Q s)).1 (le_antisymm hle measureReal_nonneg)

/-- **On a countably generated space, domination implies separability.** The probability measures
dominated by an s-finite measure `ρ` form a separable set for the total variation distance. Their
densities with respect to the finite measure `ρ.toFinite`, equivalent to `ρ`, lie in `L¹`, which is
separable on a countably generated space; and the total variation distance is at most twice the
`L¹` distance of the densities. -/
theorem isTVSeparable_setOf_absolutelyContinuous [MeasurableSpace.CountablyGenerated X]
    (ρ : Measure X) [SFinite ρ] :
    IsTVSeparable {Q : Measure X | IsProbabilityMeasure Q ∧ Q ≪ ρ} := by
  classical
  set ν := ρ.toFinite
  set 𝒬 := {Q : Measure X | IsProbabilityMeasure Q ∧ Q ≪ ρ}
  by_cases hne : 𝒬.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.1 hne]
    exact isTVSeparable_empty
  have hacν {Q : Measure X} (hQ : Q ∈ 𝒬) : Q ≪ ν := hQ.2.trans (absolutelyContinuous_toFinite ρ)
  -- the density of a member, as a real function
  let dens : Measure X → X → ℝ := fun Q x ↦ (Q.rnDeriv ν x).toReal
  have hint {Q : Measure X} (hQ : Q ∈ 𝒬) : Integrable (dens Q) ν := by
    have := hQ.1
    exact Measure.integrable_toReal_rnDeriv
  set A : Set (Lp ℝ 1 ν) := {v | ∃ Q ∈ 𝒬, (v : X → ℝ) =ᵐ[ν] dens Q}
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  obtain ⟨Q₀, hQ₀⟩ := hne
  have hA : Nonempty A := ⟨⟨(hint hQ₀).toL1 _, Q₀, hQ₀, Integrable.coeFn_toL1 _⟩⟩
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq A
  choose Q hQ hvQ using fun j ↦ (v j).property
  refine ⟨range Q, range_subset_iff.2 hQ, countable_range Q, fun Q' hQ' ε hε ↦ ?_⟩
  set a : A := ⟨(hint hQ').toL1 _, Q', hQ', Integrable.coeFn_toL1 _⟩
  obtain ⟨j, hj⟩ := hv.exists_dist_lt a (half_pos hε)
  refine ⟨Q j, ⟨j, rfl⟩, ?_⟩
  -- the `L¹` distance of the densities
  set c := ∫ x, |dens Q' x - dens (Q j) x| ∂ν
  have hc : c < ε / 2 := by
    have hdist : dist (v j : Lp ℝ 1 ν) (a : Lp ℝ 1 ν) = c := by
      rw [L1.dist_eq_integral_dist]
      refine integral_congr_ae ?_
      filter_upwards [hvQ j, Integrable.coeFn_toL1 (hint hQ')] with x hx hx'
      rw [Real.dist_eq, hx, hx', abs_sub_comm]
    rw [← hdist, ← Subtype.dist_eq, dist_comm]
    exact hj
  have := (hQ' : Q' ∈ 𝒬).1
  have := (hQ j).1
  refine (tvDist_le_two_mul_of_forall_measureReal_le_add (by simp) fun s hs ↦ ?_).trans_lt
    (by linarith)
  rw [← Measure.setIntegral_toReal_rnDeriv (hacν hQ') s,
    ← Measure.setIntegral_toReal_rnDeriv (hacν (hQ j)) s, ← sub_le_iff_le_add',
    ← integral_sub (hint hQ').integrableOn (hint (hQ j)).integrableOn]
  calc ∫ x in s, dens Q' x - dens (Q j) x ∂ν ≤ ∫ x in s, |dens Q' x - dens (Q j) x| ∂ν :=
        integral_mono ((hint hQ').integrableOn.sub (hint (hQ j)).integrableOn)
          ((hint hQ').sub (hint (hQ j))).abs.integrableOn fun x ↦ le_abs_self _
    _ ≤ c := setIntegral_le_integral ((hint hQ').sub (hint (hQ j))).abs
        (ae_of_all _ fun x ↦ abs_nonneg _)

end MeasureTheory
