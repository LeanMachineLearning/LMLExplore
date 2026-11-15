/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
public import Mathlib.Probability.Process.HittingTime

/-!
# Submartingales in `ℝ≥0∞` and Doob's maximal inequality with no integrability

An `ℝ≥0∞`-valued process `M` is a submartingale for a filtration `ℱ` under every member of a set
of measures `S` when it is adapted and `∫⁻ ω in s, M n ω ∂P ≤ ∫⁻ ω in s, M (n + 1) ω ∂P` for every
`P ∈ S`, every `n` and every `ℱ n`-measurable `s`: the definition of
`ProbabilityTheory.IsENNSupermartingale` with the inequality reversed. No integrability is
assumed.

Doob's maximal inequality holds for such processes in the form
`C * P (A ∩ G) ≤ ∫⁻ ω in A ∩ G, M N ω ∂P`, where `A` is the event that `M` reaches the level `C`
at some time between `m` and `N`, and `G` is any `ℱ m`-measurable set. Since `G` is arbitrary,
this bounds the conditional probability of `A` given `ℱ m` by the conditional mean of `M N`
divided by `C`, and by `1`. That bound is informative when `M N` has an infinite mean, as the
extended Ville inequality of Wang and Ramdas is for supermartingales [WR23], who ask for such a
form of Doob's inequality.

## Main definitions

* `ProbabilityTheory.IsENNSubmartingale M ℱ S`: `M` is an `ℝ≥0∞`-valued submartingale for `ℱ`
  under every member of `S`.

## Main statements

* `ProbabilityTheory.IsENNSubmartingale.mul_measure_inter_le_setLIntegral`: Doob's maximal
  inequality on the `ℱ m`-measurable sets, with no integrability.
* `ProbabilityTheory.IsENNSubmartingale.measure_exists_le_le`: Doob's maximal inequality,
  `P {ω | ∃ n ≤ N, C ≤ M n ω} ≤ (∫⁻ ω, M N ω ∂P) / C`.
* `ProbabilityTheory.IsTestMartingale.isENNSubmartingale`: a test martingale is a submartingale.

## References

* [WR23] H. Wang and A. Ramdas, *The extended Ville's inequality for nonintegrable nonnegative
  supermartingales*, arXiv:2304.01163v3.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {M M' : ℕ → Ω → ℝ≥0∞}

/-- `M : ℕ → Ω → ℝ≥0∞` is a submartingale for the filtration `ℱ` under every member of `S`:
it is adapted and `∫⁻ ω in s, M n ω ∂P ≤ ∫⁻ ω in s, M (n + 1) ω ∂P` for every `P ∈ S`, every `n`
and every `ℱ n`-measurable `s`. No integrability is assumed. -/
structure IsENNSubmartingale (M : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ M
  setLIntegral_le_succ : ∀ P ∈ S, ∀ n s, MeasurableSet[ℱ n] s →
    ∫⁻ ω in s, M n ω ∂P ≤ ∫⁻ ω in s, M (n + 1) ω ∂P

/-- A test martingale is a submartingale under every member of the null. -/
theorem IsTestMartingale.isENNSubmartingale (hM : IsTestMartingale M ℱ S) :
    IsENNSubmartingale M ℱ S :=
  ⟨hM.adapted, fun P hP n s hs ↦ (hM.setLIntegral_succ_eq P hP n s hs).ge⟩

namespace IsENNSubmartingale

/-- Each value of an `ℝ≥0∞`-valued submartingale is measurable. -/
theorem measurable (hM : IsENNSubmartingale M ℱ S) (n : ℕ) : Measurable (M n) :=
  (hM.adapted n).mono (ℱ.le n) le_rfl

/-- A submartingale under every member of `T` is one under every member of a subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hM : IsENNSubmartingale M ℱ T) : IsENNSubmartingale M ℱ S :=
  ⟨hM.adapted, fun P hP ↦ hM.setLIntegral_le_succ P (hST hP)⟩

/-- An adapted process almost surely equal at every time to a submartingale, under every member
of the null, is a submartingale. -/
theorem congr (hM : IsENNSubmartingale M ℱ S) (hM' : Adapted ℱ M')
    (h : ∀ P ∈ S, ∀ n, M n =ᵐ[P] M' n) : IsENNSubmartingale M' ℱ S :=
  ⟨hM', fun P hP n s hs ↦ by
    rw [← lintegral_congr_ae (ae_restrict_of_ae (h P hP (n + 1))),
      ← lintegral_congr_ae (ae_restrict_of_ae (h P hP n))]
    exact hM.setLIntegral_le_succ P hP n s hs⟩

/-- The set integrals of an `ℝ≥0∞`-valued submartingale over an `ℱ i`-measurable set do not
decrease after time `i`. -/
theorem setLIntegral_le (hM : IsENNSubmartingale M ℱ S) (hP : P ∈ S) {i j : ℕ} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫⁻ ω in s, M i ω ∂P ≤ ∫⁻ ω in s, M j ω ∂P := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact ih.trans (hM.setLIntegral_le_succ P hP j s (ℱ.mono hij s hs))

/-- The expectations of an `ℝ≥0∞`-valued submartingale do not decrease. -/
theorem lintegral_le (hM : IsENNSubmartingale M ℱ S) (hP : P ∈ S) {i j : ℕ} (hij : i ≤ j) :
    ∫⁻ ω, M i ω ∂P ≤ ∫⁻ ω, M j ω ∂P := by
  simpa using hM.setLIntegral_le hP hij MeasurableSet.univ

/-- **Doob's maximal inequality with no integrability**: for an `ℝ≥0∞`-valued submartingale `M`,
times `m` and `N`, a level `C`, the event `A` that `M n` reaches `C` for some `n` between `m` and
`N`, and an `ℱ m`-measurable set `G`, `C * P (A ∩ G) ≤ ∫⁻ ω in A ∩ G, M N ω ∂P`. -/
theorem mul_measure_inter_le_setLIntegral (hM : IsENNSubmartingale M ℱ S) (hP : P ∈ S)
    (m N : ℕ) (C : ℝ≥0∞) {G : Set Ω} (hG : MeasurableSet[ℱ m] G) :
    C * P ({ω | ∃ n ∈ Finset.Icc m N, C ≤ M n ω} ∩ G) ≤
      ∫⁻ ω in {ω | ∃ n ∈ Finset.Icc m N, C ≤ M n ω} ∩ G, M N ω ∂P := by
  -- split `A` according to the first time `τ` from `m` on at which `M` reaches `C`
  set τ : Ω → ℕ := hittingBtwn M (Set.Ici C) m N
  set B : ℕ → Set Ω := fun k ↦ τ ⁻¹' {k} ∩ ({ω | C ≤ M k ω} ∩ G)
  have hBG : ∀ k ∈ Finset.Icc m N, MeasurableSet[ℱ k] (B k) := fun k hk ↦ by
    have hτ := (Adapted.isStoppingTime_hittingBtwn (s := Set.Ici C) (n := m) (n' := N)
      hM.adapted measurableSet_Ici).measurableSet_eq k
    simp only [WithTop.coe_inj] at hτ
    exact hτ.inter ((hM.adapted k measurableSet_Ici).inter (ℱ.mono (Finset.mem_Icc.1 hk).1 _ hG))
  have hmeas : ∀ k ∈ Finset.Icc m N, MeasurableSet (B k) := fun k hk ↦ ℱ.le k _ (hBG k hk)
  have hunion : {ω | ∃ n ∈ Finset.Icc m N, C ≤ M n ω} ∩ G = ⋃ k ∈ Finset.Icc m N, B k := by
    ext ω
    simp only [B, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    refine ⟨fun ⟨⟨n, hn, hCn⟩, hωG⟩ ↦ ?_, fun ⟨k, hk, _, hCk, hωG⟩ ↦ ⟨⟨k, hk, hCk⟩, hωG⟩⟩
    have hn' := Finset.mem_Icc.1 hn
    exact ⟨τ ω, Finset.mem_Icc.2 (hittingBtwn_mem_Icc (hn'.1.trans hn'.2) ω), rfl,
      hittingBtwn_mem_set (s := Set.Ici C) ⟨n, hn', hCn⟩, hωG⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc m N)) B :=
    (Set.pairwiseDisjoint_fiber τ _).mono fun _ ↦ Set.inter_subset_left
  rw [hunion, measure_biUnion_finset hdisj hmeas, lintegral_biUnion_finset hdisj hmeas,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  calc C * P (B k) = ∫⁻ _ in B k, C ∂P := by rw [setLIntegral_const]
    _ ≤ ∫⁻ ω in B k, M k ω ∂P := setLIntegral_mono' (hmeas k hk) fun ω hω ↦ hω.2.1
    _ ≤ ∫⁻ ω in B k, M N ω ∂P := hM.setLIntegral_le hP (Finset.mem_Icc.1 hk).2 (hBG k hk)

/-- **Doob's maximal inequality** for an `ℝ≥0∞`-valued submartingale: the probability that `M`
reaches the level `C` by time `N` is at most the mean of `M N` divided by `C`. -/
theorem measure_exists_le_le (hM : IsENNSubmartingale M ℱ S) (hP : P ∈ S) (N : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hC' : C ≠ ∞) :
    P {ω | ∃ n ≤ N, C ≤ M n ω} ≤ (∫⁻ ω, M N ω ∂P) / C := by
  have h := hM.mul_measure_inter_le_setLIntegral hP 0 N C (G := Set.univ) MeasurableSet.univ
  simp only [Finset.mem_Icc, zero_le, true_and, Set.inter_univ] at h
  rw [ENNReal.le_div_iff_mul_le (Or.inl hC) (Or.inl hC'), mul_comm]
  exact h.trans (setLIntegral_le_lintegral _ _)

end IsENNSubmartingale

end ProbabilityTheory
