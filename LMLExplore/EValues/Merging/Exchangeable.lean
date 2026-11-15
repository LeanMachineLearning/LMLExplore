/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.EVariable
public import TauCeti.Probability.Exchangeability.Family
import Mathlib.Data.Fintype.Perm

/-!
# Merging functions for exchangeable e-values

A merging function for exchangeable e-values indexed by `ι` is a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every probability measure `μ` on `ι → ℝ≥0∞`
that is invariant under the permutations of the coordinates and whose coordinates have expectation
at most `1`. It turns e-variables that form an exchangeable family under every member of the null
into an e-variable (`ProbabilityTheory.IsExchangeableEMerging.isEVar_comp`). No monotonicity is
assumed.

For `ι = Fin K`, a measurable `F` is a merging function for exchangeable e-values exactly when its
symmetrization, the average of `F` over the orderings of its arguments, is at most a convex
combination `(1 - l) + l * mean` of `1` and the arithmetic mean, at every point with finite
coordinates.

The exchangeable Markov inequality of Ramdas and Manole [RM26] says that
`β * 𝟙{some running mean reaches β}` is such a function, where the running means are the means of
the first `k + 1` e-values. Wang asks whether it is admissible [Wan25, Section 4 (d)]. It is not:
its maximum with the smallest e-value is a monotone merging function for exchangeable e-values,
which dominates it and differs from it.

## Main definitions

* `ProbabilityTheory.IsExchangeableEMerging F`: `F` is a merging function for exchangeable
  e-values.
* `ProbabilityTheory.runningMeanTest β`: the function `β * 𝟙{some running mean reaches β}` of
  `K` e-values.

## Main statements

* `ProbabilityTheory.IsExchangeableEMerging.isEVar_comp`: a merging function for exchangeable
  e-values of an exchangeable family of e-variables is an e-variable.
* `ProbabilityTheory.isExchangeableEMerging_iff`: the characterization by the symmetrization.
* `ProbabilityTheory.isExchangeableEMerging_runningMeanTest`: the exchangeable Markov inequality
  [RM26].
* `ProbabilityTheory.exists_isExchangeableEMerging_monotone_runningMeanTest_lt`: the function of
  the exchangeable Markov inequality is not admissible.

## Implementation notes

The direction "merging implies the bound" of `isExchangeableEMerging_iff` tests `F` against the
mixtures of the uniform laws on the orbits of two points, and finds the constant `l` as an infimum
of slopes. The exchangeable Markov inequality is proved in its orbit form: among the orderings of
a point for which some running mean reaches `β`, the sum of the first coordinates is at least `β`
times their number. The proof splits these orderings according to the last prefix whose mean
reaches `β`, an event that is invariant under the permutations of that prefix.

## References

* [RM26] A. Ramdas and T. Manole, *Randomized and exchangeable improvements of Markov's,
  Chebyshev's and Chernoff's inequalities*, Statist. Sci. 41 (2026), arXiv:2304.02611v3.
* [Wan25] R. Wang, *The only admissible way of merging arbitrary e-values*, Biometrika (2025),
  arXiv:2409.19888v2: Section 4 (d).
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### Merging functions for exchangeable e-values -/

section Definition

variable {ι : Type*} {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A **merging function for exchangeable e-values** indexed by `ι`: a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every probability measure `μ` on
`ι → ℝ≥0∞` that is invariant under the permutations of the coordinates and whose coordinates have
expectation at most `1`. It is not required to be monotone. -/
structure IsExchangeableEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : Measure (ι → ℝ≥0∞)) [IsProbabilityMeasure μ],
    (∀ σ : Equiv.Perm ι, μ.map (fun e ↦ e ∘ σ) = μ) → (∀ i, ∫⁻ e, e i ∂μ ≤ 1) →
    ∫⁻ e, F e ∂μ ≤ 1

/-- A measurable function below a merging function for exchangeable e-values is one. -/
theorem IsExchangeableEMerging.mono (hG : IsExchangeableEMerging G) (hF : Measurable F)
    (hle : F ≤ G) : IsExchangeableEMerging F :=
  ⟨hF, fun μ _ hσ hμ ↦ (lintegral_mono hle).trans (hG.lintegral_le_one μ hσ hμ)⟩

/-- A merging function for exchangeable e-values, applied to e-variables that form an exchangeable
family under every member of the null, is an e-variable. -/
theorem IsExchangeableEMerging.isEVar_comp [Countable ι] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : Set (Measure Ω)} (hF : IsExchangeableEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ι → Ω → ℝ≥0∞} (hE : ∀ i, IsEVar (E i) S) (hexch : ∀ P ∈ S, ExchangeableFamily P E) :
    IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  have hm : Measurable fun ω i ↦ E i ω := measurable_pi_iff.2 fun i ↦ (hE i).measurable
  refine IsEVar.of_lintegral_le_one hS (hF.measurable.comp hm) fun P hP ↦ ?_
  have := hS P hP
  rw [← lintegral_map hF.measurable hm]
  refine hF.lintegral_le_one _ (fun σ ↦ ?_) fun i ↦ ?_
  · -- the law of an exchangeable family is invariant under the permutations of the coordinates
    have hσ : Measurable fun e : ι → ℝ≥0∞ ↦ e ∘ σ :=
      measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
    rw [Measure.map_map hσ hm]
    exact (hexch P hP).map_eq_of_injective (fun i ↦ (hE i).measurable.aemeasurable) σ.injective
      Function.injective_id
  · rw [lintegral_map (measurable_pi_apply i) hm]
    simpa using (hE i).lintegral_le_measure_univ P hP

end Definition

/-! ### The characterization by the symmetrization -/

variable {K : ℕ}

/-- Summing `E (σ i)` over all permutations `σ` gives a result that does not depend on `i`. -/
private lemma sum_perm_apply_eq_sum_perm_apply {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (E : ι → M) (i j : ι) :
    ∑ σ : Equiv.Perm ι, E (σ i) = ∑ σ : Equiv.Perm ι, E (σ j) :=
  Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun σ ↦ by simp

/-- Summing `E (σ i)` over all permutations `σ` counts every `E j` exactly `(n - 1)!` times,
where `n` is the number of indices. -/
private lemma card_nsmul_sum_perm_apply {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (E : ι → M) (i : ι) :
    Fintype.card ι • ∑ σ : Equiv.Perm ι, E (σ i) = (Fintype.card ι).factorial • ∑ j, E j := by
  calc Fintype.card ι • ∑ σ : Equiv.Perm ι, E (σ i)
      = ∑ j : ι, ∑ σ : Equiv.Perm ι, E (σ j) := by
        rw [← Finset.card_univ, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun j _ ↦ sum_perm_apply_eq_sum_perm_apply E i j
    _ = ∑ σ : Equiv.Perm ι, ∑ j, E (σ j) := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm ι, ∑ j, E j := Finset.sum_congr rfl fun σ _ ↦ Equiv.sum_comp σ E
    _ = (Fintype.card ι).factorial • ∑ j, E j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]

/-- The average of `E (σ i)` over the permutations `σ` of `Fin K` is the mean of `E`. -/
private lemma sum_perm_apply_div_factorial (E : Fin K → ℝ≥0∞) (i : Fin K) :
    (∑ σ : Equiv.Perm (Fin K), E (σ i)) / K.factorial = (∑ j, E j) / K := by
  have hK : (K : ℝ≥0∞) ≠ 0 := by simpa using (Fin.pos i).ne'
  rw [ENNReal.div_eq_div_iff hK (by simp) (by simp [Nat.factorial_ne_zero]) (by simp)]
  simpa [nsmul_eq_mul] using card_nsmul_sum_perm_apply E i

/-- The uniform law on the orbit of `E` under the permutations of the coordinates. -/
private noncomputable def orbitMeasure (E : Fin K → ℝ≥0∞) : Measure (Fin K → ℝ≥0∞) :=
  (K.factorial : ℝ≥0∞)⁻¹ • ∑ σ : Equiv.Perm (Fin K), Measure.dirac fun i ↦ E (σ i)

/-- The integral against the uniform law on an orbit is the average over the orbit. -/
private lemma lintegral_orbitMeasure (E : Fin K → ℝ≥0∞) (g : (Fin K → ℝ≥0∞) → ℝ≥0∞) :
    ∫⁻ x, g x ∂orbitMeasure E = (∑ σ : Equiv.Perm (Fin K), g fun i ↦ E (σ i)) / K.factorial := by
  simp only [orbitMeasure, lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac,
    smul_eq_mul]
  rw [ENNReal.div_eq_inv_mul]

/-- The uniform law on an orbit is a probability measure. -/
private lemma orbitMeasure_univ (E : Fin K → ℝ≥0∞) : orbitMeasure E Set.univ = 1 := by
  rw [← lintegral_one, lintegral_orbitMeasure E fun _ ↦ 1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact ENNReal.div_self (by simp [Nat.factorial_ne_zero]) (by simp)

/-- The uniform law on an orbit is invariant under the permutations of the coordinates. -/
private lemma map_orbitMeasure (E : Fin K → ℝ≥0∞) (τ : Equiv.Perm (Fin K)) :
    (orbitMeasure E).map (fun e ↦ e ∘ τ) = orbitMeasure E := by
  have hτ : Measurable fun e : Fin K → ℝ≥0∞ ↦ e ∘ τ :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply _
  rw [orbitMeasure, Measure.map_smul _ hτ.aemeasurable, Measure.map_finset_sum' hτ.aemeasurable]
  simp_rw [Measure.map_dirac]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ ↦ rfl

/-- The coordinate means of the uniform law on the orbit of `E` are the mean of `E`. -/
private lemma lintegral_apply_orbitMeasure (E : Fin K → ℝ≥0∞) (i : Fin K) :
    ∫⁻ x, x i ∂orbitMeasure E = (∑ j, E j) / K := by
  rw [lintegral_orbitMeasure E fun x ↦ x i, sum_perm_apply_div_factorial]

/-- If `F` is a merging function for exchangeable e-values, then for every mixture with weights
`p` and `q` of the uniform laws on the orbits of `E` and `E'` whose coordinate means are at most
one, the corresponding mixture of the symmetrizations of `F` at `E` and `E'` is at most one. -/
private lemma mix_le_one_of_isExchangeableEMerging {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) (E E' : Fin K → ℝ≥0∞) {p q : ℝ≥0∞} (hpq : p + q = 1)
    (h : p * ((∑ i, E i) / K) + q * ((∑ i, E' i) / K) ≤ 1) :
    p * ((∑ σ : Equiv.Perm (Fin K), F fun i ↦ E (σ i)) / K.factorial) +
      q * ((∑ σ : Equiv.Perm (Fin K), F fun i ↦ E' (σ i)) / K.factorial) ≤ 1 := by
  have hτ : ∀ τ : Equiv.Perm (Fin K), Measurable fun e : Fin K → ℝ≥0∞ ↦ e ∘ τ :=
    fun τ ↦ measurable_pi_iff.mpr fun i ↦ measurable_pi_apply _
  have hprob : IsProbabilityMeasure (p • orbitMeasure E + q • orbitMeasure E') :=
    ⟨by simp [orbitMeasure_univ, hpq]⟩
  have := hF.lintegral_le_one (p • orbitMeasure E + q • orbitMeasure E') (fun τ ↦ by
      rw [Measure.map_add _ _ (hτ τ), Measure.map_smul _ (hτ τ).aemeasurable,
        Measure.map_smul _ (hτ τ).aemeasurable, map_orbitMeasure, map_orbitMeasure])
    (fun i ↦ by
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_apply_orbitMeasure, lintegral_apply_orbitMeasure]
      exact h)
  rwa [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_orbitMeasure, lintegral_orbitMeasure] at this

/-- A real-valued version of the supporting-line argument: if every mixture of two points whose
`m`-value is at most one has `a`-value at most one, and some point has `m`-value zero and
nonnegative `a`-value, then `a ≤ (1 - l) + l m` for some `l ∈ [0, 1]`. -/
private lemma exists_le_one_sub_add_mul_of_mix {X : Type*} (m a : X → ℝ) (x₀ : X)
    (hm₀ : m x₀ = 0) (ha₀ : 0 ≤ a x₀)
    (hmix : ∀ x y (p : ℝ), 0 ≤ p → p ≤ 1 → p * m x + (1 - p) * m y ≤ 1 →
      p * a x + (1 - p) * a y ≤ 1) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ ∀ x, a x ≤ 1 - l + l * m x := by
  have ha1 : ∀ x, m x ≤ 1 → a x ≤ 1 := fun x hx ↦ by
    simpa using hmix x x 1 zero_le_one le_rfl (by simpa using hx)
  have hmix' : ∀ x y (p q : ℝ), 0 ≤ p → 0 ≤ q → 0 < p + q → p * m x + q * m y ≤ p + q →
      p * a x + q * a y ≤ p + q := by
    intro x y p q hp hq hpq h
    have hq' : 1 - p / (p + q) = q / (p + q) := by field_simp; ring
    have := hmix x y (p / (p + q)) (div_nonneg hp hpq.le) (div_le_one_of_le₀ (by linarith) hpq.le)
      (by rw [hq', div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hpq]
          exact h)
    rwa [hq', div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hpq] at this
  -- the constant `l` is the smallest slope `(1 - a x) / (1 - m x)` over the points with `m x < 1`
  let S := {x // m x < 1}
  have hS : Nonempty S := ⟨⟨x₀, by simp [hm₀]⟩⟩
  let s : S → ℝ := fun x ↦ (1 - a x) / (1 - m x)
  have hs0 : ∀ x : S, 0 ≤ s x := fun x ↦
    div_nonneg (by linarith [ha1 x x.2.le]) (by linarith [x.2])
  have hbdd : BddBelow (Set.range s) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hs0 x⟩
  refine ⟨⨅ x : S, s x, le_ciInf hs0, ?_, fun x ↦ ?_⟩
  · calc ⨅ x : S, s x ≤ s ⟨x₀, by simp [hm₀]⟩ := ciInf_le hbdd _
      _ = 1 - a x₀ := by simp [s, hm₀]
      _ ≤ 1 := by linarith
  rcases lt_trichotomy (m x) 1 with hx | hx | hx
  · have := ciInf_le hbdd ⟨x, hx⟩
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  · rw [hx]
    linarith [ha1 x hx.le]
  · have key : (a x - 1) / (m x - 1) ≤ ⨅ y : S, s y := by
      refine le_ciInf fun y ↦ ?_
      have hy : m y < 1 := y.2
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have := hmix' y x (m x - 1) (1 - m y) (by linarith) (by linarith) (by linarith)
        (le_of_eq (by ring))
      nlinarith
    rw [div_le_iff₀ (by linarith)] at key
    linarith

/-- The symmetrization of a merging function for exchangeable e-values is at most
`(1 - l) + l * mean` at every point with finite coordinates, for some `l ≤ 1`. -/
theorem IsExchangeableEMerging.exists_sum_perm_div_le {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) :
    ∃ l : ℝ≥0∞, l ≤ 1 ∧ ∀ e : Fin K → ℝ≥0,
      (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / (K.factorial : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (K : ℝ≥0∞)) := by
  let M : (Fin K → ℝ≥0) → ℝ≥0∞ := fun e ↦ (∑ i, (e i : ℝ≥0∞)) / K
  let A : (Fin K → ℝ≥0) → ℝ≥0∞ := fun e ↦
    (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / K.factorial
  have hmix : ∀ e e' p q, p + q = 1 → p * M e + q * M e' ≤ 1 → p * A e + q * A e' ≤ 1 :=
    fun e e' _ _ hpq h ↦ mix_le_one_of_isExchangeableEMerging hF (fun i ↦ e i) (fun i ↦ e' i) hpq h
  have hM_top : ∀ e, M e ≠ ⊤ := by
    intro e
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [M]
    · exact ENNReal.div_ne_top (by simp) (Nat.cast_ne_zero.mpr hK.ne')
  have hM₀ : M 0 = 0 := by simp [M]
  -- the symmetrization is finite: mix the orbit of `e` with the point `0`
  have hA_top : ∀ e, A e ≠ ⊤ := by
    intro e htop
    have hp : (M e + 1)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr le_add_self
    have h := hmix e 0 _ _ (add_tsub_cancel_of_le hp) (by
      rw [hM₀, mul_zero, add_zero]
      calc (M e + 1)⁻¹ * M e ≤ (M e + 1)⁻¹ * (M e + 1) := by gcongr; exact le_self_add
        _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp [hM_top e]))
    rw [htop, ENNReal.mul_top (by simp [hM_top e])] at h
    simp at h
  obtain ⟨l, hl₀, hl₁, hl⟩ := exists_le_one_sub_add_mul_of_mix (fun e ↦ (M e).toReal)
    (fun e ↦ (A e).toReal) 0 (by simp [hM₀]) ENNReal.toReal_nonneg (by
      intro e e' p hp₀ hp₁ h
      have hpq : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
        rw [← ENNReal.ofReal_add hp₀ (by linarith)]
        simp
      have h' := hmix e e' _ _ hpq (by
        rw [← ENNReal.ofReal_toReal (hM_top e), ← ENNReal.ofReal_toReal (hM_top e'),
          ← ENNReal.ofReal_mul hp₀, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) ENNReal.toReal_nonneg)]
        exact ENNReal.ofReal_le_one.mpr h)
      have := ENNReal.toReal_mono ENNReal.one_ne_top h'
      rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hA_top e))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hA_top e')), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hp₀, ENNReal.toReal_ofReal (by linarith),
        ENNReal.toReal_one] at this)
  refine ⟨ENNReal.ofReal l, ENNReal.ofReal_le_one.mpr hl₁, fun e ↦ ?_⟩
  calc A e = ENNReal.ofReal (A e).toReal := (ENNReal.ofReal_toReal (hA_top e)).symm
    _ ≤ ENNReal.ofReal (1 - l + l * (M e).toReal) := ENNReal.ofReal_le_ofReal (hl e)
    _ = (1 - ENNReal.ofReal l) + ENNReal.ofReal l * M e := by
      rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_sub _ hl₀,
        ENNReal.ofReal_one, ENNReal.ofReal_mul hl₀, ENNReal.ofReal_toReal (hM_top e)]

/-- A measurable function whose symmetrization is at most `(1 - l) + l * mean` at every point
with finite coordinates, for some `l ≤ 1`, is a merging function for exchangeable e-values. -/
theorem isExchangeableEMerging_of_sum_perm_div_le {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : Measurable F) {l : ℝ≥0∞} (hl : l ≤ 1)
    (h : ∀ e : Fin K → ℝ≥0,
      (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / (K.factorial : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (K : ℝ≥0∞))) :
    IsExchangeableEMerging F := by
  refine ⟨hF, fun μ hμ hexch hmean ↦ ?_⟩
  have hτ : ∀ τ : Equiv.Perm (Fin K), Measurable fun e : Fin K → ℝ≥0∞ ↦ fun i ↦ e (τ i) :=
    fun τ ↦ measurable_pi_iff.mpr fun i ↦ measurable_pi_apply _
  have hFτ : ∀ τ : Equiv.Perm (Fin K), Measurable fun e : Fin K → ℝ≥0∞ ↦ F fun i ↦ e (τ i) :=
    fun τ ↦ hF.comp (hτ τ)
  have hinv : ∀ τ : Equiv.Perm (Fin K), ∫⁻ e, F (fun i ↦ e (τ i)) ∂μ = ∫⁻ e, F e ∂μ := by
    intro τ
    rw [← lintegral_map hF (hτ τ)]
    exact congrArg (fun ν ↦ ∫⁻ e, F e ∂ν) (hexch τ)
  have hfin : ∀ᵐ e ∂μ, ∀ i, e i ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ae_lt_top (measurable_pi_apply i)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hmean i))] with e he using he.ne
  have hK : (K.factorial : ℝ≥0∞) ≠ 0 := by simp [Nat.factorial_ne_zero]
  have hsum : Measurable fun e : Fin K → ℝ≥0∞ ↦ ∑ i, e i :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  calc ∫⁻ e, F e ∂μ
      = ∫⁻ e, (K.factorial : ℝ≥0∞)⁻¹ * ∑ σ : Equiv.Perm (Fin K), F (fun i ↦ e (σ i)) ∂μ := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun σ _ ↦ hFτ σ),
          lintegral_finsetSum _ fun σ _ ↦ hFτ σ]
        simp_rw [hinv]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, ENNReal.inv_mul_cancel hK (by simp), one_mul]
    _ ≤ ∫⁻ e, (1 - l) + l * ((∑ i, e i) * (K : ℝ≥0∞)⁻¹) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfin] with e he
        have := h fun i ↦ (e i).toNNReal
        simp only [ENNReal.coe_toNNReal (he _)] at this
        rwa [mul_comm, ← div_eq_mul_inv, ← div_eq_mul_inv]
    _ = (1 - l) + l * ((∑ i, ∫⁻ e, e i ∂μ) / K) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (hsum.mul_const _), lintegral_mul_const _ hsum,
          lintegral_finsetSum _ fun i _ ↦ measurable_pi_apply i, div_eq_mul_inv]
    _ ≤ (1 - l) + l * 1 := by
        gcongr
        refine ENNReal.div_le_of_le_mul ?_
        calc ∑ i, ∫⁻ e, e i ∂μ ≤ ∑ _ : Fin K, (1 : ℝ≥0∞) := Finset.sum_le_sum fun i _ ↦ hmean i
          _ = 1 * K := by simp
    _ = 1 := by rw [mul_one, tsub_add_cancel_of_le hl]

/-- **The merging functions for exchangeable e-values**: a function of `K` e-values is one exactly
when it is measurable and, for some `l ≤ 1`, its symmetrization is at most `(1 - l) + l * mean`
at every point with finite coordinates. -/
theorem isExchangeableEMerging_iff (F : (Fin K → ℝ≥0∞) → ℝ≥0∞) :
    IsExchangeableEMerging F ↔ Measurable F ∧ ∃ l : ℝ≥0∞, l ≤ 1 ∧ ∀ e : Fin K → ℝ≥0,
      (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / (K.factorial : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (K : ℝ≥0∞)) :=
  ⟨fun hF ↦ ⟨hF.measurable, hF.exists_sum_perm_div_le⟩,
    fun ⟨hF, _, hl, h⟩ ↦ isExchangeableEMerging_of_sum_perm_div_le hF hl h⟩

/-! ### The exchangeable Markov inequality -/

/-- The function `β * 𝟙{some running mean reaches β}` of `K` e-values [RM26]: its value is `β`
when, for some `k`, the mean of the first `k + 1` e-values is at least `β`, and `0` otherwise. -/
noncomputable def runningMeanTest (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) : ℝ≥0∞ :=
  Set.indicator {e : Fin K → ℝ≥0∞ | ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Finset.Iic k, e j}
    (fun _ ↦ β) e

/-- The function `β * 𝟙{some running mean reaches β}` is measurable. -/
theorem measurable_runningMeanTest (β : ℝ≥0∞) : Measurable (runningMeanTest (K := K) β) := by
  refine measurable_const.indicator ?_
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun k ↦ measurableSet_le measurable_const
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- The function `β * 𝟙{some running mean reaches β}` is monotone. -/
theorem monotone_runningMeanTest (β : ℝ≥0∞) : Monotone (runningMeanTest (K := K) β) := by
  intro e e' h
  simp only [runningMeanTest, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with he he'
  · exact le_rfl
  · obtain ⟨k, hk⟩ := he
    exact absurd ⟨k, hk.trans (Finset.sum_le_sum fun j _ ↦ h j)⟩ he'
  · exact zero_le
  · exact le_rfl

open Finset in
/-- The orbit form of the exchangeable Markov inequality: if `A` is the set of orderings `σ` of
`e` for which some running mean reaches `β`, then `β * #A ≤ ∑ σ ∈ A, e (σ 0)`. The proof splits
`A` according to the last prefix whose mean reaches `β`; that event is invariant under the
permutations of the prefix, so on it the first coordinate has the same sum as the prefix mean. -/
private lemma mul_card_le_sum_apply_zero_of_runningMean [NeZero K] (β : ℝ≥0∞)
    (e : Fin K → ℝ≥0∞) :
    β * #{σ : Equiv.Perm (Fin K) | ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)} ≤
      ∑ σ : Equiv.Perm (Fin K) with ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j),
        e (σ 0) := by
  classical
  let P : Fin K → Equiv.Perm (Fin K) → Prop := fun k σ ↦
    β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)
  let B : Fin K → Finset (Equiv.Perm (Fin K)) := fun k ↦ {σ | P k σ ∧ ∀ j, k < j → ¬ P j σ}
  have hunion : ({σ | ∃ k, P k σ} : Finset (Equiv.Perm (Fin K))) = univ.biUnion B := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, B]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk, _⟩ ↦ ⟨k, hk⟩⟩
    have hne : ({j | P j σ} : Finset (Fin K)).Nonempty := ⟨k, by simpa using hk⟩
    refine ⟨_, (mem_filter.mp (max'_mem _ hne)).2, fun j hj hPj ↦ ?_⟩
    exact absurd (le_max' _ j (by simpa using hPj)) (not_le.mpr hj)
  have hdisj : ((univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint B := by
    intro k _ k' _ hkk'
    refine disjoint_left.mpr fun σ hσ hσ' ↦ ?_
    simp only [mem_filter, mem_univ, true_and, B] at hσ hσ'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact hσ.2 k' h hσ'.1
    · exact hσ'.2 k h hσ.1
  -- the event that `k` is the last prefix whose mean reaches `β` is invariant under the swaps
  -- of `0` with an index of the prefix
  have hswap : ∀ k i : Fin K, i ≤ k → ∀ σ ∈ B k, σ * Equiv.swap 0 i ∈ B k := by
    intro k i hi σ hσ
    have hsum : ∀ j, k ≤ j →
        ∑ l ∈ Iic j, e ((σ * Equiv.swap 0 i) l) = ∑ l ∈ Iic j, e (σ l) := by
      intro j hj
      refine Equiv.Perm.sum_comp (Equiv.swap 0 i) (Iic j) (fun l ↦ e (σ l)) fun a ha ↦ ?_
      have : a = 0 ∨ a = i := by
        by_contra h
        push Not at h
        exact ha (Equiv.swap_apply_of_ne_of_ne h.1 h.2)
      rw [coe_Iic, Set.mem_Iic]
      rcases this with rfl | rfl
      · exact Fin.zero_le _
      · exact hi.trans hj
    have hP : ∀ j, k ≤ j → (P j (σ * Equiv.swap 0 i) ↔ P j σ) := fun j hj ↦ by
      simp only [P, hsum j hj]
    simp only [mem_filter, mem_univ, true_and, B] at hσ ⊢
    exact ⟨(hP k le_rfl).2 hσ.1, fun j hj ↦ by rw [hP j hj.le]; exact hσ.2 j hj⟩
  have hB : ∀ k, β * #(B k) ≤ ∑ σ ∈ B k, e (σ 0) := by
    intro k
    have hsym : ∀ i ∈ Iic k, ∑ σ ∈ B k, e (σ i) = ∑ σ ∈ B k, e (σ 0) := by
      intro i hi
      rw [mem_Iic] at hi
      exact sum_nbij' (· * Equiv.swap 0 i) (· * Equiv.swap 0 i) (hswap k i hi) (hswap k i hi)
        (fun σ _ ↦ by simp) (fun σ _ ↦ by simp) (fun σ _ ↦ by simp)
    refine (ENNReal.mul_le_mul_iff_right (a := (((k : ℕ) + 1 : ℕ) : ℝ≥0∞)) (by simp)
      (by simp)).mp ?_
    calc (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * (β * #(B k))
        = ∑ σ ∈ B k, β * ((k : ℕ) + 1 : ℕ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ σ ∈ B k, ∑ j ∈ Iic k, e (σ j) := sum_le_sum fun σ hσ ↦ (mem_filter.mp hσ).2.1
      _ = ∑ j ∈ Iic k, ∑ σ ∈ B k, e (σ j) := sum_comm
      _ = ∑ j ∈ Iic k, ∑ σ ∈ B k, e (σ 0) := sum_congr rfl hsym
      _ = (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * ∑ σ ∈ B k, e (σ 0) := by
        rw [sum_const, Fin.card_Iic, nsmul_eq_mul]
  change β * #({σ | ∃ k, P k σ} : Finset _) ≤ ∑ σ ∈ ({σ | ∃ k, P k σ} : Finset _), e (σ 0)
  rw [hunion, card_biUnion hdisj, sum_biUnion hdisj, Nat.cast_sum, mul_sum]
  exact sum_le_sum fun k _ ↦ hB k

open Finset in
/-- The symmetrization of `max (runningMeanTest β) (min_k e_k)` at `e` is at most the mean of
`e`, in the form `∑ σ, G (e ∘ σ) ≤ ∑ σ, e (σ 0)`. -/
private lemma sum_perm_max_runningMeanTest_iInf_le [NeZero K] (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    ∑ σ : Equiv.Perm (Fin K), max (runningMeanTest β fun i ↦ e (σ i)) (⨅ k, e (σ k)) ≤
      ∑ σ : Equiv.Perm (Fin K), e (σ 0) := by
  classical
  have hc : ∀ σ : Equiv.Perm (Fin K), ⨅ k, e (σ k) = ⨅ k, e k := fun σ ↦ Equiv.iInf_comp σ
  simp_rw [hc]
  rw [← sum_filter_add_sum_filter_not univ
      (fun σ : Equiv.Perm (Fin K) ↦ ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)),
    ← sum_filter_add_sum_filter_not univ
      (fun σ : Equiv.Perm (Fin K) ↦ ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j))
      (fun σ ↦ e (σ 0))]
  refine add_le_add ?_ (sum_le_sum fun σ hσ ↦ ?_)
  · rw [sum_congr rfl fun σ hσ ↦ by
      rw [runningMeanTest, Set.indicator_of_mem (mem_filter.mp hσ).2], sum_const, nsmul_eq_mul]
    rcases le_total β (⨅ k, e k) with h | h
    · rw [max_eq_right h, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun σ _ ↦ iInf_le _ _
    · rw [max_eq_left h, mul_comm]
      exact mul_card_le_sum_apply_zero_of_runningMean β e
  · rw [runningMeanTest, Set.indicator_of_notMem (mem_filter.mp hσ).2, max_eq_right zero_le]
    exact iInf_le _ _

/-- The maximum of `β * 𝟙{some running mean reaches β}` and the smallest e-value is a merging
function for exchangeable e-values. -/
theorem isExchangeableEMerging_max_runningMeanTest_iInf [NeZero K] (β : ℝ≥0∞) :
    IsExchangeableEMerging fun e : Fin K → ℝ≥0∞ ↦ max (runningMeanTest β e) (⨅ k, e k) := by
  refine isExchangeableEMerging_of_sum_perm_div_le ((measurable_runningMeanTest β).max
    (Measurable.iInf fun k ↦ measurable_pi_apply k)) le_rfl fun e ↦ ?_
  rw [tsub_self, zero_add, one_mul, ← sum_perm_apply_div_factorial (fun i ↦ (e i : ℝ≥0∞)) 0]
  exact ENNReal.div_le_div_right
    (sum_perm_max_runningMeanTest_iInf_le β fun i ↦ (e i : ℝ≥0∞)) _

/-- **The exchangeable Markov inequality** [RM26]: for every number `K` of e-values and every
level `β`, the function `β * 𝟙{some running mean reaches β}` is a merging function for
exchangeable e-values. -/
theorem isExchangeableEMerging_runningMeanTest (β : ℝ≥0∞) :
    IsExchangeableEMerging (runningMeanTest (K := K) β) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have h0 : runningMeanTest β = fun _ : Fin 0 → ℝ≥0∞ ↦ 0 := funext fun e ↦
      Set.indicator_of_notMem (by rintro ⟨k, -⟩; exact k.elim0) _
    rw [h0]
    exact ⟨measurable_const, fun μ _ _ _ ↦ by simp⟩
  · have : NeZero K := ⟨hK.ne'⟩
    exact (isExchangeableEMerging_max_runningMeanTest_iInf β).mono (measurable_runningMeanTest β)
      fun e ↦ le_max_left _ _

/-- **The function of the exchangeable Markov inequality is not admissible**: for every number
`K` of e-values and every level `β`, a monotone merging function for exchangeable e-values is at
least `β * 𝟙{some running mean reaches β}` and differs from it. This answers the question of
[Wan25, Section 4 (d)], which is asked for `K ≥ 2` and `1 < β < ∞`. For `K ≥ 1` the function is
the maximum with the smallest e-value. -/
theorem exists_isExchangeableEMerging_monotone_runningMeanTest_lt (β : ℝ≥0∞) :
    ∃ G : (Fin K → ℝ≥0∞) → ℝ≥0∞, IsExchangeableEMerging G ∧ Monotone G ∧
      runningMeanTest β ≤ G ∧ runningMeanTest β ≠ G := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have h0 : runningMeanTest β = fun _ : Fin 0 → ℝ≥0∞ ↦ 0 := funext fun e ↦
      Set.indicator_of_notMem (by rintro ⟨k, -⟩; exact k.elim0) _
    refine ⟨fun _ ↦ 1, ⟨measurable_const, fun μ _ _ _ ↦ by simp⟩, monotone_const,
      fun e ↦ by simp [h0], fun h ↦ ?_⟩
    simpa [h0] using congr_fun h 0
  have : NeZero K := ⟨hK.ne'⟩
  refine ⟨fun e ↦ max (runningMeanTest β e) (⨅ k, e k),
    isExchangeableEMerging_max_runningMeanTest_iInf β, fun e e' h ↦ ?_,
    fun e ↦ le_max_left _ _, fun h ↦ ?_⟩
  · exact max_le_max (monotone_runningMeanTest β h) (iInf_mono fun k ↦ h k)
  · -- at a constant vector `x` with `0 < x < ∞` and `x ≠ β`, the two functions differ
    obtain ⟨x, hx₀, hx_top, hxβ⟩ : ∃ x : ℝ≥0∞, x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ β := by
      by_cases hβ : β = 1
      · exact ⟨2, by simp, by simp, by rw [hβ]; norm_num⟩
      · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, Ne.symm hβ⟩
    have hx : x ≤ runningMeanTest β fun _ ↦ x :=
      calc x = ⨅ _ : Fin K, x := iInf_const.symm
        _ ≤ max (runningMeanTest β fun _ ↦ x) (⨅ _ : Fin K, x) := le_max_right _ _
        _ = runningMeanTest β fun _ ↦ x := (congr_fun h fun _ ↦ x).symm
    simp only [runningMeanTest, Set.indicator_apply, Set.mem_ofPred_eq] at hx
    split_ifs at hx with hmem
    · obtain ⟨k, hk⟩ := hmem
      rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul, mul_comm β] at hk
      exact hxβ (le_antisymm hx ((ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hk))
    · exact hx₀ (nonpos_iff_eq_zero.mp hx)

end ProbabilityTheory
