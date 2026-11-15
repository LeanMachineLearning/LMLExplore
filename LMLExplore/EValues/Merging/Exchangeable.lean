/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.EVariable
public import TauCeti.Probability.Exchangeability.Family
import Mathlib.Data.Fintype.Perm
import LMLExplore.Algebra.BigOperators.Perm
import LMLExplore.Basic.ENNReal.Real

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
* `ProbabilityTheory.RunningMeanReaches β e`: some running mean of the `K` e-values `e` reaches
  `β`.
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

The characterization and the non-admissibility have no published source other than
[EVR26, Note 09]. The statements and proofs are adapted from the formalization in the paper
project `RemyDegenne/evalues_research` (same author), files
`EValuesResearch/ForLMLExplore/EValues/ExchangeableMerging.lean` (statements, commit `9c51e1d`) and
`EValuesResearch/Results/ExchangeableMerging.lean` (proofs, commit `af4950b`).

## References

* [RM26] A. Ramdas and T. Manole, *Randomized and exchangeable improvements of Markov's,
  Chebyshev's and Chernoff's inequalities*, Statist. Sci. 41 (2026), arXiv:2304.02611v3.
* [Wan25] R. Wang, *The only admissible way of merging arbitrary e-values*, Biometrika (2025),
  arXiv:2409.19888v2: Section 4 (d).
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026: Note 09.
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### Merging functions for exchangeable e-values -/

section Definition

variable {ι : Type*} {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- Permuting the coordinates is measurable. -/
private lemma measurable_comp_perm (σ : Equiv.Perm ι) : Measurable fun e : ι → ℝ≥0∞ ↦ e ∘ σ :=
  measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _

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
theorem IsExchangeableEMerging.of_le (hG : IsExchangeableEMerging G) (hF : Measurable F)
    (hle : F ≤ G) : IsExchangeableEMerging F :=
  ⟨hF, fun μ _ hσ hμ ↦ (lintegral_mono hle).trans (hG.lintegral_le_one μ hσ hμ)⟩

/-- A constant at most one is a merging function for exchangeable e-values. -/
theorem isExchangeableEMerging_const {c : ℝ≥0∞} (hc : c ≤ 1) :
    IsExchangeableEMerging fun _ : ι → ℝ≥0∞ ↦ c :=
  ⟨measurable_const, fun μ _ _ _ ↦ by simpa using hc⟩

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
    rw [Measure.map_map (measurable_comp_perm σ) hm]
    exact (hexch P hP).map_eq_of_injective (fun i ↦ (hE i).measurable.aemeasurable) σ.injective
      Function.injective_id
  · rw [lintegral_map (measurable_pi_apply i) hm]
    simpa using (hE i).lintegral_le_measure_univ P hP

end Definition

/-! ### The characterization by the symmetrization -/

variable {K : ℕ}

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
  have hτ := measurable_comp_perm (ι := Fin K) τ
  rw [orbitMeasure, Measure.map_smul _ hτ.aemeasurable, Measure.map_finset_sum' hτ.aemeasurable]
  simp_rw [Measure.map_dirac]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ ↦ by simp [Function.comp_def]

/-- The coordinate means of the uniform law on the orbit of `E` are the mean of `E`. -/
private lemma lintegral_apply_orbitMeasure (E : Fin K → ℝ≥0∞) (i : Fin K) :
    ∫⁻ x, x i ∂orbitMeasure E = (∑ j, E j) / K := by
  rw [lintegral_orbitMeasure E fun x ↦ x i]
  simpa [Fintype.card_perm] using ENNReal.sum_perm_apply_div_card E i

/-- The integral against a mixture of the uniform laws on the orbits of `E` and `E'` is the
mixture of the integrals. -/
private lemma lintegral_mix_orbitMeasure (E E' : Fin K → ℝ≥0∞) (p q : ℝ≥0∞)
    (g : (Fin K → ℝ≥0∞) → ℝ≥0∞) :
    ∫⁻ x, g x ∂(p • orbitMeasure E + q • orbitMeasure E') =
      p * ∫⁻ x, g x ∂orbitMeasure E + q * ∫⁻ x, g x ∂orbitMeasure E' := by
  simp

/-- If `F` is a merging function for exchangeable e-values, then for every mixture with weights
`p` and `q` of the uniform laws on the orbits of `E` and `E'` whose coordinate means are at most
one, the corresponding mixture of the symmetrizations of `F` at `E` and `E'` is at most one. -/
private lemma mix_le_one_of_isExchangeableEMerging {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsExchangeableEMerging F) (E E' : Fin K → ℝ≥0∞) {p q : ℝ≥0∞} (hpq : p + q = 1)
    (h : p * ((∑ i, E i) / K) + q * ((∑ i, E' i) / K) ≤ 1) :
    p * ((∑ σ : Equiv.Perm (Fin K), F fun i ↦ E (σ i)) / K.factorial) +
      q * ((∑ σ : Equiv.Perm (Fin K), F fun i ↦ E' (σ i)) / K.factorial) ≤ 1 := by
  have hτ : ∀ τ : Equiv.Perm (Fin K), Measurable fun e : Fin K → ℝ≥0∞ ↦ e ∘ τ :=
    measurable_comp_perm
  have hprob : IsProbabilityMeasure (p • orbitMeasure E + q • orbitMeasure E') :=
    ⟨by simp [orbitMeasure_univ, hpq]⟩
  have := hF.lintegral_le_one (p • orbitMeasure E + q • orbitMeasure E') (fun τ ↦ by
      rw [Measure.map_add _ _ (hτ τ), Measure.map_smul _ (hτ τ).aemeasurable,
        Measure.map_smul _ (hτ τ).aemeasurable, map_orbitMeasure, map_orbitMeasure])
    (fun i ↦ by simpa only [lintegral_mix_orbitMeasure, lintegral_apply_orbitMeasure] using h)
  simpa only [lintegral_mix_orbitMeasure, lintegral_orbitMeasure] using this

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
    -- the mixture with weights `p / (p + q)` and `q / (p + q)`, cleared of denominators
    have key : ∀ u v : ℝ, p / (p + q) * u + (1 - p / (p + q)) * v ≤ 1 ↔ p * u + q * v ≤ p + q :=
      fun u v ↦ by rw [hq', div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hpq]
    exact (key _ _).1 (hmix x y (p / (p + q)) (div_nonneg hp hpq.le)
      (div_le_one_of_le₀ (by linarith) hpq.le) ((key _ _).2 h))
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
`(1 - l) + l * mean` at every point with finite coordinates, for some `l ≤ 1` [EVR26, Note 09]. -/
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
        rw [ENNReal.ofReal_mul_add_ofReal_one_sub_mul (hM_top e) (hM_top e') hp₀ hp₁]
        exact ENNReal.ofReal_le_one.mpr h)
      rw [ENNReal.ofReal_mul_add_ofReal_one_sub_mul (hA_top e) (hA_top e') hp₀ hp₁] at h'
      exact ENNReal.ofReal_le_one.mp h')
  refine ⟨ENNReal.ofReal l, ENNReal.ofReal_le_one.mpr hl₁, fun e ↦ ?_⟩
  calc A e = ENNReal.ofReal (A e).toReal := (ENNReal.ofReal_toReal (hA_top e)).symm
    _ ≤ ENNReal.ofReal (1 - l + l * (M e).toReal) := ENNReal.ofReal_le_ofReal (hl e)
    _ = (1 - ENNReal.ofReal l) + ENNReal.ofReal l * M e := by
      rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_sub _ hl₀,
        ENNReal.ofReal_one, ENNReal.ofReal_mul hl₀, ENNReal.ofReal_toReal (hM_top e)]

/-- A measurable function whose symmetrization is at most `(1 - l) + l * mean` at every point
with finite coordinates, for some `l ≤ 1`, is a merging function for exchangeable e-values
[EVR26, Note 09]. -/
theorem isExchangeableEMerging_of_sum_perm_div_le {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : Measurable F) {l : ℝ≥0∞} (hl : l ≤ 1)
    (h : ∀ e : Fin K → ℝ≥0,
      (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / (K.factorial : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (K : ℝ≥0∞))) :
    IsExchangeableEMerging F := by
  refine ⟨hF, fun μ hμ hexch hmean ↦ ?_⟩
  have hτ : ∀ τ : Equiv.Perm (Fin K), Measurable fun e : Fin K → ℝ≥0∞ ↦ fun i ↦ e (τ i) :=
    measurable_comp_perm
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
        simp [lintegral_const_mul _ (Finset.measurable_sum _ fun σ _ ↦ hFτ σ),
          lintegral_finsetSum _ fun σ _ ↦ hFτ σ, hinv, Fintype.card_perm, ← mul_assoc,
          ENNReal.inv_mul_cancel hK]
    _ ≤ ∫⁻ e, (1 - l) + l * ((∑ i, e i) * (K : ℝ≥0∞)⁻¹) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfin] with e he
        have := h fun i ↦ (e i).toNNReal
        simp only [ENNReal.coe_toNNReal (he _)] at this
        rwa [mul_comm, ← div_eq_mul_inv, ← div_eq_mul_inv]
    _ = (1 - l) + l * ((∑ i, ∫⁻ e, e i ∂μ) / K) := by
        simp [lintegral_add_left measurable_const, lintegral_const_mul _ (hsum.mul_const _),
          lintegral_mul_const _ hsum, lintegral_finsetSum _ fun i _ ↦ measurable_pi_apply i,
          div_eq_mul_inv]
    _ ≤ (1 - l) + l * 1 := by
        gcongr
        refine ENNReal.div_le_of_le_mul ?_
        calc ∑ i, ∫⁻ e, e i ∂μ ≤ ∑ _ : Fin K, (1 : ℝ≥0∞) := Finset.sum_le_sum fun i _ ↦ hmean i
          _ = 1 * K := by simp
    _ = 1 := by rw [mul_one, tsub_add_cancel_of_le hl]

/-- **The merging functions for exchangeable e-values**: a function of `K` e-values is one exactly
when it is measurable and, for some `l ≤ 1`, its symmetrization is at most `(1 - l) + l * mean`
at every point with finite coordinates [EVR26, Note 09]. -/
theorem isExchangeableEMerging_iff (F : (Fin K → ℝ≥0∞) → ℝ≥0∞) :
    IsExchangeableEMerging F ↔ Measurable F ∧ ∃ l : ℝ≥0∞, l ≤ 1 ∧ ∀ e : Fin K → ℝ≥0,
      (∑ σ : Equiv.Perm (Fin K), F fun i ↦ e (σ i)) / (K.factorial : ℝ≥0∞) ≤
        (1 - l) + l * ((∑ i, (e i : ℝ≥0∞)) / (K : ℝ≥0∞)) :=
  ⟨fun hF ↦ ⟨hF.measurable, hF.exists_sum_perm_div_le⟩,
    fun ⟨hF, _, hl, h⟩ ↦ isExchangeableEMerging_of_sum_perm_div_le hF hl h⟩

/-! ### The exchangeable Markov inequality -/

/-- Some running mean of the `K` e-values `e` reaches `β`: for some `k`, the mean of the first
`k + 1` e-values is at least `β`. -/
def RunningMeanReaches (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) : Prop :=
  ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Finset.Iic k, e j

/-- Unfolding `RunningMeanReaches`. -/
theorem runningMeanReaches_iff {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞} :
    RunningMeanReaches β e ↔ ∃ k : Fin K, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Finset.Iic k, e j :=
  Iff.rfl

/-- Whether some running mean reaches `β` is decided by the order on `ℝ≥0∞`. -/
noncomputable instance (β : ℝ≥0∞) : DecidablePred (RunningMeanReaches (K := K) β) :=
  fun _ ↦ decidable_of_iff _ runningMeanReaches_iff.symm

/-- The set of e-values some running mean of which reaches `β` is measurable. -/
theorem measurableSet_runningMeanReaches (β : ℝ≥0∞) :
    MeasurableSet {e : Fin K → ℝ≥0∞ | RunningMeanReaches β e} := by
  simp_rw [runningMeanReaches_iff, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun k ↦ measurableSet_le measurable_const
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- If some running mean of `e` reaches `β`, so does some running mean of every larger `e'`. -/
theorem RunningMeanReaches.mono {β : ℝ≥0∞} {e e' : Fin K → ℝ≥0∞} (h : RunningMeanReaches β e)
    (hle : e ≤ e') : RunningMeanReaches β e' :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.trans (Finset.sum_le_sum fun j _ ↦ hle j)⟩

/-- The function `β * 𝟙{some running mean reaches β}` of `K` e-values [RM26]: its value is `β`
when, for some `k`, the mean of the first `k + 1` e-values is at least `β`, and `0` otherwise. -/
noncomputable def runningMeanTest (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) : ℝ≥0∞ :=
  Set.indicator {e : Fin K → ℝ≥0∞ | RunningMeanReaches β e} (fun _ ↦ β) e

/-- The value of `β * 𝟙{some running mean reaches β}`. -/
theorem runningMeanTest_apply (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    runningMeanTest β e = if RunningMeanReaches β e then β else 0 := by
  simp only [runningMeanTest, Set.indicator_apply, Set.mem_ofPred_eq]

/-- `β * 𝟙{some running mean reaches β}` is `β` when some running mean reaches `β`. -/
theorem runningMeanTest_of_runningMeanReaches {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    (h : RunningMeanReaches β e) : runningMeanTest β e = β :=
  Set.indicator_of_mem h _

/-- `β * 𝟙{some running mean reaches β}` is `0` when no running mean reaches `β`. -/
theorem runningMeanTest_of_not_runningMeanReaches {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    (h : ¬ RunningMeanReaches β e) : runningMeanTest β e = 0 :=
  Set.indicator_of_notMem h _

/-- With no e-values, `β * 𝟙{some running mean reaches β}` is `0`. -/
@[simp]
theorem runningMeanTest_of_isEmpty [IsEmpty (Fin K)] (β : ℝ≥0∞) : runningMeanTest (K := K) β = 0 :=
  funext fun _ ↦ runningMeanTest_of_not_runningMeanReaches fun ⟨k, _⟩ ↦ isEmptyElim k

/-- The function `β * 𝟙{some running mean reaches β}` is measurable. -/
theorem measurable_runningMeanTest (β : ℝ≥0∞) : Measurable (runningMeanTest (K := K) β) :=
  measurable_const.indicator (measurableSet_runningMeanReaches β)

/-- The function `β * 𝟙{some running mean reaches β}` is monotone. -/
theorem monotone_runningMeanTest (β : ℝ≥0∞) : Monotone (runningMeanTest (K := K) β) := by
  intro e e' h
  simp only [runningMeanTest_apply]
  split_ifs with he he'
  · exact le_rfl
  · exact absurd (he.mono h) he'
  · exact zero_le
  · exact le_rfl

open Finset in
/-- If every ordering `σ ∈ B` has a mean of its first `k + 1` coordinates at least `β`, and `B` is
invariant under the swaps of `0` with the indices of that prefix, then
`β * #B ≤ ∑ σ ∈ B, e (σ 0)`: by the invariance, the first coordinate has the same sum over `B` as
every coordinate of the prefix. -/
private lemma mul_card_le_sum_apply_zero_of_swap_mem [NeZero K] {β : ℝ≥0∞} {e : Fin K → ℝ≥0∞}
    {k : Fin K} {B : Finset (Equiv.Perm (Fin K))}
    (hswap : ∀ i ≤ k, ∀ σ ∈ B, σ * Equiv.swap 0 i ∈ B)
    (hB : ∀ σ ∈ B, β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)) :
    β * #B ≤ ∑ σ ∈ B, e (σ 0) := by
  have hsym : ∀ i ∈ Iic k, ∑ σ ∈ B, e (σ i) = ∑ σ ∈ B, e (σ 0) := by
    intro i hi
    rw [mem_Iic] at hi
    exact sum_nbij' (· * Equiv.swap 0 i) (· * Equiv.swap 0 i) (hswap i hi) (hswap i hi)
      (fun σ _ ↦ by simp) (fun σ _ ↦ by simp) (fun σ _ ↦ by simp)
  refine (ENNReal.mul_le_mul_iff_right (a := (((k : ℕ) + 1 : ℕ) : ℝ≥0∞)) (by simp)
    (by simp)).mp ?_
  calc (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * (β * #B)
      = ∑ σ ∈ B, β * ((k : ℕ) + 1 : ℕ) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ σ ∈ B, ∑ j ∈ Iic k, e (σ j) := sum_le_sum hB
    _ = ∑ j ∈ Iic k, ∑ σ ∈ B, e (σ j) := sum_comm
    _ = ∑ j ∈ Iic k, ∑ σ ∈ B, e (σ 0) := sum_congr rfl hsym
    _ = (((k : ℕ) + 1 : ℕ) : ℝ≥0∞) * ∑ σ ∈ B, e (σ 0) := by
      rw [sum_const, Fin.card_Iic, nsmul_eq_mul]

open Finset in
/-- The orbit form of the exchangeable Markov inequality: if `A` is the set of orderings `σ` of
`e` for which some running mean reaches `β`, then `β * #A ≤ ∑ σ ∈ A, e (σ 0)`. The proof splits
`A` according to the last prefix whose mean reaches `β`; that event is invariant under the
permutations of the prefix, so on it the first coordinate has the same sum as the prefix mean. -/
private lemma mul_card_le_sum_apply_zero_of_runningMean [NeZero K] (β : ℝ≥0∞)
    (e : Fin K → ℝ≥0∞) :
    β * #{σ : Equiv.Perm (Fin K) | RunningMeanReaches β fun j ↦ e (σ j)} ≤
      ∑ σ : Equiv.Perm (Fin K) with RunningMeanReaches β fun j ↦ e (σ j), e (σ 0) := by
  classical
  let P : Fin K → Equiv.Perm (Fin K) → Prop := fun k σ ↦
    β * ((k : ℕ) + 1 : ℕ) ≤ ∑ j ∈ Iic k, e (σ j)
  -- `B k` is the set of orderings for which `k` is the last prefix whose mean reaches `β`
  let B : Fin K → Finset (Equiv.Perm (Fin K)) := fun k ↦ {σ | P k σ ∧ ∀ j, k < j → ¬ P j σ}
  have hunion : ({σ | RunningMeanReaches β fun j ↦ e (σ j)} : Finset (Equiv.Perm (Fin K))) =
      univ.biUnion B := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, B, runningMeanReaches_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk, _⟩ ↦ ⟨k, hk⟩⟩
    have hne : ({j | P j σ} : Finset (Fin K)).Nonempty := ⟨k, by simpa [P] using hk⟩
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
    have hP : ∀ j, k ≤ j → (P j (σ * Equiv.swap 0 i) ↔ P j σ) := fun j hj ↦ by
      simp only [P, Equiv.Perm.mul_apply, Equiv.Perm.sum_comp_swap (mem_Iic.2 (Fin.zero_le j))
        (mem_Iic.2 (hi.trans hj)) fun l ↦ e (σ l)]
    simp only [mem_filter, mem_univ, true_and, B] at hσ ⊢
    exact ⟨(hP k le_rfl).2 hσ.1, fun j hj ↦ by rw [hP j hj.le]; exact hσ.2 j hj⟩
  rw [hunion, card_biUnion hdisj, sum_biUnion hdisj, Nat.cast_sum, mul_sum]
  exact sum_le_sum fun k _ ↦ mul_card_le_sum_apply_zero_of_swap_mem (hswap k)
    fun σ hσ ↦ (mem_filter.mp hσ).2.1

open Finset in
/-- The symmetrization of `max (runningMeanTest β) (min_k e_k)` at `e` is at most the mean of
`e`, in the form `∑ σ, G (e ∘ σ) ≤ ∑ σ, e (σ 0)`. -/
private lemma sum_perm_max_runningMeanTest_iInf_le [NeZero K] (β : ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    ∑ σ : Equiv.Perm (Fin K), max (runningMeanTest β fun i ↦ e (σ i)) (⨅ k, e (σ k)) ≤
      ∑ σ : Equiv.Perm (Fin K), e (σ 0) := by
  classical
  have hc : ∀ σ : Equiv.Perm (Fin K), ⨅ k, e (σ k) = ⨅ k, e k := fun σ ↦ Equiv.iInf_comp σ
  simp_rw [hc]
  rw [← sum_filter_add_sum_filter_not univ fun σ ↦ RunningMeanReaches β fun j ↦ e (σ j),
    ← sum_filter_add_sum_filter_not univ (fun σ ↦ RunningMeanReaches β fun j ↦ e (σ j))
      fun σ : Equiv.Perm (Fin K) ↦ e (σ 0)]
  refine add_le_add ?_ (sum_le_sum fun σ hσ ↦ ?_)
  · rw [sum_congr rfl fun σ hσ ↦ by
      rw [runningMeanTest_of_runningMeanReaches (mem_filter.mp hσ).2], sum_const, nsmul_eq_mul]
    rcases le_total β (⨅ k, e k) with h | h
    · rw [max_eq_right h, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun σ _ ↦ iInf_le _ _
    · rw [max_eq_left h, mul_comm]
      exact mul_card_le_sum_apply_zero_of_runningMean β e
  · rw [runningMeanTest_of_not_runningMeanReaches (mem_filter.mp hσ).2, max_eq_right zero_le]
    exact iInf_le _ _

/-- The maximum of `β * 𝟙{some running mean reaches β}` and the smallest e-value is a merging
function for exchangeable e-values [EVR26, Note 09]. -/
theorem isExchangeableEMerging_max_runningMeanTest_iInf [NeZero K] (β : ℝ≥0∞) :
    IsExchangeableEMerging fun e : Fin K → ℝ≥0∞ ↦ max (runningMeanTest β e) (⨅ k, e k) := by
  refine isExchangeableEMerging_of_sum_perm_div_le ((measurable_runningMeanTest β).max
    (Measurable.iInf fun k ↦ measurable_pi_apply k)) le_rfl fun e ↦ ?_
  have h := ENNReal.sum_perm_apply_div_card (fun i ↦ (e i : ℝ≥0∞)) 0
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [tsub_self, zero_add, one_mul, ← h]
  exact ENNReal.div_le_div_right
    (sum_perm_max_runningMeanTest_iInf_le β fun i ↦ (e i : ℝ≥0∞)) _

/-- **The exchangeable Markov inequality** [RM26]: for every number `K` of e-values and every
level `β`, the function `β * 𝟙{some running mean reaches β}` is a merging function for
exchangeable e-values. -/
theorem isExchangeableEMerging_runningMeanTest (β : ℝ≥0∞) :
    IsExchangeableEMerging (runningMeanTest (K := K) β) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [runningMeanTest_of_isEmpty]
    exact isExchangeableEMerging_const zero_le
  · have : NeZero K := ⟨hK.ne'⟩
    exact (isExchangeableEMerging_max_runningMeanTest_iInf β).of_le (measurable_runningMeanTest β)
      fun e ↦ le_max_left _ _

/-- **The function of the exchangeable Markov inequality is not admissible**: for every number
`K` of e-values and every level `β`, a monotone merging function for exchangeable e-values is at
least `β * 𝟙{some running mean reaches β}` and differs from it. This answers the question of
[Wan25, Section 4 (d)], which is asked for `K ≥ 2` and `1 < β < ∞` [EVR26, Note 09]. For `K ≥ 1`
the function is the maximum with the smallest e-value. -/
theorem exists_isExchangeableEMerging_monotone_runningMeanTest_lt (β : ℝ≥0∞) :
    ∃ G : (Fin K → ℝ≥0∞) → ℝ≥0∞, IsExchangeableEMerging G ∧ Monotone G ∧
      runningMeanTest β ≤ G ∧ runningMeanTest β ≠ G := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine ⟨fun _ ↦ 1, isExchangeableEMerging_const le_rfl, monotone_const,
      fun e ↦ by simp, fun h ↦ ?_⟩
    simpa using congr_fun h 0
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
    rw [runningMeanTest_apply] at hx
    split_ifs at hx with hmem
    · obtain ⟨k, hk⟩ := runningMeanReaches_iff.1 hmem
      rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul, mul_comm β] at hk
      exact hxβ (le_antisymm hx ((ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hk))
    · exact hx₀ (nonpos_iff_eq_zero.mp hx)

end ProbabilityTheory
