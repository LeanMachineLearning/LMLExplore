/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.NumeraireAt
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
import LMLExplore.EValues.EffectiveSet.Basic
import LMLExplore.EValues.Numeraire
import LMLExplore.Probability.ProductMeasure

/-!
# The product of one-step numeraires is optimal at every finite stopping time

Let `S₁ i` be sets of probability measures on `𝓧`, the one-step nulls, `Q₁ i` probability
measures, the one-step alternatives, and `X i` a numeraire of `S₁ i` against `Q₁ i`. On sequences
`ℕ → 𝓧` with the filtration `Filtration.piLT` of the past observations, the product
`E n ω = ∏ i < n, X i (ω i)` is optimal at every stopping time `τ` that is finite everywhere,
bounded or not, against the law `Measure.infinitePi Q₁` of independent observations from the
alternatives, for every null `𝓝` that contains the products of members of the `S₁ i` and for
which `E` is an e-process [EVR26, Note 40, Theorem 5], as soon as the numeraires are almost surely
finite. One such null is the sequential null of the one-step nulls
(`isNumeraireAt_prod_sequentialNull`), for which the product is a test supermartingale.

The proof replaces the laws of the observations by the alternatives one coordinate at a time, by
Tonelli's theorem (`lintegral_sum_mul_prod_inv_le`): no dominating measure, no measurable choice
of the null laws and no finiteness of the numeraires is used for the bound
`∫⁻ F_τ / E_τ ∂Q₁^ℕ ≤ 1` on the e-processes `F` (`lintegral_div_prod_le_one`). For a simple
i.i.d. null `P₁` and an alternative `Q₁ ≪ P₁`, this makes the likelihood ratio process optimal at
every stopping time that is finite everywhere (`isNumeraireAt_prod_rnDeriv`)
[EVR26, Note 40, Proposition 6].

## Main statements

* `ProbabilityTheory.lintegral_sum_mul_prod_inv_le`: if `∑ k < N, g k` has integral at most `c`
  under every product of members of the one-step nulls, for functions `g k` of the first `k`
  observations, then `∑ k < N, g k * ∏ i < k, (X i (ω i))⁻¹` has integral at most `c` under the
  product of the alternatives.
* `ProbabilityTheory.lintegral_div_prod_le_one`: the ratio of an e-process to the product of the
  numeraires, at a stopping time that is finite everywhere, has expectation at most `1` under the
  product of the alternatives.
* `ProbabilityTheory.isNumeraireAt_prod`: the product of almost surely finite one-step numeraires
  is optimal at every stopping time that is finite everywhere [EVR26, Note 40, Theorem 5].
* `ProbabilityTheory.isNumeraireAt_prod_sequentialNull`: the same for the sequential null of the
  one-step nulls.
* `ProbabilityTheory.isNumeraireAt_prod_rnDeriv`: the likelihood ratio process of i.i.d. laws is
  optimal at every stopping time that is finite everywhere.

## Implementation notes

The statements and the proofs are adapted from the file `notes/lean-wip/StoppedPaths.lean` and
its auxiliary file `notes/lean-wip/StoppedPathsAux.lean` (commit `c6c6ba8`) of the paper project
`RemyDegenne/evalues_research` (Apache 2.0), with the step of the effective null stated as
`lintegral_le_of_mem_effectiveSet` and the instance for the sequential null in place of the null of
independent observations.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 40.
-/

public section

open MeasureTheory Set Finset Filtration
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : ℕ → Set (Measure 𝓧)}
  {Q₁ : ℕ → Measure 𝓧} {X : ℕ → 𝓧 → ℝ≥0∞}

/-! ### Replacing the null laws by the alternatives, one coordinate at a time -/

/-- The family in which the observations `j ≤ i < N` have the laws of the alternatives and the
others have laws in the one-step nulls consists of probability measures. -/
private lemma isProbabilityMeasure_ite (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    [∀ i, IsProbabilityMeasure (Q₁ i)] {P : ℕ → Measure 𝓧} (hP : ∀ i, P i ∈ S₁ i) (j N i : ℕ) :
    IsProbabilityMeasure (if j ≤ i ∧ i < N then Q₁ i else P i) := by
  split_ifs
  exacts [inferInstance, hS₁ i _ (hP i)]

/-- Under the product of the alternatives, the one-step numeraires of nulls of probability
measures are almost surely positive at every observation. -/
private lemma ae_forall_ne_zero (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    [∀ i, IsProbabilityMeasure (Q₁ i)] (hX : ∀ i, IsNumeraire (X i) (S₁ i) (Q₁ i)) :
    ∀ᵐ ω ∂Measure.infinitePi Q₁, ∀ i, X i (ω i) ≠ 0 :=
  Measure.ae_forall_apply_infinitePi Q₁ fun i ↦
    (hX i).ae_ne_zero fun P hP ↦ (hS₁ i P hP).measure_univ.le

/-- **One coordinate.** Let `A` and `B` be functions of a sequence, `A` not depending on the
coordinate `j`, such that `A + B` has integral at most `c` under every product of the
probability measures `μ i` in which the factor `j` is a member of the null `S₁j`. Then
`A + B / Xj (ω j)` has integral at most `c` under the product in which the factor `j` is `Q₁j`,
when `∫⁻ Y / Xj ∂Q₁j ≤ 1` for every e-variable `Y` of `S₁j`. -/
private lemma lintegral_add_mul_inv_le {S₁j : Set (Measure 𝓧)}
    (hS₁j : ∀ P ∈ S₁j, IsProbabilityMeasure P) (hS₁j_ne : S₁j.Nonempty) {Q₁j : Measure 𝓧}
    [IsProbabilityMeasure Q₁j] {Xj : 𝓧 → ℝ≥0∞} (hXj : Measurable Xj)
    (hXj_le : ∀ Y, IsEVar Y S₁j → ∫⁻ x, Y x / Xj x ∂Q₁j ≤ 1) (μ : ℕ → Measure 𝓧)
    [∀ i, IsProbabilityMeasure (μ i)] (j : ℕ) {A B : (ℕ → 𝓧) → ℝ≥0∞} (hA : Measurable A)
    (hB : Measurable B) (hA_upd : ∀ ω x, A (Function.update ω j x) = A ω) {c : ℝ≥0∞}
    (h : ∀ P ∈ S₁j, ∫⁻ ω, A ω + B ω ∂Measure.infinitePi (Function.update μ j P) ≤ c) :
    ∫⁻ ω, A ω + B ω * (Xj (ω j))⁻¹ ∂Measure.infinitePi (Function.update μ j Q₁j) ≤ c := by
  set a := ∫⁻ ω, A ω ∂Measure.infinitePi μ
  set φ : 𝓧 → ℝ≥0∞ := fun x ↦ ∫⁻ ω, B (Function.update ω j x) ∂Measure.infinitePi μ
  have hφ : Measurable φ := (hB.comp measurable_update').lintegral_prod_left'
  have hB_upd (x : 𝓧) : Measurable fun ω ↦ B (Function.update ω j x) :=
    hB.comp (measurable_update' (a := j) |>.comp (measurable_id.prodMk measurable_const))
  -- by Tonelli's theorem at the coordinate `j`, both integrals are `a` plus an integral in `x`
  have h_int (ν : Measure 𝓧) [IsProbabilityMeasure ν] (f : 𝓧 → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ ω, A ω + B ω * f (ω j) ∂Measure.infinitePi (Function.update μ j ν) =
        a + ∫⁻ x, φ x * f x ∂ν := by
    rw [Measure.lintegral_infinitePi_update μ j ν (f := fun ω ↦ A ω + B ω * f (ω j))
      (hA.add (hB.mul (hf.comp (measurable_pi_apply j))))]
    simp_rw [hA_upd, Function.update_self]
    have h_in (x : 𝓧) : ∫⁻ ω, A ω + B (Function.update ω j x) * f x ∂Measure.infinitePi μ =
        a + φ x * f x := by
      rw [lintegral_add_left hA, lintegral_mul_const _ (hB_upd x)]
    simp_rw [h_in]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  -- the bound under the null laws at the coordinate `j`
  have h' (P : Measure 𝓧) (hP : P ∈ S₁j) : a + ∫⁻ x, φ x ∂P ≤ c := by
    have := hS₁j P hP
    have h1 := h_int P (fun _ ↦ 1) measurable_const
    simp only [mul_one] at h1
    exact h1 ▸ h P hP
  rw [h_int Q₁j (fun x ↦ (Xj x)⁻¹) hXj.inv]
  obtain ⟨P₀, hP₀⟩ := hS₁j_ne
  rcases eq_or_ne c ∞ with rfl | hc
  · exact le_top
  have hac : a ≤ c := le_self_add.trans (h' P₀ hP₀)
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hc hac
  -- the measure of density `Xj⁻¹` with respect to `Q₁j` is in the effective null of `S₁j`
  have hmem := (withDensity_inv_mem_effectiveSet_iff hXj).2 hXj_le
  calc a + ∫⁻ x, φ x * (Xj x)⁻¹ ∂Q₁j
  _ = a + ∫⁻ x, φ x ∂(Q₁j.withDensity fun x ↦ (Xj x)⁻¹) := by
    simp_rw [lintegral_withDensity_inv_eq_lintegral_div hXj.aemeasurable hφ.aemeasurable,
      div_eq_mul_inv]
  _ ≤ a + (c - a) := by
    gcongr
    exact lintegral_le_of_mem_effectiveSet hmem hφ fun P hP ↦
      ENNReal.le_sub_of_add_le_left ha (h' P hP)
  _ = c := add_tsub_cancel_of_le hac

/-- The splitting of `∑ k < N, g k * ∏ j + 1 ≤ i < k, Y i` into the terms `k ≤ j`, which have no
factor, and the others. -/
private lemma sum_mul_prod_Ico_succ_eq {R : Type*} [CommSemiring R] (g Y : ℕ → R) (N j : ℕ) :
    ∑ k ∈ range N, g k * ∏ i ∈ Ico (j + 1) k, Y i =
      ∑ k ∈ range N with k ≤ j, g k +
        ∑ k ∈ range N with ¬ k ≤ j, g k * ∏ i ∈ Ico (j + 1) k, Y i := by
  rw [← sum_filter_add_sum_filter_not (range N) (· ≤ j)]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  rw [Finset.Ico_eq_empty (by have := (mem_filter.1 hk).2; omega), Finset.prod_empty, mul_one]

/-- The splitting of `∑ k < N, g k * ∏ j ≤ i < k, Y i` at the coordinate `j`: the terms `k ≤ j` do
not see `Y j`, and the others carry it as a factor. -/
private lemma sum_mul_prod_Ico_eq {R : Type*} [CommSemiring R] (g Y : ℕ → R) (N j : ℕ) :
    ∑ k ∈ range N, g k * ∏ i ∈ Ico j k, Y i =
      ∑ k ∈ range N with k ≤ j, g k +
        (∑ k ∈ range N with ¬ k ≤ j, g k * ∏ i ∈ Ico (j + 1) k, Y i) * Y j := by
  rw [← sum_filter_add_sum_filter_not (range N) (· ≤ j), sum_mul]
  congr 1
  · refine sum_congr rfl fun k hk ↦ ?_
    rw [Finset.Ico_eq_empty (by have := (mem_filter.1 hk).2; omega), Finset.prod_empty, mul_one]
  · refine sum_congr rfl fun k hk ↦ ?_
    rw [prod_eq_prod_Ico_succ_bot (by have := (mem_filter.1 hk).2; omega), mul_assoc,
      mul_comm (Y j)]

/-- The induction of `lintegral_sum_mul_prod_inv_le`: under the product in which the observations
`j ≤ i < N` have the laws of the alternatives and the others have laws in the one-step nulls, the
sum weighted by the inverses of the numeraires of the observations `i ≥ j` has integral at most
`c`. It is proved by decreasing induction on `j`, from `j = N`, where it is the hypothesis. -/
private lemma lintegral_sum_mul_prod_Ico_inv_le (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    (hS₁_ne : ∀ i, (S₁ i).Nonempty) [∀ i, IsProbabilityMeasure (Q₁ i)]
    (hX : ∀ i, Measurable (X i)) (hX_le : ∀ i, ∀ Y, IsEVar Y (S₁ i) → ∫⁻ x, Y x / X i x ∂Q₁ i ≤ 1)
    {g : ℕ → (ℕ → 𝓧) → ℝ≥0∞} (hg : ∀ k, Measurable (g k))
    (hg_dep : ∀ k, DependsOn (g k) (Set.Iio k)) {N : ℕ} {c : ℝ≥0∞}
    (hg_le : ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁ i) →
      ∫⁻ ω, ∑ k ∈ range N, g k ω ∂Measure.infinitePi P ≤ c) (m : ℕ) :
    ∀ j, j + m = N → ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁ i) →
      ∫⁻ ω, ∑ k ∈ range N, g k ω * ∏ i ∈ Ico j k, (X i (ω i))⁻¹
        ∂Measure.infinitePi (fun i ↦ if j ≤ i ∧ i < N then Q₁ i else P i) ≤ c := by
  have hY (i : ℕ) : Measurable fun ω : ℕ → 𝓧 ↦ (X i (ω i))⁻¹ :=
    ((hX i).comp (measurable_pi_apply i)).inv
  induction m with
  | zero =>
    -- no observation has the law of the alternative
    intro j hj P hP
    obtain rfl : j = N := by simpa using hj
    have hνP : (fun i ↦ if j ≤ i ∧ i < j then Q₁ i else P i) = P :=
      funext fun i ↦ ite_eq_right (by omega)
    rw [hνP]
    refine le_of_eq_of_le (lintegral_congr fun ω ↦ sum_congr rfl fun k hk ↦ ?_) (hg_le P hP)
    rw [Finset.Ico_eq_empty (by have := mem_range.1 hk; omega), Finset.prod_empty, mul_one]
  | succ m ih =>
    rintro j hj P hP
    have := isProbabilityMeasure_ite (Q₁ := Q₁) hS₁ hP (j + 1) N
    set μ : ℕ → Measure 𝓧 := fun i ↦ if j + 1 ≤ i ∧ i < N then Q₁ i else P i
    -- the observation `j` has the law of the alternative here, and of `P'` in the induction
    -- hypothesis for `Function.update P j P'`
    have h_upd : (fun i ↦ if j ≤ i ∧ i < N then Q₁ i else P i) = Function.update μ j (Q₁ j) := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · have hiN : i < N := by omega
        simp [hiN]
      · simp only [Function.update_of_ne hij, μ]
        congr 1
        exact propext ⟨fun h ↦ ⟨by omega, h.2⟩, fun h ↦ ⟨by omega, h.2⟩⟩
    have h_upd' (P' : Measure 𝓧) : (fun i ↦ if j + 1 ≤ i ∧ i < N then Q₁ i else
        Function.update P j P' i) = Function.update μ j P' := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp only [Function.update_of_ne hij, μ]
    have hA_upd (ω : ℕ → 𝓧) (x : 𝓧) :
        ∑ k ∈ range N with k ≤ j, g k (Function.update ω j x) = ∑ k ∈ range N with k ≤ j, g k ω :=
      sum_congr rfl fun k hk ↦ hg_dep k fun i hi ↦ Function.update_of_ne
        (by have := (mem_filter.1 hk).2; have := Set.mem_Iio.1 hi; omega) _ _
    have hA : Measurable fun ω ↦ ∑ k ∈ range N with k ≤ j, g k ω :=
      Finset.measurable_fun_sum _ fun k _ ↦ hg k
    have hB : Measurable fun ω ↦
        ∑ k ∈ range N with ¬ k ≤ j, g k ω * ∏ i ∈ Ico (j + 1) k, (X i (ω i))⁻¹ :=
      Finset.measurable_fun_sum _ fun k _ ↦ (hg k).mul (Finset.measurable_fun_prod _ fun i _ ↦ hY i)
    have hGj (ω : ℕ → 𝓧) := sum_mul_prod_Ico_eq (g · ω) (fun i ↦ (X i (ω i))⁻¹) N j
    have hGj' (ω : ℕ → 𝓧) := sum_mul_prod_Ico_succ_eq (g · ω) (fun i ↦ (X i (ω i))⁻¹) N j
    simp_rw [h_upd, hGj]
    refine lintegral_add_mul_inv_le (hS₁ j) (hS₁_ne j) (hX j) (hX_le j) μ j hA hB hA_upd
      fun P' hP' ↦ ?_
    have h_mem (i : ℕ) : Function.update P j P' i ∈ S₁ i := by
      rcases eq_or_ne i j with rfl | hij
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hij]
        exact hP i
    have h_ih := ih (j + 1) (by omega) _ h_mem
    simp_rw [h_upd', hGj'] at h_ih
    exact h_ih

/-- **Replacing the null laws by the alternatives, one coordinate at a time**
[EVR26, Note 40, Theorem 5]. Let `g k` be a function of the first `k` observations such that
`∑ k < N, g k` has integral at most `c` under every product of members of the one-step nulls
`S₁ i` of probability measures. Then `∑ k < N, g k * ∏ i < k, (X i (ω i))⁻¹` has integral at most
`c` under the product of the probability measures `Q₁ i`, for functions `X i` with
`∫⁻ Y / X i ∂Q₁ i ≤ 1` for every e-variable `Y` of `S₁ i`, for instance numeraires of `S₁ i`
against `Q₁ i`: the product of the measures of densities `(X i)⁻¹` with respect to `Q₁ i` behaves
as a member of the effective null of the products. -/
theorem lintegral_sum_mul_prod_inv_le (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    (hS₁_ne : ∀ i, (S₁ i).Nonempty) [∀ i, IsProbabilityMeasure (Q₁ i)]
    (hX : ∀ i, Measurable (X i)) (hX_le : ∀ i, ∀ Y, IsEVar Y (S₁ i) → ∫⁻ x, Y x / X i x ∂Q₁ i ≤ 1)
    {g : ℕ → (ℕ → 𝓧) → ℝ≥0∞} (hg : ∀ k, Measurable (g k))
    (hg_dep : ∀ k, DependsOn (g k) (Set.Iio k)) (N : ℕ) {c : ℝ≥0∞}
    (hg_le : ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁ i) →
      ∫⁻ ω, ∑ k ∈ range N, g k ω ∂Measure.infinitePi P ≤ c) :
    ∫⁻ ω, ∑ k ∈ range N, g k ω * ∏ i ∈ range k, (X i (ω i))⁻¹ ∂Measure.infinitePi Q₁ ≤ c := by
  choose P₀ hP₀ using hS₁_ne
  have := isProbabilityMeasure_ite (Q₁ := Q₁) hS₁ hP₀ 0 N
  have h0 := lintegral_sum_mul_prod_Ico_inv_le hS₁ (fun i ↦ ⟨P₀ i, hP₀ i⟩) hX hX_le hg hg_dep
    hg_le N 0 (zero_add N) P₀ hP₀
  simp only [Nat.Ico_zero_eq_range] at h0
  -- the integrand only depends on the first `N` observations, which have the same laws
  refine le_of_eq_of_le (Measure.lintegral_infinitePi_congr_of_dependsOn (s := range N)
    (fun i hi ↦ ?_) ?_ fun ω ω' h ↦ sum_congr rfl fun k hk ↦ ?_) h0
  · simp [mem_range.1 hi]
  · exact Finset.measurable_fun_sum _ fun k _ ↦ (hg k).mul
      (Finset.measurable_fun_prod _ fun i _ ↦ ((hX i).comp (measurable_pi_apply i)).inv)
  · have hkN := mem_range.1 hk
    rw [hg_dep k fun i hi ↦ h i (by simpa using (Set.mem_Iio.1 hi).trans hkN)]
    exact congrArg _ (prod_congr rfl fun i hi ↦ by
      rw [h i (by simpa using (mem_range.1 hi).trans hkN)])

/-! ### The product of one-step numeraires -/

variable {𝓝 : Set (Measure (ℕ → 𝓧))} {τ : (ℕ → 𝓧) → WithTop ℕ}

/-- **The ratio of an e-process to the product of one-step numeraires** [EVR26, Note 40,
Theorem 5]. Let `S₁ i` be nonempty sets of probability measures on `𝓧`, `Q₁ i` probability
measures and `X i` a numeraire of `S₁ i` against `Q₁ i`. For every null `𝓝` on the sequences that
contains every product of members of the `S₁ i`, every e-process `F` for `𝓝` and the filtration
`Filtration.piLT` of the past observations, and every stopping time `τ` that is finite everywhere,
bounded or not, the ratio of `F` to the product of the `X i` at `τ` has expectation at most one
under the product of the `Q₁ i`. -/
theorem lintegral_div_prod_le_one (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    (hS₁_ne : ∀ i, (S₁ i).Nonempty) [∀ i, IsProbabilityMeasure (Q₁ i)]
    (hX : ∀ i, IsNumeraire (X i) (S₁ i) (Q₁ i))
    (h𝓝 : ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁ i) → Measure.infinitePi P ∈ 𝓝)
    {F : ℕ → (ℕ → 𝓧) → ℝ≥0∞} (hF : IsEProcess F piLT 𝓝)
    (hτ : IsStoppingTime piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    ∫⁻ ω, stoppedValue F τ ω / stoppedValue (fun n ω ↦ ∏ i ∈ range n, X i (ω i)) τ ω
      ∂Measure.infinitePi Q₁ ≤ 1 := by
  -- the stopping time is the cast of a time with values in `ℕ`
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top hτ_top
  simp only [stoppedValue_natCast]
  -- the ratio is the sum over the values `k` of the stopping time of `𝟙{τ = k} F k / ∏ i < k, X i`
  set g : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun k ↦ {ω | τ ω = k}.indicator (F k)
  have hτk (k : ℕ) : MeasurableSet[piLT k] {ω | τ ω = k} := by
    simpa using hτ.measurableSet_eq k
  have hg_ad (k : ℕ) : Measurable[piLT k] (g k) := (hF.adapted k).indicator (hτk k)
  have hg (k : ℕ) : Measurable (g k) := (hg_ad k).mono (piLT.le k) le_rfl
  have h_term (k : ℕ) :
      Measurable fun ω : ℕ → 𝓧 ↦ g k ω * ∏ i ∈ range k, (X i (ω i))⁻¹ :=
    (hg k).mul (Finset.measurable_fun_prod _ fun i _ ↦
      ((hX i).measurable.comp (measurable_pi_apply i)).inv)
  have h_ae : (fun ω ↦ F (τ ω) ω / ∏ i ∈ range (τ ω), X i (ω i)) =ᵐ[Measure.infinitePi Q₁]
      fun ω ↦ ∑' k, g k ω * ∏ i ∈ range k, (X i (ω i))⁻¹ := by
    filter_upwards [ae_forall_ne_zero hS₁ hX] with ω hω
    rw [tsum_eq_single (τ ω) fun k hk ↦ by
      simp [g, Ne.symm hk]]
    have hg_τ : g (τ ω) ω = F (τ ω) ω := by simp [g]
    rw [hg_τ, div_eq_mul_inv,
      ENNReal.prod_inv_distrib fun i _ j _ _ ↦ .inl (hω i)]
  rw [lintegral_congr_ae h_ae, lintegral_tsum fun k ↦ (h_term k).aemeasurable,
    ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N ↦ ?_
  rw [← lintegral_finsetSum _ fun k _ ↦ h_term k]
  refine lintegral_sum_mul_prod_inv_le hS₁ hS₁_ne (fun i ↦ (hX i).measurable)
    (fun i Y hY ↦ (hX i).lintegral_div_le_one hY) hg (fun k ↦ (hg_ad k).dependsOn_of_piLT) N
    fun P hP ↦ ?_
  have hF_le : ∫⁻ ω, F (τ ω) ω ∂Measure.infinitePi P ≤ 1 := by
    simpa only [stoppedValue_natCast] using
      hF.lintegral_le_one hτ (fun _ ↦ WithTop.natCast_ne_top _) (h𝓝 P hP)
  refine (lintegral_mono fun ω ↦ ?_).trans hF_le
  -- at most one term of the sum is not zero
  calc ∑ k ∈ range N, g k ω
  _ = ∑ k ∈ range N, if τ ω = k then F k ω else 0 :=
    sum_congr rfl fun k _ ↦ by simp [g, indicator_apply]
  _ ≤ F (τ ω) ω := by
    rw [sum_ite_eq (range N) (τ ω) fun k ↦ F k ω]
    split_ifs
    exacts [le_rfl, zero_le]

/-- **The product of one-step numeraires is optimal at every stopping time**
[EVR26, Note 40, Theorem 5]. Let `S₁ i` be sets of probability measures on `𝓧`, `Q₁ i`
probability measures, and `X i` a numeraire of `S₁ i` against `Q₁ i` that is `Q₁ i`-almost surely
finite. Let `𝓝` be a null on the sequences that contains every product of members of the `S₁ i`
and for which the product `E n ω = ∏ i < n, X i (ω i)` is an e-process for the filtration
`Filtration.piLT` of the past observations. Then `E` is optimal at every stopping time that is
finite everywhere, bounded or not, against the product of the `Q₁ i`. -/
theorem isNumeraireAt_prod (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    [∀ i, IsProbabilityMeasure (Q₁ i)] (hX : ∀ i, IsNumeraire (X i) (S₁ i) (Q₁ i))
    (hX_top : ∀ i, ∀ᵐ x ∂Q₁ i, X i x ≠ ∞)
    (h𝓝 : ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁ i) → Measure.infinitePi P ∈ 𝓝)
    (hE : IsEProcess (fun n ω ↦ ∏ i ∈ range n, X i (ω i)) piLT 𝓝)
    (hτ : IsStoppingTime piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsNumeraireAt (fun n ω ↦ ∏ i ∈ range n, X i (ω i)) piLT 𝓝 (Measure.infinitePi Q₁) τ := by
  rw [isNumeraireAt_iff hτ.measurable']
  refine ⟨hE, fun F hF ↦ ?_⟩
  -- the product is almost surely positive and finite
  rw [measure_fsupport_eq_measure_univ ?_ ?_, measure_univ]
  · exact lintegral_div_prod_le_one hS₁ (fun i ↦ (hX i).nonempty_of_ae_ne_top (hX_top i)) hX h𝓝
      hF hτ hτ_top
  · filter_upwards [Measure.ae_forall_apply_infinitePi Q₁ hX_top] with ω hω
      using ENNReal.prod_ne_top fun i _ ↦ hω i
  · filter_upwards [ae_forall_ne_zero hS₁ hX] with ω hω using prod_ne_zero_iff.2 fun i _ ↦ hω i

/-- **For the sequential null, the product of one-step numeraires is optimal at every stopping
time** [EVR26, Note 40, Theorem 5]. For the sequential null of the coordinates and one-step nulls
`S₁ i` of probability measures, which contains the laws of independent observations with laws in
the `S₁ i`, and for the product of probability measures `Q₁ i`, the product of numeraires `X i` of
`S₁ i` against `Q₁ i` that are almost surely finite is optimal at every stopping time that is
finite everywhere. -/
theorem isNumeraireAt_prod_sequentialNull (hS₁ : ∀ i, ∀ P ∈ S₁ i, IsProbabilityMeasure P)
    [∀ i, IsProbabilityMeasure (Q₁ i)] (hX : ∀ i, IsNumeraire (X i) (S₁ i) (Q₁ i))
    (hX_top : ∀ i, ∀ᵐ x ∂Q₁ i, X i x ≠ ∞) (hτ : IsStoppingTime piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsNumeraireAt (fun n ω ↦ ∏ i ∈ range n, X i (ω i)) piLT
      (sequentialNull (fun i _ ↦ S₁ i) (fun i ω ↦ ω i) piLT) (Measure.infinitePi Q₁) τ := by
  refine isNumeraireAt_prod hS₁ hX hX_top (fun P hP ↦ ?_) ?_ hτ hτ_top
  · have := fun i ↦ hS₁ i _ (hP i)
    exact infinitePi_mem_sequentialNull fun i ↦ .of_forall fun _ ↦ hP i
  · exact (isTestSupermartingale_prod_sequentialNull (r := fun i _ ↦ X i)
      (fun i ↦ measurable_piLT_apply (Nat.lt_succ_self i))
      (fun i ↦ (hX i).measurable.comp measurable_snd) fun i _ ↦ (hX i).isEVar).isEProcess
      fun _ hP ↦ have := isProbabilityMeasure_of_mem_sequentialNull hP; inferInstance

/-- **The likelihood ratio process is optimal at every stopping time**
[EVR26, Note 40, Proposition 6]. For probability measures `Q₁ ≪ P₁`, the likelihood ratio
process `∏ i < n, (dQ₁/dP₁) (ω i)` of the i.i.d. law of `Q₁` to the i.i.d. law of `P₁` is optimal
at every stopping time that is finite everywhere, for the simple null of the i.i.d. law of `P₁`. -/
theorem isNumeraireAt_prod_rnDeriv {P₁ Q₁ : Measure 𝓧} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] (hQP : Q₁ ≪ P₁)
    (hτ : IsStoppingTime piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsNumeraireAt (fun n ω ↦ ∏ i ∈ range n, Q₁.rnDeriv P₁ (ω i)) piLT
      {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁) τ := by
  have hS : ∀ (_ : ℕ), ∀ P ∈ ({P₁} : Set (Measure 𝓧)), IsProbabilityMeasure P := by
    rintro _ _ rfl
    infer_instance
  have hX : ∀ _ : ℕ, IsNumeraire (Q₁.rnDeriv P₁) {P₁} Q₁ := fun _ ↦ isNumeraire_rnDeriv hQP
  refine isNumeraireAt_prod hS hX (fun _ ↦ hQP.ae_le (Measure.rnDeriv_ne_top Q₁ P₁))
    (fun P hP ↦ by
      rw [funext fun i ↦ mem_singleton_iff.1 (hP i)]
      exact mem_singleton _) ?_ hτ hτ_top
  refine (isNumeraireAt_prod_sequentialNull hS hX
    (fun _ ↦ hQP.ae_le (Measure.rnDeriv_ne_top Q₁ P₁)) hτ hτ_top).isEProcess.anti_set ?_
  rintro _ rfl
  exact infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦ rfl

end ProbabilityTheory
