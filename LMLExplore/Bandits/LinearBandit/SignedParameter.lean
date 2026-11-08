/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.LinearBandit.Basic
public import LMLExplore.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Parameters with signed coordinates, for the lower bounds of linear bandits

The minimax lower bounds for linear bandits [LS, Theorems 24.1 and 24.2] compare the parameters
`θ` whose coordinates in an orthonormal basis `b` are `Δ * s i`, for signs `s i = ±1`, and count
the rounds at which the `i`-th coordinate `⟪b i, x⟫` of the feature `x` played does not have the
sign `s i`. This file collects the facts about these parameters and counts that both bounds use.

## Main statements

* `LMLExplore.Bandits.inner_eq_sum_of_inner_basis`,
  `LMLExplore.Bandits.inner_sub_eq_of_inner_basis`: the inner product with a parameter with
  coordinates `Δ * s i`, and with the difference of two such parameters whose signs differ only at
  one coordinate.
* `LMLExplore.Bandits.measurableSet_mul_inner_nonpos`,
  `LMLExplore.Bandits.compl_setOf_mul_nonpos_subset`: the set of actions whose feature does not
  have the sign `s i` at the coordinate `i` is measurable, and its complement is contained in the
  corresponding set for the sign `-s i`.
* `LMLExplore.Bandits.mul_sum_sum_measureReal_le_mul_integral_linearRegret`: if the gap of every
  action is at least `Δ / C` times the number of the sets `S i` that contain it, then the expected
  regret is at least `Δ / C` times the expected number of pairs of a round and an index `i` such
  that the action played lies in `S i`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorems 24.1 and 24.2.
-/

public section

open MeasureTheory Finset
open scoped InnerProductSpace

namespace LMLExplore.Bandits

variable {ι 𝓐 E Ω : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {b : OrthonormalBasis ι ℝ E} {θ θ' : E} {Δ : ℝ} {s s' : ι → ℝ}

/-- The inner product with a parameter whose coordinates in the basis `b` are `Δ * s i`. -/
lemma inner_eq_sum_of_inner_basis (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (x : E) :
    ⟪θ, x⟫_ℝ = ∑ i, Δ * s i * ⟪b i, x⟫_ℝ := by
  rw [← b.sum_inner_mul_inner θ x]
  exact sum_congr rfl fun i _ ↦ by rw [real_inner_comm (b i) θ, hθ]

/-- The inner product with the difference of two parameters whose coordinates in the basis `b` are
`Δ * s j` and `Δ * s' j`, for signs that agree except at `i`, where `s' i = -s i`. -/
lemma inner_sub_eq_of_inner_basis (hθ : ∀ j, ⟪b j, θ⟫_ℝ = Δ * s j)
    (hθ' : ∀ j, ⟪b j, θ'⟫_ℝ = Δ * s' j) {i : ι} (hs'i : s' i = -s i) (hs' : ∀ j ≠ i, s' j = s j)
    (x : E) :
    ⟪θ - θ', x⟫_ℝ = 2 * Δ * s i * ⟪b i, x⟫_ℝ := by
  rw [inner_sub_left, inner_eq_sum_of_inner_basis hθ, inner_eq_sum_of_inner_basis hθ',
    ← sum_sub_distrib, Fintype.sum_eq_single i fun j hj ↦ by rw [hs' j hj, sub_self], hs'i]
  ring

/-- A point at which `c * f` is positive is one at which `c' * f` is nonpositive, for `c' = -c`. -/
lemma compl_setOf_mul_nonpos_subset {α : Type*} (f : α → ℝ) {c c' : ℝ} (hc : c' = -c) :
    {x | c * f x ≤ 0}ᶜ ⊆ {x | c' * f x ≤ 0} := fun x hx ↦ by
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx ⊢
  rw [hc, neg_mul]
  exact neg_nonpos.2 hx.le

variable [MeasurableSpace 𝓐] {φ : 𝓐 → E}

/-- The set of actions whose feature has a nonpositive `i`-th coordinate times `s i` in the basis
`b` is measurable. -/
lemma measurableSet_mul_inner_nonpos [MeasurableSpace E] [OpensMeasurableSpace E]
    (hφ : Measurable φ) (b : OrthonormalBasis ι ℝ E) (s : ι → ℝ) (i : ι) :
    MeasurableSet {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0} :=
  measurableSet_le ((hφ.const_inner' (b i)).const_mul (s i)) measurable_const

/-- **The regret counts the bad rounds.** For a fixed action set, let `S i` be measurable sets of
actions, indexed by a finite type, and let the gap of every action `a` be at least `Δ / C` times
the number of the `S i` that contain `a`. Then the expected regret after `n` rounds, under a
finite measure, is at least `Δ / C` times the expected number of pairs of a round `t < n` and an
index `i` such that `A t ∈ S i`. The bound `B` on the expected rewards makes the regret
integrable. -/
theorem mul_sum_sum_measureReal_le_mul_integral_linearRegret {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {A : ℕ → Ω → 𝓐} (hA : ∀ t, Measurable (A t))
    (hθ : Measurable fun a ↦ ⟪θ, φ a⟫_ℝ) {B : ℝ} (hB : ∀ a, |⟪θ, φ a⟫_ℝ| ≤ B)
    {S : ι → Set 𝓐} (hS : ∀ i, MeasurableSet (S i)) {C : ℝ}
    (hgap : ∀ a, Δ * ∑ i, (S i).indicator 1 a ≤ C * ((⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ))
    (O : ℕ → Ω → Unit) (n : ℕ) :
    Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' S i) ≤
      C * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
  have hind (i : ι) (t : ℕ) : Integrable ((A t ⁻¹' S i).indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator (hA t (hS i))
  have hreg : Integrable (fun ω ↦ linearRegret (fun _ ↦ φ) θ O A n ω) P :=
    integrable_linearRegret (fun _ ↦ measurable_of_subsingleton_codomain _) hA
      (hθ.comp measurable_snd) measurable_const fun _ ↦ hB
  calc Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' S i)
      = ∫ ω, Δ * ∑ i, ∑ t ∈ range n, (A t ⁻¹' S i).indicator 1 ω ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun t _ ↦
          hind i t]
        simp_rw [integral_finsetSum _ fun t _ ↦ hind _ t, integral_indicator_one (hA _ (hS _))]
    _ ≤ ∫ ω, C * linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
        refine integral_mono (((integrable_finsetSum _ fun i _ ↦
          integrable_finsetSum _ fun t _ ↦ hind i t)).const_mul Δ) (hreg.const_mul C) fun ω ↦ ?_
        rw [linearRegret_def, sum_comm, mul_sum, mul_sum]
        exact sum_le_sum fun t _ ↦ hgap (A t ω)
    _ = C * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := integral_const_mul _ _

end LMLExplore.Bandits
