/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Expectations of finite suprema, of finite sums, of shifts by constants and of positive parts

## Main statements

* `MeasureTheory.Integrable.iSup`, `MeasureTheory.iSup_integral_le`: the pointwise supremum of
  finitely many integrable real functions is integrable, and its integral is at least the
  supremum of their integrals. Regrets against the best of finitely many comparators, whose
  expectation is compared with the best expected regret, use them.
* `MeasureTheory.integral_le_const`: under a probability measure, an integrable real function that
  is almost surely at most `c` has expectation at most `c`.
* `MeasureTheory.integral_sub_const`, `MeasureTheory.integral_const_sub`: under a probability
  measure, the integral of `f - c` is `∫ f - c`, and that of `c - f` is `c - ∫ f`.
* `MeasureTheory.one_sub_le_integral_one_sub`: under a probability measure, if `Y ∈ [0, 1]`
  almost surely has mean at most `m`, then `1 - Y` has mean at least `1 - m`.
* `MeasureTheory.integral_const_sub_sum`: under a probability measure, the expectation of
  `c - ∑ i ∈ s, g i` is `c - ∑ i ∈ s, ∫ g i ∂P`.
* `MeasureTheory.integral_sum_le_add_mul_of_ae_le`: under a probability measure, an almost sure
  bound `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0` gives `∫ ∑ i ∈ s, Z i ∂P ≤ B + c C` when
  the expectations of the `V i` sum to at most `C`.
* `MeasureTheory.posPart_integral_le_integral_posPart`: the positive part of an integral is at
  most the integral of the positive part.
* `MeasureTheory.integral_posPart_sub_posPart_le`: under a probability measure,
  `𝔼 f⁺ - c⁺ ≤ 𝔼 |f - c|`, the positive part being `1`-Lipschitz.
* `MeasureTheory.integral_eq_zero_of_mem_span`, `MeasureTheory.le_integral_of_mem_convexHull`: a
  bounded function whose integral vanishes (is at least `c`) under every member of a set of finite
  measures stays bounded and has integral `0` (at least `c`) under the finite nonnegative (convex)
  combinations of these measures. They bound integrals against signed combinations of measures by
  the total variation.
-/

public section

open Finset

namespace MeasureTheory

section Supremum

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Finite ι] {f : ι → Ω → ℝ}

/-- The pointwise supremum of finitely many integrable real functions is integrable. -/
lemma Integrable.iSup (hf : ∀ i, Integrable (f i) μ) : Integrable (fun ω ↦ ⨆ i, f i ω) μ := by
  have := Fintype.ofFinite ι
  refine Integrable.mono' (integrable_finsetSum univ fun i _ ↦ (hf i).abs)
    (AEMeasurable.iSup fun i ↦ (hf i).aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ f i ω)
  rw [← hj, Real.norm_eq_abs]
  exact single_le_sum (f := fun i ↦ |f i ω|) (fun i _ ↦ abs_nonneg _) (mem_univ j)

/-- The supremum of the integrals of finitely many integrable real functions is at most the
integral of their pointwise supremum. -/
lemma iSup_integral_le (hf : ∀ i, Integrable (f i) μ) :
    ⨆ i, ∫ ω, f i ω ∂μ ≤ ∫ ω, ⨆ i, f i ω ∂μ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  exact ciSup_le fun i ↦ integral_mono (hf i) (Integrable.iSup hf) fun ω ↦
    le_ciSup (Set.finite_range fun i ↦ f i ω).bddAbove i

end Supremum

section PositivePart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The positive part of an integral is at most the integral of the positive part. -/
lemma posPart_integral_le_integral_posPart (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ)⁺ ≤ ∫ ω, (f ω)⁺ ∂μ := by
  rw [posPart_def]
  refine sup_le ?_ (integral_nonneg fun ω ↦ posPart_nonneg _)
  by_cases hf : Integrable f μ
  · exact integral_mono hf hf.pos_part fun ω ↦ le_posPart _
  · rw [integral_undef hf]
    exact integral_nonneg fun ω ↦ posPart_nonneg _

end PositivePart

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {s : Finset ι}

/-- Under a probability measure, the expectation of an integrable real function that is almost
surely at most `c` is at most `c`. -/
lemma integral_le_const {f : Ω → ℝ} {c : ℝ} (hf : Integrable f P) (h : ∀ᵐ ω ∂P, f ω ≤ c) :
    ∫ ω, f ω ∂P ≤ c :=
  (integral_mono_ae hf (integrable_const c) h).trans_eq (by simp)

section Const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

/-- Under a probability measure, the integral of an integrable function minus a constant is the
integral of the function minus the constant. -/
lemma integral_sub_const (hf : Integrable f P) (c : E) :
    ∫ ω, (f ω - c) ∂P = ∫ ω, f ω ∂P - c := by
  rw [integral_sub hf (integrable_const c), integral_const, probReal_univ, one_smul]

/-- Under a probability measure, the integral of a constant minus an integrable function is the
constant minus the integral of the function. -/
lemma integral_const_sub (c : E) (hf : Integrable f P) :
    ∫ ω, (c - f ω) ∂P = c - ∫ ω, f ω ∂P := by
  rw [integral_sub (integrable_const c) hf, integral_const, probReal_univ, one_smul]

end Const

/-- Under a probability measure, if `Y ∈ [0, 1]` almost surely has mean at most `m`, then `1 - Y`
has mean at least `1 - m`. -/
lemma one_sub_le_integral_one_sub {Y : Ω → ℝ} {m : ℝ} (hYm : AEMeasurable Y P)
    (hY : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc 0 1) (h : ∫ ω, Y ω ∂P ≤ m) :
    1 - m ≤ ∫ ω, 1 - Y ω ∂P := by
  rw [integral_const_sub 1 (.of_mem_Icc 0 1 hYm hY)]
  linarith

/-- Under a probability measure, the expectation of a constant minus a finite sum of integrable
real functions is the constant minus the sum of their expectations. -/
lemma integral_const_sub_sum (c : ℝ) {g : ι → Ω → ℝ} (hg : ∀ i ∈ s, Integrable (g i) P) :
    ∫ ω, (c - ∑ i ∈ s, g i ω) ∂P = c - ∑ i ∈ s, ∫ ω, g i ω ∂P := by
  rw [integral_const_sub c (integrable_finsetSum _ hg), integral_finsetSum _ hg]

/-- If almost surely `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0`, where the `Z i` and `V i`
are integrable and the expectations of the `V i` sum to at most `C`, then the expectation of
`∑ i ∈ s, Z i` is at most `B + c C`. The analyses of Exp3 and Exp4 use it to turn pathwise bounds
into bounds on the expected estimated regret. -/
lemma integral_sum_le_add_mul_of_ae_le {Z V : ι → Ω → ℝ} {B c C : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ i ∈ s, Integrable (Z i) P) (hV : ∀ i ∈ s, Integrable (V i) P)
    (hVC : ∑ i ∈ s, ∫ ω, V i ω ∂P ≤ C)
    (hZV : ∀ᵐ ω ∂P, ∑ i ∈ s, Z i ω ≤ B + c * ∑ i ∈ s, V i ω) :
    ∫ ω, ∑ i ∈ s, Z i ω ∂P ≤ B + c * C := by
  calc ∫ ω, ∑ i ∈ s, Z i ω ∂P
  _ ≤ ∫ ω, B + c * ∑ i ∈ s, V i ω ∂P := by
      refine integral_mono_ae (integrable_finsetSum _ hZ)
        ((integrable_const _).add ((integrable_finsetSum _ hV).const_mul _)) ?_
      filter_upwards [hZV] with ω hω
      exact hω
  _ = B + c * ∑ i ∈ s, ∫ ω, V i ω ∂P := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ hV).const_mul _),
        integral_const_mul, integral_finsetSum _ hV, integral_const, probReal_univ, one_smul]
  _ ≤ B + c * C := by gcongr

/-- Under a probability measure, `𝔼 f⁺ - c⁺ ≤ 𝔼 |f - c|` for an integrable real function `f`,
since the positive part is `1`-Lipschitz. -/
lemma integral_posPart_sub_posPart_le {f : Ω → ℝ} (hf : Integrable f P) (c : ℝ) :
    ∫ ω, (f ω)⁺ ∂P - c⁺ ≤ ∫ ω, |f ω - c| ∂P := by
  have hf' : Integrable (fun ω ↦ (f ω)⁺) P := hf.pos_part
  rw [← integral_sub_const hf']
  refine integral_mono (hf'.sub (integrable_const _)) (hf.sub (integrable_const c)).abs
    fun ω ↦ (le_abs_self _).trans ?_
  simpa [← Real.dist_eq] using lipschitzWith_posPart.dist_le_mul (f ω) c

section Combination

open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {f : Ω → ℝ} {M c : ℝ}
  {μ : Measure Ω}

/-- **Integrals against nonnegative combinations of measures**: if a measurable `f` is bounded by
`M` almost everywhere and has integral `0` under every member of a set `S` of finite measures,
then every finite nonnegative combination `μ` of members of `S` is a finite measure under which
`f` is bounded by `M` almost everywhere and has integral `0`. -/
theorem integral_eq_zero_of_mem_span (hS : ∀ P ∈ S, IsFiniteMeasure P) (hf : Measurable f)
    (hSM : ∀ P ∈ S, ∀ᵐ x ∂P, |f x| ≤ M) (hS0 : ∀ P ∈ S, ∫ x, f x ∂P = 0)
    (hμ : μ ∈ Submodule.span ℝ≥0 S) :
    IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, |f x| ≤ M) ∧ ∫ x, f x ∂μ = 0 := by
  have hint {ν : Measure Ω} [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, |f x| ≤ M) : Integrable f ν :=
    .of_bound hf.aestronglyMeasurable M (hν.mono fun x hx ↦ by rwa [Real.norm_eq_abs])
  induction hμ using Submodule.span_induction with
  | mem P hP => exact ⟨hS P hP, hSM P hP, hS0 P hP⟩
  | zero => exact ⟨inferInstance, by simp, by simp⟩
  | add μ ν _ _ hμ hν =>
    obtain ⟨_, hμM, hμ0⟩ := hμ
    obtain ⟨_, hνM, hν0⟩ := hν
    refine ⟨inferInstance, ae_add_measure_iff.2 ⟨hμM, hνM⟩, ?_⟩
    rw [integral_add_measure (hint hμM) (hint hνM), hμ0, hν0, add_zero]
  | smul r μ _ hμ =>
    obtain ⟨_, hμM, hμ0⟩ := hμ
    exact ⟨inferInstance, Measure.ae_smul_measure hμM r,
      by rw [integral_smul_nnreal_measure, hμ0, smul_zero]⟩

/-- **Integrals against convex combinations of measures**: if a measurable `f` is bounded by `M`
almost everywhere and has integral at least `c` under every member of a set `S` of finite
measures, then every convex combination `μ` of members of `S` is a finite measure under which
`f` is bounded by `M` almost everywhere and has integral at least `c`. -/
theorem le_integral_of_mem_convexHull (hS : ∀ P ∈ S, IsFiniteMeasure P) (hf : Measurable f)
    (hSM : ∀ P ∈ S, ∀ᵐ x ∂P, |f x| ≤ M) (hSc : ∀ P ∈ S, c ≤ ∫ x, f x ∂P)
    (hμ : μ ∈ convexHull ℝ≥0 S) :
    IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, |f x| ≤ M) ∧ c ≤ ∫ x, f x ∂μ := by
  have hint {ν : Measure Ω} [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, |f x| ≤ M) : Integrable f ν :=
    .of_bound hf.aestronglyMeasurable M (hν.mono fun x hx ↦ by rwa [Real.norm_eq_abs])
  refine convexHull_min (t := {ν | IsFiniteMeasure ν ∧ (∀ᵐ x ∂ν, |f x| ≤ M) ∧
    c ≤ ∫ x, f x ∂ν}) (fun P hP ↦ ⟨hS P hP, hSM P hP, hSc P hP⟩) ?_ hμ
  intro ν₁ hν₁ ν₂ hν₂ a b _ _ hab
  obtain ⟨_, h1M, h1c⟩ := hν₁
  obtain ⟨_, h2M, h2c⟩ := hν₂
  have h1M' := Measure.ae_smul_measure h1M a
  have h2M' := Measure.ae_smul_measure h2M b
  refine ⟨inferInstance, ae_add_measure_iff.2 ⟨h1M', h2M'⟩, ?_⟩
  rw [integral_add_measure (hint h1M') (hint h2M'), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]
  have hab' : (a : ℝ) * c + b * c = c := by
    rw [← add_mul, ← NNReal.coe_add, hab, NNReal.coe_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1c a.coe_nonneg, mul_le_mul_of_nonneg_left h2c b.coe_nonneg]

end Combination

end MeasureTheory
