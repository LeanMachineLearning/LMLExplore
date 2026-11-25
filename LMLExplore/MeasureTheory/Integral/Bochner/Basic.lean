/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.Basic.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Expectations of finite suprema, of finite sums, of shifts by constants, of positive parts, of
truncations from above and under combinations of measures

## Main statements

* `MeasureTheory.Integrable.iSup`, `MeasureTheory.iSup_integral_le`: the pointwise supremum of
  finitely many integrable real functions is integrable, and its integral is at least the
  supremum of their integrals. Regrets against the best of finitely many comparators, whose
  expectation is compared with the best expected regret, use them.
* `MeasureTheory.integral_le_mul_integral_of_le_smul`,
  `MeasureTheory.mul_integral_le_integral_of_smul_le`: comparing integrals of a nonnegative real
  function against measures dominated by, or dominating, a multiple `c • μ` with `c : ℝ≥0`.
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
* `MeasureTheory.integrable_min_const`: under a finite measure, the truncation `min f c` of a real
  function whose negative part has a finite mean is integrable.
* `MeasureTheory.tendsto_ofReal_integral_min`: under a finite measure, the means of the
  truncations `min f n` of a real function tend to `𝔼 f⁺ - 𝔼 f⁻` in `ℝ≥0∞`, also when `f⁺` or
  `f⁻` has an infinite mean. Wald's bound on first passage times applies to the truncated
  increments of a random walk whose positive steps need not be integrable.
* `MeasureTheory.posPart_integral_le_integral_posPart`: the positive part of an integral is at
  most the integral of the positive part.
* `MeasureTheory.integral_posPart_sub_posPart_le`: under a probability measure,
  `𝔼 f⁺ - c⁺ ≤ 𝔼 |f - c|`, the positive part being `1`-Lipschitz.
* `MeasureTheory.ae_of_mem_span`, `MeasureTheory.isFiniteMeasure_of_mem_span`,
  `MeasureTheory.integrable_of_mem_span`: almost everywhere properties, finiteness and
  integrability pass from a set `S` of measures to the finite nonnegative combinations of members
  of `S`; `MeasureTheory.ae_of_mem_convexHull`, `MeasureTheory.isFiniteMeasure_of_mem_convexHull`:
  the same for convex combinations.
* `MeasureTheory.integral_eq_zero_of_mem_span`, `MeasureTheory.le_integral_of_mem_convexHull`: a
  function whose integral vanishes (is at least `c`) under every member of `S` has integral `0`
  (at least `c`) under the finite nonnegative (convex) combinations of members of `S`. They are
  used to bound integrals against signed combinations by the total variation
  (`ProbabilityTheory.le_mul_tvDist_of_isExactEVar`).
-/

public section

open Finset
open scoped NNReal

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

section SMulMeasure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {f : Ω → ℝ} {c : ℝ≥0}

/-- If `ν ≤ c • μ`, then the integral against `ν` of a nonnegative integrable real function is at
most `c` times its integral against `μ`. -/
lemma integral_le_mul_integral_of_le_smul (h : ν ≤ c • μ) (hf0 : 0 ≤ᵐ[c • μ] f)
    (hf : Integrable f (c • μ)) : ∫ ω, f ω ∂ν ≤ c * ∫ ω, f ω ∂μ :=
  (integral_mono_measure h hf0 hf).trans_eq <| by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

/-- If `c • μ ≤ ν`, then `c` times the integral against `μ` of a nonnegative integrable real
function is at most its integral against `ν`. -/
lemma mul_integral_le_integral_of_smul_le (h : c • μ ≤ ν) (hf0 : 0 ≤ᵐ[ν] f)
    (hf : Integrable f ν) : c * ∫ ω, f ω ∂μ ≤ ∫ ω, f ω ∂ν :=
  (integral_mono_measure h hf0 hf).trans_eq' <| by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

end SMulMeasure

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

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {S : Set (Measure Ω)} {f : Ω → ℝ} {g : Ω → E} {c : ℝ} {μ : Measure Ω}

/-- A property that holds almost everywhere for every member of a set `S` of measures holds
almost everywhere for every finite nonnegative combination of members of `S`. -/
theorem ae_of_mem_span {p : Ω → Prop} (hS : ∀ P ∈ S, ∀ᵐ x ∂P, p x)
    (hμ : μ ∈ Submodule.span ℝ≥0 S) : ∀ᵐ x ∂μ, p x := by
  induction hμ using Submodule.span_induction with
  | mem P hP => exact hS P hP
  | zero => simp
  | add μ ν _ _ hμ hν => exact ae_add_measure_iff.2 ⟨hμ, hν⟩
  | smul r μ _ hμ => exact Measure.ae_smul_measure hμ r

/-- A property that holds almost everywhere for every member of a set `S` of measures holds
almost everywhere for every convex combination of members of `S`. -/
theorem ae_of_mem_convexHull {p : Ω → Prop} (hS : ∀ P ∈ S, ∀ᵐ x ∂P, p x)
    (hμ : μ ∈ convexHull ℝ≥0 S) : ∀ᵐ x ∂μ, p x :=
  ae_of_mem_span hS (convexHull_min Submodule.subset_span (Submodule.convex _) hμ)

/-- A finite nonnegative combination of finite measures is a finite measure. -/
theorem isFiniteMeasure_of_mem_span (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hμ : μ ∈ Submodule.span ℝ≥0 S) : IsFiniteMeasure μ := by
  induction hμ using Submodule.span_induction with
  | mem P hP => exact hS P hP
  | zero | add | smul => infer_instance

/-- A convex combination of finite measures is a finite measure. -/
theorem isFiniteMeasure_of_mem_convexHull (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hμ : μ ∈ convexHull ℝ≥0 S) : IsFiniteMeasure μ :=
  isFiniteMeasure_of_mem_span hS (convexHull_min Submodule.subset_span (Submodule.convex _) hμ)

/-- A function integrable under every member of a set `S` of measures is integrable under every
finite nonnegative combination of members of `S`. -/
theorem integrable_of_mem_span (hS : ∀ P ∈ S, Integrable g P) (hμ : μ ∈ Submodule.span ℝ≥0 S) :
    Integrable g μ := by
  induction hμ using Submodule.span_induction with
  | mem P hP => exact hS P hP
  | zero => exact integrable_zero_measure
  | add μ ν _ _ hμ hν => exact hμ.add_measure hν
  | smul r μ _ hμ => exact hμ.smul_measure_nnreal

/-- **Integrals against nonnegative combinations of measures**: a function that is integrable with
integral `0` under every member of a set `S` of measures has integral `0` under every finite
nonnegative combination of members of `S`. -/
theorem integral_eq_zero_of_mem_span [NormedSpace ℝ E] (hS : ∀ P ∈ S, Integrable g P)
    (hS0 : ∀ P ∈ S, ∫ x, g x ∂P = 0) (hμ : μ ∈ Submodule.span ℝ≥0 S) : ∫ x, g x ∂μ = 0 := by
  induction hμ using Submodule.span_induction with
  | mem P hP => exact hS0 P hP
  | zero => simp
  | add μ ν hμ' hν' hμ hν =>
    rw [integral_add_measure (integrable_of_mem_span hS hμ') (integrable_of_mem_span hS hν'), hμ,
      hν, add_zero]
  | smul r μ _ hμ => rw [integral_smul_nnreal_measure, hμ, smul_zero]

/-- **Integrals against convex combinations of measures**: a real function that is integrable
with integral at least `c` under every member of a set `S` of measures has integral at least `c`
under every convex combination of members of `S`. -/
theorem le_integral_of_mem_convexHull (hS : ∀ P ∈ S, Integrable f P)
    (hSc : ∀ P ∈ S, c ≤ ∫ x, f x ∂P) (hμ : μ ∈ convexHull ℝ≥0 S) : c ≤ ∫ x, f x ∂μ := by
  refine (convexHull_min (t := {ν | Integrable f ν ∧ c ≤ ∫ x, f x ∂ν})
    (fun P hP ↦ ⟨hS P hP, hSc P hP⟩) ?_ hμ).2
  rintro ν₁ ⟨hν₁, h1c⟩ ν₂ ⟨hν₂, h2c⟩ a b - - hab
  refine ⟨hν₁.smul_measure_nnreal.add_measure hν₂.smul_measure_nnreal, ?_⟩
  rw [integral_add_measure hν₁.smul_measure_nnreal hν₂.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
    smul_eq_mul, smul_eq_mul]
  have hab' : c = a * c + b * c := by
    rw [← add_mul, ← NNReal.coe_add, hab, NNReal.coe_one, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1c a.coe_nonneg, mul_le_mul_of_nonneg_left h2c b.coe_nonneg]

end Combination

section Truncation

open Filter Topology
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Under a finite measure, the truncation `min f c` of a real function `f` from above is
integrable when the negative part of `f` has a finite mean, whether or not its positive part
does. -/
theorem integrable_min_const [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hq : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≠ ∞) (c : ℝ) :
    Integrable (fun ω ↦ min (f ω) c) μ := by
  refine Integrable.mono' ((integrable_const |c|).add
    (integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp_aemeasurable hf.neg) hq))
    (hf.min aemeasurable_const).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.add_apply, Function.comp_apply, Pi.neg_apply, ENNReal.toReal_ofReal',
    Real.norm_eq_abs, abs_le]
  -- `-|c| - (f ω)⁻ ≤ min (f ω) c ≤ |c|`
  exact ⟨le_min (by linarith [le_max_left (-f ω) 0, abs_nonneg c])
      (by linarith [neg_abs_le c, le_max_right (-f ω) 0]),
    by linarith [min_le_right (f ω) c, le_abs_self c, le_max_right (-f ω) 0]⟩

/-- **Monotone convergence for truncations from above.** Under a finite measure, the means of the
truncations `min f n` of a real function `f` tend to `𝔼 f⁺ - 𝔼 f⁻` in `ℝ≥0∞`, where `f⁺` may have
an infinite mean. When `f⁻` has an infinite mean, the truncations are not integrable, their
Bochner integrals vanish and so does the limit. -/
theorem tendsto_ofReal_integral_min [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (∫ ω, min (f ω) n ∂μ)) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ - ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ)) := by
  set q := ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ
  by_cases hq : q = ∞
  · rw [hq, ENNReal.sub_top]
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [integral_undef fun hint ↦ ?_, ENNReal.ofReal_zero]
    have h := hint.neg.lintegral_lt_top
    -- truncating at `n ≥ 0` does not change the negative part
    simp only [Pi.neg_apply, ENNReal.ofReal_neg_min_of_nonneg n.cast_nonneg] at h
    exact h.ne hq
  -- the truncation at `n` has mean `𝔼[min f⁺ n] - 𝔼 f⁻`
  have hmean (n : ℕ) :
      ENNReal.ofReal (∫ ω, min (f ω) n ∂μ) = ∫⁻ ω, ENNReal.ofReal (min (f ω) n) ∂μ - q := by
    have hn : ∫⁻ _, ENNReal.ofReal n ∂μ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
    have hfin : ∫⁻ ω, ENNReal.ofReal (min (f ω) n) ∂μ ≠ ∞ :=
      ((lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_lt hn).ne
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_min_const hf hq n)]
    simp_rw [ENNReal.ofReal_neg_min_of_nonneg n.cast_nonneg]
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_toReal hq]
  simp_rw [hmean]
  refine ENNReal.Tendsto.sub ?_ tendsto_const_nhds (Or.inr hq)
  -- monotone convergence for the positive parts
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n ↦ ENNReal.measurable_ofReal.comp_aemeasurable (hf.min aemeasurable_const))
    (ae_of_all _ fun ω n n' h ↦ ENNReal.ofReal_le_ofReal (min_le_min_left _ (mod_cast h)))
    (ae_of_all _ fun ω ↦ tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop ⌈f ω⌉₊] with n hn
  rw [min_eq_left ((Nat.le_ceil _).trans (mod_cast hn))]

end Truncation

end MeasureTheory
