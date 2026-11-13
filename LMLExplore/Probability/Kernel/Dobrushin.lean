/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Kernel.Composition.Comp
public import LMLExplore.Probability.Kernel.Operator
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Cauchy
public import LMLExplore.Probability.Kernel.TotalVariation
public import Mathlib.Topology.UniformSpace.UniformConvergence

import Mathlib.Analysis.SpecificLimits.Basic
import Statlib.Divergence.TotalVariation
import TauCeti.MeasureTheory.Integral.Bind

/-!
# The Dobrushin coefficient and uniform ergodicity

The *Dobrushin coefficient* (or ergodicity coefficient) of a kernel `κ : Kernel α β` is
`δ(κ) = ⨆ x y, tvDist (κ x) (κ y) / 2`, a number in `[0, 1]` for a Markov kernel. It is the
contraction rate of `κ` in total variation and for the oscillation of functions:
* `tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ δ(κ) * tvDist μ ν` for finite measures of the same mass;
* `osc (κ f) ≤ δ(κ) * osc f` for bounded measurable functions, where `osc f = sup f - inf f`.

It is submultiplicative, `δ(η ∘ₖ κ) ≤ δ(η) * δ(κ)`, and the Doeblin minorization `φ ≤ κ x` for
every `x` gives `δ(κ) ≤ 1 - φ univ`. When the target space is finite, `δ(κ)` is one minus the
infimum of the overlaps `∑ z, min (κ x {z}) (κ y {z})` of two rows of the transition matrix, so
that, for a finite source space too, `δ(κ) < 1` exactly when any two states reach a common state
in one step.

A Markov kernel `κ : Kernel α α` on a nonempty space with `δ(κ ^ m) < 1` for some `m` has a
unique invariant probability measure `π`, and `tvDist ((κ ^ n) x) π ≤ 2 * δ(κ ^ m) ^ (n / m)`
for every `x` and `n`. Conversely, a uniformly ergodic kernel, one whose `n`-step laws converge
to an invariant probability measure in total variation uniformly in the starting point, has
`δ(κ ^ m) ≤ 1 / 2` for some `m`. These are the tools through which the mixing of Markov chains
and the span contraction of the Bellman operators of Markov decision processes are quantified.

## Main definitions

* `ProbabilityTheory.Kernel.dobrushinCoeff κ`: the Dobrushin coefficient
  `⨆ p : α × α, tvDist (κ p.1) (κ p.2) / 2`.
* `ProbabilityTheory.Kernel.IsUniformlyErgodic κ`: `κ` has an invariant probability measure `π`
  with `tvDist ((κ ^ n) x) π → 0` uniformly in `x`.

## Main statements

* `MeasureTheory.tvDist_comp_right_le_dobrushinCoeff_mul`: the contraction in total variation.
* `ProbabilityTheory.Kernel.orderUnitOsc_integralCLM_le`: the contraction of the oscillation of
  bounded measurable functions, and
  `ProbabilityTheory.Kernel.abs_integral_sub_integral_le_dobrushinCoeff_mul` its pointwise form.
* `ProbabilityTheory.Kernel.dobrushinCoeff_comp_le`,
  `ProbabilityTheory.Kernel.dobrushinCoeff_pow_le_pow_div`: submultiplicativity.
* `ProbabilityTheory.Kernel.dobrushinCoeff_le_one_sub_of_forall_le`,
  `ProbabilityTheory.Kernel.dobrushinCoeff_le_one_sub_of_forall_smul_le`: the Doeblin condition.
* `ProbabilityTheory.Kernel.dobrushinCoeff_eq_one_sub_iInf_sum_min`: on a finite target space,
  `δ(κ) = 1 - ⨅ p : α × α, ∑ z, min ((κ p.1).real {z}) ((κ p.2).real {z})`, and
  `ProbabilityTheory.Kernel.dobrushinCoeff_lt_one_iff` the resulting characterization of
  `δ(κ) < 1` on finite spaces.
* `ProbabilityTheory.Kernel.existsUnique_invariant_of_dobrushinCoeff_pow_lt_one`,
  `ProbabilityTheory.Kernel.tvDist_pow_apply_le_two_mul_pow_div`: existence and uniqueness of the
  invariant probability measure, and the geometric convergence to it.
* `ProbabilityTheory.Kernel.isUniformlyErgodic_iff_exists_dobrushinCoeff_pow_lt_one`: on a
  nonempty space, a Markov kernel is uniformly ergodic if and only if `δ(κ ^ m) < 1` for some `m`.

## Implementation notes

The invariant measure is the limit of the laws `(κ ^ n) x₀` from a fixed `x₀`, which form a
Cauchy sequence in total variation at rate `2 * δ(κ ^ n)`. The limit is built setwise by
`MeasureTheory.exists_isProbabilityMeasure_forall_tvDist_le`.

## References

* [R. L. Dobrushin, *Central limit theorem for nonstationary Markov chains. I, II*, 1956][Dob56]
* [D. A. Levin, Y. Peres and E. L. Wilmer, *Markov chains and mixing times*, 2nd edition,
  2017][LPW17], §4.5 and Theorem 4.9
* [M. L. Puterman, *Markov decision processes*, 1994][P], Proposition 6.6.1, where `δ(κ)` is
  defined on finite spaces by the overlap formula
-/

public section

open MeasureTheory Set Filter Topology LMLExplore
open scoped ENNReal NNReal lp

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {κ : Kernel α β}

/-! ### Definition and basic bounds -/

/-- The *Dobrushin coefficient* `δ(κ) = ⨆ x y, tvDist (κ x) (κ y) / 2` of a kernel. For a Markov
kernel it lies in `[0, 1]` (`dobrushinCoeff_nonneg`, `dobrushinCoeff_le_one`), and it is the
contraction rate of `κ` in total variation (`tvDist_comp_right_le_dobrushinCoeff_mul`) and for
the oscillation of functions (`orderUnitOsc_integralCLM_le`). -/
noncomputable def dobrushinCoeff (κ : Kernel α β) : ℝ :=
  ⨆ p : α × α, tvDist (κ p.1) (κ p.2) / 2

lemma dobrushinCoeff_def (κ : Kernel α β) :
    dobrushinCoeff κ = ⨆ p : α × α, tvDist (κ p.1) (κ p.2) / 2 :=
  (rfl)

/-- The Dobrushin coefficient is nonnegative. -/
lemma dobrushinCoeff_nonneg (κ : Kernel α β) : 0 ≤ dobrushinCoeff κ :=
  Real.iSup_nonneg fun _ ↦ div_nonneg tvDist_nonneg zero_le_two

/-- A bound `c ≥ 0` on the total variation distances `tvDist (κ x) (κ y) / 2` bounds the
Dobrushin coefficient. -/
lemma dobrushinCoeff_le {c : ℝ} (hc : 0 ≤ c) (h : ∀ x y, tvDist (κ x) (κ y) ≤ 2 * c) :
    dobrushinCoeff κ ≤ c :=
  Real.iSup_le (fun p ↦ by linarith [h p.1 p.2]) hc

/-- For a Markov kernel, the laws from two starting points are within twice the Dobrushin
coefficient in total variation. -/
lemma tvDist_le_two_mul_dobrushinCoeff [IsMarkovKernel κ] (x y : α) :
    tvDist (κ x) (κ y) ≤ 2 * dobrushinCoeff κ := by
  have hbdd : BddAbove (range fun p : α × α ↦ tvDist (κ p.1) (κ p.2) / 2) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨p, rfl⟩
    linarith [tvDist_le_two (μ := κ p.1) (ν := κ p.2)]
  have := le_ciSup hbdd (x, y)
  rw [← dobrushinCoeff_def] at this
  linarith

/-- For a Markov kernel, `δ(κ) ≤ c` if and only if `tvDist (κ x) (κ y) ≤ 2 * c` for all `x` and
`y`, for every `c ≥ 0`. -/
lemma dobrushinCoeff_le_iff [IsMarkovKernel κ] {c : ℝ} (hc : 0 ≤ c) :
    dobrushinCoeff κ ≤ c ↔ ∀ x y, tvDist (κ x) (κ y) ≤ 2 * c :=
  ⟨fun h x y ↦ (tvDist_le_two_mul_dobrushinCoeff x y).trans (by linarith),
    dobrushinCoeff_le hc⟩

/-- The Dobrushin coefficient of a Markov kernel is at most one. -/
lemma dobrushinCoeff_le_one [IsMarkovKernel κ] : dobrushinCoeff κ ≤ 1 :=
  dobrushinCoeff_le zero_le_one fun x y ↦ by simpa using tvDist_le_two (μ := κ x) (ν := κ y)

/-- The masses that a Markov kernel gives to an event from two starting points differ by at most
its Dobrushin coefficient. -/
lemma abs_measureReal_sub_measureReal_le_dobrushinCoeff [IsMarkovKernel κ] (x y : α) {s : Set β}
    (hs : MeasurableSet s) :
    |(κ x).real s - (κ y).real s| ≤ dobrushinCoeff κ :=
  (abs_measureReal_sub_measureReal_le_tvDist_div_two (by simp) hs).trans
    (by linarith [tvDist_le_two_mul_dobrushinCoeff (κ := κ) x y])

/-! ### Contraction in total variation and of the oscillation -/

/-- **Contraction of the oscillation** by a Markov kernel, pointwise form: if the values of a
measurable function `f` differ by at most `c`, then the integrals of `f` against `κ x` and `κ y`
differ by at most `δ(κ) * c`. -/
theorem abs_integral_sub_integral_le_dobrushinCoeff_mul [IsMarkovKernel κ] {f : β → ℝ} {c : ℝ}
    (hf : Measurable f) (hfc : ∀ y z, f y - f z ≤ c) (x y : α) :
    |∫ z, f z ∂κ x - ∫ z, f z ∂κ y| ≤ dobrushinCoeff κ * c := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure (κ x)
  have hc : 0 ≤ c := by simpa using hfc (Classical.arbitrary β) (Classical.arbitrary β)
  refine (abs_integral_sub_integral_le_mul_tvDist_of_forall_sub_le (by simp)
    hf.aestronglyMeasurable hf.aestronglyMeasurable hfc).trans ?_
  have := tvDist_le_two_mul_dobrushinCoeff (κ := κ) x y
  nlinarith

/-- **Contraction of the oscillation** by a Markov kernel: the oscillation of `κ f` is at most
`δ(κ)` times that of `f`, for bounded measurable functions `f`. -/
theorem orderUnitOsc_integralCLM_le [IsMarkovKernel κ] (f : boundedMeasurable β) :
    orderUnitOsc 1 (κ.integralCLM f) ≤ dobrushinCoeff κ * orderUnitOsc 1 f := by
  refine boundedMeasurable.orderUnitOsc_one_le_of_forall_sub_le
    (mul_nonneg (dobrushinCoeff_nonneg κ) (orderUnitOsc_nonneg _ _)) fun x y ↦ ?_
  rw [integralCLM_apply, integralCLM_apply]
  exact (le_abs_self _).trans <| abs_integral_sub_integral_le_dobrushinCoeff_mul
    (boundedMeasurable.measurable f) (boundedMeasurable.sub_apply_le_orderUnitOsc_one f) x y

end ProbabilityTheory.Kernel

namespace MeasureTheory

open ProbabilityTheory Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

/-- **Contraction in total variation** by a Markov kernel: composing two finite measures `μ` and
`ν` of the same mass with `κ` multiplies their total variation distance by at most the Dobrushin
coefficient of `κ`. -/
theorem tvDist_comp_right_le_dobrushinCoeff_mul [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) (κ : Kernel α β) [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ dobrushinCoeff κ * tvDist μ ν := by
  suffices h : ∀ s, MeasurableSet s →
      (κ ∘ₘ μ).real s ≤ (κ ∘ₘ ν).real s + dobrushinCoeff κ / 2 * tvDist μ ν by
    have := tvDist_le_two_mul_of_forall_measureReal_le_add
      (by rw [Measure.comp_apply_univ, Measure.comp_apply_univ, hμν]) h
    linarith
  intro s hs
  -- the mass of `s` is the integral of `x ↦ κ x s`, whose values differ by at most `δ(κ)`
  have hg : Measurable fun x ↦ (κ x).real s := (κ.measurable_coe hs).ennreal_toReal
  have := abs_integral_sub_integral_le_mul_tvDist_of_forall_sub_le hμν hg.aestronglyMeasurable
    hg.aestronglyMeasurable fun x y ↦
      (le_abs_self _).trans (abs_measureReal_sub_measureReal_le_dobrushinCoeff x y hs)
  rw [Measure.bind_apply_real κ.aemeasurable hs (ae_of_all _ fun _ ↦ measure_ne_top _ _),
    Measure.bind_apply_real κ.aemeasurable hs (ae_of_all _ fun _ ↦ measure_ne_top _ _)]
  linarith [(abs_le.1 this).2]

/-- Composing two probability measures with a Markov kernel `κ` brings them within
`2 * δ(κ)` in total variation. -/
theorem tvDist_comp_right_le_two_mul_dobrushinCoeff [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (κ : Kernel α β) [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ 2 * dobrushinCoeff κ := by
  have h := tvDist_le_two (μ := μ) (ν := ν)
  have := tvDist_comp_right_le_dobrushinCoeff_mul (by simp) κ (μ := μ) (ν := ν)
  nlinarith [dobrushinCoeff_nonneg κ]

end MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {κ : Kernel α β}

/-! ### Submultiplicativity and the Doeblin condition -/

/-- The Dobrushin coefficient is submultiplicative: `δ(η ∘ₖ κ) ≤ δ(η) * δ(κ)`. -/
theorem dobrushinCoeff_comp_le (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    dobrushinCoeff (η ∘ₖ κ) ≤ dobrushinCoeff η * dobrushinCoeff κ := by
  refine dobrushinCoeff_le (mul_nonneg (dobrushinCoeff_nonneg η) (dobrushinCoeff_nonneg κ))
    fun x y ↦ ?_
  rw [comp_apply, comp_apply]
  have := tvDist_comp_right_le_dobrushinCoeff_mul (μ := κ x) (ν := κ y) (by simp) η
  have := tvDist_le_two_mul_dobrushinCoeff (κ := κ) x y
  nlinarith [dobrushinCoeff_nonneg η]

/-- The Dobrushin coefficient of a power of a Markov kernel is at most the power of its Dobrushin
coefficient. -/
theorem dobrushinCoeff_pow_le (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    dobrushinCoeff (κ ^ n) ≤ dobrushinCoeff κ ^ n := by
  induction n with
  | zero => rw [_root_.pow_zero (dobrushinCoeff κ)]; exact dobrushinCoeff_le_one
  | succ n ih =>
    rw [pow_succ, mul_eq_comp, pow_succ]
    exact (dobrushinCoeff_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (dobrushinCoeff_nonneg κ))

/-- The Dobrushin coefficients of the powers of a Markov kernel are nonincreasing. -/
theorem antitone_dobrushinCoeff_pow (κ : Kernel α α) [IsMarkovKernel κ] :
    Antitone fun n ↦ dobrushinCoeff (κ ^ n) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [pow_succ, mul_eq_comp]
  exact (dobrushinCoeff_comp_le _ _).trans
    (mul_le_of_le_one_right (dobrushinCoeff_nonneg _) dobrushinCoeff_le_one)

/-- `δ(κ ^ n) ≤ δ(κ ^ m) ^ (n / m)`: the Dobrushin coefficient of the `m`-step kernel controls
that of all longer powers. -/
theorem dobrushinCoeff_pow_le_pow_div (κ : Kernel α α) [IsMarkovKernel κ] (m n : ℕ) :
    dobrushinCoeff (κ ^ n) ≤ dobrushinCoeff (κ ^ m) ^ (n / m) := by
  conv_lhs => rw [← Nat.div_add_mod n m, Kernel.pow_add, pow_mul]
  exact (dobrushinCoeff_comp_le _ _).trans <|
    (mul_le_of_le_one_right (dobrushinCoeff_nonneg _) dobrushinCoeff_le_one).trans
      (dobrushinCoeff_pow_le _ _)

/-- If `δ(κ ^ m) < 1` for some `m`, the Dobrushin coefficients of the powers of `κ` tend to
zero. -/
theorem tendsto_dobrushinCoeff_pow (κ : Kernel α α) [IsMarkovKernel κ] {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) :
    Tendsto (fun n ↦ dobrushinCoeff (κ ^ n)) atTop (𝓝 0) := by
  -- pass to `m + 1 ≥ 1`, whose coefficient is at most that of `m`
  have hm' : dobrushinCoeff (κ ^ (m + 1)) < 1 :=
    (antitone_dobrushinCoeff_pow κ (Nat.le_succ m)).trans_lt hm
  have hlim : Tendsto (fun n ↦ dobrushinCoeff (κ ^ (m + 1)) ^ (n / (m + 1))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (dobrushinCoeff_nonneg _) hm').comp
      (Nat.tendsto_div_const_atTop m.succ_ne_zero)
  exact squeeze_zero (fun n ↦ dobrushinCoeff_nonneg _)
    (fun n ↦ dobrushinCoeff_pow_le_pow_div κ (m + 1) n) hlim

/-- **Doeblin condition**: if a measure `φ` minorizes every `κ x`, then
`δ(κ) ≤ 1 - φ univ`. -/
theorem dobrushinCoeff_le_one_sub_of_forall_le [Nonempty α] [IsMarkovKernel κ] {φ : Measure β}
    (hφ : ∀ x, φ ≤ κ x) :
    dobrushinCoeff κ ≤ 1 - φ.real univ := by
  have x₀ : α := Classical.arbitrary α
  have : IsFiniteMeasure φ := isFiniteMeasure_of_le _ (hφ x₀)
  have hle (x : α) (s : Set β) : φ.real s ≤ (κ x).real s :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hφ x s)
  have hφ1 : φ.real univ ≤ 1 := by simpa using hle x₀ univ
  refine dobrushinCoeff_le (by linarith) fun x y ↦
    tvDist_le_two_mul_of_forall_measureReal_le_add (by simp) fun s hs ↦ ?_
  -- `κ x s = 1 - κ x sᶜ ≤ 1 - φ sᶜ = 1 - φ univ + φ s ≤ 1 - φ univ + κ y s`
  have h1 := hle x sᶜ
  have h2 := hle y s
  rw [measureReal_compl (μ := φ) hs, measureReal_compl (μ := κ x) hs,
    probReal_univ (μ := κ x)] at h1
  linarith

/-- **Doeblin condition**, normalized form: if `ε • φ ≤ κ x` for every `x`, for a probability
measure `φ`, then `δ(κ) ≤ 1 - ε`. -/
theorem dobrushinCoeff_le_one_sub_of_forall_smul_le [Nonempty α] [IsMarkovKernel κ]
    {φ : Measure β} [IsProbabilityMeasure φ] {ε : ℝ≥0} (hφ : ∀ x, ε • φ ≤ κ x) :
    dobrushinCoeff κ ≤ 1 - ε := by
  simpa using dobrushinCoeff_le_one_sub_of_forall_le hφ

/-! ### Finite target spaces -/

section Finite

variable [Fintype β] [MeasurableSingletonClass β]

/-- **The Dobrushin coefficient on a finite space**: for a Markov kernel from a nonempty space to
a finite one, `δ(κ) = 1 - ⨅ p : α × α, ∑ z, min ((κ p.1).real {z}) ((κ p.2).real {z})`, one minus
the infimum of the overlaps of two rows of the transition matrix. -/
theorem dobrushinCoeff_eq_one_sub_iInf_sum_min [Nonempty α] [IsMarkovKernel κ] :
    dobrushinCoeff κ =
      1 - ⨅ p : α × α, ∑ z, min ((κ p.1).real {z}) ((κ p.2).real {z}) := by
  set s : α × α → ℝ := fun p ↦ ∑ z, min ((κ p.1).real {z}) ((κ p.2).real {z})
  have hs (p : α × α) : 0 ≤ s p :=
    Finset.sum_nonneg fun _ _ ↦ le_min measureReal_nonneg measureReal_nonneg
  have hδ : dobrushinCoeff κ = ⨆ p, (1 - s p) := by
    simp only [dobrushinCoeff_def, tvDist_div_two_eq_one_sub_sum_min, s]
  have hbdd : BddAbove (range fun p ↦ 1 - s p) :=
    ⟨1, forall_mem_range.2 fun p ↦ by linarith [hs p]⟩
  rw [hδ]
  refine le_antisymm (ciSup_le fun p ↦ ?_) (sub_le_comm.1 (le_ciInf fun p ↦ ?_))
  · linarith [ciInf_le ⟨0, forall_mem_range.2 hs⟩ p]
  · linarith [le_ciSup hbdd p]

omit [Fintype β] in
/-- **Scrambling kernels**: a Markov kernel from a finite space to a finite one has Dobrushin
coefficient `δ(κ) < 1` if and only if any two starting points can reach a common state in one
step. -/
theorem dobrushinCoeff_lt_one_iff [Finite α] [Finite β] [IsMarkovKernel κ] :
    dobrushinCoeff κ < 1 ↔ ∀ x y, ∃ z, 0 < κ x {z} ∧ 0 < κ y {z} := by
  have := Fintype.ofFinite β
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [dobrushinCoeff_def]
  -- the infimum over the finite set of pairs is positive exactly when every overlap is
  rw [dobrushinCoeff_eq_one_sub_iInf_sum_min, sub_lt_self_iff, Finite.lt_ciInf_iff, Prod.forall]
  refine forall₂_congr fun x y ↦ ?_
  rw [Finset.sum_pos_iff_of_nonneg fun _ _ ↦ le_min measureReal_nonneg measureReal_nonneg]
  simp [lt_min_iff, measureReal_def, ENNReal.toReal_pos_iff, measure_lt_top]

end Finite

/-! ### Uniform ergodicity -/

/-- A kernel `κ` is *uniformly ergodic* if it has an invariant probability measure `π` such that
the `n`-step laws `(κ ^ n) x` converge to `π` in total variation, uniformly in the starting
point `x`. On a nonempty space, a Markov kernel is uniformly ergodic if and only if `δ(κ ^ m) < 1`
for some `m` (`isUniformlyErgodic_iff_exists_dobrushinCoeff_pow_lt_one`). -/
def IsUniformlyErgodic (κ : Kernel α α) : Prop :=
  ∃ π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π ∧
    TendstoUniformly (fun n x ↦ tvDist ((κ ^ n) x) π) (fun _ ↦ 0) atTop

lemma isUniformlyErgodic_def (κ : Kernel α α) :
    IsUniformlyErgodic κ ↔ ∃ π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π ∧
      TendstoUniformly (fun n x ↦ tvDist ((κ ^ n) x) π) (fun _ ↦ 0) atTop :=
  Iff.rfl

variable {κ : Kernel α α} [IsMarkovKernel κ]

/-- **Distance to an invariant measure**: the `n`-step law from any starting point is within
`2 * δ(κ ^ n)` of an invariant probability measure in total variation. -/
theorem tvDist_pow_apply_le_two_mul_dobrushinCoeff {π : Measure α} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (n : ℕ) (x : α) :
    tvDist ((κ ^ n) x) π ≤ 2 * dobrushinCoeff (κ ^ n) := by
  conv_lhs => rw [← Measure.dirac_bind (κ ^ n).measurable x, ← (hπ.pow n).def]
  exact tvDist_comp_right_le_two_mul_dobrushinCoeff _

/-- **Geometric convergence to an invariant measure**:
`tvDist ((κ ^ n) x) π ≤ 2 * δ(κ ^ m) ^ (n / m)` for an invariant probability measure `π`. -/
theorem tvDist_pow_apply_le_two_mul_pow_div {π : Measure α} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (m n : ℕ) (x : α) :
    tvDist ((κ ^ n) x) π ≤ 2 * dobrushinCoeff (κ ^ m) ^ (n / m) :=
  (tvDist_pow_apply_le_two_mul_dobrushinCoeff hπ n x).trans
    (by linarith [dobrushinCoeff_pow_le_pow_div κ m n])

/-- If `δ(κ ^ m) < 1` for some `m`, two invariant probability measures of `κ` are equal. -/
theorem Invariant.eq_of_dobrushinCoeff_pow_lt_one {π π' : Measure α} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] (hπ : κ.Invariant π) (hπ' : κ.Invariant π') {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) :
    π = π' := by
  -- `tvDist π π' ≤ δ(κ ^ m) * tvDist π π'` with `δ(κ ^ m) < 1`
  have h := tvDist_comp_right_le_dobrushinCoeff_mul (μ := π) (ν := π') (by simp) (κ ^ m)
  rw [(hπ.pow m).def, (hπ'.pow m).def] at h
  have h0 : tvDist π π' = 0 := by nlinarith [tvDist_nonneg (μ := π) (ν := π')]
  exact (tvDist_eq_zero_iff).1 h0

/-- **Existence of an invariant measure**: on a nonempty space, if `δ(κ ^ m) < 1` for some `m`,
the Markov kernel `κ` has an invariant probability measure. -/
theorem exists_invariant_of_dobrushinCoeff_pow_lt_one [Nonempty α] {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) :
    ∃ π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π := by
  have x₀ : α := Classical.arbitrary α
  have h := tendsto_dobrushinCoeff_pow κ hm
  -- the laws `(κ ^ n) x₀` are Cauchy in total variation, at rate `2 * δ(κ ^ n)`
  have hcauchy (n m : ℕ) (hnm : n ≤ m) :
      tvDist ((κ ^ m) x₀) ((κ ^ n) x₀) ≤ 2 * dobrushinCoeff (κ ^ n) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [Kernel.pow_add, comp_apply, ← Measure.dirac_bind (κ ^ n).measurable x₀]
    exact tvDist_comp_right_le_two_mul_dobrushinCoeff _
  obtain ⟨π, hπ, hdist⟩ :=
    exists_isProbabilityMeasure_forall_tvDist_le (by simpa using h.const_mul 2) hcauchy
  -- `tvDist (κ ∘ₘ π) π ≤ tvDist π ((κ ^ n) x₀) + tvDist ((κ ^ (n + 1)) x₀) π → 0`
  refine ⟨π, hπ, ?_⟩
  rw [Invariant]
  refine (tvDist_eq_zero_iff).1 (le_antisymm ?_ tvDist_nonneg)
  have hle (n : ℕ) : tvDist (κ ∘ₘ π) π ≤
      2 * dobrushinCoeff (κ ^ n) + 2 * dobrushinCoeff (κ ^ (n + 1)) := by
    have hstep : (κ ^ (n + 1)) x₀ = κ ∘ₘ (κ ^ n) x₀ := by
      rw [pow_succ', mul_eq_comp, comp_apply]
    calc tvDist (κ ∘ₘ π) π
        ≤ tvDist (κ ∘ₘ π) ((κ ^ (n + 1)) x₀) + tvDist ((κ ^ (n + 1)) x₀) π :=
          tvDist_triangle _ _ _
      _ ≤ tvDist π ((κ ^ n) x₀) + tvDist ((κ ^ (n + 1)) x₀) π := by
          rw [hstep]
          exact add_le_add_left (tvDist_comp_le _ _ κ) _
      _ ≤ _ := by rw [tvDist_comm]; exact add_le_add (hdist n) (hdist (n + 1))
  have hlim : Tendsto (fun n ↦ 2 * dobrushinCoeff (κ ^ n) + 2 * dobrushinCoeff (κ ^ (n + 1)))
      atTop (𝓝 0) := by
    simpa using (h.const_mul 2).add ((h.comp (tendsto_add_atTop_nat 1)).const_mul 2)
  exact ge_of_tendsto' hlim hle

/-- **Uniqueness of the invariant measure**: on a nonempty space, if `δ(κ ^ m) < 1` for some `m`,
the Markov kernel `κ` has a unique invariant probability measure. -/
theorem existsUnique_invariant_of_dobrushinCoeff_pow_lt_one [Nonempty α] {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) :
    ∃! π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π := by
  obtain ⟨π, hπ, hπκ⟩ := exists_invariant_of_dobrushinCoeff_pow_lt_one hm
  exact ⟨π, ⟨hπ, hπκ⟩, fun π' ⟨_, hπ'⟩ ↦ (hπκ.eq_of_dobrushinCoeff_pow_lt_one hπ' hm).symm⟩

/-- A Markov kernel with `δ(κ ^ m) < 1` for some `m` on a nonempty space is uniformly ergodic. -/
theorem isUniformlyErgodic_of_dobrushinCoeff_pow_lt_one [Nonempty α] {m : ℕ}
    (hm : dobrushinCoeff (κ ^ m) < 1) :
    IsUniformlyErgodic κ := by
  obtain ⟨π, hπ, hπκ⟩ := exists_invariant_of_dobrushinCoeff_pow_lt_one hm
  refine ⟨π, hπ, hπκ, Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_⟩
  have h := (tendsto_dobrushinCoeff_pow κ hm).const_mul 2
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg tvDist_nonneg]
  exact (tvDist_pow_apply_le_two_mul_dobrushinCoeff hπκ n x).trans_lt hn

omit [IsMarkovKernel κ] in
/-- A uniformly ergodic kernel has `δ(κ ^ m) ≤ 1 / 2` for some `m`. -/
theorem IsUniformlyErgodic.exists_dobrushinCoeff_pow_le (h : IsUniformlyErgodic κ) :
    ∃ m, dobrushinCoeff (κ ^ m) ≤ 1 / 2 := by
  obtain ⟨π, hπ, -, hlim⟩ := h
  obtain ⟨m, hm⟩ := (Metric.tendstoUniformly_iff.1 hlim (1 / 2) (by norm_num)).exists
  refine ⟨m, dobrushinCoeff_le (by norm_num) fun x y ↦ ?_⟩
  have hx := hm x
  have hy := hm y
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg tvDist_nonneg] at hx hy
  have := tvDist_triangle ((κ ^ m) x) π ((κ ^ m) y)
  rw [tvDist_comm π] at this
  linarith

/-- On a nonempty space, a Markov kernel is uniformly ergodic if and only if `δ(κ ^ m) < 1` for
some `m`. -/
theorem isUniformlyErgodic_iff_exists_dobrushinCoeff_pow_lt_one [Nonempty α] :
    IsUniformlyErgodic κ ↔ ∃ m, dobrushinCoeff (κ ^ m) < 1 :=
  ⟨fun h ↦ (h.exists_dobrushinCoeff_pow_le).imp fun _ hm ↦ hm.trans_lt (by norm_num),
    fun ⟨_, hm⟩ ↦ isUniformlyErgodic_of_dobrushinCoeff_pow_lt_one hm⟩

end ProbabilityTheory.Kernel
