/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Tilted

/-!
# Exponential tilts and the cumulant generating function

Tilting a measure `μ` by `t * X` shifts the moment and cumulant generating functions of `X`:
under `μ.tilted (t * X ·)`, the moment generating function of `X` is
`s ↦ mgf X μ (t + s) / mgf X μ t` and its cumulant generating function is
`s ↦ cgf X μ (t + s) - cgf X μ t`. Together with Mathlib's `variance_tilted_mul`, which identifies
the second derivative of the cumulant generating function with a variance, this shows that the
derivative of the cumulant generating function is monotone on the interior of
`integrableExpSet X μ`, and strictly increasing there as soon as `X` is not almost surely
constant. For a measure on `ℝ` and `X = id`, that derivative is the mean of the exponential tilts,
so the tilts of a probability measure which is not a Dirac mass by parameters in that interior
have pairwise distinct means.

Comparing a measure with its tilts also bounds probabilities from below. Under the tilt by
`t * X`, the event that `X` is near its mean `deriv (cgf X μ) t` has probability close to `1` by
Chebyshev's inequality, and the density of the tilt is bounded on that event. This change of
measure proves the lower bound of Cramér's theorem.

## Main statements

* `ProbabilityTheory.mgf_tilted_mul`: `mgf X (μ.tilted (t * X ·)) s = mgf X μ (t + s) / mgf X μ t`.
* `ProbabilityTheory.cgf_tilted_mul`: `cgf X (μ.tilted (t * X ·)) s = cgf X μ (t + s) - cgf X μ t`.
* `ProbabilityTheory.integrableExpSet_tilted_mul`: the set `integrableExpSet X` of the tilted
  measure is `integrableExpSet X μ` translated by `-t`.
* `ProbabilityTheory.iteratedDeriv_two_cgf_pos`: if `X` is not almost surely constant, the second
  derivative of `cgf X μ` is positive on the interior of `integrableExpSet X μ`.
* `ProbabilityTheory.hasStrictDerivAt_deriv_cgf`: on the interior of `integrableExpSet X μ`,
  the derivative of `deriv (cgf X μ)` is `iteratedDeriv 2 (cgf X μ)`.
* `ProbabilityTheory.monotoneOn_deriv_cgf`: `deriv (cgf X μ)` is monotone on the interior of
  `integrableExpSet X μ`.
* `ProbabilityTheory.strictMonoOn_deriv_cgf`: if `X` is not almost surely constant,
  `deriv (cgf X μ)` is strictly increasing on the interior of `integrableExpSet X μ`.
* `ProbabilityTheory.iteratedDeriv_two_cgf_id_pos`, `ProbabilityTheory.strictMonoOn_deriv_cgf_id`:
  the versions for a probability measure on `ℝ` which is not a Dirac mass.
* `ProbabilityTheory.exp_mul_le_measureReal_abs_sub_deriv_cgf_le`: for `t` in the interior of
  `integrableExpSet X μ`, `Λ = cgf X μ` and `c > 0`,
  `exp (-(t Λ'(t) - Λ(t) + |t| c)) (1 - Λ''(t) / c²) ≤ μ(|X - Λ'(t)| ≤ c)`.
-/

public section

open MeasureTheory Real Set

open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t s : ℝ}

/-- The moment generating function of `X` under the tilted measure `μ.tilted (t * X ·)` is
`s ↦ mgf X μ (t + s) / mgf X μ t`. -/
lemma mgf_tilted_mul : mgf X (μ.tilted (t * X ·)) s = mgf X μ (t + s) / mgf X μ t := by
  simp only [mgf]
  rw [integral_tilted, ← integral_div]
  congr with ω
  rw [smul_eq_mul, add_mul, exp_add]
  ring

/-- The cumulant generating function of `X` under the tilted measure `μ.tilted (t * X ·)` is
`s ↦ cgf X μ (t + s) - cgf X μ t`, where both exponential moments exist. -/
lemma cgf_tilted_mul (ht : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (hts : Integrable (fun ω ↦ exp ((t + s) * X ω)) μ) :
    cgf X (μ.tilted (t * X ·)) s = cgf X μ (t + s) - cgf X μ t := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  rw [cgf, mgf_tilted_mul, log_div (mgf_pos' hμ.out hts).ne' (mgf_pos' hμ.out ht).ne', cgf, cgf]

/-- Under the tilted measure `μ.tilted (t * X ·)`, the exponential moment `exp (s * X)` is
integrable if and only if `exp ((t + s) * X)` is integrable under `μ`. -/
lemma integrableExpSet_tilted_mul (ht : t ∈ integrableExpSet X μ) :
    integrableExpSet X (μ.tilted (t * X ·)) = (t + ·) ⁻¹' integrableExpSet X μ := by
  ext s
  simp only [integrableExpSet, mem_ofPred_eq, mem_preimage]
  rw [integrable_tilted_iff ht]
  simp_rw [smul_eq_mul, ← exp_add, ← add_mul]

/-- If `X` is not almost surely constant, the second derivative of its cumulant generating
function is positive on the interior of `integrableExpSet X μ`: it is the variance of `X` under
the tilted measure `μ.tilted (t * X ·)`, which has the same null sets as `μ`. -/
lemma iteratedDeriv_two_cgf_pos (hX : ∀ c, ¬ X =ᵐ[μ] fun _ ↦ c)
    (ht : t ∈ interior (integrableExpSet X μ)) :
    0 < iteratedDeriv 2 (cgf X μ) t := by
  rw [← variance_tilted_mul ht]
  refine (variance_nonneg _ _).lt_of_ne' fun h ↦ hX (μ.tilted (t * X ·))[X] ?_
  exact (absolutelyContinuous_tilted (interior_subset ht)).ae_le
    (ae_eq_integral_of_variance_eq_zero (memLp_tilted_mul ht 2) h)

/-- On the interior of `integrableExpSet X μ`, the derivative of the derivative of the cumulant
generating function is its second iterated derivative, in the strict sense. -/
lemma hasStrictDerivAt_deriv_cgf (ht : t ∈ interior (integrableExpSet X μ)) :
    HasStrictDerivAt (deriv (cgf X μ)) (iteratedDeriv 2 (cgf X μ) t) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (analyticOnNhd_cgf.deriv t ht).hasStrictDerivAt

/-- The derivative of the cumulant generating function is monotone on the interior of
`integrableExpSet X μ`: the cumulant generating function is convex there. -/
lemma monotoneOn_deriv_cgf : MonotoneOn (deriv (cgf X μ)) (interior (integrableExpSet X μ)) := by
  refine monotoneOn_of_deriv_nonneg convex_integrableExpSet.interior
    analyticOnNhd_cgf.deriv.continuousOn
    (analyticOnNhd_cgf.deriv.differentiableOn.mono interior_subset) fun t ht ↦ ?_
  rw [interior_interior] at ht
  rw [(hasStrictDerivAt_deriv_cgf ht).hasDerivAt.deriv, ← variance_tilted_mul ht]
  exact variance_nonneg _ _

/-- If `X` is not almost surely constant, the derivative of its cumulant generating function is
strictly increasing on the interior of `integrableExpSet X μ`. -/
lemma strictMonoOn_deriv_cgf (hX : ∀ c, ¬ X =ᵐ[μ] fun _ ↦ c) :
    StrictMonoOn (deriv (cgf X μ)) (interior (integrableExpSet X μ)) := by
  refine strictMonoOn_of_deriv_pos convex_integrableExpSet.interior
    analyticOnNhd_cgf.deriv.continuousOn fun t ht ↦ ?_
  rw [interior_interior] at ht
  rw [(hasStrictDerivAt_deriv_cgf ht).hasDerivAt.deriv]
  exact iteratedDeriv_two_cgf_pos hX ht

/-- The derivative of the cumulant generating function of a probability measure on `ℝ` which is
not a Dirac mass is strictly increasing on the interior of `integrableExpSet id ρ`. This
derivative is the mean of the exponential tilt `ρ.tilted (t * ·)` (`integral_tilted_mul_self`). -/
lemma strictMonoOn_deriv_cgf_id {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ c, ρ ≠ Measure.dirac c) :
    StrictMonoOn (deriv (cgf id ρ)) (interior (integrableExpSet id ρ)) :=
  strictMonoOn_deriv_cgf fun c h ↦ hρ c <| by simpa using (hasLaw_dirac_of_ae_eq h).map_eq

/-- The second derivative of the cumulant generating function of a probability measure on `ℝ`
which is not a Dirac mass is positive on the interior of `integrableExpSet id ρ`. It is the
variance of the exponential tilt `ρ.tilted (t * ·)` (`variance_tilted_mul`). -/
lemma iteratedDeriv_two_cgf_id_pos {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ c, ρ ≠ Measure.dirac c) (ht : t ∈ interior (integrableExpSet id ρ)) :
    0 < iteratedDeriv 2 (cgf id ρ) t :=
  iteratedDeriv_two_cgf_pos (fun c h ↦ hρ c <| by simpa using (hasLaw_dirac_of_ae_eq h).map_eq) ht

/-! ### Lower bounds on probabilities by exponential tilting -/

/-- **Lower bound by exponential tilting.** Let `t` be in the interior of `integrableExpSet X μ`
for a nonzero finite measure `μ`, and let `Λ = cgf X μ`. Under the tilted measure
`μ.tilted (t * X ·)`, `X` has mean `m = Λ'(t)` and variance `Λ''(t)`. For every `c > 0`, the
measure under `μ` of the event that `X` is within `c` of `m` is at least
`exp (-(t m - Λ(t) + |t| c)) (1 - Λ''(t) / c²)`.

The tilted measure has density `exp (t X - Λ(t))` with respect to `μ`, which is at most
`exp (t m + |t| c - Λ(t))` on the event `|X - m| ≤ c`, and that event has probability at least
`1 - Λ''(t) / c²` under the tilted measure by Chebyshev's inequality. This is the change of
measure in the proof of the lower bound of Cramér's theorem, where `X` is a sum of `n`
independent copies of a random variable, `Λ` and `Λ''` grow linearly in `n`, and `c` is
proportional to `n`. -/
lemma exp_mul_le_measureReal_abs_sub_deriv_cgf_le [IsFiniteMeasure μ] [NeZero μ]
    (ht : t ∈ interior (integrableExpSet X μ)) {c : ℝ} (hc : 0 < c) :
    exp (-(t * deriv (cgf X μ) t - cgf X μ t + |t| * c)) *
        (1 - iteratedDeriv 2 (cgf X μ) t / c ^ 2) ≤
      μ.real {ω | |X ω - deriv (cgf X μ) t| ≤ c} := by
  set m := deriv (cgf X μ) t
  set A := {ω | |X ω - m| ≤ c}
  have h_int : Integrable (fun ω ↦ exp (t * X ω)) μ := interior_subset ht
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_le
      (continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_of_mem_interior_integrableExpSet ht).sub_const m))
      aemeasurable_const
  have := isProbabilityMeasure_tilted h_int
  -- Chebyshev's inequality under the tilted measure, where `X` has mean `m`.
  have h_tilt : 1 - iteratedDeriv 2 (cgf X μ) t / c ^ 2 ≤ (μ.tilted (t * X ·)).real A := by
    have h_compl : (μ.tilted (t * X ·)).real Aᶜ ≤ iteratedDeriv 2 (cgf X μ) t / c ^ 2 := by
      rw [← variance_tilted_mul ht]
      refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg c)) ?_
      refine (measure_mono fun ω hω ↦ ?_).trans
        (meas_ge_le_variance_div_sq (memLp_tilted_mul ht 2) hc)
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_le] at hω
      simp only [mem_ofPred_eq, integral_tilted_mul_self ht]
      exact hω.le
    rw [measureReal_compl₀ (hA.mono_ac (tilted_absolutelyContinuous _ _)), probReal_univ] at h_compl
    linarith
  -- On `A`, the density of the tilted measure is at most `exp (t m + |t| c - Λ(t))`.
  have h_le : (μ.tilted (t * X ·)).real A ≤ exp (t * m + |t| * c - cgf X μ t) * μ.real A := by
    have h_meas :
        μ.tilted (t * X ·) A ≤ ENNReal.ofReal (exp (t * m + |t| * c - cgf X μ t)) * μ A := by
      rw [tilted_mul_apply_cgf A h_int, ← setLIntegral_const]
      refine lintegral_mono_ae ((ae_restrict_iff'₀ hA).2 (ae_of_all _ fun ω hω ↦ ?_))
      simp only [A, mem_ofPred_eq] at hω
      have h_exp : t * X ω ≤ t * m + |t| * c := by
        calc t * X ω = t * m + t * (X ω - m) := by ring
        _ ≤ t * m + |t| * |X ω - m| := by
          rw [← abs_mul]
          exact add_le_add_right (le_abs_self _) _
        _ ≤ t * m + |t| * c := by gcongr
      gcongr
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      h_meas
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at this
  calc exp (-(t * m - cgf X μ t + |t| * c)) * (1 - iteratedDeriv 2 (cgf X μ) t / c ^ 2)
  _ ≤ exp (-(t * m - cgf X μ t + |t| * c)) * (μ.tilted (t * X ·)).real A := by gcongr
  _ ≤ exp (-(t * m - cgf X μ t + |t| * c)) * (exp (t * m + |t| * c - cgf X μ t) * μ.real A) := by
    gcongr
  _ = μ.real A := by
    rw [← mul_assoc, ← exp_add,
      (by ring : -(t * m - cgf X μ t + |t| * c) + (t * m + |t| * c - cgf X μ t) = 0), exp_zero,
      one_mul]

end ProbabilityTheory
