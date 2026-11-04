/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
public import LMLExplore.Probability.Kernel.Composition.Comp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.WithDensity

/-!
# The resolvent of a kernel

For a kernel `κ : Kernel α α` and a discount factor `γ : ℝ≥0`, the resolvent of `κ` is the kernel
`R_γ(κ) = ∑ n, γ ^ n κ ^ n`: the measure `resolvent γ κ x` gives to a set `s` the expected
discounted number of visits to `s` of the Markov chain with kernel `κ` started at `x`,
`∑' n, γ ^ n * (κ ^ n) x s`. Acting on functions, it maps `f` to
`x ↦ ∫ y, f y ∂(resolvent γ κ x) = ∑' n, γ ^ n * ∫ y, f y ∂((κ ^ n) x)`, the expected discounted sum
of the values of `f` along the chain. The resolvent of an s-finite kernel is s-finite, and for a
Markov kernel and `γ < 1`, it is a finite kernel of mass `(1 - γ)⁻¹`.

For every kernel and every `γ`, the resolvent satisfies, as measures,
`resolvent γ κ x = δ_x + γ • (resolvent γ κ ∘ₖ κ) x = δ_x + γ • (κ ∘ₖ resolvent γ κ) x`, which
are the operator identities `R_γ = 1 + γ κ R_γ = 1 + γ R_γ κ`. For a Markov kernel and `γ < 1`,
the resolvent is therefore the inverse of `1 - γ κ`, read as an operator on bounded measurable
functions. Consequently:
* for a Markov kernel, `γ < 1` and a bounded measurable `f`, the function `u = R_γ f` is the
  unique bounded measurable solution of the equation `u = f + γ κ u`;
* for a measure `μ`, the measure `ν = μ.bind R_γ` (written `resolvent γ κ ∘ₘ μ`) satisfies the
  flow equation `ν = μ + γ • ν.bind κ` for every kernel and every `γ`; for a Markov kernel and
  `γ < 1`, it is the unique finite measure satisfying it.

Uniqueness also compares resolvents: for every bounded measurable `y`, `R_γ f - y` is the resolvent
`R_γ (f + γ κ y - y)` of the residual of `y` in the equation `u = f + γ κ u` (the
performance-difference identity), and for a second Markov kernel `κ'`, taking `y = R_γ(κ') f` gives
the simulation identity `R_γ(κ) f - R_γ(κ') f = γ R_γ(κ) ((κ - κ') R_γ(κ') f)`. Since the
resolvent is a positive operator, the performance-difference identity also compares `R_γ f` with
sub- and supersolutions of `u = f + γ κ u`.

In a Markov decision process, the value of a stationary policy is the resolvent of the state
kernel of the policy applied to its reward, and the discounted occupancy measure of a stationary
policy is, up to the factor `1 - γ`, the image of the initial state-action law by the resolvent of
the state-action kernel. The two characterizations above are the evaluation equation and the flow
equation of these objects.

## Main definitions

* `ProbabilityTheory.Kernel.resolvent γ κ`: the resolvent kernel `∑ n, γ ^ n κ ^ n`.

## Main statements

* `ProbabilityTheory.Kernel.lintegral_resolvent`, `ProbabilityTheory.Kernel.integral_resolvent`:
  the integral against `resolvent γ κ x` is the discounted series of the integrals against the
  powers of `κ`.
* `ProbabilityTheory.Kernel.resolvent_apply_univ`: for a Markov kernel, the mass of the resolvent
  is `(1 - γ)⁻¹`; `ProbabilityTheory.Kernel.isFiniteKernel_resolvent`: it is a finite kernel for
  `γ < 1`. The resolvent of an s-finite kernel is s-finite (an instance).
* `ProbabilityTheory.Kernel.dirac_add_resolvent_comp_apply`,
  `ProbabilityTheory.Kernel.dirac_add_comp_resolvent_apply`: the resolvent identities
  `R_γ = 1 + γ κ R_γ = 1 + γ R_γ κ`.
* `ProbabilityTheory.Kernel.integral_resolvent_eq_add`,
  `ProbabilityTheory.Kernel.eq_integral_resolvent_of_eq_add`: for a Markov kernel and `γ < 1`,
  `R_γ f` is the unique bounded measurable solution of `u = f + γ κ u`.
* `ProbabilityTheory.Kernel.abs_integral_resolvent_le`,
  `ProbabilityTheory.Kernel.le_integral_resolvent`: for a Markov kernel and `γ < 1`,
  `|R_γ f| ≤ sup |f| / (1 - γ)`, and `f ≤ R_γ f` for `f ≥ 0`.
* `ProbabilityTheory.Kernel.integral_resolvent_sub_eq_integral_resolvent`: the
  performance-difference identity `R_γ f - y = R_γ (f + γ κ y - y)`.
* `ProbabilityTheory.Kernel.integral_resolvent_le_of_add_le`,
  `ProbabilityTheory.Kernel.le_integral_resolvent_of_le_add`: comparison with sub- and
  supersolutions, `f + γ κ u ≤ u → R_γ f ≤ u` and `u ≤ f + γ κ u → u ≤ R_γ f`.
* `ProbabilityTheory.Kernel.integral_resolvent_sub_integral_resolvent`: the simulation identity
  `R_γ(κ) f - R_γ(κ') f = γ R_γ(κ) ((κ - κ') R_γ(κ') f)`.
* `MeasureTheory.Measure.resolvent_comp_eq_add`: for every kernel and every `γ`,
  `resolvent γ κ ∘ₘ μ` solves the flow equation `ν = μ + γ • (κ ∘ₘ ν)`;
  `MeasureTheory.Measure.eq_resolvent_comp_of_eq_add`: for a Markov kernel and `γ < 1`, it is the
  unique finite solution. `MeasureTheory.Measure.eq_sum_range_add_of_eq_add` unfolds the flow
  equation `n` times, for every kernel.

## References

* D. Revuz, *Markov chains*, North-Holland, 2nd edition, 1984, Chapter 2
* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.1
* [A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, 2021][AKLM21], Lemma 3.2
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 2.2
-/

public section

open MeasureTheory Set Filter Topology LMLExplore
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ : ℝ≥0} {κ : Kernel α α}

/-! ### Definition -/

/-- The resolvent `R_γ(κ) = ∑ n, γ ^ n κ ^ n` of a kernel `κ : Kernel α α`: the measure
`resolvent γ κ x` gives to a measurable set `s` the mass `∑' n, γ ^ n * (κ ^ n) x s`, the expected
discounted number of visits to `s` of the Markov chain with kernel `κ` started at `x`. -/
noncomputable def resolvent (γ : ℝ≥0) (κ : Kernel α α) : Kernel α α where
  toFun x := Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • (κ ^ n) x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [Measure.sum_apply _ hs, smul_apply, smul_eq_mul]
    exact Measurable.tsum fun n ↦ ((κ ^ n).measurable_coe hs).const_mul _

lemma resolvent_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    resolvent γ κ x = Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • (κ ^ n) x :=
  (rfl)

lemma resolvent_apply' (γ : ℝ≥0) (κ : Kernel α α) (x : α) {s : Set α} (hs : MeasurableSet s) :
    resolvent γ κ x s = ∑' n, (γ : ℝ≥0∞) ^ n * (κ ^ n) x s := by
  simp [resolvent_apply, Measure.sum_apply _ hs]

/-- The resolvent of an s-finite kernel is an s-finite kernel. -/
instance [IsSFiniteKernel κ] : IsSFiniteKernel (resolvent γ κ) := by
  have h : resolvent γ κ =
      Kernel.sum fun n ↦ withDensity (κ ^ n) fun _ _ ↦ ((γ ^ n : ℝ≥0) : ℝ≥0∞) := by
    ext x : 1
    rw [resolvent_apply, Kernel.sum_apply]
    congr with n : 1
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_const, ENNReal.coe_pow]
  rw [h]
  infer_instance

/-- The lower Lebesgue integral against the resolvent is the discounted series of the integrals
against the powers of the kernel. -/
lemma lintegral_resolvent (γ : ℝ≥0) (κ : Kernel α α) (x : α) (f : α → ℝ≥0∞) :
    ∫⁻ y, f y ∂(resolvent γ κ x) = ∑' n, (γ : ℝ≥0∞) ^ n * ∫⁻ y, f y ∂((κ ^ n) x) := by
  simp [resolvent_apply, lintegral_sum_measure, lintegral_smul_measure]

/-- The integral of a function `f` integrable against the resolvent is the discounted series
`∑' n, γ ^ n • ∫ f d(κ ^ n x)`. -/
theorem integral_resolvent {f : α → E} {x : α} (hf : Integrable f (resolvent γ κ x)) :
    ∫ y, f y ∂(resolvent γ κ x) = ∑' n, ((γ : ℝ) ^ n) • ∫ y, f y ∂((κ ^ n) x) := by
  rw [resolvent_apply] at hf ⊢
  simp [integral_sum_measure hf, integral_smul_measure]

/-- The integral of a measurable function against the resolvent is a measurable function of the
starting point. -/
theorem measurable_integral_resolvent {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x ↦ ∫ y, f y ∂(resolvent γ κ x) :=
  (hf.stronglyMeasurable.integral_kernel (κ := resolvent γ κ)).measurable

/-- For `γ = 0`, the resolvent is the identity kernel. -/
@[simp]
lemma resolvent_zero (κ : Kernel α α) : resolvent 0 κ = Kernel.id := by
  ext x s hs
  rw [resolvent_apply' _ _ _ hs, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp [one_eq_id]

/-- The measure `resolvent γ κ x` dominates the Dirac mass at `x`. -/
lemma dirac_le_resolvent (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x ≤ resolvent γ κ x := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [resolvent_apply' _ _ _ hs]
  refine le_trans ?_ (le_tsum _ 0)
  simp [one_eq_id, Kernel.id_apply]

/-! ### The resolvent identities -/

/-- The resolvent identity `R_γ = 1 + γ κ R_γ`, as measures: the resolvent from `x` is the Dirac
mass at `x` plus `γ` times the resolvent from the next state. -/
theorem dirac_add_resolvent_comp_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x + (γ : ℝ≥0∞) • (resolvent γ κ ∘ₖ κ) x = resolvent γ κ x := by
  ext s hs
  have h (n : ℕ) : Measurable fun y ↦ (γ : ℝ≥0∞) ^ n * (κ ^ n) y s :=
    ((κ ^ n).measurable_coe hs).const_mul _
  rw [add_apply, smul_apply, smul_eq_mul, comp_apply' _ _ _ hs,
    resolvent_apply' _ _ _ hs, tsum_eq_zero_add' CompleteLattice.summable]
  simp_rw [resolvent_apply' _ _ _ hs]
  rw [lintegral_tsum fun n ↦ (h n).aemeasurable, ← ENNReal.tsum_mul_left]
  congr 1
  · simp [one_eq_id, Kernel.id_apply]
  · refine tsum_congr fun n ↦ ?_
    rw [lintegral_const_mul _ ((κ ^ n).measurable_coe hs), pow_succ, pow_succ, mul_eq_comp,
      comp_apply' _ _ _ hs]
    ring

/-- The resolvent identity `R_γ = 1 + γ R_γ κ`, as measures: the resolvent from `x` is the Dirac
mass at `x` plus `γ` times the image of the resolvent from `x` by one step of `κ`. -/
theorem dirac_add_comp_resolvent_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x + (γ : ℝ≥0∞) • (κ ∘ₖ resolvent γ κ) x = resolvent γ κ x := by
  ext s hs
  rw [add_apply, smul_apply, smul_eq_mul, comp_apply' _ _ _ hs,
    lintegral_resolvent, resolvent_apply' _ _ _ hs, ← ENNReal.tsum_mul_left]
  conv_rhs => rw [tsum_eq_zero_add' CompleteLattice.summable]
  congr 1
  · simp [one_eq_id, Kernel.id_apply]
  · refine tsum_congr fun n ↦ ?_
    rw [pow_succ_apply_eq_lintegral _ _ _ hs, pow_succ]
    ring

/-! ### Mass and finiteness -/

section Markov

variable [IsMarkovKernel κ]

variable (γ κ) in
/-- The resolvent of a Markov kernel has mass `(1 - γ)⁻¹`. -/
@[simp]
lemma resolvent_apply_univ (x : α) : resolvent γ κ x univ = (1 - (γ : ℝ≥0∞))⁻¹ := by
  simp [resolvent_apply' _ _ _ MeasurableSet.univ, ENNReal.tsum_geometric]

/-- For `γ < 1`, the resolvent of a Markov kernel is a finite kernel. -/
lemma isFiniteKernel_resolvent (hγ : γ < 1) : IsFiniteKernel (resolvent γ κ) := by
  refine ⟨⟨(1 - (γ : ℝ≥0∞))⁻¹, ?_, fun x ↦ (resolvent_apply_univ γ κ x).le⟩⟩
  rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
  exact_mod_cast hγ

/-- For `γ < 1`, the resolvent of a Markov kernel has real mass `(1 - γ)⁻¹`. -/
lemma measureReal_resolvent_univ (hγ : γ < 1) (x : α) :
    (resolvent γ κ x).real univ = (1 - (γ : ℝ))⁻¹ := by
  simp [measureReal_def, ENNReal.toReal_inv, ENNReal.toReal_sub_of_le, hγ.le]

/-! ### The resolvent acting on bounded functions -/

/-- For `γ < 1`, a function bounded by `B` has an integral against the resolvent of a Markov
kernel bounded by `B / (1 - γ)`: `|R_γ f| ≤ sup |f| / (1 - γ)`. -/
theorem abs_integral_resolvent_le (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hfB : ∀ y, |f y| ≤ B)
    (x : α) : |∫ y, f y ∂(resolvent γ κ x)| ≤ B / (1 - γ) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  rw [← Real.norm_eq_abs, div_eq_mul_inv, ← measureReal_resolvent_univ (κ := κ) hγ x]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (hfB y)

/-- The resolvent equation `R_γ f = f + γ κ R_γ f`: for `γ < 1` and a bounded measurable `f`, the
function `u = R_γ f` solves `u = f + γ κ u`. -/
theorem integral_resolvent_eq_add (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (x : α) :
    ∫ y, f y ∂(resolvent γ κ x) =
      f x + γ * ∫ y, (∫ z, f z ∂(resolvent γ κ y)) ∂(κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have hint : Integrable f (resolvent γ κ x) := integrable_of_abs_le hf hfB _
  rw [← dirac_add_resolvent_comp_apply] at hint
  conv_lhs => rw [← dirac_add_resolvent_comp_apply]
  rw [integral_add_measure (hint.mono_measure (Measure.le_add_right le_rfl))
    (hint.mono_measure (Measure.le_add_left le_rfl)), integral_dirac' _ _ hf.stronglyMeasurable,
    integral_smul_measure, integral_comp (integrable_of_abs_le hf hfB _)]
  simp

/-- **Uniqueness of the solution of the resolvent equation**: for `γ < 1`, if a bounded measurable
`u` solves `u = f + γ κ u` for a bounded measurable `f`, then `u = R_γ f`. -/
theorem eq_integral_resolvent_of_eq_add (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (hu : Measurable u) (huB : ∀ y, |u y| ≤ B')
    (h : ∀ x, u x = f x + γ * ∫ y, u y ∂(κ x)) :
    u = fun x ↦ ∫ y, f y ∂(resolvent γ κ x) := by
  have hR := measurable_integral_resolvent (γ := γ) (κ := κ) hf
  have hRB := abs_integral_resolvent_le (κ := κ) hγ hfB
  refine eq_of_forall_abs_sub_le_mul (NNReal.coe_lt_one.2 hγ)
    (fun x ↦ (abs_sub _ _).trans (add_le_add (huB x) (hRB x))) fun E hE x ↦ ?_
  rw [h x, integral_resolvent_eq_add hγ hf hfB x, add_sub_add_left_eq_sub, ← mul_sub,
    ← integral_sub (integrable_of_abs_le hu huB _) (integrable_of_abs_le hR hRB _), abs_mul,
    NNReal.abs_eq]
  gcongr
  exact abs_integral_le_of_abs_le hE

/-- The resolvent of a Markov kernel dominates the identity on nonnegative functions: for `γ < 1`
and a nonnegative bounded measurable `f`, `f ≤ R_γ f`. -/
theorem le_integral_resolvent (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (hf₀ : 0 ≤ f) (x : α) : f x ≤ ∫ y, f y ∂(resolvent γ κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  rw [← integral_dirac' f x hf.stronglyMeasurable]
  exact integral_mono_measure (dirac_le_resolvent γ κ x) (.of_forall hf₀)
    (integrable_of_abs_le hf hfB _)

/-! ### Resolvent identities for differences -/

/-- **The performance-difference identity** `R_γ f - y = R_γ (f + γ κ y - y)`: for `γ < 1` and
bounded measurable `f` and `y`, the function `R_γ f` differs from `y` by the resolvent of the
residual of `y` in the equation `u = f + γ κ u`. -/
theorem integral_resolvent_sub_eq_integral_resolvent (hγ : γ < 1) {f y : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hy : Measurable y) (hyB : ∀ z, |y z| ≤ B')
    (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) - y x =
      ∫ z, (f z + γ * ∫ w, y w ∂(κ z) - y z) ∂(resolvent γ κ x) := by
  have hR := measurable_integral_resolvent (γ := γ) (κ := κ) hf
  have hRB := abs_integral_resolvent_le (κ := κ) hγ hfB
  have hκy : Measurable fun z ↦ ∫ w, y w ∂(κ z) :=
    (hy.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hgB (z : α) : |f z + γ * ∫ w, y w ∂(κ z) - y z| ≤ B + γ * B' + B' := by
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hfB z) ?_))
      (hyB z))
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_of_abs_le hyB) γ.coe_nonneg
  -- `u = R_γ f - y` solves `u = (f + γ κ y - y) + γ κ u`, hence is the resolvent of that residual.
  refine congrFun (eq_integral_resolvent_of_eq_add hγ ((hf.add (hκy.const_mul _)).sub hy) hgB
    (u := fun x ↦ ∫ z, f z ∂(resolvent γ κ x) - y x) (hR.sub hy)
    (fun z ↦ (abs_sub _ _).trans (add_le_add (hRB z) (hyB z))) fun x ↦ ?_) x
  rw [integral_sub (integrable_of_abs_le hR hRB _) (integrable_of_abs_le hy hyB _),
    integral_resolvent_eq_add hγ hf hfB x, Pi.sub_apply, Pi.add_apply]
  ring

/-- **Comparison with supersolutions of the resolvent equation**: for `γ < 1` and bounded
measurable `f`, a bounded measurable `u` with `f + γ κ u ≤ u` dominates `R_γ f`. -/
theorem integral_resolvent_le_of_add_le (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hu : Measurable u) (huB : ∀ z, |u z| ≤ B')
    (h : ∀ z, f z + γ * ∫ w, u w ∂(κ z) ≤ u z) (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) ≤ u x := by
  rw [← sub_nonpos, integral_resolvent_sub_eq_integral_resolvent hγ hf hfB hu huB]
  exact integral_nonpos fun z ↦ sub_nonpos.2 (h z)

/-- **Comparison with subsolutions of the resolvent equation**: for `γ < 1` and bounded measurable
`f`, a bounded measurable `u` with `u ≤ f + γ κ u` is dominated by `R_γ f`. -/
theorem le_integral_resolvent_of_le_add (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hu : Measurable u) (huB : ∀ z, |u z| ≤ B')
    (h : ∀ z, u z ≤ f z + γ * ∫ w, u w ∂(κ z)) (x : α) :
    u x ≤ ∫ z, f z ∂(resolvent γ κ x) := by
  rw [← sub_nonneg, integral_resolvent_sub_eq_integral_resolvent hγ hf hfB hu huB]
  exact integral_nonneg fun z ↦ sub_nonneg.2 (h z)

/-- **The simulation identity** `R_γ(κ) f - R_γ(κ') f = γ R_γ(κ) ((κ - κ') R_γ(κ') f)`: for Markov
kernels `κ` and `κ'`, `γ < 1` and a bounded measurable `f`, the discounted sums of `f` along the
chains with kernels `κ` and `κ'` differ by the resolvent of `κ` applied to the one-step difference
of the kernels, acting on the discounted sum of `f` along the chain with kernel `κ'`. -/
theorem integral_resolvent_sub_integral_resolvent (κ' : Kernel α α) [IsMarkovKernel κ']
    (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) - ∫ z, f z ∂(resolvent γ κ' x) =
      γ * ∫ z, (∫ w, (∫ y, f y ∂(resolvent γ κ' w)) ∂(κ z) -
        ∫ w, (∫ y, f y ∂(resolvent γ κ' w)) ∂(κ' z)) ∂(resolvent γ κ x) := by
  rw [integral_resolvent_sub_eq_integral_resolvent hγ hf hfB
    (measurable_integral_resolvent (κ := κ') hf) (abs_integral_resolvent_le (κ := κ') hγ hfB),
    ← integral_const_mul]
  congr with z
  rw [integral_resolvent_eq_add (κ := κ') hγ hf hfB z]
  ring

end Markov

end ProbabilityTheory.Kernel

/-! ### The flow equation -/

namespace MeasureTheory.Measure

open ProbabilityTheory Kernel

variable {α : Type*} {mα : MeasurableSpace α} {γ : ℝ≥0} {κ : Kernel α α} {μ ν : Measure α}

/-- The image of a measure by the resolvent is the discounted sum of its images by the powers of
the kernel. -/
theorem resolvent_comp (γ : ℝ≥0) (κ : Kernel α α) (μ : Measure α) :
    resolvent γ κ ∘ₘ μ = Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • ((κ ^ n : Kernel α α) ∘ₘ μ) := by
  ext s hs
  rw [bind_apply hs (resolvent γ κ).aemeasurable, Measure.sum_apply _ hs]
  simp_rw [resolvent_apply' _ _ _ hs, smul_apply, smul_eq_mul, bind_apply hs (κ ^ _).aemeasurable]
  rw [lintegral_tsum fun n ↦ (((κ ^ n).measurable_coe hs).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ ((κ ^ _).measurable_coe hs)]

/-- **The flow equation**: the image `ν = resolvent γ κ ∘ₘ μ` of a measure `μ` by the resolvent
satisfies `ν = μ + γ • (κ ∘ₘ ν)`. -/
theorem resolvent_comp_eq_add (γ : ℝ≥0) (κ : Kernel α α) (μ : Measure α) :
    resolvent γ κ ∘ₘ μ = μ + (γ : ℝ≥0∞) • (κ ∘ₘ (resolvent γ κ ∘ₘ μ)) := by
  ext s hs
  rw [comp_assoc, add_apply, smul_apply, smul_eq_mul, bind_apply hs (resolvent γ κ).aemeasurable,
    bind_apply hs (κ ∘ₖ resolvent γ κ).aemeasurable]
  simp_rw [← dirac_add_comp_resolvent_apply γ κ, add_apply, smul_apply, smul_eq_mul]
  rw [lintegral_add_right _ (((κ ∘ₖ resolvent γ κ).measurable_coe hs).const_mul _),
    lintegral_const_mul _ ((κ ∘ₖ resolvent γ κ).measurable_coe hs)]
  simp_rw [dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]

/-- Unfolding the flow equation `n` times: if `ν = μ + c • (κ ∘ₘ ν)`, then
`ν = ∑ k < n, c ^ k • (κ ^ k ∘ₘ μ) + c ^ n • (κ ^ n ∘ₘ ν)`. -/
theorem eq_sum_range_add_of_eq_add {c : ℝ≥0∞} (h : ν = μ + c • (κ ∘ₘ ν)) (n : ℕ) :
    ν = (∑ k ∈ Finset.range n, c ^ k • ((κ ^ k : Kernel α α) ∘ₘ μ)) +
      c ^ n • ((κ ^ n : Kernel α α) ∘ₘ ν) := by
  induction n with
  | zero => simp [one_eq_id, id_comp]
  | succ n ih =>
    conv_lhs => rw [ih, h]
    simp [comp_add, comp_smul, comp_assoc, ← mul_eq_comp, ← pow_succ, smul_smul,
      Finset.sum_range_succ, add_assoc]

/-- **Uniqueness of the solution of the flow equation**: for a Markov kernel `κ` and `γ < 1`, a
finite measure `ν` with `ν = μ + γ • (κ ∘ₘ ν)` is the image `resolvent γ κ ∘ₘ μ` of `μ` by the
resolvent. -/
theorem eq_resolvent_comp_of_eq_add [IsMarkovKernel κ] (hγ : γ < 1) [IsFiniteMeasure ν]
    (h : ν = μ + (γ : ℝ≥0∞) • (κ ∘ₘ ν)) : ν = resolvent γ κ ∘ₘ μ := by
  ext s hs
  rw [resolvent_comp, Measure.sum_apply _ hs]
  simp_rw [smul_apply, smul_eq_mul]
  -- The remainder `γ ^ n * (κ ^ n ∘ₘ ν) s` is at most `γ ^ n * ν univ`, which tends to `0`.
  have hrem : Tendsto (fun n ↦ (γ : ℝ≥0∞) ^ n * ((κ ^ n : Kernel α α) ∘ₘ ν) s) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n ↦ (γ : ℝ≥0∞) ^ n * ν univ) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.coe_lt_one_iff.2 hγ))
        (Or.inr (measure_ne_top ν univ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
      fun n ↦ ?_
    gcongr (γ : ℝ≥0∞) ^ n * ?_
    exact (measure_mono (subset_univ s)).trans_eq (comp_apply_univ (κ := κ ^ n))
  refine tendsto_nhds_unique (f := fun _ : ℕ ↦ ν s) (l := atTop) tendsto_const_nhds ?_
  convert (ENNReal.tendsto_nat_tsum fun k ↦
    (γ : ℝ≥0∞) ^ k * ((κ ^ k : Kernel α α) ∘ₘ μ) s).add hrem using 1
  · ext n
    conv_lhs => rw [eq_sum_range_add_of_eq_add h n]
    simp
  · rw [add_zero]

end MeasureTheory.Measure
