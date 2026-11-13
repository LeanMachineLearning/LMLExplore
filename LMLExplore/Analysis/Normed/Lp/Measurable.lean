/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import LMLExplore.Analysis.Normed.Lp.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Algebra.Algebra

import LMLExplore.Order.ConditionallyCompleteLattice.Group
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Bounded measurable functions

On a measurable space `α`, the bounded measurable real functions form a closed subalgebra
`LMLExplore.boundedMeasurable α` of `ℓ^∞(α, ℝ)`. With the sup norm `‖f‖ = ⨆ x, |f x|` it is a
Banach algebra, ordered by the pointwise order, which is closed (`OrderClosedTopology`, inherited
from `lp.instOrderClosedTopology`). This is the space on which kernels act as
operators (`ProbabilityTheory.Kernel.integralCLM`) and on which the Bellman operators of dynamic
programming on a general measurable state space are defined; its completeness is what lets
Banach's fixed point theorem apply to them.

The closedness holds more generally: in `lp (fun _ : α ↦ E) p` with `1 ≤ p`, the elements that are
measurable as functions `α → E` form a closed set, since convergence in `lp` implies pointwise
convergence and a pointwise limit of measurable functions is measurable.

## Main definitions

* `LMLExplore.boundedMeasurable α`: the subalgebra of `ℓ^∞(α, ℝ)` of measurable functions.
* `LMLExplore.boundedMeasurable.mk`: a bounded measurable function as an element of
  `boundedMeasurable α`.

## Main statements

* `lp.isClosed_setOf_measurable`: the measurable elements of `lp (fun _ : α ↦ E) p` form a closed
  set.
* `LMLExplore.isClosed_boundedMeasurable`, `LMLExplore.boundedMeasurable.instCompleteSpace`:
  `boundedMeasurable α` is closed in `ℓ^∞(α, ℝ)`, hence complete.
* `LMLExplore.boundedMeasurable.orderUnitNorm_one_eq_norm`: for the pointwise order, the
  order-unit norm of the constant `1` is the sup norm, so that maps satisfying Blackwell's
  conditions for `1` are contractions of `boundedMeasurable α` (`LMLExplore.IsBlackwell`).
* `LMLExplore.boundedMeasurable.abs_sub_apply_le_mul_of_dist_le`: a bound
  `dist f g ≤ c * dist f₀ g₀` turns a pointwise bound `|f₀ - g₀| ≤ D` into `|f - g| ≤ c * D`.
* `LMLExplore.boundedMeasurable.abs_sub_apply_le_of_isBlackwell`: Blackwell's argument, pointwise:
  such maps turn a pointwise bound `|f - g| ≤ D` into `|T f - T g| ≤ γ * D`;
  `LMLExplore.boundedMeasurable.abs_sub_apply_le_of_isBlackwell_of_coeFn_eq` states it for the
  plain functions on which `T` acts pointwise.
* `LMLExplore.boundedMeasurable.sub_apply_le_orderUnitOsc_one`,
  `LMLExplore.boundedMeasurable.orderUnitOsc_one_le_of_forall_sub_le`: the oscillation of `f` for
  `1` is the least bound on the differences `f x - f y`.
* `LMLExplore.boundedMeasurable.orderUnitOsc_one_eq_zero_iff`: the functions of oscillation zero
  are the constants.
-/

public section

open MeasureTheory Set
open scoped ENNReal lp

namespace lp

section Algebra

variable {𝕜 I : Type*} {B : I → Type*} [NormedField 𝕜] [∀ i, NormedRing (B i)]
  [∀ i, NormedAlgebra 𝕜 (B i)] [∀ i, NormOneClass (B i)]

/-- The image of `k : 𝕜` in the algebra `lp B ∞` is the constant function `algebraMap 𝕜 (B i) k`.
Constants of `LMLExplore.boundedMeasurable α` simplify to this form. -/
@[simp]
theorem infty_coeFn_algebraMap (k : 𝕜) : ⇑(algebraMap 𝕜 (lp B ∞) k) = algebraMap 𝕜 (∀ i, B i) k :=
  rfl

end Algebra

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] {p : ENNReal} [Fact (1 ≤ p)]

/-- In `lp (fun _ : α ↦ E) p` with `1 ≤ p`, the elements that are measurable as functions
`α → E` form a closed set. -/
theorem isClosed_setOf_measurable :
    IsClosed {f : lp (fun _ : α ↦ E) p | Measurable ⇑f} := by
  refine IsSeqClosed.isClosed fun f g hf hfg ↦ ?_
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun x ↦ ?_)
  exact ((lipschitzWith_one_eval (E := fun _ : α ↦ E) p x).continuous.tendsto g).comp hfg

end lp

namespace LMLExplore

variable (α : Type*) [MeasurableSpace α]

/-- The bounded measurable real functions on `α`, as a subalgebra of `ℓ^∞(α, ℝ)`. -/
noncomputable def boundedMeasurable : Subalgebra ℝ ℓ^∞(α, ℝ) where
  carrier := {f | Measurable ⇑f}
  mul_mem' hf hg := by simpa [lp.infty_coeFn_mul] using hf.mul hg
  add_mem' {f g} hf hg := by
    rw [mem_ofPred_eq, lp.coeFn_add]
    exact hf.add hg
  algebraMap_mem' c := by
    rw [mem_ofPred_eq, Algebra.algebraMap_eq_smul_one, lp.coeFn_smul, lp.infty_coeFn_one]
    exact measurable_const.const_smul c

variable {α}

@[simp]
theorem mem_boundedMeasurable_iff {f : ℓ^∞(α, ℝ)} : f ∈ boundedMeasurable α ↔ Measurable ⇑f :=
  Iff.rfl

/-- The bounded measurable functions form a closed subset of `ℓ^∞(α, ℝ)`. -/
theorem isClosed_boundedMeasurable : IsClosed (boundedMeasurable α : Set ℓ^∞(α, ℝ)) :=
  lp.isClosed_setOf_measurable

namespace boundedMeasurable

/-! The four instances below are found by instance search, but only through a search that also
tries to view `ℓ^∞(α, ℝ)` as a subring of the type `PreLp`, which carries no norm, and exceeds the
default budget. Declaring them directly keeps the normed structure of `boundedMeasurable α` cheap
to find, also inside the searches for the structure of the continuous linear maps of
`boundedMeasurable α`, such as their scalar multiplication. -/

noncomputable instance instSeminormedRing : SeminormedRing (boundedMeasurable α) :=
  Subalgebra.seminormedRing _

noncomputable instance instNormedCommRing : NormedCommRing (boundedMeasurable α) :=
  Subalgebra.normedCommRing _

noncomputable instance instNormedAlgebra : NormedAlgebra ℝ (boundedMeasurable α) :=
  Subalgebra.toNormedAlgebra _

noncomputable instance instNormedSpace : NormedSpace ℝ (boundedMeasurable α) :=
  NormedAlgebra.toNormedSpace _

/-- The bounded measurable real functions on `α` form a Banach space. -/
instance instCompleteSpace : CompleteSpace (boundedMeasurable α) :=
  isClosed_boundedMeasurable.completeSpace_coe

theorem measurable (f : boundedMeasurable α) : Measurable ⇑(f : ℓ^∞(α, ℝ)) :=
  f.2

@[ext]
theorem ext {f g : boundedMeasurable α}
    (h : ∀ x, (f : ℓ^∞(α, ℝ)) x = (g : ℓ^∞(α, ℝ)) x) : f = g :=
  Subtype.ext <| lp.ext <| funext h

@[simp]
theorem coeFn_zero : ⇑((0 : boundedMeasurable α) : ℓ^∞(α, ℝ)) = 0 :=
  rfl

@[simp]
theorem coeFn_one : ⇑((1 : boundedMeasurable α) : ℓ^∞(α, ℝ)) = 1 :=
  rfl

@[simp]
theorem coeFn_neg (f : boundedMeasurable α) :
    ⇑((-f : boundedMeasurable α) : ℓ^∞(α, ℝ)) = -⇑(f : ℓ^∞(α, ℝ)) :=
  rfl

@[simp]
theorem coeFn_add (f g : boundedMeasurable α) :
    ⇑((f + g : boundedMeasurable α) : ℓ^∞(α, ℝ)) = ⇑(f : ℓ^∞(α, ℝ)) + ⇑(g : ℓ^∞(α, ℝ)) :=
  rfl

@[simp]
theorem coeFn_sub (f g : boundedMeasurable α) :
    ⇑((f - g : boundedMeasurable α) : ℓ^∞(α, ℝ)) = ⇑(f : ℓ^∞(α, ℝ)) - ⇑(g : ℓ^∞(α, ℝ)) :=
  rfl

@[simp]
theorem coeFn_mul (f g : boundedMeasurable α) :
    ⇑((f * g : boundedMeasurable α) : ℓ^∞(α, ℝ)) = ⇑(f : ℓ^∞(α, ℝ)) * ⇑(g : ℓ^∞(α, ℝ)) :=
  rfl

@[simp]
theorem coeFn_smul (c : ℝ) (f : boundedMeasurable α) :
    ⇑((c • f : boundedMeasurable α) : ℓ^∞(α, ℝ)) = c • ⇑(f : ℓ^∞(α, ℝ)) :=
  rfl

/-- The value of `f - c • 1` at `x` is `f x - c`. Not `@[simp]`: its left-hand side is not in
simp normal form, since `coeFn_sub` rewrites it. -/
theorem sub_smul_one_apply (f : boundedMeasurable α) (c : ℝ) (x : α) :
    ((f - c • 1 : boundedMeasurable α) : ℓ^∞(α, ℝ)) x = (f : ℓ^∞(α, ℝ)) x - c := by
  simp only [coeFn_sub, coeFn_smul, coeFn_one, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]

theorem le_def {f g : boundedMeasurable α} :
    f ≤ g ↔ ∀ x, (f : ℓ^∞(α, ℝ)) x ≤ (g : ℓ^∞(α, ℝ)) x :=
  Iff.rfl

/-- Multiplication by a nonnegative scalar is monotone for the pointwise order on
`boundedMeasurable α`. -/
instance instPosSMulMono : PosSMulMono ℝ (boundedMeasurable α) where
  smul_le_smul_of_nonneg_left _ hc _ _ h := le_def.2 fun x ↦ by
    simpa only [coeFn_smul, Pi.smul_apply, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (le_def.1 h x) hc

/-- A measurable function `f : α → ℝ` with bounded absolute value, as an element of
`boundedMeasurable α`. -/
noncomputable def mk (f : α → ℝ) (hf : Measurable f) (hb : BddAbove (range fun x ↦ |f x|)) :
    boundedMeasurable α :=
  ⟨⟨f, memℓp_infty hb⟩, hf⟩

@[simp]
theorem coeFn_mk (f : α → ℝ) (hf : Measurable f) (hb : BddAbove (range fun x ↦ |f x|)) :
    ⇑(mk f hf hb : ℓ^∞(α, ℝ)) = f :=
  (rfl)

theorem norm_eq_ciSup (f : boundedMeasurable α) : ‖f‖ = ⨆ x, |(f : ℓ^∞(α, ℝ)) x| := by
  simp only [AddSubgroupClass.coe_norm, lp.norm_eq_ciSup, Real.norm_eq_abs]

theorem abs_apply_le_norm (f : boundedMeasurable α) (x : α) : |(f : ℓ^∞(α, ℝ)) x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, AddSubgroupClass.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ x

/-- A pointwise bound `|f x| ≤ C` with `0 ≤ C` bounds the sup norm of `f`. -/
theorem norm_le_of_forall_le {f : boundedMeasurable α} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, |(f : ℓ^∞(α, ℝ)) x| ≤ C) : ‖f‖ ≤ C := by
  rw [AddSubgroupClass.coe_norm]
  exact lp.norm_le_of_forall_le hC fun x ↦ (Real.norm_eq_abs _).trans_le (hf x)

/-- The values of two bounded measurable functions at a point differ by at most their distance. -/
theorem abs_sub_apply_le_dist (f g : boundedMeasurable α) (x : α) :
    |(f : ℓ^∞(α, ℝ)) x - (g : ℓ^∞(α, ℝ)) x| ≤ dist f g := by
  rw [dist_eq_norm, ← Pi.sub_apply, ← coeFn_sub]
  exact abs_apply_le_norm _ x

/-- A pointwise bound `|f x - g x| ≤ C` with `0 ≤ C` bounds the distance of `f` and `g`. -/
theorem dist_le_of_forall_abs_sub_le {f g : boundedMeasurable α} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, |(f : ℓ^∞(α, ℝ)) x - (g : ℓ^∞(α, ℝ)) x| ≤ C) : dist f g ≤ C := by
  rw [dist_eq_norm]
  exact norm_le_of_forall_le hC fun x ↦ by rw [coeFn_sub, Pi.sub_apply]; exact h x

/-- A bound `dist f g ≤ c * dist f₀ g₀` with `0 ≤ c` turns a pointwise bound `|f₀ x - g₀ x| ≤ D`
into the pointwise bound `|f x - g x| ≤ c * D`. This is how the contraction and convergence rates
of operators on `boundedMeasurable α` are read pointwise. -/
theorem abs_sub_apply_le_mul_of_dist_le {f g f₀ g₀ : boundedMeasurable α} {c D : ℝ} (hc : 0 ≤ c)
    (h : dist f g ≤ c * dist f₀ g₀) (hD : ∀ x, |(f₀ : ℓ^∞(α, ℝ)) x - (g₀ : ℓ^∞(α, ℝ)) x| ≤ D)
    (x : α) : |(f : ℓ^∞(α, ℝ)) x - (g : ℓ^∞(α, ℝ)) x| ≤ c * D :=
  (abs_sub_apply_le_dist f g x).trans <| h.trans <|
    mul_le_mul_of_nonneg_left (dist_le_of_forall_abs_sub_le ((abs_nonneg _).trans (hD x)) hD) hc

/-- A bounded measurable function lies in the order interval `[-c • 1, c • 1]` if and only if it
is bounded by `c` in absolute value. -/
theorem mem_Icc_neg_smul_one_iff {f : boundedMeasurable α} {c : ℝ} :
    f ∈ Icc (-(c • 1)) (c • 1) ↔ ∀ x, |(f : ℓ^∞(α, ℝ)) x| ≤ c := by
  simp only [mem_Icc, le_def, coeFn_neg, coeFn_smul, coeFn_one, Pi.neg_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one, ← forall_and, abs_le]

/-- For the pointwise order, the order-unit norm of the constant function `1` on bounded measurable
functions is the sup norm. -/
@[simp]
theorem orderUnitNorm_one_eq_norm (f : boundedMeasurable α) : orderUnitNorm 1 f = ‖f‖ := by
  have hS : {c : ℝ | 0 ≤ c ∧ f ∈ Icc (-(c • 1)) (c • 1)} = Ici ‖f‖ := by
    ext c
    simp only [mem_ofPred_eq, mem_Ici, mem_Icc_neg_smul_one_iff]
    exact ⟨fun ⟨hc, h⟩ ↦ norm_le_of_forall_le hc h,
      fun h ↦ ⟨(norm_nonneg f).trans h, fun x ↦ (abs_apply_le_norm f x).trans h⟩⟩
  rw [orderUnitNorm_def, hS, csInf_Ici]

/-- The constant function `1` is an order unit of the bounded measurable functions. -/
theorem isOrderUnit_one : IsOrderUnit (1 : boundedMeasurable α) :=
  isOrderUnit_of_forall_orderUnitNorm_eq_norm orderUnitNorm_one_eq_norm

/-- **Blackwell's argument, pointwise**: if `T` satisfies Blackwell's conditions for the constant
function `1` with modulus `γ`, then `|f x - g x| ≤ D` at every point `x` gives
`|T f x - T g x| ≤ γ * D` at every point `x`. -/
theorem abs_sub_apply_le_of_isBlackwell {T : boundedMeasurable α → boundedMeasurable α}
    {γ : NNReal} (hT : IsBlackwell 1 γ T) {f g : boundedMeasurable α} {D : ℝ}
    (h : ∀ x, |(f : ℓ^∞(α, ℝ)) x - (g : ℓ^∞(α, ℝ)) x| ≤ D) (x : α) :
    |(T f : ℓ^∞(α, ℝ)) x - (T g : ℓ^∞(α, ℝ)) x| ≤ γ * D :=
  abs_sub_apply_le_mul_of_dist_le γ.coe_nonneg
    ((hT.lipschitzWith orderUnitNorm_one_eq_norm).dist_le_mul f g) h x

/-- **Blackwell's argument, for plain functions**: if `T` satisfies Blackwell's conditions for the
constant function `1` with modulus `γ` and acts on bounded measurable functions as `t : (α → ℝ) →
α → ℝ`, then for measurable bounded `u` and `v`, `|u x - v x| ≤ D` at every point `x` gives
`|t u x - t v x| ≤ γ * D` at every point `x`. -/
theorem abs_sub_apply_le_of_isBlackwell_of_coeFn_eq {T : boundedMeasurable α → boundedMeasurable α}
    {t : (α → ℝ) → α → ℝ} {γ : NNReal} (hT : IsBlackwell 1 γ T)
    (ht : ∀ f, ⇑(T f : ℓ^∞(α, ℝ)) = t ⇑(f : ℓ^∞(α, ℝ))) {u v : α → ℝ} {B B' D : ℝ}
    (hu : Measurable u) (huB : ∀ x, |u x| ≤ B) (hv : Measurable v) (hvB : ∀ x, |v x| ≤ B')
    (h : ∀ x, |u x - v x| ≤ D) (x : α) :
    |t u x - t v x| ≤ γ * D := by
  simpa only [ht, coeFn_mk] using abs_sub_apply_le_of_isBlackwell hT
    (f := mk u hu (bddAbove_def.2 ⟨B, forall_mem_range.2 huB⟩))
    (g := mk v hv (bddAbove_def.2 ⟨B', forall_mem_range.2 hvB⟩))
    (by simpa only [coeFn_mk] using h) x

/-- The values of a bounded measurable function differ by at most its oscillation for the
constant function `1`. -/
theorem sub_apply_le_orderUnitOsc_one (f : boundedMeasurable α) (x y : α) :
    (f : ℓ^∞(α, ℝ)) x - (f : ℓ^∞(α, ℝ)) y ≤ orderUnitOsc 1 f := by
  refine le_orderUnitOsc isOrderUnit_one fun d _ a hf ↦ ?_
  have hy := le_def.1 hf.1 y
  have hx := le_def.1 hf.2 x
  simp only [coeFn_smul, coeFn_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hx hy
  linarith

/-- If the values of a bounded measurable function differ by at most `c ≥ 0`, its oscillation for
the constant function `1` is at most `c`. -/
theorem orderUnitOsc_one_le_of_forall_sub_le {f : boundedMeasurable α} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, (f : ℓ^∞(α, ℝ)) x - (f : ℓ^∞(α, ℝ)) y ≤ c) : orderUnitOsc 1 f ≤ c := by
  -- `f` takes values in `[a, a + c]` with `a` its infimum
  refine orderUnitOsc_le (a := ⨅ x, (f : ℓ^∞(α, ℝ)) x) hc
    ⟨le_def.2 fun x ↦ ?_, le_def.2 fun x ↦ ?_⟩ <;>
    simp only [coeFn_smul, coeFn_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  · exact (mem_Icc_ciInf_of_forall_sub_le h x).1
  · exact (mem_Icc_ciInf_of_forall_sub_le h x).2

/-- A bounded measurable function has oscillation zero for the constant function `1` if and only
if it is constant. -/
theorem orderUnitOsc_one_eq_zero_iff {f : boundedMeasurable α} :
    orderUnitOsc 1 f = 0 ↔ ∃ c : ℝ, f = c • 1 := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
    · exact ⟨0, ext fun x ↦ isEmptyElim x⟩
    refine ⟨(f : ℓ^∞(α, ℝ)) x₀, ext fun x ↦ ?_⟩
    have h₁ := sub_apply_le_orderUnitOsc_one f x x₀
    have h₂ := sub_apply_le_orderUnitOsc_one f x₀ x
    simp only [coeFn_smul, coeFn_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linarith
  · rintro ⟨c, rfl⟩
    exact (orderUnitOsc_one_le_of_forall_sub_le le_rfl fun x y ↦ by simp).antisymm
      (orderUnitOsc_nonneg _ _)

end boundedMeasurable

end LMLExplore
