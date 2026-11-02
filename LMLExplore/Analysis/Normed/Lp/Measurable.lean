/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Normed.Lp.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Algebra.Algebra

/-!
# Bounded measurable functions

On a measurable space `α`, the bounded measurable real functions form a closed subalgebra
`LMLExplore.boundedMeasurable α` of `ℓ^∞(α, ℝ)`. With the sup norm `‖f‖ = ⨆ x, |f x|` it is a
Banach algebra, ordered by the pointwise order. This is the space on which kernels act as
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

/-! The three instances below are found by instance search, but only through a search that also
tries to view `ℓ^∞(α, ℝ)` as a subring of the type `PreLp`, which carries no norm, and exceeds the
default budget. Declaring them directly keeps the normed structure of `boundedMeasurable α` cheap
to find. -/

noncomputable instance instSeminormedRing : SeminormedRing (boundedMeasurable α) :=
  Subalgebra.seminormedRing _

noncomputable instance instNormedCommRing : NormedCommRing (boundedMeasurable α) :=
  Subalgebra.normedCommRing _

noncomputable instance instNormedAlgebra : NormedAlgebra ℝ (boundedMeasurable α) :=
  Subalgebra.toNormedAlgebra _

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

end boundedMeasurable

end LMLExplore
