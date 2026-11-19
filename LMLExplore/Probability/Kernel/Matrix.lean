/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import TauCeti.Probability.Kernel.ClosedClass.Basic
public import TauCeti.Probability.Kernel.Matrix.Basic

/-!
# The real transition matrix of a kernel on a finite space

A finite kernel `κ` on a finite space `α` with measurable singletons has the transition matrix
`κ.toMatrix : Matrix α α ℝ≥0` of Tau Ceti, with entries `κ a {b}`. Linear algebra over `ℝ`
(limiting and deviation matrices, resolvents `(1 - γ P)⁻¹`) works with its real image
`κ.toMatrix.map (↑)`. This file relates that real matrix to the kernel: its entries are the real
masses `(κ a).real {b}`, its `mulVec` is integration against `κ`, the matrix of `κ ^ n` is its
`n`-th power, and it is row-stochastic for a Markov kernel.

It also proves the *maximum principle* on closed classes: a function `g` that is harmonic for a
Markov kernel, `P g = g`, is constant on every closed communicating class. In particular a
kernel under which every state reaches every other state (an irreducible kernel, by Tau Ceti's
`ProbabilityTheory.Kernel.isIrreducible_count_iff_forall_reaches`) has only constant harmonic
functions. These facts describe the fixed vectors of `P`, such as the long-run averages
`P* r` of a finite Markov chain.

## Main statements

* `ProbabilityTheory.Kernel.toMatrix_map_coe_mulVec`: `(P f) a = ∫ x, f x ∂(κ a)`.
* `ProbabilityTheory.Kernel.toMatrix_map_coe_pow`: the real matrix of `κ ^ n` is `P ^ n`.
* `ProbabilityTheory.Kernel.toMatrix_map_coe_mem_rowStochastic`: `P` is row-stochastic.
* `ProbabilityTheory.Kernel.eq_of_toMatrix_map_coe_mulVec_eq_of_mem_communicatingClass`: a
  harmonic function is constant on each closed communicating class, and
  `ProbabilityTheory.Kernel.eq_of_toMatrix_map_coe_mulVec_eq_of_forall_reaches`: it is constant
  when every state reaches every other state.

## References

* [D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, 2017][LPW17],
  Lemma 1.16
* [M. L. Puterman, *Markov Decision Processes*, 1994][P], Appendix A.2
-/

public section

open MeasureTheory Finset Matrix
open scoped NNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
  (κ : Kernel α α)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The entries of the real transition matrix of a kernel are its real masses. -/
theorem toMatrix_map_coe_apply (a b : α) :
    κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) a b = (κ a).real {b} := by
  rw [Matrix.map_apply, toMatrix_apply, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]

/-- The real transition matrix of a finite kernel acts on functions by integration:
`(P f) a = ∫ x, f x ∂(κ a)`. -/
theorem toMatrix_map_coe_mulVec [IsFiniteKernel κ] (f : α → ℝ) (a : α) :
    (κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ f) a = ∫ x, f x ∂(κ a) := by
  simp only [integral_fintype (.of_finite), mulVec, dotProduct, toMatrix_map_coe_apply,
    smul_eq_mul]

/-- The real transition matrix of `κ ^ n` is the `n`-th power of that of `κ`. -/
theorem toMatrix_map_coe_pow [DecidableEq α] [IsFiniteKernel κ] (n : ℕ) :
    (κ ^ n).toMatrix.map ((↑) : ℝ≥0 → ℝ) = κ.toMatrix.map (↑) ^ n := by
  simpa [toMatrix_pow] using map_pow (NNReal.toRealHom.mapMatrix (m := α)) κ.toMatrix n

/-- The real transition matrix of a Markov kernel is row-stochastic. -/
theorem toMatrix_map_coe_mem_rowStochastic [DecidableEq α] [IsMarkovKernel κ] :
    κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) ∈ Matrix.rowStochastic ℝ α := by
  refine Matrix.mem_rowStochastic.2 ⟨fun a b ↦ by simp, ?_⟩
  ext a
  simpa using toMatrix_map_coe_mulVec κ 1 a

variable {κ}

/-- A function harmonic for `κ` is harmonic for every power of `κ`. -/
theorem toMatrix_map_coe_pow_mulVec_eq [IsFiniteKernel κ] {g : α → ℝ}
    (hg : κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ g = g) (n : ℕ) :
    (κ ^ n).toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ g = g := by
  classical
  rw [toMatrix_map_coe_pow]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hg, ih]

/-- Under a kernel whose mass stays in a closed set `s`, a harmonic function that is maximal on
`s` at `z ∈ s` takes the value `g z` at every state of `s` reachable from `z`. -/
private lemma eq_of_reaches_of_isMaxOn [IsMarkovKernel κ] {g : α → ℝ}
    (hg : κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ g = g) {s : Set α} (hs : κ.IsClosedSet s)
    {z w : α} (hz : z ∈ s) (hmax : IsMaxOn g s z) (hzw : κ.Reaches z w) : g w = g z := by
  obtain ⟨n, hn⟩ := (reaches_def z w).1 hzw
  -- `g z` is the `κ ^ n z`-average of `g`, whose terms are at most `g z`
  have havg : ∑ t, ((κ ^ n) z).real {t} * (g z - g t) = 0 := by
    have h := congrFun (toMatrix_map_coe_pow_mulVec_eq hg n) z
    rw [toMatrix_map_coe_mulVec, integral_fintype (.of_finite)] at h
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, smul_eq_mul] at h ⊢
    rw [sum_measureReal_singleton, coe_univ, probReal_univ, one_mul, h, sub_self]
  have hterm (t : α) : 0 ≤ ((κ ^ n) z).real {t} * (g z - g t) := by
    by_cases ht : (κ ^ n) z {t} = 0
    · simp [measureReal_def, ht]
    · exact mul_nonneg measureReal_nonneg <| sub_nonneg.2 <| hmax <|
        hs.mem_of_reaches (Set.toFinite s).measurableSet hz ((reaches_def z t).2
          ⟨n, pos_iff_ne_zero.2 ht⟩)
  have hw := (sum_eq_zero_iff_of_nonneg fun t _ ↦ hterm t).1 havg w (mem_univ w)
  have hpos : 0 < ((κ ^ n) z).real {w} := ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  rw [mul_eq_zero, or_iff_right hpos.ne', sub_eq_zero] at hw
  exact hw.symm

/-- **The maximum principle on closed classes**: a function harmonic for a Markov kernel on a
finite space, `P g = g`, is constant on every closed communicating class. -/
theorem eq_of_toMatrix_map_coe_mulVec_eq_of_mem_communicatingClass [IsMarkovKernel κ]
    {g : α → ℝ} (hg : κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ g = g) {x y : α}
    (hx : κ.IsClosedSet (κ.communicatingClass x)) (hy : y ∈ κ.communicatingClass x) :
    g y = g x := by
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image _ g (Set.toFinite (κ.communicatingClass x))
    ⟨x, (mem_communicatingClass_iff x x).2 (Communicates.refl x)⟩
  have hz' : κ.Communicates z x := ((mem_communicatingClass_iff x z).1 hz).symm
  have hzy : κ.Communicates z y := hz'.trans ((mem_communicatingClass_iff x y).1 hy)
  rw [eq_of_reaches_of_isMaxOn hg hx hz hmax ((communicates_def z y).1 hzy).1,
    eq_of_reaches_of_isMaxOn hg hx hz hmax ((communicates_def z x).1 hz').1]

/-- **The maximum principle**: a function harmonic for a Markov kernel on a finite space in which
every state reaches every other state is constant. -/
theorem eq_of_toMatrix_map_coe_mulVec_eq_of_forall_reaches [IsMarkovKernel κ]
    {g : α → ℝ} (hg : κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) *ᵥ g = g) (hκ : ∀ x y, κ.Reaches x y)
    (x y : α) : g y = g x := by
  have huniv : κ.communicatingClass x = Set.univ :=
    Set.eq_univ_of_forall fun w ↦ (mem_communicatingClass_iff x w).2 <|
      (communicates_def x w).2 ⟨hκ x w, hκ w x⟩
  refine eq_of_toMatrix_map_coe_mulVec_eq_of_mem_communicatingClass hg ?_ (huniv ▸ trivial)
  rw [isClosedSet_def, huniv]
  simp

end ProbabilityTheory.Kernel
