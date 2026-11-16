/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import LMLExplore.Analysis.Normed.Operator.MeanErgodic
public import LMLExplore.Analysis.SpecificLimits.Normed
public import LMLExplore.Topology.Algebra.Module.Basic

/-!
# The deviation operator and the Laurent expansion of the resolvent

Let `T` be a power-bounded continuous linear operator on a Banach space `E` over `ℝ` or `ℂ`, such
that the fixed points `ker (1 - T)` and the range of `1 - T` span `E`. Then the range of `1 - T`
is closed and complementary to `ker (1 - T)`, the Cesàro means of `T` converge everywhere, and
their limit is the mean ergodic projection `Π` (`LMLExplore.IsPowerBounded.meanErgodicProj`). In
finite dimension the hypothesis always holds.

The operator `1 - T + Π` is then invertible, and the *deviation operator*
`D = (1 - T + Π)⁻¹ - Π` is the group inverse of `1 - T`:
`(1 - T) D = D (1 - T) = 1 - Π` and `D Π = Π D = 0`. For a stochastic matrix `P` acting on
functions, `Π` is the limiting matrix `P*` and `D` the deviation matrix of `P`: if the rewards are
`r`, then `Π r` is the gain and `D r` the bias of the Markov reward process.

For `0 < γ < 1` close to `1` the resolvent `(1 - γ T)⁻¹` has the Laurent expansion
`(1 - γ T)⁻¹ = (1 + u) (u⁻¹ Π + ∑ₙ (-u) ^ n D ^ (n + 1))` in `u = (1 - γ) / γ`, so that
`(1 - γ T)⁻¹ = (1 - γ)⁻¹ Π + D + o(1)` as `γ ↑ 1`.

Inverses are Mathlib's `Ring.inverse` (notation `x⁻¹ʳ`) in the Banach algebra `E →L[𝕜] E`, as for
the resolvent `ProbabilityTheory.Kernel.ringInverse_one_sub_smul_integralCLM` of a Markov kernel.

## Main definitions

* `LMLExplore.IsPowerBounded.deviation`: the deviation operator `D = (1 - T + Π)⁻¹ - Π`.

## Main statements

* `LMLExplore.IsPowerBounded.isCompl_ker_range`, `LMLExplore.IsPowerBounded.isClosed_range`: the
  hypothesis is that `ker (1 - T)` and the closed range of `1 - T` are complementary.
* `LMLExplore.IsPowerBounded.ker_sup_range_eq_top`: the hypothesis holds in finite dimension.
* `LMLExplore.IsPowerBounded.isUnit_one_sub_add_meanErgodicProj`: `1 - T + Π` is invertible.
* `LMLExplore.IsPowerBounded.one_sub_mul_deviation`,
  `LMLExplore.IsPowerBounded.deviation_mul_one_sub`,
  `LMLExplore.IsPowerBounded.deviation_mul_meanErgodicProj`,
  `LMLExplore.IsPowerBounded.meanErgodicProj_mul_deviation`: `(1 - T) D = D (1 - T) = 1 - Π` and
  `D Π = Π D = 0`.
* `LMLExplore.IsPowerBounded.eq_deviation_of_mul_one_sub`,
  `LMLExplore.IsPowerBounded.eq_deviation_of_one_sub_mul`: these identities characterize `D`.
* `LMLExplore.IsPowerBounded.tendsto_cesaro_sum_pow_sub_meanErgodicProj_apply`: `D x` is the
  Cesàro limit of the partial sums `∑ k < n, (T ^ k x - Π x)`; in operator norm in finite
  dimension (`LMLExplore.IsPowerBounded.tendsto_cesaro_sum_pow_sub_meanErgodicProj`).
* `LMLExplore.IsPowerBounded.eq_meanErgodicProj_and_eq_deviation_iff`: `(g, h) = (Π r, D r)` is the
  unique solution of `(1 - T) g = 0`, `g + (1 - T) h = r`, `Π h = 0`.
* `LMLExplore.IsPowerBounded.isUnit_one_sub_smul`,
  `LMLExplore.IsPowerBounded.ringInverse_one_sub_smul_eq_laurent`: the Laurent expansion of the
  resolvent.
* `LMLExplore.IsPowerBounded.tendsto_ringInverse_one_sub_smul_sub`:
  `(1 - γ T)⁻¹ = (1 - γ)⁻¹ Π + D + o(1)` as `γ ↑ 1`.
* `LMLExplore.IsPowerBounded.tendsto_one_sub_smul_ringInverse_one_sub_smul` and
  `LMLExplore.IsPowerBounded.tendsto_inv_smul_one_sub_smul_ringInverse_one_sub_smul_sub`:
  `(1 - γ) (1 - γ T)⁻¹ → Π` and `((1 - γ) (1 - γ T)⁻¹ - Π) / (1 - γ) → D` as `γ ↑ 1`, in
  operator norm.

## References

* M. L. Puterman, *Markov Decision Processes*, Wiley, 1994, Appendix A.5, Theorems A.7–A.8.
* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Exercises 38.7 and 38.9.
-/

public section

open Filter Finset Function Module Submodule Topology
open scoped Ring

namespace LMLExplore.IsPowerBounded

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E}

/-- In finite dimension, the fixed points and the range of `1 - T` span the space when `T` is
power bounded. -/
theorem ker_sup_range_eq_top [FiniteDimensional 𝕜 E] (hT : IsPowerBounded T) :
    (1 - T).ker ⊔ (1 - T).range = ⊤ := by
  simpa [(Submodule.isClosed_of_finiteDimensional _).submodule_topologicalClosure_eq] using
    hT.ker_sup_topologicalClosure_range_eq_top

section Deviation

variable (hT : IsPowerBounded T) (hR : (1 - T).ker ⊔ (1 - T).range = ⊤)
include hT hR

/-- The range of `1 - T` is closed. -/
theorem isClosed_range : IsClosed ((1 - T).range : Set E) := by
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  rw [← topologicalClosure_coe, SetLike.mem_coe,
    ← hT.meanErgodicProj_apply_eq_zero_iff (sup_topologicalClosure_eq_top hR)] at hy
  obtain ⟨k, hk, r, hr, rfl⟩ := mem_sup.1 (hR ▸ mem_top : y ∈ (1 - T).ker ⊔ (1 - T).range)
  have hr' : hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) r = 0 :=
    (hT.meanErgodicProj_apply_eq_zero_iff _).2 (le_topologicalClosure _ hr)
  rw [map_add, hT.meanErgodicProj_apply_of_mem_ker _ hk, hr', add_zero] at hy
  simpa [hy] using hr

/-- The fixed points and the range of `1 - T` are complementary. -/
theorem isCompl_ker_range : IsCompl (1 - T).ker (1 - T).range :=
  ⟨hT.disjoint_ker_topologicalClosure_range.mono_right (le_topologicalClosure _),
    codisjoint_iff.2 hR⟩

/-- `(1 - T + Π) Π = Π`. -/
private lemma one_sub_add_meanErgodicProj_mul :
    (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) *
      hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) =
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  rw [add_mul, one_sub_mul_meanErgodicProj, meanErgodicProj_mul_self, zero_add]

/-- `Π (1 - T + Π) = Π`. -/
private lemma meanErgodicProj_mul_one_sub_add :
    hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) *
      (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) =
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  rw [mul_add, meanErgodicProj_mul_one_sub, meanErgodicProj_mul_self, zero_add]

/-- The operator `1 - T + Π` is invertible. It is the identity on the fixed points of `T` and
`1 - T` on the range of `1 - T`. -/
theorem isUnit_one_sub_add_meanErgodicProj [CompleteSpace E] :
    IsUnit (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) := by
  set P := hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)
  refine ContinuousLinearMap.isUnit_iff_bijective.2 ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    fun y ↦ ?_⟩
  · -- Applying `Π` gives `Π x = 0`, hence `x - T x = 0`, so that `x = Π x = 0`.
    have hPx : P x = 0 := by
      simpa [← mul_apply_eq_comp, P, meanErgodicProj_mul_one_sub_add] using
        congr(P $hx)
    have hx' : x ∈ (1 - T).ker := by
      simpa [hPx] using hx
    exact (hT.meanErgodicProj_apply_of_mem_ker _ hx').symm.trans hPx
  · -- Write `y = k + (1 - T) z` with `T k = k`; then `y = (1 - T + Π) (k + z - Π z)`.
    obtain ⟨k, hk, r, ⟨z, rfl⟩, rfl⟩ := mem_sup.1 (hR ▸ mem_top : y ∈ (1 - T).ker ⊔ (1 - T).range)
    refine ⟨k + (z - P z), ?_⟩
    have hk' : (1 - T) k = 0 := LinearMap.mem_ker.1 hk
    have h1 : (1 - T) (P z) = 0 := by
      rw [← mul_apply_eq_comp, one_sub_mul_meanErgodicProj, zero_apply]
    have h2 : P (P z) = P z := hT.meanErgodicProj_meanErgodicProj_apply _ z
    have h3 : P k = k := hT.meanErgodicProj_apply_of_mem_ker _ hk
    simp only [add_apply, map_add, map_sub, hk', h1, h2, h3]
    abel

/-- The *deviation operator* `D = (1 - T + Π)⁻¹ - Π` of a power-bounded operator `T` whose fixed
points and range of `1 - T` span the space, where `Π` is the mean ergodic projection of `T`. It is
the group inverse of `1 - T` (`LMLExplore.IsPowerBounded.eq_deviation_of_mul_one_sub`), and the
Cesàro limit of the partial sums `∑ k < n, (T ^ k - Π)`
(`LMLExplore.IsPowerBounded.tendsto_cesaro_sum_pow_sub_meanErgodicProj_apply`). For a
stochastic matrix it is the deviation matrix. -/
noncomputable def deviation : E →L[𝕜] E :=
  (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))⁻¹ʳ -
    hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)

/-- `(1 - T + Π)⁻¹ = D + Π`. -/
theorem ringInverse_one_sub_add_meanErgodicProj :
    (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))⁻¹ʳ =
      hT.deviation hR + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  rw [deviation, sub_add_cancel]

variable [CompleteSpace E]

/-- `(1 - T + Π)⁻¹ Π = Π`. -/
private lemma ringInverse_one_sub_add_meanErgodicProj_mul :
    (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))⁻¹ʳ *
      hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) =
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  have := Ring.inverse_mul_cancel_left _
    (hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))
    (hT.isUnit_one_sub_add_meanErgodicProj hR)
  rwa [hT.one_sub_add_meanErgodicProj_mul hR] at this

/-- `Π (1 - T + Π)⁻¹ = Π`. -/
private lemma meanErgodicProj_mul_ringInverse_one_sub_add :
    hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) *
      (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))⁻¹ʳ =
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  have := Ring.mul_inverse_cancel_right _
    (hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))
    (hT.isUnit_one_sub_add_meanErgodicProj hR)
  rwa [hT.meanErgodicProj_mul_one_sub_add hR] at this

/-- `D Π = 0`. -/
@[simp]
theorem deviation_mul_meanErgodicProj :
    hT.deviation hR * hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) = 0 := by
  rw [deviation, sub_mul, hT.ringInverse_one_sub_add_meanErgodicProj_mul hR,
    meanErgodicProj_mul_self, sub_self]

/-- `Π D = 0`. -/
@[simp]
theorem meanErgodicProj_mul_deviation :
    hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) * hT.deviation hR = 0 := by
  rw [deviation, mul_sub, hT.meanErgodicProj_mul_ringInverse_one_sub_add hR,
    meanErgodicProj_mul_self, sub_self]

/-- `(1 - T) D = 1 - Π`. -/
@[simp]
theorem one_sub_mul_deviation :
    (1 - T) * hT.deviation hR = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  have hS := hT.isUnit_one_sub_add_meanErgodicProj hR
  calc (1 - T) * hT.deviation hR
      = (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) -
          hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) * hT.deviation hR := by
        rw [add_sub_cancel_right]
    _ = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
        rw [sub_mul, hT.meanErgodicProj_mul_deviation hR, sub_zero, deviation, mul_sub,
          Ring.mul_inverse_cancel _ hS, hT.one_sub_add_meanErgodicProj_mul hR]

/-- `D (1 - T) = 1 - Π`. -/
@[simp]
theorem deviation_mul_one_sub :
    hT.deviation hR * (1 - T) = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
  have hS := hT.isUnit_one_sub_add_meanErgodicProj hR
  calc hT.deviation hR * (1 - T)
      = hT.deviation hR * (1 - T + hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) -
          hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) := by
        rw [add_sub_cancel_right]
    _ = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) := by
        rw [mul_sub, hT.deviation_mul_meanErgodicProj hR, sub_zero, deviation, sub_mul,
          Ring.inverse_mul_cancel _ hS, hT.meanErgodicProj_mul_one_sub_add hR]

/-- `D` is the only operator `X` with `X (1 - T) = 1 - Π` and `X Π = 0`. -/
theorem eq_deviation_of_mul_one_sub {X : E →L[𝕜] E}
    (h₁ : X * (1 - T) = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))
    (h₂ : X * hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) = 0) :
    X = hT.deviation hR := by
  -- `X = X (1 - Π) = X (1 - T) D = (1 - Π) D = D`.
  have h : X * (1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) = X := by
    rw [mul_sub, mul_one, h₂, sub_zero]
  rw [← h, ← hT.one_sub_mul_deviation hR, ← mul_assoc, h₁, sub_mul, one_mul,
    meanErgodicProj_mul_deviation, sub_zero]

/-- `D` is the only operator `X` with `(1 - T) X = 1 - Π` and `Π X = 0`. -/
theorem eq_deviation_of_one_sub_mul {X : E →L[𝕜] E}
    (h₁ : (1 - T) * X = 1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))
    (h₂ : hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) * X = 0) :
    X = hT.deviation hR := by
  -- `X = (1 - Π) X = D (1 - T) X = D (1 - Π) = D`.
  have h : (1 - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) * X = X := by
    rw [sub_mul, one_mul, h₂, sub_zero]
  rw [← h, ← hT.deviation_mul_one_sub hR, mul_assoc, h₁, mul_sub, mul_one,
    deviation_mul_meanErgodicProj, sub_zero]

/-- The partial sums of the deviations `T ^ k - Π` are `∑ k < n, (T ^ k - Π) = D (1 - T ^ n)`. -/
theorem sum_range_pow_sub_meanErgodicProj (n : ℕ) :
    ∑ k ∈ range n, (T ^ k - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) =
      hT.deviation hR * (1 - T ^ n) := by
  set P := hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)
  have hS := hT.isUnit_one_sub_add_meanErgodicProj hR
  -- `(1 - T + Π) (T ^ k - Π) = T ^ k - T ^ (k + 1)` telescopes to `1 - T ^ n`.
  have hsum : (1 - T + P) * ∑ k ∈ range n, (T ^ k - P) = 1 - T ^ n := by
    rw [mul_sum]
    have hk : ∀ k, (1 - T + P) * (T ^ k - P) = T ^ k - T ^ (k + 1) := fun k ↦ by
      rw [mul_sub, hT.one_sub_add_meanErgodicProj_mul hR, add_mul, sub_mul, one_mul,
        meanErgodicProj_mul_pow, ← pow_succ']
      abel
    simp only [hk]
    rw [sum_range_sub', pow_zero]
  rw [← Ring.inverse_mul_cancel_left _ (∑ k ∈ range n, (T ^ k - P)) hS, hsum,
    ringInverse_one_sub_add_meanErgodicProj, add_mul, mul_sub P, mul_one, meanErgodicProj_mul_pow,
    sub_self, add_zero]

/-- The deviation operator is the Cesàro limit of the partial sums of the deviations
`T ^ k x - Π x`: `(N : 𝕜)⁻¹ • ∑ n < N, ∑ k < n, (T ^ k x - Π x) → D x`. -/
theorem tendsto_cesaro_sum_pow_sub_meanErgodicProj_apply (x : E) :
    Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n ∈ range N, ∑ k ∈ range n,
      ((T ^ k) x - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) x)) atTop
      (𝓝 (hT.deviation hR x)) := by
  set P := hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)
  set D := hT.deviation hR
  -- The Cesàro mean is `D x - D (A_N x)`, with `A_N` the Cesàro mean of `T`, and `A_N x → Π x`.
  have hlim : Tendsto (fun N ↦ D x - D (birkhoffAverage 𝕜 T _root_.id N x)) atTop
      (𝓝 (D x - D (P x))) :=
    tendsto_const_nhds.sub ((D.continuous.tendsto _).comp
      (hT.tendsto_birkhoffAverage_meanErgodicProj _ x))
  have hDP : D (P x) = 0 := by
    rw [← mul_apply_eq_comp, hT.deviation_mul_meanErgodicProj hR, zero_apply]
  rw [hDP, sub_zero] at hlim
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun N hN ↦ ?_⟩)
  have hinner : ∀ n, ∑ k ∈ range n, ((T ^ k) x - P x) = D x - D ((T ^ n) x) := fun n ↦ by
    have := congr($(hT.sum_range_pow_sub_meanErgodicProj hR n) x)
    simpa [sum_apply, D, P] using this
  have hN0 : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [ContinuousLinearMap.birkhoffAverage_eq_smul_sum_pow]
  simp only [hinner, sum_sub_distrib, sum_const, card_range, smul_apply,
    sum_apply, map_smul, map_sum, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hN0, one_smul]

/-- In finite dimension, the Cesàro means of the partial sums `∑ k < n, (T ^ k - Π)` converge to
the deviation operator in operator norm. -/
theorem tendsto_cesaro_sum_pow_sub_meanErgodicProj [FiniteDimensional 𝕜 E] :
    Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n ∈ range N, ∑ k ∈ range n,
      (T ^ k - hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))) atTop
      (𝓝 (hT.deviation hR)) := by
  refine tendsto_clm_apply.2 fun x ↦ ?_
  simpa [sum_apply] using
    hT.tendsto_cesaro_sum_pow_sub_meanErgodicProj_apply hR x

/-- **The evaluation equations.** `(g, h) = (Π r, D r)` is the unique solution of
`(1 - T) g = 0`, `g + (1 - T) h = r` and `Π h = 0`. For the action of a stochastic matrix and a
reward `r`, these are the equations of the gain `g` and the bias `h`. -/
theorem eq_meanErgodicProj_and_eq_deviation_iff {g h r : E} :
    g = hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) r ∧ h = hT.deviation hR r ↔
      (1 - T) g = 0 ∧ g + (1 - T) h = r ∧
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) h = 0 := by
  set P := hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)
  set D := hT.deviation hR
  have hNP : ∀ x, (1 - T) (P x) = 0 := fun x ↦ by
    rw [← mul_apply_eq_comp, one_sub_mul_meanErgodicProj, zero_apply]
  have hPN : ∀ x, P ((1 - T) x) = 0 := fun x ↦ by
    rw [← mul_apply_eq_comp, meanErgodicProj_mul_one_sub, zero_apply]
  have hND : ∀ x, (1 - T) (D x) = x - P x := fun x ↦ by
    rw [← mul_apply_eq_comp, hT.one_sub_mul_deviation hR]
    simp [P]
  have hDN : ∀ x, D ((1 - T) x) = x - P x := fun x ↦ by
    rw [← mul_apply_eq_comp, hT.deviation_mul_one_sub hR]
    simp [P]
  have hPD : ∀ x, P (D x) = 0 := fun x ↦ by
    rw [← mul_apply_eq_comp, hT.meanErgodicProj_mul_deviation hR, zero_apply]
  have hDP : ∀ x, D (P x) = 0 := fun x ↦ by
    rw [← mul_apply_eq_comp, hT.deviation_mul_meanErgodicProj hR, zero_apply]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨hNP r, by rw [hND, add_sub_cancel], hPD r⟩
  · rintro ⟨hg, hgh, hh⟩
    -- Applying `Π` to `g + (1 - T) h = r` gives `g = Π g = Π r`.
    have hPg : P g = g := hT.meanErgodicProj_apply_of_mem_ker _ hg
    have hgr : g = P r := by
      rw [← hgh, map_add, hPN, add_zero, hPg]
    refine ⟨hgr, ?_⟩
    -- Applying `D` to `(1 - T) h = r - g` gives `h = h - Π h = D r - D (Π r) = D r`.
    have hNh : (1 - T) h = r - P r := by
      rw [← hgr, ← hgh, add_sub_cancel_left]
    have := hDN h
    rw [hNh, hh, sub_zero, map_sub, hDP, sub_zero] at this
    exact this.symm

/-! ### The Laurent expansion of the resolvent -/

/-- For `u ≠ 0` with `‖u‖ ‖D‖ < 1`, `u + (1 - T)` has the two-sided inverse
`u⁻¹ Π + D (1 + u D)⁻¹`. -/
private lemma smul_one_add_one_sub_mul_eq_one {u : 𝕜} (hu : u ≠ 0)
    (hD : ‖u‖ * ‖hT.deviation hR‖ < 1) :
    (u • 1 + (1 - T)) * (u⁻¹ • hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        hT.deviation hR * (1 + u • hT.deviation hR)⁻¹ʳ) = 1 ∧
      (u⁻¹ • hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        hT.deviation hR * (1 + u • hT.deviation hR)⁻¹ʳ) * (u • 1 + (1 - T)) = 1 := by
  set P := hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)
  set D := hT.deviation hR
  set Q := 1 + u • D
  set V := Q⁻¹ʳ
  have hQ : IsUnit Q := by
    have hx : ‖-(u • D)‖ < 1 := by
      rw [norm_neg]
      exact (norm_smul_le u D).trans_lt hD
    simpa [Q, sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hx
  have hQV : Q * V = 1 := Ring.mul_inverse_cancel _ hQ
  have hVQ : V * Q = 1 := Ring.inverse_mul_cancel _ hQ
  have hPD : P * D = 0 := hT.meanErgodicProj_mul_deviation hR
  have hDP : D * P = 0 := hT.deviation_mul_meanErgodicProj hR
  -- `Π` commutes with `Q` and `Q⁻¹`, and so does `D`.
  have hPQ : P * Q = P := by simp [Q, mul_add, hPD]
  have hQP : Q * P = P := by simp [Q, add_mul, hDP]
  have hPV : P * V = P := by rw [← hPQ, mul_assoc, hQV, mul_one, hPQ]
  have hVP : V * P = P := by rw [← hQP, ← mul_assoc, hVQ, one_mul, hQP]
  have hDQ : D * Q = Q * D := by simp [Q, mul_add, add_mul]
  have hDV : D * V = V * D := by
    calc D * V = V * Q * D * V := by rw [hVQ, one_mul]
      _ = V * D * (Q * V) := by rw [mul_assoc V Q D, ← hDQ]; noncomm_ring
      _ = V * D := by rw [hQV, mul_one]
  have hVDV : V + u • (D * V) = 1 := by
    rw [← hQV, add_mul, one_mul, smul_mul_assoc]
  constructor
  · calc (u • 1 + (1 - T)) * (u⁻¹ • P + D * V)
        = (u⁻¹ * u) • P + u • (D * V) + u⁻¹ • ((1 - T) * P) + (1 - T) * D * V := by
          simp only [add_mul, mul_add, smul_add, smul_mul_assoc, one_mul, mul_smul_comm, smul_smul,
            mul_assoc]
          abel
      _ = 1 := by
          rw [inv_mul_cancel₀ hu, one_smul, one_sub_mul_meanErgodicProj, smul_zero, add_zero,
            hT.one_sub_mul_deviation hR, sub_mul, one_mul, hPV, ← hVDV]
          abel
  · calc (u⁻¹ • P + D * V) * (u • 1 + (1 - T))
        = (u * u⁻¹) • P + u • (D * V) + u⁻¹ • (P * (1 - T)) + V * (D * (1 - T)) := by
          rw [← mul_assoc V, ← hDV]
          simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_one, mul_smul_comm, smul_smul,
            mul_assoc]
          abel
      _ = 1 := by
          rw [mul_inv_cancel₀ hu, one_smul, meanErgodicProj_mul_one_sub, smul_zero, add_zero,
            hT.deviation_mul_one_sub hR, mul_sub, mul_one, hVP, ← hVDV]
          abel

/-- For `0 < γ < 1` and `u = (1 - γ) / γ` with `u ‖D‖ < 1`, `1 - γ T` has the two-sided inverse
`γ⁻¹ (u⁻¹ Π + D (1 + u D)⁻¹)`. -/
private lemma one_sub_smul_mul_eq_one {γ u : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hu : u = (1 - γ) / γ) (hD : u * ‖hT.deviation hR‖ < 1) :
    (1 - (γ : 𝕜) • T) * ((γ : 𝕜)⁻¹ • ((u : 𝕜)⁻¹ •
        hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        hT.deviation hR * (1 + (u : 𝕜) • hT.deviation hR)⁻¹ʳ)) = 1 ∧
      ((γ : 𝕜)⁻¹ • ((u : 𝕜)⁻¹ • hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        hT.deviation hR * (1 + (u : 𝕜) • hT.deviation hR)⁻¹ʳ)) * (1 - (γ : 𝕜) • T) = 1 := by
  have hu₀ : 0 < u := hu ▸ div_pos (sub_pos.2 hγ₁) hγ₀
  have hγ : (γ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hγ₀.ne'
  -- `1 - γ T = γ (u + (1 - T))`.
  have hsplit : 1 - (γ : 𝕜) • T = (γ : 𝕜) • ((u : 𝕜) • 1 + (1 - T)) := by
    have hγu : (γ : 𝕜) * u = 1 - γ := by
      rw [← RCLike.ofReal_mul, hu, mul_div_cancel₀ _ hγ₀.ne', RCLike.ofReal_sub,
        RCLike.ofReal_one]
    rw [smul_add, smul_smul, hγu, smul_sub, sub_smul, one_smul]
    abel
  have hD' : ‖(u : 𝕜)‖ * ‖hT.deviation hR‖ < 1 := by
    rwa [RCLike.norm_ofReal, abs_of_pos hu₀]
  obtain ⟨h₁, h₂⟩ := hT.smul_one_add_one_sub_mul_eq_one hR (RCLike.ofReal_ne_zero.2 hu₀.ne') hD'
  rw [hsplit, smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ hγ, inv_mul_cancel₀ hγ,
    h₁, h₂, one_smul]
  exact ⟨rfl, rfl⟩

/-- For `0 < γ < 1` with `(1 - γ) / γ * ‖D‖ < 1`, the operator `1 - γ T` is invertible. -/
theorem isUnit_one_sub_smul {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hD : (1 - γ) / γ * ‖hT.deviation hR‖ < 1) :
    IsUnit (1 - (γ : 𝕜) • T) :=
  isUnit_iff_exists.2 ⟨_, hT.one_sub_smul_mul_eq_one hR hγ₀ hγ₁ rfl hD⟩

/-- The closed form `(1 - γ T)⁻¹ = γ⁻¹ (u⁻¹ Π + D (1 + u D)⁻¹)` of the resolvent. -/
private lemma ringInverse_one_sub_smul_eq {γ u : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hu : u = (1 - γ) / γ) (hD : u * ‖hT.deviation hR‖ < 1) :
    (1 - (γ : 𝕜) • T)⁻¹ʳ = (γ : 𝕜)⁻¹ • ((u : 𝕜)⁻¹ •
      hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        hT.deviation hR * (1 + (u : 𝕜) • hT.deviation hR)⁻¹ʳ) :=
  Ring.inverse_unit ⟨_, _, (hT.one_sub_smul_mul_eq_one hR hγ₀ hγ₁ hu hD).1,
    (hT.one_sub_smul_mul_eq_one hR hγ₀ hγ₁ hu hD).2⟩

/-- **Laurent expansion of the resolvent.** For `0 < γ < 1` and `u = (1 - γ) / γ` with
`u ‖D‖ < 1`,
`(1 - γ T)⁻¹ = (1 + u) (u⁻¹ Π + ∑ₙ (-u) ^ n D ^ (n + 1))`. -/
theorem ringInverse_one_sub_smul_eq_laurent {γ u : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hu : u = (1 - γ) / γ) (hD : u * ‖hT.deviation hR‖ < 1) :
    (1 - (γ : 𝕜) • T)⁻¹ʳ = ((1 + u : ℝ) : 𝕜) • ((u : 𝕜)⁻¹ •
      hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) +
        ∑' n : ℕ, (-(u : 𝕜)) ^ n • hT.deviation hR ^ (n + 1)) := by
  have hu₀ : 0 < u := hu ▸ div_pos (sub_pos.2 hγ₁) hγ₀
  have hD' : ‖(u : 𝕜)‖ * ‖hT.deviation hR‖ < 1 := by
    rwa [RCLike.norm_ofReal, abs_of_pos hu₀]
  have h1u : 1 + u = γ⁻¹ := by
    rw [hu, one_add_div hγ₀.ne', add_sub_cancel, one_div]
  rw [hT.ringInverse_one_sub_smul_eq hR hγ₀ hγ₁ hu hD, tsum_neg_pow_smul_pow_succ hD', h1u,
    RCLike.ofReal_inv]

/-- For `γ < 1` close to `1`, `(1 - γ T)⁻¹ - (1 - γ)⁻¹ Π = γ⁻¹ D (1 + u D)⁻¹` with
`u = (1 - γ) / γ`. -/
private lemma eventually_ringInverse_one_sub_smul_sub :
    ∀ᶠ γ : ℝ in 𝓝[<] 1, (1 - (γ : 𝕜) • T)⁻¹ʳ -
        (1 - (γ : 𝕜))⁻¹ • hT.meanErgodicProj (sup_topologicalClosure_eq_top hR) =
      (γ : 𝕜)⁻¹ • (hT.deviation hR *
        (1 + (((1 - γ) / γ : ℝ) : 𝕜) • hT.deviation hR)⁻¹ʳ) := by
  have hu : Tendsto (fun γ : ℝ ↦ (1 - γ) / γ * ‖hT.deviation hR‖) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun γ : ℝ ↦ (1 - γ) / γ * ‖hT.deviation hR‖) 1 := by
      fun_prop (disch := norm_num)
    simpa using this.tendsto
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds one_pos),
    nhdsWithin_le_nhds (hu.eventually (gt_mem_nhds one_pos))] with γ hγ₁ hγ₀ hD
  rw [Set.mem_Iio] at hγ₁
  rw [Set.mem_Ioi] at hγ₀
  have hγu : (γ : 𝕜)⁻¹ * (((1 - γ) / γ : ℝ) : 𝕜)⁻¹ = (1 - (γ : 𝕜))⁻¹ := by
    rw [← mul_inv, ← RCLike.ofReal_mul, mul_div_cancel₀ _ hγ₀.ne', RCLike.ofReal_sub,
      RCLike.ofReal_one]
  rw [hT.ringInverse_one_sub_smul_eq hR hγ₀ hγ₁ rfl hD, smul_add, smul_smul, hγu,
    add_sub_cancel_left]

/-- **Laurent expansion to first order**: `(1 - γ T)⁻¹ = (1 - γ)⁻¹ Π + D + o(1)` as `γ ↑ 1`, in
operator norm. -/
theorem tendsto_ringInverse_one_sub_smul_sub :
    Tendsto (fun γ : ℝ ↦ (1 - (γ : 𝕜) • T)⁻¹ʳ -
      (1 - (γ : 𝕜))⁻¹ • hT.meanErgodicProj (sup_topologicalClosure_eq_top hR)) (𝓝[<] 1)
      (𝓝 (hT.deviation hR)) := by
  refine Tendsto.congr' ((hT.eventually_ringInverse_one_sub_smul_sub hR).mono fun _ h ↦ h.symm) ?_
  have h₁ : Tendsto (fun γ : ℝ ↦ (γ : 𝕜)⁻¹) (𝓝[<] 1) (𝓝 1) := by
    have : ContinuousAt (fun γ : ℝ ↦ (γ : 𝕜)⁻¹) 1 := by
      fun_prop (disch := simp)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have h₂ : Tendsto (fun γ : ℝ ↦ (1 + (((1 - γ) / γ : ℝ) : 𝕜) • hT.deviation hR)⁻¹ʳ) (𝓝[<] 1)
      (𝓝 1) := by
    have hc : Tendsto (fun γ : ℝ ↦ 1 + (((1 - γ) / γ : ℝ) : 𝕜) • hT.deviation hR) (𝓝 1)
        (𝓝 1) := by
      have : ContinuousAt (fun γ : ℝ ↦ 1 + (((1 - γ) / γ : ℝ) : 𝕜) • hT.deviation hR) 1 := by
        fun_prop (disch := norm_num)
      simpa using this.tendsto
    have hinv := (NormedRing.inverse_continuousAt (1 : (E →L[𝕜] E)ˣ)).tendsto
    rw [Units.val_one, Ring.inverse_one] at hinv
    exact (hinv.comp hc).mono_left nhdsWithin_le_nhds
  simpa using h₁.smul (tendsto_const_nhds.mul h₂)

/-- `(1 - γ) (1 - γ T)⁻¹ → Π` as `γ ↑ 1`, in operator norm. -/
theorem tendsto_one_sub_smul_ringInverse_one_sub_smul :
    Tendsto (fun γ : ℝ ↦ (1 - (γ : 𝕜)) • (1 - (γ : 𝕜) • T)⁻¹ʳ) (𝓝[<] 1)
      (𝓝 (hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))) := by
  have h₀ : Tendsto (fun γ : ℝ ↦ 1 - (γ : 𝕜)) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun γ : ℝ ↦ 1 - (γ : 𝕜)) 1 := by fun_prop
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have := (h₀.smul (hT.tendsto_ringInverse_one_sub_smul_sub hR)).add_const
    (hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))
  rw [zero_smul, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hγ' : 1 - (γ : 𝕜) ≠ 0 := by
    norm_cast
    exact sub_ne_zero.2 (Set.mem_Iio.1 hγ).ne'
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hγ', one_smul, sub_add_cancel]

/-- `((1 - γ) (1 - γ T)⁻¹ - Π) / (1 - γ) → D` as `γ ↑ 1`, in operator norm. -/
theorem tendsto_inv_smul_one_sub_smul_ringInverse_one_sub_smul_sub :
    Tendsto (fun γ : ℝ ↦ (1 - (γ : 𝕜))⁻¹ • ((1 - (γ : 𝕜)) • (1 - (γ : 𝕜) • T)⁻¹ʳ -
      hT.meanErgodicProj (sup_topologicalClosure_eq_top hR))) (𝓝[<] 1)
      (𝓝 (hT.deviation hR)) := by
  refine (hT.tendsto_ringInverse_one_sub_smul_sub hR).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hγ' : 1 - (γ : 𝕜) ≠ 0 := by
    norm_cast
    exact sub_ne_zero.2 (Set.mem_Iio.1 hγ).ne'
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hγ', one_smul]

end Deviation

end LMLExplore.IsPowerBounded
