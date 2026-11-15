/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Deterministic
public import Mathlib.Algebra.Order.Chebyshev
public import LMLExplore.Analysis.InnerProductSpace.EllipticalPotential
public import LMLExplore.Bandits.LinearBandit.Basic

/-!
# The optimistic algorithm OFUL for stochastic linear bandits

OFUL (optimism in the face of uncertainty for linear bandits, also called LinUCB) plays at every
round an action whose features maximize an upper confidence bound on the expected reward
[LS, §19.3]. With the features `x s` and the rewards `y s` of the past rounds `s < t`, the design
operator `V_t = designOp (λ • 1) x t`, the ridge estimate `θ̂_t = ridgeEstimate λ x y t` and a
radius `r`, the optimistic index of a feature vector `v` is [LS, (19.13)]
`ofulIndex λ x y r t v = ⟪θ̂_t, v⟫ + r ‖v‖_{V_t⁻¹}`, with `‖v‖_{V⁻¹} = √⟪v, V⁻¹ v⟫`.
By the Cauchy–Schwarz inequality for the dual norms `‖·‖_{V_t}` and `‖·‖_{V_t⁻¹}`, it is at
least the expected reward `⟪θ', v⟫` of every parameter `θ'` of the confidence ellipsoid
`‖θ̂_t - θ'‖_{V_t} ≤ r`, in particular of the unknown parameter `θ` whenever it lies in that
ellipsoid.

The algorithm `oful S` is the deterministic algorithm whose action at round `n` is given by an
`OptimisticSelection` `S`: a measurable choice, from the history and the context, of an action
maximizing the optimistic index with radius `r n` among all actions. Such a measurable maximizer
is a parameter of the algorithm, since an infinite action set has no canonical measurable choice
of maximizers. For finitely many actions, `OptimisticSelection.ofFintype` plays the `argmax` of
the optimistic index, which depends measurably on the history in finite dimension.

The regret analysis [LS, Theorem 19.2] is pathwise. If `θ` lies in the confidence ellipsoids of
the rounds `t < n` with radii `r t ≤ R`, and the gaps between the expected rewards of the actions
are at most `G ≤ 2 R` (for example `G = 2` and `R ≥ 1` under [LS, Assumption 19.1]), then the
instantaneous regret of an optimistic action is at most `min G (2 R ‖x t‖_{V_t⁻¹})` and the
elliptical potential lemma gives
`R̂_n ≤ √(8 n R² log (det V_n / det V_0)) ≤ √(8 n R² d log (1 + n L² / (λ d)))` for features
bounded by `L`. Along the runs of OFUL in a linear bandit environment with σ²-sub-Gaussian noise,
the confidence ellipsoids of ridge regression [LS, Theorem 20.5] contain `θ` with probability at
least `1 - δ` for the radii [LS, (19.8)]
`√λ m + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d)))`, where `‖θ‖ ≤ m`.

## Main definitions

* `LMLExplore.Bandits.ofulIndex lam x y r t v`: the optimistic index `⟪θ̂_t, v⟫ + r ‖v‖_{V_t⁻¹}`.
* `LMLExplore.Bandits.OptimisticSelection φ lam r`: a measurable choice of an action of maximal
  optimistic index at every round.
* `LMLExplore.Bandits.oful S`: the OFUL algorithm.
* `LMLExplore.Bandits.OptimisticSelection.ofFintype φ hφ lam r`: the optimistic selection of an
  `argmax` of the optimistic index, for finitely many actions.

## Main statements

* `inner_le_ofulIndex`, `ofulIndex_le_inner_add`: if `θ` lies in the confidence ellipsoid of
  radius `r`, then `⟪θ, v⟫ ≤ ofulIndex λ x y r t v ≤ ⟪θ, v⟫ + 2 r ‖v‖_{V_t⁻¹}`.
* `inner_sub_inner_le_of_ofulIndex_le`: the instantaneous regret of an action of maximal
  optimistic index is at most `2 r ‖v‖_{V_t⁻¹}` for its features `v` [LS, (19.10)].
* `sum_iSup_inner_sub_inner_le_sqrt_log_det`, `sum_iSup_inner_sub_inner_le_sqrt_mul_log`:
  [LS, Theorem 19.2] in pathwise form, for any sequence of action sets.
* `OFUL.ofulIndex_le_ofulIndex_action`: the run lemma, along a run of OFUL the action played has
  maximal optimistic index.
* `OFUL.le_measureReal_linearRegret_le`: [LS, Theorem 19.2], with probability at least `1 - δ`
  the random regret of OFUL is at most `√(8 n R² d log (1 + n L² / (λ d)))`.
* `OFUL.integral_linearRegret_le`, `OFUL.integral_linearRegret_le_add_sqrt`: the expected regret
  of OFUL is at most `n G δ + √(8 n R² d log (1 + n L² / (λ d)))`, and at most
  `G + √(8 n R² d log (1 + n L² / (λ d)))` for `δ = 1 / n` [LS, Corollary 19.3, with explicit
  constants].
* `Measurable.ofulIndex`: in finite dimension, the optimistic index depends measurably on the
  covariates, the responses and the feature vector.
* `OFUL.integral_regret_le_add_sqrt`: on a stochastic bandit with `k` σ²-sub-Gaussian arms, seen
  as a linear bandit with one-hot features, the expected regret of OFUL is at most
  `G + √(8 n R² k log (1 + n / (λ k)))` for gaps at most `G`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 19.
* [AYPS] Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved algorithms for linear stochastic
  bandits*, NeurIPS 2011, Theorem 3.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module Learning Bandits
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits

variable {𝓞 𝓐 E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mΩ : MeasurableSpace Ω}
  {φ : 𝓞 → 𝓐 → E} {θ : E} {lam : ℝ}

section Index

variable {x : ℕ → E} {y : ℕ → ℝ} {r : ℝ} {t : ℕ}

/-- The **optimistic index** of OFUL [LS, (19.13)]: for the covariates `x s` and the responses
`y s` of the rounds `s < t`, a radius `r` and a feature vector `v`, the upper confidence bound
`⟪θ̂_t, v⟫ + r ‖v‖_{V_t⁻¹}` on the expected reward `⟪θ, v⟫`, where `V_t = designOp (λ • 1) x t`,
`θ̂_t = ridgeEstimate λ x y t` and `‖v‖_{V⁻¹} = √⟪v, V⁻¹ v⟫`. -/
noncomputable def ofulIndex (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (r : ℝ) (t : ℕ) (v : E) : ℝ :=
  ⟪ridgeEstimate lam x y t, v⟫_ℝ + r * √⟪v, Ring.inverse (designOp (lam • 1) x t) v⟫_ℝ

lemma ofulIndex_def (v : E) :
    ofulIndex lam x y r t v =
      ⟪ridgeEstimate lam x y t, v⟫_ℝ + r * √⟪v, Ring.inverse (designOp (lam • 1) x t) v⟫_ℝ :=
  (rfl)

/-- The optimistic index of round `t` only depends on the covariates and the responses of the
rounds `s < t`. -/
lemma ofulIndex_congr {x' : ℕ → E} {y' : ℕ → ℝ} (hx : ∀ s < t, x s = x' s)
    (hy : ∀ s < t, y s = y' s) :
    ofulIndex lam x y r t = ofulIndex lam x' y' r t := by
  funext v
  rw [ofulIndex_def, ofulIndex_def, ridgeEstimate_congr hx hy, designOp_congr hx]

/-- **Optimism**: if `θ` lies in the confidence ellipsoid `‖θ̂_t - θ‖_{V_t} ≤ r`, then the
optimistic index of `v` is an upper bound on the expected reward `⟪θ, v⟫`. -/
theorem inner_le_ofulIndex (hlam : 0 < lam)
    (hθ : √⟪ridgeEstimate lam x y t - θ,
      designOp (lam • 1) x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤ r)
    (v : E) :
    ⟪θ, v⟫_ℝ ≤ ofulIndex lam x y r t v := by
  have h := (abs_le.1 (abs_inner_ridgeEstimate_sub_le hlam x y t hθ v)).1
  rw [inner_sub_left] at h
  rw [ofulIndex_def]
  linarith

/-- If `θ` lies in the confidence ellipsoid `‖θ̂_t - θ‖_{V_t} ≤ r`, then the optimistic index of
`v` exceeds the expected reward `⟪θ, v⟫` by at most `2 r ‖v‖_{V_t⁻¹}`. -/
theorem ofulIndex_le_inner_add (hlam : 0 < lam)
    (hθ : √⟪ridgeEstimate lam x y t - θ,
      designOp (lam • 1) x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤ r)
    (v : E) :
    ofulIndex lam x y r t v ≤
      ⟪θ, v⟫_ℝ + 2 * r * √⟪v, Ring.inverse (designOp (lam • 1) x t) v⟫_ℝ := by
  have h := (abs_le.1 (abs_inner_ridgeEstimate_sub_le hlam x y t hθ v)).2
  rw [inner_sub_left] at h
  rw [ofulIndex_def]
  linarith

/-- **Instantaneous regret of an optimistic action** [LS, (19.10)]: if `θ` lies in the confidence
ellipsoid `‖θ̂_t - θ‖_{V_t} ≤ r` and the action `b` has maximal optimistic index among the
actions with features `f a`, then `⟪θ, f a⟫ - ⟪θ, f b⟫ ≤ 2 r ‖f b‖_{V_t⁻¹}` for every action
`a`. -/
theorem inner_sub_inner_le_of_ofulIndex_le (hlam : 0 < lam)
    (hθ : √⟪ridgeEstimate lam x y t - θ,
      designOp (lam • 1) x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤ r)
    {f : 𝓐 → E} {b : 𝓐} (hb : ∀ a, ofulIndex lam x y r t (f a) ≤ ofulIndex lam x y r t (f b))
    (a : 𝓐) :
    ⟪θ, f a⟫_ℝ - ⟪θ, f b⟫_ℝ ≤ 2 * r * √⟪f b, Ring.inverse (designOp (lam • 1) x t) (f b)⟫_ℝ := by
  linarith [inner_le_ofulIndex hlam hθ (f a), ofulIndex_le_inner_add hlam hθ (f b), hb a]

end Index

section MeasurableIndex

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {β : Type*}
  {mβ : MeasurableSpace β}

/-- In finite dimension, the optimistic index of measurable families of covariates, responses and
feature vectors is measurable. -/
@[fun_prop]
theorem _root_.Measurable.ofulIndex {x : β → ℕ → E} {y : β → ℕ → ℝ} {v : β → E}
    (hx : Measurable x) (hy : Measurable y) (hv : Measurable v) (lam r : ℝ) (t : ℕ) :
    Measurable fun b ↦ ofulIndex lam (x b) (y b) r t (v b) := by
  simp_rw [ofulIndex_def]
  refine ((hx.ridgeEstimate hy lam t).inner hv).add (measurable_const.mul ?_)
  exact (hv.inner (isBoundedBilinearMap_apply.continuous.measurable2
    (hx.designOp (lam • 1) t).ringInverse hv)).sqrt

end MeasurableIndex

section Pathwise

variable [FiniteDimensional ℝ E] {f : ℕ → 𝓐 → E} {b : ℕ → 𝓐} {y : ℕ → ℝ} {r : ℕ → ℝ}
  {G R : ℝ} {n : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The square of the instantaneous regret of an optimistic action is at most
`4 R² min 1 ‖x‖²_{V⁻¹}`, for the features `x` of that action, when the gaps are at most `G`, the
radius is at most `R` and `G ≤ 2 R`. -/
private lemma sq_iSup_inner_sub_inner_le (hlam : 0 < lam) (hG : G ≤ 2 * R) {t : ℕ}
    (hrR : r t ≤ R) (hgap : ∀ a, ⟪θ, f t a⟫_ℝ - ⟪θ, f t (b t)⟫_ℝ ≤ G)
    (hθ : √⟪ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ,
      designOp (lam • 1) (fun s ↦ f s (b s)) t (ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ)⟫_ℝ ≤
        r t)
    (hopt : ∀ a, ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t a) ≤
      ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t (b t))) :
    ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ^ 2 ≤ 4 * R ^ 2 *
        min 1 ⟪f t (b t),
          Ring.inverse (designOp (lam • 1) (fun s ↦ f s (b s)) t) (f t (b t))⟫_ℝ := by
  have : Nonempty 𝓐 := ⟨b t⟩
  set u := ⟪f t (b t), Ring.inverse (designOp (lam • 1) (fun s ↦ f s (b s)) t) (f t (b t))⟫_ℝ
  have hu : 0 ≤ u := (isPositive_designOp_smul_one hlam.le _ t).ringInverse.inner_nonneg_right _
  have h0 := sub_nonneg.2 (le_ciSup (bddAbove_range_inner_of_gap hgap) (b t))
  have h1 := (iSup_inner_sub_inner_le_of_gap hgap).trans hG
  have h2 : (⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ ≤ 2 * R * √u := by
    refine sub_le_iff_le_add.2 (ciSup_le fun a ↦ ?_)
    have h := inner_sub_inner_le_of_ofulIndex_le (f := f t) hlam hθ hopt a
    nlinarith [Real.sqrt_nonneg u]
  rcases le_total u 1 with hu1 | hu1
  · rw [min_eq_right hu1]
    calc ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ^ 2 ≤ (2 * R * √u) ^ 2 :=
          pow_le_pow_left₀ h0 h2 2
      _ = 4 * R ^ 2 * u := by rw [mul_pow, Real.sq_sqrt hu]; ring
  · rw [min_eq_left hu1]
    calc ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * R ^ 2 * 1 := by ring

/-- **Regret of optimistic actions** [LS, Theorem 19.2], pathwise form. At every round `t < n` the
actions have features `f t a`, the action `b t` is played and the response `y t` observed. Let
`V_t` and `θ̂_t` be the design operator and the ridge estimate of the features `f s (b s)` and the
responses `y s` of the rounds `s < t`, with `λ > 0`. Suppose that at every round `t < n` the
gaps between the expected rewards `⟪θ, f t a⟫` are at most `G`, the parameter `θ` lies in the
confidence ellipsoid `‖θ̂_t - θ‖_{V_t} ≤ r t`, and `b t` has maximal optimistic index with radius
`r t`. If `r t ≤ R` for `t < n` and `G ≤ 2 R`, then the regret is
`∑_{t < n} (sup_a ⟪θ, f t a⟫ - ⟪θ, f t (b t)⟫) ≤ √(8 n R² log (det V_n / λ ^ d))`, where `d` is
the dimension of `E`. -/
theorem sum_iSup_inner_sub_inner_le_sqrt_log_det (hlam : 0 < lam) (hG : G ≤ 2 * R)
    (hrR : ∀ t < n, r t ≤ R) (hgap : ∀ t < n, ∀ a, ⟪θ, f t a⟫_ℝ - ⟪θ, f t (b t)⟫_ℝ ≤ G)
    (hθ : ∀ t < n, √⟪ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ,
      designOp (lam • 1) (fun s ↦ f s (b s)) t (ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ)⟫_ℝ ≤
        r t)
    (hopt : ∀ t < n, ∀ a, ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t a) ≤
      ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t (b t))) :
    ∑ t ∈ range n, ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ≤
      √(8 * n * R ^ 2 * log (LinearMap.det (designOp (lam • 1) (fun s ↦ f s (b s)) n : E →ₗ[ℝ] E) /
        lam ^ finrank ℝ E)) := by
  have hg (t : ℕ) (ht : t ∈ range n) := sq_iSup_inner_sub_inner_le hlam hG
    (hrR t (mem_range.1 ht)) (hgap t (mem_range.1 ht)) (hθ t (mem_range.1 ht))
    (hopt t (mem_range.1 ht))
  have hpot := sum_min_one_inner_inverse_designOp_le_log_det
    (ContinuousLinearMap.isPositive_smul_one hlam.le)
    (ContinuousLinearMap.isUnit_smul_one hlam.ne') (fun s ↦ f s (b s)) n
  rw [ContinuousLinearMap.det_smul_one] at hpot
  -- Cauchy–Schwarz, the bound on the squared instantaneous regrets, and the elliptical potential
  have hsq : (∑ t ∈ range n, ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ)) ^ 2 ≤
      8 * n * R ^ 2 * log (LinearMap.det (designOp (lam • 1) (fun s ↦ f s (b s)) n : E →ₗ[ℝ] E) /
        lam ^ finrank ℝ E) := by
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    rw [card_range]
    calc (n : ℝ) * ∑ t ∈ range n, ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ^ 2
        ≤ n * ∑ t ∈ range n, 4 * R ^ 2 * min 1
            ⟪f t (b t), Ring.inverse (designOp (lam • 1) (fun s ↦ f s (b s)) t) (f t (b t))⟫_ℝ := by
          gcongr with t ht
          exact hg t ht
      _ ≤ n * (4 * R ^ 2 * (2 * log
            (LinearMap.det (designOp (lam • 1) (fun s ↦ f s (b s)) n : E →ₗ[ℝ] E) /
              lam ^ finrank ℝ E))) := by
          rw [← mul_sum]
          gcongr
      _ = _ := by ring
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- **Regret of optimistic actions with bounded features** [LS, Theorem 19.2], pathwise form:
under the assumptions of `sum_iSup_inner_sub_inner_le_sqrt_log_det`, if moreover the features of
the played actions satisfy `‖f t (b t)‖ ≤ L` for `t < n`, then the regret is at most
`√(8 n R² d log (1 + n L² / (λ d)))`, where `d` is the dimension of `E`. -/
theorem sum_iSup_inner_sub_inner_le_sqrt_mul_log (hlam : 0 < lam) (hG : G ≤ 2 * R)
    (hrR : ∀ t < n, r t ≤ R) (hgap : ∀ t < n, ∀ a, ⟪θ, f t a⟫_ℝ - ⟪θ, f t (b t)⟫_ℝ ≤ G)
    {L : ℝ} (hL : ∀ t < n, ‖f t (b t)‖ ≤ L)
    (hθ : ∀ t < n, √⟪ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ,
      designOp (lam • 1) (fun s ↦ f s (b s)) t (ridgeEstimate lam (fun s ↦ f s (b s)) y t - θ)⟫_ℝ ≤
        r t)
    (hopt : ∀ t < n, ∀ a, ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t a) ≤
      ofulIndex lam (fun s ↦ f s (b s)) y (r t) t (f t (b t))) :
    ∑ t ∈ range n, ((⨆ a, ⟪θ, f t a⟫_ℝ) - ⟪θ, f t (b t)⟫_ℝ) ≤
      √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E)))) := by
  refine (sum_iSup_inner_sub_inner_le_sqrt_log_det hlam hG hrR hgap hθ hopt).trans ?_
  gcongr
  exact log_det_designOp_div_pow_le hlam _ hL

end Pathwise

section Algorithm

variable [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]

/-- An **optimistic selection** for the features `φ`, the regularization `λ` and the radii `r`: a
measurable choice, at every round `n`, from the history `h` and the context `o`, of an action
with maximal optimistic index `ofulIndex λ x y (r n) n (φ o ·)` for the features `x` and the
rewards `y` of the rounds of `h`. -/
@[ext]
structure OptimisticSelection (φ : 𝓞 → 𝓐 → E) (lam : ℝ) (r : ℕ → ℝ) where
  /-- The action chosen at round `n` from the history and the context. -/
  sel : (n : ℕ) → Hist 𝓞 𝓐 ℝ n × 𝓞 → 𝓐
  measurable_sel : ∀ n, Measurable (sel n)
  ofulIndex_le_ofulIndex_sel : ∀ n (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐),
    ofulIndex lam (histFeature φ h) (histReward h) (r n) n (φ o a) ≤
      ofulIndex lam (histFeature φ h) (histReward h) (r n) n (φ o (sel n (h, o)))

variable {r : ℕ → ℝ} {S : OptimisticSelection φ lam r}

/-- The **OFUL algorithm** [LS, §19.3] of an optimistic selection `S`: the deterministic algorithm
playing at round `n` the action `S.sel n (h, o)` of maximal optimistic index, for the history `h`
and the context `o`. -/
noncomputable def oful (S : OptimisticSelection φ lam r) : Algorithm 𝓞 𝓐 ℝ :=
  Algorithm.deterministic S.sel S.measurable_sel

lemma oful_eq_deterministic : oful S = Algorithm.deterministic S.sel S.measurable_sel :=
  (rfl)

@[simp]
lemma oful_policy (n : ℕ) :
    (oful S).policy n = Kernel.deterministic (S.sel n) (S.measurable_sel n) := by
  rw [oful_eq_deterministic, Algorithm.deterministic_policy]

instance : (oful S).IsDeterministic where
  exists_nextAction n := ⟨_, _, oful_policy n⟩

/-- The **optimistic selection for finitely many actions**: at every round, the action of maximal
optimistic index, ties being broken by LML's `argmax`. For finitely many actions, it makes `oful`
an algorithm with no parameter beyond the features, the regularization and the radii. -/
noncomputable def OptimisticSelection.ofFintype [Fintype 𝓐] [Nonempty 𝓐] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (φ : 𝓞 → 𝓐 → E) (hφ : Measurable (Function.uncurry φ))
    (lam : ℝ) (r : ℕ → ℝ) : OptimisticSelection φ lam r where
  sel n x := argmax fun a ↦ ofulIndex lam (histFeature φ x.1) (histReward x.1) (r n) n (φ x.2 a)
  measurable_sel n := measurable_argmax.comp <| Measurable.of_eval fun _ ↦
    ((measurable_histFeature hφ n).comp measurable_fst).ofulIndex
      ((measurable_histReward n).comp measurable_fst) (hφ.comp (measurable_snd.prodMk
        measurable_const)) lam (r n) n
  ofulIndex_le_ofulIndex_sel n h o a :=
    isMaxOn_argmax (fun b ↦ ofulIndex lam (histFeature φ h) (histReward h) (r n) n (φ o b))
      (Set.mem_univ a)

@[simp]
lemma OptimisticSelection.ofFintype_sel [Fintype 𝓐] [Nonempty 𝓐] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {hφ : Measurable (Function.uncurry φ)} (n : ℕ)
    (x : Hist 𝓞 𝓐 ℝ n × 𝓞) :
    (OptimisticSelection.ofFintype φ hφ lam r).sel n x =
      argmax fun a ↦ ofulIndex lam (histFeature φ x.1) (histReward x.1) (r n) n (φ x.2 a) := by
  rfl

namespace OFUL

variable {env : Environment 𝓞 𝓐 ℝ} {P : Measure Ω} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → ℝ}

/-- The run lemma of OFUL: along a run, the action of round `n` is almost surely the action
`S.sel n (h, o)` chosen from the history `h` and the context `o` of that round. -/
lemma action_ae_all_eq [MeasurableEq 𝓐] [SFinite P] (h : IsAlgEnvSeq O A Y (oful S) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = S.sel n (history O A Y n ω, O n ω) := by
  rw [oful_eq_deterministic] at h
  exact h.action_ae_all_eq_deterministic

/-- Along a run of OFUL, the action played at round `n` has maximal optimistic index with radius
`r n`, for the features `φ (O s) (A s)` and the rewards `Y s` of the rounds `s < n`. -/
theorem ofulIndex_le_ofulIndex_action [MeasurableEq 𝓐] [SFinite P]
    (h : IsAlgEnvSeq O A Y (oful S) env P) :
    ∀ᵐ ω ∂P, ∀ n a,
      ofulIndex lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) (r n) n (φ (O n ω) a) ≤
        ofulIndex lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) (r n) n
          (φ (O n ω) (A n ω)) := by
  filter_upwards [action_ae_all_eq h] with ω hω n a
  have hcongr : ofulIndex lam (histFeature φ (history O A Y n ω))
      (histReward (history O A Y n ω)) (r n) n =
      ofulIndex lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) (r n) n :=
    ofulIndex_congr (fun s hs ↦ histFeature_history hs ω) (fun s hs ↦ histReward_history hs ω)
  rw [← hcongr, hω n]
  exact S.ofulIndex_le_ofulIndex_sel n _ _ a

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [MeasurableEq 𝓐] {σ2 : ℝ≥0} {δ L m G R : ℝ} {n : ℕ}

omit [StandardBorelSpace Ω] [MeasurableSpace E] [BorelSpace E] in
/-- Along a run of OFUL, almost surely, if `θ` lies in all the confidence ellipsoids of ridge
regression for bounded features of [LS, Theorem 20.5 and (20.9)], then the random regret after
`n` rounds is at most `√(8 n R² d log (1 + n L² / (λ d)))`, for radii `r t` above the radii
[LS, (19.8)]. -/
private lemma ae_linearRegret_le (h : IsAlgEnvSeq O A Y (oful S) env P)
    (hgap : ∀ o a b, ⟪θ, φ o a⟫_ℝ - ⟪θ, φ o b⟫_ℝ ≤ G) (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hθ : ‖θ‖ ≤ m)
    (hr : ∀ t < n, √lam * m + √(2 * σ2 * log (1 / δ) +
      σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤ r t)
    (hG : G ≤ 2 * R) (hrR : ∀ t < n, r t ≤ R) :
    ∀ᵐ ω ∂P, (∀ t : ℕ,
      √⟪ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ,
        designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t
          (ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ)⟫_ℝ <
      √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E)))) →
      linearRegret φ θ O A n ω ≤
        √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E)))) := by
  filter_upwards [ofulIndex_le_ofulIndex_action h] with ω hω hgood
  rw [linearRegret_def]
  refine sum_iSup_inner_sub_inner_le_sqrt_mul_log (f := fun t ↦ φ (O t ω)) hlam hG hrR
    (fun t _ a ↦ hgap _ a _) (fun t _ ↦ hL _ _) (fun t ht ↦ (hgood t).le.trans ?_)
    (fun t _ ↦ hω t)
  refine le_trans ?_ (hr t ht)
  gcongr

/-- **Regret of OFUL with high probability** [LS, Theorem 19.2]. Let `oful S` run in a linear
bandit environment with features `φ`, parameter `θ` and σ²-sub-Gaussian noise, `σ² ≠ 0`, where
the features are measurable and bounded by `L`, `‖θ‖ ≤ m`, and the gaps between the expected
rewards of two actions are at most `G` at every context. Let `λ > 0` and `δ > 0`, and let the
radii of the optimistic selection satisfy
`√λ m + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d))) ≤ r t ≤ R` for `t < n`, with
`G ≤ 2 R`. Then with probability at least `1 - δ`, the random regret after `n` rounds is at most
`√(8 n R² d log (1 + n L² / (λ d)))`. -/
theorem le_measureReal_linearRegret_le (h : IsAlgEnvSeq O A Y (oful S) env P)
    (henv : IsSubgaussianLinearEnv φ θ σ2 env) (hφ : Measurable (Function.uncurry φ))
    (hσ : σ2 ≠ 0) (hgap : ∀ o a b, ⟪θ, φ o a⟫_ℝ - ⟪θ, φ o b⟫_ℝ ≤ G) (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) (hθ : ‖θ‖ ≤ m)
    (hr : ∀ t < n, √lam * m + √(2 * σ2 * log (1 / δ) +
      σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤ r t)
    (hG : G ≤ 2 * R) (hrR : ∀ t < n, r t ≤ R) :
    1 - δ ≤ P.real {ω | linearRegret φ θ O A n ω ≤
      √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E))))} := by
  refine (h.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le henv hφ hσ hL hlam
    hδ).trans ?_
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_linearRegret_le h hgap hL hlam hθ hr hG hrR] with ω hω hgood
  exact hω hgood

/-- **Expected regret of OFUL** [LS, Corollary 19.3, with explicit constants]: under the
assumptions of `le_measureReal_linearRegret_le`, the expected regret after `n` rounds is at most
`n G δ + √(8 n R² d log (1 + n L² / (λ d)))`. -/
theorem integral_linearRegret_le (h : IsAlgEnvSeq O A Y (oful S) env P)
    (henv : IsSubgaussianLinearEnv φ θ σ2 env) (hφ : Measurable (Function.uncurry φ))
    (hσ : σ2 ≠ 0) (hgap : ∀ o a b, ⟪θ, φ o a⟫_ℝ - ⟪θ, φ o b⟫_ℝ ≤ G) (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) (hθ : ‖θ‖ ≤ m)
    (hr : ∀ t < n, √lam * m + √(2 * σ2 * log (1 / δ) +
      σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤ r t)
    (hG : G ≤ 2 * R) (hrR : ∀ t < n, r t ≤ R) :
    P[linearRegret φ θ O A n] ≤
      n * G * δ + √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E)))) := by
  set B := √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E))))
  -- the event on which some confidence ellipsoid fails to contain `θ`
  set bad := {ω | ∃ t : ℕ, √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
      σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤
    √⟪ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ,
      designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t
        (ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ)⟫_ℝ}
  have hbad : P bad ≤ ENNReal.ofReal δ :=
    h.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le_of_norm_le henv hφ hσ hL hlam hδ
  have hG0 : 0 ≤ G := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact nonneg_of_gap (hgap (O 0 ω) · (A 0 ω))
  -- the regret is at most `B` outside `bad`, and at most `n G` everywhere
  have hle : ∀ᵐ ω ∂P,
      linearRegret φ θ O A n ω ≤ B + n * G * (toMeasurable P bad).indicator 1 ω := by
    filter_upwards [ae_linearRegret_le h hgap hL hlam hθ hr hG hrR] with ω hω
    by_cases hω' : ω ∈ bad
    · rw [Set.indicator_of_mem (subset_toMeasurable P bad hω'), Pi.one_apply, mul_one]
      exact (linearRegret_le_mul hgap).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    · refine (hω fun t ↦ ?_).trans (le_add_of_nonneg_right ?_)
      · simp only [bad, Set.mem_ofPred_eq, not_exists, not_le] at hω'
        exact hω' t
      · exact mul_nonneg (mul_nonneg n.cast_nonneg hG0)
          (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hint : Integrable (fun ω ↦ (n : ℝ) * G * (toMeasurable P bad).indicator 1 ω) P :=
    ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable P bad)).const_mul _
  have hnonneg : 0 ≤ᵐ[P] linearRegret φ θ O A n := ae_of_all _ fun ω ↦
    linearRegret_nonneg fun o ↦ bddAbove_range_inner_of_gap (hgap o · (A 0 ω))
  calc P[linearRegret φ θ O A n]
      ≤ ∫ ω, B + n * G * (toMeasurable P bad).indicator 1 ω ∂P :=
        integral_mono_of_nonneg hnonneg ((integrable_const B).add hint) hle
    _ = B + n * G * P.real (toMeasurable P bad) := by
        rw [integral_add (integrable_const B) hint, integral_const_mul,
          integral_indicator_one (measurableSet_toMeasurable P bad)]
        simp
    _ ≤ B + n * G * δ := by
        gcongr
        rw [measureReal_def, measure_toMeasurable]
        exact ENNReal.toReal_le_of_le_ofReal hδ.le hbad
    _ = n * G * δ + B := add_comm _ _

/-- **Expected regret of OFUL for `δ = 1 / n`** [LS, Corollary 19.3, with explicit constants]:
under the assumptions of `integral_linearRegret_le` with `δ = 1 / n`, that is for radii
`√λ m + √(2σ² log n + σ² d log (1 + t L² / (λ d))) ≤ r t ≤ R` for `t < n`, the expected regret
after `n` rounds is at most `G + √(8 n R² d log (1 + n L² / (λ d)))`. -/
theorem integral_linearRegret_le_add_sqrt (h : IsAlgEnvSeq O A Y (oful S) env P)
    (henv : IsSubgaussianLinearEnv φ θ σ2 env) (hφ : Measurable (Function.uncurry φ))
    (hσ : σ2 ≠ 0) (hgap : ∀ o a b, ⟪θ, φ o a⟫_ℝ - ⟪θ, φ o b⟫_ℝ ≤ G) (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hθ : ‖θ‖ ≤ m)
    (hr : ∀ t < n, √lam * m + √(2 * σ2 * log n +
      σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤ r t)
    (hG : G ≤ 2 * R) (hrR : ∀ t < n, r t ≤ R) :
    P[linearRegret φ θ O A n] ≤
      G + √(8 * n * R ^ 2 * (finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E)))) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    simpa using nonneg_of_gap (hgap (O 0 ω) · (A 0 ω))
  have := integral_linearRegret_le (δ := 1 / n) h henv hφ hσ hgap hL hlam (by positivity) hθ
    (by simpa only [one_div_one_div] using hr) hG hrR
  have hnG : (n : ℝ) * G * (1 / n) = G := by field_simp
  linarith

end OFUL

end Algorithm

section Bandit

/-! ### Finitely many arms

A stochastic bandit with finitely many σ²-sub-Gaussian arms is a linear bandit with the one-hot
features `a ↦ EuclideanSpace.single a 1` in dimension `k`, the number of arms
(`isSubgaussianLinearEnv_bandit`), so the regret bound of OFUL applies to it. -/

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {r : ℕ → ℝ}
  {S : OptimisticSelection (fun (_ : Unit) (a : α) ↦ EuclideanSpace.single a (1 : ℝ)) lam r}
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit}
  {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {σ2 : ℝ≥0} {m G R : ℝ} {n : ℕ}

/-- **Expected regret of OFUL on finitely many arms** [LS, Corollary 19.3, with explicit
constants]: let OFUL with the one-hot features run on a stochastic bandit `ν` with `k` arms that
are σ²-sub-Gaussian, `σ² ≠ 0`, whose gaps are at most `G` and whose vector of means has
Euclidean norm at most `m`. Let `λ > 0` and let the radii satisfy
`√λ m + √(2σ² log n + σ² k log (1 + t / (λ k))) ≤ r t ≤ R` for `t < n`, with `G ≤ 2 R`. Then the
expected regret after `n` rounds is at most `G + √(8 n R² k log (1 + n / (λ k)))`. -/
theorem OFUL.integral_regret_le_add_sqrt
    (h : IsAlgEnvSeq O A Y (oful S) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ : σ2 ≠ 0)
    (hgap : ∀ a, gap ν a ≤ G) (hlam : 0 < lam) (hm : √(∑ a, (ν a)[id] ^ 2) ≤ m)
    (hr : ∀ t < n, √lam * m + √(2 * σ2 * log n +
      σ2 * Fintype.card α * log (1 + t / (lam * Fintype.card α))) ≤ r t)
    (hG : G ≤ 2 * R) (hrR : ∀ t < n, r t ≤ R) :
    P[regret ν A n] ≤
      G + √(8 * n * R ^ 2 * (Fintype.card α * log (1 + n / (lam * Fintype.card α)))) := by
  have hφ : Measurable (Function.uncurry fun (_ : Unit) (a : α) ↦
      EuclideanSpace.single a (1 : ℝ)) := measurable_of_countable _
  have hgap' (o : Unit) (a b : α) : ⟪WithLp.toLp 2 (fun a ↦ (ν a)[id]),
      EuclideanSpace.single a (1 : ℝ)⟫_ℝ - ⟪WithLp.toLp 2 (fun a ↦ (ν a)[id]),
        EuclideanSpace.single b (1 : ℝ)⟫_ℝ ≤ G := by
    have : Nonempty α := ⟨a⟩
    simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
    linarith [hgap b, gap_eq_bestArm_sub (ν := ν) (a := b), le_bestArm (ν := ν) a]
  have key := OFUL.integral_linearRegret_le_add_sqrt (L := 1) h (isSubgaussianLinearEnv_bandit hν)
    hφ hσ hgap' (fun _ a ↦ by simp) hlam (by simpa [EuclideanSpace.norm_eq] using hm)
    (by simpa [finrank_euclideanSpace] using hr) hG hrR
  simp_rw [linearRegret_single_eq_regret] at key
  simpa [finrank_euclideanSpace] using key

end Bandit

end LMLExplore.Bandits
