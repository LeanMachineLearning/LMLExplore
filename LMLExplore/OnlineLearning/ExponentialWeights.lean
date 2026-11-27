/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.OnlineLearning.GibbsMixture
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Exponential weights

The softmax of a vector `v : α → ℝ` over a finite set `α`, also called its exponential weights, is
the probability vector `softmax v = a ↦ exp (v a) / ∑ b, exp (v b)`. Exponential weights with
learning rate `η > 0` and losses `y 0, y 1, …` play at round `t` the vector
`p t = softmax (-(η • ∑ s < t, y s))`, which puts more mass on the coordinates with small
cumulative loss. For rewards `r t = 1 - y t` (more generally `r t = c t - y t` with constants
`c t`), the softmax of `η` times the cumulative rewards is the same vector, since adding a constant
to every coordinate of `v` does not change `softmax v`.

The analysis of exponential weights rests on the *mix loss*
`mixLoss η w ℓ = -(1/η) log ∑ a, w a exp (-η ℓ a)` of a loss vector `ℓ` under weights `w`, and on
the potential `hedgePotential η L = -(1/η) log ((1/k) ∑ a, exp (-η L a))` of a cumulative loss
vector `L`, with `k` the cardinality of `α`. The mix loss of the weights `softmax (-(η • L))` is the
increment of the potential from `L` to `L + ℓ`, and the potential is nonincreasing in `η`, so for
nonincreasing learning rates `η t` the mix losses of the weights
`p t = softmax (-(η t • ∑ s < t, y s))` telescope: their sum is at most the potential at the last
learning rate, which is at most the cumulative loss of every coordinate plus `log k / η (n - 1)`
[dRvEGK14, Section 2]. These facts are the case of the prior `∑ a, w a • δ_a` and the temperature
`η⁻¹` of the Gibbs mixtures of `LMLExplore.OnlineLearning.GibbsMixture`, from which they are
derived: the mix loss is `MeasureTheory.Measure.mixLoss` of that prior
(`mixLoss_eq_mixLoss_weightedMeasure`), and the exponential weights are the Gibbs measure of the
uniform prior (`weightedMeasure_softmax`). The regret is therefore at most
`log k / η (n - 1)` plus the sum of the *mixability gaps* `⟨p t, y t⟩ - mixLoss (η t) (p t) (y t)`,
with `⟨p, y⟩ = ∑ b, p b * y b`. Since
`log x ≤ x - 1`, the mixability gap is at most `(∑ b, p b * (exp (-(η * y b)) - 1 + η * y b)) / η`.

For nonnegative losses this gives the local-norm bound
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η (n - 1) + ∑ t < n, η t / 2 * ⟨p t, (y t) ^ 2⟩`
against every coordinate `a`. The second-order terms are averages under the played weights, rather
than squared sup norms of the losses: this is what makes the bound useful for the unbounded but
nonnegative importance-weighted loss estimates of Exp3 [LS, Section 11.3]. For losses that may be
negative but satisfy `η t * y t a ≥ -1`, such as the loss estimates of adversarial linear bandits,
`exp (-x) ≤ 1 - x + x ^ 2` for `x ≥ -1` gives the same bound with `η t * ⟨p t, (y t) ^ 2⟩` in place
of `η t / 2 * ⟨p t, (y t) ^ 2⟩` [LS, proof of Theorem 27.1]. The same mix losses and potential give
the regret bound of AdaHedge (`LMLExplore.OnlineLearning.AdaHedge`), and the mixability gap at `p`
is the maximum over the simplex of the stability term of follow the regularized leader with the
negative entropy at `p`, by the Gibbs variational principle
(`isGreatest_sum_sub_mul_sub_sum_mul_log_div_div` in `LMLExplore.OnlineLearning.Simplex`).

## Main definitions

* `LMLExplore.OnlineLearning.softmax v`: the softmax (exponential weights) of `v`.
* `LMLExplore.OnlineLearning.mixLoss η w ℓ`: the mix loss `-(1/η) log ∑ a, w a exp (-η ℓ a)`.
* `LMLExplore.OnlineLearning.hedgePotential η L`: the potential
  `-(1/η) log ((1/k) ∑ a, exp (-η L a))` of exponential weights.

## Main statements

* `softmax_mem_simplex`, `softmax_pos`: on a nonempty finite type, the softmax is a probability
  vector with positive entries.
* `softmax_add_const`: adding a constant to every coordinate does not change the softmax.
* `softmax_log_add_apply`, `softmax_log_softmax_add`: the softmax of `log w + v` is the
  multiplicative update `a ↦ w a * exp (v a)` normalized, and a multiplicative update of a softmax
  is a softmax; `softmax_add_apply`: the softmax of `v + u` is the update of `softmax v` by
  `exp u`.
* `measurable_softmax`: `v ↦ softmax v` is measurable.
* `sum_mul_exp_neg_sub_one_add_le`: for nonnegative weights `p`, a nonnegative loss `y` and
  `η ≥ 0`, `∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2`.
* `sum_mul_exp_neg_sub_one_add_le_of_neg_one_le`: for nonnegative weights `p` and a loss `y` with
  `η * y b ≥ -1`, `∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2`.
* `mixLoss_eq_mixLoss_weightedMeasure`: the mix loss of weights `w ≥ 0` is the mix loss of the
  prior `weightedMeasure w` at the temperature `η⁻¹`.
* `hedgePotential_eq_mixLoss_weightedMeasure`: the potential is the mix loss of the uniform prior
  at the temperature `η⁻¹`.
* `weightedMeasure_softmax`: the exponential weights `softmax (-(η • L))` are the Gibbs measure of
  `L` under the uniform prior at the temperature `η⁻¹`.
* `mixLoss_le_sum_mul`, `le_mixLoss`: the mix loss lies between the smallest loss and `⟨w, ℓ⟩`.
* `mixLoss_softmax`: the mix loss of exponential weights is the increment of the potential.
* `hedgePotential_le_of_le`: the potential is nonincreasing in the learning rate.
* `hedgePotential_le_sum_mul`: the potential is at most `⟨u, L⟩ + log k / η` for every probability
  vector `u`.
* `sum_mul_sub_mixLoss_le`: the mixability gap is at most
  `(∑ b, p b * (exp (-(η * y b)) - 1 + η * y b)) / η`.
* `add_mixLoss_softmax_le_hedgePotential`: one step of the telescoping of the mix losses.
* `sum_mixLoss_softmax_le_of_antitone`: with nonincreasing learning rates, the total mix loss of
  exponential weights is at most the potential at the last learning rate.
* `softmax_regret_le_sum_sub_mixLoss_of_antitone`: the regret of exponential weights with
  nonincreasing learning rates is at most `log k / η (n - 1)` plus the sum of the mixability gaps.
* `softmax_regret_le_sum_exp_of_antitone`: the same bound through the stability terms
  `(∑ b, p b * (exp (-(η * y b)) - 1 + η * y b)) / η`.
* `softmax_regret_le_of_antitone`: the local-norm regret bound for nonnegative losses, and
  `softmax_regret_le` its case of a constant learning rate.
* `softmax_regret_le_of_antitone_of_neg_one_le`, `softmax_regret_le_of_neg_one_le`: the local-norm
  bound `∑ t < n, η t * ⟨p t, (y t) ^ 2⟩` for losses with `η t * y t a ≥ -1`.

## Implementation notes

The lemmas `softmax_log_add_apply` and `softmax_log_softmax_add` are adapted from the
formalization of [SSKM26] in the paper project `RemyDegenne/Schlisselberg2026Hidden`
(same author).

## References

* [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
* [dRvEGK14] S. de Rooij, T. van Erven, P. D. Grünwald and W. M. Koolen, *Follow the leader if you
  can, hedge if you must*, JMLR 15 (2014), Section 2.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

open Finset Real MeasureTheory

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

/-- The **softmax** of `v : α → ℝ`, also called its exponential weights: the probability vector
`a ↦ exp (v a) / ∑ b, exp (v b)`. -/
noncomputable def softmax (v : α → ℝ) : α → ℝ := fun a ↦ exp (v a) / ∑ b, exp (v b)

lemma softmax_apply (v : α → ℝ) (a : α) :
    softmax v a = exp (v a) / ∑ b, exp (v b) := (rfl)

lemma softmax_pos [Nonempty α] (v : α → ℝ) (a : α) : 0 < softmax v a :=
  div_pos (exp_pos _) (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty)

lemma softmax_nonneg (v : α → ℝ) (a : α) : 0 ≤ softmax v a :=
  div_nonneg (exp_pos _).le (Finset.sum_nonneg fun b _ ↦ (exp_pos (v b)).le)

@[simp]
lemma sum_softmax [Nonempty α] (v : α → ℝ) : ∑ a, softmax v a = 1 := by
  simp_rw [softmax_apply, ← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty).ne'

lemma softmax_mem_simplex [Nonempty α] (v : α → ℝ) : softmax v ∈ simplex α :=
  mem_simplex_iff.2 ⟨softmax_nonneg v, sum_softmax v⟩

/-- Adding a constant `c` to every coordinate of `v` does not change its softmax. -/
@[simp]
lemma softmax_add_const (v : α → ℝ) (c : ℝ) :
    softmax (fun a ↦ v a + c) = softmax v := by
  funext a
  simp_rw [softmax_apply, exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (exp_pos c).ne'

/-- The softmax of the zero vector is uniform. -/
@[simp]
lemma softmax_zero : softmax (0 : α → ℝ) = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  funext a
  simp [softmax_apply]

/-- The softmax of `log w + v`, for `w` with positive coordinates, is the multiplicative update
of `w` by `exp v`: the vector `a ↦ w a * exp (v a)` normalized. -/
lemma softmax_log_add_apply {w : α → ℝ} (hw : ∀ a, 0 < w a) (v : α → ℝ) (a : α) :
    softmax (fun a ↦ log (w a) + v a) a = w a * exp (v a) / ∑ b, w b * exp (v b) := by
  simp only [softmax_apply, exp_add, exp_log (hw _)]

/-- A multiplicative update of a softmax is a softmax:
`softmax (log (softmax v) + u) = softmax (v + u)`. -/
lemma softmax_log_softmax_add [Nonempty α] (v u : α → ℝ) :
    softmax (fun a ↦ log (softmax v a) + u a) = softmax (fun a ↦ v a + u a) := by
  have hS : 0 < ∑ b, exp (v b) := sum_pos (fun b _ ↦ exp_pos _) univ_nonempty
  have h : (fun a ↦ log (softmax v a) + u a) = fun a ↦ (v a + u a) + -log (∑ b, exp (v b)) := by
    funext a
    rw [softmax_apply, log_div (exp_pos _).ne' hS.ne', log_exp]
    ring
  rw [h, softmax_add_const]

/-- The softmax of `v + u` is the multiplicative update of the softmax of `v` by `exp u`: the
vector `a ↦ softmax v a * exp (u a)` normalized. -/
lemma softmax_add_apply [Nonempty α] (v u : α → ℝ) (a : α) :
    softmax (fun b ↦ v b + u b) a = softmax v a * exp (u a) / ∑ b, softmax v b * exp (u b) := by
  rw [← softmax_log_softmax_add, softmax_log_add_apply (softmax_pos v)]

@[fun_prop]
lemma measurable_softmax : Measurable (softmax (α := α)) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [softmax_apply]
  exact (Real.measurable_exp.comp (measurable_pi_apply a)).div
    (Finset.measurable_sum _ fun b _ ↦ Real.measurable_exp.comp (measurable_pi_apply b))

/-- **Second-order bound under exponential weights.** For nonnegative weights `p`, a nonnegative
loss `y` and a learning rate `η ≥ 0`,
`∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2`, from
`exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`. This bounds the stability terms of exponential weights
by local norms [Ora, Section 7.5]. -/
theorem sum_mul_exp_neg_sub_one_add_le {p y : α → ℝ} (hp : ∀ b, 0 ≤ p b) (hy : ∀ b, 0 ≤ y b)
    {η : ℝ} (hη : 0 ≤ η) :
    ∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  have h := exp_le_one_add_add_sq_div_two_of_nonpos (neg_nonpos.2 (mul_nonneg hη (hy b)))
  calc p b * (exp (-(η * y b)) - 1 + η * y b)
  _ ≤ p b * (η ^ 2 / 2 * y b ^ 2) := mul_le_mul_of_nonneg_left (by linarith) (hp b)
  _ = η ^ 2 / 2 * (p b * y b ^ 2) := by ring

/-- **Second-order bound under exponential weights, for losses bounded below.** For nonnegative
weights `p`, a learning rate `η` and a loss `y` with `η * y b ≥ -1` for every `b`,
`∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2`, from
`exp (-x) ≤ 1 - x + x ^ 2` for `x ≥ -1` [LS, proof of Theorem 27.1]. -/
theorem sum_mul_exp_neg_sub_one_add_le_of_neg_one_le {p y : α → ℝ} (hp : ∀ b, 0 ≤ p b) {η : ℝ}
    (hy : ∀ b, -1 ≤ η * y b) :
    ∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  have h := exp_neg_le_one_sub_add_sq (hy b)
  calc p b * (exp (-(η * y b)) - 1 + η * y b)
  _ ≤ p b * (η ^ 2 * y b ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) (hp b)
  _ = η ^ 2 * (p b * y b ^ 2) := by ring

/-! ### The mix loss and the potential of exponential weights -/

/-- Multiplying an inequality by `-η⁻¹` for `0 < η`: `-η⁻¹ X ≤ c ↔ -η c ≤ X`. -/
private lemma neg_inv_mul_le_iff {η : ℝ} (hη : 0 < η) {X c : ℝ} :
    -η⁻¹ * X ≤ c ↔ -η * c ≤ X := by
  rw [neg_mul, neg_le, inv_mul_eq_div, le_div_iff₀ hη, neg_mul, mul_comm, neg_mul]

/-- Multiplying an inequality by `-η⁻¹` for `0 < η`: `c ≤ -η⁻¹ X ↔ X ≤ -η c`. -/
private lemma le_neg_inv_mul_iff {η : ℝ} (hη : 0 < η) {X c : ℝ} :
    c ≤ -η⁻¹ * X ↔ X ≤ -η * c := by
  rw [neg_mul, le_neg, inv_mul_eq_div, div_le_iff₀ hη, neg_mul, mul_comm, neg_mul]

/-- The **mix loss** `-(1/η) log ∑ a, w a exp (-η ℓ a)` of the loss vector `ℓ` under the weights
`w`, at the learning rate `η`. -/
noncomputable def mixLoss (η : ℝ) (w ℓ : α → ℝ) : ℝ :=
  -η⁻¹ * log (∑ a, w a * exp (-η * ℓ a))

lemma mixLoss_def (η : ℝ) (w ℓ : α → ℝ) :
    mixLoss η w ℓ = -η⁻¹ * log (∑ a, w a * exp (-η * ℓ a)) := (rfl)

/-- The mix loss `-(1/η) log ∑ a, w a exp (-(η ℓ a))`, with the exponent in `simp` normal form. -/
lemma mixLoss_eq_neg_log_div (η : ℝ) (w ℓ : α → ℝ) :
    mixLoss η w ℓ = -(log (∑ a, w a * exp (-(η * ℓ a))) / η) := by
  simp_rw [mixLoss_def, neg_mul]
  ring

/-- For `0 < η`, the mix loss is at most `c` iff `-η c ≤ log ∑ a, w a exp (-η ℓ a)`. -/
lemma mixLoss_le_iff {η : ℝ} (hη : 0 < η) {w ℓ : α → ℝ} {c : ℝ} :
    mixLoss η w ℓ ≤ c ↔ -η * c ≤ log (∑ a, w a * exp (-η * ℓ a)) := by
  rw [mixLoss_def, neg_inv_mul_le_iff hη]

/-- For `0 < η`, the mix loss is at least `c` iff `log ∑ a, w a exp (-η ℓ a) ≤ -η c`. -/
lemma le_mixLoss_iff {η : ℝ} (hη : 0 < η) {w ℓ : α → ℝ} {c : ℝ} :
    c ≤ mixLoss η w ℓ ↔ log (∑ a, w a * exp (-η * ℓ a)) ≤ -η * c := by
  rw [mixLoss_def, le_neg_inv_mul_iff hη]

/-- The mix loss of nonnegative weights `w` at the learning rate `η` is the mix loss of the
prior `weightedMeasure w = ∑ a, w a • δ_a` at the temperature `η⁻¹`
(`MeasureTheory.Measure.mixLoss`). -/
lemma mixLoss_eq_mixLoss_weightedMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (η : ℝ) (ℓ : α → ℝ) :
    mixLoss η w ℓ = (weightedMeasure w).mixLoss ℓ η⁻¹ := by
  rw [mixLoss_def, Measure.mixLoss_def, integral_weightedMeasure_eq_sum hw]
  congr 3 with a
  rw [smul_eq_mul, div_inv_eq_mul, neg_mul, neg_mul, mul_comm η]

/-- The mix loss is at most the loss `⟨w, ℓ⟩` of the weights, by Jensen's inequality. -/
lemma mixLoss_le_sum_mul {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η) (ℓ : α → ℝ) :
    mixLoss η w ℓ ≤ ∑ a, w a * ℓ a := by
  let _ : MeasurableSpace α := ⊤
  have hw0 := (mem_simplex_iff.1 hw).1
  have := isProbabilityMeasure_weightedMeasure hw
  have h := Measure.mixLoss_le_integral (μ := weightedMeasure w) (L := ℓ) (inv_pos.2 hη)
    Integrable.of_finite Integrable.of_finite
  rwa [integral_weightedMeasure_eq_sum hw0, ← mixLoss_eq_mixLoss_weightedMeasure hw0] at h

/-- The mix loss of losses at least `lo` is at least `lo`. -/
lemma le_mixLoss {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η) {ℓ : α → ℝ} {lo : ℝ}
    (hℓ : ∀ a, lo ≤ ℓ a) :
    lo ≤ mixLoss η w ℓ := by
  let _ : MeasurableSpace α := ⊤
  have := isProbabilityMeasure_weightedMeasure hw
  rw [mixLoss_eq_mixLoss_weightedMeasure (mem_simplex_iff.1 hw).1]
  exact Measure.le_mixLoss (inv_pos.2 hη) Integrable.of_finite (ae_of_all _ hℓ)

/-- The potential `-(1/η) log ((1/K) ∑ a, exp (-η L a))` of exponential weights with learning rate
`η` at the cumulative loss vector `L`, with `K` the cardinality of `α`. -/
noncomputable def hedgePotential (η : ℝ) (L : α → ℝ) : ℝ :=
  -η⁻¹ * log ((∑ a, exp (-η * L a)) / Fintype.card α)

lemma hedgePotential_def (η : ℝ) (L : α → ℝ) :
    hedgePotential η L = -η⁻¹ * log ((∑ a, exp (-η * L a)) / Fintype.card α) := (rfl)

/-- The potential is the mix loss of the cumulative losses under the uniform weights. -/
lemma hedgePotential_eq_mixLoss (η : ℝ) (L : α → ℝ) :
    hedgePotential η L = mixLoss η (fun _ ↦ (Fintype.card α : ℝ)⁻¹) L := by
  simp_rw [hedgePotential_def, mixLoss_def, Finset.sum_div, div_eq_inv_mul]

/-- The potential is the mix loss of the cumulative losses under the uniform prior
`weightedMeasure fun _ ↦ 1 / K`, at the temperature `η⁻¹`. -/
lemma hedgePotential_eq_mixLoss_weightedMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (η : ℝ) (L : α → ℝ) :
    hedgePotential η L = (weightedMeasure fun _ : α ↦ (Fintype.card α : ℝ)⁻¹).mixLoss L η⁻¹ := by
  rw [hedgePotential_eq_mixLoss, mixLoss_eq_mixLoss_weightedMeasure fun _ ↦ by positivity]

/-- **Exponential weights are a Gibbs measure**: the weights `softmax (-(η • L))` are the masses of
the Gibbs measure of the cumulative losses `L` under the uniform prior, at the temperature `η⁻¹`. -/
lemma weightedMeasure_softmax [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    (η : ℝ) (L : α → ℝ) :
    weightedMeasure (softmax (-(η • L))) =
      (weightedMeasure fun _ : α ↦ (Fintype.card α : ℝ)⁻¹).gibbs L η⁻¹ := by
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hZ : 0 < ∑ b, exp (-(η * L b)) := Finset.sum_pos (fun b _ ↦ exp_pos _) univ_nonempty
  refine Measure.ext_iff_singleton.2 fun a ↦ ?_
  rw [weightedMeasure_singleton, Measure.gibbs_apply, lintegral_singleton,
    weightedMeasure_singleton, integral_weightedMeasure_eq_sum fun _ ↦ inv_nonneg.2 hK.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp_rw [softmax_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, div_inv_eq_mul, neg_mul,
    mul_comm (L _) η, ← Finset.mul_sum]
  field_simp

/-- The mix loss of the exponential weights `softmax (-(η • L))` is the increment
`Φ_η(L + ℓ) - Φ_η(L)` of the potential. -/
lemma mixLoss_softmax [Nonempty α] (η : ℝ) (L ℓ : α → ℝ) :
    mixLoss η (softmax (-(η • L))) ℓ = hedgePotential η (L + ℓ) - hedgePotential η L := by
  let _ : MeasurableSpace α := ⊤
  have := isProbabilityMeasure_weightedMeasure (uniform_mem_simplex α)
  rw [mixLoss_eq_mixLoss_weightedMeasure (softmax_nonneg _), weightedMeasure_softmax,
    Measure.mixLoss_gibbs Integrable.of_finite Integrable.of_finite,
    hedgePotential_eq_mixLoss_weightedMeasure, hedgePotential_eq_mixLoss_weightedMeasure]

/-- The potential is at most `L a + log K / η` for every expert `a`. -/
lemma hedgePotential_le {η : ℝ} (hη : 0 < η) (L : α → ℝ) (a : α) :
    hedgePotential η L ≤ L a + log (Fintype.card α) / η := by
  have : Nonempty α := ⟨a⟩
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hle : exp (-η * L a) ≤ ∑ b, exp (-η * L b) :=
    Finset.single_le_sum (f := fun b ↦ exp (-η * L b)) (fun b _ ↦ (exp_pos _).le) (mem_univ a)
  have hlog : -η * L a - log (Fintype.card α) ≤ log ((∑ b, exp (-η * L b)) / Fintype.card α) := by
    rw [log_div (Finset.sum_pos (fun b _ ↦ exp_pos _) univ_nonempty).ne' hK.ne',
      ← log_exp (-η * L a)]
    exact sub_le_sub_right (log_le_log (exp_pos _) hle) _
  rw [hedgePotential_def, neg_inv_mul_le_iff hη]
  refine le_of_eq_of_le ?_ hlog
  field_simp
  ring

/-- The potential is at least every lower bound of the cumulative losses. -/
lemma le_hedgePotential [Nonempty α] {η : ℝ} (hη : 0 < η) {L : α → ℝ} {x : ℝ}
    (hL : ∀ a, x ≤ L a) :
    x ≤ hedgePotential η L :=
  hedgePotential_eq_mixLoss η L ▸ le_mixLoss (uniform_mem_simplex α) hη hL

/-- The potential is nonincreasing in the learning rate: for `0 < η' ≤ η`,
`Φ_η(L) ≤ Φ_η'(L)`, since the mix loss is nondecreasing in the temperature `η⁻¹`
(`MeasureTheory.Measure.mixLoss_le_mixLoss_of_le`). -/
lemma hedgePotential_le_of_le [Nonempty α] {η η' : ℝ} (hη' : 0 < η') (hη : η' ≤ η)
    (L : α → ℝ) :
    hedgePotential η L ≤ hedgePotential η' L := by
  let _ : MeasurableSpace α := ⊤
  have := isProbabilityMeasure_weightedMeasure (uniform_mem_simplex α)
  rw [hedgePotential_eq_mixLoss_weightedMeasure, hedgePotential_eq_mixLoss_weightedMeasure]
  exact Measure.mixLoss_le_mixLoss_of_le (inv_pos.2 (hη'.trans_le hη)) (inv_anti₀ hη' hη)
    Integrable.of_finite

/-- The potential of the zero cumulative loss vector is zero. -/
@[simp]
lemma hedgePotential_zero_right (η : ℝ) : hedgePotential η (0 : α → ℝ) = 0 := by
  rcases isEmpty_or_nonempty α with _ | _ <;> simp [hedgePotential_def]

/-- The potential is at most `⟨u, L⟩ + log K / η` for every probability vector `u`, with `K` the
cardinality of `α`. -/
lemma hedgePotential_le_sum_mul {η : ℝ} (hη : 0 < η) (L : α → ℝ) {u : α → ℝ}
    (hu : u ∈ simplex α) :
    hedgePotential η L ≤ ∑ a, u a * L a + log (Fintype.card α) / η := by
  have := nonempty_of_mem_simplex hu
  obtain ⟨hu0, hu1⟩ := mem_simplex_iff.1 hu
  obtain ⟨a, ha⟩ := Finite.exists_min L
  have h_min : L a ≤ ∑ b, u b * L b :=
    calc L a = ∑ b, u b * L a := by rw [← sum_mul, hu1, one_mul]
    _ ≤ ∑ b, u b * L b := sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (ha b) (hu0 b)
  linarith [hedgePotential_le hη L a]

/-- **The mixability gap is at most the exponential stability term.** For a probability vector
`w`, a loss `ℓ` and a learning rate `η > 0`, the mixability gap `⟨w, ℓ⟩ - mixLoss η w ℓ` is at
most `(∑ a, w a * (exp (-(η * ℓ a)) - 1 + η * ℓ a)) / η`, since `log x ≤ x - 1`. -/
lemma sum_mul_sub_mixLoss_le {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η)
    (ℓ : α → ℝ) :
    ∑ a, w a * ℓ a - mixLoss η w ℓ ≤ (∑ a, w a * (exp (-(η * ℓ a)) - 1 + η * ℓ a)) / η := by
  have hw1 := (mem_simplex_iff.1 hw).2
  have hZ : 0 < ∑ a, w a * exp (-(η * ℓ a)) := sum_mul_pos_of_mem_simplex hw fun a ↦ exp_pos _
  have h_log := log_le_sub_one_of_pos hZ
  have h_expand : ∑ a, w a * (exp (-(η * ℓ a)) - 1 + η * ℓ a) =
      ∑ a, w a * exp (-(η * ℓ a)) - 1 + η * ∑ a, w a * ℓ a := by
    simp_rw [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, hw1, mul_sum]
    congr 1
    exact sum_congr rfl fun a _ ↦ by ring
  rw [h_expand, mixLoss_eq_neg_log_div, sub_neg_eq_add, add_div,
    mul_div_cancel_left₀ _ hη.ne', add_comm (∑ a, w a * ℓ a)]
  gcongr

/-! ### Regret of exponential weights -/

/-- **One step of the telescoping of the mix losses.** If `S` is at most the potential of `L` at a
learning rate `η'`, then adding the mix loss of the exponential weights `softmax (-(η • L))` at a
smaller learning rate `0 < η ≤ η'` keeps `S` below the potential of `L + ℓ` at `η`. -/
lemma add_mixLoss_softmax_le_hedgePotential [Nonempty α] {η η' : ℝ} (hη : 0 < η) (hηη' : η ≤ η')
    {S : ℝ} {L : α → ℝ} (hS : S ≤ hedgePotential η' L) (ℓ : α → ℝ) :
    S + mixLoss η (softmax (-(η • L))) ℓ ≤ hedgePotential η (L + ℓ) := by
  rw [mixLoss_softmax]
  linarith [hedgePotential_le_of_le hη hηη' L]

/-- **The mix losses of exponential weights telescope** [dRvEGK14, Section 2]. For losses `y t`
and nonincreasing learning rates `η t > 0`, the mix losses of the weights
`p t = softmax (-(η t • ∑ s < t, y s))` satisfy
`∑ t < n, mixLoss (η t) (p t) (y t) ≤ hedgePotential (η (n - 1)) (∑ t < n, y t)`: each mix loss is
an increment of the potential at the current learning rate, and the potential grows when the
learning rate decreases (`add_mixLoss_softmax_le_hedgePotential`). -/
theorem sum_mixLoss_softmax_le_of_antitone [Nonempty α] {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → α → ℝ) (n : ℕ) :
    ∑ t ∈ range n, mixLoss (η t) (softmax (-(η t • ∑ s ∈ range t, y s))) (y t) ≤
      hedgePotential (η (n - 1)) (∑ t ∈ range n, y t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, Nat.add_sub_cancel]
    exact add_mixLoss_softmax_le_hedgePotential (hη n) (hη_anti (Nat.sub_le n 1)) ih (y n)

/-- **Regret of exponential weights with nonincreasing learning rates**, through the mixability
gaps [dRvEGK14, Section 2; Ora, Section 7.5]. For losses `y t` and nonincreasing learning rates
`η t > 0`, the weights `p t = softmax (-(η t • ∑ s < t, y s))` satisfy, against every point `u` of
the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1)
  + ∑ t < n, (⟨p t, y t⟩ - mixLoss (η t) (p t) (y t))`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The mixability gap
`⟨p, y⟩ - mixLoss η p y = ⟨p, y⟩ + log (∑ b, p b * exp (-(η * y b))) / η` is also the maximum
over the simplex of the stability term of follow the regularized leader with the negative entropy
at `p`, by the Gibbs variational principle (`isGreatest_sum_sub_mul_sub_sum_mul_log_div_div`). -/
theorem softmax_regret_le_sum_sub_mixLoss_of_antitone {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → α → ℝ) (n : ℕ) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b -
          mixLoss (η t) (softmax (-(η t • ∑ s ∈ range t, y s))) (y t)) := by
  have := nonempty_of_mem_simplex hu
  have h_tel := sum_mixLoss_softmax_le_of_antitone hη hη_anti y n
  have h_pot := hedgePotential_le_sum_mul (hη (n - 1)) (∑ t ∈ range n, y t) hu
  have h_u : ∑ b, u b * (∑ t ∈ range n, y t) b = ∑ t ∈ range n, ∑ b, u b * y t b := by
    simp_rw [Finset.sum_apply, mul_sum]
    exact sum_comm
  rw [sum_sub_distrib, sum_sub_distrib]
  linarith

/-- **Regret of exponential weights with nonincreasing learning rates**, through the exponential
stability terms [Ora, Section 7.5; BCB12, proof of Theorem 3.1]. For losses `y t` and nonincreasing
learning rates `η t > 0`, the weights `p t = softmax (-(η t • ∑ s < t, y s))` satisfy, against
every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1)
  + ∑ t < n, (∑ b, p t b * (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. No sign condition on the losses is
needed; the local-norm bounds `softmax_regret_le_of_antitone` (nonnegative losses) and
`softmax_regret_le_of_antitone_of_neg_one_le` (losses with `η t * y t b ≥ -1`) bound the
stability terms. -/
theorem softmax_regret_le_sum_exp_of_antitone {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → α → ℝ) (n : ℕ) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b *
          (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t := by
  have := nonempty_of_mem_simplex hu
  exact (softmax_regret_le_sum_sub_mixLoss_of_antitone hη hη_anti y n hu).trans <|
    add_le_add le_rfl <| sum_le_sum fun t _ ↦
      sum_mul_sub_mixLoss_le (softmax_mem_simplex _) (hη t) (y t)


/-- **Regret of exponential weights with nonincreasing learning rates** [Ora, Section 7.5;
BCB12, proof of Theorem 3.1]. For losses `y t` that are nonnegative at the rounds `t < n` and
nonincreasing learning rates `η t > 0`, the weights `p t = softmax (-(η t • ∑ s < t, y s))`
satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1) + ∑ t < n, η t / 2 * ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. -/
theorem softmax_regret_le_of_antitone {η : ℕ → ℝ} (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    {y : ℕ → α → ℝ} {n : ℕ} (hy : ∀ t < n, ∀ b, 0 ≤ y t b) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, η t / 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  refine (softmax_regret_le_sum_exp_of_antitone hη hη_anti y n hu).trans
    (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  rw [div_le_iff₀ (hη t)]
  calc _ ≤ η t ^ 2 / 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 :=
        sum_mul_exp_neg_sub_one_add_le (softmax_nonneg _) (hy t (mem_range.1 ht)) (hη t).le
    _ = _ := by ring

/-- **Regret of exponential weights with nonincreasing learning rates, for losses bounded
below** [LS, proof of Theorem 27.1]. For losses `y t` with
`η t * y t b ≥ -1` at the rounds `t < n` and nonincreasing learning rates `η t > 0`, the weights
`p t = softmax (-(η t • ∑ s < t, y s))` satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1) + ∑ t < n, η t * ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The losses may be negative, as
the loss estimates of adversarial linear bandits are. -/
theorem softmax_regret_le_of_antitone_of_neg_one_le {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) {y : ℕ → α → ℝ} {n : ℕ} (hy : ∀ t < n, ∀ b, -1 ≤ η t * y t b)
    {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, η t * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  refine (softmax_regret_le_sum_exp_of_antitone hη hη_anti y n hu).trans
    (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  rw [div_le_iff₀ (hη t)]
  calc _ ≤ η t ^ 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 :=
        sum_mul_exp_neg_sub_one_add_le_of_neg_one_le (softmax_nonneg _) (hy t (mem_range.1 ht))
    _ = _ := by ring

/-- **Regret of exponential weights** with local norms. For losses `y t` that are nonnegative at
the rounds `t < n` and a learning rate `η > 0`, the weights `p t = softmax (-(η • ∑ s < t, y s))`
satisfy, against every coordinate `a`,
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η / 2 * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α`. This is the case of a constant learning rate and a vertex of the
simplex in `softmax_regret_le_of_antitone`. -/
theorem softmax_regret_le {η : ℝ} (hη : 0 < η) {y : ℕ → α → ℝ} {n : ℕ}
    (hy : ∀ t < n, ∀ b, 0 ≤ y t b) (a : α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b - y t a) ≤
      log (Fintype.card α) / η +
        η / 2 * ∑ t ∈ range n, ∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  classical
  have h := softmax_regret_le_of_antitone (η := fun _ ↦ η) (fun _ ↦ hη) antitone_const hy
    (single_mem_simplex a)
  simpa [Pi.single_apply, mul_sum] using h

/-- **Regret of exponential weights for losses bounded below** [LS, proof of Theorem 27.1]. For
losses `y t` with `η * y t b ≥ -1` at the rounds `t < n` and a learning rate `η > 0`, the weights
`p t = softmax (-(η • ∑ s < t, y s))` satisfy, against every coordinate `a`,
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α`. This is the case of a constant learning rate and a vertex of the
simplex in `softmax_regret_le_of_antitone_of_neg_one_le`. -/
theorem softmax_regret_le_of_neg_one_le {η : ℝ} (hη : 0 < η) {y : ℕ → α → ℝ} {n : ℕ}
    (hy : ∀ t < n, ∀ b, -1 ≤ η * y t b) (a : α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b - y t a) ≤
      log (Fintype.card α) / η +
        η * ∑ t ∈ range n, ∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  classical
  have h := softmax_regret_le_of_antitone_of_neg_one_le (η := fun _ ↦ η) (fun _ ↦ hη)
    antitone_const hy (single_mem_simplex a)
  simpa [Pi.single_apply, mul_sum] using h

end LMLExplore.OnlineLearning
