/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Kernel.Poisson
public import LMLExplore.Probability.MarkovChain.MarkovProperty
public import LMLExplore.Probability.Martingale.SubGaussian
public import LMLExplore.Probability.Moments.SubGaussian.Basic
public import Mathlib.Probability.Martingale.Basic

import LMLExplore.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.Order.ConditionallyCompleteLattice.Group
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Statlib.ForMathlib.Probability.Process.Filtration
import TauCeti.Probability.MarkovChain.Filtered.Basic

/-!
# The Poisson equation along a Markov chain

Let `X` be the coordinate process on path space `ℕ → α` under the law `markovChainLaw ν κ` of the
homogeneous Markov chain with initial law `ν` and transition kernel `κ`, with its natural filtration
`MeasureTheory.Filtration.piLE`. If a bounded measurable `g` solves the Poisson equation
`g - κ g = f - c` for a bounded measurable `f` and a constant `c` (for instance the solution
`ProbabilityTheory.Kernel.poissonSolution` with `c = ∫ f dπ` when `κ` is uniformly ergodic with
invariant law `π`), then `∑ k < n, (f (X k) - c) = g (X 0) - g (X n) + M n`, where
`M n = ∑ k < n, (g (X (k + 1)) - κ g (X k))` is a martingale. Given the past, its increment
`g (X (k + 1)) - κ g (X k)` is centered and lies in an interval of length `osc g = sup g - inf g`.
Hoeffding's lemma and the Azuma–Hoeffding inequality then give, for every `b ≥ osc g`, the
concentration bound `P(|(1 / n) ∑ k < n, f (X k) - c| ≥ ε) ≤ 2 exp (-2 (n ε - b)₊ ^ 2 / (n b ^ 2))`,
and the Borel–Cantelli lemma the law of large numbers: `(1 / n) ∑ k < n, f (X k) → c` almost
surely and in mean square.

The concentration bounds and the law of large numbers assume that `α` is a standard Borel space,
for the conditional sub-Gaussian bounds of Mathlib, which go through conditional distributions.

## Main statements

* `ProbabilityTheory.Kernel.sum_sub_eq_add_sum_sub_integralCLM`: the path-level decomposition.
* `MeasureTheory.Measure.martingale_sum_sub_integralCLM`: `M` is a martingale.
* `MeasureTheory.Measure.hasCondSubgaussianMGF_sub_integralCLM`: its increments are conditionally
  `(b / 2) ^ 2`-sub-Gaussian.
* `MeasureTheory.Measure.measureReal_le_sum_sub_le`,
  `MeasureTheory.Measure.measureReal_le_abs_average_sub_le`: the Hoeffding bounds.
* `MeasureTheory.Measure.ae_tendsto_average_markovChainLaw`,
  `MeasureTheory.Measure.tendsto_integral_sq_average_sub_markovChainLaw`: the law of large numbers,
  almost surely and in mean square.

## References

* [S. Meyn and R. L. Tweedie, *Markov chains and stochastic stability*, 2nd edition, 2009][MT09],
  Chapter 17
* [P. W. Glynn and D. Ormoneit, *Hoeffding's inequality for uniformly ergodic Markov chains*,
  2002][GO02]
-/

public section

open MeasureTheory Filter Topology Finset LMLExplore TauCeti.Probability
open scoped ENNReal NNReal lp

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  {f g : boundedMeasurable α} {c : ℝ}

/-- The Poisson equation `g - κ g = f - c • 1`, evaluated at a point. -/
lemma apply_sub_integralCLM_apply (hg : g - κ.integralCLM g = f - c • 1) (x : α) :
    (g : ℓ^∞(α, ℝ)) x - (κ.integralCLM g : ℓ^∞(α, ℝ)) x = (f : ℓ^∞(α, ℝ)) x - c := by
  rw [← boundedMeasurable.sub_smul_one_apply f c x, ← hg, boundedMeasurable.coeFn_sub,
    Pi.sub_apply]

/-- **The Poisson decomposition of an additive functional.** If `g - κ g = f - c`, then along every
path `ω`, `∑ k < n, (f (ω k) - c) = g (ω 0) - g (ω n) + ∑ k < n, (g (ω (k + 1)) - κ g (ω k))`. -/
theorem sum_sub_eq_add_sum_sub_integralCLM (hg : g - κ.integralCLM g = f - c • 1) (ω : ℕ → α)
    (n : ℕ) :
    ∑ k ∈ range n, ((f : ℓ^∞(α, ℝ)) (ω k) - c) =
      (g : ℓ^∞(α, ℝ)) (ω 0) - (g : ℓ^∞(α, ℝ)) (ω n) +
        ∑ k ∈ range n, ((g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih, ← apply_sub_integralCLM_apply hg]
    ring

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open ProbabilityTheory Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  {ν : Measure α} [IsProbabilityMeasure ν] {f g : boundedMeasurable α} {c b : ℝ}

/-! ### The martingale -/

/-- The increment `g (X (k + 1)) - κ g (X k)` of the martingale of the Poisson decomposition. -/
private lemma measurable_increment (g : boundedMeasurable α) {k n : ℕ} (hkn : k + 1 ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ α) n] fun ω : ℕ → α ↦
      (g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k) :=
  ((boundedMeasurable.measurable g).comp (Filtration.measurable_piLE_apply hkn)).sub
    ((boundedMeasurable.measurable _).comp
    (Filtration.measurable_piLE_apply (by omega)))

private lemma integrable_increment (g : boundedMeasurable α) (k : ℕ) :
    Integrable (fun ω : ℕ → α ↦
      (g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k)) (markovChainLaw ν κ) :=
  ((boundedMeasurable.integrable g _).comp_measurable (measurable_pi_apply _)).sub
    ((boundedMeasurable.integrable _ _).comp_measurable (measurable_pi_apply _))

/-- **The martingale of the Poisson decomposition.** For a bounded measurable `g`,
`M n = ∑ k < n, (g (X (k + 1)) - κ g (X k))` is a martingale for the natural filtration of the
chain. -/
theorem martingale_sum_sub_integralCLM (g : boundedMeasurable α) :
    Martingale (fun n ω ↦ ∑ k ∈ range n,
      ((g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k)))
      (Filtration.piLE (X := fun _ : ℕ ↦ α)) (markovChainLaw ν κ) := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun n ↦ ?_)
    (fun n ↦ integrable_finsetSum _ fun k _ ↦ integrable_increment g k) fun n ↦ ?_
  · exact (Finset.measurable_sum _ fun k hk ↦
      measurable_increment g (Nat.succ_le_of_lt (mem_range.1 hk))).stronglyMeasurable
  -- the increment is `g (X (n + 1)) - κ g (X n)`, of conditional expectation zero
  have hD : (fun ω : ℕ → α ↦ ∑ k ∈ range (n + 1),
      ((g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k))) -
      (fun ω : ℕ → α ↦ ∑ k ∈ range n,
        ((g : ℓ^∞(α, ℝ)) (ω (k + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω k))) =
      (fun ω : ℕ → α ↦ (g : ℓ^∞(α, ℝ)) (ω (n + 1))) -
        fun ω : ℕ → α ↦ (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω n) := by
    funext ω
    simp only [Pi.sub_apply, sum_range_succ, add_sub_cancel_left]
  rw [hD]
  have hκg : StronglyMeasurable[Filtration.piLE n]
      fun ω : ℕ → α ↦ (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω n) :=
    ((boundedMeasurable.measurable _).comp
      (Filtration.measurable_piLE_apply le_rfl)).stronglyMeasurable
  have hgint : Integrable (fun ω : ℕ → α ↦ (g : ℓ^∞(α, ℝ)) (ω (n + 1))) (markovChainLaw ν κ) :=
    (boundedMeasurable.integrable g _).comp_measurable (measurable_pi_apply _)
  have hκint : Integrable (fun ω : ℕ → α ↦ (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω n))
      (markovChainLaw ν κ) :=
    (boundedMeasurable.integrable _ _).comp_measurable (measurable_pi_apply _)
  filter_upwards [condExp_sub hgint hκint (Filtration.piLE n),
    (isMarkovChain_markovChainLaw ν κ).condExp_eq n _ (boundedMeasurable.measurable g)
      ⟨‖g‖, boundedMeasurable.abs_apply_le_norm g⟩] with ω h₁ h₂
  rw [h₁, Pi.sub_apply, h₂, ← integralCLM_apply,
    condExp_of_stronglyMeasurable (Filtration.le _ n) hκg hκint, sub_self, Pi.zero_apply]

/-! ### Concentration -/

/-- **Conditional Hoeffding lemma for the increments.** Given the history `X 0, …, X n`, the
increment `g (X (n + 1)) - κ g (X n)` is centered and lies in an interval of length `osc g`, hence
is conditionally `(b / 2) ^ 2`-sub-Gaussian for every `b ≥ osc g`. -/
theorem hasCondSubgaussianMGF_sub_integralCLM [StandardBorelSpace α] (g : boundedMeasurable α)
    (hb : orderUnitOsc 1 g ≤ b) (n : ℕ) :
    HasCondSubgaussianMGF (Filtration.piLE n) (Filtration.piLE.le n)
      (fun ω : ℕ → α ↦ (g : ℓ^∞(α, ℝ)) (ω (n + 1)) - (κ.integralCLM g : ℓ^∞(α, ℝ)) (ω n))
      ((‖b‖₊ / 2) ^ 2) (markovChainLaw ν κ) := by
  set X : (ℕ → α) → Fin (n + 1) → α := fun ω i ↦ ω i
  have hX : Measurable X := by fun_prop
  have hlast : Measurable fun w : Fin (n + 1) → α ↦ w (Fin.last n) := measurable_pi_apply _
  -- `g (X (n + 1))` has conditional law `(κ (w (Fin.last n))).map g` given the prefix `w`
  have hcd := (hasCondDistrib_eval_succ_markovChainLaw (ν := ν) (κ := κ) n).comp_left
    (boundedMeasurable.measurable g)
  have h := hcd.hasCondSubgaussianMGF_sub (c := (‖b‖₊ / 2) ^ 2) hX
    (g := fun w ↦ (κ.integralCLM g : ℓ^∞(α, ℝ)) (w (Fin.last n)))
    ((boundedMeasurable.measurable _).comp hlast) (.of_forall fun w ↦ ?_)
  · -- the σ-algebra generated by the prefix is the natural filtration; `convert` rather than `▸`,
    -- since the measurability proof of `HasCondSubgaussianMGF` depends on the σ-algebra
    convert h using 1
    exacts [Filtration.piLE_eq_comap_prefix n, rfl]
  -- Hoeffding's lemma under `(κ x).map g`, with `x = w (Fin.last n)`
  rw [Kernel.map_apply _ (boundedMeasurable.measurable g), Kernel.comap_apply]
  have hmem := mem_Icc_ciInf_of_forall_sub_le
    (fun y z ↦ (boundedMeasurable.sub_apply_le_orderUnitOsc_one g y z).trans hb)
  set a := ⨅ z, (g : ℓ^∞(α, ℝ)) z
  have hsub : b = a + b - (κ.integralCLM g : ℓ^∞(α, ℝ)) (w (Fin.last n)) -
      (a - (κ.integralCLM g : ℓ^∞(α, ℝ)) (w (Fin.last n))) := by ring
  -- write the parameter `(‖b‖₊ / 2) ^ 2` in the `(‖b' - a'‖₊ / 2) ^ 2` form of Hoeffding's
  -- lemma, for the interval `[a', b'] = [a - κ g x, a + b - κ g x]`
  rw [hsub]
  refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (by fun_prop) ?_ ?_
  · refine (ae_map_iff (boundedMeasurable.measurable g).aemeasurable
      (measurableSet_Icc.preimage (measurable_id.sub_const _))).2 (.of_forall fun z ↦ ?_)
    simp only [Set.mem_Icc, id_eq]
    exact ⟨by linarith [(hmem z).1], by linarith [(hmem z).2]⟩
  · rw [integral_map (boundedMeasurable.measurable g).aemeasurable (by fun_prop),
      integral_sub_const (boundedMeasurable.integrable g _), integralCLM_apply, sub_self]

/-- **Hoeffding's inequality for an additive functional of a Markov chain.** If `g - κ g = f - c`
for bounded measurable `f` and `g`, then for `osc g ≤ b ≤ ε`,
`P(ε ≤ ∑ k < n, (f (X k) - c)) ≤ exp (-2 (ε - b) ^ 2 / (n b ^ 2))`. -/
theorem measureReal_le_sum_sub_le [StandardBorelSpace α]
    (hg : g - κ.integralCLM g = f - c • 1) (hb : orderUnitOsc 1 g ≤ b) (n : ℕ) {ε : ℝ}
    (hbε : b ≤ ε) :
    (markovChainLaw ν κ).real {ω | ε ≤ ∑ k ∈ range n, ((f : ℓ^∞(α, ℝ)) (ω k) - c)} ≤
      Real.exp (-2 * (ε - b) ^ 2 / (n * b ^ 2)) := by
  have hb₀ : 0 ≤ b := (orderUnitOsc_nonneg _ _).trans hb
  -- the maximal Azuma–Hoeffding inequality for the martingale `M`, at the level `ε - b`
  have h := measure_exists_le_sum_le_of_hasCondSubgaussianMGF (μ := markovChainLaw ν κ)
    (ℱ := Filtration.piLE) (fun k ↦ measurable_increment g le_rfl)
    (fun k ↦ hasCondSubgaussianMGF_sub_integralCLM g hb k) (sub_nonneg.2 hbε) n
  have hexp : -(ε - b) ^ 2 / (2 * n * ((‖b‖₊ / 2) ^ 2 : ℝ≥0)) =
      -2 * (ε - b) ^ 2 / (n * b ^ 2) := by
    push_cast [Real.norm_of_nonneg hb₀]
    ring
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    ((measure_mono ?_).trans (h.trans_eq (by rw [hexp])))
  intro ω (hω : ε ≤ _)
  refine ⟨n, le_rfl, ?_⟩
  -- `∑ k < n, (f (X k) - c) ≤ osc g + M n`
  rw [sum_sub_eq_add_sum_sub_integralCLM hg] at hω
  linarith [boundedMeasurable.sub_apply_le_orderUnitOsc_one g (ω 0) (ω n)]

/-- **Two-sided Hoeffding inequality for the averages of a Markov chain.** If `g - κ g = f - c`
for bounded measurable `f` and `g`, then for every `b ≥ osc g`,
`P(ε ≤ |(1 / n) ∑ k < n, f (X k) - c|) ≤ 2 exp (-2 (n ε - b)₊ ^ 2 / (n b ^ 2))`. -/
theorem measureReal_le_abs_average_sub_le [StandardBorelSpace α]
    (hg : g - κ.integralCLM g = f - c • 1) (hb : orderUnitOsc 1 g ≤ b) (n : ℕ) (ε : ℝ) :
    (markovChainLaw ν κ).real
        {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c|} ≤
      2 * Real.exp (-2 * max (n * ε - b) 0 ^ 2 / (n * b ^ 2)) := by
  rcases le_or_gt (n * ε - b) 0 with hnε | hnε
  · rw [max_eq_right hnε]
    simpa using (measureReal_le_one (μ := markovChainLaw ν κ)).trans one_le_two
  rw [max_eq_left hnε.le]
  -- `n ε > b ≥ 0`, so that `n ≠ 0`
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CharP.cast_eq_zero, zero_mul, zero_sub] at hnε
      linarith [(orderUnitOsc_nonneg (1 : boundedMeasurable α) g).trans hb]
    · exact_mod_cast hn
  -- the upper tail of `f` and that of `-f`, which solves the equation with `-g` and `-c`
  have hneg : -g - κ.integralCLM (-g) = -f - (-c) • 1 := by
    rw [ContinuousLinearMap.map_neg, neg_smul]
    linear_combination (norm := abel_nf) -hg
  have h₁ := measureReal_le_sum_sub_le (ν := ν) hg hb n (ε := n * ε) (by linarith)
  have h₂ := measureReal_le_sum_sub_le (ν := ν) (b := b) hneg (by rwa [orderUnitOsc_neg]) n
    (ε := n * ε) (by linarith)
  refine (measureReal_mono (s₂ := {ω | n * ε ≤ ∑ k ∈ range n, ((f : ℓ^∞(α, ℝ)) (ω k) - c)} ∪
    {ω | n * ε ≤ ∑ k ∈ range n, (((-f : boundedMeasurable α) : ℓ^∞(α, ℝ)) (ω k) - -c)})
      (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (by linarith))
  simp only [Set.mem_ofPred_eq, boundedMeasurable.coeFn_neg, Pi.neg_apply, sum_sub_distrib,
    Finset.sum_const, card_range, nsmul_eq_mul, Set.mem_union] at hω ⊢
  -- `ε ≤ |S / n - c|` gives `n ε ≤ S - n c` or `n ε ≤ n c - S`
  field_simp at hω
  rw [abs_div, abs_of_pos hn, le_div_iff₀ hn] at hω
  rcases le_abs'.1 hω with h | h
  · right
    rw [sum_neg_distrib]
    linarith
  · left
    linarith

/-! ### The law of large numbers -/

/-- The Hoeffding bound of `measureReal_le_abs_average_sub_le` is summable in `n` for `ε, b > 0`:
it is at most `2 exp (4 ε / b) exp (-2 ε ^ 2 / b ^ 2) ^ n`. -/
private lemma summable_two_mul_exp {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    Summable fun n : ℕ ↦ 2 * Real.exp (-2 * max (n * ε - b) 0 ^ 2 / (n * b ^ 2)) := by
  have hr : Real.exp (-2 * ε ^ 2 / b ^ 2) < 1 := Real.exp_lt_one_iff.2 (by
    have : 0 < ε ^ 2 / b ^ 2 := by positivity
    rw [mul_div_assoc]; linarith)
  refine .of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    (((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (2 * Real.exp (4 * ε / b))))
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  gcongr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul, div_zero, add_zero]
    positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `2 n ^ 2 ε ^ 2 - 2 (n ε - b)₊ ^ 2 ≤ 4 n ε b`, in both cases of the positive part
  have key : -2 * max (n * ε - b) 0 ^ 2 ≤ 4 * ε * b * n - 2 * n ^ 2 * ε ^ 2 := by
    rcases le_or_gt (n * ε - b) 0 with hnε | hnε
    · rw [max_eq_right hnε]
      nlinarith [mul_pos hn' hε]
    · rw [max_eq_left hnε.le]
      nlinarith
  calc -2 * max (n * ε - b) 0 ^ 2 / (n * b ^ 2)
      ≤ (4 * ε * b * n - 2 * n ^ 2 * ε ^ 2) / (n * b ^ 2) :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = 4 * ε / b + n * (-2 * ε ^ 2 / b ^ 2) := by
        field_simp
        ring

/-- **Law of large numbers for a Markov chain.** If `g - κ g = f - c` for bounded measurable `f`
and `g`, then the averages `(1 / n) ∑ k < n, f (X k)` converge to `c` almost surely. -/
theorem ae_tendsto_average_markovChainLaw [StandardBorelSpace α]
    (hg : g - κ.integralCLM g = f - c • 1) :
    ∀ᵐ ω ∂(markovChainLaw ν κ),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k)) atTop (𝓝 c) := by
  set b := orderUnitOsc 1 g + 1
  have hb : 0 < b := by positivity [orderUnitOsc_nonneg (1 : boundedMeasurable α) g]
  -- for each `ε = 1 / (j + 1)`, Borel–Cantelli: eventually `|average - c| < ε`
  have hε (j : ℕ) : ∀ᵐ ω ∂(markovChainLaw ν κ), ∀ᶠ n : ℕ in atTop,
      ω ∉ {ω | 1 / ((j : ℝ) + 1) ≤
        |(n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c|} := by
    refine ae_eventually_notMem ?_
    have hs := summable_two_mul_exp hb (ε := 1 / ((j : ℝ) + 1)) (by positivity)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs ▸
      ENNReal.ofReal_ne_top) (tsum_le_tsum fun n ↦ ?_)
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (measureReal_le_abs_average_sub_le hg (by linarith) n _)
  filter_upwards [ae_all_iff.2 hε] with ω hω
  refine Metric.tendsto_atTop.2 fun ε hεpos ↦ ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hεpos
  obtain ⟨N, hN⟩ := (hω j).exists_forall_of_atTop
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  simp only [not_le] at this
  rw [Real.dist_eq]
  exact this.trans hj

/-- **Mean-square law of large numbers for a Markov chain.** If `g - κ g = f - c` for bounded
measurable `f` and `g`, then `E[((1 / n) ∑ k < n, f (X k) - c) ^ 2] → 0`. -/
theorem tendsto_integral_sq_average_sub_markovChainLaw [StandardBorelSpace α]
    (hg : g - κ.integralCLM g = f - c • 1) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c) ^ 2
      ∂(markovChainLaw ν κ)) atTop (𝓝 0) := by
  -- dominated convergence, with the constant bound `(‖f‖ + |c|) ^ 2`
  have hbound (n : ℕ) (ω : ℕ → α) :
      |(n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k)| ≤ ‖f‖ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ (by exact_mod_cast hn)]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simpa using sum_le_sum fun k (_ : k ∈ range n) ↦ boundedMeasurable.abs_apply_le_norm f (ω k)
  have hlim : ∀ᵐ ω ∂(markovChainLaw ν κ), Tendsto (fun n : ℕ ↦
      ((n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c) ^ 2) atTop (𝓝 0) := by
    filter_upwards [ae_tendsto_average_markovChainLaw (ν := ν) hg] with ω hω
    simpa using (hω.sub_const c).pow 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω : ℕ → α ↦
      ((n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c) ^ 2) (markovChainLaw ν κ) :=
    ((((Finset.measurable_sum _ fun k _ ↦ (boundedMeasurable.measurable f).comp
      (measurable_pi_apply k)).const_mul _).sub_const _).pow_const 2).aestronglyMeasurable
  have hle (n : ℕ) : ∀ᵐ ω ∂(markovChainLaw ν κ),
      ‖((n : ℝ)⁻¹ * ∑ k ∈ range n, (f : ℓ^∞(α, ℝ)) (ω k) - c) ^ 2‖ ≤ (‖f‖ + |c|) ^ 2 := by
    refine .of_forall fun ω ↦ ?_
    rw [Real.norm_eq_abs, abs_pow, sq_le_sq₀ (abs_nonneg _) (by positivity)]
    exact (abs_sub _ _).trans (add_le_add (hbound n ω) le_rfl)
  have h := tendsto_integral_of_dominated_convergence (fun _ ↦ (‖f‖ + |c|) ^ 2) hmeas
    (integrable_const _) hle hlim
  simpa only [integral_zero] using h

end MeasureTheory.Measure
