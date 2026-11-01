/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.Means
public import LMLExplore.Probability.HasCondDistrib
public import LMLExplore.Topology.Algebra.InfiniteSum.NatInt

/-!
# Wald's identities for sequential algorithms

*Wald's identities* express the expectation of a sum over the rounds before a random time `τ`
through the expected numbers of pulls `N_a(τ)` of the actions, where `N_a(τ)` is the number of
rounds before `τ` at which the action `a` was played.

For finitely many actions and any measurable random time `τ`, regrouping the rounds by the action
played gives `𝔼[∑_{t < τ} f(A_t)] = ∑ a, 𝔼[N_a(τ)] f(a)` for `f ≥ 0`, and with `f = 1`, Wald's
identity for the number of rounds `𝔼[τ] = ∑ a, 𝔼[N_a(τ)]` when `τ` is almost surely finite. These
hold for every sequence of actions; the divergence decomposition of bandit lower bounds and the
sample complexity of identification algorithms are built on them.

Let now `A`, `Y` be the actions and rewards of an algorithm run against a stationary environment
`stationaryEnv ν` with finitely many actions and integrable real reward distributions `ν a` of
means `μ_a`. For a random time `τ` of finite expectation such that the event `{t < τ}` is known
when the action of round `t` is chosen (a stopping time of `IsAlgEnvSeq.filtrationAction`, such as
the stopping time of an identification algorithm), *Wald's identity for the rewards* states
`𝔼[∑_{t < τ} Y_t] = ∑ a, 𝔼[N_a(τ)] μ_a`.

The identity rests on conditioning on the information available when the action of a round is
chosen: on an event of `IsAlgEnvSeq.filtrationAction n`, the reward `Y_n` can be replaced by the
mean `μ_{A_n}` of its distribution.

## Main statements

* `LMLExplore.sum_lintegral_pullCount_mul`: for a measurable random time `g`,
  `∑ a, 𝔼[N_a(g)] f a = 𝔼[∑ s < g, f (A s)]`.
* `LMLExplore.natCast_pullCount_toNat_le`: `N_a(n) ≤ n` for `n : ℕ∞`.
* `LMLExplore.lintegral_toENNReal_eq_sum_lintegral_pullCount`: Wald's identity
  `𝔼[τ] = ∑ a, 𝔼[N_a(τ)]` for an almost surely finite measurable random time `τ`.
* `Learning.IsAlgEnvSeq.setLIntegral_comp_feedback_stationaryEnv`: on an event of
  `h.filtrationAction n`, the expectation of `g(Y_n)` is that of `∫ g dν(A_n)`, for `g ≥ 0`.
* `Learning.IsAlgEnvSeq.integrable_feedback_stationaryEnv`: the rewards are integrable when the
  reward distributions are.
* `Learning.IsAlgEnvSeq.setIntegral_feedback_stationaryEnv`: on an event of `h.filtrationAction n`,
  the expectation of `Y_n` is that of the mean `μ_{A_n}`.
* `Learning.IsAlgEnvSeq.integral_sum_feedback_eq_sum_integral_pullCount_mul`: Wald's identity for
  the rewards `𝔼[∑_{t < τ} Y_t] = ∑ a, 𝔼[N_a(τ)] μ_a`.

## References

* A. Wald, *On cumulative sums of random variables*, Ann. Math. Statist. 15 (1944).
-/

public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

namespace LMLExplore

variable {𝓐 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {mΩ : MeasurableSpace Ω} [DecidableEq 𝓐]
  [Fintype 𝓐] {P : Measure Ω} {A : ℕ → Ω → 𝓐}

/-- For a finite action set and a measurable random time `g`, the expected number of rounds
before `g` at which each action is played, weighted by `f`, is the expected sum of `f` over the
actions played before `g`: `∑ a, E[N_a(g)] f a = E[∑ s < g, f (A s)]`. -/
lemma sum_lintegral_pullCount_mul [MeasurableSingletonClass 𝓐] (hA : ∀ n, Measurable (A n))
    {g : Ω → ℕ} (hg : Measurable g) (f : 𝓐 → ℝ≥0∞) :
    ∑ a, (∫⁻ ω, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) ∂P) * f a =
      ∫⁻ ω, ∑ s ∈ range (g ω), f (A s ω) ∂P := by
  have hmeas (a : 𝓐) : Measurable fun ω ↦ (Learning.pullCount A a (g ω) ω : ℝ≥0∞) :=
    (measurable_of_countable _).comp
      (Learning.measurable_uncurry_pullCount_comp hA measurable_const hg)
  calc ∑ a, (∫⁻ ω, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) ∂P) * f a
      = ∫⁻ ω, ∑ a, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) * f a ∂P := by
        rw [lintegral_finsetSum _ fun a _ ↦ (hmeas a).mul_const _]
        exact sum_congr rfl fun a _ ↦ (lintegral_mul_const _ (hmeas a)).symm
    _ = ∫⁻ ω, ∑ s ∈ range (g ω), f (A s ω) ∂P :=
        lintegral_congr fun ω ↦ Learning.sum_pullCount_mul ω f (g ω)

omit [Fintype 𝓐] in
/-- The number of pulls of an action before `n.toNat` is at most `n`, for `n : ℕ∞`. -/
lemma natCast_pullCount_toNat_le (a : 𝓐) (n : ℕ∞) (ω : Ω) :
    (Learning.pullCount A a n.toNat ω : ℝ≥0∞) ≤ n := by
  rw [← ENat.toENNReal_coe, ENat.toENNReal_le]
  exact (Nat.cast_le.2 (Learning.pullCount_le a _ ω)).trans (ENat.natCast_toNat_le_self _)

/-- **Wald's identity for the number of rounds.** For an almost surely finite measurable random
time `τ` and finitely many actions, `E[τ] = ∑ a, E[N_a(τ)]`, where `N_a(τ)` is the number of
rounds before `τ` at which the action `a` is played. -/
lemma lintegral_toENNReal_eq_sum_lintegral_pullCount [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) {τ : Ω → ℕ∞} (hτ : Measurable τ) (h_fin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P = ∑ a, ∫⁻ ω, (Learning.pullCount A a (τ ω).toNat ω : ℝ≥0∞) ∂P := by
  have h := sum_lintegral_pullCount_mul (P := P) hA (g := fun ω ↦ (τ ω).toNat)
    (Measurable.of_discrete.comp hτ) fun _ ↦ 1
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul] at h
  rw [h]
  refine lintegral_congr_ae ?_
  filter_upwards [h_fin] with ω hω
  rw [← ENat.toENNReal_coe, ENat.natCast_toNat hω]

end LMLExplore


namespace Learning

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- On an event `s` of `h.filtrationAction n` (determined by the history before round `n` and the
action of round `n`), the expectation of `g(Y_n)` against a stationary environment `ν` is that of
`∫ g dν(A_n)`, for a measurable `g ≥ 0`. -/
lemma IsAlgEnvSeq.setLIntegral_comp_feedback_stationaryEnv {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐}
    {Y : ℕ → Ω → 𝓨} {alg : Algorithm Unit 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) {n : ℕ} {s : Set Ω}
    (hs : MeasurableSet[h.filtrationAction n] s) {g : 𝓨 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω in s, g (Y n ω) ∂P = ∫⁻ ω in s, ∫⁻ y, g y ∂(ν (A n ω)) ∂P := by
  rw [h.filtrationAction_eq_comap n] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [feedback_stationaryEnv] using
    (h.hasCondDistrib_feedback n).setLIntegral_comp_eq_setLIntegral_lintegral ht hg

variable {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]

/-- On an event `s` of `h.filtrationAction n` (determined by the history before round `n` and the
action of round `n`), the expectation of the reward `Y_n` against a stationary environment `ν` is
that of the mean of `ν (A_n)`. -/
lemma IsAlgEnvSeq.setIntegral_feedback_stationaryEnv (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P)
    {n : ℕ} (hY : Integrable (Y n) P) {s : Set Ω} (hs : MeasurableSet[h.filtrationAction n] s) :
    ∫ ω in s, Y n ω ∂P = ∫ ω in s, ∫ y, y ∂(ν (A n ω)) ∂P := by
  rw [← setIntegral_condExp (h.filtrationAction.le n) hY hs]
  refine setIntegral_congr_ae (h.filtrationAction.le n _ hs) ?_
  filter_upwards [h.condExp_feedback n hY] with ω hω _
  simp [hω]

section Finite

variable [Finite 𝓐]

/-- Against a stationary environment with finitely many actions and integrable reward
distributions, the reward of each round is integrable. -/
lemma IsAlgEnvSeq.integrable_feedback_stationaryEnv (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P)
    (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    Integrable (Y n) P := by
  have := Fintype.ofFinite 𝓐
  refine ⟨(h.measurable_feedback n).aestronglyMeasurable, ?_⟩
  have h_eq := h.setLIntegral_comp_feedback_stationaryEnv (n := n) MeasurableSet.univ
    measurable_enorm
  simp only [Measure.restrict_univ] at h_eq
  rw [hasFiniteIntegral_iff_enorm, h_eq]
  calc ∫⁻ ω, ∫⁻ y, ‖y‖ₑ ∂(ν (A n ω)) ∂P ≤ ∫⁻ _, ∑ a, ∫⁻ y, ‖y‖ₑ ∂(ν a) ∂P :=
        lintegral_mono fun ω ↦ single_le_sum (f := fun a ↦ ∫⁻ y, ‖y‖ₑ ∂(ν a))
          (fun _ _ ↦ bot_le) (mem_univ _)
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.sum_lt_top.2 fun a _ ↦ (hν a).2) (measure_lt_top _ _)

/-- The expected sum over the rounds before a random time `τ` with `𝔼[τ] < ∞` of the absolute
moments `∫ |y| dν(A_t)` of the reward distributions is finite. -/
private lemma tsum_lintegral_indicator_lintegral_enorm_ne_top [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) (hν : ∀ a, Integrable id (ν a))
    {τ : Ω → ℕ∞} (hτ : Measurable τ) (hτ_int : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P ≠ ∞)
    (hτ_fin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∑' t : ℕ, ∫⁻ ω, {ω | (t : ℕ∞) < τ ω}.indicator
      (fun ω ↦ ∫⁻ y, ‖y‖ₑ ∂(ν (A t ω))) ω ∂P ≠ ∞ := by
  classical
  have := Fintype.ofFinite 𝓐
  set c : 𝓐 → ℝ≥0∞ := fun a ↦ ∫⁻ y, ‖y‖ₑ ∂(ν a)
  rw [← lintegral_tsum (f := fun t : ℕ ↦ {ω | (t : ℕ∞) < τ ω}.indicator (fun ω ↦ c (A t ω)))
      fun t ↦ (((measurable_of_countable c).comp (h.measurable_action t)).indicator
        (hτ (MeasurableSet.of_discrete (s := Set.Ioi (t : ℕ∞))))).aemeasurable,
    lintegral_congr_ae (by
      filter_upwards [hτ_fin] with ω hω using
        LMLExplore.tsum_indicator_natCast_lt_eq_sum_range hω fun t ↦ c (A t ω)),
    ← LMLExplore.sum_lintegral_pullCount_mul (g := fun ω ↦ (τ ω).toNat) h.measurable_action
      (Measurable.of_discrete.comp hτ) c]
  refine (ENNReal.sum_lt_top.2 fun a _ ↦ ENNReal.mul_lt_top ?_ (hν a).2).ne
  exact (lintegral_mono fun ω ↦ LMLExplore.natCast_pullCount_toNat_le a (τ ω) ω).trans_lt
    hτ_int.lt_top

end Finite

variable [Fintype 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐]

/-- **Wald's identity for the rewards.** For an algorithm run against a stationary environment
`ν` with finitely many actions and integrable reward distributions, and a stopping time `τ` of
`h.filtrationAction` (the event `{t < τ}` is known when the action of round `t` is chosen) with
`𝔼[τ] < ∞`, the expected sum of the rewards before `τ` is `∑ a, 𝔼[N_a(τ)] μ_a`, where `N_a(τ)` is
the number of rounds before `τ` at which `a` was played and `μ_a` is the mean of `ν a`. -/
theorem IsAlgEnvSeq.integral_sum_feedback_eq_sum_integral_pullCount_mul
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) {τ : Ω → ℕ∞}
    (hτ : IsStoppingTime h.filtrationAction τ) (hτ_int : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P ≠ ∞)
    (hν : ∀ a, Integrable id (ν a)) :
    ∫ ω, ∑ t ∈ range (τ ω).toNat, Y t ω ∂P =
      ∑ a, (∫ ω, (pullCount A a (τ ω).toNat ω : ℝ) ∂P) * ∫ y, y ∂(ν a) := by
  -- `S t = {t < τ}` is known when the action of round `t` is chosen
  set S : ℕ → Set Ω := fun t ↦ {ω | (t : ℕ∞) < τ ω}
  have hS_F (t : ℕ) : MeasurableSet[h.filtrationAction t] (S t) := hτ.measurableSet_gt t
  have hS (t : ℕ) : MeasurableSet (S t) := h.filtrationAction.le t _ (hS_F t)
  -- `hτ.measurable'` is measurability for Mathlib's Borel σ-algebra on `WithTop ℕ`, the
  -- codomain of stopping times, whereas `ℕ∞` carries the discrete σ-algebra `⊤`: the two
  -- instances live on the same type but are not syntactically equal, so measurability for `ℕ∞`
  -- is rebuilt from the measurable preimages of the (Borel-measurable) singletons.
  have hτ_meas : Measurable τ :=
    measurable_to_countable' fun x ↦ hτ.measurable' (measurableSet_singleton (α := WithTop ℕ) x)
  have hτ_fin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (Measurable.of_discrete.comp hτ_meas) hτ_int] with ω hω
    simpa using hω.ne
  set μ : 𝓐 → ℝ := fun a ↦ ∫ y, y ∂(ν a)
  have hN_int (a : 𝓐) : Integrable (fun ω ↦ (pullCount A a (τ ω).toNat ω : ℝ)) P := by
    refine ⟨(Measurable.of_discrete.comp (measurable_uncurry_pullCount_comp h.measurable_action
      measurable_const (Measurable.of_discrete.comp hτ_meas))).aestronglyMeasurable, ?_⟩
    refine (lintegral_mono fun ω ↦ ?_).trans_lt hτ_int.lt_top
    rw [Real.enorm_natCast]
    exact LMLExplore.natCast_pullCount_toNat_le a (τ ω) ω
  -- the series `∑ t, 1{t < τ} Y_t` and `∑ t, 1{t < τ} μ (A t)` are dominated by the finite
  -- `𝔼[∑_{t < τ} ∫ |y| dν(A t)]`
  have hB := tsum_lintegral_indicator_lintegral_enorm_ne_top h hν hτ_meas hτ_int hτ_fin
  have hY_sum : ∑' t, ∫⁻ ω, ‖(S t).indicator (Y t) ω‖ₑ ∂P ≠ ∞ := by
    refine ne_of_eq_of_ne (tsum_congr fun t ↦ ?_) hB
    simp_rw [enorm_indicator_eq_indicator_enorm, lintegral_indicator (hS t)]
    exact (h.setLIntegral_comp_feedback_stationaryEnv (hS_F t) measurable_enorm).trans
      (lintegral_indicator (hS t) _).symm
  have hμ_sum : ∑' t, ∫⁻ ω, ‖(S t).indicator (fun ω ↦ μ (A t ω)) ω‖ₑ ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top hB (ENNReal.tsum_le_tsum fun t ↦ lintegral_mono fun ω ↦ ?_)
    rw [enorm_indicator_eq_indicator_enorm]
    exact Set.indicator_le_indicator (enorm_integral_le_lintegral_enorm _)
  calc ∫ ω, ∑ t ∈ range (τ ω).toNat, Y t ω ∂P
      = ∫ ω, ∑' t, (S t).indicator (Y t) ω ∂P := integral_congr_ae (by
        filter_upwards [hτ_fin] with ω hω using
          (LMLExplore.tsum_indicator_natCast_lt_eq_sum_range hω fun t ↦ Y t ω).symm)
    _ = ∑' t, ∫ ω, (S t).indicator (Y t) ω ∂P := integral_tsum (fun t ↦
        ((h.measurable_feedback t).indicator (hS t)).aestronglyMeasurable) hY_sum
    -- on `{t < τ}`, the reward `Y t` can be replaced by its conditional mean `μ (A t)`
    _ = ∑' t, ∫ ω, (S t).indicator (fun ω ↦ μ (A t ω)) ω ∂P := tsum_congr fun t ↦ by
        rw [integral_indicator (hS t), integral_indicator (hS t),
          h.setIntegral_feedback_stationaryEnv (h.integrable_feedback_stationaryEnv hν t) (hS_F t)]
    _ = ∫ ω, ∑' t, (S t).indicator (fun ω ↦ μ (A t ω)) ω ∂P := (integral_tsum (fun t ↦
        (((measurable_of_countable μ).comp (h.measurable_action t)).indicator
          (hS t)).aestronglyMeasurable) hμ_sum).symm
    _ = ∫ ω, ∑ a, (pullCount A a (τ ω).toNat ω : ℝ) * μ a ∂P := integral_congr_ae (by
        filter_upwards [hτ_fin] with ω hω
        exact (LMLExplore.tsum_indicator_natCast_lt_eq_sum_range hω fun t ↦ μ (A t ω)).trans
          (sum_pullCount_mul ω μ _).symm)
    _ = ∑ a, (∫ ω, (pullCount A a (τ ω).toNat ω : ℝ) ∂P) * μ a := by
        rw [integral_finsetSum _ fun a _ ↦ (hN_int a).mul_const _]
        exact sum_congr rfl fun a _ ↦ integral_mul_const _ _

end Learning
