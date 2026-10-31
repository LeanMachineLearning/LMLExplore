/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.Algorithm
public import LMLExplore.SequentialLearning.FiniteActions
public import LMLExplore.SequentialLearning.StoppedHistory
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# The divergence decomposition, reindexed by the actions, and at a stopping time

LML's `IsAlgEnvSeq.klDiv_map_history` writes the relative entropy between the laws of the
histories of the first `M` rounds of one algorithm run against two stationary environments with
reward kernels `κ` and `κ'` as a sum over the rounds: `∑ t < M, E[KL(κ (A t) ‖ κ' (A t))]`. For a
finite set of actions, this file regroups the sum by the action played, which gives the
*divergence decomposition* of bandit lower bounds [LS, Lemma 15.1]:
`KL = ∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M` is the number of rounds
before `M` at which `a` was played.

The same bound holds at an almost surely finite stopping time `τ`, the hitting time of a stopping
rule `S`, for the laws of the history stopped by `S`:
`KL ≤ ∑ a, E[N_a(τ)] KL(κ a ‖ κ' a)`. This is the change of measure behind the lower bounds of
bandit identification.

## Main statements

* `LMLExplore.sum_lintegral_pullCount_mul`: for a measurable random time `g`,
  `∑ a, E[N_a(g)] f a = E[∑ s < g, f (A s)]`.
* `LMLExplore.lintegral_toENNReal_eq_sum_lintegral_pullCount`: Wald's identity
  `E[τ] = ∑ a, E[N_a(τ)]` for an almost surely finite measurable random time `τ`.
* `LMLExplore.natCast_pullCount_toNat_le`: `N_a(n) ≤ n` for `n : ℕ∞`.
* `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`: the divergence decomposition.
* `Learning.IsAlgEnvSeq.klDiv_map_history_eq_lintegral_pullCount_mul`: if the reward kernels
  agree outside the action `i`, then `KL = E[N_i(M)] KL(κ i ‖ κ' i)`.
* `Learning.IsAlgEnvSeq.klDiv_map_history_le_ofReal_integral_pullCount_mul`: if moreover
  `KL(κ i ‖ κ' i) ≤ c`, then `KL ≤ E[N_i(M)] c`.
* `Learning.klDiv_stoppedHistMeasure_le`: the divergence decomposition at a stopping time,
  `KL(stoppedHistMeasure alg (stationaryEnv κ) S ‖ stoppedHistMeasure alg (stationaryEnv κ') S) ≤
  ∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)` when the hitting time `τ` of `S` is almost surely finite
  under `κ`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 15.1.
* E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), proof of Lemma 1, for the decomposition at a
  stopping time.
* The proofs of the fixed-horizon statements are adapted from the formalization in the LMLPapers
  project
  (`LMLPapers/LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
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

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm Unit 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- **Divergence decomposition** [LS, Lemma 15.1]: the relative entropy between the laws of the
histories of the first `M` rounds of an algorithm run against two stationary environments with
reward kernels `κ` and `κ'` is `∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M`
is the number of rounds before `M` at which `a` was played. -/
lemma IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ a, (∫⁻ ω, (pullCount A a M ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) := by
  have hsum : ∑ t ∈ range M, ∫⁻ ω, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P =
      ∫⁻ ω, ∑ t ∈ range M, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P :=
    (lintegral_finsetSum _ fun t _ ↦
      (measurable_klDiv_kernel κ κ').comp (h.measurable_action t)).symm
  rw [h.klDiv_map_history h' M, hsum]
  exact (LMLExplore.sum_lintegral_pullCount_mul (g := fun _ ↦ M) h.measurable_action
    measurable_const fun a ↦ klDiv (κ a) (κ' a)).symm

omit [Fintype 𝓐] in
/-- **Divergence decomposition** for reward kernels `κ` and `κ'` that agree outside the action
`i`: the relative entropy between the laws of the histories of the first `M` rounds is
`E[N_i(M)] KL(κ i ‖ κ' i)`. -/
lemma IsAlgEnvSeq.klDiv_map_history_eq_lintegral_pullCount_mul [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') {i : 𝓐} (hκ : ∀ a ≠ i, κ a = κ' a)
    (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      (∫⁻ ω, (pullCount A i M ω : ℝ≥0∞) ∂P) * klDiv (κ i) (κ' i) := by
  have := Fintype.ofFinite 𝓐
  rw [h.klDiv_map_history_eq_sum_pullCount h' M,
    sum_eq_single i (fun a _ ha ↦ by rw [hκ a ha, klDiv_self, mul_zero])
      (fun hi ↦ absurd (mem_univ i) hi)]

omit [Fintype 𝓐] in
/-- If the reward kernels `κ` and `κ'` agree outside the action `i` and
`KL(κ i ‖ κ' i) ≤ c`, then the relative entropy between the laws of the histories of the first `M`
rounds is at most `E[N_i(M)] c`. -/
lemma IsAlgEnvSeq.klDiv_map_history_le_ofReal_integral_pullCount_mul [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') {i : 𝓐} (hκ : ∀ a ≠ i, κ a = κ' a)
    {c : ℝ} (hc : klDiv (κ i) (κ' i) ≤ ENNReal.ofReal c) (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≤
      ENNReal.ofReal ((∫ ω, (pullCount A i M ω : ℝ) ∂P) * c) := by
  rw [h.klDiv_map_history_eq_lintegral_pullCount_mul h' hκ M,
    LMLExplore.lintegral_pullCount_eq_ofReal_integral h.measurable_action,
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ Nat.cast_nonneg _)]
  gcongr

section StoppingTime

/-! ### The divergence decomposition at a stopping time

Let `τ` be the hitting time of a stopping rule `S`. The environment `swapEnv` below follows `κ'`
until `τ` and `κ` afterwards. Its stopped history has the same law as under `κ'`
(`stoppedHistMeasure_congr`), and the divergence between its trajectory and the trajectory
under `κ` only collects the rounds before `τ`. The data processing inequality for the stopped
history, a function of the trajectory, concludes. -/

variable {S : Set (Σ n : ℕ, Hist Unit 𝓐 𝓨 n)}

/-- The environment that follows the reward kernel `κ'` while the stopping rule `S` has not
stopped and the reward kernel `κ` afterwards. -/
private noncomputable abbrev swapEnv (κ κ' : Kernel 𝓐 𝓨) [IsMarkovKernel κ] [IsMarkovKernel κ']
    (hS : MeasurableSet S) : Environment Unit 𝓐 𝓨 :=
  (stationaryEnv κ').piecewise (notStoppedSet S) (measurableSet_notStoppedSet hS)
    (stationaryEnv κ)

omit [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] in
/-- The divergence of round `t` between `κ` and `swapEnv κ κ' hS` is the divergence between the
reward kernels at the played action, on the event that round `t` is played before stopping. -/
private lemma klDiv_compProd_stepKernel_swapEnv (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (hS : MeasurableSet S) (t : ℕ) :
    klDiv (P.map (history O A Y t) ⊗ₘ stepKernel alg (stationaryEnv κ) t)
        (P.map (history O A Y t) ⊗ₘ stepKernel alg (swapEnv κ κ' hS) t) =
      ∫⁻ ω, {ω | history O A Y t ω ∈ notStoppedSet S t}.indicator
        (fun ω ↦ klDiv (κ (A t ω)) (κ' (A t ω))) ω ∂P := by
  have h_obs : (swapEnv κ κ' hS).obs t = Kernel.const _ (Measure.dirac ()) := by
    ext x : 1
    simp [Environment.obs_piecewise, Kernel.piecewise_apply]
  have hX : Measurable fun ω ↦ ((history O A Y t ω, O t ω), A t ω) :=
    ((h.measurable_history t).prodMk (h.measurable_obs t)).prodMk (h.measurable_action t)
  -- Reassociate the step kernels so that only the feedback kernels differ.
  rw [stepKernel_stationaryEnv, stepKernel_def, h_obs,
    ← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm, Measure.compProd_assoc,
    Measure.compProd_assoc, ← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm,
    Measure.compProd_assoc, Measure.compProd_assoc, ← obs_stationaryEnv κ t,
    ← (h.hasCondDistrib_obs t).map_eq, ← (h.hasCondDistrib_action t).map_eq,
    klDiv_compProd_right_eq_lintegral, lintegral_map (measurable_klDiv_kernel _ _) hX]
  refine lintegral_congr fun ω ↦ ?_
  by_cases hω : history O A Y t ω ∈ notStoppedSet S t <;>
    simp [hω, Environment.feedback_piecewise, Kernel.piecewise_apply]

omit [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] in
/-- The divergence between the trajectories under `κ` and under `swapEnv κ κ' hS` is the
expected sum of the divergences between the reward kernels at the actions played before
stopping. -/
private lemma klDiv_trajMeasure_swapEnv (hS : MeasurableSet S) :
    klDiv (trajMeasure alg (stationaryEnv κ)) (trajMeasure alg (swapEnv κ κ' hS)) =
      ∫⁻ ω, ∑' t, {ω | history IT.obs IT.action IT.feedback t ω ∈ notStoppedSet S t}.indicator
        (fun ω ↦ klDiv (κ (IT.action t ω)) (κ' (IT.action t ω))) ω
        ∂(trajMeasure alg (stationaryEnv κ)) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv κ)
  have h' := IT.isAlgEnvSeq_trajMeasure alg (swapEnv κ κ' hS)
  have h_chain := h.klDiv_map_trajectory_stepKernel h'
  rw [h.map_trajectory, h'.map_trajectory] at h_chain
  rw [h_chain, lintegral_tsum (f := fun t ↦ {ω | history IT.obs IT.action IT.feedback t ω ∈
      notStoppedSet S t}.indicator fun ω ↦ klDiv (κ (IT.action t ω)) (κ' (IT.action t ω)))
    fun t ↦ (((measurable_klDiv_kernel κ κ').comp
    (IT.measurable_action t)).indicator ((h.measurable_history t)
      (measurableSet_notStoppedSet hS t))).aemeasurable]
  exact tsum_congr fun t ↦ klDiv_compProd_stepKernel_swapEnv h hS t

/-- **Divergence decomposition at a stopping time.** Let `τ` be the hitting time of a measurable
stopping rule `S` by an algorithm run against a stationary environment with reward kernel `κ`, and
suppose that `τ` is almost surely finite. Then the relative entropy between the laws of the history
stopped by `S` under the reward kernels `κ` and `κ'` is at most
`∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`, where `N_a(τ)` is the number of pulls of `a` before `τ`. -/
theorem klDiv_stoppedHistMeasure_le (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂(trajMeasure alg (stationaryEnv κ)),
      hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω ≠ ⊤) :
    klDiv (stoppedHistMeasure alg (stationaryEnv κ) S)
        (stoppedHistMeasure alg (stationaryEnv κ') S) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a
          (ENat.toNat (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω)) ω :
            ℝ≥0∞) ∂(trajMeasure alg (stationaryEnv κ))) * klDiv (κ a) (κ' a) := by
  set τ := hittingAfter (sigmaHistory (IT.obs (𝓞 := Unit) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) S 0 with hτ_def
  have hτm : Measurable τ := measurable_hittingAfter_sigmaHistory IT.measurable_obs
    IT.measurable_action IT.measurable_feedback hS
  -- The stopped history under `swapEnv κ κ' hS` has the same law as under `κ'`.
  have h_swap : stoppedHistMeasure alg (stationaryEnv κ') S =
      stoppedHistMeasure alg (swapEnv κ κ' hS) S :=
    stoppedHistMeasure_congr hS fun _ _ hx ↦ (stepKernel_piecewise_of_mem alg hx).symm
  calc klDiv (stoppedHistMeasure alg (stationaryEnv κ) S)
        (stoppedHistMeasure alg (stationaryEnv κ') S)
      ≤ klDiv (trajMeasure alg (stationaryEnv κ)) (trajMeasure alg (swapEnv κ κ' hS)) := by
        rw [h_swap, stoppedHistMeasure, stoppedHistMeasure]
        exact klDiv_map_le _ _ (measurable_stoppedValue_sigmaHistory IT.measurable_obs
          IT.measurable_action IT.measurable_feedback hτm)
    _ = ∫⁻ ω, ∑ t ∈ range (ENat.toNat (τ ω)), klDiv (κ (IT.action t ω)) (κ' (IT.action t ω))
          ∂(trajMeasure alg (stationaryEnv κ)) := by
        rw [klDiv_trajMeasure_swapEnv hS]
        refine lintegral_congr_ae ?_
        filter_upwards [hτ] with ω hω
        have h_lt (t : ℕ) : history IT.obs IT.action IT.feedback t ω ∈ notStoppedSet S t ↔
            t < ENat.toNat (τ ω) := by
          rw [history_mem_notStoppedSet_iff, ← hτ_def]
          lift τ ω to ℕ using hω with k
          -- `ℕ∞` is `WithTop ℕ`, on which `ENat.toNat` sends `↑k` to `k`.
          exact WithTop.coe_lt_coe
        rw [tsum_eq_sum (s := range (ENat.toNat (τ ω))) fun t ht ↦ by
          simp [Set.indicator, h_lt, mem_range.not.1 ht]]
        exact sum_congr rfl fun t ht ↦ by simp [Set.indicator, h_lt, mem_range.1 ht]
    _ = _ := (LMLExplore.sum_lintegral_pullCount_mul IT.measurable_action
        (Measurable.of_discrete.comp hτm) fun a ↦ klDiv (κ a) (κ' a)).symm

end StoppingTime

end Learning
