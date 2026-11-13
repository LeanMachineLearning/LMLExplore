/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Algorithm
public import LMLExplore.Probability.HasCondDistrib
public import LMLExplore.SequentialLearning.SumRewards
public import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Follow-the-perturbed-leader policies

A follow-the-perturbed-leader policy on a finite set of arms `α` computes, at every round `n`, a
probability law `F n (h, o) a` on a linearly ordered type `β` for every arm `a`, from the history
`h` of the first `n` rounds and the current observation `o`. It then samples independent
perturbations `θ a ∼ F n (h, o) a` and plays `argmax θ`, ties being broken by LML's `argmax`
[LS, Algorithm 24]. Thompson sampling with a prior that is independent over the arms is such a
policy, with `F n (h, o) a` the posterior law of the mean of arm `a`.

## Main definitions

* `LMLExplore.Bandits.perturbedLeaderKernel F hF hP`: the kernel `x ↦ (⊗ a, F x a).map argmax`,
  the law of the arm of maximal perturbation for independent perturbations of laws `F x a`.
* `LMLExplore.Bandits.perturbedLeaderAlgorithm F hF hP`: the algorithm whose policy at round `n`
  is `perturbedLeaderKernel (F n)`.

## Main statements

* `perturbedLeaderKernel_apply_singleton`: the probability of playing `a` is the probability that
  `a` is the `argmax` of independent perturbations.
* `measure_pi_argmax_eq_le_add`: for independent perturbations `θ b ∼ μ b`, every arm `b` and
  level `c`, `P(argmax θ = a) ≤ P(θ a ≥ c) + P(θ b < c)`, since the `argmax` has the largest
  perturbation.
* `mul_measure_pi_argmax_eq_and_le_le_mul`: the key inequality of the analysis of
  [LS, Theorem 36.2], [LS, (36.5)]: for independent perturbations `θ b ∼ μ b`, arms `i ≠ j`, a
  level `c` and `G = P(θ j > c)`, `G * P(argmax θ = i, θ i ≤ c) ≤ (1 - G) * P(argmax θ = j)`.
* `measure_pi_argmax_eq_le_inv_sub_one_mul_add`: the per-round inequality of the proof of
  [LS, Theorem 36.2]: with `G_b = P(θ b > c)` and `G_j ≠ 0`, for every threshold `δ`,
  `P(argmax θ = i) ≤ (G_j⁻¹ - 1) P(argmax θ = j) + 𝟙{δ < G_i} P(argmax θ = i) + δ`.

In the namespace `LMLExplore.Bandits.PerturbedLeader`, for a run of `perturbedLeaderAlgorithm`:
* `measure_preimage_inter_action_eq`: the run lemma in integral form, for a measurable set `s` of
  pasts and an arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} (⊗ b, F n (past) b) {argmax = a} dP`;
* `measure_action_eq`: `P(A n = a) = E[(⊗ b, F n (past) b) {argmax = a}]`;
* `measure_preimage_inter_action_eq_zero`: if at every past in a measurable set `s` there are an
  arm `b` and a level `c` with `θ a < c ≤ θ b` almost surely, then `a` is almost surely not played
  while the past is in `s`;
* `measure_action_eq_le_of_ae_ne_zero`: the per-round bound of the proof of [LS, Theorem 36.2],
  `P(A t = i) ≤ E[𝟙{A t = j} (G_j⁻¹ - 1)] + P(A t = i, G_i > δ) + δ` if `G_j ≠ 0` almost surely;
* `lintegral_pullCount_le_of_ae_ne_zero`: [LS, Theorem 36.2] along the run, against any
  environment: with `G_b(t) = P(θ b > c)` for the perturbation laws of round `t`, if `G_j(t) ≠ 0`
  almost surely, then `E[T_i(n)] ≤ 1 + E[∑_{t < n, A t = j} (G_j(t)⁻¹ - 1)] +
  ∑_{t < n} P(A t = i, G_i(t) > 1 / n)`;
* `lintegral_pullCount_le`: [LS, Theorem 36.2] against a stochastic bandit, for perturbation laws
  `Φ a s x` that depend on the history only through the number of pulls `s` of the arm `a` and the
  sum `x` of its rewards: with `G_{a s} = Φ a s (X₀ a + ⋯ + X_{s-1} a) (Ioi c)` in the
  reward-stack model `streamMeasure ν`,
  `E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + ∑_{s < n} P(G_{i s} > 1 / n)`. Conjugate
  posterior updates, as in Thompson sampling with Gaussian or Beta priors, have this form.

The conditional law of the action of round `n` given the past is
`(perturbedLeaderAlgorithm F …).policy n = perturbedLeaderKernel (F n) _ _`, by LML's
`IsAlgEnvSeq.hasCondDistrib_action` and `perturbedLeaderAlgorithm_policy`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 36.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Bandits
open scoped ENNReal

namespace LMLExplore.Bandits

variable {α β X : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [LinearOrder β]
  [MeasurableSpace β] [MeasurableEq β] [MeasurableSup₂ β] [MeasurableSpace X]
  {F : X → α → Measure β} {hF : ∀ a, Measurable fun x ↦ F x a}
  {hP : ∀ x a, IsProbabilityMeasure (F x a)}

/-- The perturbed-leader kernel: for every `x`, the law of `argmax θ` for independent perturbations
`θ a ∼ F x a`, that is, `x ↦ (Measure.pi (F x)).map argmax`. -/
noncomputable def perturbedLeaderKernel (F : X → α → Measure β)
    (hF : ∀ a, Measurable fun x ↦ F x a) (hP : ∀ x a, IsProbabilityMeasure (F x a)) :
    Kernel X α where
  toFun x := (Measure.pi (F x)).map argmax
  measurable' := by
    have h := TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_toMeasure
      (fun a x ↦ (⟨F x a, hP x a⟩ : ProbabilityMeasure β)) fun a ↦ (hF a).subtype_mk
    -- `h` is stated for `(ProbabilityMeasure.pi _).toMeasure`, which is `Measure.pi (F x)` by
    -- `ProbabilityMeasure.toMeasure_pi` (proved by `rfl`)
    exact (Measure.measurable_map _ measurable_argmax).comp h

lemma perturbedLeaderKernel_apply (x : X) :
    perturbedLeaderKernel F hF hP x = (Measure.pi (F x)).map argmax := (rfl)

instance : IsMarkovKernel (perturbedLeaderKernel F hF hP) := by
  refine ⟨fun x ↦ ?_⟩
  have := hP x
  rw [perturbedLeaderKernel_apply]
  infer_instance

/-- The perturbed-leader kernel plays the arm `a` with the probability that `a` is the `argmax` of
independent perturbations of laws `F x b`. -/
lemma perturbedLeaderKernel_apply_singleton [MeasurableSingletonClass α] (x : X) (a : α) :
    perturbedLeaderKernel F hF hP x {a} = Measure.pi (F x) {θ | argmax θ = a} := by
  rw [perturbedLeaderKernel_apply, Measure.map_apply measurable_argmax (measurableSet_singleton a)]
  rfl

omit [MeasurableSpace α] [MeasurableEq β] [MeasurableSup₂ β] in
/-- The `argmax` of independent perturbations `θ b ∼ μ b` has the largest perturbation: for every
arm `b` and every level `c`, `P(argmax θ = a) ≤ P(c ≤ θ a) + P(θ b < c)`. -/
lemma measure_pi_argmax_eq_le_add [TopologicalSpace β] [OpensMeasurableSpace β]
    [OrderClosedTopology β] (μ : α → Measure β) [∀ a, IsProbabilityMeasure (μ a)] (a b : α)
    (c : β) :
    Measure.pi μ {θ | argmax θ = a} ≤ μ a (Set.Ici c) + μ b (Set.Iio c) := by
  rw [← (measurePreserving_eval μ a).measure_preimage measurableSet_Ici.nullMeasurableSet,
    ← (measurePreserving_eval μ b).measure_preimage measurableSet_Iio.nullMeasurableSet]
  have hsub : {θ : α → β | argmax θ = a} ⊆
      Function.eval a ⁻¹' Set.Ici c ∪ Function.eval b ⁻¹' Set.Iio c := by
    intro θ (hθ : argmax θ = a)
    have hba : θ b ≤ θ a := hθ ▸ isMaxOn_argmax θ (Set.mem_univ b)
    by_cases hc : c ≤ θ a
    · exact Or.inl hc
    · exact Or.inr (hba.trans_lt (not_le.mp hc))
  exact (measure_mono hsub).trans (measure_union_le _ _)

open Finset in
omit [MeasurableSpace α] [MeasurableEq β] [MeasurableSup₂ β] in
/-- The key inequality of the analysis of follow-the-perturbed-leader [LS, (36.5)]: for arms
`i ≠ j`, a level `c` and independent perturbations `θ b ∼ μ b`, with `G = P(θ j > c)` the
probability that the perturbation of `j` exceeds `c`,
`G * P(argmax θ = i, θ i ≤ c) ≤ (1 - G) * P(argmax θ = j)`. -/
lemma mul_measure_pi_argmax_eq_and_le_le_mul [TopologicalSpace β] [OrderClosedTopology β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (μ : α → Measure β)
    [∀ a, IsProbabilityMeasure (μ a)] {i j : α} (hij : i ≠ j) (c : β) :
    μ j (Set.Ioi c) * Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c} ≤
      μ j (Set.Iic c) * Measure.pi μ {θ | argmax θ = j} := by
  classical
  -- `i` is the `argmax` with `θ i ≤ c` only if `θ i ≤ c` is the largest perturbation among the
  -- arms other than `j` and `θ j ≤ c`, while `j` is the `argmax` as soon as that same event holds
  -- with `θ j > c` instead; the perturbation of `j` is independent of the others.
  -- the perturbations of the arms other than `j`, and the event that `θ i ≤ c` is the largest
  let R : (α → β) → (↥(univ.erase j) → β) := fun θ k ↦ θ k
  have hi : i ∈ univ.erase j := mem_erase.2 ⟨hij, mem_univ i⟩
  let B : Set (↥(univ.erase j) → β) := {g | g ⟨i, hi⟩ ≤ c ∧ ∀ k, g k ≤ g ⟨i, hi⟩}
  have hB : MeasurableSet B := by
    simp only [B, Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_le (measurable_pi_apply _) measurable_const).inter
      (MeasurableSet.iInter fun k ↦ measurableSet_le (measurable_pi_apply k)
        (measurable_pi_apply _))
  -- the perturbation of `j` is independent of the others
  have hind : IndepFun (fun θ : α → β ↦ θ j) R (Measure.pi μ) := by
    have h0 := (iIndepFun_pi (μ := μ) (X := fun _ y ↦ y) fun _ ↦ aemeasurable_id).indepFun_finset
      {j} (univ.erase j) (by simp) fun b ↦ measurable_pi_apply b
    have hφ : Measurable fun g : ↥({j} : Finset α) → β ↦ g ⟨j, mem_singleton_self j⟩ :=
      measurable_pi_apply _
    exact h0.comp hφ measurable_id
  have hmul {S : Set β} (hS : MeasurableSet S) :
      Measure.pi μ ((fun θ ↦ θ j) ⁻¹' S ∩ R ⁻¹' B) =
        μ j S * Measure.pi μ (R ⁻¹' B) := by
    rw [hind.measure_inter_preimage_eq_mul _ _ hS hB,
      ← (measurePreserving_eval μ j).measure_preimage hS.nullMeasurableSet]
  have h_sub_i : {θ : α → β | argmax θ = i ∧ θ i ≤ c} ⊆
      (fun θ ↦ θ j) ⁻¹' Set.Iic c ∩ R ⁻¹' B := by
    rintro θ ⟨hθ, hc⟩
    have hmax (b : α) : θ b ≤ θ i := hθ ▸ isMaxOn_argmax θ (Set.mem_univ b)
    exact ⟨(hmax j).trans hc, hc, fun k ↦ hmax k⟩
  have h_sub_j : (fun θ ↦ θ j) ⁻¹' Set.Ioi c ∩ R ⁻¹' B ⊆ {θ : α → β | argmax θ = j} := by
    rintro θ ⟨hj, hc, hmax⟩
    -- every arm `b ≠ j` has a perturbation at most `c < θ j`
    have hlt (b : α) (hb : b ≠ j) : θ b < θ j :=
      ((hmax ⟨b, mem_erase.2 ⟨hb, mem_univ b⟩⟩).trans hc).trans_lt hj
    by_contra hne
    exact (hlt _ hne).not_ge (isMaxOn_argmax θ (Set.mem_univ j))
  calc μ j (Set.Ioi c) * Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c}
      ≤ μ j (Set.Ioi c) * (μ j (Set.Iic c) * Measure.pi μ (R ⁻¹' B)) := by
        rw [← hmul measurableSet_Iic]
        gcongr
    _ = μ j (Set.Iic c) * Measure.pi μ ((fun θ ↦ θ j) ⁻¹' Set.Ioi c ∩ R ⁻¹' B) := by
        rw [hmul measurableSet_Ioi, mul_left_comm]
    _ ≤ μ j (Set.Iic c) * Measure.pi μ {θ | argmax θ = j} := by
        gcongr

omit [MeasurableSpace α] [MeasurableEq β] [MeasurableSup₂ β] in
/-- The per-round inequality of the proof of [LS, Theorem 36.2]: for arms `i ≠ j`, a level `c`, a
threshold `δ` and independent perturbations `θ b ∼ μ b`, with `G_b = P(θ b > c)` and `G_j ≠ 0`,
`P(argmax θ = i) ≤ (G_j⁻¹ - 1) P(argmax θ = j) + 𝟙{δ < G_i} P(argmax θ = i) + δ`. The first term
bounds the probability that `i` is played with `θ i ≤ c`, by [LS, (36.5)], and the other two the
probability that `i` is played with `θ i > c`. -/
lemma measure_pi_argmax_eq_le_inv_sub_one_mul_add [TopologicalSpace β] [OrderClosedTopology β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (μ : α → Measure β)
    [∀ a, IsProbabilityMeasure (μ a)] {i j : α} (hij : i ≠ j) (c : β) (δ : ℝ≥0∞)
    (hj : μ j (Set.Ioi c) ≠ 0) :
    Measure.pi μ {θ | argmax θ = i} ≤
      ((μ j (Set.Ioi c))⁻¹ - 1) * Measure.pi μ {θ | argmax θ = j} +
        (if δ < μ i (Set.Ioi c) then Measure.pi μ {θ | argmax θ = i} else 0) + δ := by
  have hsplit : Measure.pi μ {θ | argmax θ = i} ≤ Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c} +
      Measure.pi μ {θ | argmax θ = i ∧ c < θ i} := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro θ (hθ : argmax θ = i)
    rcases le_or_gt (θ i) c with hc | hc
    · exact Or.inl ⟨hθ, hc⟩
    · exact Or.inr ⟨hθ, hc⟩
  -- the event `θ i ≤ c`: [LS, (36.5)], divided by `G_j`, with `(1 - G_j) / G_j = G_j⁻¹ - 1`
  have h_le : Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c} ≤
      ((μ j (Set.Ioi c))⁻¹ - 1) * Measure.pi μ {θ | argmax θ = j} := by
    have hG := measure_ne_top (μ j) (Set.Ioi c)
    have hcoef : (μ j (Set.Ioi c))⁻¹ * μ j (Set.Iic c) = (μ j (Set.Ioi c))⁻¹ - 1 := by
      rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
        ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.mpr hj, mul_one, ENNReal.inv_mul_cancel hj hG]
    calc Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c}
        = (μ j (Set.Ioi c))⁻¹ * (μ j (Set.Ioi c) * Measure.pi μ {θ | argmax θ = i ∧ θ i ≤ c}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hj hG, one_mul]
      _ ≤ (μ j (Set.Ioi c))⁻¹ * (μ j (Set.Iic c) * Measure.pi μ {θ | argmax θ = j}) := by
          exact mul_le_mul_right (mul_measure_pi_argmax_eq_and_le_le_mul μ hij c) _
      _ = ((μ j (Set.Ioi c))⁻¹ - 1) * Measure.pi μ {θ | argmax θ = j} := by rw [← mul_assoc, hcoef]
  -- the event `θ i > c`, which has probability `G_i`
  have h_gt : Measure.pi μ {θ | argmax θ = i ∧ c < θ i} ≤
      (if δ < μ i (Set.Ioi c) then Measure.pi μ {θ | argmax θ = i} else 0) + δ := by
    split_ifs with hδ
    · exact le_add_right (measure_mono fun θ hθ ↦ hθ.1)
    · calc Measure.pi μ {θ | argmax θ = i ∧ c < θ i}
          ≤ Measure.pi μ (Function.eval i ⁻¹' Set.Ioi c) := measure_mono fun θ hθ ↦ hθ.2
        _ = μ i (Set.Ioi c) :=
          (measurePreserving_eval μ i).measure_preimage measurableSet_Ioi.nullMeasurableSet
        _ ≤ 0 + δ := by rw [zero_add]; exact not_lt.mp hδ
  calc Measure.pi μ {θ | argmax θ = i}
      ≤ ((μ j (Set.Ioi c))⁻¹ - 1) * Measure.pi μ {θ | argmax θ = j} +
        ((if δ < μ i (Set.Ioi c) then Measure.pi μ {θ | argmax θ = i} else 0) + δ) :=
        hsplit.trans (add_le_add h_le h_gt)
    _ = _ := (add_assoc _ _ _).symm

variable {𝓞 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓨]
  {F : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → Measure β} {hF : ∀ n a, Measurable fun x ↦ F n x a}
  {hP : ∀ n x a, IsProbabilityMeasure (F n x a)}

/-- The follow-the-perturbed-leader algorithm [LS, Algorithm 24]: at round `n`, with history `h`
and observation `o`, it samples independent perturbations `θ a ∼ F n (h, o) a` and plays
`argmax θ`, an arm of maximal perturbation with ties broken by LML's `argmax`. -/
noncomputable def perturbedLeaderAlgorithm (F : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → Measure β)
    (hF : ∀ n a, Measurable fun x ↦ F n x a) (hP : ∀ n x a, IsProbabilityMeasure (F n x a)) :
    Algorithm 𝓞 α 𝓨 where
  policy n := perturbedLeaderKernel (F n) (hF n) (hP n)

@[simp]
lemma perturbedLeaderAlgorithm_policy (n : ℕ) :
    (perturbedLeaderAlgorithm F hF hP).policy n = perturbedLeaderKernel (F n) (hF n) (hP n) :=
  (rfl)

namespace PerturbedLeader

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {env : Environment 𝓞 α 𝓨}

/-- The run lemma of a follow-the-perturbed-leader algorithm: for a measurable set `s` of pasts
(history and observation) of round `n` and an arm `a`, the probability that the past is in `s` and
`a` is played at round `n` is the integral over `s` of the probability that `a` is the `argmax` of
independent perturbations of laws `F n (past) b`. -/
lemma measure_preimage_inter_action_eq
    (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) env P) (n : ℕ)
    {s : Set (Hist 𝓞 α 𝓨 n × 𝓞)} (hs : MeasurableSet s) (a : α) :
    P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s ∩ A n ⁻¹' {a}) =
      ∫⁻ ω in (fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s,
        Measure.pi (F n (history O A Y n ω, O n ω)) {θ | argmax θ = a} ∂P := by
  rw [(h.hasCondDistrib_action n).measure_preimage_inter_eq_setLIntegral hs
    (measurableSet_singleton a)]
  simp_rw [perturbedLeaderAlgorithm_policy, perturbedLeaderKernel_apply_singleton]

/-- Along a run of a follow-the-perturbed-leader algorithm, the probability of playing `a` at
round `n` is the expected probability that `a` is the `argmax` of independent perturbations of laws
`F n (past) b`. -/
lemma measure_action_eq (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) env P) (n : ℕ)
    (a : α) :
    P (A n ⁻¹' {a}) =
      ∫⁻ ω, Measure.pi (F n (history O A Y n ω, O n ω)) {θ | argmax θ = a} ∂P := by
  simpa using measure_preimage_inter_action_eq h n MeasurableSet.univ a

/-- Along a run of a follow-the-perturbed-leader algorithm, if for every past in a measurable set
`s` of pasts of round `n` there is an arm `b` and a level `c` such that the perturbation of `a` is
almost surely below `c` and that of `b` almost surely at least `c`, then `a` is almost surely not
played at round `n` while the past is in `s`. -/
lemma measure_preimage_inter_action_eq_zero [TopologicalSpace β] [OpensMeasurableSpace β]
    [OrderClosedTopology β] (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) env P)
    (n : ℕ) {s : Set (Hist 𝓞 α 𝓨 n × 𝓞)} (hs : MeasurableSet s) (a : α)
    (hab : ∀ x ∈ s, ∃ b c, F n x a (Set.Ici c) = 0 ∧ F n x b (Set.Iio c) = 0) :
    P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s ∩ A n ⁻¹' {a}) = 0 := by
  have hX : Measurable fun ω ↦ (history O A Y n ω, O n ω) :=
    (h.measurable_history n).prodMk (h.measurable_obs n)
  rw [measure_preimage_inter_action_eq h n hs a,
    setLIntegral_congr_fun (hX hs) (g := fun _ ↦ 0) fun ω hω ↦ ?_]
  · simp
  obtain ⟨b, c, hac, hbc⟩ := hab _ hω
  have := hP n (history O A Y n ω, O n ω)
  have hle := measure_pi_argmax_eq_le_add (F n (history O A Y n ω, O n ω)) a b c
  rwa [hac, hbc, add_zero, nonpos_iff_eq_zero] at hle

omit [IsFiniteMeasure P] in
/-- The per-round bound of the proof of [LS, Theorem 36.2] along a run of a
follow-the-perturbed-leader algorithm, against any environment. For arms `i ≠ j`, a level `c`, a
threshold `δ` and a round `t`, write `G_b = P(θ b > c)` for the perturbation laws of round `t`. If
`G_j ≠ 0` almost surely, then `P(A t = i) ≤ E[𝟙{A t = j} (G_j⁻¹ - 1)] + P(A t = i, G_i > δ) + δ`. -/
lemma measure_action_eq_le_of_ae_ne_zero [IsProbabilityMeasure P] [TopologicalSpace β]
    [OrderClosedTopology β] [SecondCountableTopology β] [OpensMeasurableSpace β]
    (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) env P) {i j : α} (hij : i ≠ j)
    (c : β) (δ : ℝ≥0∞) (t : ℕ)
    (hj : ∀ᵐ ω ∂P, F t (history O A Y t ω, O t ω) j (Set.Ioi c) ≠ 0) :
    P (A t ⁻¹' {i}) ≤
      ∫⁻ ω in A t ⁻¹' {j}, (F t (history O A Y t ω, O t ω) j (Set.Ioi c))⁻¹ - 1 ∂P +
        P {ω | A t ω = i ∧ δ < F t (history O A Y t ω, O t ω) i (Set.Ioi c)} + δ := by
  -- `G a x` is the probability that the perturbation of `a` exceeds `c` at the past `x`
  set G : α → Hist 𝓞 α 𝓨 t × 𝓞 → ℝ≥0∞ := fun a x ↦ F t x a (Set.Ioi c)
  have hG a : Measurable (G a) := (Measure.measurable_coe measurableSet_Ioi).comp (hF t a)
  set X : Ω → Hist 𝓞 α 𝓨 t × 𝓞 := fun ω ↦ (history O A Y t ω, O t ω)
  have hX : Measurable X := (h.measurable_history t).prodMk (h.measurable_obs t)
  set κ := perturbedLeaderKernel (F t) (hF t) (hP t)
  have hκ (a : α) (x : Hist 𝓞 α 𝓨 t × 𝓞) : κ x {a} = Measure.pi (F t x) {θ | argmax θ = a} :=
    perturbedLeaderKernel_apply_singleton x a
  have hcd : HasCondDistrib (A t) X κ P := h.hasCondDistrib_action t
  set s : Set (Hist 𝓞 α 𝓨 t × 𝓞) := {x | δ < G i x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (hG i)
  have hf₁ : Measurable fun ω ↦ ((G j (X ω))⁻¹ - 1) * κ (X ω) {j} :=
    ((((hG j).comp hX).inv).sub_const 1).mul
      ((κ.measurable_coe (measurableSet_singleton j)).comp hX)
  -- the first term: `P(A t = j | past) = κ (past) {j}`
  have h₁ : ∫⁻ ω, ((G j (X ω))⁻¹ - 1) * κ (X ω) {j} ∂P =
      ∫⁻ ω in A t ⁻¹' {j}, (G j (X ω))⁻¹ - 1 ∂P := by
    have hg : Measurable fun q : (Hist 𝓞 α 𝓨 t × 𝓞) × α ↦
        ({j} : Set α).indicator (fun _ ↦ (G j q.1)⁻¹ - 1) q.2 :=
      measurable_from_prod_countable_left fun a ↦ by
        by_cases ha : a = j
        · simpa [ha] using (hG j).inv.sub_const 1
        · simp [ha]
    have := hcd.lintegral_comp_prodMk_eq_lintegral_lintegral hg
    simp_rw [lintegral_indicator_const (measurableSet_singleton j)] at this
    rw [← this, ← lintegral_indicator (h.measurable_action t (measurableSet_singleton j))]
    refine lintegral_congr fun ω ↦ ?_
    by_cases hω : A t ω = j <;> simp [hω]
  -- the second term: the run lemma on the set of pasts at which `δ < G_i`
  have h₂ : ∫⁻ ω, (X ⁻¹' s).indicator (fun ω ↦ κ (X ω) {i}) ω ∂P =
      P {ω | A t ω = i ∧ δ < G i (X ω)} := by
    rw [lintegral_indicator (hX hs), ← hcd.measure_preimage_inter_eq_setLIntegral hs
      (measurableSet_singleton i)]
    congr 1 with ω
    simp [s, X, and_comm]
  -- integrate the per-past inequality `measure_pi_argmax_eq_le_inv_sub_one_mul_add`
  calc P (A t ⁻¹' {i}) = ∫⁻ ω, κ (X ω) {i} ∂P := by
        simpa [hκ] using measure_action_eq h t i
    _ ≤ ∫⁻ ω, (((G j (X ω))⁻¹ - 1) * κ (X ω) {j} +
          (X ⁻¹' s).indicator (fun ω ↦ κ (X ω) {i}) ω + δ) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hj] with ω hω
        have := hP t (X ω)
        simpa [hκ, G, s, Set.indicator_apply] using
          measure_pi_argmax_eq_le_inv_sub_one_mul_add (F t (X ω)) hij c δ hω
    _ = ∫⁻ ω in A t ⁻¹' {j}, (G j (X ω))⁻¹ - 1 ∂P + P {ω | A t ω = i ∧ δ < G i (X ω)} + δ := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left hf₁, lintegral_const,
          measure_univ, mul_one, h₁, h₂]

omit [IsFiniteMeasure P] in
/-- **[LS, Theorem 36.2], in terms of the perturbation laws along the run.** For a run of a
follow-the-perturbed-leader algorithm against any environment, arms `i ≠ j`, a level `c` and a
horizon `n`, write `G_b(t) = P(θ b > c)` for the perturbation laws of round `t`. If `G_j(t) ≠ 0`
almost surely at every round `t < n`, then
`E[T_i(n)] ≤ 1 + E[∑_{t < n, A t = j} (G_j(t)⁻¹ - 1)] + ∑_{t < n} P(A t = i, G_i(t) > 1 / n)`. -/
theorem lintegral_pullCount_le_of_ae_ne_zero [DecidableEq α] [IsProbabilityMeasure P]
    [TopologicalSpace β] [OrderClosedTopology β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) env P)
    {i j : α} (hij : i ≠ j) (c : β) (n : ℕ)
    (hj : ∀ t < n, ∀ᵐ ω ∂P, F t (history O A Y t ω, O t ω) j (Set.Ioi c) ≠ 0) :
    ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤
      1 + ∑ t ∈ Finset.range n,
          ∫⁻ ω in A t ⁻¹' {j}, (F t (history O A Y t ω, O t ω) j (Set.Ioi c))⁻¹ - 1 ∂P +
        ∑ t ∈ Finset.range n,
          P {ω | A t ω = i ∧ (n : ℝ≥0∞)⁻¹ < F t (history O A Y t ω, O t ω) i (Set.Ioi c)} := by
  -- sum the per-round bounds over the rounds: the terms `1 / n` add up to at most `1`
  calc ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P = ∑ t ∈ Finset.range n, P (A t ⁻¹' {i}) :=
        lintegral_pullCount_eq_sum h.measurable_action i n
    _ ≤ ∑ t ∈ Finset.range n,
          (∫⁻ ω in A t ⁻¹' {j}, (F t (history O A Y t ω, O t ω) j (Set.Ioi c))⁻¹ - 1 ∂P +
            P {ω | A t ω = i ∧ (n : ℝ≥0∞)⁻¹ < F t (history O A Y t ω, O t ω) i (Set.Ioi c)} +
              (n : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_sum fun t ht ↦
          measure_action_eq_le_of_ae_ne_zero h hij c _ t (hj t (Finset.mem_range.mp ht))
    _ = n * (n : ℝ≥0∞)⁻¹ + ∑ t ∈ Finset.range n,
          ∫⁻ ω in A t ⁻¹' {j}, (F t (history O A Y t ω, O t ω) j (Set.Ioi c))⁻¹ - 1 ∂P +
        ∑ t ∈ Finset.range n,
          P {ω | A t ω = i ∧ (n : ℝ≥0∞)⁻¹ < F t (history O A Y t ω, O t ω) i (Set.Ioi c)} := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact ENNReal.mul_inv_le_one _

omit [IsFiniteMeasure P] in
/-- **[LS, Theorem 36.2].** Consider a run of a follow-the-perturbed-leader algorithm against the
stochastic bandit `Environment.bandit ν`, whose perturbation law of each arm `a` depends on the
history only through the number of pulls `s` of `a` and the sum `x` of its rewards, as
`Φ a s x`. For arms `i ≠ j`, a level `c` and a horizon `n`, write
`G_{a s} = Φ a s (X₀ a + ⋯ + X_{s-1} a) (Ioi c)` in the reward-stack model `streamMeasure ν`, where
`X_k a` is the `(k + 1)`-th reward of arm `a`. Then
`E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + ∑_{s < n} P(G_{i s} > 1 / n)`.

[LS] takes `j` optimal and `c = μ_j - ε`; the inequality holds for all arms `i ≠ j` and all levels
`c`. -/
theorem lintegral_pullCount_le [DecidableEq α] [IsProbabilityMeasure P] [TopologicalSpace β]
    [OrderClosedTopology β] [SecondCountableTopology β] [OpensMeasurableSpace β]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {O : ℕ → Ω → Unit} {Y : ℕ → Ω → ℝ}
    {F : (n : ℕ) → Hist Unit α ℝ n × Unit → α → Measure β} {hF : ∀ n a, Measurable fun x ↦ F n x a}
    {hP : ∀ n x a, IsProbabilityMeasure (F n x a)}
    (h : IsAlgEnvSeq O A Y (perturbedLeaderAlgorithm F hF hP) (Environment.bandit ν) P)
    (Φ : α → ℕ → ℝ → Measure β) (hΦ : ∀ a s, Measurable (Φ a s))
    (hFΦ : ∀ t x a, F t x a = Φ a (pullCount' t x.1 a) (sumRewards' t x.1 a))
    {i j : α} (hij : i ≠ j) (c : β) (n : ℕ) :
    ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤
      1 + ∑ s ∈ Finset.range n,
          ∫⁻ x, (Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1 ∂(streamMeasure ν) +
        ∑ s ∈ Finset.range n,
          streamMeasure ν {x | (n : ℝ≥0∞)⁻¹ < Φ i s (∑ k ∈ Finset.range s, x k i) (Set.Ioi c)} := by
  have hG (a : α) : Measurable fun q : ℕ × ℝ ↦ Φ a q.1 q.2 (Set.Ioi c) :=
    measurable_from_prod_countable_right fun s ↦
      (Measure.measurable_coe measurableSet_Ioi).comp (hΦ a s)
  -- along the run, the perturbation law of `a` is `Φ a` at the pull count and sum of rewards of `a`
  have hF_run (t : ℕ) (ω : Ω) (a : α) : F t (history O A Y t ω, O t ω) a =
      Φ a (pullCount A a t ω) (sumRewards A Y a t ω) := by
    rw [hFΦ, pullCount_eq_pullCount' (O := O) (R' := Y), sumRewards_eq_sumRewards' (O := O)]
  -- if some `G_{j s}` vanishes with positive probability, the bound is trivial
  by_cases hfin : ∑ s ∈ Finset.range n,
      ∫⁻ x, (Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1 ∂(streamMeasure ν) = ⊤
  · simp [hfin]
  -- otherwise every `G_{j s}` with `s < n` is almost surely positive in the stream model, hence so
  -- is the probability `G_j(t)` along the run at every round `t < n`
  have hpos : ∀ t < n, ∀ᵐ ω ∂P, F t (history O A Y t ω, O t ω) j (Set.Ioi c) ≠ 0 := by
    have hstream : ∀ s ∈ Finset.range n, ∀ᵐ x ∂(streamMeasure ν),
        Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c) ≠ 0 := by
      intro s hs
      have hne : ∫⁻ x, (Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1
          ∂(streamMeasure ν) ≠ ⊤ := fun htop ↦ hfin (ENNReal.sum_eq_top.mpr ⟨s, hs, htop⟩)
      have hmeas : Measurable fun x : ℕ → α → ℝ ↦
          (Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1 :=
        (((Measure.measurable_coe measurableSet_Ioi).comp (hΦ j s)).comp
          (by fun_prop : Measurable fun x : ℕ → α → ℝ ↦ ∑ k ∈ Finset.range s, x k j)).inv.sub_const
          1
      filter_upwards [ae_lt_top hmeas hne] with x hx h0
      simp [h0] at hx
    have hnull : streamMeasure ν
        {x | ∃ s < n, Φ j s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c) = 0} = 0 := by
      have hall := (Filter.eventually_all_finset _).2 hstream
      rw [ae_iff] at hall
      refine measure_mono_null (fun x ⟨s, hs, h0⟩ ↦ ?_) hall
      simpa using ⟨s, hs, h0⟩
    have hrun := measure_exists_lt_pullCount_sumRewards_le h j n
      (fun s y ↦ Φ j s y (Set.Ioi c) = 0)
    intro t ht
    rw [ae_iff]
    refine measure_mono_null (fun ω hω ↦ ?_) (nonpos_iff_eq_zero.mp (hrun.trans hnull.le))
    exact ⟨t, ht, by simpa [hF_run] using hω⟩
  -- the bound of `lintegral_pullCount_le_of_ae_ne_zero`, transferred to the reward stack
  refine (lintegral_pullCount_le_of_ae_ne_zero h hij c n hpos).trans ?_
  simp_rw [hF_run]
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · exact sum_setLIntegral_action_eq_pullCount_sumRewards_le h j n
      (g := fun s y ↦ (Φ j s y (Set.Ioi c))⁻¹ - 1) ((hG j).inv.sub_const 1)
  · exact sum_measure_action_eq_and_pullCount_sumRewards_le h i n
      (p := fun s y ↦ (n : ℝ≥0∞)⁻¹ < Φ i s y (Set.Ioi c))
      (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hG i)))

end PerturbedLeader

end LMLExplore.Bandits
