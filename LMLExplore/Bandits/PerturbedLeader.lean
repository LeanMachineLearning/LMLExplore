/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Algorithm
public import LMLExplore.Probability.HasCondDistrib
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

In the namespace `LMLExplore.Bandits.PerturbedLeader`, for a run of `perturbedLeaderAlgorithm`:
* `measure_preimage_inter_action_eq`: the run lemma in integral form, for a measurable set `s` of
  pasts and an arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} (⊗ b, F n (past) b) {argmax = a} dP`;
* `measure_action_eq`: `P(A n = a) = E[(⊗ b, F n (past) b) {argmax = a}]`;
* `measure_preimage_inter_action_eq_zero`: if at every past in a measurable set `s` there are an
  arm `b` and a level `c` with `θ a < c ≤ θ b` almost surely, then `a` is almost surely not played
  while the past is in `s`.

The conditional law of the action of round `n` given the past is
`(perturbedLeaderAlgorithm F …).policy n = perturbedLeaderKernel (F n) _ _`, by LML's
`IsAlgEnvSeq.hasCondDistrib_action` and `perturbedLeaderAlgorithm_policy`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 36.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning
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

end PerturbedLeader

end LMLExplore.Bandits
