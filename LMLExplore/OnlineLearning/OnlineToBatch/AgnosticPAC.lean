/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import LMLExplore.OnlineLearning.Learner.Basic
public import LMLExplore.OnlineLearning.OnlineToBatch.Validation
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import Mathlib.MeasureTheory.Constructions.Pi
import LMLExplore.Algebra.Order.BigOperators.Expect
import LMLExplore.Probability.ProductMeasure
import LMLExplore.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Agnostic PAC learning from online learning

A class of losses `{f x · | x ∈ V}` on a measurable space `Z` of data is **agnostic PAC
learnable** [Ora, Definition 3.16] if some learning algorithm, a measurable map from samples of
size `n` to `V`, returns from `n` independent data with a common law `ρ` a point whose risk
`∫ z, f x z ∂ρ` exceeds that of every point of `V` by at most `ε`, with probability at least
`1 - δ`, as soon as `n` is at least a sample size that depends on `ε` and `δ` but not on `ρ`.
"Agnostic" refers to the absence of any assumption on `ρ`, and on the best risk over `V`.

This file proves that an online learner with a sublinear regret makes the class learnable, by the
online-to-batch conversion with a validation sample [Ora, §3.2]. Let `A` be a deterministic online
learner with plays in `V` and feedback in `Z`, whose regret against every `u ∈ V` on the losses
`f (·) (z t)` of every sequence of data is at most `R u n` after `n` rounds. On a sample of size
`n`, with `k = n / 2`:

* `A` is run on the first half of the sample, the training data, and plays `x 0, …, x (k - 1)`
  (`OnlineLearner.trainingPlay`);
* the algorithm returns the play with the smallest cumulative loss on the second half of the
  sample, the validation data (`OnlineLearner.validationPlay`).

The online-to-batch conversion with high probability bounds the average risk of the plays, and
the selection on a validation sample (`measureReal_exists_add_sqrt_lt_le`) bounds the risk of the
selected play by the smallest risk of the plays, hence by their average. For every `u ∈ V` and
`δ > 0`, with probability at least `1 - 2 δ`, the selected play has risk at most
`F u + R u k / k + √(2 log (1 / δ) / k) + √(2 log (2 k / δ) / k)`. For an even sample size `n`,
this is `F u + 2 R u (n / 2) / n + 2 √(log (1 / δ) / n) + 2 √(log (n / δ) / n)`, at most the bound
`F u + 2 R u (n / 2) / n + 8 √(log (n / δ) / n)` of [Ora, §3.2]. A regret bound that is sublinear
uniformly over `V` then gives agnostic PAC learnability, with no convexity of the losses or of
`V`.

The finite classes are agnostic PAC learnable by empirical risk minimization, by the same
selection bound on the whole sample (`Set.Finite.agnosticPACLearnable`).

## Main definitions

* `LMLExplore.OnlineLearning.AgnosticPACLearnable f V`: agnostic PAC learnability of the class of
  losses `{f x · | x ∈ V}`.
* `LMLExplore.OnlineLearning.validationLoss f s y`: the cumulative loss of `y` on the second half
  of the sample `s`.
* `LMLExplore.OnlineLearning.OnlineLearner.trainingPlay A s t`: the play of round `t < n / 2` of
  `A` on the first half of the sample `s`.
* `LMLExplore.OnlineLearning.OnlineLearner.validationPlay A f s`: the training play with the
  smallest validation loss.

## Main statements

* `OnlineLearner.HasRegretBound.measureReal_lt_integral_validationPlay_le`: the risk bound of the
  validation-selected play, with probability at least `1 - 2 δ`.
* `OnlineLearner.HasRegretBound.agnosticPACLearnable`: an online learner with a regret bound that
  is sublinear uniformly over `V` makes the class agnostic PAC learnable.
* `Set.Finite.agnosticPACLearnable`: finite classes are agnostic PAC learnable.

## Implementation notes

The samples of size `n` are the maps `Fin n → Z`, with the product law
`Measure.pi fun _ : Fin n ↦ ρ`. The proofs run on the sequence space `ℕ → Z` with the product
law `Measure.infinitePi fun _ ↦ ρ`, whose first `n` coordinates have the law of a sample
(`MeasureTheory.measurePreserving_initSeg`), and the filtration of the strict past of the
coordinates. The selections use LML's measurable `argmin` over the finite types of candidates.

## References

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Definition 3.16, Theorem 3.17 and §3.2.
-/

public section

open MeasureTheory ProbabilityTheory Real Finset Filter Topology

namespace LMLExplore.OnlineLearning

variable {α Z : Type*} {f : α → Z → ℝ} {V : Set α}

/-! ### The validation-selected play of an online learner -/

/-- The **validation loss** of `y` on a sample `s` of size `n`: its cumulative loss
`∑ j < n / 2, f y (s (n / 2 + j))` on the second half of the sample. For an odd `n`, the last
point of the sample is not used. -/
def validationLoss {n : ℕ} (f : α → Z → ℝ) (s : Fin n → Z) (y : α) : ℝ :=
  ∑ j : Fin (n / 2), f y (s (Fin.castLE (by omega) (Fin.natAdd (n / 2) j)))

lemma validationLoss_def {n : ℕ} (s : Fin n → Z) (y : α) :
    validationLoss f s y =
      ∑ j : Fin (n / 2), f y (s (Fin.castLE (by omega) (Fin.natAdd (n / 2) j))) :=
  (rfl)

/-- On the first `n` terms of a sequence `ω`, the validation loss is the cumulative loss on the
terms `ω (n / 2 + j)`, `j < n / 2`. -/
@[simp]
lemma validationLoss_initSeg {n : ℕ} (ω : ℕ → Z) (y : α) :
    validationLoss f (initSeg n ω) y = ∑ j ∈ range (n / 2), f y (ω (n / 2 + j)) := by
  rw [validationLoss_def, ← Fin.sum_univ_eq_sum_range]
  simp [add_comm]

namespace OnlineLearner

variable (A : OnlineLearner Unit Z α) {n : ℕ}

/-- The **training play** of round `t < n / 2` of the learner `A` on a sample `s` of size `n`: the
play of `A` fed with the first `t` points `s 0, …, s (t - 1)` of the sample, which belong to its
first half. -/
def trainingPlay (s : Fin n → Z) (t : Fin (n / 2)) : α :=
  A.play t (fun r ↦ ((), s (Fin.castLE (by have := t.isLt; omega) r))) ()

lemma trainingPlay_def (s : Fin n → Z) (t : Fin (n / 2)) :
    A.trainingPlay s t =
      A.play t (fun r ↦ ((), s (Fin.castLE (by have := t.isLt; omega) r))) () :=
  (rfl)

/-- On the first `n` terms of a sequence `ω`, the training plays are the plays of the run of `A`
against the feedback `ω`. -/
@[simp]
lemma trainingPlay_initSeg (ω : ℕ → Z) (t : Fin (n / 2)) :
    A.trainingPlay (initSeg n ω) t = A.run (fun _ ↦ ()) ω t := by
  simp [trainingPlay_def, run_def]

/-- The **validation-selected play** of the learner `A` on a sample `s` of size `n` [Ora, §3.2]:
among the training plays `A.trainingPlay s t`, `t < n / 2`, on the first half of the sample, one
with the smallest validation loss on the second half. For `n < 2` there is no training play, and
it is the first play of `A`. -/
noncomputable def validationPlay (f : α → Z → ℝ) (s : Fin n → Z) : α :=
  if h : n / 2 = 0 then A.play 0 Fin.elim0 () else
    haveI : Nonempty (Fin (n / 2)) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    A.trainingPlay s (argmin fun t ↦ validationLoss f s (A.trainingPlay s t))

/-- For `n < 2` there is no training play, and the validation-selected play is the first play of
`A`. -/
lemma validationPlay_of_div_two_eq_zero (h : n / 2 = 0) (s : Fin n → Z) :
    A.validationPlay f s = A.play 0 Fin.elim0 () := by
  simp only [validationPlay, h, ↓reduceDIte]

lemma validationPlay_eq [Nonempty (Fin (n / 2))] (s : Fin n → Z) :
    A.validationPlay f s =
      A.trainingPlay s (argmin fun t ↦ validationLoss f s (A.trainingPlay s t)) := by
  simp only [validationPlay, (Fin.pos_iff_nonempty.2 ‹_›).ne', ↓reduceDIte]

/-- The validation-selected play has the smallest validation loss among the training plays. -/
lemma validationLoss_validationPlay_le [Nonempty (Fin (n / 2))] (s : Fin n → Z)
    (t : Fin (n / 2)) :
    validationLoss f s (A.validationPlay f s) ≤ validationLoss f s (A.trainingPlay s t) := by
  rw [validationPlay_eq]
  exact isMinOn_univ_iff.1 (isMinOn_argmin fun t ↦ validationLoss f s (A.trainingPlay s t)) t

/-- The validation-selected play is a play of `A`, hence lies in every set containing them. -/
lemma validationPlay_mem (hAV : ∀ t h, A.play t h () ∈ V) (s : Fin n → Z) :
    A.validationPlay f s ∈ V := by
  rcases eq_or_ne (n / 2) 0 with h | h
  · rw [A.validationPlay_of_div_two_eq_zero h]
    exact hAV _ _
  · have : Nonempty (Fin (n / 2)) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    rw [validationPlay_eq]
    exact hAV _ _

end OnlineLearner

/-! ### Measurability -/

variable [MeasurableSpace α] [MeasurableSpace Z]

lemma measurable_validationLoss (hf : Measurable (Function.uncurry f)) {n : ℕ}
    {y : (Fin n → Z) → α} (hy : Measurable y) : Measurable fun s ↦ validationLoss f s (y s) :=
  Finset.measurable_sum _ fun _ _ ↦ hf.comp (hy.prodMk (measurable_pi_apply _))

namespace OnlineLearner

variable (A : OnlineLearner Unit Z α) {n : ℕ}

lemma measurable_trainingPlay (hA : ∀ t, Measurable fun h : Fin t → Unit × Z ↦ A.play t h ())
    (t : Fin (n / 2)) : Measurable fun s : Fin n → Z ↦ A.trainingPlay s t :=
  (hA t).comp (Measurable.of_eval fun _ ↦ measurable_const.prodMk (measurable_pi_apply _))

/-- For a jointly measurable loss and a learner whose plays are measurable functions of the past
feedback, the validation-selected play is a measurable function of the sample. -/
theorem measurable_validationPlay (hf : Measurable (Function.uncurry f))
    (hA : ∀ t, Measurable fun h : Fin t → Unit × Z ↦ A.play t h ()) :
    Measurable (A.validationPlay f (n := n)) := by
  rcases eq_or_ne (n / 2) 0 with h | h
  · rw [funext (A.validationPlay_of_div_two_eq_zero (f := f) h)]
    exact measurable_const
  have : Nonempty (Fin (n / 2)) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
  have hk : Measurable fun s : Fin n → Z ↦
      argmin fun t ↦ validationLoss f s (A.trainingPlay s t) :=
    measurable_argmin.comp (Measurable.of_eval fun t ↦
      measurable_validationLoss hf (A.measurable_trainingPlay hA t))
  rw [funext (A.validationPlay_eq (f := f))]
  exact (measurable_from_prod_countable_left
    (f := fun p : (Fin n → Z) × Fin (n / 2) ↦ A.trainingPlay p.1 p.2)
    fun t ↦ A.measurable_trainingPlay hA t).comp (measurable_id.prodMk hk)

end OnlineLearner

/-! ### Agnostic PAC learnability -/

/-- **Agnostic PAC learnability** [Ora, Definition 3.16] of the class of losses `{f x · | x ∈ V}`:
there is a learning algorithm `A`, made of measurable maps `A n` from the samples `Fin n → Z` of
size `n` to `V`, such that for all `ε, δ > 0` there is a sample size `N` with the following
property. For every `n ≥ N` and every probability measure `ρ` on `Z`, on a sample of `n`
independent data with law `ρ`, the risk `∫ z, f (A n s) z ∂ρ` of the returned point exceeds the
risk `∫ z, f u z ∂ρ` of some `u ∈ V` by more than `ε` with probability at most `δ`.

The sample size `N` does not depend on `ρ`. The risks are Bochner integrals, as is meaningful for
bounded measurable losses. -/
def AgnosticPACLearnable (f : α → Z → ℝ) (V : Set α) : Prop :=
  ∃ A : (n : ℕ) → (Fin n → Z) → α, (∀ n, Measurable (A n)) ∧ (∀ n s, A n s ∈ V) ∧
    ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ],
      (Measure.pi fun _ : Fin n ↦ ρ).real
        {s | ∃ u ∈ V, ∫ z, f u z ∂ρ + ε < ∫ z, f (A n s) z ∂ρ} ≤ δ

lemma agnosticPACLearnable_iff : AgnosticPACLearnable f V ↔
    ∃ A : (n : ℕ) → (Fin n → Z) → α, (∀ n, Measurable (A n)) ∧ (∀ n s, A n s ∈ V) ∧
      ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ],
        (Measure.pi fun _ : Fin n ↦ ρ).real
          {s | ∃ u ∈ V, ∫ z, f u z ∂ρ + ε < ∫ z, f (A n s) z ∂ρ} ≤ δ :=
  Iff.rfl

/-- For every `c`, `a > 0` and `ε > 0`, eventually `√(c / k) < ε` and `√(2 log (a k) / k) < ε`:
the deviation terms of the risk bounds vanish as the sample size grows. -/
private lemma eventually_sqrt_lt (c a : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, √(c / k) < ε ∧ √(2 * log (a * k) / k) < ε := by
  have hsqrt {g : ℕ → ℝ} (hg : Tendsto g atTop (𝓝 0)) : ∀ᶠ k in atTop, √(g k) < ε := by
    have h := (continuous_sqrt.tendsto 0).comp hg
    rw [sqrt_zero] at h
    exact h.eventually (gt_mem_nhds hε)
  have hlog : Tendsto (fun k : ℕ ↦ log k / k) atTop (𝓝 0) := by
    have h :=
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
    simp only [pow_one, one_mul, add_zero] at h
    exact h
  filter_upwards [hsqrt (tendsto_const_div_atTop_nhds_zero_nat c),
    hsqrt (g := fun k : ℕ ↦ 2 * (log a / k + log k / k)) (by simpa using
      ((tendsto_const_div_atTop_nhds_zero_nat (log a)).add hlog).const_mul 2),
    eventually_ge_atTop 1] with k h₁ h₂ hk
  refine ⟨h₁, ?_⟩
  rw [← add_div, ← mul_div_assoc] at h₂
  rwa [log_mul ha.ne' (by positivity)]

/-- For a jointly measurable loss `f`, the risk `∫ z, f (g s) z ∂ρ` of a measurable choice `g s` is
a measurable function of `s`. -/
private lemma measurable_integral_comp {β : Type*} [MeasurableSpace β]
    (hf : Measurable (Function.uncurry f)) (ρ : Measure Z) [SFinite ρ] {g : β → α}
    (hg : Measurable g) : Measurable fun s ↦ ∫ z, f (g s) z ∂ρ :=
  (hf.stronglyMeasurable.integral_prod_right (ν := ρ)).measurable.comp hg

namespace OnlineLearner.HasRegretBound

variable {A : OnlineLearner Unit Z α} {R : α → ℕ → ℝ}

/-- **Online-to-batch with a validation sample** [Ora, §3.2]. Let `A` be an online learner with
data in `Z` as feedback, whose plays are measurable functions of the past data, and whose regret
against `u ∈ V` on the losses `f (·) (z t)` is at most `R u n` after `n` rounds, for every sequence
of data. Let `f` be jointly measurable with values in `[0, 1]`, `ρ` a probability measure on `Z`,
`n ≥ 2`, `k = n / 2` and `δ > 0`. On a sample of `n` independent data with law `ρ`, the risk of
the validation-selected play exceeds
`∫ z, f u z ∂ρ + R u k / k + √(2 log (1 / δ) / k) + √(2 log (2 k / δ) / k)`
with probability at most `2 δ`.

For an even `n`, the bound is
`∫ z, f u z ∂ρ + 2 R u (n / 2) / n + 2 √(log (1 / δ) / n) + 2 √(log (n / δ) / n)`. -/
theorem measureReal_lt_integral_validationPlay_le
    (hreg : A.HasRegretBound (fun z y ↦ f y z) (fun _ _ ↦ True) V fun n _ _ u ↦ R u n)
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1)
    (hA : ∀ t, Measurable fun h : Fin t → Unit × Z ↦ A.play t h ())
    (ρ : Measure Z) [IsProbabilityMeasure ρ] {u : α} (hu : u ∈ V) {n : ℕ} (hn : 2 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n ↦ ρ).real {s | ∫ z, f u z ∂ρ + R u (n / 2) / (n / 2 : ℕ) +
      √(2 * log (1 / δ) / (n / 2 : ℕ)) + √(2 * log (2 * (n / 2 : ℕ) / δ) / (n / 2 : ℕ)) <
        ∫ z, f (A.validationPlay f s) z ∂ρ} ≤ 2 * δ := by
  have hk : n / 2 ≠ 0 := by omega
  have : Nonempty (Fin (n / 2)) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  -- The proof runs on the sequence space, whose first `n` terms have the law of a sample, with
  -- the filtration `ℱ` of the strict past of the coordinates.
  have hmeas : MeasurableSet {s : Fin n → Z | ∫ z, f u z ∂ρ + R u (n / 2) / (n / 2 : ℕ) +
      √(2 * log (1 / δ) / (n / 2 : ℕ)) + √(2 * log (2 * (n / 2 : ℕ) / δ) / (n / 2 : ℕ)) <
        ∫ z, f (A.validationPlay f s) z ∂ρ} :=
    measurableSet_lt measurable_const
      (measurable_integral_comp hf ρ (A.measurable_validationPlay hf hA))
  rw [← (measurePreserving_initSeg ρ n).measureReal_preimage hmeas.nullMeasurableSet]
  set P := Measure.infinitePi fun _ : ℕ ↦ ρ
  let ℱ := Filtration.naturalLT (fun t (ω : ℕ → Z) ↦ ω t) measurable_pi_apply
  have hx (t : ℕ) : Measurable[ℱ t] fun ω ↦ A.run (fun _ ↦ ()) ω t := by
    simp only [run_def]
    exact (hA t).comp (@Measurable.of_eval _ _ _ (ℱ t) _ _ fun r ↦ measurable_const.prodMk
      (Filtration.measurable_naturalLT measurable_pi_apply r.2))
  have hξ (t : ℕ) : Measurable[ℱ (t + 1)] fun ω : ℕ → Z ↦ ω t :=
    Filtration.measurable_naturalLT measurable_pi_apply t.lt_succ_self
  have hindep := Filtration.indep_naturalLT_infinitePi fun _ : ℕ ↦ ρ
  have hlaw := Measure.infinitePi_map_eval fun _ : ℕ ↦ ρ
  -- The average risk of the training plays is controlled by their regret [Ora, Theorem 3.10].
  have h1 := measureReal_add_div_add_sqrt_lt_sum_div_le_of_indep (ℱ := ℱ) (μ := P)
    (x := fun t ω ↦ A.run (fun _ ↦ ()) ω t) (ξ := fun t ω ↦ ω t) (n := n / 2) hf hf01 hx hξ
    hindep hlaw u (R := R u (n / 2)) (ae_of_all _ fun ω ↦ by
      simpa only [regret_def] using hreg.regret_le (c := fun _ ↦ ()) (g := ω) (n := n / 2)
        (fun _ _ ↦ trivial) hu) hk hδ
  -- The selected play is nearly the best training play [Ora, Theorem 3.17], for the filtration
  -- `ℱ` shifted by `n / 2`, at whose time `0` the training plays are known.
  let ℱ' : Filtration ℕ MeasurableSpace.pi :=
    ⟨fun j ↦ ℱ (n / 2 + j), fun _ _ hij ↦ ℱ.mono (by omega), fun _ ↦ ℱ.le _⟩
  have hsel (ω : ℕ → Z) (i : Fin (n / 2)) :
      ∑ j ∈ range (n / 2), f (A.run (fun _ ↦ ()) ω (Fin.val (argmin fun t : Fin (n / 2) ↦
          validationLoss f (initSeg n ω) (A.trainingPlay (initSeg n ω) t))))
        (ω (n / 2 + j)) ≤ ∑ j ∈ range (n / 2), f (A.run (fun _ ↦ ()) ω i) (ω (n / 2 + j)) := by
    have h := isMinOn_univ_iff.1 (isMinOn_argmin fun t ↦
      validationLoss f (initSeg n ω) (A.trainingPlay (initSeg n ω) t)) i
    simpa only [validationLoss_initSeg, trainingPlay_initSeg] using h
  have h2 := measureReal_exists_add_sqrt_lt_le_of_indep (ℱ := ℱ') (μ := P) (ρ := ρ)
    (c := fun t : Fin (n / 2) ↦ fun ω ↦ A.run (fun _ ↦ ()) ω t) (ξ := fun j ω ↦ ω (n / 2 + j))
    (k := fun ω ↦ argmin fun t ↦ validationLoss f (initSeg n ω) (A.trainingPlay (initSeg n ω) t))
    hf hf01 (fun t ↦ (hx t).mono (ℱ.mono (by omega)) le_rfl) (fun j ↦ hξ (n / 2 + j))
    (fun _ _ ↦ hindep _) (fun _ _ ↦ hlaw _) hsel hk hδ
  simp only [Fintype.card_fin] at h2
  refine (measureReal_mono fun ω hω ↦ ?_).trans ((measureReal_union_le _ _).trans
    ((add_le_add h1 h2).trans_eq (two_mul δ).symm))
  -- Outside both events, the risk of the selected play is at most the average risk of the
  -- training plays plus the selection term.
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  rw [A.validationPlay_eq, A.trainingPlay_initSeg] at hω
  by_contra! h
  obtain ⟨h1', h2'⟩ := h
  rw [← Fin.sum_univ_eq_sum_range (fun t ↦ ∫ z, f (A.run (fun _ ↦ ()) ω t) z ∂ρ)] at h1'
  linarith [le_add_of_sum_div_card_le
    (f := fun i : Fin (n / 2) ↦ ∫ z, f (A.run (fun _ ↦ ()) ω i) z ∂ρ) (mem_univ _)
    (fun i _ ↦ h2' i) (Eq.trans_le (by rw [card_fin]) h1')]

/-- **Sublinear regret gives agnostic PAC learnability** [Ora, §3.2]. Let `A` be an online learner
with data in `Z` as feedback and plays in `V`, measurable functions of the past data, whose regret
against `u ∈ V` on the losses `f (·) (z t)` is at most `R u n` after `n` rounds, for every
sequence of data. If the regret bound is sublinear uniformly over `V`, that is, for every `ε > 0`
eventually `R u n ≤ ε n` for all `u ∈ V`, then for a jointly measurable loss `f` with values in
`[0, 1]`, the class `{f x · | x ∈ V}` is agnostic PAC learnable, by the validation-selected
plays of `A`. -/
theorem agnosticPACLearnable
    (hreg : A.HasRegretBound (fun z y ↦ f y z) (fun _ _ ↦ True) V fun n _ _ u ↦ R u n)
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1)
    (hA : ∀ t, Measurable fun h : Fin t → Unit × Z ↦ A.play t h ())
    (hAV : ∀ t h, A.play t h () ∈ V) (hR : ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ V, R u n ≤ ε * n) :
    AgnosticPACLearnable f V := by
  refine ⟨fun n ↦ A.validationPlay f, fun n ↦ A.measurable_validationPlay hf hA,
    fun n ↦ A.validationPlay_mem hAV, fun ε hε δ hδ ↦ ?_⟩
  -- The regret term and the two deviation terms of the risk bound, at the confidence `δ / 2`, are
  -- eventually at most `ε / 4`.
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hR (ε / 4) (by positivity)).and
    ((eventually_sqrt_lt (2 * log (1 / (δ / 2))) (2 / (δ / 2)) (by positivity)
      (by positivity : 0 < ε / 4)).and (eventually_ge_atTop 1)))
  refine ⟨2 * K, fun n hn ρ _ ↦ ?_⟩
  obtain ⟨hRK, ⟨h1K, h2K⟩, hK1⟩ := hK (n / 2) (by omega)
  -- A point `u` of `V` whose risk is within `ε / 4` of the infimum of the risks over `V`.
  have hbdd : BddBelow ((fun y ↦ ∫ z, f y z ∂ρ) '' V) :=
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact integral_nonneg fun z ↦ (hf01 y z).1⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
    (Set.Nonempty.image _ ⟨_, hAV 0 Fin.elim0⟩)
    (lt_add_of_pos_right (sInf ((fun y ↦ ∫ z, f y z ∂ρ) '' V)) (by positivity : 0 < ε / 4))
  refine (measureReal_mono fun s hs ↦ ?_).trans
    ((hreg.measureReal_lt_integral_validationPlay_le hf hf01 hA ρ hu (by omega)
      (by positivity : 0 < δ / 2)).trans_eq (by ring))
  obtain ⟨v, hv, hvs⟩ := hs
  have hinf := csInf_le hbdd ⟨v, hv, rfl⟩
  have hk' : (0 : ℝ) < (n / 2 : ℕ) := by positivity
  have hRu : R u (n / 2) / (n / 2 : ℕ) ≤ ε / 4 := (div_le_iff₀ hk').2 (hRK u hu)
  rw [div_mul_eq_mul_div] at h2K
  simp only [Set.mem_ofPred_eq]
  linarith

end OnlineLearner.HasRegretBound

end LMLExplore.OnlineLearning

open LMLExplore.OnlineLearning in
/-- **Finite classes are agnostic PAC learnable** [Ora, Theorem 3.17], by empirical risk
minimization: for a jointly measurable loss `f` with values in `[0, 1]` and a finite nonempty set
`V`, the class `{f x · | x ∈ V}` is agnostic PAC learnable by the algorithm returning the point of
`V` with the smallest cumulative loss on the sample. The proof applies the selection bound
`measureReal_exists_add_sqrt_lt_le_of_indep` on the whole sample: for a sample size `n ≠ 0`, with
probability at least `1 - δ`, the risk of that point is within `√(2 log (2 |V| / δ) / n)` of the
smallest risk over `V`. -/
theorem Set.Finite.agnosticPACLearnable {α Z : Type*} [MeasurableSpace α] [MeasurableSpace Z]
    {f : α → Z → ℝ} {V : Set α} (hV : V.Finite) (hVne : V.Nonempty)
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) :
    AgnosticPACLearnable f V := by
  let := hV.fintype
  have : Nonempty V := hVne.to_subtype
  have hL (n : ℕ) : Measurable fun s : Fin n → Z ↦ fun v : V ↦ ∑ j, f v (s j) :=
    Measurable.of_eval fun _ ↦ Finset.measurable_sum _ fun j _ ↦
      hf.comp (measurable_const.prodMk (measurable_pi_apply j))
  refine ⟨fun n s ↦ (argmin fun v : V ↦ ∑ j, f v (s j) : V),
    fun n ↦ measurable_subtype_coe.comp (measurable_argmin.comp (hL n)),
    fun n s ↦ (argmin fun v : V ↦ ∑ j, f v (s j)).2, fun ε hε δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((eventually_sqrt_lt (2 * log (2 * Fintype.card V / δ)) 1 one_pos hε)).and
      (eventually_ge_atTop 1))
  refine ⟨N, fun n hn ρ _ ↦ ?_⟩
  obtain ⟨⟨hNn, -⟩, hn1⟩ := hN n hn
  -- The event that some point of `V` beats the minimizer by `√(2 log (2 |V| / δ) / n)`, on the
  -- sequence space whose first `n` terms have the law of a sample.
  set E : Set (Fin n → Z) := {s | ∃ v : V,
      ∫ z, f v z ∂ρ + √(2 * log (2 * Fintype.card V / δ) / n) <
        ∫ z, f (argmin fun v : V ↦ ∑ j, f v (s j) : V) z ∂ρ} with hE
  have hmeas : MeasurableSet E := by
    simp only [hE, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun _ ↦ measurableSet_lt measurable_const
      (measurable_integral_comp hf ρ (measurable_subtype_coe.comp (measurable_argmin.comp (hL n))))
  refine (measureReal_mono (s₂ := E) fun s hs ↦ ?_).trans ?_
  · obtain ⟨u, hu, hus⟩ := hs
    exact ⟨⟨u, hu⟩, by linarith⟩
  rw [← (measurePreserving_initSeg ρ n).measureReal_preimage hmeas.nullMeasurableSet]
  refine measureReal_exists_add_sqrt_lt_le_of_indep
    (ℱ := Filtration.naturalLT (fun t (ω : ℕ → Z) ↦ ω t) measurable_pi_apply) (ρ := ρ) (m := n)
    (c := fun (v : V) _ ↦ (v : α)) (ξ := fun t ω ↦ ω t)
    (k := fun ω ↦ argmin fun v : V ↦ ∑ j, f v (initSeg n ω j)) hf hf01
    (fun _ ↦ measurable_const)
    (fun t ↦ Filtration.measurable_naturalLT measurable_pi_apply t.lt_succ_self)
    (fun t _ ↦ Filtration.indep_naturalLT_infinitePi (fun _ ↦ ρ) t)
    (fun t _ ↦ Measure.infinitePi_map_eval (fun _ ↦ ρ) t) (fun ω v ↦ ?_) (by omega) hδ
  have h := isMinOn_univ_iff.1 (isMinOn_argmin fun v : V ↦ ∑ j, f v (initSeg n ω j)) v
  simp only [Finset.sum_range]
  simpa only [initSeg_def] using h
