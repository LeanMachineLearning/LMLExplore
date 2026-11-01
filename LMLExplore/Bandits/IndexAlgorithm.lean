/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LMLExplore.SequentialLearning.FiniteActions

/-!
# Index policies

An index policy on a finite set of arms `α` computes, at every round `n`, an index
`I n (h, o) : α → EReal` from the history `h` of the first `n` rounds and the current observation
`o`, and plays an arm of maximal index, ties being broken by LML's `argmax`. UCB, MOSS and KL-UCB
are index policies [LS, Algorithms 3, 6, 7 and 8].

The indices take values in `EReal` so that an arm that has not been pulled yet can be given the
index `⊤`. The policy then pulls such an arm before any arm with a finite index, and "pull each arm
once" is the behaviour of the index policy itself rather than a separate initialization phase
that would depend on an enumeration of the arms.

## Main definitions

* `LMLExplore.Bandits.indexAlgorithm I hI`: the deterministic algorithm that plays
  `argmax (I n (h, o))` at round `n`.

## Main statements

In the namespace `LMLExplore.Bandits.IndexAlgorithm`:

* `action_ae_eq`: the run lemma. Along any run of the index policy, the action of round `n` is
  almost surely `argmax (I n (h, o))` for the history `h` and the observation `o` of that run.
* `index_le_index_action`: along a run, the arm played has maximal index.
* `index_action_eq_top`: along a run, if some arm has index `⊤`, then the arm played has
  index `⊤`.
* `pullCount_card_eq_one`: if the index is `⊤` exactly on the arms that have not been pulled yet,
  then every arm is pulled exactly once during the first `Fintype.card α` rounds.
* `integral_pullCount_le_sum_add_sum`: the decomposition of the expected number of pulls of an
  arm `a`, as in the proofs of [LS, Theorems 8.1 and 10.6]: for every arm `b` and threshold `c`,
  `E[T_a(n)] ≤ ∑_{t < n} P(I_t(b) ≤ c) + ∑_{t < n} P(A_t = a, c < I_t(a))`.
* `pullCount_eq_card_filter_of_forall_lt_index`: along a run, if the index of an arm `b` exceeds a
  threshold `c` at every round before `n`, then every pull of an arm `a` before `n` happens with
  an index of `a` above `c`, as in the proof of [LS, Theorem 9.1].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace LMLExplore.Bandits

variable {α 𝓞 𝓨 : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  {m𝓞 : MeasurableSpace 𝓞} {m𝓨 : MeasurableSpace 𝓨}
  {I : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → EReal}

/-- The index policy with index `I`: at round `n`, with history `h` and observation `o`, it plays
the arm `argmax (I n (h, o))`, a maximizer of the index with ties broken by LML's `argmax`. -/
noncomputable def indexAlgorithm (I : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → EReal)
    (hI : ∀ n, Measurable (I n)) : Algorithm 𝓞 α 𝓨 :=
  detAlgorithm (fun n x ↦ argmax (I n x)) fun n ↦ measurable_argmax.comp (hI n)

variable {hI : ∀ n, Measurable (I n)}

/-- The index policy is the deterministic algorithm playing `argmax (I n x)` at round `n`. -/
lemma indexAlgorithm_eq_detAlgorithm :
    indexAlgorithm I hI =
      detAlgorithm (fun n x ↦ argmax (I n x)) fun n ↦ measurable_argmax.comp (hI n) :=
  (rfl)

@[simp]
lemma indexAlgorithm_policy (n : ℕ) :
    (indexAlgorithm I hI).policy n =
      Kernel.deterministic (fun x ↦ argmax (I n x)) (measurable_argmax.comp (hI n)) := by
  rw [indexAlgorithm_eq_detAlgorithm, detAlgorithm_policy]

instance : IsDeterministicAlg (indexAlgorithm I hI) where
  exists_nextAction n := ⟨_, _, indexAlgorithm_policy n⟩

/-- The action function of the index policy at round `n` is `x ↦ argmax (I n x)`. -/
@[simp]
lemma nextAction_indexAlgorithm [MeasurableSingletonClass α] (n : ℕ) :
    nextAction (indexAlgorithm I hI) n = fun x ↦ argmax (I n x) := by
  simpa using (policy_eq_deterministic (indexAlgorithm I hI) n).symm

namespace IndexAlgorithm

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {env : Environment 𝓞 α 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- The run lemma of the index policy: the action of round `n` is almost surely the arm of
maximal index, for the history and the observation of the run. -/
lemma action_ae_eq (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ argmax (I n (history O A Y n ω, O n ω)) :=
  (IsDeterministicAlg.action_ae_eq h n).trans (by simp)

/-- The run lemma of the index policy, for all rounds simultaneously. -/
lemma action_ae_all_eq (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = argmax (I n (history O A Y n ω, O n ω)) :=
  ae_all_iff.mpr (action_ae_eq h)

/-- Along a run of the index policy, the arm played at round `n` has maximal index. -/
lemma index_le_index_action (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) :
    ∀ᵐ ω ∂P, ∀ n b,
      I n (history O A Y n ω, O n ω) b ≤ I n (history O A Y n ω, O n ω) (A n ω) := by
  filter_upwards [action_ae_all_eq h] with ω hω n b
  rw [hω n]
  exact isMaxOn_argmax _ b

/-- Along a run of the index policy, if some arm has index `⊤` at round `n`, then the arm played at
round `n` has index `⊤`: arms with index `⊤` are pulled before arms with a finite index. -/
lemma index_action_eq_top (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) :
    ∀ᵐ ω ∂P, ∀ n, (∃ b, I n (history O A Y n ω, O n ω) b = ⊤) →
      I n (history O A Y n ω, O n ω) (A n ω) = ⊤ := by
  filter_upwards [index_le_index_action h] with ω hω n ⟨b, hb⟩
  exact top_le_iff.mp (hb ▸ hω n b)

/-- Along a run of the index policy, for arms `a`, `b` and a threshold `c`, if the arm `a` is
played at round `n`, then the index of `b` is at most `c` or the index of `a` exceeds `c`. -/
lemma index_le_or_lt_index_of_action_eq (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (a b : α) (c : EReal) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = a →
      I n (history O A Y n ω, O n ω) b ≤ c ∨ c < I n (history O A Y n ω, O n ω) a := by
  filter_upwards [index_le_index_action h] with ω hω n hn
  rw [← hn, or_iff_not_imp_left, not_le]
  exact fun hc ↦ hc.trans_le (hω n b)

variable [DecidableEq α]

/-- If the index is `⊤` exactly on the arms not pulled yet, then during the first `Fintype.card α`
rounds the index policy only plays arms it has not pulled before. -/
lemma pullCount_action_eq_zero (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ n < Fintype.card α, pullCount A (A n ω) n ω = 0 := by
  filter_upwards [index_action_eq_top h] with ω hω n hn
  obtain ⟨b, hb⟩ := exists_pullCount_eq_zero_of_lt_card (A := A) (ω := ω) hn
  rw [pullCount_eq_pullCount' (O := O) (R' := Y)] at hb ⊢
  exact (hI_top _ _ _).mp (hω n ⟨b, (hI_top _ _ _).mpr hb⟩)

/-- If the index is `⊤` exactly on the arms not pulled yet, then the index policy pulls every arm
exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  filter_upwards [pullCount_action_eq_zero h hI_top] with ω hω a
  exact pullCount_card_eq_one_of_forall_pullCount_action_eq_zero hω a

/-- If the index is `⊤` exactly on the arms not pulled yet, then from round `Fintype.card α` on,
every arm has been pulled at least once. -/
lemma pullCount_pos_of_card_le (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ n, Fintype.card α ≤ n → ∀ a, 0 < pullCount A a n ω := by
  filter_upwards [pullCount_card_eq_one h hI_top] with ω hω n hn a
  have h_mono := pullCount_mono (A := A) a hn ω
  rw [hω a] at h_mono
  omega

/-- The decomposition of the expected number of pulls of an arm `a` by an index policy, as in the
proofs of [LS, Theorems 8.1 and 10.6]: for every arm `b` (typically an optimal arm) and every
threshold `c`,
`E[T_a(n)] ≤ ∑_{t < n} P(I_t(b) ≤ c) + ∑_{t < n} P(A_t = a, c < I_t(a))`. The first sum counts
the rounds at which the index of `b` underestimates `c`, the second the rounds at which `a` is
played with an index above `c`. -/
theorem integral_pullCount_le_sum_add_sum
    (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) (a b : α) (c : EReal) (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤
      ∑ t ∈ Finset.range n, P.real {ω | I t (history O A Y t ω, O t ω) b ≤ c} +
        ∑ t ∈ Finset.range n,
          P.real {ω | A t ω = a ∧ c < I t (history O A Y t ω, O t ω) a} := by
  rw [integral_pullCount_eq_sum h.measurable_action, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ ↦ le_trans ?_ (measureReal_union_le _ _)
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [index_le_or_lt_index_of_action_eq h a b c] with ω hω hωt
  exact (hω t hωt).imp id fun hc ↦ ⟨hωt, hc⟩

open Finset in
/-- Along a run of the index policy, for arms `a`, `b` and a threshold `c`, if the index of `b`
exceeds `c` at every round `t < n`, then `a` has an index above `c` at every round `t < n` at which
it is played: its number of pulls before round `n` is the number of rounds `t < n` at which it is
played with an index above `c`. This is the pathwise step of the proof of [LS, Theorem 9.1]. -/
lemma pullCount_eq_card_filter_of_forall_lt_index
    (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P) (a b : α) (c : EReal) :
    ∀ᵐ ω ∂P, ∀ n, (∀ t < n, c < I t (history O A Y t ω, O t ω) b) →
      pullCount A a n ω = #{t ∈ range n | A t ω = a ∧ c < I t (history O A Y t ω, O t ω) a} := by
  filter_upwards [index_le_or_lt_index_of_action_eq h a b c] with ω hω n hb
  refine congrArg card (filter_congr fun t ht ↦ ⟨fun hat ↦ ⟨hat, ?_⟩, And.left⟩)
  exact (hω t hat).resolve_left (not_le.mpr (hb t (mem_range.mp ht)))

end IndexAlgorithm

end LMLExplore.Bandits
