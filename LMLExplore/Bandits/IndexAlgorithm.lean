/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.FiniteActions

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

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning

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

variable [DecidableEq α]

/-- If the index is `⊤` exactly on the arms not pulled yet, then during the first `Fintype.card α`
rounds the index policy only plays arms it has not pulled before. -/
lemma pullCount_action_eq_zero (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ n < Fintype.card α, pullCount A (A n ω) n ω = 0 := by
  filter_upwards [index_action_eq_top h] with ω hω n hn
  obtain ⟨b, hb⟩ : ∃ b, pullCount A b n ω = 0 := by
    by_contra! h0
    have : Fintype.card α ≤ n := calc
      Fintype.card α = ∑ _ : α, 1 := by simp
      _ ≤ ∑ a, pullCount A a n ω := sum_le_sum fun a _ ↦ Nat.one_le_iff_ne_zero.mpr (h0 a)
      _ = n := sum_pullCount
    omega
  rw [pullCount_eq_pullCount' (O := O) (R' := Y)] at hb ⊢
  exact (hI_top _ _ _).mp (hω n ⟨b, (hI_top _ _ _).mpr hb⟩)

/-- If the index is `⊤` exactly on the arms not pulled yet, then the index policy pulls every arm
exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  filter_upwards [pullCount_action_eq_zero h hI_top] with ω hω a
  -- The arms played during the first `Fintype.card α` rounds are pairwise distinct.
  have h_inj : Set.InjOn (A · ω) (range (Fintype.card α)) := by
    intro s hs t ht hst
    by_contra hne
    wlog hlt : s < t generalizing s t
    · exact this ht hs hst.symm (Ne.symm hne) (by omega)
    have h_zero := hω t (by simpa using ht)
    simp only [pullCount, card_eq_zero, filter_eq_empty_iff, mem_range] at h_zero
    exact h_zero hlt hst
  -- Hence every arm is played during those rounds, at a single round.
  have h_univ : (range (Fintype.card α)).image (A · ω) = univ :=
    eq_univ_of_card _ (by rw [card_image_of_injOn h_inj, card_range])
  obtain ⟨s, hs, rfl⟩ := mem_image.mp (h_univ ▸ mem_univ a)
  rw [pullCount, card_eq_one]
  refine ⟨s, eq_singleton_iff_unique_mem.mpr ⟨by simpa using hs, fun t ht ↦ ?_⟩⟩
  rw [mem_filter] at ht
  exact h_inj ht.1 hs ht.2

/-- If the index is `⊤` exactly on the arms not pulled yet, then from round `Fintype.card α` on,
every arm has been pulled at least once. -/
lemma pullCount_pos_of_card_le (h : IsAlgEnvSeq O A Y (indexAlgorithm I hI) env P)
    (hI_top : ∀ n x a, I n x a = ⊤ ↔ pullCount' n x.1 a = 0) :
    ∀ᵐ ω ∂P, ∀ n, Fintype.card α ≤ n → ∀ a, 0 < pullCount A a n ω := by
  filter_upwards [pullCount_card_eq_one h hI_top] with ω hω n hn a
  have h_mono := pullCount_mono (A := A) a hn ω
  rw [hω a] at h_mono
  omega

end IndexAlgorithm

end LMLExplore.Bandits
