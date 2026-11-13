/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import Mathlib.Data.Fin.Tuple.Take
public import LMLExplore.Topology.Algebra.InfiniteSum.NatInt
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Stopped histories: dependence on the rounds before stopping, histories stopped at a fixed time

Complements to LML's `LeanMachineLearning.SequentialLearning.StoppedHistory`. A stopping rule
`S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)` stops the interaction after `n` rounds if the history of these
`n` rounds belongs to `S`, so the round `n` is played if and only if no history of `m ≤ n` rounds
along the run belongs to `S`. The kernel generating round `n` from an `n`-round history is
therefore only used on the set `notStoppedSet S n` of `n`-round histories none of whose prefixes
belong to `S`.

The main result is that the law `stoppedHistMeasure alg env S` of the stopped history only
depends on the step kernels of `alg` and `env` on these histories: two algorithm-environment
pairs whose step kernels agree on `notStoppedSet S n` for every `n` give the same law of the
stopped history. This is the basis of the change of measure at stopping times: an environment
can be modified after the stopping time without changing the law of the stopped history.

The history stopped at a fixed time `M`, `stoppedProcess (sigmaHistory O X Y) τ M`, is the history
of the first `min M τ` rounds. Its law splits according to whether round `M` is played, which
gives the chain rule for the divergence at a bounded stopping time
(`Learning.IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_eq_sum`); when `τ` is almost surely
finite, it is the image of the law of the stopped history by the truncation `truncHist M` to at
most `M` rounds.

## Main definitions

* `Learning.notStoppedSet S n`: the `n`-round histories after which the stopping rule `S` has not
  stopped, that is, none of whose prefixes belong to `S`.
* `Learning.truncHist M`: the truncation of a history of variable length to at most `M` rounds.

## Main statements

* `Learning.history_mem_notStoppedSet_iff`: the history of the first `n` rounds belongs to
  `notStoppedSet S n` if and only if the hitting time of `S` is larger than `n`.
* `Learning.tsum_setLIntegral_notStoppedSet`: the series over the rounds `t` of the integrals of
  `f t` on the event `history t ∈ notStoppedSet S t` is the integral of `∑ t < τ, f t` for an
  almost surely finite hitting time `τ` of `S`.
* `Learning.stoppedHistMeasure_congr`: if the step kernels of `(alg, env)` and `(alg', env')`
  agree on `notStoppedSet S n` for every `n`, then
  `stoppedHistMeasure alg env S = stoppedHistMeasure alg' env' S`.
* `Learning.map_stoppedProcess_sigmaHistory_eq_map_truncHist`: for an almost surely finite `τ`,
  the law of the history stopped at the time `M` is the image of the law of the stopped history by
  `truncHist M`.
* `Learning.map_stoppedProcess_sigmaHistory_eq_add`,
  `Learning.map_stoppedProcess_sigmaHistory_succ_eq_add`: the laws of the histories stopped at the
  times `M` and `M + 1` split according to whether round `M` is played.

The material on the histories stopped at a fixed time is adapted from the formalization of prefixes
of stopped processes in the Essakine2026Tight project (`RemyDegenne/Essakine2026Tight`,
Apache 2.0, `ForLMLExplore/Probability/Process/SigmaPrefix.lean`).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Learning

variable {𝓞 𝓐 𝓨 Ω Ω' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} {n : ℕ} {ω : Ω}

/-- The map sending an `n`-round history to its prefix of length `m ≤ n`, as a history of variable
length, is measurable. -/
private lemma measurable_sigma_prefix {m : ℕ} (hm : m ≤ n) :
    Measurable fun h : Hist 𝓞 𝓐 𝓨 n ↦
      (⟨m, fun i ↦ h (Fin.castLE hm i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) :=
  (measurable_sigmaMk m).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _)

/-- For `m ≤ n`, the history of the first `m` rounds is the prefix of length `m` of the history
of the first `n` rounds. -/
private lemma sigmaHistory_eq_prefix {m : ℕ} (hm : m ≤ n) :
    sigmaHistory O X Y m ω = ⟨m, fun i ↦ history O X Y n ω (Fin.castLE hm i)⟩ := by
  rw [sigmaHistory_apply, history_eq_comp_history hm, Function.comp_apply]

/-- The `n`-round histories after which the stopping rule `S` has not stopped: the histories none
of whose prefixes of length `m ≤ n` belong to `S`. Along an algorithm-environment sequence, the
history of the first `n` rounds belongs to this set if and only if round `n` is played, that is
the hitting time of `S` is larger than `n` (`history_mem_notStoppedSet_iff`). -/
def notStoppedSet (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) (n : ℕ) : Set (Hist 𝓞 𝓐 𝓨 n) :=
  {h | ∀ m (hm : m ≤ n), (⟨m, fun i ↦ h (Fin.castLE hm i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) ∉ S}

lemma mem_notStoppedSet_iff {h : Hist 𝓞 𝓐 𝓨 n} :
    h ∈ notStoppedSet S n ↔
      ∀ m (hm : m ≤ n), (⟨m, fun i ↦ h (Fin.castLE hm i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) ∉ S :=
  Iff.rfl

lemma measurableSet_notStoppedSet (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (notStoppedSet S n) := by
  have : notStoppedSet S n = ⋂ m, ⋂ (hm : m ≤ n),
      (fun h : Hist 𝓞 𝓐 𝓨 n ↦ (⟨m, fun i ↦ h (Fin.castLE hm i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) ⁻¹'
        Sᶜ := by
    ext
    simp [notStoppedSet]
  rw [this]
  exact .iInter fun m ↦ .iInter fun hm ↦ measurable_sigma_prefix hm hS.compl

/-- The history of the first `n` rounds belongs to `notStoppedSet S n` if and only if the hitting
time of `S` is larger than `n`, that is round `n` is played. -/
lemma history_mem_notStoppedSet_iff :
    history O X Y n ω ∈ notStoppedSet S n ↔
      (n : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω := by
  rw [← not_le]
  refine Iff.trans ?_ (not_congr hittingAfter_le_iff).symm
  simp only [mem_notStoppedSet_iff, mem_Icc, zero_le, true_and, not_exists, not_and]
  exact forall₂_congr fun m hm ↦ by rw [sigmaHistory_eq_prefix hm]

/-- The series over the rounds `t` of the integrals of `f t` on the event that the stopping rule
`S` has not stopped after the first `t` rounds is the integral of the sum of the `f t` over the
rounds before the hitting time of `S`, when that hitting time is almost surely finite. -/
lemma tsum_setLIntegral_notStoppedSet {P : Measure Ω} (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O X Y) S 0 ω ≠ ⊤)
    {f : ℕ → Ω → ℝ≥0∞} (hf : ∀ t, Measurable (f t)) :
    ∑' t, ∫⁻ ω in history O X Y t ⁻¹' notStoppedSet S t, f t ω ∂P =
      ∫⁻ ω, ∑ t ∈ Finset.range (ENat.toNat (hittingAfter (sigmaHistory O X Y) S 0 ω)), f t ω
        ∂P := by
  have hmeas (t : ℕ) : MeasurableSet (history O X Y t ⁻¹' notStoppedSet S t) :=
    measurable_history hO hX hY t (measurableSet_notStoppedSet hS t)
  simp_rw [← lintegral_indicator (hmeas _)]
  rw [← lintegral_tsum fun t ↦ ((hf t).indicator (hmeas t)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hτ] with ω hω
  have h_ind (t : ℕ) : (history O X Y t ⁻¹' notStoppedSet S t).indicator (f t) ω =
      {t : ℕ | (t : ℕ∞) < hittingAfter (sigmaHistory O X Y) S 0 ω}.indicator
        (fun t ↦ f t ω) t := by
    simp only [indicator, mem_preimage, history_mem_notStoppedSet_iff]
    -- Both conditions are `t < τ ω`, with `t` cast to `WithTop ℕ` and to `ℕ∞ = WithTop ℕ`.
    congr 1
  simp_rw [h_ind]
  exact LMLExplore.tsum_indicator_natCast_lt_eq_sum_range hω fun t ↦ f t ω

section Congr

/-! ### Congruence of the law of the stopped history -/

/-- The `n`-round histories none of whose strict prefixes belong to `S`. Along a sequence, the
history of the first `n` rounds belongs to this set if and only if the hitting time of `S` is at
least `n`. -/
private def notStoppedBeforeSet (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) (n : ℕ) :
    Set (Hist 𝓞 𝓐 𝓨 n) :=
  {h | ∀ m (hm : m < n), (⟨m, fun i ↦ h (Fin.castLE hm.le i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) ∉ S}

private lemma measurableSet_notStoppedBeforeSet (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (notStoppedBeforeSet S n) := by
  have : notStoppedBeforeSet S n = ⋂ m, ⋂ (hm : m < n),
      (fun h : Hist 𝓞 𝓐 𝓨 n ↦ (⟨m, fun i ↦ h (Fin.castLE hm.le i)⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) ⁻¹'
        Sᶜ := by
    ext
    simp [notStoppedBeforeSet]
  rw [this]
  exact .iInter fun m ↦ .iInter fun hm ↦ measurable_sigma_prefix hm.le hS.compl

private lemma notStoppedSet_subset_notStoppedBeforeSet :
    notStoppedSet S n ⊆ notStoppedBeforeSet S n :=
  fun _ hh m hm ↦ hh m hm.le

private lemma history_mem_notStoppedBeforeSet_iff :
    history O X Y n ω ∈ notStoppedBeforeSet S n ↔
      (n : WithTop ℕ) ≤ hittingAfter (sigmaHistory O X Y) S 0 ω := by
  rw [← not_lt]
  refine Iff.trans ?_ (not_congr hittingAfter_lt_iff).symm
  simp only [notStoppedBeforeSet, mem_ofPred_eq, mem_Ico, zero_le, true_and, not_exists, not_and]
  exact forall₂_congr fun m hm ↦ by rw [sigmaHistory_eq_prefix hm.le]

/-- An `(n + 1)`-round history has no strict prefix in `S` iff its first `n` rounds form a
history in `notStoppedSet S n`. -/
private lemma preimage_finSuccProd_symm_notStoppedBeforeSet :
    (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm ⁻¹' notStoppedBeforeSet S (n + 1) =
      notStoppedSet S n ×ˢ univ := by
  ext ⟨h, r⟩
  simp only [mem_preimage, MeasurableEquiv.finSuccProd_symm_apply, mem_prod, mem_univ, and_true]
  have key (m : ℕ) (hm : m ≤ n) : (fun i : Fin m ↦
      (Fin.snoc (α := fun _ ↦ Round 𝓞 𝓐 𝓨) h r (Fin.castLE (Nat.lt_succ_of_le hm).le i))) =
        fun i ↦ h (Fin.castLE hm i) := by
    funext i
    exact Fin.snoc_castSucc (α := fun _ ↦ Round 𝓞 𝓐 𝓨) r h (Fin.castLE hm i)
  refine ⟨fun H m hm ↦ key m hm ▸ H m (Nat.lt_succ_of_le hm), fun H m hm ↦ ?_⟩
  rw [key m (Nat.le_of_lt_succ hm)]
  exact H m _

variable {alg alg' : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {O' : ℕ → Ω' → 𝓞} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}

/-- If the step kernels of `(alg, env)` and `(alg', env')` agree on the histories after which
`S` has not stopped, then the laws of the `n`-round histories agree on the histories without
strict prefix in `S`. -/
private lemma map_history_restrict_notStoppedBeforeSet (h : IsAlgEnvSeq O X Y alg env P)
    (h' : IsAlgEnvSeq O' X' Y' alg' env' P') (hS : MeasurableSet S)
    (h_eq : ∀ n, ∀ x ∈ notStoppedSet S n, stepKernel alg env n x = stepKernel alg' env' n x)
    (n : ℕ) :
    (P.map (history O X Y n)).restrict (notStoppedBeforeSet S n) =
      (P'.map (history O' X' Y' n)).restrict (notStoppedBeforeSet S n) := by
  induction n with
  | zero => simp [Measure.map_const]
  | succ n ih =>
    have hm := measurableSet_notStoppedSet hS n
    have h_restrict : (P.map (history O X Y n)).restrict (notStoppedSet S n) =
        (P'.map (history O' X' Y' n)).restrict (notStoppedSet S n) := by
      rw [← Measure.restrict_restrict_of_subset notStoppedSet_subset_notStoppedBeforeSet, ih,
        Measure.restrict_restrict_of_subset notStoppedSet_subset_notStoppedBeforeSet]
    have he := (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm.measurable
    rw [history_succ, history_succ,
      ← Measure.map_map he ((h.measurable_history n).prodMk (h.measurable_step n)),
      ← Measure.map_map he ((h'.measurable_history n).prodMk (h'.measurable_step n)),
      (h.hasCondDistrib_step n).map_eq, (h'.hasCondDistrib_step n).map_eq,
      Measure.restrict_map he (measurableSet_notStoppedBeforeSet hS _),
      Measure.restrict_map he (measurableSet_notStoppedBeforeSet hS _),
      preimage_finSuccProd_symm_notStoppedBeforeSet, ← Measure.compProd_restrict_left _ _ hm,
      ← Measure.compProd_restrict_left _ _ hm, h_restrict,
      Measure.compProd_congr (ae_restrict_of_forall_mem hm (h_eq n))]

/-- Under the hypotheses of `map_history_restrict_notStoppedBeforeSet`, the events determined by
the `n`-round history and contained in `{n ≤ τ}` have the same probability. -/
private lemma measure_history_preimage_eq (h : IsAlgEnvSeq O X Y alg env P)
    (h' : IsAlgEnvSeq O' X' Y' alg' env' P') (hS : MeasurableSet S)
    (h_eq : ∀ n, ∀ x ∈ notStoppedSet S n, stepKernel alg env n x = stepKernel alg' env' n x)
    {D : Set (Hist 𝓞 𝓐 𝓨 n)} (hD : MeasurableSet D) (hDS : D ⊆ notStoppedBeforeSet S n) :
    P (history O X Y n ⁻¹' D) = P' (history O' X' Y' n ⁻¹' D) := by
  rw [← Measure.map_apply (h.measurable_history n) hD,
    ← Measure.map_apply (h'.measurable_history n) hD, ← Measure.restrict_eq_self _ hDS,
    ← Measure.restrict_eq_self (P'.map (history O' X' Y' n)) hDS,
    map_history_restrict_notStoppedBeforeSet h h' hS h_eq]

/-- On the event `{τ = n}` the stopped history is the history of the first `n` rounds, so the
events `{F ∈ B, τ = n}` have the same probability for the two pairs, where `τ` is the hitting time
of `S` and `F` the stopped history. -/
private lemma measure_stoppedValue_preimage_inter_eq_coe (hS : MeasurableSet S)
    (h_eq : ∀ n, ∀ x ∈ notStoppedSet S n, stepKernel alg env n x = stepKernel alg' env' n x)
    {B : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} (hB : MeasurableSet B) (n : ℕ) :
    trajMeasure alg env (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0) ⁻¹' B ∩
          hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ⁻¹' {(n : WithTop ℕ)}) =
      trajMeasure alg' env' (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0) ⁻¹' B ∩
          hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ⁻¹' {(n : WithTop ℕ)}) := by
  set τ := hittingAfter (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) S 0 with hτ_def
  set F := stoppedValue (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) τ with hF_def
  have hF_of (ω : ℕ → Round 𝓞 𝓐 𝓨) (hω : τ ω = n) :
      F ω = sigmaHistory IT.obs IT.action IT.feedback n ω := by
    rw [hF_def, stoppedValue, hω, WithTop.untopA, ← WithTop.coe_natCast, WithTop.untopD_coe,
      Nat.cast_id]
  have h_eq_pre : F ⁻¹' B ∩ τ ⁻¹' {(n : WithTop ℕ)} =
      history IT.obs IT.action IT.feedback n ⁻¹'
        (notStoppedBeforeSet S n ∩ Sigma.mk n ⁻¹' (S ∩ B)) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
      history_mem_notStoppedBeforeSet_iff]
    constructor
    · rintro ⟨hFB, hτn⟩
      have hne : τ ω ≠ ⊤ := by simp [hτn]
      have h_mem : F ω ∈ S := by
        rw [hF_def]
        exact hittingAfter_mem_set_of_ne_top hne
      rw [hF_of ω hτn] at hFB h_mem
      exact ⟨hτn.ge, h_mem, hFB⟩
    · rintro ⟨hle, hS', hB'⟩
      have hτn : τ ω = n := le_antisymm (hittingAfter_le_of_mem (Nat.zero_le n) hS') hle
      rw [hF_of ω hτn]
      exact ⟨hB', hτn⟩
  rw [h_eq_pre]
  exact measure_history_preimage_eq (IT.isAlgEnvSeq_trajMeasure alg env)
    (IT.isAlgEnvSeq_trajMeasure alg' env') hS h_eq ((measurableSet_notStoppedBeforeSet hS n).inter
      ((measurable_sigmaMk n) (hS.inter hB))) inter_subset_left

/-- On the event `{τ = ⊤}` the stopped history is the history of the first `c` rounds for a fixed
`c`, and `{τ = ⊤}` is the decreasing intersection of the events `{m + c < τ}`, which are determined
by the first `m + c` rounds. Hence the events `{F ∈ B, τ = ⊤}` have the same probability for the
two pairs, where `τ` is the hitting time of `S` and `F` the stopped history. -/
private lemma measure_stoppedValue_preimage_inter_eq_top (hS : MeasurableSet S)
    (h_eq : ∀ n, ∀ x ∈ notStoppedSet S n, stepKernel alg env n x = stepKernel alg' env' n x)
    {B : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} (hB : MeasurableSet B) :
    trajMeasure alg env (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0) ⁻¹' B ∩
          hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ⁻¹' {⊤}) =
      trajMeasure alg' env' (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0) ⁻¹' B ∩
          hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ⁻¹' {⊤}) := by
  set τ := hittingAfter (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) S 0 with hτ_def
  set F := stoppedValue (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) τ with hF_def
  set c := (⊤ : WithTop ℕ).untopA with hc_def
  have hF_of (ω : ℕ → Round 𝓞 𝓐 𝓨) (hω : τ ω = ⊤) :
      F ω = sigmaHistory IT.obs IT.action IT.feedback c ω := by
    simp only [hF_def, stoppedValue, hω, hc_def]
  -- The event `{m + c < τ} ∩ {the first `c` rounds form a history in `B`}`.
  set s : ℕ → Set (ℕ → Round 𝓞 𝓐 𝓨) := fun m ↦
    history IT.obs IT.action IT.feedback (m + c) ⁻¹' (notStoppedSet S (m + c) ∩
      (fun x : Hist 𝓞 𝓐 𝓨 (m + c) ↦ (⟨c, fun i ↦ x (Fin.castLE (Nat.le_add_left c m) i)⟩ :
        Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' B) with hs_def
  have hs_mem (m : ℕ) (ω : ℕ → Round 𝓞 𝓐 𝓨) :
      ω ∈ s m ↔ ((m + c : ℕ) : WithTop ℕ) < τ ω ∧
        sigmaHistory IT.obs IT.action IT.feedback c ω ∈ B := by
    rw [hs_def, mem_preimage, mem_inter_iff, history_mem_notStoppedSet_iff, mem_preimage,
      sigmaHistory_eq_prefix (Nat.le_add_left c m)]
  have h_eq_inter : F ⁻¹' B ∩ τ ⁻¹' {⊤} = ⋂ m, s m := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_iInter, hs_mem]
    constructor
    · rintro ⟨hFB, hτ⟩
      rw [hF_of ω hτ] at hFB
      exact fun m ↦ ⟨by simp [hτ], hFB⟩
    · intro H
      have hτ : τ ω = ⊤ := WithTop.eq_top_iff_forall_gt.2 fun m ↦
        (WithTop.coe_le_coe.2 (Nat.le_add_right m c)).trans_lt (H m).1
      rw [hF_of ω hτ]
      exact ⟨(H 0).2, hτ⟩
  have hs_anti : Antitone s := fun m m' hmm' ω hω ↦ by
    rw [hs_mem] at hω ⊢
    exact ⟨(WithTop.coe_le_coe.2 (Nat.add_le_add_right hmm' c)).trans_lt hω.1, hω.2⟩
  have hD (m : ℕ) : MeasurableSet (notStoppedSet S (m + c) ∩
      (fun x : Hist 𝓞 𝓐 𝓨 (m + c) ↦ (⟨c, fun i ↦ x (Fin.castLE (Nat.le_add_left c m) i)⟩ :
        Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' B) :=
    (measurableSet_notStoppedSet hS _).inter (measurable_sigma_prefix _ hB)
  have hs_meas (m : ℕ) : NullMeasurableSet (s m) (trajMeasure alg env) :=
    (IT.measurable_hist _ (hD m)).nullMeasurableSet
  have hs_meas' (m : ℕ) : NullMeasurableSet (s m) (trajMeasure alg' env') :=
    (IT.measurable_hist _ (hD m)).nullMeasurableSet
  rw [h_eq_inter, hs_anti.measure_iInter hs_meas ⟨0, measure_ne_top _ _⟩,
    hs_anti.measure_iInter hs_meas' ⟨0, measure_ne_top _ _⟩]
  exact iInf_congr fun m ↦ measure_history_preimage_eq (IT.isAlgEnvSeq_trajMeasure alg env)
    (IT.isAlgEnvSeq_trajMeasure alg' env') hS h_eq (hD m)
    (inter_subset_left.trans notStoppedSet_subset_notStoppedBeforeSet)

/-- **The law of the stopped history only depends on the rounds before stopping.** If the step
kernels of `(alg, env)` and `(alg', env')` agree on the histories after which the stopping rule
`S` has not stopped, then the laws of the histories stopped by `S` are equal. -/
theorem stoppedHistMeasure_congr (hS : MeasurableSet S)
    (h_eq : ∀ n, ∀ x ∈ notStoppedSet S n, stepKernel alg env n x = stepKernel alg' env' n x) :
    stoppedHistMeasure alg env S = stoppedHistMeasure alg' env' S := by
  have hτ := measurable_hittingAfter_sigmaHistory (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)
    IT.measurable_obs IT.measurable_action IT.measurable_feedback hS
  have hF := measurable_stoppedValue_sigmaHistory IT.measurable_obs IT.measurable_action
    IT.measurable_feedback hτ
  set τ := hittingAfter (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) S 0
  set F := stoppedValue (sigmaHistory (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
    IT.feedback) τ
  ext B hB
  rw [stoppedHistMeasure, stoppedHistMeasure, Measure.map_apply hF hB, Measure.map_apply hF hB]
  -- Decompose the event `{F ∈ B}` according to the value of the stopping time.
  have h_union : F ⁻¹' B = ⋃ k : WithTop ℕ, F ⁻¹' B ∩ τ ⁻¹' {k} := by
    ext
    simp
  have h_disj : Pairwise (Function.onFun Disjoint fun k : WithTop ℕ ↦ F ⁻¹' B ∩ τ ⁻¹' {k}) :=
    fun k l hkl ↦ ((pairwise_disjoint_fiber τ) hkl).mono inter_subset_right inter_subset_right
  have h_meas (k : WithTop ℕ) : MeasurableSet (F ⁻¹' B ∩ τ ⁻¹' {k}) :=
    (hF hB).inter (hτ (measurableSet_singleton k))
  rw [h_union, measure_iUnion h_disj h_meas, measure_iUnion h_disj h_meas]
  refine tsum_congr fun k ↦ ?_
  induction k with
  | top => exact measure_stoppedValue_preimage_inter_eq_top hS h_eq hB
  | coe n => exact measure_stoppedValue_preimage_inter_eq_coe hS h_eq hB n

end Congr


section StoppedAtTime

/-! ### Histories stopped at a fixed time

Let `τ` be the hitting time of a stopping rule `S`. The history stopped at the time `M`,
`stoppedProcess (sigmaHistory O X Y) τ M`, is the history of the first `min M τ` rounds. Its law
splits according to whether round `M` is played, that is whether the history of the first `M`
rounds lies in `notStoppedSet S M`: if it is not, the history stopped at `M + 1` is the history
stopped at `M`; if it is, the history stopped at `M` is the history of the first `M` rounds and
the history stopped at `M + 1` is the history of the first `M + 1` rounds. When `τ` is finite, the
history stopped at `M` is the truncation `truncHist M` of the history stopped at `τ`. -/

/-- The truncation of a history of variable length to at most `M` rounds: a history of `n`
rounds is sent to the history of its first `min M n` rounds (`Fin.take`). -/
def truncHist (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  ⟨min M h.1, Fin.take (min M h.1) (min_le_right M h.1) h.2⟩

/-- Unfolding lemma for `truncHist`. -/
lemma truncHist_def (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) :
    truncHist M h = ⟨min M h.1, Fin.take (min M h.1) (min_le_right M h.1) h.2⟩ := (rfl)

/-- The truncation of a history to at most `M` rounds has `min M n` rounds, where `n` is the
number of rounds of the history. -/
@[simp]
lemma fst_truncHist (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) : (truncHist M h).1 = min M h.1 := (rfl)

/-- The truncation to at most `M` rounds fixes the histories of at most `M` rounds. -/
lemma truncHist_of_le {M : ℕ} {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n} (hM : h.1 ≤ M) :
    truncHist M h = h := by
  obtain ⟨n, x⟩ := h
  rw [truncHist_def]
  refine Sigma.ext (min_eq_right hM) ((Fin.heq_fun_iff (min_eq_right hM)).2 fun i ↦ ?_)
  exact Fin.take_apply (min M n) (min_le_right M n) x i

/-- The truncation of histories of variable length is measurable. -/
@[fun_prop]
lemma measurable_truncHist (M : ℕ) : Measurable (truncHist (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) M) :=
  measurable_sigma fun n ↦ (measurable_sigmaMk (min M n)).comp
    (Measurable.of_eval fun i ↦ measurable_pi_apply (Fin.castLE (min_le_right M n) i))

/-- Truncating the history of the first `n` rounds to at most `M` rounds gives the history of the
first `min M n` rounds. -/
@[simp]
lemma truncHist_sigmaHistory (M n : ℕ) (ω : Ω) :
    truncHist M (sigmaHistory O X Y n ω) = sigmaHistory O X Y (min M n) ω := by
  rw [sigmaHistory_apply, sigmaHistory_apply, truncHist_def]
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  simp [Fin.take_apply, history_apply]

/-- Truncating the history stopped at a finite time `τ` to at most `M` rounds gives the history
stopped at the time `M`. -/
lemma truncHist_stoppedValue_sigmaHistory {τ : Ω → WithTop ℕ} (hτ : τ ω ≠ ⊤) (M : ℕ) :
    truncHist M (stoppedValue (sigmaHistory O X Y) τ ω) =
      stoppedProcess (sigmaHistory O X Y) τ M ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hτ
  simp only [stoppedValue, stoppedProcess, ← hk, ← WithTop.coe_min, WithTop.untopD_coe,
    truncHist_sigmaHistory]

/-- The history stopped at the time `M` by a measurable time `τ` is measurable. -/
@[fun_prop]
lemma measurable_stoppedProcess_sigmaHistory (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) {τ : Ω → WithTop ℕ}
    (hτ : Measurable τ) (M : ℕ) :
    Measurable (stoppedProcess (sigmaHistory O X Y) τ M) :=
  measurable_stoppedValue_sigmaHistory hO hX hY (measurable_const.min hτ)

/-- For a measurable time `τ` that is almost surely finite, the law of the history stopped at the
time `M` is the image of the law of the history stopped at `τ` by the truncation to at most `M`
rounds. -/
lemma map_stoppedProcess_sigmaHistory_eq_map_truncHist {P : Measure Ω}
    (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    {τ : Ω → WithTop ℕ} (hτm : Measurable τ) (hτ : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) τ M) =
      (P.map (stoppedValue (sigmaHistory O X Y) τ)).map (truncHist M) := by
  rw [Measure.map_map (measurable_truncHist M)
    (measurable_stoppedValue_sigmaHistory hO hX hY hτm)]
  refine Measure.map_congr ?_
  filter_upwards [hτ] with ω hω
  exact (truncHist_stoppedValue_sigmaHistory hω M).symm

/-- The history stopped at the time `0` is the empty history. -/
@[simp]
lemma stoppedProcess_sigmaHistory_zero (τ : Ω → WithTop ℕ) :
    stoppedProcess (sigmaHistory O X Y) τ 0 = fun _ ↦ ⟨0, default⟩ := by
  funext ω
  rw [stoppedProcess_eq_of_le (i := 0) bot_le, sigmaHistory_apply, history_zero]

/-- If round `M` is played, the history stopped at the time `M` is the history of the first `M`
rounds. -/
lemma stoppedProcess_sigmaHistory_of_mem_notStoppedSet {M : ℕ}
    (hω : history O X Y M ω ∈ notStoppedSet S M) :
    stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M ω =
      sigmaHistory O X Y M ω :=
  stoppedProcess_eq_of_le (history_mem_notStoppedSet_iff.1 hω).le

/-- If round `M` is played, the history stopped at the time `M + 1` is the history of the first
`M + 1` rounds. -/
lemma stoppedProcess_sigmaHistory_succ_of_mem_notStoppedSet {M : ℕ}
    (hω : history O X Y M ω ∈ notStoppedSet S M) :
    stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) (M + 1) ω =
      sigmaHistory O X Y (M + 1) ω := by
  refine stoppedProcess_eq_of_le ?_
  have h_lt := history_mem_notStoppedSet_iff.1 hω
  exact_mod_cast Order.add_one_le_of_lt (α := ℕ∞) h_lt

/-- If round `M` is not played, the history stopped at the time `M + 1` is the history stopped at
the time `M`. -/
lemma stoppedProcess_sigmaHistory_succ_of_notMem_notStoppedSet {M : ℕ}
    (hω : history O X Y M ω ∉ notStoppedSet S M) :
    stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) (M + 1) ω =
      stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M ω := by
  have h_le : hittingAfter (sigmaHistory O X Y) S 0 ω ≤ M :=
    not_lt.1 (history_mem_notStoppedSet_iff.not.1 hω)
  rw [stoppedProcess_eq_of_ge (i := M) h_le,
    stoppedProcess_eq_of_ge (i := M + 1) (h_le.trans (by simp))]

/-- If round `M` is not played, the history stopped at the time `M` is not a history of `M` rounds
in `notStoppedSet S M`. -/
lemma stoppedProcess_sigmaHistory_notMem_image_notStoppedSet {M : ℕ}
    (hω : history O X Y M ω ∉ notStoppedSet S M) :
    stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M ω ∉
      Sigma.mk M '' notStoppedSet S M := by
  have h_le : hittingAfter (sigmaHistory O X Y) S 0 ω ≤ M :=
    not_lt.1 (history_mem_notStoppedSet_iff.not.1 hω)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (h_le.trans_lt (WithTop.coe_lt_top M)).ne
  rw [stoppedProcess_eq_of_ge (i := M) h_le, ← hk]
  simp only [WithTop.untopA, WithTop.untopD_coe, sigmaHistory_apply]
  rintro ⟨x, hx, hxk⟩
  -- The rule `S` stops after exactly `M` rounds, so the history of these rounds lies outside
  -- `notStoppedSet S M`.
  obtain ⟨rfl, hx'⟩ := Sigma.mk.inj_iff.1 hxk
  exact hω (eq_of_heq hx' ▸ hx)

variable {P : Measure Ω}

/-- The law of the history stopped at the time `M` is the sum of its restriction to the event
that round `M` is not played and of the image by `Sigma.mk M` of the law of the history of the
first `M` rounds, restricted to `notStoppedSet S M`. -/
lemma map_stoppedProcess_sigmaHistory_eq_add (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hS : MeasurableSet S) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M) =
      (P.restrict (history O X Y M ⁻¹' notStoppedSet S M)ᶜ).map
          (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M) +
        ((P.map (history O X Y M)).restrict (notStoppedSet S M)).map (Sigma.mk M) := by
  have hH := measurable_history hO hX hY M
  have hE : MeasurableSet (history O X Y M ⁻¹' notStoppedSet S M) :=
    hH (measurableSet_notStoppedSet hS M)
  have hm := measurable_stoppedProcess_sigmaHistory hO hX hY
    (measurable_hittingAfter_sigmaHistory hO hX hY hS) M
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hE, Measure.map_add _ _ hm]
  rw [add_comm, Measure.restrict_map hH (measurableSet_notStoppedSet hS M),
    Measure.map_map (measurable_sigmaMk M) hH]
  congr 1
  refine Measure.map_congr ((ae_restrict_iff' hE).2 (.of_forall fun ω hω ↦ ?_))
  exact stoppedProcess_sigmaHistory_of_mem_notStoppedSet hω

/-- The law of the history stopped at the time `M + 1` is the sum of the restriction to the event
that round `M` is not played of the law of the history stopped at the time `M`, and of the image
by `Sigma.mk (M + 1)` of the law of the history of the first `M + 1` rounds on the event that
round `M` is played. -/
lemma map_stoppedProcess_sigmaHistory_succ_eq_add (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hS : MeasurableSet S) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) (M + 1)) =
      (P.restrict (history O X Y M ⁻¹' notStoppedSet S M)ᶜ).map
          (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M) +
        ((P.restrict (history O X Y M ⁻¹' notStoppedSet S M)).map (history O X Y (M + 1))).map
          (Sigma.mk (M + 1)) := by
  have hE : MeasurableSet (history O X Y M ⁻¹' notStoppedSet S M) :=
    measurable_history hO hX hY M (measurableSet_notStoppedSet hS M)
  have hm := measurable_stoppedProcess_sigmaHistory hO hX hY
    (measurable_hittingAfter_sigmaHistory hO hX hY hS) (M + 1)
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hE, Measure.map_add _ _ hm]
  rw [add_comm, Measure.map_map (measurable_sigmaMk (M + 1)) (measurable_history hO hX hY _)]
  congr 1
  · refine Measure.map_congr ((ae_restrict_iff' hE.compl).2 (.of_forall fun ω hω ↦ ?_))
    exact stoppedProcess_sigmaHistory_succ_of_notMem_notStoppedSet hω
  · refine Measure.map_congr ((ae_restrict_iff' hE).2 (.of_forall fun ω hω ↦ ?_))
    exact stoppedProcess_sigmaHistory_succ_of_mem_notStoppedSet hω

/-- On the event that round `M` is not played, the history stopped at the time `M` is not a
history of `M` rounds in `notStoppedSet S M`. -/
lemma map_restrict_stoppedProcess_sigmaHistory_apply_image_notStoppedSet
    (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hS : MeasurableSet S) (M : ℕ) :
    (P.restrict (history O X Y M ⁻¹' notStoppedSet S M)ᶜ).map
        (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M)
      (Sigma.mk M '' notStoppedSet S M) = 0 := by
  have hm := measurable_stoppedProcess_sigmaHistory hO hX hY
    (measurable_hittingAfter_sigmaHistory hO hX hY hS) M
  have hT : MeasurableSet (Sigma.mk M '' notStoppedSet S M) :=
    (measurableEmbedding_sigmaMk M).measurableSet_image.2 (measurableSet_notStoppedSet hS M)
  rw [Measure.map_apply hm hT, Measure.restrict_apply (hm hT)]
  refine measure_mono_null (fun ω hω ↦ ?_) measure_empty
  exact stoppedProcess_sigmaHistory_notMem_image_notStoppedSet hω.2 hω.1

/-- The history stopped at the time `M` has at most `M` rounds. -/
lemma map_stoppedProcess_sigmaHistory_apply_compl_fst_le (hO : ∀ n, Measurable (O n))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) {τ : Ω → WithTop ℕ}
    (hτ : Measurable τ) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) τ M) {x | x.1 ≤ M}ᶜ = 0 := by
  have hm := measurable_stoppedProcess_sigmaHistory hO hX hY hτ M
  rw [Measure.map_apply hm (measurableSet_sigma_fst_le M).compl]
  refine measure_mono_null (fun ω hω ↦ hω ?_) measure_empty
  exact (fst_sigmaHistory _ ω).trans_le (WithTop.untopA_le (min_le_left _ _))

end StoppedAtTime

end Learning
