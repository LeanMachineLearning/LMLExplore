/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import LMLExplore.Probability.Kernel.Composition.MeasureCompProd

/-!
# The law of a stopped history only depends on the rounds before stopping

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

## Main definitions

* `Learning.notStoppedSet S n`: the `n`-round histories after which the stopping rule `S` has not
  stopped, that is, none of whose prefixes belong to `S`.

## Main statements

* `Learning.history_mem_notStoppedSet_iff`: the history of the first `n` rounds belongs to
  `notStoppedSet S n` if and only if the hitting time of `S` is larger than `n`.
* `Learning.stoppedHistMeasure_congr`: if the step kernels of `(alg, env)` and `(alg', env')`
  agree on `notStoppedSet S n` for every `n`, then
  `stoppedHistMeasure alg env S = stoppedHistMeasure alg' env' S`.
-/

public section

open MeasureTheory ProbabilityTheory Set

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
  (measurable_sigma_mk m).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _)

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
      preimage_finSuccProd_symm_notStoppedBeforeSet, ← Measure.compProd_restrict_left hm,
      ← Measure.compProd_restrict_left hm, h_restrict,
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
      ((measurable_sigma_mk n) (hS.inter hB))) inter_subset_left

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

end Learning
