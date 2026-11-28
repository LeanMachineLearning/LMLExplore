/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
public import LMLExplore.Identification.SampleComplexity
import LeanMachineLearning.SequentialLearning.Deterministic
import LMLExplore.Bandits.ArrayModel.AlgEnvSeq
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.BipolarRate.Design.Algorithm
import LMLExplore.EValues.BipolarRate.SequentialTest
import LMLExplore.Identification.Basic
import LMLExplore.SequentialLearning.StoppedHistory

/-!
# Sequential tests with adaptive sampling attain the rate of the designs

An algorithm chooses at each round which of finitely many sources `a : α` to observe, the
sources sharing one observation space `𝓧`, and an instance is a Markov kernel `κ : Kernel α 𝓧`,
the law of the observations of each source. A *sequential test of level `δ`* of a set `Λ` of
instances is an identification algorithm, with a sampling rule and a stopping rule, that rejects
`Λ` when it stops and stops with probability at most `δ` under every instance of `Λ`
(`Learning.IdentAlg.IsLevelTest`); its output is ignored. For testing a known instance `κ`, the
smallest expected number of observations under `κ` of such a test is `log (1/δ) / D*` to first
order as `δ → 0`, where `D* = designRate κ Λ` is the rate of the designs [EVR26, Note 41].

* **No sampling rule does better.** Every test of level `δ` makes at least `log (1/δ) / D*`
  observations in expectation under `κ`: the constant `1/δ` is an e-variable at its stopping
  time, and the Wald inequality with a design
  (`Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`) bounds its expected
  logarithm `log (1/δ)` by `D*` times the expected number of observations.
* **Blocks of a near-optimal shape attain it.** For every real `d' < D*` there is a shape
  `r : α → ℕ` of blocks whose bipolar rate per observation exceeds `d'`
  (`ProbabilityTheory.designRate_eq_iSup_bipolarRate`). The algorithm that samples the sources in
  successive blocks of shape `r`, whatever it observes, sees i.i.d. blocks with the law of the
  table of the design `r`, and the sequential tests at the bipolar rate of the blocks
  (`ProbabilityTheory.exists_isLevelStoppingTime_limsup_lintegral_div_log_le`) give tests of
  every level `δ` with `limsup_{δ → 0} 𝔼_κ[τ_δ] / log (1/δ) ≤ 1 / d'`.

## Main definitions

* `Learning.IdentAlg.IsLevelTest A Λ δ`: the identification algorithm `A` is a sequential test of
  level `δ` of the set of instances `Λ`.

## Main statements

* `Learning.IdentAlg.IsLevelTest.toENNReal_log_inv_div_designRate_le_expectedStoppingTime`: every
  test of level `δ` has `log (1/δ) / D* ≤ 𝔼_κ[τ]`.
* `ProbabilityTheory.exists_isLevelTest_limsup_expectedStoppingTime_div_log_le`: for every real
  `0 < d' < D*`, tests `A δ` of every level `δ` with
  `limsup_{δ → 0} 𝔼_κ[τ_δ] / log (1/δ) ≤ 1 / d'`.
* `ProbabilityTheory.tendsto_iInf_expectedStoppingTime_div_log`: the smallest expected number of
  observations of a test of level `δ`, divided by `log (1/δ)`, tends to `1 / D*` as `δ → 0`.

## Implementation notes

The tests are LML's identification algorithms `IdentAlg Unit α 𝓧 𝓓`, whose stopping time is the
hitting time of a stopping rule of the history; this is the framework of the Wald inequality with
a design for algorithms and of `LMLExplore.Identification.expectedStoppingTime`. Levels are in
`ℝ≥0∞`, `log (1/δ)` is `(ENNReal.log δ⁻¹).toENNReal`, and the limits along `𝓝[>] 0` in `ℝ≥0∞`,
as for the sequential tests of one stream (`ProbabilityTheory.IsLevelStoppingTime`); `1 / 0 = ∞`
and `1 / ∞ = 0`. The blocks are i.i.d. by LMLExplore's array model
(`LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit`): the sampling in blocks reads the entries of
the i.i.d. table of observations without repetition. The space of the sources is standard Borel,
as the Wald inequality and the array model ask; the observation space is any measurable space.

The statements and proofs are adapted from `EValuesResearch/Results/DesignTesting.lean` (commit
`cb8238f`) in the paper project `RemyDegenne/evalues_research`, where they formalize
[EVR26, Note 41, Theorem 4], rewritten on the API of LMLExplore.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory ProbabilityTheory Filter LMLExplore.Identification
open scoped ENNReal Topology

namespace Learning.IdentAlg

variable {α 𝓧 𝓓 : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓓 : MeasurableSpace 𝓓}

/-- The identification algorithm `A`, which chooses at each round one of the sources `α`, is a
**sequential test of level `δ`** of the set `Λ` of instances: it rejects `Λ` when it stops, which
happens with probability at most `δ` under every instance of `Λ`. Its output is ignored. -/
structure IsLevelTest (A : IdentAlg Unit α 𝓧 𝓓) (Λ : Set (Kernel α 𝓧)) (δ : ℝ≥0∞) : Prop where
  /-- Under every instance of `Λ`, the test stops with probability at most `δ`. -/
  measure_stoppingTime_lt_top_le : ∀ (ν : Kernel α 𝓧) [IsMarkovKernel ν], ν ∈ Λ →
    trajMeasure A.alg (Environment.bandit ν)
      {ω | A.stoppingTime IT.obs IT.action IT.feedback ω < ⊤} ≤ δ

/-- **No sampling rule does better than `log (1/δ) / D*`** [EVR26, Note 41, Theorem 4]. A
sequential test of level `δ` of the set `Λ` of instances makes at least `log (1/δ) / D*`
observations in expectation under the instance `κ`, where `D*` is the rate of the designs of `κ`
against `Λ`. The left side is in `ℝ≥0∞`, with `log (1/δ)` replaced by `0` for `δ ≥ 1`: if
`D* = 0` and `δ < 1`, the expected number of observations is infinite, and if `D* = ∞` the bound
is `0`. It follows from the Wald inequality with a design for the constant `1/δ`, which is an
e-variable at the stopping time. -/
theorem IsLevelTest.toENNReal_log_inv_div_designRate_le_expectedStoppingTime [Fintype α]
    [StandardBorelSpace α] {A : IdentAlg Unit α 𝓧 𝓓} {Λ : Set (Kernel α 𝓧)} {δ : ℝ≥0∞}
    (hA : A.IsLevelTest Λ δ) (κ : Kernel α 𝓧) [IsMarkovKernel κ]
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) :
    (ENNReal.log δ⁻¹).toENNReal /
        (designRate (fun a ↦ κ a)
          ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ)).toENNReal ≤
      expectedStoppingTime A (Environment.bandit κ) := by
  set E := expectedStoppingTime A (Environment.bandit κ)
  rcases eq_or_ne E ⊤ with hE | hE
  · exact hE ▸ le_top
  have : Nonempty α := nonempty_of_isProbabilityMeasure (A.alg.policyZero ())
  rcases Λ.eq_empty_or_nonempty with rfl | hΛne
  · -- against no instance, the rate of the designs is infinite
    have hD : designRate (fun a ↦ κ a) ∅ = ⊤ := by
      refine eq_top_iff.2 ((le_of_eq ?_).trans
        (designValue_div_le_designRate _ _ fun _ ↦ 1))
      rw [designValue_def, Set.image_empty, maxEPower_empty]
      refine (EReal.top_div_of_pos_ne_top ?_ (EReal.natCast_ne_top _)).symm
      have : 0 < ∑ _a : α, 1 := by simpa using Fintype.card_pos
      exact_mod_cast this
    rw [Set.image_empty, hD, EReal.toENNReal_top, ENNReal.div_top]
    exact zero_le
  have hseq := IT.isAlgEnvSeq_trajMeasure A.alg (Environment.bandit κ)
  -- the constant `1/δ` is an e-variable at the stopping time for `Λ`
  have hGΛ : ∀ (ν : Kernel α 𝓧) [IsMarkovKernel ν], ν ∈ Λ →
      ∫⁻ _ in A.stopSet, δ⁻¹ ∂stoppedHistMeasure A.alg (Environment.bandit ν) A.stopSet ≤ 1 := by
    intro ν _ hν
    have h := hA.measure_stoppingTime_lt_top_le ν hν
    simp_rw [lt_top_iff_ne_top, IdentAlg.stoppingTime_def] at h
    rw [← (IT.isAlgEnvSeq_trajMeasure A.alg
      (Environment.bandit ν)).setLIntegral_comp_stoppedValue_sigmaHistory A.measurableSet_stopSet
      measurable_const, setLIntegral_const]
    calc δ⁻¹ * _ ≤ δ⁻¹ * δ := by gcongr
    _ ≤ 1 := ENNReal.inv_mul_le_one δ
  have hτ := (stopsAS_iff_ae_stoppingTime_ne_top hseq).1 (.of_expectedStoppingTime_ne_top hE)
  have hW := hseq.eintegral_log_le_designRate_mul_lintegral hΛ hΛne A.measurableSet_stopSet
    measurable_const hGΛ hτ
  rw [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one, ← IdentAlg.stoppingTime_def,
    ← expectedStoppingTime_def] at hW
  -- `log (1/δ) ≤ D* 𝔼_κ[τ]`
  refine ENNReal.div_le_of_le_mul ?_
  calc (ENNReal.log δ⁻¹).toENNReal
      ≤ (designRate (fun a ↦ κ a)
          ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ) * (E : EReal)).toENNReal :=
        EReal.toENNReal_le_toENNReal hW
  _ = E * (designRate (fun a ↦ κ a)
          ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ)).toENNReal := by
      rw [mul_comm, EReal.toENNReal_mul (EReal.coe_ennreal_nonneg _), EReal.toENNReal_coe]

end Learning.IdentAlg

namespace ProbabilityTheory

open Learning

variable {α 𝓧 𝓓 : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓓 : MeasurableSpace 𝓓} [Fintype α]

/-! ### Sampling in blocks -/

section Blocks

variable (r : α → ℕ) [NeZero (∑ a, r a)]

/-- The rounds of the sampling in blocks of shape `r`: the entry `p` of the block `j` is observed
at round `j * |r| + e p`, for an enumeration `e` of the entries of a block. -/
private noncomputable def blockRound : ℕ × (Σ a, Fin (r a)) ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl ℕ)
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma]))).trans
    (Nat.divModEquiv (∑ a, r a)).symm

/-- The source observed at round `t` by the sampling in blocks of shape `r`. -/
private noncomputable def blockSchedule (t : ℕ) : α := ((blockRound r).symm t).2.1

/-- The sampling rule that samples the sources in blocks of shape `r`, whatever it observes. -/
private noncomputable def blockAlg : Algorithm Unit α 𝓧 :=
  Algorithm.deterministic (fun n _ ↦ blockSchedule r n) fun _ ↦ measurable_const

/-- The sequence of the blocks of shape `r` of a sequence `Y` of observations: the entry `p` of
the block `j` is the observation of the round `blockRound r (j, p)`. -/
private noncomputable def blockSeq {Ω : Type*} (Y : ℕ → Ω → 𝓧) (ω : Ω) : ℕ → (Σ a, Fin (r a)) → 𝓧 :=
  fun j p ↦ Y (blockRound r (j, p)) ω

variable {r}

/-- The round of the entry `p` of a block observes the source of `p`. -/
private lemma blockSchedule_blockRound (q : ℕ × (Σ a, Fin (r a))) :
    blockSchedule r (blockRound r q) = q.2.1 := by
  simp [blockSchedule]

/-- The entries of the block `j` are observed before the end of the block `j`. -/
private lemma blockRound_lt {j k : ℕ} (hjk : j < k) (p : Σ a, Fin (r a)) :
    blockRound r (j, p) < k * ∑ a, r a := by
  simp only [blockRound, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Nat.divModEquiv_symm_apply]
  calc j * ∑ a, r a + _ < j * ∑ a, r a + ∑ a, r a := Nat.add_lt_add_left (Fin.isLt _) _
  _ = (j + 1) * ∑ a, r a := by ring
  _ ≤ k * ∑ a, r a := Nat.mul_le_mul_right _ hjk

/-- **The blocks are i.i.d. in the array model.** When the sources are sampled in blocks of shape
`r`, the blocks of the observations of the array model are i.i.d. with the law of the table of the
design `r`: the algorithm reads the entries of the i.i.d. table of observations without
repetition. -/
private lemma hasLaw_blockSeq_arrayMeasure [DecidableEq α] [Nonempty α] [StandardBorelSpace α]
    (ν : Kernel α 𝓧) [IsMarkovKernel ν] :
    HasLaw (blockSeq r (Bandits.ArrayModel.reward (blockAlg r : Algorithm Unit α 𝓧)))
      (Measure.infinitePi fun _ : ℕ ↦ designLaw (fun a ↦ ν a) r)
      (Bandits.ArrayModel.arrayMeasure ν) := by
  set s := blockSchedule r
  -- the number of the rounds before `t` that observe the source `a`
  set c : α → ℕ → ℕ := fun a t ↦ pullCount (fun u (_ : Unit) ↦ s u) a t ()
  -- round `t` reads the observation number `c (s t) t` of the source `s t`, and two rounds read
  -- different entries
  have hc : Function.Injective fun t ↦ (c (s t) t, s t) := by
    have key (t t' : ℕ) (ht : t < t') (ha : s t = s t') : c (s t) t < c (s t') t' := by
      rw [← ha]
      calc c (s t) t < c (s t) (t + 1) := by
            simp only [c, pullCount_action_eq_pullCount_add_one, Nat.lt_add_one]
      _ ≤ c (s t) t' := pullCount_mono _ ht ()
    intro t t' h
    simp only [Prod.mk.injEq] at h
    rcases lt_trichotomy t t' with htt | htt | htt
    · exact absurd h.1 (key t t' htt h.2).ne
    · exact htt
    · exact absurd h.1.symm (key t' t htt h.2.symm).ne
  -- the entries read by the blocks
  set g : ℕ × (Σ a, Fin (r a)) → ℕ × α := fun q ↦ (c q.2.1 (blockRound r q), q.2.1)
  have hg : Function.Injective g := by
    have : g = (fun t ↦ (c (s t) t, s t)) ∘ blockRound r := by
      ext q <;> simp [g, s, blockSchedule_blockRound]
    rw [this]
    exact hc.comp (blockRound r).injective
  -- reading the i.i.d. table at the entries `g` gives i.i.d. blocks of shape `r`
  have hlaw : (Bandits.streamMeasure ν).map (fun x j p ↦ x (g (j, p)).1 (g (j, p)).2) =
      Measure.infinitePi fun _ : ℕ ↦ designLaw (fun a ↦ ν a) r := by
    have h_eq : (fun (x : ℕ → α → 𝓧) j p ↦ x (g (j, p)).1 (g (j, p)).2) =
        (MeasurableEquiv.curry ℕ (Σ a, Fin (r a)) 𝓧) ∘ (fun z q ↦ z (g q)) ∘
          (MeasurableEquiv.curry ℕ α 𝓧).symm := by
      ext x j p
      rfl
    rw [h_eq, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
      ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), Bandits.streamMeasure,
      Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (a : α) ↦ ν a),
      Measure.map_infinitePi_infinitePi_of_inj hg,
      Measure.infinitePi_map_curry (fun (_ : ℕ) (p : Σ a, Fin (r a)) ↦ ν p.1)]
    simp_rw [designLaw_def, Measure.infinitePi_eq_pi]
  have hsnd : HasLaw Prod.snd (Bandits.streamMeasure ν) (Bandits.ArrayModel.arrayMeasure ν) := by
    rw [Bandits.ArrayModel.arrayMeasure]
    exact hasLaw_snd_prod _ _
  have hmeas : Measurable fun (x : ℕ → α → 𝓧) j p ↦ x (g (j, p)).1 (g (j, p)).2 :=
    Measurable.of_eval fun j ↦ Measurable.of_eval fun p ↦
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hact := (LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit
    (blockAlg r : Algorithm Unit α 𝓧) ν).action_ae_all_eq_deterministic
  refine ((⟨hmeas.aemeasurable, hlaw⟩ : HasLaw _ _ _).comp hsnd).congr ?_
  filter_upwards [hact] with ω hω
  have hω' (n : ℕ) : Bandits.ArrayModel.action (blockAlg r : Algorithm Unit α 𝓧) n ω = s n :=
    hω n
  ext j p
  simp only [Function.comp_apply, blockSeq, Bandits.ArrayModel.reward_eq, hω', pullCount, g, c,
    blockSchedule_blockRound, s]

/-- **The blocks are i.i.d.** Under the law of the run of the sampling in blocks of shape `r`
against the instance `ν`, the blocks of the observations are i.i.d. with the law of the table of
the design `r`. -/
private lemma hasLaw_blockSeq_trajMeasure [Nonempty α] [StandardBorelSpace α] (ν : Kernel α 𝓧)
    [IsMarkovKernel ν] :
    HasLaw (blockSeq r IT.feedback) (Measure.infinitePi fun _ : ℕ ↦ designLaw (fun a ↦ ν a) r)
      (trajMeasure (blockAlg r : Algorithm Unit α 𝓧) (Environment.bandit ν)) := by
  classical
  have h := LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit (blockAlg r : Algorithm Unit α 𝓧) ν
  have hm : Measurable (blockSeq r (IT.feedback (𝓞 := Unit) (𝓐 := α) (𝓨 := 𝓧))) :=
    Measurable.of_eval fun j ↦ Measurable.of_eval fun p ↦ IT.measurable_feedback _
  exact HasLaw.comp_of_hasLaw_comp hm.aemeasurable h.hasLaw_trajectory HasLaw.id
    (hasLaw_blockSeq_arrayMeasure ν)

/-- The first blocks of shape `r` read in a history of `n` rounds of the sampling in blocks,
padded with the block `b₀`. -/
private noncomputable def padBlocks (b₀ : (Σ a, Fin (r a)) → 𝓧) (n : ℕ) (h : Hist Unit α 𝓧 n) :
    ℕ → (Σ a, Fin (r a)) → 𝓧 :=
  fun j p ↦ if hj : blockRound r (j, p) < n then (h ⟨_, hj⟩).2.2 else b₀ p

/-- The padded blocks of a history are a measurable function of the history. -/
private lemma measurable_padBlocks (b₀ : (Σ a, Fin (r a)) → 𝓧) (n : ℕ) :
    Measurable (padBlocks (α := α) b₀ n) := by
  refine Measurable.of_eval fun j ↦ Measurable.of_eval fun p ↦ ?_
  simp only [padBlocks]
  split_ifs
  · exact measurable_snd.comp (measurable_snd.comp (measurable_pi_apply _))
  · exact measurable_const

/-- The test that samples the sources in blocks of shape `r` and stops after the `k` complete
blocks at which the test `τ` of the sequence of the blocks stops. -/
private noncomputable def blockTest [Nonempty 𝓓] (b₀ : (Σ a, Fin (r a)) → 𝓧)
    {τ : (ℕ → (Σ a, Fin (r a)) → 𝓧) → WithTop ℕ} (hτ : IsStoppingTime Filtration.piLT τ) :
    IdentAlg Unit α 𝓧 𝓓 :=
  ofStop (blockAlg r) (fun n h ↦ ∃ k : ℕ, n = k * ∑ a, r a ∧ τ (padBlocks b₀ n h) = k)
    (fun n ↦ by
      simp only [Set.ofPred_exists, Set.ofPred_and]
      exact MeasurableSet.iUnion fun k ↦ (MeasurableSet.const _).inter
        (measurable_padBlocks b₀ n (Filtration.le _ k _ (hτ.measurableSet_eq k))))
    fun _ ↦ Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))

/-- The test in blocks stops after `τ` complete blocks: its stopping time is `τ * |r|` at the
sequence of the blocks of the observations. -/
private lemma stoppingTime_blockTest [Nonempty 𝓓] (b₀ : (Σ a, Fin (r a)) → 𝓧)
    {τ : (ℕ → (Σ a, Fin (r a)) → 𝓧) → WithTop ℕ} (hτ : IsStoppingTime Filtration.piLT τ)
    (ω : ℕ → Round Unit α 𝓧) :
    (blockTest b₀ hτ : IdentAlg Unit α 𝓧 𝓓).stoppingTime IT.obs IT.action IT.feedback ω =
      (τ (blockSeq r IT.feedback ω)).map (· * ∑ a, r a) := by
  -- the history of `k |r|` rounds stops exactly when `τ = k` at the sequence of the blocks
  have key (n : ℕ) : (⟨n, history IT.obs IT.action IT.feedback n ω⟩ : Σ n, Hist Unit α 𝓧 n) ∈
      (blockTest b₀ hτ : IdentAlg Unit α 𝓧 𝓓).stopSet ↔
        ∃ k : ℕ, n = k * ∑ a, r a ∧ τ (blockSeq r IT.feedback ω) = k := by
    simp only [blockTest, mem_stopSet_ofStop]
    refine exists_congr fun k ↦ and_congr_right fun hn ↦ ?_
    refine (hτ.measurableSet_eq k).dependsOn_of_piLT fun j hj ↦ ?_
    ext p
    have hlt : blockRound r (j, p) < n := hn ▸ blockRound_lt hj p
    simp only [padBlocks, blockSeq, dite_eq_left hlt]
    rfl
  induction hτω : τ (blockSeq r IT.feedback ω) using WithTop.recTopCoe with
  | top =>
    refine IdentAlg.stoppingTime_eq_top_iff.2 fun n hn ↦ ?_
    obtain ⟨k, -, hk⟩ := (key n).1 hn
    exact WithTop.top_ne_coe (hτω ▸ hk)
  | coe k =>
    refine IdentAlg.stoppingTime_eq_coe_iff.2 ⟨(key _).2 ⟨k, rfl, hτω⟩, fun j hj hmem ↦ ?_⟩
    obtain ⟨k', hk', hk'τ⟩ := (key j).1 hmem
    have hkk : k = k' := Option.some.inj (hτω.symm.trans hk'τ)
    exact hj.ne (hkk ▸ hk')

/-- **The level of the test in blocks**: if the test `τ` of the sequence of the blocks is a
sequential test of level `δ` for the i.i.d. blocks of the instances of `Λ`, so is the test in
blocks for `Λ`. -/
private lemma isLevelTest_blockTest [Nonempty 𝓓] [Nonempty α] [StandardBorelSpace α]
    (b₀ : (Σ a, Fin (r a)) → 𝓧) {Λ : Set (Kernel α 𝓧)}
    {τ : (ℕ → (Σ a, Fin (r a)) → 𝓧) → WithTop ℕ} {δ : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT
      (iidNull ((fun ν ↦ designLaw ν r) '' ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ))) δ) :
    (blockTest b₀ hτ.isStoppingTime : IdentAlg Unit α 𝓧 𝓓).IsLevelTest Λ δ := by
  refine ⟨fun ν _ hν ↦ ?_⟩
  have hlaw := hasLaw_blockSeq_trajMeasure (r := r) ν
  have hset : {ω | (blockTest b₀ hτ.isStoppingTime : IdentAlg Unit α 𝓧 𝓓).stoppingTime IT.obs
      IT.action IT.feedback ω < ⊤} = blockSeq r IT.feedback ⁻¹' {x | τ x < ⊤} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, stoppingTime_blockTest, lt_top_iff_ne_top,
      ne_eq, WithTop.map_eq_top_iff]
  rw [hset, blockTest, alg_ofStop, ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable
    (measurableSet_lt hτ.isStoppingTime.measurable' measurable_const), hlaw.map_eq]
  exact hτ.measure_lt_top_le _
    (infinitePi_mem_iidNull (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hν)))

/-- **The expected number of observations of the test in blocks** is `|r|` times the expected
number of blocks of the test `τ` under the i.i.d. blocks of `κ`. -/
private lemma expectedStoppingTime_blockTest [Nonempty 𝓓] [Nonempty α] [StandardBorelSpace α]
    (b₀ : (Σ a, Fin (r a)) → 𝓧) {τ : (ℕ → (Σ a, Fin (r a)) → 𝓧) → WithTop ℕ}
    (hτ : IsStoppingTime Filtration.piLT τ) (κ : Kernel α 𝓧) [IsMarkovKernel κ] :
    expectedStoppingTime (blockTest b₀ hτ : IdentAlg Unit α 𝓧 𝓓) (Environment.bandit κ) =
      (∑ a, r a : ℕ) * ∫⁻ x, ENat.toENNReal (τ x)
        ∂(Measure.infinitePi fun _ : ℕ ↦ designLaw (fun a ↦ κ a) r) := by
  have hlaw := hasLaw_blockSeq_trajMeasure (r := r) κ
  have hm : Measurable fun x ↦ ENat.toENNReal (τ x) :=
    Measurable.of_discrete.comp hτ.measurable'
  rw [expectedStoppingTime_def, blockTest, alg_ofStop, ← lintegral_const_mul _ hm,
    ← hlaw.lintegral_comp (hm.const_mul _).aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  have h := stoppingTime_blockTest (mα := mα) (m𝓓 := m𝓓) b₀ hτ ω
  rw [blockTest] at h
  rw [h]
  induction τ (blockSeq r IT.feedback ω) using WithTop.recTopCoe with
  | top => exact (ENNReal.mul_top (Nat.cast_ne_zero.2 (NeZero.ne _))).symm
  | coe k =>
    change ENat.toENNReal ((k * ∑ a, r a : ℕ) : ℕ∞) = (∑ a, r a : ℕ) * ENat.toENNReal (k : ℕ∞)
    rw [ENat.toENNReal_coe, ENat.toENNReal_coe, Nat.cast_mul, mul_comm]

end Blocks

/-- **Blocks of a near-optimal shape attain `log (1/δ) / D*` to first order**
[EVR26, Note 41, Theorem 4]. Let `κ` be an instance and `Λ` a set of instances, with rate of the
designs `D*`. For every real `d' > 0` below `D*` there are sequential tests `A δ` of every level
`δ` of `Λ` whose expected numbers of observations under `κ` satisfy
`limsup_{δ → 0} 𝔼_κ[τ_δ] / log (1/δ) ≤ 1 / d'`. The tests sample the sources in successive
blocks of a shape `r` whose bipolar rate per observation exceeds `d'`, whatever they observe, and
stop when the sequential test at the bipolar rate of the i.i.d. blocks stops; they are built for
`κ`. The rate `D*` may be infinite. -/
theorem exists_isLevelTest_limsup_expectedStoppingTime_div_log_le [StandardBorelSpace α]
    [Nonempty 𝓓] (κ : Kernel α 𝓧) [IsMarkovKernel κ] {Λ : Set (Kernel α 𝓧)}
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) {d' : ℝ} (hd' : 0 < d')
    (hd'D : (d' : EReal) < designRate (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ)) :
    ∃ A : ℝ≥0∞ → IdentAlg Unit α 𝓧 𝓓, (∀ δ, (A δ).IsLevelTest Λ δ) ∧
      limsup (fun δ ↦ expectedStoppingTime (A δ) (Environment.bandit κ) /
        (ENNReal.log δ⁻¹).toENNReal) (𝓝[>] 0) ≤ ENNReal.ofReal d'⁻¹ := by
  set Λ' := (fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ
  have hΛ' : ∀ ν ∈ Λ', ∀ a, IsProbabilityMeasure (ν a) := by
    rintro _ ⟨ν, hν, rfl⟩ a
    have := hΛ ν hν
    infer_instance
  -- a shape `r` of blocks whose bipolar rate per observation exceeds `d'`
  rw [designRate_eq_iSup_bipolarRate _ hΛ'] at hd'D
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 hd'D
  have hR : 0 < ∑ a, r a := by
    refine Nat.pos_of_ne_zero fun hR0 ↦ ?_
    rw [hR0, Nat.cast_zero, EReal.div_zero] at hr
    exact (EReal.coe_pos.2 hd').not_gt hr
  have : NeZero (∑ a, r a) := ⟨hR.ne'⟩
  obtain ⟨a₀, -, -⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ 0) (g := r)
    (by simpa using hR)
  have : Nonempty α := ⟨a₀⟩
  have : Nonempty 𝓧 := nonempty_of_isProbabilityMeasure (κ a₀)
  set R := ∑ a, r a
  -- the sequential tests at the bipolar rate of the i.i.d. blocks
  obtain ⟨τ, hτ, hlim⟩ := exists_isLevelStoppingTime_limsup_lintegral_div_log_le
    (designLaw (fun a ↦ κ a) r) (S₁ := (fun ν ↦ designLaw ν r) '' Λ')
    (by rintro _ ⟨ν, hν, rfl⟩; have := hΛ' ν hν; infer_instance)
    (by positivity : 0 < (R : ℝ) * d') ((EReal.coe_lt_div_natCast_iff hR).1 hr)
  obtain ⟨b₀⟩ : Nonempty ((Σ a, Fin (r a)) → 𝓧) := inferInstance
  refine ⟨fun δ ↦ blockTest b₀ (hτ δ).isStoppingTime, fun δ ↦ isLevelTest_blockTest b₀ (hτ δ), ?_⟩
  -- `R / (R d') = 1 / d'`
  have hR0 : (R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  simp_rw [expectedStoppingTime_blockTest, mul_div_assoc]
  rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.natCast_ne_top R)]
  calc (R : ℝ≥0∞) * limsup _ _ ≤ R * ENNReal.ofReal ((R : ℝ) * d')⁻¹ := by gcongr
  _ = ENNReal.ofReal d'⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_inv_of_pos hd',
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.mul_inv (Or.inl hR0) (Or.inl (ENNReal.natCast_ne_top R)), ← mul_assoc,
      ENNReal.mul_inv_cancel hR0 (ENNReal.natCast_ne_top R), one_mul]

/-- **The smallest expected number of observations of a test is `log (1/δ) / D*`** to first order
[EVR26, Note 41, Theorem 4]. Let `κ` be an instance and `Λ` a set of instances, with rate of the
designs `D*`. The smallest expected number of observations under `κ` of a sequential test of level
`δ` of `Λ`, divided by `log (1/δ)`, tends to `1 / D*` as `δ → 0`, in `ℝ≥0∞` with `1 / 0 = ∞` and
`1 / ∞ = 0`: no sampling rule does better than `log (1/δ) / D*`
(`Learning.IdentAlg.IsLevelTest.toENNReal_log_inv_div_designRate_le_expectedStoppingTime`), and
blocks of a near-optimal shape attain it
(`ProbabilityTheory.exists_isLevelTest_limsup_expectedStoppingTime_div_log_le`). Nothing is
assumed of `D*`. -/
theorem tendsto_iInf_expectedStoppingTime_div_log [StandardBorelSpace α] [Nonempty 𝓓]
    (κ : Kernel α 𝓧) [IsMarkovKernel κ] {Λ : Set (Kernel α 𝓧)}
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) :
    Tendsto (fun δ ↦ (⨅ (A : IdentAlg Unit α 𝓧 𝓓) (_ : A.IsLevelTest Λ δ),
        expectedStoppingTime A (Environment.bandit κ)) / (ENNReal.log δ⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 (designRate (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ)).toENNReal⁻¹) := by
  set D := designRate (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ (by isBoundedDefault) (by isBoundedDefault)
  · -- no test does better than `log (1/δ) / D*`
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ≥0∞)] with δ hδ
    have h0 : (ENNReal.log δ⁻¹).toENNReal ≠ 0 := EReal.toENNReal_ne_zero_iff.2
      (ENNReal.zero_lt_log_iff.2 (ENNReal.one_lt_inv.2 hδ.2))
    have htop : (ENNReal.log δ⁻¹).toENNReal ≠ ⊤ := EReal.toENNReal_ne_top_iff.2
      (ENNReal.log_eq_top_iff.not.2 (ENNReal.inv_ne_top.2 hδ.1.ne'))
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
    refine le_iInf₂ fun A hA ↦ ?_
    have h := hA.toENNReal_log_inv_div_designRate_le_expectedStoppingTime κ hΛ
    rwa [ENNReal.div_eq_inv_mul] at h
  -- the tests in blocks do better than every `c > 1 / D*`
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hctop
  · exact le_top
  have hc' : c⁻¹ < D.toENNReal := by rwa [ENNReal.inv_lt_iff_inv_lt]
  obtain ⟨d', hcd', hd'D⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc'
  have hd'0 : 0 < (d' : ℝ) := by
    have : (0 : ℝ≥0∞) < d' := (pos_iff_ne_zero.2 (ENNReal.inv_ne_zero.2 hctop)).trans hcd'
    exact_mod_cast this
  have hd'D' : ((d' : ℝ) : EReal) < D := calc
    ((d' : ℝ) : EReal) = ((d' : ℝ≥0∞) : EReal) := by
      rw [← ENNReal.ofReal_coe_nnreal, EReal.coe_ennreal_ofReal, max_eq_left d'.coe_nonneg]
    _ < (D.toENNReal : EReal) := EReal.coe_ennreal_lt_coe_ennreal_iff.2 hd'D
    _ = D := EReal.coe_toENNReal (designRate_nonneg _ _)
  obtain ⟨A, hA, hlim⟩ := exists_isLevelTest_limsup_expectedStoppingTime_div_log_le (𝓓 := 𝓓) κ hΛ
    hd'0 hd'D'
  calc limsup (fun δ ↦ (⨅ (A : IdentAlg Unit α 𝓧 𝓓) (_ : A.IsLevelTest Λ δ),
        expectedStoppingTime A (Environment.bandit κ)) / (ENNReal.log δ⁻¹).toENNReal) (𝓝[>] 0)
      ≤ limsup (fun δ ↦ expectedStoppingTime (A δ) (Environment.bandit κ) /
        (ENNReal.log δ⁻¹).toENNReal) (𝓝[>] 0) :=
      limsup_le_limsup (.of_forall fun δ ↦ ENNReal.div_le_div_right (iInf₂_le (A δ) (hA δ)) _)
  _ ≤ ENNReal.ofReal (d' : ℝ)⁻¹ := hlim
  _ ≤ c := by
    rw [ENNReal.ofReal_inv_of_pos hd'0, ENNReal.ofReal_coe_nnreal, ENNReal.inv_le_iff_inv_le]
    exact hcd'.le

end ProbabilityTheory
