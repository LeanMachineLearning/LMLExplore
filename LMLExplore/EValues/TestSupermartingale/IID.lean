/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.Martingale.TestSupermartingale
public import LMLExplore.Probability.ProductMeasure.Blocks
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Probability.ProductMeasure
import Statlib.ForMathlib.Probability.Process.Filtration

/-!
# Products of i.i.d. copies of an e-variable

Let `e` be an e-variable for a null `S` of probability measures on `𝓧`. Evaluated along a
sequence `ω : ℕ → 𝓧`, the products `∏ i ≤ n, e (ω i)` of copies of `e` form a test
supermartingale, hence an e-process, for the i.i.d. null `{P ^ ℕ | P ∈ S}` and the filtration
`Filtration.piLE`, whose time `n` has seen the observations `ω 0, …, ω n`. This is the i.i.d.
instance of the wealth processes `ProbabilityTheory.isTestSupermartingale_mul_prod`: under
`P ^ ℕ`, the factor `e (ω (n + 1))` is independent of the past and has expectation at most `1`.

The blocks of `m` observations of an i.i.d. sequence are i.i.d., of law the `m`-fold product
(`MeasureTheory.measurePreserving_seqBlock_infinitePi`). Applied to them, Ville's inequality for
these e-processes bounds the probability that the product `seqBlockProd m V k` of a function `V`
of `m` observations over the first `k` blocks ever reaches a level `c` by `c⁻¹`, when `V` has
expectation at most `1` under the `m`-fold product of `P`.

## Main statements

* `ProbabilityTheory.IsEVar.isTestSupermartingale_prod_piLE`: the products of copies of an
  e-variable form a test supermartingale for the i.i.d. null.
* `ProbabilityTheory.IsEVar.isEProcess_prod_piLE`: they form an e-process for the i.i.d. null.
* `ProbabilityTheory.measure_exists_le_seqBlockProd_le`: Ville's inequality for products over
  blocks.

## Implementation notes

The statement of `ProbabilityTheory.measure_exists_le_seqBlockProd_le` is adapted from
`EValuesResearch/Results/NumeraireAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, where it is proved by optional stopping for the product stopped
when it reaches `c`; here it is Ville's inequality for the e-process
`ProbabilityTheory.IsEVar.isEProcess_prod_piLE` along the blocks.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S : Set (Measure 𝓧)} {e : 𝓧 → ℝ≥0∞}

/-- **Products of copies of an e-variable form a test supermartingale.** If `e` is an e-variable
for a null `S` of probability measures, the products `∏ i ≤ n, e (ω i)` form a test
supermartingale for the i.i.d. null `{P ^ ℕ | P ∈ S}` and `Filtration.piLE`. -/
theorem IsEVar.isTestSupermartingale_prod_piLE (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (he : IsEVar e S) :
    IsTestSupermartingale (fun n ω ↦ ∏ i : Fin (n + 1), e (ω i))
      (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) (iidNull S) := by
  set T := iidNull S with hT
  have h0 : ∀ P ∈ T, ∫⁻ ω, e (ω 0) ∂P ≤ 1 := by
    refine hT ▸ forall_mem_iidNull.2 fun P hP ↦ ?_
    have := hS P hP
    rw [(measurePreserving_eval_infinitePi (fun _ ↦ P) 0).lintegral_comp he.measurable]
    exact he.lintegral_le_one hP
  have hF : ∀ k, IsCondEVar (fun ω : ℕ → 𝓧 ↦ e (ω (k + 1))) (Filtration.piLE k) T := by
    refine fun k ↦ ⟨he.measurable.comp (measurable_pi_apply _), ?_⟩
    refine hT ▸ forall_mem_iidNull.2 fun P hP s hs ↦ ?_
    have := hS P hP
    rw [setLIntegral_comp_eval_succ P he.measurable k hs]
    exact mul_le_of_le_one_right' (he.lintegral_le_one hP)
  have hM := isTestSupermartingale_mul_prod (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
    (he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) h0
    (fun k ↦ he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) hF
  convert hM using 3 with n ω
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ e (ω i)), Finset.prod_range_succ', mul_comm]
  simp only [Function.comp_apply]

/-- **Products of copies of an e-variable form an e-process.** If `e` is an e-variable for a null
`S` of probability measures, the products `∏ i ≤ n, e (ω i)` form an e-process for the i.i.d.
null `{P ^ ℕ | P ∈ S}` and `Filtration.piLE`. -/
theorem IsEVar.isEProcess_prod_piLE (hS : ∀ P ∈ S, IsProbabilityMeasure P) (he : IsEVar e S) :
    IsEProcess (fun n ω ↦ ∏ i : Fin (n + 1), e (ω i))
      (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) (iidNull S) :=
  (he.isTestSupermartingale_prod_piLE hS).isEProcess fun P hP ↦
    (isProbabilityMeasure_of_mem_iidNull hS P hP).measure_univ.le

/-- **Ville's inequality for products over blocks.** If a function `V` of `m` observations has
expectation at most `1` under the `m`-fold product of `P`, then under the i.i.d. law of `P` the
product of `V` over the first `k` blocks of `m` observations reaches `c` for some `k` with
probability at most `c⁻¹`. If `P` is not a probability measure, its i.i.d. law is `0`. -/
theorem measure_exists_le_seqBlockProd_le (P : Measure 𝓧) {m : ℕ} {V : (Fin m → 𝓧) → ℝ≥0∞}
    (hV : Measurable V) (hVP : ∫⁻ x, V x ∂Measure.pi (fun _ : Fin m ↦ P) ≤ 1) (c : ℝ≥0∞) :
    Measure.infinitePi (fun _ : ℕ ↦ P) {ω | ∃ k, c ≤ seqBlockProd m V k ω} ≤ c⁻¹ := by
  by_cases hP : IsProbabilityMeasure P
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ P) (i := 0) hP]
  rcases le_or_gt c 1 with hc | hc
  · exact prob_le_one.trans (ENNReal.one_le_inv.2 hc)
  -- the products of copies of `V` along the sequence of the blocks
  have hE := (show IsEVar V {Measure.pi fun _ : Fin m ↦ P} from
    ⟨hV, fun _ h ↦ h ▸ hVP⟩).isEProcess_prod_piLE (fun _ h ↦ h ▸ inferInstance)
  have hblocks := measurePreserving_seqBlock_infinitePi (fun _ ↦ P) m
  have hset : {ω | ∃ k, c ≤ seqBlockProd m V k ω} = (fun ω j ↦ seqBlock m j ω) ⁻¹'
      {y | ∃ n, c ≤ ∏ i : Fin (n + 1), V (y i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage,
      Fin.prod_univ_eq_prod_range (fun i ↦ V (seqBlock m i ω)), ← seqBlockProd_def]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨n + 1, hn⟩⟩
    obtain _ | n := k
    · exact absurd (hk.trans_eq (seqBlockProd_zero m V ω)) (not_le.2 hc)
    · exact ⟨n, hk⟩
  have hmeas : MeasurableSet {y : ℕ → Fin m → 𝓧 | ∃ n, c ≤ ∏ i : Fin (n + 1), V (y i)} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n ↦ measurableSet_le measurable_const
      (Finset.measurable_prod _ fun i _ ↦ hV.comp (measurable_pi_apply _))
  rw [hset, hblocks.measure_preimage hmeas.nullMeasurableSet]
  exact hE.measure_exists_le_le (infinitePi_mem_iidNull rfl) c

end ProbabilityTheory
