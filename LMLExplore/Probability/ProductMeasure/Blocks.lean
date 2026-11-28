/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.ProductMeasure
public import TauCeti.Probability.Process.PathLaw.Shift
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Probability.ProductMeasure
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.StrongLaw

/-!
# Blocks of a sequence, and the blocks of an i.i.d. sequence

The `j`-th block of `m` terms of a sequence `ω : ℕ → 𝓧` is `seqBlock m j ω : Fin m → 𝓧`, the terms
`j * m, …, j * m + m - 1`; the first block is the initial segment `initSeg m ω`, and the block
`j` is the initial segment of the sequence shifted by `j * m` terms. The product of a function
`V` of `m` terms over the first `k` blocks is `seqBlockProd m V k ω`, a function of the first
`k * m` terms.

Under a product `Measure.infinitePi μ` of probability measures, the blocks of `m` terms are
independent, the block `j` with the law `Measure.pi fun i : Fin m ↦ μ (j * m + i)`: the sequence of
the blocks is the currying of the reindexing `(j, i) ↦ j * m + i` of the terms, which is
injective. Under the i.i.d. law `Measure.infinitePi fun _ ↦ P` of a probability measure `P`, the
blocks are therefore i.i.d. with law the `m`-fold product `Measure.pi fun _ ↦ P`, the expectation
of a product over `k` blocks is the `k`-th power of the expectation of one factor, the strong law
of large numbers holds along the blocks, and so does Wald's bound on first passage times.

## Main definitions

* `MeasureTheory.seqBlock m j ω`: the `j`-th block of `m` terms of `ω`.
* `MeasureTheory.seqBlockProd m V k ω`: the product of `V` over the first `k` blocks of `m` terms.

## Main statements

* `MeasureTheory.measurePreserving_seqBlock_infinitePi`: the blocks of `m` terms of an independent
  sequence form an independent sequence, of the `m`-fold products of the laws of their terms.
* `MeasureTheory.measurePreserving_seqBlock`: the law of one block;
  `MeasureTheory.integral_comp_seqBlock`: the integral of a function of one block.
* `ProbabilityTheory.iIndepFun_seqBlock`: the blocks are independent.
* `ProbabilityTheory.lintegral_seqBlockProd`: the expectation of a product over `k` blocks is the
  product of the expectations of its factors; `ProbabilityTheory.lintegral_seqBlockProd_const`:
  under an i.i.d. law, it is the `k`-th power of the expectation of one factor.
* `ProbabilityTheory.strong_law_ae_seqBlock`, `ProbabilityTheory.strong_law_ae_seqBlock_nat_div`:
  the strong law of large numbers along the blocks, averaged over the blocks and over the
  observations.
* `ProbabilityTheory.lintegral_hittingAfter_sum_seqBlock_le`: Wald's bound on the expected number
  of blocks over which the sum of a function bounded above reaches a level.

## Implementation notes

The definitions and their first lemmas are adapted from
`EValuesResearch/Results/NumeraireAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`; the laws of the blocks are proved here through Mathlib's
`Measure.map_infinitePi_infinitePi_of_inj` and `Measure.infinitePi_map_curry`.
-/

public section

open Filter
open TauCeti.Probability (shift shift_iterate_apply)
open scoped ENNReal Topology

namespace MeasureTheory

variable {𝓧 : Type*}

/-! ### Blocks of a sequence -/

/-- The `j`-th block of `m` terms of a sequence: the terms `j * m, …, j * m + m - 1`. -/
def seqBlock (m j : ℕ) (ω : ℕ → 𝓧) : Fin m → 𝓧 := fun i ↦ ω (j * m + i)

/-- The terms of the `j`-th block of `m` terms. -/
@[simp]
lemma seqBlock_apply (m j : ℕ) (ω : ℕ → 𝓧) (i : Fin m) : seqBlock m j ω i = ω (j * m + i) :=
  (rfl)

/-- The `j`-th block of `m` terms is the initial segment of the sequence shifted by `j * m`
terms. -/
lemma seqBlock_eq_initSeg_shift_iterate (m j : ℕ) (ω : ℕ → 𝓧) :
    seqBlock m j ω = initSeg m ((shift 𝓧)^[j * m] ω) :=
  funext fun i ↦ by rw [seqBlock_apply, initSeg_apply, shift_iterate_apply, Nat.add_comm]

/-- The first block of `m` terms is the initial segment of length `m`. -/
@[simp]
lemma seqBlock_zero (m : ℕ) (ω : ℕ → 𝓧) : seqBlock m 0 ω = initSeg m ω :=
  funext fun i ↦ by rw [seqBlock_apply, initSeg_apply, Nat.zero_mul, Nat.zero_add]

/-- The block `j + 1` is the block `j` of the sequence shifted by one block. -/
lemma seqBlock_succ (m j : ℕ) (ω : ℕ → 𝓧) :
    seqBlock m (j + 1) ω = seqBlock m j ((shift 𝓧)^[m] ω) :=
  funext fun i ↦ by
    rw [seqBlock_apply, seqBlock_apply, shift_iterate_apply, Nat.succ_mul]
    congr 1
    omega

/-- The `j`-th block of `m` terms is a function of the terms `j * m, …, j * m + m - 1`. -/
lemma dependsOn_seqBlock (m j : ℕ) :
    DependsOn (seqBlock (𝓧 := 𝓧) m j) (Set.Ico (j * m) (j * m + m)) :=
  fun _ _ h ↦ funext fun i ↦ h _ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩

/-- A block is measurable. -/
@[fun_prop]
lemma measurable_seqBlock [MeasurableSpace 𝓧] (m j : ℕ) :
    Measurable (seqBlock (𝓧 := 𝓧) m j) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-! ### Products over blocks -/

section Prod

variable {M : Type*} [CommMonoid M] {m : ℕ} {V : (Fin m → 𝓧) → M}

variable (m V) in
/-- The product of `V` over the first `k` blocks of `m` terms of a sequence. -/
def seqBlockProd (k : ℕ) (ω : ℕ → 𝓧) : M := ∏ j ∈ Finset.range k, V (seqBlock m j ω)

variable (m V) in
/-- The definition of the product over blocks. -/
lemma seqBlockProd_def (k : ℕ) (ω : ℕ → 𝓧) :
    seqBlockProd m V k ω = ∏ j ∈ Finset.range k, V (seqBlock m j ω) :=
  (rfl)

variable (m V) in
/-- The product over no block is `1`. -/
@[simp]
lemma seqBlockProd_zero (ω : ℕ → 𝓧) : seqBlockProd m V 0 ω = 1 :=
  Finset.prod_range_zero _

variable (m V) in
/-- The product over `k + 1` blocks is the product over the first `k` blocks times the factor of
the block `k`. -/
lemma seqBlockProd_succ (k : ℕ) (ω : ℕ → 𝓧) :
    seqBlockProd m V (k + 1) ω = seqBlockProd m V k ω * V (seqBlock m k ω) :=
  Finset.prod_range_succ _ _

variable (V) in
/-- The product over `k` blocks of `m` terms is a function of the first `k * m` terms. -/
lemma dependsOn_seqBlockProd (k : ℕ) :
    DependsOn (seqBlockProd (𝓧 := 𝓧) m V k) (Set.Iio (k * m)) := by
  intro ω ω' h
  refine Finset.prod_congr rfl fun j hj ↦ congrArg V (dependsOn_seqBlock m j fun i hi ↦ h i ?_)
  have hjk : (j + 1) * m ≤ k * m := Nat.mul_le_mul_right m (Finset.mem_range.1 hj)
  rw [Nat.succ_mul] at hjk
  exact Set.mem_Iio.2 (hi.2.trans_le hjk)

/-- The product of a measurable function over blocks is measurable. -/
@[fun_prop]
lemma measurable_seqBlockProd [MeasurableSpace 𝓧] [MeasurableSpace M] [MeasurableMul₂ M]
    (hV : Measurable V) (k : ℕ) : Measurable (seqBlockProd m V k) :=
  Finset.measurable_prod _ fun j _ ↦ hV.comp (measurable_seqBlock m j)

end Prod

/-! ### The blocks of an independent sequence -/

variable {m𝓧 : MeasurableSpace 𝓧}

/-- **The blocks of an independent sequence are independent.** Under the product
`Measure.infinitePi μ` of probability measures, the sequence of the blocks of `m` terms has the
product law of the `m`-fold products `Measure.pi fun i : Fin m ↦ μ (j * m + i)`. For an i.i.d.
sequence of law `P`, the blocks are i.i.d. of law `Measure.pi fun _ : Fin m ↦ P`. -/
theorem measurePreserving_seqBlock_infinitePi (μ : ℕ → Measure 𝓧)
    [∀ i, IsProbabilityMeasure (μ i)] (m : ℕ) :
    MeasurePreserving (fun ω j ↦ seqBlock m j ω) (Measure.infinitePi μ)
      (Measure.infinitePi fun j ↦ Measure.pi fun i : Fin m ↦ μ (j * m + i)) := by
  refine ⟨Measurable.of_eval (measurable_seqBlock m), ?_⟩
  -- the blocks curry the reindexing `(j, i) ↦ j * m + i`, which is injective
  have hinj : Function.Injective fun p : ℕ × Fin m ↦ p.1 * m + (p.2 : ℕ) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact fun p ↦ p.2.elim0
    · have : NeZero m := ⟨hm.ne'⟩
      exact (Nat.divModEquiv m).symm.injective
  have h : (fun (ω : ℕ → 𝓧) j ↦ seqBlock m j ω) =
      MeasurableEquiv.curry ℕ (Fin m) 𝓧 ∘ fun ω p ↦ ω (p.1 * m + p.2) := by
    rw [MeasurableEquiv.coe_curry]
    funext ω j i
    rw [Function.comp_apply, Function.curry_apply, seqBlock_apply]
  have hm : Measurable fun (ω : ℕ → 𝓧) (p : ℕ × Fin m) ↦ ω (p.1 * m + p.2) :=
    Measurable.of_eval fun _ ↦ measurable_pi_apply _
  rw [h, ← Measure.map_map (MeasurableEquiv.measurable _) hm,
    Measure.map_infinitePi_infinitePi_of_inj hinj,
    Measure.infinitePi_map_curry (fun (j : ℕ) (i : Fin m) ↦ μ (j * m + i))]
  simp only [Measure.infinitePi_eq_pi]

/-- Under the product `Measure.infinitePi μ` of probability measures, the `j`-th block of `m`
terms has the law `Measure.pi fun i : Fin m ↦ μ (j * m + i)`. -/
theorem measurePreserving_seqBlock (μ : ℕ → Measure 𝓧) [∀ i, IsProbabilityMeasure (μ i)]
    (m j : ℕ) :
    MeasurePreserving (seqBlock m j) (Measure.infinitePi μ)
      (Measure.pi fun i : Fin m ↦ μ (j * m + i)) :=
  (measurePreserving_eval_infinitePi _ j).comp (measurePreserving_seqBlock_infinitePi μ m)

/-- Under the product `Measure.infinitePi μ` of probability measures, the integral of a function
of the `j`-th block of `m` terms is its integral under the law
`Measure.pi fun i : Fin m ↦ μ (j * m + i)` of the block. -/
theorem integral_comp_seqBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ℕ → Measure 𝓧) [∀ i, IsProbabilityMeasure (μ i)] (m j : ℕ) {f : (Fin m → 𝓧) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun i : Fin m ↦ μ (j * m + i))) :
    ∫ ω, f (seqBlock m j ω) ∂Measure.infinitePi μ =
      ∫ x, f x ∂Measure.pi fun i : Fin m ↦ μ (j * m + i) := by
  rw [← (measurePreserving_seqBlock μ m j).map_eq] at hf ⊢
  exact (integral_map (measurable_seqBlock m j).aemeasurable hf).symm

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- Under a product `Measure.infinitePi μ` of probability measures, the blocks of `m` terms are
independent. -/
theorem iIndepFun_seqBlock (μ : ℕ → Measure 𝓧) [∀ i, IsProbabilityMeasure (μ i)] (m : ℕ) :
    iIndepFun (fun j ↦ seqBlock m j) (Measure.infinitePi μ) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (measurable_seqBlock m),
    (measurePreserving_seqBlock_infinitePi μ m).map_eq]
  simp_rw [(measurePreserving_seqBlock μ m _).map_eq]

/-- Under a product `Measure.infinitePi μ` of probability measures, the expectation of the
product of `V` over `k` blocks of `m` terms is the product of the expectations of `V` under the
laws `Measure.pi fun i ↦ μ (j * m + i)` of the blocks. -/
theorem lintegral_seqBlockProd (μ : ℕ → Measure 𝓧) [∀ i, IsProbabilityMeasure (μ i)] {m : ℕ}
    {V : (Fin m → 𝓧) → ℝ≥0∞} (hV : Measurable V) (k : ℕ) :
    ∫⁻ ω, seqBlockProd m V k ω ∂Measure.infinitePi μ =
      ∏ j ∈ Finset.range k, ∫⁻ x, V x ∂Measure.pi fun i : Fin m ↦ μ (j * m + i) := by
  simp_rw [seqBlockProd_def]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ (fun j ω ↦ V (seqBlock m j ω))
    ((iIndepFun_seqBlock μ m).comp _ fun _ ↦ hV) fun j ↦ hV.comp (measurable_seqBlock m j)]
  simp_rw [(measurePreserving_seqBlock μ m _).lintegral_comp hV]

/-- Under the i.i.d. law of `P`, the expectation of the product of `V` over `k` blocks of `m`
terms is the `k`-th power of the expectation of `V` under the `m`-fold product of `P`. -/
theorem lintegral_seqBlockProd_const (P : Measure 𝓧) [IsProbabilityMeasure P] {m : ℕ}
    {V : (Fin m → 𝓧) → ℝ≥0∞} (hV : Measurable V) (k : ℕ) :
    ∫⁻ ω, seqBlockProd m V k ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (∫⁻ x, V x ∂Measure.pi fun _ : Fin m ↦ P) ^ k := by
  rw [lintegral_seqBlockProd _ hV, Finset.prod_const, Finset.card_range]

/-- **Wald's bound along blocks.** Let `v` be a measurable function of `m` terms, bounded above by
`C`, whose means under the laws `Measure.pi fun i ↦ μ (j * m + i)` of the blocks are at least
`a > 0`. Under the product `Measure.infinitePi μ` of probability measures, the first time at which
the sum of the values of `v` over the blocks of `m` terms reaches `b` has expectation at most
`(b + C) / a`: the values of `v` on the blocks are independent
(`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`). -/
theorem lintegral_hittingAfter_sum_seqBlock_le (μ : ℕ → Measure 𝓧)
    [∀ i, IsProbabilityMeasure (μ i)] {m : ℕ} {v : (Fin m → 𝓧) → ℝ} (hv : Measurable v)
    {C : ℝ} (hvC : ∀ x, v x ≤ C) {a : ℝ} (ha : 0 < a)
    (hva : ∀ j, a ≤ ∫ x, v x ∂Measure.pi fun i : Fin m ↦ μ (j * m + i)) (b : ℝ) :
    ∫⁻ ω, ENat.toENNReal (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, v (seqBlock m j ω))
        (Set.Ici b) 0 ω) ∂Measure.infinitePi μ ≤
      ENNReal.ofReal ((b + C) / a) :=
  ((iIndepFun_seqBlock μ m).comp (fun _ ↦ v) fun _ ↦ hv).lintegral_hittingAfter_sum_le
    (fun j ↦ hv.comp (measurable_seqBlock m j)) ha
    (fun j ↦ (hva j).trans_eq (integral_comp_seqBlock μ m j hv.aestronglyMeasurable).symm)
    (fun _ ↦ ae_of_all _ fun _ ↦ hvC _) b

section StrongLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The strong law of large numbers along blocks.** Under the i.i.d. law of `Q`, the averages
of an integrable function over the first `k` blocks of `m` terms tend almost surely to its
expectation under the `m`-fold product of `Q`. -/
theorem strong_law_ae_seqBlock (Q : Measure 𝓧) [IsProbabilityMeasure Q] {m : ℕ}
    {g : (Fin m → 𝓧) → E} (hg : Integrable g (Measure.pi fun _ : Fin m ↦ Q)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹ • ∑ j ∈ Finset.range k, g (seqBlock m j ω)) atTop
        (𝓝 (∫ x, g x ∂Measure.pi fun _ : Fin m ↦ Q)) :=
  (measurePreserving_seqBlock_infinitePi (fun _ ↦ Q) m).quasiMeasurePreserving.ae
    (TauCeti.Probability.strong_law_ae_infinitePi _ hg)

/-- **The strong law of large numbers along blocks, per observation.** Under the i.i.d. law of
`Q`, the sum of an integrable function over the complete blocks of `m` terms among the first `n`,
divided by `n`, tends almost surely to its expectation under the `m`-fold product of `Q` divided
by `m`. For `m = 0` both sides are `0`. -/
theorem strong_law_ae_seqBlock_nat_div (Q : Measure 𝓧) [IsProbabilityMeasure Q] {m : ℕ}
    {g : (Fin m → 𝓧) → E} (hg : Integrable g (Measure.pi fun _ : Fin m ↦ Q)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ j ∈ Finset.range (n / m), g (seqBlock m j ω)) atTop
        (𝓝 ((m : ℝ)⁻¹ • ∫ x, g x ∂Measure.pi fun _ : Fin m ↦ Q)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  filter_upwards [strong_law_ae_seqBlock Q hg] with ω hω
  refine ((LMLExplore.tendsto_nat_div_div_atTop (m := m)).smul
    (hω.comp (Nat.tendsto_div_const_atTop hm))).congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hnm : ((n / m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos hn (Nat.pos_of_ne_zero hm)).ne'
  rw [Function.comp_apply, smul_smul]
  congr 1
  field_simp

end StrongLaw

end ProbabilityTheory
