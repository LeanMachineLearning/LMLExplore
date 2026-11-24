/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Merging.Independent
public import LMLExplore.Probability.Martingale.CondEVariable
public import LMLExplore.Probability.Process.Filtration
import LMLExplore.Order.Filter.Basic
import LMLExplore.Probability.Distributions.Bernoulli

/-!
# Merging sequential e-values, martingale merging functions and reading strategies

E-values `e 0, …, e (K - 1)` are sequential when each `e k` is a conditional e-variable given the
previous ones. Their joint laws are the sequential laws `ProbabilityTheory.sequentialLaws K` on
`Fin K → ℝ≥0∞`, under which each coordinate `e k` is a conditional e-variable given the strict past
`Filtration.piLT k` of the coordinates. A merging function for sequential e-values (an se-merging
function [VW24, Section 2]) is a measurable `F` with `∫⁻ e, F e ∂μ ≤ 1` for every sequential
probability law `μ`; equivalently, an e-variable of the merging null of the sequential laws, and a
function turning sequential e-variables, for any σ-algebras, into an e-variable.

The martingale merging function of a gambling system `b` [VW24, Section 4] is the final wealth
`∏ k, (1 - b k e + b k e * e k)` of a gambler with initial capital `1` who bets, before reading
`e k`, the fraction `b k e ∈ [0, 1]` of the current capital on `e k`; the bet `b k` only sees the
e-values read before, it is `piLT k`-measurable. Martingale merging functions are se-merging
[VW24, Lemma 2]. Under a law whose coordinates have conditional expectation exactly `1` given the
past, their expectation is `1`.

Independent e-values may be read in any order, chosen adaptively. A reading strategy `π` gives the
index `π k x` of the e-value read at step `k` from the values `x` of the `k` e-values read before,
never reading an e-value twice; `readValues π e` lists the values of `e` in the order of reading.
Read by a reading strategy, independent e-values are sequential e-values [VW24, Lemma 4]: the law
of `readValues π` under a product of laws with expectation at most `1` is a sequential law. So an
se-merging function of the values read is a merging function for independent e-values, and the
generalized martingale merging functions of [VW24, Section 6], the mixtures of martingale merging
functions of the values read by reading strategies, are merging functions for independent
e-values [VW24, Theorem 3]. When the initial capital is `1`, a mixture against a probability
measure, they are moreover precise: their integral against a product of laws with expectation `1`
is `1`, so they are admissible merging functions for independent e-values.

Martingale merging functions are also admissible se-merging functions: the quasi-sure filter of the
merging null of the sequential laws is, as for the product laws, the principal filter of the points
with finite coordinates, so an se-merging function that is admissible among the merging functions
for independent e-values is admissible among the se-merging functions. This is the direction of
[VW24, Corollary 1] in which martingale merging functions are admissible; its converse, that every
se-merging function is dominated by a martingale merging function [VW24, Theorem 1], is not proved
here.

## Main definitions

* `ProbabilityTheory.sequentialLaws K`: the laws on `Fin K → ℝ≥0∞` under which each coordinate is a
  conditional e-variable given the previous ones.
* `ProbabilityTheory.IsSEMerging F`: `F` is a merging function for sequential e-values.
* `ProbabilityTheory.IsAdmissibleSEMerging F`: `F` is an admissible e-variable for the merging null
  of the sequential laws.
* `ProbabilityTheory.martingaleMerging b`: the martingale merging function of the bets `b`.
* `ProbabilityTheory.IsReadingStrategy π`: `π` is a reading strategy.
* `ProbabilityTheory.readIndex π e k`, `ProbabilityTheory.readValues π e k`: the index and the value
  of the e-value read at step `k`.

## Main statements

* `ProbabilityTheory.map_mem_sequentialLaws`: the joint law of sequential e-variables is a
  sequential law.
* `ProbabilityTheory.isSEMerging_iff_isEVar_mergingNull`,
  `ProbabilityTheory.isSEMerging_iff_forall_isEVar`: se-merging functions are the e-variables of
  the merging null of the sequential laws, and the functions merging sequential e-variables.
* `ProbabilityTheory.isSEMerging_martingaleMerging`: martingale merging functions are se-merging
  [VW24, Lemma 2].
* `ProbabilityTheory.map_readValues_pi_mem_sequentialLaws`: independent e-values read by a reading
  strategy are sequential e-values [VW24, Lemma 4].
* `ProbabilityTheory.IsSEMerging.isIEMerging_comp_readValues`,
  `ProbabilityTheory.IsSEMerging.isIEMerging`:
  an se-merging function of the values read by a reading strategy, in particular an se-merging
  function, is a merging function for independent e-values.
* `ProbabilityTheory.isIEMerging_lintegral_martingaleMerging_readValues`,
  `ProbabilityTheory.isPreciseIEMerging_lintegral_martingaleMerging_readValues`: the generalized
  martingale merging functions are merging functions for independent e-values [VW24, Theorem 3],
  precise when the initial capital is `1`.
* `ProbabilityTheory.isAdmissibleSEMerging_martingaleMerging`,
  `ProbabilityTheory.isAdmissibleIEMerging_martingaleMerging`: martingale merging functions are
  admissible se-merging functions (one direction of [VW24, Corollary 1]) and admissible merging
  functions for independent e-values.
* `ProbabilityTheory.IsAdmissibleSEMerging.eq_of_le`: an se-merging function dominating an
  admissible one at finite arguments equals it there.

## Implementation notes

The e-values take values in `ℝ≥0∞`, where [VW24] takes them in `[0, ∞)`; as for the other merging
functions, the values at infinite arguments are irrelevant (`ProbabilityTheory.IsSEMerging.of_le`).
A gambling system of [VW24] is a function of the e-values read before; here the bet `b k` is a
function on `Fin K → ℝ≥0∞` that is measurable for `Filtration.piLT k`, which is the same by the
Doob–Dynkin lemma. The generalized martingale merging functions are stated for any family of
gambling systems and reading strategies parametrized by a measurable space with a measure of mass
at most `1` (a probability measure for precision), such that the mixture is jointly
measurable.

## References

* [VW24] V. Vovk and R. Wang, *Merging sequential e-values via martingales*, Electron. J.
  Statist. 18 (2024), arXiv:2007.06382v3: Section 2 (sequential e-values, se-merging functions),
  Section 4 (gambling systems, martingale merging functions, Lemma 2, Corollary 1) and Section 6
  (reading strategies, generalized martingale merging functions, Lemma 4,
  Theorem 3).
-/

public section

open MeasureTheory MeasureTheory.Filtration Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {K : ℕ}

/-! ### The sequential laws and se-merging functions -/

section SequentialLaws

variable {μ : Measure (Fin K → ℝ≥0∞)} {F G : (Fin K → ℝ≥0∞) → ℝ≥0∞}

/-- The **sequential laws** on `Fin K → ℝ≥0∞`: the measures under which each coordinate `e k` is a
conditional e-variable given the previous coordinates, the strict past `piLT k`. Their merging
null is the null of the joint laws of sequential e-values
(`ProbabilityTheory.map_mem_sequentialLaws`). -/
def sequentialLaws (K : ℕ) : Set (Measure (Fin K → ℝ≥0∞)) :=
  {μ | ∀ k, IsCondEVar (fun e ↦ e k) (piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k) {μ}}

/-- Membership in the sequential laws, unfolded. -/
theorem mem_sequentialLaws :
    μ ∈ sequentialLaws K ↔ ∀ k, IsCondEVar (fun e ↦ e k) (piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k) {μ} :=
  Iff.rfl

/-- The members of the merging null of the sequential laws are the sequential probability laws:
the coordinates of a sequential law have expectation at most `1`. -/
theorem mem_mergingNull_sequentialLaws :
    μ ∈ mergingNull (sequentialLaws K) ↔ IsProbabilityMeasure μ ∧ μ ∈ sequentialLaws K := by
  refine ⟨fun h ↦ ⟨(mem_mergingNull.1 h).2.1, (mem_mergingNull.1 h).1⟩,
    fun ⟨h1, h⟩ ↦ mem_mergingNull.2 ⟨h, h1, fun k ↦ ?_⟩⟩
  simpa using (h k).setLIntegral_le μ rfl univ MeasurableSet.univ

/-- **The joint law of sequential e-variables is a sequential law**: for σ-algebras `m k` such that
`E k` is a conditional e-variable given `m k` and every earlier `E j` is `m k`-measurable, the law
of `E` is a sequential law. -/
theorem map_mem_sequentialLaws {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {m : Fin K → MeasurableSpace Ω} {E : Fin K → Ω → ℝ≥0∞}
    (hE : ∀ k, IsCondEVar (E k) (m k) {P}) (hEm : ∀ j k, j < k → Measurable[m k] (E j)) :
    P.map (fun ω k ↦ E k ω) ∈ sequentialLaws K := by
  have hmeas : Measurable fun ω k ↦ E k ω := Measurable.of_eval fun k ↦ (hE k).measurable
  refine fun k ↦ ⟨measurable_pi_apply k, fun μ hμ s hs ↦ ?_⟩
  rw [Set.mem_singleton_iff] at hμ
  subst hμ
  have hs' : MeasurableSet s := (piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs
  -- the preimage of a set of the strict past is `m k`-measurable
  have hpre : MeasurableSet[m k] ((fun ω k ↦ E k ω) ⁻¹' s) := by
    refine Measurable.of_comap_le ?_ hs
    simp only [piLT_apply, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup₂_le fun j hj ↦ (hEm j k hj).comap_le
  rw [setLIntegral_map hs' (measurable_pi_apply k) hmeas, Measure.map_apply hmeas hs']
  exact (hE k).setLIntegral_le P rfl _ hpre

/-- A **merging function for sequential e-values** (an se-merging function) indexed by `Fin K`
[VW24, Section 2]: a measurable `F : (Fin K → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every
sequential probability law `μ`. It is not required to be monotone. -/
structure IsSEMerging (F : (Fin K → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : Measure (Fin K → ℝ≥0∞)) [IsProbabilityMeasure μ],
    μ ∈ sequentialLaws K → ∫⁻ e, F e ∂μ ≤ 1

/-- **Se-merging functions are the e-variables of the merging null of the sequential laws.** -/
theorem isSEMerging_iff_isEVar_mergingNull :
    IsSEMerging F ↔ IsEVar F (mergingNull (sequentialLaws K)) :=
  ⟨fun hF ↦ ⟨hF.measurable, fun μ hμ ↦ have := (mem_mergingNull_sequentialLaws.1 hμ).1
      hF.lintegral_le_one μ (mem_mergingNull_sequentialLaws.1 hμ).2⟩,
    fun hF ↦ ⟨hF.measurable, fun μ _ hμ ↦
      hF.lintegral_le_one (mem_mergingNull_sequentialLaws.2 ⟨‹_›, hμ⟩)⟩⟩

/-- An e-merging function is se-merging. -/
theorem IsEMerging.isSEMerging (hF : IsEMerging F) : IsSEMerging F :=
  isSEMerging_iff_isEVar_mergingNull.2 (hF.isEVar_mergingNull _)

/-- A measurable function dominated on finite arguments by an se-merging function is se-merging:
the values at infinite arguments are irrelevant. -/
theorem IsSEMerging.of_le (hG : IsSEMerging G) (hF : Measurable F)
    (hle : ∀ e : Fin K → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) : IsSEMerging F :=
  isSEMerging_iff_isEVar_mergingNull.2
    ((isSEMerging_iff_isEVar_mergingNull.1 hG).mono_mergingNull hF hle)

/-- An se-merging function of sequential e-variables is an e-variable: for σ-algebras `m k` such
that `E k` is a conditional e-variable given `m k` and every earlier `E j` is `m k`-measurable,
`F (E 0, …, E (K - 1))` is an e-variable for every null of probability measures. -/
theorem IsSEMerging.isEVar_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)}
    (hF : IsSEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P) {m : Fin K → MeasurableSpace Ω}
    {E : Fin K → Ω → ℝ≥0∞} (hE : ∀ k, IsCondEVar (E k) (m k) S)
    (hEm : ∀ j k, j < k → Measurable[m k] (E j)) :
    IsEVar (fun ω ↦ F fun k ↦ E k ω) S := by
  have hmeas : Measurable fun ω k ↦ E k ω := Measurable.of_eval fun k ↦ (hE k).measurable
  refine ⟨hF.measurable.comp hmeas, fun P hP ↦ ?_⟩
  have := hS P hP
  rw [← lintegral_map hF.measurable hmeas]
  exact hF.lintegral_le_one _
    (map_mem_sequentialLaws (fun k ↦ (hE k).anti_set (singleton_subset_iff.2 hP)) hEm)

/-- A function of `K` e-values is se-merging exactly when it turns sequential e-variables, for
any σ-algebras, into an e-variable, for every null of probability measures on every measurable
space. -/
theorem isSEMerging_iff_forall_isEVar :
    IsSEMerging F ↔ ∀ (Ω : Type) [MeasurableSpace Ω] (S : Set (Measure Ω)),
      (∀ P ∈ S, IsProbabilityMeasure P) → ∀ m : Fin K → MeasurableSpace Ω,
        ∀ E : Fin K → Ω → ℝ≥0∞, (∀ k, IsCondEVar (E k) (m k) S) →
          (∀ j k, j < k → Measurable[m k] (E j)) → IsEVar (fun ω ↦ F fun k ↦ E k ω) S := by
  refine ⟨fun hF Ω _ S hS m E hE hEm ↦ hF.isEVar_comp hS hE hEm, fun h ↦ ?_⟩
  -- Apply the hypothesis to the coordinates and the strict past, under the merging null.
  refine isSEMerging_iff_isEVar_mergingNull.2 <| h (Fin K → ℝ≥0∞) (mergingNull (sequentialLaws K))
    (fun _ ↦ isProbabilityMeasure_of_mem_mergingNull) (piLT (X := fun _ : Fin K ↦ ℝ≥0∞))
    (fun k e ↦ e k) (fun k ↦ ⟨measurable_pi_apply k,
      fun μ hμ ↦ ((mem_mergingNull_sequentialLaws.1 hμ).2 k).setLIntegral_le μ rfl⟩)
    fun j k hjk ↦ measurable_piLT_apply hjk

end SequentialLaws

/-! ### Martingale merging functions -/

section MartingaleMerging

variable {b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞} {μ : Measure (Fin K → ℝ≥0∞)}

/-- The **martingale merging function** of the bets `b` [VW24, Section 4]: the final wealth
`∏ k, (1 - b k e + b k e * e k)` of a gambler with initial capital `1` who bets the fraction
`b k e` of the current capital on `e k`. It is se-merging when each bet `b k` is at most `1` and
measurable for the strict past `piLT k` (`ProbabilityTheory.isSEMerging_martingaleMerging`). -/
noncomputable def martingaleMerging (b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∏ k, (1 - b k e + b k e * e k)

/-- The martingale merging function, unfolded. -/
theorem martingaleMerging_apply (b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞) (e : Fin K → ℝ≥0∞) :
    martingaleMerging b e = ∏ k, (1 - b k e + b k e * e k) :=
  (rfl)

/-- A martingale merging function with measurable bets is measurable. -/
theorem measurable_martingaleMerging (hb : ∀ k, Measurable (b k)) :
    Measurable (martingaleMerging b) :=
  Finset.measurable_fun_prod _ fun k _ ↦
    ((hb k).const_sub 1).add ((hb k).mul (measurable_pi_apply k))

/-- The factor of round `k` of a martingale merging function is the portfolio of `1` and of `e k`
with the weights `1 - b k e` and `b k e`. -/
private lemma factor_eq_sum_mul (k : Fin K) :
    (fun e ↦ 1 - b k e + b k e * e k) = fun e ↦
      ∑ i, ![1 - b k e, b k e] i * (![1, fun e ↦ e k] : Fin 2 → (Fin K → ℝ≥0∞) → ℝ≥0∞) i e := by
  funext e
  simp [Fin.sum_univ_two]

variable (hb : ∀ k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b k))
  (hb1 : ∀ k e, b k e ≤ 1)
include hb

/-- The weights `1 - b k e` and `b k e` of the portfolio of round `k` are measurable for the strict
past `piLT k`. -/
private lemma measurable_piLT_weight (k : Fin K) (i : Fin 2) :
    Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] fun e ↦ ![1 - b k e, b k e] i := by
  fin_cases i <;> simp [(hb k).const_sub, hb k]

/-- The factor of round `j` of a martingale merging function is measurable for the strict past at
every later round `k`. -/
private lemma measurable_piLT_factor {j k : Fin K} (hjk : j < k) :
    Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] fun e ↦ 1 - b j e + b j e * e j := by
  have hbj := (hb j).mono ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).mono hjk.le) le_rfl
  exact (hbj.const_sub 1).add (hbj.mul (measurable_piLT_apply hjk))

include hb1

/-- **Martingale merging functions are bounded by the mass under sequential laws**: the wealth of
the gambler is a supermartingale under a sequential law. -/
theorem lintegral_martingaleMerging_le (hμ : μ ∈ sequentialLaws K) :
    ∫⁻ e, martingaleMerging b e ∂μ ≤ μ univ := by
  refine lintegral_prod_le_of_isCondEVar (piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le (fun k ↦ ?_)
    (fun j k hjk ↦ measurable_piLT_factor hb hjk) (Set.mem_singleton μ)
  -- the factor of round `k` is a portfolio of `1` and of `e k`
  rw [factor_eq_sum_mul]
  exact isCondEVar_sum_mul ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k)
    (fun i ↦ by fin_cases i <;> simp [hμ k]) (measurable_piLT_weight hb k)
    fun e ↦ by simp [tsub_add_cancel_of_le (hb1 k e)]

/-- **Martingale merging functions are exact under exact sequential laws**: under a law under which
each coordinate has conditional expectation `1` given the previous ones, the expectation of a
martingale merging function is the mass. -/
theorem lintegral_martingaleMerging_eq
    (hμ : ∀ k, IsExactCondEVar (fun e ↦ e k) (piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k) {μ}) :
    ∫⁻ e, martingaleMerging b e ∂μ = μ univ := by
  refine lintegral_prod_eq_of_isExactCondEVar (piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le (fun k ↦ ?_)
    (fun j k hjk ↦ measurable_piLT_factor hb hjk) (Set.mem_singleton μ)
  rw [factor_eq_sum_mul]
  exact isExactCondEVar_sum_mul ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k)
    (fun i ↦ by fin_cases i <;> simp [hμ k]) (measurable_piLT_weight hb k)
    fun e ↦ by simp [tsub_add_cancel_of_le (hb1 k e)]

/-- **Martingale merging functions are se-merging** [VW24, Lemma 2]: for bets `b k` at most `1`
that are measurable for the strict past `piLT k`. -/
theorem isSEMerging_martingaleMerging : IsSEMerging (martingaleMerging b) :=
  ⟨measurable_martingaleMerging fun k ↦
      (hb k).mono ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k) le_rfl,
    fun μ _ hμ ↦ by simpa using lintegral_martingaleMerging_le hb hb1 hμ⟩

end MartingaleMerging

/-! ### Reading strategies -/

section Reading

/-- A **reading strategy** for `K` e-values [VW24, Section 6]: `π k x` is the index of the e-value
read at step `k`, after the values `x` of the `k` e-values read before. It is measurable, and it
never reads an e-value twice: along the same values, the index read at step `k` differs from the
indices read at the steps `i < k`. -/
structure IsReadingStrategy (π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K) : Prop where
  measurable : ∀ k, Measurable (π k)
  ne : ∀ (i k : Fin K) (hik : i < k) (x : Fin k → ℝ≥0∞),
    π i (fun j ↦ x (Fin.castLE hik.le j)) ≠ π k x

variable {π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K} {e : Fin K → ℝ≥0∞}

/-- The **index read at step `k`** by the reading strategy `π` from the e-values `e`: the index
`π k x`, for the values `x` read at the steps before `k`. -/
def readIndex (π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K) (e : Fin K → ℝ≥0∞) (k : Fin K) : Fin K :=
  π k fun j ↦ e (readIndex π e (Fin.castLT j (j.isLt.trans k.isLt)))
termination_by k.val
decreasing_by exact j.isLt

/-- The **values read** by the reading strategy `π` from the e-values `e`, in the order of reading:
the value read at step `k` is `e (readIndex π e k)`. -/
def readValues (π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K) (e : Fin K → ℝ≥0∞) (k : Fin K) :
    ℝ≥0∞ :=
  e (readIndex π e k)

/-- The value read at step `k` is the e-value of the index read at step `k`. -/
theorem readValues_apply (π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K) (e : Fin K → ℝ≥0∞)
    (k : Fin K) : readValues π e k = e (readIndex π e k) :=
  (rfl)

/-- The index read at step `k` is `π k` of the values read before. -/
theorem readIndex_eq (π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K) (e : Fin K → ℝ≥0∞) (k : Fin K) :
    readIndex π e k = π k fun j ↦ readValues π e (Fin.castLT j (j.isLt.trans k.isLt)) := by
  rw [readIndex]
  rfl

/-- Reading the e-values in their order, `π k x = k`, is a reading strategy. -/
theorem isReadingStrategy_self : IsReadingStrategy fun (k : Fin K) (_ : Fin k → ℝ≥0∞) ↦ k :=
  ⟨fun _ ↦ measurable_const, fun _ _ hik _ ↦ hik.ne⟩

/-- Reading the e-values in their order reads the e-value `k` at step `k`. -/
@[simp]
theorem readIndex_self (e : Fin K → ℝ≥0∞) (k : Fin K) :
    readIndex (fun (k : Fin K) (_ : Fin k → ℝ≥0∞) ↦ k) e k = k :=
  readIndex_eq _ _ _

/-- Reading the e-values in their order gives back the e-values. -/
@[simp]
theorem readValues_self : readValues (fun (k : Fin K) (_ : Fin k → ℝ≥0∞) ↦ k) = id := by
  funext e k
  rw [readValues_apply, readIndex_self, id]

/-- An e-value is never read twice: the indices read at different steps differ. -/
theorem IsReadingStrategy.readIndex_ne (hπ : IsReadingStrategy π) {i k : Fin K} (hik : i < k)
    (e : Fin K → ℝ≥0∞) : readIndex π e i ≠ readIndex π e k := by
  rw [readIndex_eq π e i, readIndex_eq π e k]
  exact hπ.ne i k hik fun j ↦ readValues π e (Fin.castLT j (j.isLt.trans k.isLt))

/-- The index read at step `k` is measurable. -/
theorem IsReadingStrategy.measurable_readIndex (hπ : IsReadingStrategy π) (k : Fin K) :
    Measurable fun e ↦ readIndex π e k := by
  simp_rw [readIndex_eq π _ k, readValues_apply]
  exact (hπ.measurable k).comp (Measurable.of_eval fun j ↦
    measurable_id.eval_index (hπ.measurable_readIndex (Fin.castLT j (j.isLt.trans k.isLt))))
termination_by k.val
decreasing_by exact j.isLt

/-- The values read by a reading strategy are measurable. -/
theorem IsReadingStrategy.measurable_readValues (hπ : IsReadingStrategy π) :
    Measurable (readValues π) :=
  Measurable.of_eval fun k ↦ measurable_id.eval_index (hπ.measurable_readIndex k)

/-- Changing an e-value that is not read before step `k` does not change the index read at
step `k`. -/
theorem readIndex_update {j k : Fin K} (h : ∀ l < k, readIndex π e l ≠ j) (c : ℝ≥0∞) :
    readIndex π (Function.update e j c) k = readIndex π e k := by
  rw [readIndex_eq π (Function.update e j c) k, readIndex_eq π e k]
  congr 1
  funext l
  have hl : Fin.castLT l (l.isLt.trans k.isLt) < k := l.isLt
  rw [readValues_apply, readValues_apply, readIndex_update (fun l' hl' ↦ h l' (hl'.trans hl)) c,
    Function.update_of_ne (h _ hl)]
termination_by k.val
decreasing_by exact l.isLt

/-- Changing an e-value that is not read before step `k` does not change the values read before
step `k`. -/
theorem readValues_update_of_lt {j k l : Fin K} (h : ∀ l < k, readIndex π e l ≠ j) (hl : l < k)
    (c : ℝ≥0∞) : readValues π (Function.update e j c) l = readValues π e l := by
  rw [readValues_apply, readValues_apply, readIndex_update (fun l' hl' ↦ h l' (hl'.trans hl)) c,
    Function.update_of_ne (h l hl)]

variable (hπ : IsReadingStrategy π) (ν : Fin K → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (ν i)]
include hπ

/-- The event that a set of the strict past of the values read before step `k` happens and that
the e-value `j` is read at step `k` is measurable for the coordinates other than `j`: it is
unchanged when the e-value `j`, not read before step `k`, changes. -/
private lemma measurableSet_iSup_compl_readIndex {k j : Fin K} {s : Set (Fin K → ℝ≥0∞)}
    (hs : MeasurableSet[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] s) :
    MeasurableSet[⨆ i ∈ ({j}ᶜ : Set (Fin K)),
      MeasurableSpace.comap (fun e : Fin K → ℝ≥0∞ ↦ e i) inferInstance]
      ((fun e ↦ readIndex π e k) ⁻¹' {j} ∩ readValues π ⁻¹' s) := by
  set t := (fun e ↦ readIndex π e k) ⁻¹' {j} ∩ readValues π ⁻¹' s
  have hs' : MeasurableSet s := (piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs
  have ht : MeasurableSet t :=
    (hπ.measurable_readIndex k (measurableSet_singleton j)).inter (hπ.measurable_readValues hs')
  -- changing `e j` keeps the index read at step `k` and the membership in `s`
  have hinv (e : Fin K → ℝ≥0∞) (c : ℝ≥0∞) (he : readIndex π e k = j) :
      readIndex π (Function.update e j c) k = j ∧
        (readValues π (Function.update e j c) ∈ s ↔ readValues π e ∈ s) := by
    have h : ∀ l < k, readIndex π e l ≠ j := fun l hl ↦ by
      rw [← he]
      exact hπ.readIndex_ne hl e
    exact ⟨(readIndex_update h c).trans he,
      hs.dependsOn_of_piLT fun l hl ↦ readValues_update_of_lt h hl c⟩
  have ht_eq : (fun e ↦ Function.update e j 0) ⁻¹' t = t := by
    ext e
    simp only [t, mem_inter_iff, mem_preimage, mem_singleton_iff]
    refine ⟨fun ⟨hj, hs⟩ ↦ ?_, fun ⟨hj, hs⟩ ↦ ?_⟩
    · obtain ⟨hj', hs''⟩ := hinv _ (e j) hj
      rw [Function.update_idem, Function.update_eq_self] at hj' hs''
      exact ⟨hj', hs''.2 hs⟩
    · obtain ⟨hj', hs''⟩ := hinv e 0 hj
      exact ⟨hj', hs''.2 hs⟩
  -- the map changing `e j` is measurable for the coordinates other than `j`
  have hupd : Measurable[⨆ i ∈ ({j}ᶜ : Set (Fin K)),
      MeasurableSpace.comap (fun e : Fin K → ℝ≥0∞ ↦ e i) inferInstance]
      fun e : Fin K → ℝ≥0∞ ↦ Function.update e j 0 := by
    -- as in `measurable_pi_iff`, whose source σ-algebra is an instance: coordinatewise
    refine measurable_iff_comap_le.2 ?_
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun i ↦ measurable_iff_comap_le.1 ?_
    by_cases hi : i = j
    · subst hi
      simp [Function.comp_def]
    · simp only [Function.comp_def, Function.update_of_ne hi]
      exact measurable_biSup_comap (fun i (e : Fin K → ℝ≥0∞) ↦ e i) hi
  have := hupd ht
  rwa [ht_eq] at this

/-- Under the law of the values read from a product of laws, the set integral of the value read at
step `k` over a set `s` of the strict past is the sum, over the indices `j`, of the probability that
`j` is read at step `k` while the values read lie in `s`, times the mean of `ν j`. -/
private lemma setLIntegral_map_readValues_pi {k : Fin K} {s : Set (Fin K → ℝ≥0∞)}
    (hs : MeasurableSet[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] s) :
    ∫⁻ e in s, e k ∂(Measure.pi ν).map (readValues π) =
      ∑ j, Measure.pi ν ((fun e ↦ readIndex π e k) ⁻¹' {j} ∩ readValues π ⁻¹' s) *
        ∫⁻ x, x ∂ν j := by
  rw [setLIntegral_map ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs) (measurable_pi_apply k)
    hπ.measurable_readValues]
  have hB (j : Fin K) : MeasurableSet ((fun e ↦ readIndex π e k) ⁻¹' {j}) :=
    hπ.measurable_readIndex k (measurableSet_singleton j)
  -- the value read at step `k` is the coordinate `j` on the event that `j` is read at step `k`
  have hsum : (readValues π · k) = fun e ↦
      ∑ j, ((fun e ↦ readIndex π e k) ⁻¹' {j}).indicator (fun e ↦ e j) e := by
    funext e
    rw [Finset.sum_eq_single_of_mem (readIndex π e k) (Finset.mem_univ _) fun j _ hj ↦ by
      simp [Ne.symm hj]]
    simp [readValues_apply]
  rw [hsum, lintegral_finsetSum _ fun j _ ↦ (measurable_pi_apply j).indicator (hB j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [setLIntegral_indicator (hB j)]
  set t := (fun e ↦ readIndex π e k) ⁻¹' {j} ∩ readValues π ⁻¹' s
  have ht : MeasurableSet t := (hB j).inter
    (hπ.measurable_readValues ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs))
  -- the event `t` is independent of the coordinate `j`
  have hindep := indep_iSup_of_disjoint (fun i ↦ (measurable_pi_apply i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_pi (μ := ν) (X := fun _ x ↦ x)
      fun _ ↦ aemeasurable_id)) (disjoint_compl_left (a := ({j} : Set (Fin K))))
  have hj : Measurable[⨆ i ∈ ({j} : Set (Fin K)),
      MeasurableSpace.comap (fun e : Fin K → ℝ≥0∞ ↦ e i) inferInstance] fun e ↦ e j :=
    measurable_biSup_comap (fun i (e : Fin K → ℝ≥0∞) ↦ e i) rfl
  calc ∫⁻ e in t, e j ∂Measure.pi ν = ∫⁻ e, t.indicator (fun _ ↦ 1) e * e j ∂Measure.pi ν := by
        rw [← lintegral_indicator ht]
        refine lintegral_congr fun e ↦ ?_
        by_cases he : e ∈ t <;> simp [he]
    _ = Measure.pi ν t * ∫⁻ x, x ∂ν j := by
        rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
          (iSup₂_le fun i _ ↦ (measurable_pi_apply i).comap_le)
          (iSup₂_le fun i _ ↦ (measurable_pi_apply i).comap_le) hindep
          (measurable_const.indicator (measurableSet_iSup_compl_readIndex hπ hs)) hj,
          lintegral_indicator_const ht, one_mul,
          (measurePreserving_eval ν j).lintegral_comp measurable_id']

/-- The mass of a measurable set `s` under the law of the values read is the sum, over the indices
`j`, of the masses of the events that `j` is read at step `k` while the values read lie in `s`. -/
private lemma map_readValues_apply_eq_sum (k : Fin K) (μ : Measure (Fin K → ℝ≥0∞))
    {s : Set (Fin K → ℝ≥0∞)} (hs : MeasurableSet s) :
    μ.map (readValues π) s = ∑ j, μ ((fun e ↦ readIndex π e k) ⁻¹' {j} ∩ readValues π ⁻¹' s) := by
  rw [Measure.map_apply hπ.measurable_readValues hs]
  have := sum_measure_preimage_singleton (μ := μ.restrict (readValues π ⁻¹' s)) Finset.univ
    (f := fun e ↦ readIndex π e k) fun j _ ↦ hπ.measurable_readIndex k (measurableSet_singleton j)
  simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ ↦
    Measure.restrict_apply (hπ.measurable_readIndex k (measurableSet_singleton j))

/-- **Independent e-values read by a reading strategy are sequential e-values** [VW24, Lemma 4]:
under a product of laws with expectation at most `1`, the law of the values read by a reading
strategy is a sequential law. -/
theorem map_readValues_pi_mem_sequentialLaws (hν : ∀ i, ∫⁻ x, x ∂ν i ≤ 1) :
    (Measure.pi ν).map (readValues π) ∈ sequentialLaws K := by
  refine fun k ↦ ⟨measurable_pi_apply k, fun μ hμ s hs ↦ ?_⟩
  rw [Set.mem_singleton_iff.1 hμ, setLIntegral_map_readValues_pi hπ ν hs,
    map_readValues_apply_eq_sum hπ k _ ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs)]
  exact Finset.sum_le_sum fun j _ ↦ mul_le_of_le_one_right' (hν j)

/-- **Independent e-values with expectation `1` read by a reading strategy are exact sequential
e-values**: under a product of laws with expectation `1`, each value read is an exact conditional
e-variable given the values read before. -/
theorem isExactCondEVar_map_readValues_pi (hν : ∀ i, ∫⁻ x, x ∂ν i = 1) (k : Fin K) :
    IsExactCondEVar (fun e ↦ e k) (piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k)
      {(Measure.pi ν).map (readValues π)} := by
  refine ⟨measurable_pi_apply k, fun μ hμ s hs ↦ ?_⟩
  rw [Set.mem_singleton_iff.1 hμ, setLIntegral_map_readValues_pi hπ ν hs,
    map_readValues_apply_eq_sum hπ k _ ((piLT (X := fun _ : Fin K ↦ ℝ≥0∞)).le k s hs)]
  simp [hν]

omit [∀ i, IsProbabilityMeasure (ν i)] in
/-- **An se-merging function of the values read by a reading strategy is a merging function for
independent e-values.** -/
theorem IsSEMerging.isIEMerging_comp_readValues {F : (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hF : IsSEMerging F) : IsIEMerging fun e ↦ F (readValues π e) := by
  refine ⟨hF.measurable.comp hπ.measurable_readValues, fun ν _ hν ↦ ?_⟩
  rw [← lintegral_map hF.measurable hπ.measurable_readValues]
  exact hF.lintegral_le_one _ (map_readValues_pi_mem_sequentialLaws hπ ν hν)

end Reading

/-- **Independent e-values are sequential e-values**: a product of laws with expectation at most
`1` is a sequential law. -/
theorem pi_mem_sequentialLaws (ν : Fin K → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ∫⁻ x, x ∂ν i ≤ 1) : Measure.pi ν ∈ sequentialLaws K := by
  simpa using map_readValues_pi_mem_sequentialLaws isReadingStrategy_self ν hν

/-- **An se-merging function is a merging function for independent e-values**: independent
e-values are sequential e-values. -/
theorem IsSEMerging.isIEMerging {F : (Fin K → ℝ≥0∞) → ℝ≥0∞} (hF : IsSEMerging F) :
    IsIEMerging F := by
  simpa using hF.isIEMerging_comp_readValues isReadingStrategy_self

/-! ### Generalized martingale merging functions -/

section Generalized

variable {b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞} {π : (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K}

/-- **A martingale merging function of the values read by a reading strategy is a precise merging
function for independent e-values**: its integral against a product of laws with expectation `1`
is `1`. -/
theorem isPreciseIEMerging_martingaleMerging_readValues
    (hb : ∀ k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b k)) (hb1 : ∀ k e, b k e ≤ 1)
    (hπ : IsReadingStrategy π) :
    IsPreciseIEMerging fun e ↦ martingaleMerging b (readValues π e) := by
  refine ⟨(isSEMerging_martingaleMerging hb hb1).isIEMerging_comp_readValues hπ, fun ν _ hν ↦ ?_⟩
  rw [← lintegral_map (isSEMerging_martingaleMerging hb hb1).measurable hπ.measurable_readValues,
    lintegral_martingaleMerging_eq hb hb1 (isExactCondEVar_map_readValues_pi hπ ν hν), measure_univ]

/-- **A martingale merging function is a precise merging function for independent e-values.** -/
theorem isPreciseIEMerging_martingaleMerging
    (hb : ∀ k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b k)) (hb1 : ∀ k e, b k e ≤ 1) :
    IsPreciseIEMerging (martingaleMerging b) := by
  simpa using isPreciseIEMerging_martingaleMerging_readValues hb hb1 isReadingStrategy_self

/-- **Generalized martingale merging functions are merging functions for independent e-values**
[VW24, Theorem 3]: a mixture, against a measure `ρ` of mass at most `1` (the initial capital) on a
measurable space of parameters, of martingale merging functions of the values read by reading
strategies, with bets `b a` and reading strategies `π a` depending on the parameter `a`, is a
merging function for independent e-values when it is jointly measurable. -/
theorem isIEMerging_lintegral_martingaleMerging_readValues {A : Type*}
    {mA : MeasurableSpace A} {ρ : Measure A} (hρ : ρ univ ≤ 1)
    {b : A → Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞} {π : A → (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K}
    (hb : ∀ a k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b a k))
    (hb1 : ∀ a k e, b a k e ≤ 1) (hπ : ∀ a, IsReadingStrategy (π a))
    (hm : Measurable fun p : A × (Fin K → ℝ≥0∞) ↦
      martingaleMerging (b p.fst) (readValues (π p.fst) p.snd)) :
    IsIEMerging fun e ↦ ∫⁻ a, martingaleMerging (b a) (readValues (π a) e) ∂ρ :=
  isIEMerging_lintegral hρ hm fun a ↦
    (isPreciseIEMerging_martingaleMerging_readValues (hb a) (hb1 a) (hπ a)).toIsIEMerging

/-- **Generalized martingale merging functions with initial capital `1` are precise** merging
functions for independent e-values: a mixture, against a probability measure `ρ` on a measurable
space of parameters, of martingale merging functions of the values read by reading strategies,
with bets `b a` and reading strategies `π a` depending on the parameter `a`, is a precise merging
function for independent e-values when it is jointly measurable. -/
theorem isPreciseIEMerging_lintegral_martingaleMerging_readValues {A : Type*}
    {mA : MeasurableSpace A} {ρ : Measure A} [IsProbabilityMeasure ρ]
    {b : A → Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞} {π : A → (k : Fin K) → (Fin k → ℝ≥0∞) → Fin K}
    (hb : ∀ a k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b a k))
    (hb1 : ∀ a k e, b a k e ≤ 1) (hπ : ∀ a, IsReadingStrategy (π a))
    (hm : Measurable fun p : A × (Fin K → ℝ≥0∞) ↦
      martingaleMerging (b p.fst) (readValues (π p.fst) p.snd)) :
    IsPreciseIEMerging fun e ↦ ∫⁻ a, martingaleMerging (b a) (readValues (π a) e) ∂ρ :=
  isPreciseIEMerging_lintegral hm fun a ↦
    isPreciseIEMerging_martingaleMerging_readValues (hb a) (hb1 a) (hπ a)

end Generalized

/-! ### Admissible se-merging functions -/

section Admissible

variable {F G : (Fin K → ℝ≥0∞) → ℝ≥0∞}

/-- **The quasi-sure filter of the merging null of the sequential laws** is the principal filter
of the points with finite coordinates: a product of laws with mean `1` charges each of them. -/
theorem quasiSure_mergingNull_sequentialLaws_eq_principal :
    quasiSure (mergingNull (sequentialLaws K)) =
      Filter.principal (Set.range fun (e : Fin K → ℝ≥0) i ↦ (e i : ℝ≥0∞)) := by
  refine quasiSure_mergingNull_eq_principal fun e ↦ ?_
  obtain ⟨ν, hν, hmean, hne⟩ := exists_pi_lintegral_id_eq_one e
  exact ⟨_, mem_mergingNull_sequentialLaws.2
    ⟨inferInstance, pi_mem_sequentialLaws ν fun i ↦ (hmean i).le⟩, hne⟩

/-- An **admissible se-merging function**: an admissible e-variable for the merging null of the
sequential laws, whose e-variables are the se-merging functions
(`isSEMerging_iff_isEVar_mergingNull`). Its quasi-sure filter is the principal filter of the
points with finite coordinates (`quasiSure_mergingNull_sequentialLaws_eq_principal`), so `F` is
admissible when every se-merging function dominating it at finite arguments equals it there
(`isAdmissibleSEMerging_iff_isAdmissible`, `ProbabilityTheory.IsAdmissibleSEMerging.eq_of_le`). -/
abbrev IsAdmissibleSEMerging (F : (Fin K → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  IsAdmissibleEVar F (mergingNull (sequentialLaws K))

/-- An admissible se-merging function is se-merging. -/
theorem IsAdmissibleSEMerging.isSEMerging (hF : IsAdmissibleSEMerging F) : IsSEMerging F :=
  isSEMerging_iff_isEVar_mergingNull.2 hF.mem

/-- An admissible se-merging function is admissible (`Filter.IsAdmissible`) among the se-merging
functions for the order at finite arguments, the eventual order along the principal filter of the
finite vectors, and conversely. -/
theorem isAdmissibleSEMerging_iff_isAdmissible :
    IsAdmissibleSEMerging F ↔
      (Filter.principal (Set.range fun (e : Fin K → ℝ≥0) i ↦ (e i : ℝ≥0∞))).IsAdmissible
        {G | IsSEMerging G} F := by
  simp only [IsAdmissibleSEMerging, IsAdmissibleEVar,
    quasiSure_mergingNull_sequentialLaws_eq_principal, ← isSEMerging_iff_isEVar_mergingNull]

/-- An se-merging function dominating an admissible se-merging function at finite arguments equals
it there. -/
theorem IsAdmissibleSEMerging.eq_of_le (hF : IsAdmissibleSEMerging F) (hG : IsSEMerging G)
    (hFG : ∀ e : Fin K → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) (e : Fin K → ℝ≥0) :
    G (fun i ↦ e i) = F (fun i ↦ e i) :=
  (Filter.eventuallyLE_principal_range_iff.1
    ((isAdmissibleSEMerging_iff_isAdmissible.1 hF).eventuallyLE hG
      (Filter.eventuallyLE_principal_range_iff.2 hFG)) e).antisymm (hFG e)

/-- **An se-merging function that is admissible among the merging functions for independent
e-values is an admissible se-merging function**: an se-merging function dominating it is a merging
function for independent e-values. -/
theorem IsAdmissibleIEMerging.isAdmissibleSEMerging (hF : IsAdmissibleIEMerging F)
    (hFse : IsSEMerging F) : IsAdmissibleSEMerging F := by
  have hF' := isAdmissibleIEMerging_iff_isAdmissible.1 hF
  exact isAdmissibleSEMerging_iff_isAdmissible.2
    ⟨hFse, fun G hG hle ↦ hF'.eventuallyLE (IsSEMerging.isIEMerging hG) hle⟩

/-- **Martingale merging functions are admissible merging functions for independent e-values**:
they are precise. -/
theorem isAdmissibleIEMerging_martingaleMerging {b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hb : ∀ k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b k)) (hb1 : ∀ k e, b k e ≤ 1) :
    IsAdmissibleIEMerging (martingaleMerging b) :=
  (isPreciseIEMerging_martingaleMerging hb hb1).isAdmissibleIEMerging

/-- **Martingale merging functions are admissible se-merging functions**: one direction of
[VW24, Corollary 1]. -/
theorem isAdmissibleSEMerging_martingaleMerging {b : Fin K → (Fin K → ℝ≥0∞) → ℝ≥0∞}
    (hb : ∀ k, Measurable[piLT (X := fun _ : Fin K ↦ ℝ≥0∞) k] (b k)) (hb1 : ∀ k e, b k e ≤ 1) :
    IsAdmissibleSEMerging (martingaleMerging b) :=
  (isAdmissibleIEMerging_martingaleMerging hb hb1).isAdmissibleSEMerging
    (isSEMerging_martingaleMerging hb hb1)

end Admissible

end ProbabilityTheory
