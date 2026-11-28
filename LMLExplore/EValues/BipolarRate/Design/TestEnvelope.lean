/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Growth
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.InformationTheory.KullbackLeibler.Pi
import LMLExplore.Probability.LargeDeviations.EmpiricalAverage
import LMLExplore.Probability.LargeDeviations.EmpiricalAverage.Integrable

/-!
# The growth of the designs from boxes of test functions

Finitely many sources `a : α` produce observations in a measurable space `𝓧`, and an instance is
a family `κ : α → Measure 𝓧` of laws. For every source `a`, let `G a` be a set of measurable real
functions on `𝓧`, bounded or not, the *test functions* of `a`. A *box* is a set of instances of
probability measures of the form

  `V = {κ | ∀ a, ∀ g ∈ F a, g is κ a-integrable and |∫ g dκ a - q a g| ≤ ε}`

(`ProbabilityTheory.testBox F q ε`), for finite sets `F a` of functions, centres `q a g` and a
radius `ε`, with no condition that `κ` belong to a model. The box is *around* the instance `μ` if
its inequalities are strict at `μ` (`ProbabilityTheory.IsTestBoxAround`).

For a set `Λ` of instances and weights `x : α → ℝ≥0`, the weighted smallest relative entropy
`Ψ_x(κ) = ⨅ ν ∈ Λ, ∑ a, x a * KL(κ a, ν a)` (`ProbabilityTheory.weightedKLInf`) and its envelope
on the boxes around `μ` with test functions in the `G a`,
`Ψ^G_x(μ) = ⨆ (V around μ), ⨅ κ ∈ V, Ψ_x(κ)` (`ProbabilityTheory.testEnvelope`), bound the
growth `D(x)` of the designs proportional to `x` (`ProbabilityTheory.designGrowth`) when the test
functions are integrable under the instances of `Λ`:

  `Ψ^G_x(μ) ≤ D(x) ≤ Ψ_x(μ)`, and so `⨆ w ∈ Δ, Ψ^G_w(μ) ≤ D* ≤ ⨆ w ∈ Δ, Ψ_w(μ)`

for the rate `D*` of the designs (`ProbabilityTheory.designRate`) [EVR26, Note 55, Proposition 8].
The equality `Ψ^G_x(μ) = Ψ_x(μ)` is a lower semicontinuity of `Ψ_x` at `μ` for the topology of the
test functions; under it `D(x) = Ψ_x(μ)`, and under it at the allocations with rational
coordinates `D* = ⨆ w ∈ Δ, Ψ_w(μ)`. The upper bounds are the entropy bounds
`ProbabilityTheory.designGrowth_le_iInf_sum_mul_klDiv` and
`ProbabilityTheory.designRate_le_iSup_iInf_sum_mul_klDiv`.

The lower bound is a Sanov-type argument on the tables of the designs. For a box `V` and a design
`n`, the event `A_n(V)` that the empirical measures of the rows of the table satisfy the
inequalities of `V` (`ProbabilityTheory.testBoxEvent`) has probability at most `exp (- c)` under
every instance of `Λ`, for `c` at most the cost `⨅ κ ∈ V, ∑ a, n a * KL(κ a, ν a)` of the box
[Csi84], also for unbounded test functions; so `1/2 + (1/2) e^c 𝟙_A` is an e-variable for the
laws of the table under `Λ`, and the law of large numbers at `μ` gives `P_μ(A_n(V)) → 1` along
the designs proportional to `x`.

## Main definitions

* `ProbabilityTheory.weightedKLInf κ Λ x`: `Ψ_x(κ) = ⨅ ν ∈ Λ, ∑ a, x a * KL(κ a, ν a)`.
* `ProbabilityTheory.testBox F q ε`: the box of the test functions `F a`, centres `q a g` and
  radius `ε`.
* `ProbabilityTheory.IsTestBoxAround F q ε μ`: that box is around the instance `μ`.
* `ProbabilityTheory.testEnvelope G μ Λ x`: the envelope `Ψ^G_x(μ)`.
* `ProbabilityTheory.testBoxEvent F q ε n`: the event of the table of the design `n` that the
  empirical measures of its rows satisfy the inequalities of the box.

## Main statements

* `ProbabilityTheory.testEnvelope_le_designGrowth`,
  `ProbabilityTheory.designGrowth_le_weightedKLInf`: `Ψ^G_x(μ) ≤ D(x) ≤ Ψ_x(μ)`.
* `ProbabilityTheory.iSup_testEnvelope_le_designRate`,
  `ProbabilityTheory.designRate_le_iSup_weightedKLInf`: `⨆ w ∈ Δ, Ψ^G_w(μ) ≤ D* ≤ ⨆ w ∈ Δ, Ψ_w(μ)`.
* `ProbabilityTheory.designGrowth_eq_weightedKLInf_of_testEnvelope_eq`,
  `ProbabilityTheory.designRate_eq_iSup_weightedKLInf_of_testEnvelope_eq`: the equality cases.
* `ProbabilityTheory.ofReal_exp_mul_designLaw_testBoxEvent_le_one`: the Sanov-type bound on the
  table of a design [Csi84]; the bound for one source is
  `ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one_of_integrable`.
* `ProbabilityTheory.isEVar_inv_two_add_inv_two_mul_indicator_testBoxEvent`: the e-variable
  `1/2 + (1/2) e^c 𝟙_A` of the event of a box on the table of a design.
* `ProbabilityTheory.tendsto_designLaw_testBoxEvent`: the law of large numbers on the tables.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/DesignTestFunctions.lean` and
`EValuesResearch/Results/DesignTestFunctionsAux.lean` (commit `cb8238f`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. The Sanov-type bound conditions
the law of the whole table on the event and uses the superadditivity of the relative entropy over
all the entries at once, rather than the independence of the rows; the law of large numbers for
integrable test functions comes from the strong law. A box contains only instances of
probability measures, whose test functions are integrable: an integral that does not exist does
not satisfy a constraint.

## References

* [Csi84] I. Csiszár, *Sanov property, generalized I-projection and a conditional limit theorem*,
  Ann. Probab. 12 (1984), 768–793.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 55, *Classes that are not dominated: attaining the rate and `D*`
  with one procedure*, Proposition 8.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α 𝓧 : Type*}

/-! ### Boxes of test functions -/

/-- The box of the test functions `F a`, the centres `q a g` and the radius `ε`: the instances `κ`
of probability measures under which, for every source `a` and every `g ∈ F a`, `g` is
`κ a`-integrable and `|∫ g dκ a - q a g| ≤ ε` [EVR26, Note 55, Section 2]. -/
def testBox [MeasurableSpace 𝓧] (F : α → Finset (𝓧 → ℝ)) (q : α → (𝓧 → ℝ) → ℝ) (ε : ℝ) :
    Set (α → Measure 𝓧) :=
  {κ | ∀ a, IsProbabilityMeasure (κ a) ∧
    ∀ g ∈ F a, Integrable g (κ a) ∧ |∫ y, g y ∂(κ a) - q a g| ≤ ε}

variable {m𝓧 : MeasurableSpace 𝓧} {μ κ ν : α → Measure 𝓧}
  {Λ : Set (α → Measure 𝓧)} {x y : α → ℝ≥0} {G : α → Set (𝓧 → ℝ)} {F : α → Finset (𝓧 → ℝ)}
  {q : α → (𝓧 → ℝ) → ℝ} {ε : ℝ}

/-- The instances of a box are the instances of probability measures that satisfy its
inequalities. -/
lemma mem_testBox :
    κ ∈ testBox F q ε ↔ ∀ a, IsProbabilityMeasure (κ a) ∧
      ∀ g ∈ F a, Integrable g (κ a) ∧ |∫ y, g y ∂(κ a) - q a g| ≤ ε :=
  Iff.rfl

/-- The box of the test functions `F a`, the centres `q a g` and the radius `ε` is around the
instance `μ`: `μ` is an instance of probability measures under which the test functions are
integrable and the inequalities of the box are strict [EVR26, Note 55, Section 2]. The radius is
then positive as soon as some `F a` is not empty; when all are empty, the box is the set of all
the instances of probability measures, whatever `ε`. -/
structure IsTestBoxAround (F : α → Finset (𝓧 → ℝ)) (q : α → (𝓧 → ℝ) → ℝ) (ε : ℝ)
    (μ : α → Measure 𝓧) : Prop where
  /-- The laws of `μ` are probability measures. -/
  isProbabilityMeasure (a : α) : IsProbabilityMeasure (μ a)
  /-- The test functions of the box are integrable under `μ`. -/
  integrable ⦃a : α⦄ ⦃g : 𝓧 → ℝ⦄ (hg : g ∈ F a) : Integrable g (μ a)
  /-- The inequalities of the box are strict at `μ`. -/
  abs_sub_lt ⦃a : α⦄ ⦃g : 𝓧 → ℝ⦄ (hg : g ∈ F a) : |∫ y, g y ∂(μ a) - q a g| < ε

/-- An instance is in every box around it. -/
lemma IsTestBoxAround.mem_testBox (hV : IsTestBoxAround F q ε μ) : μ ∈ testBox F q ε :=
  fun a ↦ ⟨hV.isProbabilityMeasure a, fun _ hg ↦ ⟨hV.integrable hg, (hV.abs_sub_lt hg).le⟩⟩

/-- The event of the table of the design `n` that, for every source `a` that `n` observes, the
empirical averages of the test functions `g ∈ F a` on the row of `a` are within `ε` of the centres
`q a g`: the empirical measures of the rows satisfy the inequalities of the box
`testBox F q ε` [EVR26, Note 55, Proposition 8]. -/
def testBoxEvent (F : α → Finset (𝓧 → ℝ)) (q : α → (𝓧 → ℝ) → ℝ) (ε : ℝ) (n : α → ℕ) :
    Set ((Σ a, Fin (n a)) → 𝓧) :=
  {y | ∀ a, n a ≠ 0 → ∀ g ∈ F a, |(∑ i : Fin (n a), g (y ⟨a, i⟩)) / n a - q a g| ≤ ε}

/-- The tables in the event of a box are those whose rows satisfy the inequalities of the box. -/
lemma mem_testBoxEvent {n : α → ℕ} {y : (Σ a, Fin (n a)) → 𝓧} :
    y ∈ testBoxEvent F q ε n ↔
      ∀ a, n a ≠ 0 → ∀ g ∈ F a, |(∑ i : Fin (n a), g (y ⟨a, i⟩)) / n a - q a g| ≤ ε :=
  Iff.rfl

/-- The event of a box of measurable test functions on the table of a design is measurable. -/
lemma measurableSet_testBoxEvent [Countable α] (hFm : ∀ a, ∀ g ∈ F a, Measurable g)
    (n : α → ℕ) : MeasurableSet (testBoxEvent F q ε n) := by
  have h : testBoxEvent F q ε n = ⋂ a, ⋂ (_ : n a ≠ 0), ⋂ g ∈ F a,
      {y : (Σ a, Fin (n a)) → 𝓧 | |(∑ i : Fin (n a), g (y ⟨a, i⟩)) / n a - q a g| ≤ ε} := by
    ext y
    simp [testBoxEvent]
  rw [h]
  refine MeasurableSet.iInter fun a ↦ MeasurableSet.iInter fun _ ↦
    Finset.measurableSet_biInter _ fun g hg ↦ measurableSet_le ?_ measurable_const
  have := hFm a g hg
  fun_prop

/-! ### The weighted smallest relative entropy and its envelope -/

section Envelope

variable [Fintype α]

/-- The weighted smallest relative entropy `Ψ_x(κ) = ⨅ ν ∈ Λ, ∑ a, x a * KL(κ a, ν a)` from the
instance `κ` to the set of instances `Λ`, with the weights `x : α → ℝ≥0` and `0 * ∞ = 0`
[EVR26, Note 55, Section 2]. At the laws of the arms at a model of an identification task, against
the laws of the arms at the alternatives to an answer, and with `x a = (w a).toNNReal`, it is the
cost `LMLExplore.Identification.IdentTask.altCost` of the alternatives at the allocation `w`. -/
noncomputable def weightedKLInf (κ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) :
    ℝ≥0∞ :=
  ⨅ ν ∈ Λ, ∑ a, (x a : ℝ≥0∞) * klDiv (κ a) (ν a)

/-- The definition of `Ψ_x(κ)`, for use outside this file. -/
lemma weightedKLInf_def (κ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) :
    weightedKLInf κ Λ x = ⨅ ν ∈ Λ, ∑ a, (x a : ℝ≥0∞) * klDiv (κ a) (ν a) :=
  (rfl)

/-- `Ψ_x(κ)` is at most the weighted sum of the relative entropies to any instance of `Λ`. -/
lemma weightedKLInf_le_sum (hν : ν ∈ Λ) :
    weightedKLInf κ Λ x ≤ ∑ a, (x a : ℝ≥0∞) * klDiv (κ a) (ν a) :=
  iInf₂_le ν hν

/-- `Ψ_x(κ)` is monotone in the weights. -/
lemma weightedKLInf_mono (h : x ≤ y) : weightedKLInf κ Λ x ≤ weightedKLInf κ Λ y :=
  iInf₂_mono fun _ _ ↦ Finset.sum_le_sum fun a _ ↦ by gcongr; exact h a

/-- `Ψ_x(κ)` is positively homogeneous in the weights. -/
lemma weightedKLInf_smul {t : ℝ≥0} (ht : t ≠ 0) (κ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧))
    (x : α → ℝ≥0) : weightedKLInf κ Λ (t • x) = t * weightedKLInf κ Λ x := by
  simp only [weightedKLInf, Pi.smul_apply, smul_eq_mul, ENNReal.coe_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.2 ht) ENNReal.coe_ne_top]
  exact iInf_congr fun ν ↦
    (ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.2 ht) ENNReal.coe_ne_top).symm

/-- The envelope `Ψ^G_x(μ) = ⨆ (V around μ), ⨅ κ ∈ V, Ψ_x(κ)` of `Ψ_x` at the instance `μ`, over
the boxes `V` around `μ` whose test functions of every source `a` are in `G a`
[EVR26, Note 55, Section 2]. It is at most `Ψ_x(μ)` (`testEnvelope_le_weightedKLInf`), and the
equality is a lower semicontinuity of `Ψ_x` at `μ` for the topology of the test functions. -/
noncomputable def testEnvelope (G : α → Set (𝓧 → ℝ)) (μ : α → Measure 𝓧)
    (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) : ℝ≥0∞ :=
  ⨆ (F : α → Finset (𝓧 → ℝ)) (q : α → (𝓧 → ℝ) → ℝ) (ε : ℝ) (_ : ∀ a, ↑(F a) ⊆ G a)
    (_ : IsTestBoxAround F q ε μ), ⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ x

/-- The definition of the envelope `Ψ^G_x(μ)`, for use outside this file. -/
lemma testEnvelope_def (G : α → Set (𝓧 → ℝ)) (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧))
    (x : α → ℝ≥0) :
    testEnvelope G μ Λ x = ⨆ (F : α → Finset (𝓧 → ℝ)) (q : α → (𝓧 → ℝ) → ℝ) (ε : ℝ)
      (_ : ∀ a, ↑(F a) ⊆ G a) (_ : IsTestBoxAround F q ε μ),
        ⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ x :=
  (rfl)

/-- The envelope is at most `Ψ_x(μ)`: `μ` is in every box around `μ`. -/
theorem testEnvelope_le_weightedKLInf (G : α → Set (𝓧 → ℝ)) (μ : α → Measure 𝓧)
    (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) : testEnvelope G μ Λ x ≤ weightedKLInf μ Λ x :=
  iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hV ↦
    iInf₂_le μ hV.mem_testBox

end Envelope

/-! ### The rows of a table -/

/-- The row of the source `a` of the table of a design `n` has the law of `n a` independent
observations of `μ a`. -/
lemma measurePreserving_designLaw_row [Fintype α] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (n : α → ℕ) (a : α) :
    MeasurePreserving (fun y : (Σ a, Fin (n a)) → 𝓧 ↦ fun i : Fin (n a) ↦ y ⟨a, i⟩)
      (designLaw μ n) (Measure.pi fun _ : Fin (n a) ↦ μ a) := by
  refine ⟨by fun_prop, ?_⟩
  rw [designLaw_def, ← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj sigma_mk_injective

/-! ### The Sanov-type bound on a table -/

/-- **A Sanov-type bound on the table of a design** [Csi84; EVR26, Note 55, Proposition 8]. Let
the test functions `F a` be measurable and integrable under the instance `ν` of probability
measures, and let the box `testBox F q ε` be nonempty. If every instance `κ` of the box has
`c ≤ ∑ a, n a * KL(κ a, ν a)`, then the event of the box on the table of the design `n` has
probability at most `exp (- c)` under `ν`. The test functions need not be bounded. -/
theorem ofReal_exp_mul_designLaw_testBoxEvent_le_one [Fintype α]
    [∀ a, IsProbabilityMeasure (ν a)] (hFm : ∀ a, ∀ g ∈ F a, Measurable g)
    (hFν : ∀ a, ∀ g ∈ F a, Integrable g (ν a)) (hne : (testBox F q ε).Nonempty) {n : α → ℕ}
    {c : ℝ} (hU : ∀ κ ∈ testBox F q ε, ENNReal.ofReal c ≤ ∑ a, (n a : ℝ≥0∞) * klDiv (κ a) (ν a)) :
    ENNReal.ofReal (Real.exp c) * designLaw ν n (testBoxEvent F q ε n) ≤ 1 := by
  set A := testBoxEvent F q ε n
  set P := designLaw ν n
  rcases eq_or_ne (P A) 0 with h0 | h0
  · simp [h0]
  have hA : MeasurableSet A := measurableSet_testBoxEvent hFm n
  -- the law `μ` of the table conditioned on the event, and its rows
  set μ := P[|A]
  have : IsProbabilityMeasure μ := cond_isProbabilityMeasure h0
  set row : (a : α) → ((Σ a, Fin (n a)) → 𝓧) → Fin (n a) → 𝓧 := fun a y i ↦ y ⟨a, i⟩
  have hrow (a : α) : Measurable (row a) := by fun_prop
  -- the test functions along the entries of the rows are integrable under `μ`
  have hint (a : α) {g : 𝓧 → ℝ} (hg : g ∈ F a) (i : Fin (n a)) :
      Integrable (fun x : Fin (n a) → 𝓧 ↦ g (x i)) (μ.map (row a)) := by
    have h1 : Integrable (fun y : (Σ a, Fin (n a)) → 𝓧 ↦ g (y ⟨a, i⟩)) P := by
      rw [show P = Measure.pi fun p : Σ a, Fin (n a) ↦ ν p.1 from designLaw_def ν n]
      exact (measurePreserving_eval (fun p : Σ a, Fin (n a) ↦ ν p.1) ⟨a, i⟩
        ).integrable_comp_of_integrable (hFν a g hg)
    exact (integrable_map_measure ((hFm a g hg).comp (measurable_pi_apply i)).aestronglyMeasurable
      (hrow a).aemeasurable).2 (h1.restrict.smul_measure (ENNReal.inv_ne_top.2 h0))
  -- the instance `R`: the average of the marginals of each observed row, a point of the box
  -- for the other sources
  obtain ⟨κ₀, hκ₀⟩ := hne
  set R : α → Measure 𝓧 := fun a ↦ if n a = 0 then κ₀ a else
    ∑ j : Fin (n a), (((n a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • (μ.map (row a)).map fun x ↦ x j
  have hR : R ∈ testBox F q ε := by
    intro a
    by_cases hna : n a = 0
    · simpa [R, hna] using hκ₀ a
    simp only [R, hna, ↓reduceIte]
    refine ⟨isProbabilityMeasure_sum_smul_map_eval hna _, fun g hg ↦
      ⟨integrable_sum_smul_map_eval _ (hFm a g hg) (hint a hg),
        abs_integral_sum_smul_map_eval_sub_le_of_integrable _ (hFm a g hg) (hint a hg) ?_⟩⟩
    have hms : MeasurableSet {x : Fin (n a) → 𝓧 | |(∑ j, g (x j)) / (n a) - q a g| ≤ ε} := by
      have := hFm a g hg
      exact measurableSet_le (by fun_prop) measurable_const
    refine (ae_map_iff (hrow a).aemeasurable hms).2 ?_
    filter_upwards [ae_cond_mem hA] with y hy
    exact hy a hna g hg
  -- the relative entropy from `μ` to `P` is at least `c`, by convexity on each row and
  -- superadditivity over the entries of the table
  refine ofReal_exp_mul_le_one_of_ofReal_le_klDiv_cond h0 ((hU R hR).trans ?_)
  calc ∑ a, (n a : ℝ≥0∞) * klDiv (R a) (ν a)
  _ ≤ ∑ a, ∑ i : Fin (n a), klDiv (μ.map fun y ↦ y ⟨a, i⟩) (ν a) := by
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases hna : n a = 0
    · simp [hna]
    simp only [R, hna, ↓reduceIte]
    refine (mul_klDiv_sum_smul_map_eval_le _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [Measure.map_map (measurable_pi_apply i) (hrow a)]
    rfl
  _ = ∑ p : Σ a, Fin (n a), klDiv (μ.map fun y ↦ y p) (ν p.1) :=
    (Fintype.sum_sigma fun p : Σ a, Fin (n a) ↦ klDiv (μ.map fun y ↦ y p) (ν p.1)).symm
  _ ≤ klDiv μ P := by
    rw [show P = Measure.pi fun p : Σ a, Fin (n a) ↦ ν p.1 from designLaw_def ν n]
    exact sum_klDiv_map_eval_le (fun p : Σ a, Fin (n a) ↦ ν p.1) μ

/-! ### The law of large numbers on the tables -/

/-- **The law of large numbers on the tables of designs.** Let the box `testBox F q ε` of
measurable test functions be around the instance `μ`, and let the designs `N m` observe every
source never or, in the limit, infinitely often. Then the probability under `μ` of the event of
the box on the table of `N m` tends to `1`. The test functions need only be `μ`-integrable. -/
theorem tendsto_designLaw_testBoxEvent [Fintype α] (hFm : ∀ a, ∀ g ∈ F a, Measurable g)
    (hV : IsTestBoxAround F q ε μ) {N : ℕ → α → ℕ}
    (hN : ∀ a, (∀ m, N m a = 0) ∨ Tendsto (fun m ↦ N m a) atTop atTop) :
    Tendsto (fun m ↦ designLaw μ (N m) (testBoxEvent F q ε (N m))) atTop (𝓝 1) := by
  have := hV.isProbabilityMeasure
  -- the probability that a row violates the inequality of a test function
  set f : α → (𝓧 → ℝ) → ℕ → ℝ≥0∞ := fun a g M ↦
    (Measure.pi fun _ : Fin M ↦ μ a) {z | ε < |(∑ i, g (z i)) / M - q a g|}
  have hf (a : α) {g : 𝓧 → ℝ} (hg : g ∈ F a) :
      Tendsto (fun m ↦ if N m a = 0 then 0 else f a g (N m a)) atTop (𝓝 0) := by
    rcases hN a with h | h
    · simp [h]
    refine ((tendsto_measure_pi_lt_abs_sum_div_sub (hFm a g hg) (hV.integrable hg)
      (hV.abs_sub_lt hg)).comp h).congr' ?_
    filter_upwards [h.eventually_ne_atTop 0] with m hm
    simp [hm, f]
  have hcompl (m : ℕ) : designLaw μ (N m) (testBoxEvent F q ε (N m))ᶜ ≤
      ∑ a, ∑ g ∈ F a, if N m a = 0 then 0 else f a g (N m a) := by
    have hsub : (testBoxEvent F q ε (N m))ᶜ ⊆ ⋃ a, ⋃ g ∈ F a,
        {y : (Σ a, Fin (N m a)) → 𝓧 | N m a ≠ 0 ∧
          ε < |(∑ i : Fin (N m a), g (y ⟨a, i⟩)) / N m a - q a g|} := by
      intro y hy
      simp only [testBoxEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le,
        exists_prop] at hy
      obtain ⟨a, ha, g, hg, hlt⟩ := hy
      exact Set.mem_iUnion₂.2 ⟨a, g, Set.mem_iUnion.2 ⟨hg, ha, hlt⟩⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun a _ ↦ (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun g hg ↦ ?_)))
    by_cases ha : N m a = 0
    · simp [ha]
    simp only [ha, ne_eq, not_false_eq_true, true_and, ↓reduceIte, f]
    have := hFm a g hg
    have hs : NullMeasurableSet {z : Fin (N m a) → 𝓧 | ε < |(∑ i, g (z i)) / (N m a) - q a g|}
        (Measure.pi fun _ : Fin (N m a) ↦ μ a) :=
      (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet
    exact ((measurePreserving_designLaw_row μ (N m) a).measure_preimage hs).le
  have h0 : Tendsto (fun m ↦ designLaw μ (N m) (testBoxEvent F q ε (N m))ᶜ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ bot_le)
      hcompl
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.univ : Finset α)
      fun a _ ↦ tendsto_finsetSum (F a) fun g hg ↦ hf a hg
  have h1 := ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at h1
  refine h1.congr fun m ↦ ?_
  rw [prob_compl_eq_one_sub (measurableSet_testBoxEvent hFm (N m)),
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-! ### The e-variable of an event -/

section EVariable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The e-variable of an event.** If `e^t P(A) ≤ 1` for every member `P` of a null `S` of
measures of mass at most `1`, then `1/2 + (1/2) e^t 𝟙_A` is an e-variable for `S`. -/
lemma isEVar_inv_two_add_inv_two_mul_indicator {S : Set (Measure Ω)}
    (hS : ∀ P ∈ S, P Set.univ ≤ 1) {A : Set Ω} (hA : MeasurableSet A) {t : ℝ}
    (hP : ∀ P ∈ S, ENNReal.ofReal (Real.exp t) * P A ≤ 1) :
    IsEVar (fun ω ↦ 2⁻¹ + 2⁻¹ * A.indicator (fun _ ↦ ENNReal.ofReal (Real.exp t)) ω) S := by
  refine ⟨measurable_const.add (measurable_const.mul (measurable_const.indicator hA)),
    fun P hPS ↦ ?_⟩
  calc ∫⁻ ω, 2⁻¹ + 2⁻¹ * A.indicator (fun _ ↦ ENNReal.ofReal (Real.exp t)) ω ∂P
  _ = 2⁻¹ * P Set.univ + 2⁻¹ * (ENNReal.ofReal (Real.exp t) * P A) := by
    simp [lintegral_add_right _ ((measurable_const.indicator hA).const_mul _),
      lintegral_const_mul _ (measurable_const.indicator hA), lintegral_indicator_const hA]
  _ ≤ 2⁻¹ * 1 + 2⁻¹ * 1 := by gcongr; exacts [hS P hPS, hP P hPS]
  _ = 1 := by rw [mul_one, ENNReal.inv_two_add_inv_two]

/-- The expected logarithm of `1/2 + (1/2) e^t 𝟙_A` under a probability measure `Q` is at least
`t Q(A) - log 2`. -/
lemma sub_log_two_le_eintegral_log_inv_two_add_inv_two_mul_indicator (Q : Measure Ω)
    [IsProbabilityMeasure Q] {A : Set Ω} (hA : MeasurableSet A) (t : ℝ) :
    ((t * Q.real A - Real.log 2 : ℝ) : EReal) ≤
      ∫ᵉ ω, ENNReal.log (2⁻¹ + 2⁻¹ * A.indicator (fun _ ↦ ENNReal.ofReal (Real.exp t)) ω) ∂Q := by
  set g : Ω → ℝ := fun ω ↦ A.indicator (fun _ ↦ t) ω - Real.log 2
  have hg (ω : Ω) : ENNReal.ofReal (Real.exp (g ω)) ≤
      2⁻¹ + 2⁻¹ * A.indicator (fun _ ↦ ENNReal.ofReal (Real.exp t)) ω := by
    by_cases hω : ω ∈ A
    · simp only [g, Set.indicator_of_mem hω]
      rw [Real.exp_sub, Real.exp_log two_pos, ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
      exact le_add_self
    · simp only [g, Set.indicator_of_notMem hω, zero_sub, Real.exp_neg, Real.exp_log two_pos,
        mul_zero, add_zero]
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hgi : Integrable g Q := ((integrable_const t).indicator hA).sub (integrable_const _)
  calc ((t * Q.real A - Real.log 2 : ℝ) : EReal)
  _ = ∫ᵉ ω, (g ω : EReal) ∂Q := by
    rw [eintegral_eq_integral hgi]
    simp [g, integral_sub ((integrable_const t).indicator hA) (integrable_const _),
      integral_indicator_const _ hA, mul_comm]
  _ ≤ _ := eintegral_mono fun ω ↦ by
    calc (g ω : EReal)
    _ = ENNReal.log (ENNReal.ofReal (Real.exp (g ω))) := by rw [ENNReal.log_ofReal_exp]
    _ ≤ _ := ENNReal.log_monotone (hg ω)

end EVariable

/-- **The e-variable of a box on the table of a design** [EVR26, Note 55, Proposition 8]. Let
the box `V = testBox F q ε` be nonempty, with measurable test functions integrable under the
instances of `Λ`, instances of probability measures. For a design `n` and a real `c` at most the
cost `⨅ κ ∈ V, Ψ_n(κ)` of the box against `Λ`, the function `1/2 + (1/2) e^c 𝟙_A` of the table of
`n`, for the event `A` of the box, is an e-variable for the laws of the table under the instances
of `Λ`. -/
theorem isEVar_inv_two_add_inv_two_mul_indicator_testBoxEvent [Fintype α]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hFm : ∀ a, ∀ g ∈ F a, Measurable g)
    (hFΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ F a, Integrable g (ν a)) (hne : (testBox F q ε).Nonempty)
    {n : α → ℕ} {c : ℝ}
    (hc : ENNReal.ofReal c ≤ ⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ fun a ↦ (n a : ℝ≥0)) :
    IsEVar (fun y ↦ 2⁻¹ + 2⁻¹ *
        (testBoxEvent F q ε n).indicator (fun _ ↦ ENNReal.ofReal (Real.exp c)) y)
      ((fun ν ↦ designLaw ν n) '' Λ) := by
  refine isEVar_inv_two_add_inv_two_mul_indicator ?_ (measurableSet_testBoxEvent hFm n) ?_
  · rintro _ ⟨ν, hν, rfl⟩
    exact designLaw_univ_le_one (fun a ↦ (hΛ ν hν a).measure_univ.le) n
  · rintro _ ⟨ν, hν, rfl⟩
    have := hΛ ν hν
    refine ofReal_exp_mul_designLaw_testBoxEvent_le_one hFm (hFΛ ν hν) hne fun κ hκ ↦ ?_
    exact (hc.trans (iInf₂_le κ hκ)).trans ((weightedKLInf_le_sum hν).trans_eq (by simp))

/-! ### The designs proportional to a vector -/

/-- The design proportional to `x` observes every source `a` at least `m x a` times. -/
lemma mul_le_proportionalDesign (x : α → ℝ≥0) (η : ℝ≥0) (m : ℕ) (a : α) :
    (m : ℝ≥0) * x a ≤ proportionalDesign x η m a := by
  by_cases hx : x a = 0
  · simp [hx]
  exact le_trans (mul_le_mul_right (le_add_of_nonneg_right zero_le) _) (le_proportionalDesign hx)

/-- The designs proportional to `x` observe a source `a` with `x a ≠ 0` infinitely often in the
limit. -/
lemma tendsto_proportionalDesign_atTop {a : α} (hx : x a ≠ 0) (η : ℝ≥0) :
    Tendsto (fun m ↦ proportionalDesign x η m a) atTop atTop := by
  refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono (fun m ↦ ?_)
    (tendsto_natCast_atTop_atTop.atTop_mul_const (pos_iff_ne_zero.2 hx)))
  exact_mod_cast mul_le_proportionalDesign x η m a

/-! ### The lower bound on the growth of the designs -/

section Growth

variable [Fintype α]

/-- The lower bound on the growth of the designs for one box: if the box `testBox F q ε` of
measurable test functions, integrable under the instances of `Λ`, is around `μ`, then
`⨅ κ ∈ V, Ψ_x(κ) ≤ D(x)` for that box `V`. -/
private lemma iInf_weightedKLInf_le_designGrowth
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hFm : ∀ a, ∀ g ∈ F a, Measurable g)
    (hFΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ F a, Integrable g (ν a)) (hV : IsTestBoxAround F q ε μ)
    (x : α → ℝ≥0) :
    ((⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ x : ℝ≥0∞) : EReal) ≤ designGrowth μ Λ x := by
  have := hV.isProbabilityMeasure
  set L := ⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ x
  have hΛ1 : ∀ ν ∈ Λ, ∀ a, ν a Set.univ ≤ 1 := fun ν hν a ↦ (hΛ ν hν a).measure_univ.le
  refine le_of_forall_lt_imp_le_of_dense fun b hb ↦ ?_
  rcases le_or_gt b 0 with hb0 | hb0
  · exact hb0.trans (designGrowth_nonneg μ hΛ1 x)
  -- `b` is a positive real `ℓ`, and `ℓ < ℓ' < L` for a real `ℓ'`
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ℝ, (ℓ : EReal) = b :=
    ⟨b.toReal, EReal.coe_toReal (hb.trans_le le_top).ne (ne_bot_of_gt hb0)⟩
  have hℓ0 : 0 < ℓ := by exact_mod_cast hb0
  have hℓL : ENNReal.ofReal ℓ < L := by
    rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hℓ0.le]
    exact hb
  obtain ⟨b', hb'1, hb'2⟩ := exists_between hℓL
  have hb'top : b' ≠ ⊤ := (hb'2.trans_le le_top).ne
  set ℓ' := b'.toReal
  have hℓℓ' : ℓ < ℓ' := by
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hℓ0.le, ENNReal.ofReal_toReal hb'top]
    exact hb'1
  have hℓ'0 : 0 < ℓ' := hℓ0.trans hℓℓ'
  have hℓ'L : ENNReal.ofReal ℓ' < L := by rwa [ENNReal.ofReal_toReal hb'top]
  refine le_designGrowth_of_forall_sub_le fun η hη ↦ ?_
  set N : ℕ → α → ℕ := fun m ↦ proportionalDesign x η m
  -- the law of large numbers under `μ`: the event of the box has probability above `ℓ / ℓ'`
  -- for the large designs
  have hlim : Tendsto (fun m ↦ (designLaw μ (N m)).real (testBoxEvent F q ε (N m))) atTop
      (𝓝 1) :=
    (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (tendsto_designLaw_testBoxEvent hFm hV
      fun a ↦ if hx : x a = 0 then .inl fun _ ↦ proportionalDesign_of_eq_zero hx
        else .inr (tendsto_proportionalDesign_atTop hx η))
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds ((div_lt_one hℓ'0).2 hℓℓ')))
  refine ⟨M * ℓ + Real.log 2, fun m hm ↦ ?_⟩
  rcases lt_or_ge m M with hmM | hmM
  · -- the first designs: the value is nonnegative
    refine le_trans ?_ (designValue_nonneg μ hΛ1 _)
    have : (m : ℝ) * ℓ ≤ M * ℓ := by gcongr
    exact_mod_cast (by linarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)] :
      (m : ℝ) * ℓ - (M * ℓ + Real.log 2) ≤ 0)
  -- the e-variable of the event of the box, at the level `m ℓ'`
  have hc : ENNReal.ofReal (m * ℓ') ≤
      ⨅ κ ∈ testBox F q ε, weightedKLInf κ Λ fun a ↦ (N m a : ℝ≥0) := by
    refine le_iInf₂ fun κ hκ ↦ ?_
    calc ENNReal.ofReal (m * ℓ')
    _ = ((m : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ℓ' := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.coe_natCast]
    _ ≤ (m : ℝ≥0) * weightedKLInf κ Λ x := by
      gcongr
      exact hℓ'L.le.trans (iInf₂_le κ hκ)
    _ = weightedKLInf κ Λ ((m : ℝ≥0) • x) :=
      (weightedKLInf_smul (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 hm)) κ Λ x).symm
    _ ≤ weightedKLInf κ Λ fun a ↦ (N m a : ℝ≥0) :=
      weightedKLInf_mono fun a ↦ mul_le_proportionalDesign x η m a
  have h := (sub_log_two_le_eintegral_log_inv_two_add_inv_two_mul_indicator (designLaw μ (N m))
    (measurableSet_testBoxEvent hFm (N m)) (m * ℓ')).trans
    ((isEVar_inv_two_add_inv_two_mul_indicator_testBoxEvent hΛ hFm hFΛ ⟨μ, hV.mem_testBox⟩
      hc).eintegral_log_le_maxEPower _)
  rw [← designValue_def] at h
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) h
  have hPm := (hM m hmM).le
  rw [div_le_iff₀ hℓ'0] at hPm
  have : (m : ℝ) * ℓ ≤ m * ℓ' * (designLaw μ (N m)).real (testBoxEvent F q ε (N m)) := by
    calc (m : ℝ) * ℓ
    _ ≤ m * ((designLaw μ (N m)).real (testBoxEvent F q ε (N m)) * ℓ') := by gcongr
    _ = _ := by ring
  have hMℓ : 0 ≤ (M : ℝ) * ℓ := by positivity
  linarith

/-- **The lower bound on the growth of the designs** [EVR26, Note 55, Proposition 8]. If the test
functions are measurable and integrable under every instance of `Λ`, an instance of probability
measures, then `Ψ^G_x(μ) ≤ D(x)` for every `x`. Nothing is assumed on `μ`: a box around `μ`
makes `μ` an instance of probability measures under which its test functions are integrable. -/
theorem testEnvelope_le_designGrowth (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    (hGm : ∀ a, ∀ g ∈ G a, Measurable g) (hGΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ G a, Integrable g (ν a))
    (x : α → ℝ≥0) :
    (testEnvelope G μ Λ x : EReal) ≤ designGrowth μ Λ x := by
  have hD0 := designGrowth_nonneg μ (fun ν hν a ↦ (hΛ ν hν a).measure_univ.le) x
  rw [← EReal.coe_toENNReal hD0, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine iSup_le fun F ↦ iSup_le fun q ↦ iSup_le fun ε ↦ iSup_le fun hFG ↦ iSup_le fun hV ↦ ?_
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hD0]
  exact iInf_weightedKLInf_le_designGrowth hΛ (fun a g hg ↦ hGm a g (hFG a hg))
    (fun ν hν a g hg ↦ hGΛ ν hν a g (hFG a hg)) hV x

/-- **The upper bound on the growth of the designs**: `D(x) ≤ Ψ_x(μ)`. This is the entropy bound
`ProbabilityTheory.designGrowth_le_iInf_sum_mul_klDiv`, written with `weightedKLInf`. -/
theorem designGrowth_le_weightedKLInf [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (x : α → ℝ≥0) :
    designGrowth μ Λ x ≤ weightedKLInf μ Λ x :=
  designGrowth_le_iInf_sum_mul_klDiv hΛ x

/-- **The growth of the designs in the equality case** [EVR26, Note 55, Proposition 8]: if the
test functions are measurable and integrable under the instances of `Λ` and
`Ψ^G_x(μ) = Ψ_x(μ)`, then `D(x) = Ψ_x(μ)`. -/
theorem designGrowth_eq_weightedKLInf_of_testEnvelope_eq [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hGm : ∀ a, ∀ g ∈ G a, Measurable g)
    (hGΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ G a, Integrable g (ν a))
    (h : testEnvelope G μ Λ x = weightedKLInf μ Λ x) :
    designGrowth μ Λ x = weightedKLInf μ Λ x :=
  le_antisymm (designGrowth_le_weightedKLInf hΛ x) (h ▸ testEnvelope_le_designGrowth hΛ hGm hGΛ x)

/-- For weights `x` of sum `1`, the growth of the designs proportional to `x` is at most the rate
of the designs, also when `Λ` is empty. -/
theorem designGrowth_le_designRate_of_sum_eq_one [∀ a, IsProbabilityMeasure (μ a)]
    (hx : ∑ a, x a = 1) : designGrowth μ Λ x ≤ designRate μ Λ := by
  rcases Λ.eq_empty_or_nonempty with rfl | hΛ
  · -- against no instance, the rate of the designs is infinite
    have : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hx
    refine le_top.trans (le_of_eq ?_)
    have h1 : designValue μ ∅ (fun _ ↦ 1) = ⊤ := by
      rw [designValue_def, Set.image_empty, maxEPower_empty]
    have h2 := designValue_div_le_designRate μ ∅ (fun _ ↦ 1)
    rw [h1, EReal.top_div_of_pos_ne_top (by simpa using Fintype.card_pos)
      (EReal.natCast_ne_top _)] at h2
    exact (top_le_iff.1 h2).symm
  refine (designGrowth_le_designRate_mul hΛ x).trans_eq ?_
  rw [← NNReal.coe_sum, hx]
  simp

end Growth

/-! ### The rate of the designs -/

section Rate

variable [Fintype α]

/-- Every allocation `w` of the simplex is, up to a factor `t < 1`, below an allocation of the
simplex with rational coordinates. -/
lemma exists_rat_mem_simplex_mul_le {w : α → ℝ} (hw : w ∈ LMLExplore.simplex α) {t : ℝ}
    (ht : t < 1) : ∃ w' ∈ LMLExplore.simplex α,
      (∀ a, w' a ∈ Set.range ((↑) : ℚ → ℝ)) ∧ ∀ a, t * w a ≤ w' a := by
  classical
  obtain ⟨hw0, hw1⟩ := LMLExplore.mem_simplex_iff.1 hw
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨a₀⟩ := hne
  -- rational coordinates `r a` between `max (t w a) 0` and `w a`
  have hr (a : α) : ∃ r : ℚ, t * w a ≤ r ∧ (r : ℝ) ≤ w a ∧ 0 ≤ (r : ℝ) := by
    rcases (hw0 a).eq_or_lt with h | h
    · exact ⟨0, by simp [← h], by simp [← h], by simp⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt (mul_lt_of_lt_one_left h ht) h)
    exact ⟨r, (le_max_left _ _).trans hr1.le, hr2.le, (le_max_right _ _).trans hr1.le⟩
  choose r hr using hr
  set s : ℚ := ∑ a, r a
  have hs : (s : ℝ) ≤ 1 := by
    rw [← hw1]
    push_cast [s]
    exact Finset.sum_le_sum fun a _ ↦ (hr a).2.1
  -- the missing mass `1 - s` goes to the source `a₀`
  refine ⟨fun a ↦ (r a : ℝ) + if a = a₀ then 1 - (s : ℝ) else 0,
    LMLExplore.mem_simplex_iff.2 ⟨fun a ↦ ?_, ?_⟩, fun a ↦ ?_, fun a ↦ ?_⟩
  · have := (hr a).2.2
    split_ifs <;> linarith
  · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    push_cast [s]
    ring
  · exact ⟨r a + if a = a₀ then 1 - s else 0, by dsimp only; split_ifs <;> push_cast <;> ring⟩
  · have := (hr a).1
    dsimp only
    split_ifs <;> linarith

/-- The supremum of `Ψ_w(κ)` over the simplex is its supremum over the allocations with rational
coordinates, since `w ↦ Ψ_w(κ)` is monotone and positively homogeneous. -/
theorem iSup_weightedKLInf_le_iSup_rat (κ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) :
    ⨆ w ∈ LMLExplore.simplex α, weightedKLInf κ Λ (fun a ↦ (w a).toNNReal) ≤
      ⨆ w ∈ LMLExplore.simplex α, ⨆ (_ : ∀ a, w a ∈ Set.range ((↑) : ℚ → ℝ)),
        weightedKLInf κ Λ (fun a ↦ (w a).toNNReal) := by
  refine iSup₂_le fun w hw ↦ ?_
  set R := ⨆ w ∈ LMLExplore.simplex α, ⨆ (_ : ∀ a, w a ∈ Set.range ((↑) : ℚ → ℝ)),
    weightedKLInf κ Λ (fun a ↦ (w a).toNNReal)
  -- `t Ψ_w(κ) ≤ R` for every `t < 1`, and `t Ψ_w(κ) → Ψ_w(κ)` as `t → 1`
  have h_tendsto : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ≥0∞) * weightedKLInf κ Λ (fun a ↦ (w a).toNNReal))
      (𝓝[<] 1) (𝓝 ((1 : ℝ≥0) * weightedKLInf κ Λ (fun a ↦ (w a).toNNReal))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 (tendsto_nhdsWithin_of_tendsto_nhds
      tendsto_id)) (Or.inl (by simp))
  rw [ENNReal.coe_one, one_mul] at h_tendsto
  have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  refine le_of_tendsto h_tendsto ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ≥0) < 1)] with t ht
  obtain ⟨w', hw', hw'q, hw'le⟩ := exists_rat_mem_simplex_mul_le hw (t := t)
    (by exact_mod_cast ht.2)
  calc (t : ℝ≥0∞) * weightedKLInf κ Λ (fun a ↦ (w a).toNNReal)
  _ = weightedKLInf κ Λ (t • fun a ↦ (w a).toNNReal) := (weightedKLInf_smul ht.1.ne' _ _ _).symm
  _ ≤ weightedKLInf κ Λ (fun a ↦ (w' a).toNNReal) := by
    refine weightedKLInf_mono fun a ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← NNReal.coe_le_coe, NNReal.coe_mul,
      Real.coe_toNNReal _ ((LMLExplore.mem_simplex_iff.1 hw).1 a),
      Real.coe_toNNReal _ ((LMLExplore.mem_simplex_iff.1 hw').1 a)]
    exact hw'le a
  _ ≤ R := le_iSup₂_of_le w' hw' (le_iSup_of_le hw'q le_rfl)

/-- **The lower bound on the rate of the designs** [EVR26, Note 55, Proposition 8]: if the test
functions are measurable and integrable under the instances of `Λ`, then
`⨆ w ∈ Δ, Ψ^G_w(μ) ≤ D*`. -/
theorem iSup_testEnvelope_le_designRate (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    (hGm : ∀ a, ∀ g ∈ G a, Measurable g) (hGΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ G a, Integrable g (ν a)) :
    ⨆ w ∈ LMLExplore.simplex α, (testEnvelope G μ Λ (fun a ↦ (w a).toNNReal) : EReal) ≤
      designRate μ Λ := by
  refine iSup₂_le fun w hw ↦ ?_
  have hw1 : ∑ a, (w a).toNNReal = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_sum, NNReal.coe_one,
      ← (LMLExplore.mem_simplex_iff.1 hw).2]
    exact Finset.sum_congr rfl fun a _ ↦ Real.coe_toNNReal _ ((LMLExplore.mem_simplex_iff.1 hw).1 a)
  have hD0 := designRate_nonneg μ Λ
  rw [← EReal.coe_toENNReal hD0, EReal.coe_ennreal_le_coe_ennreal_iff, testEnvelope_def]
  refine iSup_le fun F ↦ iSup_le fun q ↦ iSup_le fun ε ↦ iSup_le fun hFG ↦ iSup_le fun hV ↦ ?_
  have := hV.isProbabilityMeasure
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hD0]
  refine le_trans ?_ (designGrowth_le_designRate_of_sum_eq_one hw1)
  exact iInf_weightedKLInf_le_designGrowth hΛ (fun a g hg ↦ hGm a g (hFG a hg))
    (fun ν hν a g hg ↦ hGΛ ν hν a g (hFG a hg)) hV _

/-- **The upper bound on the rate of the designs**: `D* ≤ ⨆ w ∈ Δ, Ψ_w(μ)`. This is the entropy
bound `ProbabilityTheory.designRate_le_iSup_iInf_sum_mul_klDiv`, written with `weightedKLInf`. -/
theorem designRate_le_iSup_weightedKLInf [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) :
    designRate μ Λ ≤ ((⨆ w ∈ LMLExplore.simplex α,
      weightedKLInf μ Λ (fun a ↦ (w a).toNNReal) : ℝ≥0∞) : EReal) :=
  designRate_le_iSup_iInf_sum_mul_klDiv hΛ

/-- **The rate of the designs in the equality case** [EVR26, Note 55, Proposition 8]: if the test
functions are measurable and integrable under the instances of `Λ` and `Ψ^G_w(μ) = Ψ_w(μ)` for
every allocation `w` of the simplex with rational coordinates, then `D* = ⨆ w ∈ Δ, Ψ_w(μ)`. -/
theorem designRate_eq_iSup_weightedKLInf_of_testEnvelope_eq [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hGm : ∀ a, ∀ g ∈ G a, Measurable g)
    (hGΛ : ∀ ν ∈ Λ, ∀ a, ∀ g ∈ G a, Integrable g (ν a))
    (h : ∀ w ∈ LMLExplore.simplex α, (∀ a, w a ∈ Set.range ((↑) : ℚ → ℝ)) →
      testEnvelope G μ Λ (fun a ↦ (w a).toNNReal) = weightedKLInf μ Λ (fun a ↦ (w a).toNNReal)) :
    designRate μ Λ = ((⨆ w ∈ LMLExplore.simplex α,
      weightedKLInf μ Λ (fun a ↦ (w a).toNNReal) : ℝ≥0∞) : EReal) := by
  refine le_antisymm (designRate_le_iSup_weightedKLInf hΛ) ?_
  have hD0 := designRate_nonneg μ Λ
  rw [← EReal.coe_toENNReal hD0, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine (iSup_weightedKLInf_le_iSup_rat μ Λ).trans (iSup₂_le fun w hw ↦ iSup_le fun hwq ↦ ?_)
  rw [← h w hw hwq, ← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hD0]
  exact le_trans (le_iSup₂_of_le w hw le_rfl) (iSup_testEnvelope_le_designRate hΛ hGm hGΛ)

end Rate

end ProbabilityTheory
