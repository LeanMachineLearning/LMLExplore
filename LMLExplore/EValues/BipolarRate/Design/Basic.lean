/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.EValues.BipolarRate.Basic
import LMLExplore.Data.EReal.Inv
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Data.EReal.Operations

/-!
# The value and the rate of designs with several sources

Finitely many sources `a : α` produce observations in a common measurable space `𝓧`. An instance
is a family `μ : α → Measure 𝓧` of laws, one for each source, and a set of instances is any
`Λ : Set (α → Measure 𝓧)`: products of models of the sources and structured models are both
covered. A design `n : α → ℕ` observes the source `a` exactly `n a` times, with no adaptivity. Its
observations form a table indexed by the entries `⟨a, i⟩` with `i < n a`, a point of
`(Σ a, Fin (n a)) → 𝓧`, whose law under the instance `μ` is the product `designLaw μ n`.

The value `designValue μ Λ n` of the design `n` is the largest expected logarithm under `μ` of an
e-variable of its table for the instances of `Λ`, and the rate `designRate μ Λ` of the designs is
the supremum of the values per observation, `D* = ⨆ n, designValue μ Λ n / ∑ a, n a`. These are
the constants of the Wald inequality with a design, which bounds the expected logarithm of an
e-variable at a stopping time of an algorithm that chooses adaptively which source to observe
[EVR26, Note 41]: adaptive sampling does not beat the best fixed design. With one source, the
rate of the designs is the bipolar rate of `ProbabilityTheory.bipolarRate`.

## Main definitions

* `ProbabilityTheory.designLaw μ n`: the law of the table of the design `n` under the instance
  `μ`, the product of `n a` copies of `μ a` for every source `a`.
* `ProbabilityTheory.designValue μ Λ n`: the value of the design `n`, the largest e-power under
  `designLaw μ n` of the null `{designLaw ν n | ν ∈ Λ}`.
* `ProbabilityTheory.designRate μ Λ`: the rate of the designs,
  `⨆ n, designValue μ Λ n / ∑ a, n a`.

* `ProbabilityTheory.designBlockEquiv r m`: `m` tables of the design `r`, as one table of the
  design `m • r`.

## Main statements

* `ProbabilityTheory.designValue_mono`: the value of a design is monotone in the design.
* `ProbabilityTheory.designValue_le_iInf_sum_mul_klDiv`: the entropy bound
  `designValue μ Λ n ≤ ⨅ ν ∈ Λ, ∑ a, n a * klDiv (μ a) (ν a)`.
* `ProbabilityTheory.designRate_le_iSup_iInf_sum_mul_klDiv`: the entropy bound on the rate,
  `designRate μ Λ ≤ ⨆ w, ⨅ ν ∈ Λ, ∑ a, w a * klDiv (μ a) (ν a)` over the probability vectors `w`.
* `ProbabilityTheory.measurePreserving_designBlockEquiv`: `m` independent tables of the design `r`
  have the law of the table of the design `m • r`.
* `ProbabilityTheory.maxLogGrowth_designLaw`: `m` independent tables of the design `r` are the
  table of the design `m • r`, so the value of `m • r` is the largest expected logarithm of an
  `m`-sample e-variable for the i.i.d. null of the laws `designLaw ν r`, `ν ∈ Λ`.
* `ProbabilityTheory.designRate_eq_iSup_bipolarRate`: the rate of the designs is the supremum,
  over the designs `r`, of the bipolar rate of the tables of `r` per observation.
* `ProbabilityTheory.designRate_unique`: with one source, the rate of the designs is the bipolar
  rate of the law of the source against the laws of the source in `Λ`.

## Implementation notes

The definitions and proofs are adapted from the draft `notes/lean-wip/SeveralArmsAux.lean` of the
paper project `RemyDegenne/evalues_research`, changed to `maxEPower` and `maxLogGrowth`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Sections 1 and 2.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {α 𝓧 : Type*} [Fintype α] {m𝓧 : MeasurableSpace 𝓧} {μ ν : α → Measure 𝓧}
  {Λ Λ' : Set (α → Measure 𝓧)} {n n' : α → ℕ}

/-! ### The table of a design -/

/-- The law of the table of the design `n` under the instance `μ`: the source `a` is observed
`n a` times, and the observations are independent, those of the source `a` with law `μ a`. The
table is indexed by the entries `⟨a, i⟩` with `i < n a`. -/
noncomputable def designLaw (μ : α → Measure 𝓧) (n : α → ℕ) :
    Measure ((Σ a, Fin (n a)) → 𝓧) :=
  Measure.pi fun p ↦ μ p.1

lemma designLaw_def (μ : α → Measure 𝓧) (n : α → ℕ) :
    designLaw μ n = Measure.pi fun p : Σ a, Fin (n a) ↦ μ p.1 :=
  (rfl)

instance [∀ a, IsProbabilityMeasure (μ a)] : IsProbabilityMeasure (designLaw μ n) := by
  rw [designLaw_def]
  infer_instance

/-- The table of a design under an instance of measures of mass at most `1` has mass at most
`1`. -/
lemma designLaw_univ_le_one (hν : ∀ a, ν a Set.univ ≤ 1) (n : α → ℕ) :
    designLaw ν n Set.univ ≤ 1 := by
  have (a : α) : IsFiniteMeasure (ν a) := ⟨(hν a).trans_lt ENNReal.one_lt_top⟩
  rw [designLaw_def, Measure.pi_univ]
  exact Finset.prod_le_one fun p _ ↦ hν p.1

/-- The table of the empty design is a point mass. -/
lemma designLaw_zero (ν : α → Measure 𝓧) :
    designLaw ν 0 = Measure.dirac fun p : Σ a, Fin ((0 : α → ℕ) a) ↦ p.2.elim0 := by
  have : IsEmpty (Σ a, Fin ((0 : α → ℕ) a)) := ⟨fun p ↦ p.2.elim0⟩
  rw [designLaw_def]
  exact Measure.pi_of_empty _ _

/-- The first `n a` observations of each source `a`, read in the table of a larger design `n'`,
form the table of the design `n`. -/
lemma map_designLaw_comp_sigmaMap [∀ a, IsProbabilityMeasure (ν a)] (h : n ≤ n') :
    (designLaw ν n').map (fun y : (Σ a, Fin (n' a)) → 𝓧 ↦
        y ∘ Sigma.map id fun a : α ↦ (Fin.castLE (h a) : Fin (n a) → Fin (n' a))) =
      designLaw ν n := by
  rw [designLaw_def, designLaw_def, ← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj
    (Function.injective_id.sigma_map fun a ↦ Fin.castLE_injective (h a))

/-! ### The value of a design -/

/-- The value of the design `n` for the instance `μ` against the set of instances `Λ`: the largest
expected logarithm `∫ᵉ y, log (X y) ∂(designLaw μ n)` of a function `X` of the table of `n` that
is an e-variable for the laws `designLaw ν n` of that table under the instances `ν` of `Λ`
[EVR26, Note 41, Section 1]. -/
noncomputable def designValue (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (n : α → ℕ) :
    EReal :=
  maxEPower (designLaw μ n) ((fun ν ↦ designLaw ν n) '' Λ)

/-- The rate of the designs for the instance `μ` against the set of instances `Λ`: the supremum
over the designs `n` of the value of `n` per observation, `designValue μ Λ n / ∑ a, n a`
[EVR26, Note 41, Section 1]. The empty design contributes `0`, since division by `0` in `EReal`
gives `0`. -/
noncomputable def designRate (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) : EReal :=
  ⨆ n : α → ℕ, designValue μ Λ n / ((∑ a, n a : ℕ) : EReal)

lemma designValue_def (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (n : α → ℕ) :
    designValue μ Λ n = maxEPower (designLaw μ n) ((fun ν ↦ designLaw ν n) '' Λ) :=
  (rfl)

lemma designRate_def (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) :
    designRate μ Λ = ⨆ n : α → ℕ, designValue μ Λ n / ((∑ a, n a : ℕ) : EReal) :=
  (rfl)

/-- The value of a design against instances of measures of mass at most `1` is nonnegative, as
the constant `1` is an e-variable. -/
lemma designValue_nonneg (μ : α → Measure 𝓧) (hΛ : ∀ ν ∈ Λ, ∀ a, ν a Set.univ ≤ 1)
    (n : α → ℕ) : 0 ≤ designValue μ Λ n :=
  maxEPower_nonneg _ fun _ ⟨ν, hν, h⟩ ↦ h ▸ designLaw_univ_le_one (hΛ ν hν) n

/-- The value of a design is antitone in the set of instances. -/
@[gcongr]
lemma designValue_anti (h : Λ ⊆ Λ') : designValue μ Λ' n ≤ designValue μ Λ n :=
  maxEPower_anti (Set.image_mono h)

/-- The value of a design is monotone in the design: an e-variable of the table of a design is an
e-variable of the table of every larger design, which contains it. -/
lemma designValue_mono [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (h : n ≤ n') :
    designValue μ Λ n ≤ designValue μ Λ n' := by
  rw [designValue_def, designValue_def, ← map_designLaw_comp_sigmaMap (ν := μ) h]
  refine (maxEPower_anti fun P hP ↦ ?_).trans (maxEPower_map_le _ (by fun_prop))
  obtain ⟨_, ⟨ν, hν, rfl⟩, rfl⟩ := mem_mapNull.1 hP
  have := hΛ ν hν
  exact ⟨ν, hν, (map_designLaw_comp_sigmaMap h).symm⟩

/-- The value of the empty design is `0` when the set of instances is not empty: an e-variable of
the empty table is a constant at most `1`. -/
@[simp]
lemma designValue_zero (μ : α → Measure 𝓧) (hΛ : Λ.Nonempty) : designValue μ Λ 0 = 0 := by
  obtain ⟨ν, hν⟩ := hΛ
  refine le_antisymm (maxEPower_le_iff.2 fun X hX ↦ ?_)
    (maxEPower_nonneg _ fun _ ⟨ν', _, h⟩ ↦ by simp [← h, designLaw_zero])
  have hX1 : ∫⁻ y, X y ∂designLaw ν 0 ≤ 1 := hX.lintegral_le_one ⟨ν, hν, rfl⟩
  rw [designLaw_zero, lintegral_dirac' _ hX.measurable] at hX1
  rw [designLaw_zero, eintegral_dirac' _ hX.measurable.ennreal_log]
  exact ENNReal.log_le_zero_iff.2 hX1

/-- The rate of the designs is nonnegative. -/
lemma designRate_nonneg (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) :
    0 ≤ designRate μ Λ :=
  le_iSup_of_le (0 : α → ℕ) (by simp)

/-- The value of a design per observation is at most the rate of the designs. -/
lemma designValue_div_le_designRate (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧))
    (n : α → ℕ) : designValue μ Λ n / ((∑ a, n a : ℕ) : EReal) ≤ designRate μ Λ :=
  le_iSup (fun n : α → ℕ ↦ designValue μ Λ n / ((∑ a, n a : ℕ) : EReal)) n

/-- The value of a design that is not empty is at most its number of observations times the rate
of the designs. -/
lemma designValue_le_mul_designRate (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧))
    (hn : n ≠ 0) : designValue μ Λ n ≤ ((∑ a, n a : ℕ) : EReal) * designRate μ Λ :=
  (EReal.div_natCast_le_iff (Fintype.sum_pos (pos_iff_ne_zero.2 hn))).1
    (designValue_div_le_designRate μ Λ n)

/-- The rate of the designs is at most `c ≥ 0` if and only if the value of every design that is
not empty is at most its number of observations times `c`. -/
lemma designRate_le_iff {c : EReal} (hc : 0 ≤ c) :
    designRate μ Λ ≤ c ↔
      ∀ n : α → ℕ, n ≠ 0 → designValue μ Λ n ≤ ((∑ a, n a : ℕ) : EReal) * c := by
  refine ⟨fun h n hn ↦ (designValue_le_mul_designRate μ Λ hn).trans
    (mul_le_mul_of_nonneg_left h (by positivity)), fun h ↦ iSup_le fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hc
  exact (EReal.div_natCast_le_iff (Fintype.sum_pos (pos_iff_ne_zero.2 hn))).2 (h n hn)

/-- The rate of the designs is antitone in the set of instances. -/
@[gcongr]
lemma designRate_anti (h : Λ ⊆ Λ') : designRate μ Λ' ≤ designRate μ Λ :=
  iSup_mono fun _ ↦ EReal.div_le_div_right_of_nonneg (by positivity) (designValue_anti h)

/-! ### The entropy bound -/

/-- The value of a design is at most the sum of the relative entropies of its observations from
`μ` to any instance `ν` of `Λ`, `designValue μ Λ n ≤ ∑ a, n a * klDiv (μ a) (ν a)`: this is the
value of the design against the simple null `{ν}`, by the tensorization of the relative entropy
[EVR26, Note 41, Section 2]. -/
lemma designValue_le_sum_mul_klDiv [∀ a, IsProbabilityMeasure (μ a)] (hν : ν ∈ Λ)
    [∀ a, IsProbabilityMeasure (ν a)] (n : α → ℕ) :
    designValue μ Λ n ≤ ((∑ a, (n a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  calc designValue μ Λ n
  _ ≤ maxEPower (designLaw μ n) {designLaw ν n} :=
    maxEPower_anti (Set.singleton_subset_iff.2 ⟨ν, hν, rfl⟩)
  _ = ((∑ a, (n a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
    rw [maxEPower_singleton_eq_klDiv, designLaw_def, designLaw_def, klDiv_pi, Fintype.sum_sigma]
    simp

/-- **The entropy bound.** The value of a design is at most the infimum over the instances `ν` of
`Λ` of the sum of the relative entropies of its observations,
`designValue μ Λ n ≤ ⨅ ν ∈ Λ, ∑ a, n a * klDiv (μ a) (ν a)` [EVR26, Note 41, Section 2]. -/
theorem designValue_le_iInf_sum_mul_klDiv [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (n : α → ℕ) :
    designValue μ Λ n ≤
      ((⨅ ν ∈ Λ, ∑ a, (n a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  simp only [EReal.coe_ennreal_iInf]
  refine le_iInf₂ fun ν hν ↦ ?_
  have := hΛ ν hν
  exact designValue_le_sum_mul_klDiv hν n

/-- **The entropy bound on the rate of the designs.** The rate of the designs is at most the
supremum over the probability vectors `w` of `⨅ ν ∈ Λ, ∑ a, w a * klDiv (μ a) (ν a)`: the
rate is at most the inverse `1 / T*(μ)` of the characteristic time of Garivier and Kaufmann, with
the alternatives `Λ` [EVR26, Note 41, Corollary 2]. -/
theorem designRate_le_iSup_iInf_sum_mul_klDiv [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) :
    designRate μ Λ ≤ ((⨆ w ∈ LMLExplore.simplex α, ⨅ ν ∈ Λ,
      ∑ a, ENNReal.ofReal (w a) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  refine (designRate_le_iff (EReal.coe_ennreal_nonneg _)).2 fun n hn ↦ ?_
  set N := ∑ a, n a
  have hN : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.sum_pos (pos_iff_ne_zero.2 hn)).ne'
  -- the proportions of the design `n`
  set w : α → ℝ := fun a ↦ n a / N
  have hw : w ∈ LMLExplore.simplex α := by
    refine LMLExplore.mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self (by exact_mod_cast hN)]
  have hn_eq (a : α) : (n a : ℝ≥0∞) = N * ENNReal.ofReal (w a) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast (pos_iff_ne_zero.2 hN)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.mul_div_cancel hN (ENNReal.natCast_ne_top N)]
  refine (designValue_le_iInf_sum_mul_klDiv hΛ n).trans ?_
  rw [← ENNReal.toEReal_natCast, ← EReal.coe_ennreal_mul, EReal.coe_ennreal_le_coe_ennreal_iff]
  calc ⨅ ν ∈ Λ, ∑ a, (n a : ℝ≥0∞) * klDiv (μ a) (ν a)
  _ = N * ⨅ ν ∈ Λ, ∑ a, ENNReal.ofReal (w a) * klDiv (μ a) (ν a) := by
    simp_rw [ENNReal.mul_iInf_of_ne hN (ENNReal.natCast_ne_top N), Finset.mul_sum, ← mul_assoc,
      hn_eq]
  _ ≤ N * ⨆ w ∈ LMLExplore.simplex α, ⨅ ν ∈ Λ,
      ∑ a, ENNReal.ofReal (w a) * klDiv (μ a) (ν a) := by
    gcongr
    exact le_iSup₂ (f := fun w _ ↦ ⨅ ν ∈ Λ, ∑ a, ENNReal.ofReal (w a) * klDiv (μ a) (ν a)) w hw

/-! ### Blocks of observations and the bipolar rate -/

/-- The entries of `m` tables of the design `r` are the entries of the table of the design
`m • r`: the entry `⟨a, i⟩` of the table number `k` is the entry `⟨a, finProdFinEquiv (k, i)⟩`.
-/
def designBlockIndexEquiv (r : α → ℕ) (m : ℕ) :
    Fin m × (Σ a, Fin (r a)) ≃ Σ a, Fin ((m • r) a) :=
  (Equiv.prodComm _ _).trans ((Equiv.sigmaProdDistrib _ _).trans
    (Equiv.sigmaCongrRight fun _ ↦ (Equiv.prodComm _ _).trans finProdFinEquiv))

omit [Fintype α] in
/-- The entry `p` of the table number `k` is the entry `⟨p.1, finProdFinEquiv (k, p.2)⟩`. -/
@[simp]
lemma designBlockIndexEquiv_apply (r : α → ℕ) (m : ℕ) (k : Fin m) (p : Σ a, Fin (r a)) :
    designBlockIndexEquiv r m (k, p) = ⟨p.1, finProdFinEquiv (k, p.2)⟩ :=
  (rfl)

omit [Fintype α] in
/-- The entry `q` of the table of `m • r` is an entry of the table number
`(finProdFinEquiv.symm q.2).1`. -/
@[simp]
lemma designBlockIndexEquiv_symm_apply (r : α → ℕ) (m : ℕ) (q : Σ a, Fin ((m • r) a)) :
    (designBlockIndexEquiv r m).symm q =
      ((finProdFinEquiv.symm q.2).1, ⟨q.1, (finProdFinEquiv.symm q.2).2⟩) :=
  (rfl)

/-- `m` tables of the design `r`, as one table of the design `m • r`, through
`designBlockIndexEquiv`. -/
def designBlockEquiv (r : α → ℕ) (m : ℕ) :
    (Fin m → (Σ a, Fin (r a)) → 𝓧) ≃ᵐ ((Σ a, Fin ((m • r) a)) → 𝓧) :=
  (MeasurableEquiv.curry (Fin m) (Σ a, Fin (r a)) 𝓧).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ ↦ 𝓧) (designBlockIndexEquiv r m))

omit [Fintype α] in
/-- The entry `q` of the table of `m • r` built from `m` tables `x` of `r`. -/
@[simp]
lemma designBlockEquiv_apply (r : α → ℕ) (m : ℕ) (x : Fin m → (Σ a, Fin (r a)) → 𝓧)
    (q : Σ a, Fin ((m • r) a)) :
    designBlockEquiv (m𝓧 := m𝓧) r m x q =
      x (finProdFinEquiv.symm q.2).1 ⟨q.1, (finProdFinEquiv.symm q.2).2⟩ := by
  rw [designBlockEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast, cast_eq, designBlockIndexEquiv_symm_apply,
    MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair]

omit [Fintype α] in
/-- The entry `p` of the table number `k` read in a table `y` of `m • r`. -/
@[simp]
lemma designBlockEquiv_symm_apply (r : α → ℕ) (m : ℕ) (y : (Σ a, Fin ((m • r) a)) → 𝓧)
    (k : Fin m) (p : Σ a, Fin (r a)) :
    (designBlockEquiv (m𝓧 := m𝓧) r m).symm y k p = y ⟨p.1, finProdFinEquiv (k, p.2)⟩ :=
  (rfl)

/-- `m` independent tables of the design `r` have the law of the table of the design `m • r`. -/
theorem measurePreserving_designBlockEquiv (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (r : α → ℕ) (m : ℕ) :
    MeasurePreserving (designBlockEquiv (m𝓧 := m𝓧) r m)
      (Measure.pi fun _ : Fin m ↦ designLaw μ r) (designLaw μ (m • r)) := by
  refine ⟨(designBlockEquiv r m).measurable, ?_⟩
  have h_pi : (Measure.pi fun _ : Fin m ↦ designLaw μ r) =
      Measure.infinitePi fun _ : Fin m ↦ Measure.infinitePi fun p : Σ a, Fin (r a) ↦ μ p.1 := by
    simp_rw [designLaw_def, Measure.infinitePi_eq_pi]
  unfold designBlockEquiv
  rw [h_pi, MeasurableEquiv.coe_trans, ← Measure.map_map (MeasurableEquiv.measurable _)
    (MeasurableEquiv.measurable _),
    Measure.infinitePi_map_curry_symm (fun (_ : Fin m) (p : Σ a, Fin (r a)) ↦ μ p.1),
    designLaw_def, ← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_piCongrLeft (fun p : Σ a, Fin ((m • r) a) ↦ μ p.1)
    (designBlockIndexEquiv r m)

/-- **Blocks.** The table of the design `m • r` is made of `m` independent tables of the design
`r`, so its value is the largest expected logarithm of an `m`-sample e-variable for the i.i.d.
null of the laws `designLaw ν r` of the tables of `r`, `ν ∈ Λ` [EVR26, Note 41, Section 1]. -/
theorem maxLogGrowth_designLaw (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (r : α → ℕ) (m : ℕ) :
    maxLogGrowth (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) m = designValue μ Λ (m • r) := by
  rw [maxLogGrowth_def, designValue_def, ← (measurePreserving_designBlockEquiv μ r m).map_eq,
    ← (designBlockEquiv (m𝓧 := m𝓧) r m).maxEPower_map_eq,
    mapNull_sampleNull_image fun ν hν ↦ have := hΛ ν hν
      (measurePreserving_designBlockEquiv ν r m).map_eq]

/-- The bipolar rate of the tables of a design `r` that is not empty is at most the number of
observations of `r` times the rate of the designs [EVR26, Note 41, Section 1]. -/
theorem bipolarRate_designLaw_le (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) {r : α → ℕ} (hr : r ≠ 0) :
    bipolarRate (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) ≤
      ((∑ a, r a : ℕ) : EReal) * designRate μ Λ := by
  refine bipolarRate_le_iff.2 fun m hm ↦ ?_
  rw [maxLogGrowth_designLaw μ hΛ r m]
  refine (designValue_le_mul_designRate μ Λ (smul_ne_zero hm hr)).trans_eq ?_
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, EReal.natCast_mul, mul_assoc]

/-- **The rate of the designs and the bipolar rates of blocks.** The rate of the designs is the
supremum over the designs `r` of the bipolar rate of the tables of `r` against the tables of the
instances of `Λ`, per observation of `r` [EVR26, Note 41, Section 1]. As in `designRate`, the
empty design contributes `0`. -/
theorem designRate_eq_iSup_bipolarRate (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) :
    designRate μ Λ = ⨆ r : α → ℕ,
      bipolarRate (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) / ((∑ a, r a : ℕ) : EReal) := by
  refine le_antisymm (iSup_mono fun n ↦ EReal.div_le_div_right_of_nonneg (by positivity) ?_)
    (iSup_le fun r ↦ ?_)
  · -- the value of a design is the growth of one table of that design
    rw [← one_smul ℕ n, ← maxLogGrowth_designLaw μ hΛ n 1, one_smul]
    exact maxLogGrowth_one_le_bipolarRate _ _
  · rcases eq_or_ne r 0 with rfl | hr
    · simpa using designRate_nonneg μ Λ
    exact (EReal.div_natCast_le_iff (Fintype.sum_pos (pos_iff_ne_zero.2 hr))).2
      (bipolarRate_designLaw_le μ hΛ hr)

/-! ### One source -/

/-- With one source, the value of a design is the largest expected logarithm of an e-variable of
that many observations of the source, for the i.i.d. null of the laws of the source in `Λ`. -/
theorem designValue_unique [Unique α] (μ : α → Measure 𝓧) [∀ a, SigmaFinite (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, SigmaFinite (ν a)) (n : α → ℕ) :
    designValue μ Λ n = maxLogGrowth (μ default) ((fun ν ↦ ν default) '' Λ) (n default) := by
  set e := MeasurableEquiv.piCongrLeft (fun _ : Σ a, Fin (n a) ↦ 𝓧)
    (Equiv.uniqueSigma fun a ↦ Fin (n a)).symm
  have h_map (ν : α → Measure 𝓧) [∀ a, SigmaFinite (ν a)] :
      (Measure.pi fun _ : Fin (n default) ↦ ν default).map e = designLaw ν n :=
    (measurePreserving_piCongrLeft (fun p : Σ a, Fin (n a) ↦ ν p.1)
      (Equiv.uniqueSigma fun a ↦ Fin (n a)).symm).map_eq
  rw [maxLogGrowth_def, designValue_def, ← h_map μ, ← e.maxEPower_map_eq,
    mapNull_sampleNull_image fun ν hν ↦ have := hΛ ν hν; h_map ν]

/-- **One source.** With one source, the rate of the designs is the bipolar rate of the law of the
source against the laws of the source in `Λ` [EVR26, Note 41, Section 1]. -/
theorem designRate_unique [Unique α] (μ : α → Measure 𝓧) [∀ a, SigmaFinite (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, ν a Set.univ ≤ 1) :
    designRate μ Λ = bipolarRate (μ default) ((fun ν ↦ ν default) '' Λ) := by
  have hΛ' (ν : α → Measure 𝓧) (hν : ν ∈ Λ) (a : α) : SigmaFinite (ν a) :=
    have : IsFiniteMeasure (ν a) := ⟨(hΛ ν hν a).trans_lt ENNReal.one_lt_top⟩
    inferInstance
  simp_rw [designRate_def, designValue_unique μ hΛ', Fintype.sum_unique]
  refine le_antisymm (iSup_le fun n ↦ ?_) ((bipolarRate_def _ _).trans_le (iSup_le fun k ↦ ?_))
  · rcases Nat.eq_zero_or_pos (n default) with h | h
    · refine (le_of_eq (by simp [h])).trans (bipolarRate_nonneg (μ default) ?_)
      rintro _ ⟨ν, hν, rfl⟩
      exact hΛ ν hν default
    · exact maxLogGrowth_div_le_bipolarRate _ _ h.ne'
  · exact le_iSup (fun n : α → ℕ ↦ maxLogGrowth (μ default) ((fun ν ↦ ν default) '' Λ)
      (n default) / ((n default : ℕ) : EReal)) fun _ ↦ k + 1

end ProbabilityTheory
