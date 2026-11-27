/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
import LMLExplore.MeasureTheory.Measure.Singletons
import Statlib.Divergence.KullbackLeibler.CondKL

/-!
# Independent coins

For a finite type `ι` and parameters `θ : ι → ℝ`, `prodBernoulli θ` is the law on `ι → Bool` of
`ι` independent coins, the coin `i` showing `true` with probability `θ i`, clamped to `[0, 1]`:
the product of the Bernoulli laws `Ber(true, false, θ i)`. The clamping follows the binary
relative entropy `LMLExplore.klBer`, whose arguments are clamped in the same way, so that the
parameters range over `ι → ℝ` and sets of parameters can be convex.

For `θ` in the cube `[0, 1] ^ ι`, the mass of a point `x` is the product over the coins of `θ i`
or `1 - θ i` according to `x i`, and it is positive for `θ` in the open cube. The relative entropy
between two laws of coins is the sum over the coins of the binary relative entropies of their
parameters (Statlib's `klDiv_pi`). Under `prodBernoulli θ`, the likelihood ratio of
`prodBernoulli ψ` against `prodBernoulli η` has expectation
`∏ i, (ψ i / η i * θ i + (1 - ψ i) / (1 - η i) * (1 - θ i))`, one nonnegative factor per coin.

## Main definitions

* `ProbabilityTheory.prodBernoulli θ`: the law of independent coins with parameters `θ`.

## Main statements

* `ProbabilityTheory.prodBernoulli_singleton`: the mass of a point, for `θ` in `[0, 1] ^ ι`.
* `ProbabilityTheory.prodBernoulli_singleton_ne_zero`: every point is charged for `θ` in
  `(0, 1) ^ ι`, so that `ProbabilityTheory.prodBernoulli_absolutelyContinuous`: `prodBernoulli θ`
  then dominates every law of coins.
* `ProbabilityTheory.klDiv_prodBernoulli`: the relative entropy is the sum of the binary relative
  entropies of the parameters; `ProbabilityTheory.toReal_klDiv_prodBernoulli`: its real value, for
  `θ` in `(0, 1) ^ ι`.
* `ProbabilityTheory.lintegral_prodBernoulli_div_prodBernoulli`: the expectation of a likelihood
  ratio of coins.

## Implementation notes

The definition and its lemmas are adapted from `EValuesResearch/Results/ConvexPieces.lean` (commit
`83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore.
-/

public section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The law of a vector of independent coins, the coin `i` showing `true` with probability
`θ i`, clamped to `[0, 1]`. -/
noncomputable def prodBernoulli (θ : ι → ℝ) : Measure (ι → Bool) :=
  Measure.pi fun i ↦ Ber(true, false, projIcc 0 1 zero_le_one (θ i))

/-- `prodBernoulli θ` is the product of the Bernoulli laws of the clamped parameters. -/
theorem prodBernoulli_def (θ : ι → ℝ) :
    prodBernoulli θ = Measure.pi fun i ↦ Ber(true, false, projIcc 0 1 zero_le_one (θ i)) :=
  (rfl)

instance (θ : ι → ℝ) : IsProbabilityMeasure (prodBernoulli θ) := by
  rw [prodBernoulli_def]
  infer_instance

/-- Clamping the parameters to `[0, 1]` does not change `prodBernoulli`. -/
@[simp]
theorem prodBernoulli_projIcc (θ : ι → ℝ) :
    prodBernoulli (fun i ↦ (projIcc 0 1 zero_le_one (θ i) : ℝ)) = prodBernoulli θ := by
  simp [prodBernoulli_def, projIcc_val]

omit [Fintype ι] in
/-- A real of the form `if x i then θ i else 1 - θ i` is nonnegative for `θ` in the closed
cube. -/
private lemma ite_nonneg_of_mem_Icc {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) (x : ι → Bool)
    (i : ι) : 0 ≤ if x i then θ i else 1 - θ i := by
  have := hθ i (mem_univ i)
  split_ifs <;> linarith [this.1, this.2]

/-- A product of reals of the form `if x i then θ i else 1 - θ i` is nonnegative for `θ` in the
closed cube. -/
private lemma prod_ite_nonneg {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) (x : ι → Bool) :
    0 ≤ ∏ i, if x i then θ i else 1 - θ i :=
  Finset.prod_nonneg fun i _ ↦ ite_nonneg_of_mem_Icc hθ x i

/-- A product of reals of the form `if x i then θ i else 1 - θ i` is positive for `θ` in the open
cube. -/
private lemma prod_ite_pos {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) (x : ι → Bool) :
    0 < ∏ i, if x i then θ i else 1 - θ i := by
  refine Finset.prod_pos fun i _ ↦ ?_
  have := hθ i (mem_univ i)
  split_ifs <;> linarith [this.1, this.2]

/-- The mass of a point under `prodBernoulli θ`, for `θ` in the cube `[0, 1] ^ ι`: the product
over the coins of `θ i` or `1 - θ i` according to the value of the coin. -/
theorem prodBernoulli_singleton {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) (x : ι → Bool) :
    prodBernoulli θ {x} = ENNReal.ofReal (∏ i, if x i then θ i else 1 - θ i) := by
  rw [prodBernoulli_def, Measure.pi_singleton,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ ite_nonneg_of_mem_Icc hθ x i]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hθi : θ i ∈ Icc (0 : ℝ) 1 := hθ i (mem_univ i)
  cases x i
  · rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp)
      (mem_singleton _), ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, projIcc_of_mem _ hθi]
    simp
  · rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (mem_singleton _)
      (by simp), ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, projIcc_of_mem _ hθi]
    simp

/-- Every point has a positive mass under `prodBernoulli θ` for `θ` in the open cube. -/
theorem prodBernoulli_singleton_ne_zero {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (x : ι → Bool) : prodBernoulli θ {x} ≠ 0 := by
  rw [prodBernoulli_singleton (fun i _ ↦ Ioo_subset_Icc_self (hθ i trivial)) x]
  exact (ENNReal.ofReal_pos.2 (prod_ite_pos hθ x)).ne'

/-- The laws of coins with parameters in the open cube dominate every law of coins. -/
theorem prodBernoulli_absolutelyContinuous (ψ : ι → ℝ) {θ : ι → ℝ}
    (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) : prodBernoulli ψ ≪ prodBernoulli θ :=
  Measure.absolutelyContinuous_of_forall_singleton_pos fun x ↦
    pos_iff_ne_zero.2 (prodBernoulli_singleton_ne_zero hθ x)

/-- **The relative entropy between laws of coins** is the sum over the coins of the binary
relative entropies of their parameters. -/
theorem klDiv_prodBernoulli (ψ θ : ι → ℝ) :
    klDiv (prodBernoulli ψ) (prodBernoulli θ) = ∑ i, LMLExplore.klBer (ψ i) (θ i) := by
  rw [prodBernoulli_def, prodBernoulli_def, klDiv_pi]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LMLExplore.klDiv_bernoulliMeasure (by decide : true ≠ false), LMLExplore.klBer_projIcc]

/-- The relative entropy from `prodBernoulli ψ` to `prodBernoulli θ` is finite for `θ` in the open
cube. -/
theorem klDiv_prodBernoulli_ne_top (ψ : ι → ℝ) {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) :
    klDiv (prodBernoulli ψ) (prodBernoulli θ) ≠ ∞ := by
  rw [klDiv_prodBernoulli]
  exact ENNReal.sum_ne_top.2 fun i _ ↦ LMLExplore.klBer_ne_top (hθ i (mem_univ i))

/-- For `θ` in the open cube, the real value of the relative entropy from `prodBernoulli ψ` to
`prodBernoulli θ` is the sum of the real binary relative entropies `klBerReal`, with `ψ` clamped
to `[0, 1]`. -/
theorem toReal_klDiv_prodBernoulli (ψ : ι → ℝ) {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) :
    (klDiv (prodBernoulli ψ) (prodBernoulli θ)).toReal =
      ∑ i, klBerReal (projIcc 0 1 zero_le_one (ψ i)) (θ i) := by
  have hθ' (i : ι) : θ i ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hθ i (mem_univ i))
  rw [← prodBernoulli_projIcc ψ, klDiv_prodBernoulli,
    ENNReal.toReal_sum fun i _ ↦ LMLExplore.klBer_ne_top (hθ i (mem_univ i))]
  exact Finset.sum_congr rfl fun i _ ↦ LMLExplore.toReal_klBer
    (projIcc 0 1 zero_le_one (ψ i)).property (hθ' i) (LMLExplore.klBer_ne_top (hθ i (mem_univ i)))

omit [Fintype ι] in
/-- The two terms `ψ i / η i * θ i` and `(1 - ψ i) / (1 - η i) * (1 - θ i)` of the expectation of
the likelihood ratio of one coin are nonnegative, for `ψ` and `θ` in the closed cube and `η` in
the open cube. -/
private lemma ite_div_mul_nonneg {ψ η θ : ι → ℝ} (hψ : ψ ∈ univ.pi fun _ ↦ Icc 0 1)
    (hη : η ∈ univ.pi fun _ ↦ Ioo 0 1) (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) (i : ι) (b : Bool) :
    0 ≤ if b then ψ i / η i * θ i else (1 - ψ i) / (1 - η i) * (1 - θ i) := by
  have h1 := hψ i (mem_univ i)
  have h2 := hη i (mem_univ i)
  have h3 := hθ i (mem_univ i)
  split_ifs
  · exact mul_nonneg (div_nonneg h1.1 h2.1.le) h3.1
  · exact mul_nonneg (div_nonneg (by linarith [h1.2]) (by linarith [h2.2])) (by linarith [h3.2])

/-- **The expectation of a likelihood ratio of coins.** Under `prodBernoulli θ`, the likelihood
ratio of `prodBernoulli ψ` against `prodBernoulli η` has expectation
`∏ i, (ψ i / η i * θ i + (1 - ψ i) / (1 - η i) * (1 - θ i))`, one nonnegative factor per coin,
for `ψ` and `θ` in the closed cube and `η` in the open cube. -/
theorem lintegral_prodBernoulli_div_prodBernoulli {ψ η θ : ι → ℝ}
    (hψ : ψ ∈ univ.pi fun _ ↦ Icc 0 1) (hη : η ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) :
    ∫⁻ x, prodBernoulli ψ {x} / prodBernoulli η {x} ∂prodBernoulli θ =
      ∏ i, ENNReal.ofReal (ψ i / η i * θ i + (1 - ψ i) / (1 - η i) * (1 - θ i)) := by
  classical
  have hη' : η ∈ univ.pi fun _ ↦ Icc 0 1 := fun i _ ↦ Ioo_subset_Icc_self (hη i trivial)
  -- each factor is the sum over the two values of the coin of nonnegative terms
  have hb (i : ι) : ψ i / η i * θ i + (1 - ψ i) / (1 - η i) * (1 - θ i) =
      ∑ b : Bool, if b then ψ i / η i * θ i else (1 - ψ i) / (1 - η i) * (1 - θ i) := by
    simp
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hb i ▸
    Finset.sum_nonneg fun b _ ↦ ite_div_mul_nonneg hψ hη hθ i b, lintegral_fintype]
  simp_rw [prodBernoulli_singleton hψ, prodBernoulli_singleton hη', prodBernoulli_singleton hθ]
  -- each term is the product over the coins of the terms of one coin
  have hterm (x : ι → Bool) :
      ENNReal.ofReal (∏ i, if x i then ψ i else 1 - ψ i) /
          ENNReal.ofReal (∏ i, if x i then η i else 1 - η i) *
        ENNReal.ofReal (∏ i, if x i then θ i else 1 - θ i) =
      ENNReal.ofReal (∏ i, if x i then ψ i / η i * θ i
        else (1 - ψ i) / (1 - η i) * (1 - θ i)) := by
    rw [← ENNReal.ofReal_div_of_pos (prod_ite_pos hη x),
      ← ENNReal.ofReal_mul (div_nonneg (prod_ite_nonneg hψ x) (prod_ite_nonneg hη' x)),
      ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs <;> rfl
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦
    Finset.prod_nonneg fun i _ ↦ ite_div_mul_nonneg hψ hη hθ i (x i)]
  -- the sum over the points of the products is the product of the sums over the coins
  congr 1
  rw [Finset.prod_congr rfl fun i _ ↦ hb i, Finset.prod_univ_sum, Fintype.piFinset_univ]

end ProbabilityTheory
