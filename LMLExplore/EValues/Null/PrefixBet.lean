/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.ProductMeasure.Blocks

/-!
# Bets on the first observations of an i.i.d. sequence

The observations are the coordinates of `ℕ → 𝓧`, and the null is the i.i.d. null `iidNull S₁` of a
set `S₁` of laws on `𝓧`. A bet on the first `n` observations is an e-variable `f` for `iidNull S₁`
that is a function of the first `n` coordinates, `DependsOn f (Set.Iio n)`: its expectation is at
most `1` under the i.i.d. law of every member of the null. The wealth of a gambler who bets on
blocks of observations [RR26, Definitions 2.3–2.5] is built from such bets by a few operations,
which this file shows produce bets again:

* **skipping** the first `n` observations: `g ∘ (shift 𝓧)^[n]`, a bet read on the observations
  after the first `n`, whose law under an i.i.d. law is that of `g`;
* **concatenation** with a shifted continuation: `f ω * g ((shift 𝓧)^[n] ω)`, a bet `f` on the
  first `n` observations followed by a bet `g` on the next ones, whose expectations multiply since
  the two are independent under an i.i.d. law;
* **mixtures** `∑ i, w i * f i`, countable or finite, with weights of sum at most `1`
  (`ProbabilityTheory.isEVar_tsum_mul`, `ProbabilityTheory.isEVar_finsetSum_mul`, for any null);
* **parsing into blocks**: the product `seqBlockProd m V k` of a bet `V` on `m` observations over
  the first `k` consecutive blocks of `m` observations.

Each operation also keeps track of the observations the bet has seen:
`MeasureTheory.dependsOn_comp_shift_iterate`, `MeasureTheory.dependsOn_mul_comp_shift_iterate`
and `MeasureTheory.dependsOn_seqBlockProd`. A function of the first `n` observations is exactly a
function measurable for the time `n` of the filtration `Filtration.piLT` of the observations
(`Filtration.measurable_piLT_of_dependsOn`, `Measurable.dependsOn_of_piLT`), so a sequence of
bets, the `n`-th on the first `n` observations, is adapted to that filtration.

## Main statements

* `ProbabilityTheory.IsEVar.comp_shift_iterate`: a bet read after the first `n` observations is a
  bet.
* `ProbabilityTheory.IsEVar.mul_comp_shift_iterate`: the concatenation of a bet on the first `n`
  observations with a bet on the next ones is a bet.
* `ProbabilityTheory.isEVar_seqBlockProd`: the product over blocks of a bet on `m` observations,
  for the null `sampleNull S₁ m` of `m`-samples, is a bet for the i.i.d. null.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1,
  Definitions 2.3–2.5.
-/

public section

open MeasureTheory
open TauCeti.Probability (shift measurable_shift_iterate)
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)} {f g : (ℕ → 𝓧) → ℝ≥0∞}

/-- **Skipping observations.** An e-variable for the i.i.d. null, read on the observations after
the first `n`, is an e-variable for the i.i.d. null, which is invariant under the shift
(`ProbabilityTheory.mapNull_shift_iterate_iidNull`). -/
theorem IsEVar.comp_shift_iterate (hg : IsEVar g (iidNull S₁)) (n : ℕ) :
    IsEVar (fun ω ↦ g ((shift 𝓧)^[n] ω)) (iidNull S₁) :=
  (isEVar_mapNull_iff (measurable_shift_iterate n) hg.measurable).1
    (by rwa [mapNull_shift_iterate_iidNull])

/-- **Concatenation of bets.** For an e-variable `f` for the i.i.d. null that is a function of the
first `n` observations and an e-variable `g` for the i.i.d. null, the bet `f` on the first `n`
observations followed by the bet `g` on the next ones, `ω ↦ f ω * g ((shift 𝓧)^[n] ω)`, is an
e-variable for the i.i.d. null. If `g` is a function of the first `m` observations, the
concatenation is a function of the first `n + m` (`MeasureTheory.dependsOn_mul_comp_shift_iterate`).
-/
theorem IsEVar.mul_comp_shift_iterate {n : ℕ} (hf : IsEVar f (iidNull S₁))
    (hfn : DependsOn f (Set.Iio n)) (hg : IsEVar g (iidNull S₁)) :
    IsEVar (fun ω ↦ f ω * g ((shift 𝓧)^[n] ω)) (iidNull S₁) :=
  isEVar_iidNull_iff.2 ⟨hf.measurable.mul (hg.measurable.comp (measurable_shift_iterate n)),
    fun P hP _ ↦ by
      rw [lintegral_mul_comp_shift_iterate P hf.measurable hfn hg.measurable]
      exact mul_le_one' (hf.lintegral_le_one (infinitePi_mem_iidNull hP))
        (hg.lintegral_le_one (infinitePi_mem_iidNull hP))⟩

/-- **Parsing into blocks.** For an e-variable `V` of `m` observations for the null
`sampleNull S₁ m` of `m`-samples, its product `seqBlockProd m V k` over the first `k` consecutive
blocks of `m` observations is an e-variable for the i.i.d. null, a function of the first `k * m`
observations (`MeasureTheory.dependsOn_seqBlockProd`). -/
theorem isEVar_seqBlockProd {m : ℕ} {V : (Fin m → 𝓧) → ℝ≥0∞}
    (hV : IsEVar V (sampleNull S₁ m)) (k : ℕ) :
    IsEVar (seqBlockProd m V k) (iidNull S₁) :=
  isEVar_iidNull_iff.2 ⟨measurable_seqBlockProd hV.measurable k, fun P hP _ ↦ by
    rw [lintegral_seqBlockProd_const P hV.measurable]
    exact pow_le_one₀ (by positivity) (hV.lintegral_le_one (pi_mem_sampleNull hP))⟩

end ProbabilityTheory
