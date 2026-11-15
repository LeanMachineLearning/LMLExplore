/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing
public import Mathlib.Probability.Process.Filtration
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import TauCeti.Probability.Martingale.Reverse
import LMLExplore.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.Probability.Exchangeability.Law
import LMLExplore.Probability.Martingale.Upcrossing
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Statlib.ForMathlib.Probability.Process.Filtration
import TauCeti.Probability.Martingale.Crossings.Pathwise
import TauCeti.Probability.Martingale.MaximalInequality.Basic

/-!
# Maximal and upcrossing inequalities for the sample means of an exchangeable sequence

Let `μ` be an exchangeable law of a sequence `X₀, X₁, …` of real random variables (a probability
measure on `ℕ → ℝ` invariant under the permutations of the coordinates, Tau Ceti's
`TauCeti.Probability.ExchangeableLaw`), for instance the law `Measure.infinitePi fun _ ↦ P` of an
i.i.d. sequence, with `X₀` integrable of mean `m`. Let `Aₙ = (X₀ + ⋯ + Xₙ) / (n + 1)`. For a
horizon `N`, the sample means read backwards, `k ↦ A_{N - k}`, form a martingale for the
σ-algebras of the events that are symmetric in the first `N - k + 1` coordinates. Doob's
inequalities for this martingale give two bounds that hold uniformly in the horizon:

* for every `m' : ℝ`, the sample means come at distance at least `L` from `m'` with probability
  at most `𝔼|X₀ - m'| / L`;
* the expected number of upcrossings of `[a, b]` by the sample means is at most
  `𝔼|X₀ - m| / (b - a)`.

The second bound does not depend on the position of `[a, b]` relative to `m`. It rests on Doob's
upcrossing inequality with the initial term,
`MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_posPart_sub`, which bounds
the expected upcrossings of `[-b, -a]` by the negated reversed means by
`𝔼(b - X₀)⁺ - (b - m)⁺ ≤ 𝔼|X₀ - m|`, and on Tau Ceti's comparison of the upcrossings of a process
with those of its negated time reversal.

## Main definitions

* `ProbabilityTheory.prefixExchangeableSigma α n`: the σ-algebra of the events on `ℕ → α` that are
  symmetric in the first `n + 1` coordinates.
* `ProbabilityTheory.sampleMean n`: the mean `(ω 0 + ⋯ + ω n) / (n + 1)` of the coordinates
  `0, …, n` of a sequence.

## Main statements

* `ProbabilityTheory.martingale_sampleMean_rev`: the sample means read backwards from a horizon
  form a martingale for the reverse filtration of the symmetric events.
* `ProbabilityTheory.mul_measure_exists_le_abs_sampleMean_sub_le`: the maximal inequality.
* `ProbabilityTheory.mul_lintegral_upcrossings_sampleMean_le`: the upcrossing inequality.

## Implementation notes

The argument is that of [EVR26, Note 16], for i.i.d. sequences there. The proofs are adapted from
`EValuesResearch/Results/CompositeSLLN.lean` (commit `7695891`) in the paper project
`RemyDegenne/evalues_research`, and stated here for exchangeable laws; its reverse-martingale
helpers are replaced by Tau Ceti's `MeasureTheory.revFiltration` and `MeasureTheory.revProcess`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {μ : Measure (ℕ → ℝ)}

/-! ### Symmetric events -/

/-- The σ-algebra of the measurable events on `ℕ → α` that are invariant under the swap of the
coordinates `0` and `i` for every `i ≤ n`. These swaps generate the permutations of the first
`n + 1` coordinates, so these are the events symmetric in the first `n + 1` coordinates. -/
@[instance_reducible]
def prefixExchangeableSigma (α : Type*) [MeasurableSpace α] (n : ℕ) : MeasurableSpace (ℕ → α) :=
  ⨅ i ≤ n, MeasurableSpace.invariants (permReindex (α := α) (Equiv.swap 0 i))

variable {α : Type*} [MeasurableSpace α]

/-- An event is symmetric in the first `n + 1` coordinates when it is measurable and invariant
under the swaps of the coordinates `0` and `i ≤ n`. -/
theorem measurableSet_prefixExchangeableSigma_iff {n : ℕ} {s : Set (ℕ → α)} :
    MeasurableSet[prefixExchangeableSigma α n] s ↔
      ∀ i ≤ n, MeasurableSet s ∧ permReindex (Equiv.swap 0 i) ⁻¹' s = s := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants]

variable (α) in
/-- Fewer events are symmetric in more coordinates. -/
theorem prefixExchangeableSigma_anti : Antitone (prefixExchangeableSigma α) := fun _ _ hnm ↦
  biInf_mono fun _ hi ↦ hi.trans hnm

variable (α) in
/-- The symmetric events are measurable. -/
theorem prefixExchangeableSigma_le (n : ℕ) : prefixExchangeableSigma α n ≤ MeasurableSpace.pi :=
  (iInf₂_le 0 (Nat.zero_le n)).trans (MeasurableSpace.invariants_le _)

/-! ### The reverse martingale of the sample means -/

/-- The mean `(ω 0 + ⋯ + ω n) / (n + 1)` of the coordinates `0, …, n` of a sequence. -/
noncomputable def sampleMean (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1)

/-- The defining formula of the sample mean. -/
theorem sampleMean_def (n : ℕ) (ω : ℕ → ℝ) :
    sampleMean n ω = (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1) := by
  rw [sampleMean]

/-- The mean of the coordinate `0` alone is that coordinate. -/
@[simp]
theorem sampleMean_zero (ω : ℕ → ℝ) : sampleMean 0 ω = ω 0 := by simp [sampleMean]

/-- The sample means are measurable. -/
@[fun_prop]
theorem measurable_sampleMean (n : ℕ) : Measurable (sampleMean n) := by
  unfold sampleMean
  fun_prop

/-- The mean of the coordinates `0, …, n` is measurable at time `n` for the canonical filtration
of `ℕ → ℝ`. -/
theorem measurable_piLE_sampleMean (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n] (sampleMean n) := by
  simp only [funext (sampleMean_def n)]
  refine Measurable.div_const (Finset.measurable_sum _ fun i hi ↦ ?_) _
  exact Filtration.measurable_piLE_apply (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-- The sample means are adapted to the canonical filtration of `ℕ → ℝ`. -/
theorem stronglyAdapted_piLE_sampleMean :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ ↦ ℝ)) sampleMean :=
  fun n ↦ (measurable_piLE_sampleMean n).stronglyMeasurable

/-- The mean of the coordinates `0, …, n` is invariant under the swap of the coordinates `0` and
`i ≤ n`. -/
theorem sampleMean_permReindex_swap {n i : ℕ} (hi : i ≤ n) (ω : ℕ → ℝ) :
    sampleMean n (permReindex (Equiv.swap 0 i) ω) = sampleMean n ω := by
  simp only [sampleMean, permReindex_apply]
  congr 1
  refine Equiv.Perm.sum_comp (Equiv.swap 0 i) (Finset.range (n + 1)) ω fun j hj ↦ ?_
  simp only [Set.mem_ofPred_eq] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra! h
  exact hj (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))

/-- The mean of the coordinates `0, …, n` is measurable for the events symmetric in them. -/
theorem measurable_prefixExchangeableSigma_sampleMean (n : ℕ) :
    Measurable[prefixExchangeableSigma ℝ n] (sampleMean n) := by
  intro t ht
  rw [measurableSet_prefixExchangeableSigma_iff]
  intro i hi
  refine ⟨measurable_sampleMean n ht, ?_⟩
  ext ω
  simp only [Set.mem_preimage, sampleMean_permReindex_swap hi]

/-- The sample means of an exchangeable sequence with an integrable first coordinate are
integrable. -/
theorem integrable_sampleMean (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    (n : ℕ) : Integrable (sampleMean n) μ :=
  (integrable_finsetSum _ fun i _ ↦ hμ.integrable_comp_eval (f := fun x ↦ x) hint i).div_const _

/-- On an event symmetric in the first `n + 1` coordinates, the integral of the mean of the
coordinates `0, …, m`, for `m ≤ n`, is that of the coordinate `0`. -/
theorem setIntegral_sampleMean_eq (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    {n m : ℕ} (hmn : m ≤ n) {s : Set (ℕ → ℝ)} (hs : MeasurableSet[prefixExchangeableSigma ℝ n] s) :
    ∫ ω in s, sampleMean m ω ∂μ = ∫ ω in s, ω 0 ∂μ := by
  rw [measurableSet_prefixExchangeableSigma_iff] at hs
  have h (i : ℕ) (hi : i ∈ Finset.range (m + 1)) : ∫ ω in s, ω i ∂μ = ∫ ω in s, ω 0 ∂μ :=
    hμ.setIntegral_comp_eval_eq_of_preimage_eq (fun x ↦ x)
      (hs i ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hmn)).2
  have hint' (i : ℕ) : Integrable (fun ω : ℕ → ℝ ↦ ω i) (μ.restrict s) :=
    (hμ.integrable_comp_eval (f := fun x ↦ x) hint i).restrict
  simp only [sampleMean, integral_div, integral_finsetSum _ fun i _ ↦ hint' i,
    Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- The integral of a sample mean is that of the first coordinate. -/
theorem integral_sampleMean (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    (n : ℕ) : ∫ ω, sampleMean n ω ∂μ = ∫ ω, ω 0 ∂μ := by
  simpa using setIntegral_sampleMean_eq hμ hint le_rfl
    (MeasurableSet.univ (m := prefixExchangeableSigma ℝ n))

/-- **The reverse martingale of the sample means.** Under an exchangeable law with an integrable
first coordinate, the sample means read backwards from the horizon `N`, `k ↦ A_{N - k}`, form a
martingale for the reverse filtration of the events symmetric in the first `N - k + 1`
coordinates. -/
theorem martingale_sampleMean_rev [IsFiniteMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (N : ℕ) :
    Martingale (fun k ↦ sampleMean (N - k))
      (revFiltration (prefixExchangeableSigma ℝ) (prefixExchangeableSigma_anti ℝ)
        (prefixExchangeableSigma_le ℝ) N) μ := by
  refine martingale_of_setIntegral_eq_succ (fun k ↦ ?_) (fun k ↦ integrable_sampleMean hμ hint _)
    fun k s hs ↦ ?_
  · rw [revFiltration_apply]
    exact (measurable_prefixExchangeableSigma_sampleMean (N - k)).stronglyMeasurable
  · rw [revFiltration_apply] at hs
    rw [setIntegral_sampleMean_eq hμ hint le_rfl hs,
      setIntegral_sampleMean_eq hμ hint (by omega) hs]

/-! ### The maximal inequality -/

/-- **Maximal inequality for the sample means of an exchangeable sequence**: if the first
coordinate is integrable, then for every `m : ℝ` the probability that some sample mean is at
distance at least `L` from `m` is at most `∫ |X₀ - m| / L`. -/
theorem mul_measure_exists_le_abs_sampleMean_sub_le [IsFiniteMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (m : ℝ) (L : ℝ≥0) :
    L * μ {ω | ∃ n : ℕ, (L : ℝ) ≤ |sampleMean n ω - m|} ≤
      ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) := by
  -- the event is the increasing union of the events up to the horizons `N`
  have hset : {ω | ∃ n : ℕ, (L : ℝ) ≤ |sampleMean n ω - m|} =
      ⋃ N, {ω | ∃ n ≤ N, (L : ℝ) ≤ |sampleMean n ω - m|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  have hmono : Monotone fun N ↦ {ω | ∃ n ≤ N, (L : ℝ) ≤ |sampleMean n ω - m|} :=
    fun _ _ h _ ⟨n, hn, hn'⟩ ↦ ⟨n, hn.trans h, hn'⟩
  rw [hset, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun N ↦ ?_
  -- Doob's maximal inequality for the submartingale `k ↦ |A_{N - k} - m|`
  have hM := ((martingale_sampleMean_rev hμ hint N).sub (martingale_const _ _ m)).submartingale_norm
  have h : L * μ {ω | ∃ k ∈ Finset.range (N + 1), (L : ℝ) ≤ |sampleMean (N - k) ω - m|} ≤
      ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) := by
    simpa [Real.norm_eq_abs, sampleMean_zero] using hM.mul_measure_exists_mem_le_le
      (fun _ _ ↦ norm_nonneg _) L (F := Finset.range (N + 1)) (T := N)
      fun _ ht ↦ Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) h
  rintro ω ⟨n, hn, hL⟩
  exact ⟨N - n, Finset.mem_range.2 (by omega), by rwa [Nat.sub_sub_self hn]⟩

/-! ### The upcrossing inequality -/

/-- The upcrossings of `[a, b]` by the sample means before `N` are upcrossings of `[-b, -a]` by
the negated sample means read backwards from the horizon `N`, before `N + 1`. -/
private lemma upcrossingsBefore_sampleMean_le {a b : ℝ} (hab : a < b) (N : ℕ) (ω : ℕ → ℝ) :
    upcrossingsBefore a b sampleMean N ω ≤
      upcrossingsBefore (-b) (-a) (-fun k ↦ sampleMean (N - k)) (N + 1) ω := by
  refine (upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ sampleMean a b hab N
    ω).trans_eq ?_
  refine upcrossingsBefore_succ_congr fun k hk ↦ ?_
  simp only [Pi.neg_apply, revProcess_apply_of_le _ hk]

/-- **Upcrossing inequality for the sample means of an exchangeable sequence**: if the first
coordinate `X₀` is integrable, of mean `m`, the expected number of upcrossings of `[a, b]` by the
sample means is at most `∫ |X₀ - m| / (b - a)`. -/
theorem mul_lintegral_upcrossings_sampleMean_le [IsProbabilityMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (a b : ℝ) :
    ENNReal.ofReal (b - a) * ∫⁻ ω, upcrossings a b sampleMean ω ∂μ ≤
      ENNReal.ofReal (∫ ω, |ω 0 - ∫ ω', ω' 0 ∂μ| ∂μ) := by
  rcases le_or_gt b a with hba | hab
  · simp [ENNReal.ofReal_of_nonpos (sub_nonpos.2 hba)]
  set m := ∫ ω, ω 0 ∂μ
  -- monotone convergence in the horizon
  have hadapted : StronglyAdapted (Filtration.const ℕ MeasurableSpace.pi le_rfl) sampleMean :=
    fun n ↦ (measurable_sampleMean n).stronglyMeasurable
  simp only [upcrossings]
  rw [lintegral_iSup (f := fun N ω ↦ (upcrossingsBefore a b sampleMean N ω : ℝ≥0∞))
    (fun N ↦ measurable_from_top.comp (hadapted.measurable_upcrossingsBefore hab))
    (fun _ _ h ω ↦ Nat.cast_le.2 (upcrossingsBefore_mono hab h ω)), ENNReal.mul_iSup]
  refine iSup_le fun N ↦ ?_
  -- Doob's upcrossing inequality for the negated reversed means
  have hM := (martingale_sampleMean_rev hμ hint N).neg
  have hint' := hM.stronglyAdapted.integrable_upcrossingsBefore (μ := μ) (N := N + 1)
    (neg_lt_neg hab)
  have hDoob := hM.submartingale.mul_integral_upcrossingsBefore_le_integral_posPart_sub
    (-b) (-a) (N + 1)
  rw [neg_sub_neg] at hDoob
  simp only [Pi.neg_apply, Nat.sub_eq_zero_of_le (Nat.le_succ N), Nat.sub_zero, sampleMean_zero,
    sub_neg_eq_add, neg_add_eq_sub] at hDoob
  -- the expectation at time `0` is at least `(b - m)⁺`, by convexity
  have h₁ : (b - m)⁺ ≤ ∫ ω, (b - sampleMean N ω)⁺ ∂μ := by
    have hm : ∫ ω, sampleMean N ω ∂μ = m := integral_sampleMean hμ hint N
    rw [← hm, ← integral_const_sub b (integrable_sampleMean hμ hint N)]
    exact posPart_integral_le_integral_posPart _
  -- `𝔼(b - X₀)⁺ - (b - m)⁺ ≤ 𝔼|X₀ - m|`, the positive part being `1`-Lipschitz
  have h₂ : ∫ ω, (b - ω 0)⁺ ∂μ - (b - m)⁺ ≤ ∫ ω, |ω 0 - m| ∂μ := by
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm m] using
      integral_posPart_sub_posPart_le (f := fun ω : ℕ → ℝ ↦ b - ω 0) ((integrable_const b).sub hint)
        (b - m)
  calc ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b sampleMean N ω : ℝ≥0∞) ∂μ
      ≤ ENNReal.ofReal (b - a) * ∫⁻ ω,
          (upcrossingsBefore (-b) (-a) (-fun k ↦ sampleMean (N - k)) (N + 1) ω : ℝ≥0∞) ∂μ := by
        gcongr with ω
        exact_mod_cast upcrossingsBefore_sampleMean_le hab N ω
    _ = ENNReal.ofReal ((b - a) * ∫ ω,
          (upcrossingsBefore (-b) (-a) (-fun k ↦ sampleMean (N - k)) (N + 1) ω : ℝ) ∂μ) := by
        rw [ENNReal.ofReal_mul (sub_nonneg.2 hab.le),
          ofReal_integral_eq_lintegral_ofReal hint' (.of_forall fun ω ↦ Nat.cast_nonneg _)]
        simp
    _ ≤ ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) :=
        ENNReal.ofReal_le_ofReal (by linarith)

end ProbabilityTheory
