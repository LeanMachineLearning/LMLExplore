/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
import LMLExplore.Probability.Martingale.Upcrossing
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import TauCeti.Probability.Martingale.Crossings.Pathwise
import TauCeti.Probability.Martingale.MaximalInequality.Basic
import TauCeti.Probability.Martingale.Reverse

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

## Main statements

* `ProbabilityTheory.mul_measure_exists_le_abs_sum_div_sub_le`: the maximal inequality.
* `ProbabilityTheory.mul_lintegral_upcrossings_sum_div_le`: the upcrossing inequality.
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {μ : Measure (ℕ → ℝ)}

/-! ### Swaps of coordinates and symmetric events -/

/-- The swap of the coordinates `0` and `i` of a sequence. -/
private abbrev swapAt (i : ℕ) : (ℕ → ℝ) → ℕ → ℝ := permReindex (Equiv.swap 0 i)

/-- Swapping the coordinates `0` and `i` twice gives back the sequence. -/
private lemma swapAt_involutive (i : ℕ) : Function.Involutive (swapAt i) := fun ω ↦ by
  ext j
  simp

/-- On a set invariant under the swap of the coordinates `0` and `i`, the coordinates `0` and `i`
of an exchangeable sequence have the same integral. -/
private lemma setIntegral_apply_eq_of_preimage_swapAt_eq (hμ : ExchangeableLaw μ) {i : ℕ}
    {s : Set (ℕ → ℝ)} (hs : swapAt i ⁻¹' s = s) :
    ∫ ω in s, ω i ∂μ = ∫ ω in s, ω 0 ∂μ := by
  have h := (hμ.measurePreserving_permReindex (Equiv.swap 0 i)).setIntegral_preimage_emb
    (MeasurableEquiv.ofInvolutive _ (swapAt_involutive i)
      (measurable_reindex _)).measurableEmbedding (fun ω ↦ ω 0) s
  rw [hs] at h
  simpa using h

/-- The coordinates of an exchangeable sequence whose first coordinate is integrable are
integrable. -/
private lemma integrable_apply (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    (i : ℕ) : Integrable (fun ω : ℕ → ℝ ↦ ω i) μ := by
  simpa [Function.comp_def] using
    ((hμ.measurePreserving_permReindex (Equiv.swap 0 i)).integrable_comp
      hint.aestronglyMeasurable).2 hint

/-- The σ-algebra of the measurable events that are invariant under the swap of the coordinates
`0` and `i` for every `i ≤ n`, that is, symmetric in the first `n + 1` coordinates. -/
@[instance_reducible]
private def symmLE (n : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨅ i ≤ n, MeasurableSpace.invariants (swapAt i)

/-- An event is symmetric in the first `n + 1` coordinates when it is measurable and invariant
under the swaps of the coordinates `0` and `i ≤ n`. -/
private lemma measurableSet_symmLE_iff {n : ℕ} {s : Set (ℕ → ℝ)} :
    MeasurableSet[symmLE n] s ↔ ∀ i ≤ n, MeasurableSet s ∧ swapAt i ⁻¹' s = s := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants]

/-- Fewer events are symmetric in more coordinates. -/
private lemma symmLE_anti : Antitone symmLE := fun _ _ hnm ↦
  biInf_mono fun _ hi ↦ hi.trans hnm

/-- The symmetric events are measurable. -/
private lemma symmLE_le (n : ℕ) : symmLE n ≤ MeasurableSpace.pi :=
  (iInf₂_le 0 (Nat.zero_le n)).trans (MeasurableSpace.invariants_le _)

/-! ### The reverse martingale of the sample means -/

/-- The mean of the coordinates `0, …, n` of a sequence. -/
private noncomputable def smean (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1)

/-- The mean of the coordinate `0` alone is that coordinate. -/
private lemma smean_zero (ω : ℕ → ℝ) : smean 0 ω = ω 0 := by simp [smean]

/-- The sample means are measurable. -/
private lemma measurable_smean (n : ℕ) : Measurable (smean n) := by
  unfold smean
  fun_prop

/-- The mean of the coordinates `0, …, n` is invariant under the swap of the coordinates `0` and
`i ≤ n`. -/
private lemma smean_swapAt {n i : ℕ} (hi : i ≤ n) (ω : ℕ → ℝ) :
    smean n (swapAt i ω) = smean n ω := by
  simp only [smean, swapAt, permReindex_apply]
  congr 1
  refine Equiv.Perm.sum_comp (Equiv.swap 0 i) (Finset.range (n + 1)) ω fun j hj ↦ ?_
  simp only [Set.mem_ofPred_eq] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra! h
  exact hj (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))

/-- The mean of the coordinates `0, …, n` is measurable for the events symmetric in them. -/
private lemma measurable_symmLE_smean (n : ℕ) : Measurable[symmLE n] (smean n) := by
  intro t ht
  rw [measurableSet_symmLE_iff]
  intro i hi
  refine ⟨measurable_smean n ht, ?_⟩
  ext ω
  simp only [Set.mem_preimage, smean_swapAt hi]

/-- The sample means of an exchangeable sequence with an integrable first coordinate are
integrable. -/
private lemma integrable_smean (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    (n : ℕ) : Integrable (smean n) μ :=
  (integrable_finsetSum _ fun i _ ↦ integrable_apply hμ hint i).div_const _

/-- On an event symmetric in the first `n + 1` coordinates, the integral of the mean of the
coordinates `0, …, m`, for `m ≤ n`, is that of the coordinate `0`. -/
private lemma setIntegral_smean_eq (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    {n m : ℕ} (hmn : m ≤ n) {s : Set (ℕ → ℝ)} (hs : MeasurableSet[symmLE n] s) :
    ∫ ω in s, smean m ω ∂μ = ∫ ω in s, ω 0 ∂μ := by
  rw [measurableSet_symmLE_iff] at hs
  unfold smean
  rw [integral_div, integral_finsetSum _ fun i _ ↦ (integrable_apply hμ hint i).integrableOn,
    Finset.sum_congr rfl fun i hi ↦ setIntegral_apply_eq_of_preimage_swapAt_eq hμ
      (hs i ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hmn)).2,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- The integral of a sample mean is that of the first coordinate. -/
private lemma integral_smean (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ)
    (n : ℕ) : ∫ ω, smean n ω ∂μ = ∫ ω, ω 0 ∂μ := by
  simpa using setIntegral_smean_eq hμ hint le_rfl (MeasurableSet.univ (m := symmLE n))

/-- Under an exchangeable law with an integrable first coordinate, the sample means read backwards
from the horizon `N` form a martingale. -/
private lemma martingale_smean_rev [IsFiniteMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (N : ℕ) :
    Martingale (fun k ↦ smean (N - k)) (revFiltration symmLE symmLE_anti symmLE_le N) μ := by
  refine martingale_of_setIntegral_eq_succ (fun k ↦ ?_) (fun k ↦ integrable_smean hμ hint _)
    fun k s hs ↦ ?_
  · rw [revFiltration_apply]
    exact (measurable_symmLE_smean (N - k)).stronglyMeasurable
  · rw [revFiltration_apply] at hs
    rw [setIntegral_smean_eq hμ hint le_rfl hs, setIntegral_smean_eq hμ hint (by omega) hs]

/-! ### The maximal inequality -/

/-- **Maximal inequality for the sample means of an exchangeable sequence**: if the first
coordinate is integrable, then for every `m : ℝ` the probability that some sample mean is at
distance at least `L` from `m` is at most `∫ |X₀ - m| / L`. -/
theorem mul_measure_exists_le_abs_sum_div_sub_le [IsFiniteMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (m : ℝ) (L : ℝ≥0) :
    L * μ {ω | ∃ n : ℕ, (L : ℝ) ≤ |(∑ i ∈ Finset.range (n + 1), ω i) / (n + 1) - m|} ≤
      ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) := by
  change L * μ {ω | ∃ n : ℕ, (L : ℝ) ≤ |smean n ω - m|} ≤ _
  -- the event is the increasing union of the events up to the horizons `N`
  have hset : {ω | ∃ n : ℕ, (L : ℝ) ≤ |smean n ω - m|} =
      ⋃ N, {ω | ∃ n ≤ N, (L : ℝ) ≤ |smean n ω - m|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  have hmono : Monotone fun N ↦ {ω | ∃ n ≤ N, (L : ℝ) ≤ |smean n ω - m|} :=
    fun _ _ h _ ⟨n, hn, hn'⟩ ↦ ⟨n, hn.trans h, hn'⟩
  rw [hset, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun N ↦ ?_
  -- Doob's maximal inequality for the submartingale `k ↦ |A_{N - k} - m|`
  have hM := ((martingale_smean_rev hμ hint N).sub (martingale_const _ _ m)).submartingale_norm
  have h : L * μ {ω | ∃ k ∈ Finset.range (N + 1), (L : ℝ) ≤ |smean (N - k) ω - m|} ≤
      ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) := by
    simpa [Real.norm_eq_abs, smean_zero] using hM.mul_measure_exists_mem_le_le
      (fun _ _ ↦ norm_nonneg _) L (F := Finset.range (N + 1)) (T := N)
      fun _ ht ↦ Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) h
  rintro ω ⟨n, hn, hL⟩
  exact ⟨N - n, Finset.mem_range.2 (by omega), by rwa [Nat.sub_sub_self hn]⟩

/-! ### The upcrossing inequality -/

/-- The upcrossings of `[a, b]` by the sample means before `N` are upcrossings of `[-b, -a]` by
the negated sample means read backwards from the horizon `N`, before `N + 1`. -/
private lemma upcrossingsBefore_smean_le {a b : ℝ} (hab : a < b) (N : ℕ) (ω : ℕ → ℝ) :
    upcrossingsBefore a b smean N ω ≤
      upcrossingsBefore (-b) (-a) (-fun k ↦ smean (N - k)) (N + 1) ω := by
  refine (upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ smean a b hab N ω).trans_eq ?_
  refine upcrossingsBefore_succ_congr fun k hk ↦ ?_
  simp only [Pi.neg_apply, revProcess_apply_of_le _ hk]

/-- **Upcrossing inequality for the sample means of an exchangeable sequence**: if the first
coordinate `X₀` is integrable, of mean `m`, the expected number of upcrossings of `[a, b]` by the
sample means is at most `∫ |X₀ - m| / (b - a)`. -/
theorem mul_lintegral_upcrossings_sum_div_le [IsProbabilityMeasure μ] (hμ : ExchangeableLaw μ)
    (hint : Integrable (fun ω ↦ ω 0) μ) (a b : ℝ) :
    ENNReal.ofReal (b - a) *
        ∫⁻ ω, upcrossings a b (fun n ω ↦ (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1)) ω ∂μ ≤
      ENNReal.ofReal (∫ ω, |ω 0 - ∫ ω', ω' 0 ∂μ| ∂μ) := by
  rcases le_or_gt b a with hba | hab
  · simp [ENNReal.ofReal_of_nonpos (sub_nonpos.2 hba)]
  set m := ∫ ω, ω 0 ∂μ
  change ENNReal.ofReal (b - a) * ∫⁻ ω, upcrossings a b smean ω ∂μ ≤ _
  -- monotone convergence in the horizon
  have hadapted : StronglyAdapted (Filtration.const ℕ MeasurableSpace.pi le_rfl) smean :=
    fun n ↦ (measurable_smean n).stronglyMeasurable
  simp only [upcrossings]
  rw [lintegral_iSup (f := fun N ω ↦ (upcrossingsBefore a b smean N ω : ℝ≥0∞))
    (fun N ↦ measurable_from_top.comp (hadapted.measurable_upcrossingsBefore hab))
    (fun _ _ h ω ↦ Nat.cast_le.2 (upcrossingsBefore_mono hab h ω)), ENNReal.mul_iSup]
  refine iSup_le fun N ↦ ?_
  -- Doob's upcrossing inequality for the negated reversed means
  have hM := (martingale_smean_rev hμ hint N).neg
  have hint' := hM.stronglyAdapted.integrable_upcrossingsBefore (μ := μ) (N := N + 1)
    (neg_lt_neg hab)
  have hDoob := hM.submartingale.mul_integral_upcrossingsBefore_le_integral_posPart_sub
    (-b) (-a) (N + 1)
  rw [neg_sub_neg] at hDoob
  simp only [Pi.neg_apply, Nat.sub_eq_zero_of_le (Nat.le_succ N), Nat.sub_zero, smean_zero,
    sub_neg_eq_add, neg_add_eq_sub] at hDoob
  -- the expectation at time `0` is at least `(b - m)⁺`, by convexity
  have hb : Integrable (fun ω ↦ b - smean N ω) μ := (integrable_const b).sub
    (integrable_smean hμ hint N)
  have h₁ : (b - m)⁺ ≤ ∫ ω, (b - smean N ω)⁺ ∂μ := by
    have heq : ∫ ω, (b - smean N ω) ∂μ = b - m := by
      rw [integral_sub (integrable_const b) (integrable_smean hμ hint N), integral_const,
        probReal_univ, one_smul, integral_smean hμ hint N]
    rw [← heq, posPart_def]
    exact sup_le (integral_mono hb hb.pos_part fun ω ↦ le_posPart _)
      (integral_nonneg fun ω ↦ posPart_nonneg _)
  -- `(b - x)⁺ - (b - m)⁺ ≤ |x - m|`, the positive part being `1`-Lipschitz
  have h₂ : ∫ ω, (b - ω 0)⁺ ∂μ - (b - m)⁺ ≤ ∫ ω, |ω 0 - m| ∂μ := by
    have key (x : ℝ) : (b - x)⁺ - (b - m)⁺ ≤ |x - m| := by
      rw [sub_le_iff_le_add, posPart_def, posPart_def]
      refine sup_le ?_ ?_
      · have := le_sup_left (a := b - m) (b := 0)
        have := neg_abs_le (x - m)
        linarith
      · have := le_sup_right (a := b - m) (b := 0)
        have := abs_nonneg (x - m)
        linarith
    have hint₀ : Integrable (fun ω ↦ (b - ω 0)⁺) μ := ((integrable_const b).sub hint).pos_part
    calc ∫ ω, (b - ω 0)⁺ ∂μ - (b - m)⁺ = ∫ ω, ((b - ω 0)⁺ - (b - m)⁺) ∂μ := by
          rw [integral_sub hint₀ (integrable_const _), integral_const, probReal_univ, one_smul]
      _ ≤ ∫ ω, |ω 0 - m| ∂μ := integral_mono (hint₀.sub (integrable_const _))
          (hint.sub (integrable_const m)).abs fun ω ↦ key (ω 0)
  calc ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b smean N ω : ℝ≥0∞) ∂μ
      ≤ ENNReal.ofReal (b - a) * ∫⁻ ω,
          (upcrossingsBefore (-b) (-a) (-fun k ↦ smean (N - k)) (N + 1) ω : ℝ≥0∞) ∂μ := by
        gcongr with ω
        exact_mod_cast upcrossingsBefore_smean_le hab N ω
    _ = ENNReal.ofReal ((b - a) * ∫ ω,
          (upcrossingsBefore (-b) (-a) (-fun k ↦ smean (N - k)) (N + 1) ω : ℝ) ∂μ) := by
        rw [ENNReal.ofReal_mul (sub_nonneg.2 hab.le),
          ofReal_integral_eq_lintegral_ofReal hint' (.of_forall fun ω ↦ Nat.cast_nonneg _)]
        simp
    _ ≤ ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) :=
        ENNReal.ofReal_le_ofReal (by linarith)

end ProbabilityTheory
