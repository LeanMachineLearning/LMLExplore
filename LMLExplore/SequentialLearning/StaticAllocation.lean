/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecificLimits.Basic
public import LMLExplore.Probability.LargeDeviations.Pi
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Large deviations of the empirical means of a run under static allocations

Let the arms `a` of a stochastic bandit `ν : Kernel α ℝ`, finitely many, have laws whose empirical
means satisfy the large deviation principle with good rate functions `I a`, for instance by
Cramér's theorem when their cumulant generating functions are finite near `0`. Consider runs of
algorithms whose numbers of pulls after `T` rounds satisfy `|N_{T,a} - T w a| ≤ k` almost surely,
for proportions `w a > 0`, as the static proportions algorithms of fixed-budget identification do.
Then the laws of the vectors `μ̂_T` of the empirical means after `T` rounds satisfy the large
deviation principle with speed `1 / T` and rate function `x ↦ ∑ a, w a I a (x a)`
[GJ04; D23, Theorem 12]. The numbers of pulls are random and may depend on the rewards, so the
law of `μ̂_T` is not a product, unlike the laws of `LMLExplore.hasLDP_pi_comp_of_tendsto_div`.

The proof goes through LML's reward stream model `streamMeasure ν`, the stack of rewards of
[LS, Section 4.6], whose rows are independent i.i.d. sequences
(`LMLExplore.streamMeasure_forall_row_mem`): the empirical mean of arm `a`
after `T` rounds is the mean of the first `N_{T,a}` entries of its row
(`hasLaw_rewardByCount_streamMeasure`).

* The upper bound is uniform over the numbers of samples in a window around `T w`
  (`eventually_streamMeasure_mean_mem_le_exp`), by the product principle for fixed numbers of
  samples growing like `T w`; the `(2 k + 1)^K` possible numbers of pulls then cost a constant
  factor.
* The lower bound asks the mean of the first `⌈T w a - k⌉₊` entries of each row to be close to the
  target and the next `2 k` entries to lie in a fixed ball
  (`exists_eventually_le_streamMeasure_forall_mean_mem`): the means after every number of pulls in
  the window are then close to the target, at the price of a constant factor.

## Main statements

* `MeasureTheory.Measure.infinitePi_fin_mem_and_forall_add_mem`: for an i.i.d. sequence, the
  first `n` terms and the next `m` terms are independent.
* `LMLExplore.eventually_streamMeasure_mean_mem_le_exp`,
  `LMLExplore.exists_eventually_le_streamMeasure_forall_mean_mem`: the exponential upper and lower
  bounds for the empirical means of the rows, uniformly over the numbers of samples in a window.
* `LMLExplore.measure_empMean_mem_le_streamMeasure`,
  `LMLExplore.streamMeasure_le_measure_empMean_mem`: the transfer of events about the empirical
  means of a run to the stream model, in both directions, when the numbers of pulls lie in a set
  almost surely.
* `LMLExplore.hasLDP_empMean_of_abs_pullCount_sub_le`: the large deviation principle of the
  empirical means of runs with numbers of pulls within `k` of `T w`.
* `LMLExplore.hasLDP_empMean_rateFunction_of_abs_pullCount_sub_le`: the same with the Cramér rate
  functions of arms whose cumulant generating functions are finite near `0`.

## Implementation notes

The statements and proofs are adapted from the formalization of [D23] in the paper project
RemyDegenne/Degenne2023Existence (same author), which works in LML's array model for trajectory
measures. Here the theorems hold for every algorithm-environment sequence against the bandit, the
transfer to the stream goes through the rewards by count of the run, and the bounds for fixed
numbers of samples come from the product principle `LMLExplore.hasLDP_pi_comp_of_tendsto_div`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2, Theorem 12.
* [GJ04] P. Glynn and S. Juneja, *A large deviations perspective on ordinal optimization*,
  Winter Simulation Conference 2004.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Learning Bandits
open TauCeti.Probability (HasLDP IsGoodRateFunction)

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- **The first terms of an i.i.d. sequence and the next terms are independent.** For an i.i.d.
sequence `z` of law `μ`, the first `n` terms `(z i)_{i < n}` lie in `B` and the next `m` terms lie
in `C` with probability `μ^⊗n(B) μ(C)^m`. -/
theorem infinitePi_fin_mem_and_forall_add_mem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n m : ℕ) {B : Set (Fin n → X)} {C : Set X} (hB : MeasurableSet B)
    (hC : MeasurableSet C) :
    (Measure.infinitePi fun _ : ℕ ↦ μ) {z | (fun i : Fin n ↦ z i) ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      Measure.pi (fun _ : Fin n ↦ μ) B * μ C ^ m := by
  -- The first `n` terms and the next `m` terms are independent.
  have h_ind := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)).indepFun_finset (range n) (Ico n (n + m))
    (Finset.disjoint_left.2 fun i hi hi' ↦ by simp at hi hi'; omega) (fun _ ↦ by fun_prop)
  simp only [id] at h_ind
  have h_fin : Measurable fun (u : {i // i ∈ range n} → X) (i : Fin n) ↦
      u ⟨i, mem_range.2 i.2⟩ := by fun_prop
  have h_set : {z : ℕ → X | (fun i : Fin n ↦ z i) ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      (fun z (i : range n) ↦ z i) ⁻¹' ((fun u (i : Fin n) ↦ u ⟨i, mem_range.2 i.2⟩) ⁻¹' B) ∩
        (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Subtype.forall, mem_Ico]
    refine and_congr Iff.rfl ⟨fun h i hi ↦ ?_, fun h j hj ↦ h _ ⟨by omega, by omega⟩⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi.1
    exact h j (by omega)
  rw [h_set, h_ind.measure_inter_preimage_eq_mul _ _ (h_fin hB) (.univ_pi fun _ ↦ hC)]
  congr 1
  · -- The first `n` terms are `n` independent samples of `μ`.
    have h_pi : (Measure.infinitePi fun _ : ℕ ↦ μ).map (fun z (i : Fin n) ↦ z i) =
        Measure.pi fun _ : Fin n ↦ μ := by
      rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
    rw [← h_pi, Measure.map_apply (by fun_prop) hB]
    rfl
  · have h_pi : (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) =
        ((Ico n (n + m) : Finset ℕ) : Set ℕ).pi fun _ ↦ C := by
      ext z
      simp
    rw [h_pi, Measure.infinitePi_pi _ fun _ _ ↦ hC, Finset.prod_const, Nat.card_Ico,
      Nat.add_sub_cancel_left]

end MeasureTheory.Measure

namespace LMLExplore

variable {α : Type*} {mα : MeasurableSpace α}

/-! ### Large deviations of the empirical means of the rows of the stream -/

section Stream

variable [Fintype α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {I : α → ℝ → ℝ≥0∞} {w : α → ℝ}

/-- **The exponential upper bound for the rows of the reward stream, uniformly in a window.** Let
the laws of the empirical means of `m` independent samples of `ν a` satisfy the large deviation
principle with speed `1 / m` and a good rate function `I a`, and let `w a > 0`. For a closed set
`F` and every real `r` below the infimum of `x ↦ ∑ a, w a I a (x a)` on `F`, for every large `T`
and every `n : α → ℕ` with `|n a - T w a| ≤ c`, the vector of the empirical means of the first
`n a` entries of the rows lies in `F` with probability at most `exp (-(T r))`. -/
theorem eventually_streamMeasure_mean_mem_le_exp
    (hP : ∀ a, HasLDP atTop (fun m : ℕ ↦ (m : ℝ≥0)⁻¹)
      (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map fun z : Fin m → ℝ ↦ (∑ i, z i) / (m : ℝ))
      (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) (hw : ∀ a, 0 < w a) (c : ℝ) {F : Set (α → ℝ)}
    (hF : IsClosed F) {r : ℝ}
    (hr : (r : EReal) < ((⨅ x ∈ F, ∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal)) :
    ∀ᶠ T : ℕ in atTop, ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ c) →
      streamMeasure ν {ω | (fun a ↦ (∑ i ∈ range (n a), ω i a) / (n a : ℝ)) ∈ F} ≤
        ENNReal.ofReal (Real.exp (-(T * r))) := by
  classical
  -- For each `T`, pick numbers of samples in the window that violate the bound if there are some,
  -- and `⌈T w⌉₊` otherwise. They grow like `T w`, so the product principle applies to them.
  set B : ℕ → (α → ℕ) → Prop := fun T n ↦ (∀ a, |(n a : ℝ) - T * w a| ≤ c) ∧
    ENNReal.ofReal (Real.exp (-(T * r))) <
      streamMeasure ν {ω | (fun a ↦ (∑ i ∈ range (n a), ω i a) / (n a : ℝ)) ∈ F} with hB
  set m : ℕ → α → ℕ := fun T ↦ if h : ∃ n, B T n then h.choose else fun a ↦ ⌈T * w a⌉₊ with hm
  have hm_abs (T : ℕ) (a : α) : |(m T a : ℝ) - T * w a| ≤ max c 1 := by
    by_cases h : ∃ n, B T n
    · simp only [hm, h, dite_true]
      exact (h.choose_spec.1 a).trans (le_max_left _ _)
    · simp only [hm, h, dite_false]
      have h0 : 0 ≤ (T : ℝ) * w a := mul_nonneg T.cast_nonneg (hw a).le
      rw [abs_of_nonneg (sub_nonneg.2 (Nat.le_ceil _))]
      linarith [Nat.ceil_lt_add_one h0, le_max_right c 1]
  have hLDP := hasLDP_pi_comp_of_tendsto_div hP hI (m := fun a T ↦ m T a) hw
    fun a ↦ tendsto_div_natCast_of_abs_sub_mul_le fun T ↦ hm_abs T a
  filter_upwards [hLDP.eventually_measure_le_exp hF hr] with T hT n hn
  by_contra hlt
  have h : ∃ n, B T n := ⟨n, hn, not_le.1 hlt⟩
  have hmT : m T = h.choose := by simp only [hm, h, dite_true]
  have h_eq := congrArg (· F) (streamMeasure_map_mean (ν := ν) (m T))
  rw [Measure.map_apply (by fun_prop) hF.measurableSet] at h_eq
  have h_bad := h.choose_spec.2
  rw [← hmT] at h_bad
  exact absurd (h_bad.trans_le (h_eq.trans_le hT)) (lt_irrefl _)

omit [Fintype α] in
/-- The natural numbers within `k` of a real `x` are `⌈x - k⌉₊ + d` for some `d ≤ 2 k`. -/
private lemma exists_eq_ceil_sub_add {x : ℝ} {k n : ℕ} (hn : |(n : ℝ) - x| ≤ k) :
    ∃ d ≤ 2 * k, n = ⌈x - k⌉₊ + d := by
  have h := abs_le.1 hn
  have hlo : ⌈x - k⌉₊ ≤ n := Nat.ceil_le.2 (by linarith)
  have hhi : n ≤ ⌈x - k⌉₊ + 2 * k := by
    have : (n : ℝ) ≤ ⌈x - k⌉₊ + 2 * k := by linarith [Nat.le_ceil (x - k)]
    exact_mod_cast this
  exact ⟨n - ⌈x - k⌉₊, by omega, (Nat.add_sub_cancel' hlo).symm⟩

omit [Fintype α] in
/-- For a real `x ≥ 0` and `d ≤ 2 k`, the natural number `⌈x - k⌉₊ + d` is within `2 k + 1`
of `x`. -/
private lemma abs_ceil_sub_add_sub_le {x : ℝ} (hx : 0 ≤ x) {k d : ℕ} (hd : d ≤ 2 * k) :
    |((⌈x - k⌉₊ + d : ℕ) : ℝ) - x| ≤ 2 * k + 1 := by
  have h1 : x - k ≤ ⌈x - k⌉₊ := Nat.le_ceil _
  have h2 : (⌈x - k⌉₊ : ℝ) < x + 1 := (Nat.cast_le.2 (Nat.ceil_mono
    (by linarith [k.cast_nonneg (α := ℝ)]))).trans_lt (Nat.ceil_lt_add_one hx)
  have h3 : (d : ℝ) ≤ 2 * k := by exact_mod_cast hd
  rw [abs_le]
  push_cast
  constructor <;> linarith [d.cast_nonneg (α := ℝ)]

omit [Fintype α] in
/-- If the mean of `n₀` numbers of sum `S` is within `δ / 2` of `x`, and `j` further numbers are
within `L` of `x`, with `2 j L < n₀ δ`, then the mean of all the `n₀ + j` numbers is within `δ`
of `x`. -/
private lemma dist_mean_add_lt {n₀ j : ℕ} (hn₀ : 0 < n₀) {S x δ L : ℝ} {z : ℕ → ℝ}
    (hS : dist (S / n₀) x < δ / 2) (hz : ∀ i < j, dist (z i) x ≤ L) (hjL : 2 * (j * L) < n₀ * δ) :
    dist ((S + ∑ i ∈ range j, z i) / ((n₀ + j : ℕ) : ℝ)) x < δ := by
  have hn₀' : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hm : (0 : ℝ) < ((n₀ + j : ℕ) : ℝ) := by positivity
  have hS' : |S - n₀ * x| < n₀ * (δ / 2) := by
    rw [Real.dist_eq, show S / n₀ - x = (S - n₀ * x) / n₀ by field_simp, abs_div,
      abs_of_pos hn₀', div_lt_iff₀ hn₀'] at hS
    linarith
  have hsum : |∑ i ∈ range j, (z i - x)| ≤ j * L := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi ↦ (?_ : |z i - x| ≤ L)).trans (by simp)
    rw [← Real.dist_eq]
    exact hz i (Finset.mem_range.1 hi)
  have h_eq : (S + ∑ i ∈ range j, z i) / ((n₀ + j : ℕ) : ℝ) - x =
      ((S - n₀ * x) + ∑ i ∈ range j, (z i - x)) / ((n₀ + j : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  have hδ : 0 < δ := by linarith [dist_nonneg.trans_lt hS]
  have hj : (n₀ : ℝ) ≤ ((n₀ + j : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n₀ j
  rw [Real.dist_eq, h_eq, abs_div, abs_of_pos hm, div_lt_iff₀ hm]
  calc |S - n₀ * x + ∑ i ∈ range j, (z i - x)|
      ≤ |S - n₀ * x| + |∑ i ∈ range j, (z i - x)| := abs_add_le _ _
    _ < n₀ * δ := by linarith
    _ ≤ δ * ((n₀ + j : ℕ) : ℝ) := by nlinarith

omit [Fintype α] in
/-- If the mean of the first `n₀ > 0` terms of `z` is within `δ / 2` of `x`, the next `2 k` terms
are within `L` of `x`, and `4 k L < n₀ δ`, then the mean of the first `n₀ + d` terms of `z` is
within `δ` of `x` for every `d ≤ 2 k`. -/
private lemma dist_mean_lt {z : ℕ → ℝ} {n₀ k d : ℕ} {x δ L : ℝ} (hn₀ : 0 < n₀) (hL : 0 ≤ L)
    (hδL : 4 * k * L < n₀ * δ) (hz : dist ((∑ i ∈ range n₀, z i) / n₀) x < δ / 2)
    (hzL : ∀ j < 2 * k, dist (z (n₀ + j)) x ≤ L) (hd : d ≤ 2 * k) :
    dist ((∑ i ∈ range (n₀ + d), z i) / ((n₀ + d : ℕ) : ℝ)) x < δ := by
  rw [Finset.sum_range_add]
  refine dist_mean_add_lt hn₀ hz (fun i hi ↦ hzL i (by omega)) ?_
  have : (d : ℝ) ≤ 2 * k := by exact_mod_cast hd
  nlinarith

/-- **The exponential lower bound for the rows of the reward stream, uniformly in a window.** Let
the laws of the empirical means of `m` independent samples of `ν a` satisfy the large deviation
principle with speed `1 / m` and rate function `I a`, and let `w a > 0`. For a neighbourhood `U` of
`x` and every real `r > ∑ a, w a I a (x a)`, there is `C > 0` such that for every large `T`, with
probability at least `C exp (-(T r))`, the vectors of the empirical means of the first `n a` entries
of the rows lie in `U` for all the `n : α → ℕ` in the window `|n a - T w a| ≤ k`. -/
theorem exists_eventually_le_streamMeasure_forall_mean_mem
    (hP : ∀ a, HasLDP atTop (fun m : ℕ ↦ (m : ℝ≥0)⁻¹)
      (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map fun z : Fin m → ℝ ↦ (∑ i, z i) / (m : ℝ))
      (I a))
    (hw : ∀ a, 0 < w a) (k : ℕ) {x : α → ℝ} {U : Set (α → ℝ)} (hU : U ∈ 𝓝 x) {r : ℝ}
    (hr : ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal) < r) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ ∀ᶠ T : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(T * r))) ≤
      streamMeasure ν {ω | ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ k) →
        (fun a ↦ (∑ i ∈ range (n a), ω i a) / (n a : ℝ)) ∈ U} := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  -- A closed ball of positive probability for each arm.
  have hL (a : α) : ∃ L : ℕ, ν a (Metric.closedBall (x a) L) ≠ 0 := by
    by_contra! h
    have h_null := measure_iUnion_null (μ := ν a) h
    rw [Metric.iUnion_closedBall_nat, measure_univ] at h_null
    exact one_ne_zero h_null
  choose L hL using hL
  -- The first `n₀ T a = ⌈T w a - k⌉₊` entries of the row of `a`, a number within `2 k + 1` of
  -- `T w a`, have a mean close to `x a` with probability at least `exp (-(T r))` jointly.
  set n₀ : ℕ → α → ℕ := fun T a ↦ ⌈T * w a - k⌉₊ with hn₀
  have hn₀_le (T : ℕ) (a : α) : T * w a - k ≤ n₀ T a := Nat.le_ceil _
  have hn₀_abs (T : ℕ) (a : α) : |(n₀ T a : ℝ) - T * w a| ≤ 2 * k + 1 :=
    abs_ceil_sub_add_sub_le (d := 0) (mul_nonneg T.cast_nonneg (hw a).le) (Nat.zero_le _)
  set V : Set (α → ℝ) := Set.univ.pi fun a ↦ Metric.ball (x a) (δ / 2)
  have h_box := eventually_exp_le_of_neg_le_liminf_inv_mul_log
    (neg_sum_le_liminf_log_pi (fun a ↦ (hP a).comp_of_tendsto_div (hw a)
      (tendsto_div_natCast_of_abs_sub_mul_le fun T ↦ hn₀_abs T a))
      (x := x) (s := V) (set_pi_mem_nhds Set.finite_univ fun a _ ↦
        Metric.ball_mem_nhds (x a) (half_pos hδ))) hr
  refine ⟨∏ a, ν a (Metric.closedBall (x a) (L a)) ^ (2 * k),
    Finset.prod_ne_zero_iff.2 fun a _ ↦ pow_ne_zero _ (hL a), ?_⟩
  filter_upwards [h_box, eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const
    (hw a)).eventually_ge_atTop ((k : ℝ) + 1 + 4 * k * L a / δ)] with T hT hT_large
  have hLδ (a : α) : 0 ≤ 4 * k * (L a : ℝ) / δ := by positivity
  have hn₀_pos (a : α) : 0 < n₀ T a := by
    have : (0 : ℝ) < n₀ T a := by linarith [hn₀_le T a, hT_large a, hLδ a]
    exact_mod_cast this
  have hn₀_L (a : α) : 4 * k * (L a : ℝ) < n₀ T a * δ := by
    have h1 : 4 * k * (L a : ℝ) / δ < n₀ T a := by linarith [hn₀_le T a, hT_large a]
    rwa [div_lt_iff₀ hδ] at h1
  -- The event on the rows: the mean of the first `n₀ T a` entries is within `δ / 2` of `x a`, and
  -- the next `2 k` entries are within `L a` of `x a`.
  set E : α → Set (ℕ → ℝ) := fun a ↦ {z | (∑ i ∈ range (n₀ T a), z i) / (n₀ T a : ℝ) ∈
    Metric.ball (x a) (δ / 2) ∧ ∀ j < 2 * k, z (n₀ T a + j) ∈ Metric.closedBall (x a) (L a)}
  have hE (a : α) : MeasurableSet (E a) := by
    have : E a = (fun z : ℕ → ℝ ↦ (∑ i ∈ range (n₀ T a), z i) / (n₀ T a : ℝ)) ⁻¹'
        Metric.ball (x a) (δ / 2) ∩ ⋂ j ∈ Finset.range (2 * k),
          (fun z : ℕ → ℝ ↦ z (n₀ T a + j)) ⁻¹' Metric.closedBall (x a) (L a) := by
      ext z
      simp [E]
    rw [this]
    exact ((by fun_prop : Measurable fun z : ℕ → ℝ ↦ (∑ i ∈ range (n₀ T a), z i) / (n₀ T a : ℝ))
      Metric.isOpen_ball.measurableSet).inter (Finset.measurableSet_biInter _ fun j _ ↦
        (measurable_pi_apply _) Metric.isClosed_closedBall.measurableSet)
  -- On this event, the means after every number of samples in the window are within `δ` of `x`.
  have h_sub : {ω : ℕ → α → ℝ | ∀ a, (fun i ↦ ω i a) ∈ E a} ⊆
      {ω | ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ k) →
        (fun a ↦ (∑ i ∈ range (n a), ω i a) / (n a : ℝ)) ∈ U} := by
    intro ω hω n hn
    refine hδU ?_
    rw [ball_pi _ hδ]
    intro a _
    obtain ⟨d, hd, hnd⟩ := exists_eq_ceil_sub_add (hn a)
    simp only [Metric.mem_ball, hnd]
    exact dist_mean_lt (hn₀_pos a) (L a).cast_nonneg (hn₀_L a) (hω a).1 (hω a).2 hd
  refine le_trans ?_ (measure_mono h_sub)
  -- The event on each row splits into an event on its first `n₀ T a` entries and on the next ones.
  have hE_eq (a : α) : (Measure.infinitePi fun _ : ℕ ↦ ν a) (E a) =
      ((Measure.pi fun _ : Fin (n₀ T a) ↦ ν a).map fun y ↦ (∑ i, y i) / (n₀ T a : ℝ))
        (Metric.ball (x a) (δ / 2)) * ν a (Metric.closedBall (x a) (L a)) ^ (2 * k) := by
    rw [Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet,
      ← Measure.infinitePi_fin_mem_and_forall_add_mem _ _ _
        ((by fun_prop : Measurable fun y : Fin (n₀ T a) → ℝ ↦ (∑ i, y i) / (n₀ T a : ℝ))
          Metric.isOpen_ball.measurableSet) Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext z
    simp only [E, Set.mem_ofPred_eq, Set.mem_preimage,
      Fin.sum_univ_eq_sum_range (fun i ↦ z i)]
  rw [streamMeasure_forall_row_mem ν hE, Finset.prod_congr rfl fun a _ ↦ hE_eq a,
    Finset.prod_mul_distrib, mul_comm]
  gcongr
  refine hT.trans_eq ?_
  rw [Measure.pi_pi]

end Stream

/-! ### Transfer of the empirical means of a run to the stream -/

section Transfer

variable [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Upper transfer of the empirical means of a run to the stream.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, if the numbers of pulls after `T` rounds lie
almost surely in a set `S`, the probability that the vector of the empirical means after `T`
rounds lies in `F` is at most the probability that for some `n ∈ S`, the vector of the empirical
means of the first `n a` entries of the rows of the reward stream lies in `F`. Neither `S` nor `F`
needs to be measurable: for non-measurable events, both sides are outer measures. -/
theorem measure_empMean_mem_le_streamMeasure [Countable α]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (T : ℕ) {S : Set (α → ℕ)} (hS : ∀ᵐ ω ∂P, (fun a ↦ pullCount A a T ω) ∈ S) (F : Set (α → ℝ)) :
    P {ω | (fun a ↦ empMean A R a T ω) ∈ F} ≤
      streamMeasure ν {y | ∃ n ∈ S, (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ F} := by
  calc P {ω | (fun a ↦ empMean A R a T ω) ∈ F}
  _ ≤ P {ω | ∃ t, (fun a ↦ pullCount A a t ω) ∈ S ∧
      (fun a ↦ sumRewards A R a t ω / (pullCount A a t ω : ℝ)) ∈ F} := by
    refine measure_mono_ae ?_
    filter_upwards [hS] with ω hω hF
    exact ⟨T, hω, by simpa only [empMean] using hF⟩
  _ ≤ streamMeasure ν {y | ∃ n ∈ S, (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ F} :=
    measure_exists_pullCount_sumRewards_pi_le h fun s y ↦ s ∈ S ∧ (fun a ↦ y a / (s a : ℝ)) ∈ F

/-- **Lower transfer of the empirical means of a run to the stream.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, if the numbers of pulls after `T` rounds lie
almost surely in a set `S`, the probability that the vector of the empirical means after `T`
rounds lies in a measurable set `U` is at least the probability that for all `n ∈ S`, the vector of
the empirical means of the first `n a` entries of the rows of the reward stream lies in `U`. -/
theorem streamMeasure_le_measure_empMean_mem [Finite α]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (T : ℕ) {S : Set (α → ℕ)} (hS : ∀ᵐ ω ∂P, (fun a ↦ pullCount A a T ω) ∈ S)
    {U : Set (α → ℝ)} (hU : MeasurableSet U) :
    streamMeasure ν {y | ∀ n ∈ S, (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ U} ≤
      P {ω | (fun a ↦ empMean A R a T ω) ∈ U} := by
  -- The rewards by count of the run, arranged as a reward stream, have the law of the stream.
  have hZ := hasLaw_rewardByCount_streamMeasure h
  have hG : MeasurableSet
      {y : ℕ → α → ℝ | ∀ n ∈ S, (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ U} := by
    simp_rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun _ ↦
      (by fun_prop : Measurable fun y : ℕ → α → ℝ ↦
        fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) hU
  rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable hG,
    ← one_mul (P _), ← measure_univ (μ := streamMeasure ν), ← Measure.prod_preimage_fst]
  -- The empirical mean of arm `a` is the mean of its first `N_{T,a}` rewards by count.
  refine measure_mono_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hS] with ω hω hG
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hG ⊢
  convert hG _ hω using 2 with a
  rw [empMean, sumRewards_eq_sum_range_rewardByCount a T ω]

end Transfer

/-! ### Large deviations of the empirical means under static allocations -/

section LDP

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {O : ℕ → ℕ → Ω → Unit} {A : ℕ → ℕ → Ω → α} {R : ℕ → ℕ → Ω → ℝ}
  {P : ℕ → Measure Ω} [∀ T, IsProbabilityMeasure (P T)] {alg : ℕ → Algorithm Unit α ℝ}
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {I : α → ℝ → ℝ≥0∞} {w : α → ℝ}

/-- **Large deviations of the empirical means under static allocations** [GJ04; D23, Theorem 12].
Let the laws of the empirical means of `m` independent samples of `ν a` satisfy the large deviation
principle with speed `1 / m` and a good rate function `I a`, and let `w a > 0`. For runs of
algorithms `alg T` against the bandit `ν` whose numbers of pulls after `T` rounds satisfy
`|N_{T,a} - T w a| ≤ k` almost surely, the laws of the vectors of the empirical means after `T`
rounds satisfy the large deviation principle with speed `1 / T` and rate function
`x ↦ ∑ a, w a I a (x a)`, a good rate function by `LMLExplore.isGoodRateFunction_sum_mul`. -/
theorem hasLDP_empMean_of_abs_pullCount_sub_le
    (hP : ∀ a, HasLDP atTop (fun m : ℕ ↦ (m : ℝ≥0)⁻¹)
      (fun m ↦ (Measure.pi fun _ : Fin m ↦ ν a).map fun z : Fin m → ℝ ↦ (∑ i, z i) / (m : ℝ))
      (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) (hw : ∀ a, 0 < w a) (k : ℕ)
    (h : ∀ T, IsAlgEnvSeq (O T) (A T) (R T) (alg T) (Environment.bandit ν) (P T))
    (h_pull : ∀ T, ∀ᵐ ω ∂(P T), ∀ a, |(pullCount (A T) a T ω : ℝ) - T * w a| ≤ k) :
    HasLDP atTop (fun T : ℕ ↦ (T : ℝ≥0)⁻¹)
      (fun T ↦ (P T).map fun ω a ↦ empMean (A T) (R T) a T ω)
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a)) := by
  have hmeas (T : ℕ) : Measurable fun ω a ↦ empMean (A T) (R T) a T ω :=
    measurable_empMean_pi (h T).measurable_action (h T).measurable_feedback T
  have hS (T : ℕ) : ∀ᵐ ω ∂(P T), (fun a ↦ pullCount (A T) a T ω) ∈
      {n : α → ℕ | ∀ a, |(n a : ℝ) - T * w a| ≤ k} := h_pull T
  refine .of_isClosed_of_mem_nhds (isGoodRateFunction_sum_mul hI hw).lowerSemicontinuous
    (fun F hF ↦ ?_) (fun x U hU ↦ ?_)
  · -- Every number of pulls in the window is `n₀ + d` for `n₀ a = ⌈T w a - k⌉₊` and some
    -- `d : α → Fin (2 k + 1)`, a number within `2 k + 1` of `T w a`.
    refine limsup_inv_mul_log_le_neg_of_le_mul_exp fun r hr ↦
      ⟨Fintype.card (α → Fin (2 * k + 1)), ENNReal.natCast_ne_top _, ?_⟩
    filter_upwards [eventually_streamMeasure_mean_mem_le_exp hP hI hw (2 * k + 1) hF hr]
      with T hT
    set n₀ : α → ℕ := fun a ↦ ⌈T * w a - k⌉₊
    rw [Measure.map_apply (hmeas T) hF.measurableSet]
    calc (P T) ((fun ω a ↦ empMean (A T) (R T) a T ω) ⁻¹' F)
    _ ≤ streamMeasure ν {y | ∃ n ∈ {n : α → ℕ | ∀ a, |(n a : ℝ) - T * w a| ≤ k},
        (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ F} :=
      measure_empMean_mem_le_streamMeasure (h T) T (hS T) F
    _ ≤ streamMeasure ν (⋃ d : α → Fin (2 * k + 1), {y | (fun a ↦
        (∑ i ∈ range (n₀ a + d a), y i a) / ((n₀ a + d a : ℕ) : ℝ)) ∈ F}) := by
      refine measure_mono fun y ⟨n, hn, hnF⟩ ↦ Set.mem_iUnion.2 ?_
      choose d hd hnd using fun a ↦ exists_eq_ceil_sub_add (hn a)
      refine ⟨fun a ↦ ⟨d a, Nat.lt_succ_of_le (hd a)⟩, ?_⟩
      obtain rfl : n = fun a ↦ n₀ a + d a := funext hnd
      exact hnF
    _ ≤ ∑ d : α → Fin (2 * k + 1), streamMeasure ν {y | (fun a ↦
        (∑ i ∈ range (n₀ a + d a), y i a) / ((n₀ a + d a : ℕ) : ℝ)) ∈ F} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _d : α → Fin (2 * k + 1), ENNReal.ofReal (Real.exp (-(T * r))) :=
      Finset.sum_le_sum fun d _ ↦ hT (fun a ↦ n₀ a + d a) fun a ↦
        abs_ceil_sub_add_sub_le (mul_nonneg T.cast_nonneg (hw a).le) (Nat.lt_succ_iff.1 (d a).2)
    _ = Fintype.card (α → Fin (2 * k + 1)) * ENNReal.ofReal (Real.exp (-(T * r))) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  · -- The means of the stream are in the interior of `U` for all the numbers of pulls in the
    -- window with probability at least `C exp (-(T r))`.
    refine neg_le_liminf_inv_mul_log_of_mul_exp_le fun r hr ↦ ?_
    obtain ⟨C, hC, hev⟩ := exists_eventually_le_streamMeasure_forall_mean_mem hP hw k
      (interior_mem_nhds.2 hU) hr
    refine ⟨C, hC, hev.mono fun T hT ↦ hT.trans ?_⟩
    calc streamMeasure ν {y | ∀ n : α → ℕ, (∀ a, |(n a : ℝ) - T * w a| ≤ k) →
          (fun a ↦ (∑ i ∈ range (n a), y i a) / (n a : ℝ)) ∈ interior U}
    _ ≤ (P T) {ω | (fun a ↦ empMean (A T) (R T) a T ω) ∈ interior U} :=
      streamMeasure_le_measure_empMean_mem (h T) T (hS T) isOpen_interior.measurableSet
    _ ≤ (P T).map (fun ω a ↦ empMean (A T) (R T) a T ω) U :=
      (Measure.map_apply (hmeas T) isOpen_interior.measurableSet).symm.trans_le
        (measure_mono interior_subset)

/-- **Cramér's theorem under static allocations** [GJ04; D23, Theorem 12]. If the cumulant
generating function of each arm `ν a` is finite on a neighbourhood of `0`, `w a > 0`, and the
numbers of pulls after `T` rounds of runs of algorithms `alg T` against the bandit `ν` satisfy
`|N_{T,a} - T w a| ≤ k` almost surely, then the laws of the vectors of the empirical means after
`T` rounds satisfy the large deviation principle with speed `1 / T` and rate function
`x ↦ ∑ a, w a I_a(x a)`, with `I_a` the Cramér rate function of `ν a`. This rate function is
good, by `LMLExplore.isGoodRateFunction_sum_mul` and `LMLExplore.isGoodRateFunction_rateFunction`.
-/
theorem hasLDP_empMean_rateFunction_of_abs_pullCount_sub_le
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (ν a))) (hw : ∀ a, 0 < w a) (k : ℕ)
    (h : ∀ T, IsAlgEnvSeq (O T) (A T) (R T) (alg T) (Environment.bandit ν) (P T))
    (h_pull : ∀ T, ∀ᵐ ω ∂(P T), ∀ a, |(pullCount (A T) a T ω : ℝ) - T * w a| ≤ k) :
    HasLDP atTop (fun T : ℕ ↦ (T : ℝ≥0)⁻¹)
      (fun T ↦ (P T).map fun ω a ↦ empMean (A T) (R T) a T ω)
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * rateFunction id (ν a) (x a)) :=
  hasLDP_empMean_of_abs_pullCount_sub_le
    (fun a ↦ hasLDP_cramer (integrable_of_mem_interior_integrableExpSet (hν a)))
    (fun a ↦ isGoodRateFunction_rateFunction (hν a)) hw k h h_pull

end LDP

end LMLExplore
