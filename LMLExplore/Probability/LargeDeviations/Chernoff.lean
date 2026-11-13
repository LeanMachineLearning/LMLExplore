/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Moments.MGF.Dominated
public import LMLExplore.Probability.Moments.RateFunction

/-!
# Cramér–Chernoff bounds with the rate function

Let `Y` be an integrable real random variable under a probability measure `Q`, with Cramér rate
function `I = rateFunction Y Q`. For independent real random variables `X i`, `i ∈ s`, whose
moment generating functions are dominated by that of `Y` on `[0, ∞)`
(`LMLExplore.MGFDominatedOn (X i) P Y Q (Set.Ici 0)`), the sum of the `X i` deviates above `#s x`
with probability at most `exp (-(#s I(x)))` at every level `x ≥ E[Y]`: for every real `r ≤ I(x)`,
`P(#s x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s r))`. Symmetrically, domination on `(-∞, 0]` bounds the lower
tail at the levels `x ≤ E[Y]`. These are the bounds of the Cramér–Chernoff method with the optimal
exponent: the rate function is the supremum of the exponents `t x - cgf Y Q t` of the Chernoff
bounds at the parameters `t`. The levels are arbitrary reals: at a level where `I(x) = ⊤`, for
example beyond the essential supremum of `Y`, the bound holds for every `r`.

With `μ̂ = (∑ i ∈ s, X i) / #s` the empirical mean, the same bounds control the deviations of
`#s I(μ̂)`, the generalized likelihood ratio statistic of the empirical mean when `Y` is the
statistic of an exponential family: on each side of `E[Y]`, `#s I(μ̂) ≥ z` has probability at most
`exp (-z)`, and for variables dominated on `ℝ` the probability that `#s I(μ̂) ≥ z` is at most
`2 exp (-z)`. These bounds are the source of the confidence regions and stopping thresholds built
from the rate function.

## Main statements

* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_of_le_rateFunction`: the upper tail
  `P(#s x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s r))` for `x ≥ E[Y]`, `r ≤ I(x)` and variables dominated by
  `Y` on `Set.Ici 0`.
* `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_of_le_rateFunction`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s x) ≤ exp (-(#s r))` for `x ≤ E[Y]`, `r ≤ I(x)` and variables dominated by
  `Y` on `Set.Iic 0`.
* `ProbabilityTheory.iIndepFun.measureReal_integral_le_and_le_card_mul_rateFunction_le_exp`,
  `ProbabilityTheory.iIndepFun.measureReal_le_integral_and_le_card_mul_rateFunction_le_exp`:
  `P(E[Y] ≤ μ̂, z ≤ #s I(μ̂)) ≤ exp (-z)` and `P(μ̂ ≤ E[Y], z ≤ #s I(μ̂)) ≤ exp (-z)`.
* `ProbabilityTheory.iIndepFun.measureReal_le_card_mul_rateFunction_le_two_mul_exp`: the
  two-sided bound `P(z ≤ #s I(μ̂)) ≤ 2 exp (-z)` for variables dominated by `Y` on `Set.univ`.
* `ProbabilityTheory.measureReal_eq_zero_or_le_div_or_apply_div_le_le_ite`: an upper tail bound
  `P(s a ≤ S) ≤ B` bounds the probability of the events `s = 0`, `c ≤ S / s` or
  `f(S / s) ≤ L / s` of [LS, Lemma 10.8], for `f` antitone on `Set.Iic c` and `a ≤ c`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 10.8.
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Section 2.2 (the Cramér–Chernoff method).
* A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Section 2.2 (the upper bound of Cramér's theorem).
-/

public section

open MeasureTheory Real Finset Filter LMLExplore

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω Ω' ι : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {X : ι → Ω → ℝ} {Y : Ω' → ℝ} {s : Finset ι} {x r : ℝ}

/-! ### Tails of the sum -/

/-- Negating independent random variables dominated on `Set.Iic 0` by an integrable random
variable `Y` gives independent random variables dominated on `Set.Ici 0` by the integrable `-Y`. -/
private lemma iIndepFun.neg_of_mgfDominatedOn_Iic (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Iic 0)) (hY : Integrable Y Q) :
    iIndepFun (fun i ω ↦ -X i ω) P ∧
      (∀ i ∈ s, MGFDominatedOn (fun ω ↦ -X i ω) P (fun ω ↦ -Y ω) Q (Set.Ici 0)) ∧
      Integrable (fun ω ↦ -Y ω) Q :=
  ⟨h_indep.comp (fun _ y ↦ -y) fun _ ↦ measurable_neg,
    fun i hi ↦ by simpa only [Set.neg_Iic, neg_zero] using (hX i hi).neg,
    by simpa only [Pi.neg_def] using hY.neg⟩

/-- **Cramér–Chernoff bound with the rate function, upper tail.** For independent random
variables `X i`, `i ∈ s`, dominated on `Set.Ici 0` by an integrable random variable `Y` under a
probability measure `Q`, every level `x ≥ E[Y]` and every real `r ≤ I(x)`, where `I` is the rate
function of `Y`, `P(#s x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s r))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_of_le_rateFunction [IsProbabilityMeasure Q]
    (h_indep : iIndepFun X P) (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Ici 0))
    (hY : Integrable Y Q) (hx : Q[Y] ≤ x) (hr : ENNReal.ofReal r ≤ rateFunction Y Q x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * r)) := by
  have := h_indep.isProbabilityMeasure
  rcases le_or_gt r 0 with hr0 | hr0
  · -- for `r ≤ 0` the bound is at least `1`
    exact measureReal_le_one.trans
      (one_le_exp (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hr0)))
  -- every `r' < r` is below the exponent `t x - cgf Y Q t` at some parameter `t ≥ 0`
  rw [rateFunction_eq_iSup_nonneg hY hx] at hr
  have h_cont : Continuous fun r' : ℝ ↦ exp (-(#s * r')) := by fun_prop
  refine ge_of_tendsto (x := 𝓝[<] r) (h_cont.tendsto r |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsLT hr0] with r' hr'
  obtain ⟨t, ⟨ht, ht0⟩, hlt⟩ :=
    lt_biSup_iff.1 (((ENNReal.ofReal_lt_ofReal_iff hr0).2 hr'.2).trans_le hr)
  refine (h_indep.measureReal_sum_ge_le_exp_mul_sub_cgf hX x ht0 ht0 ht).trans
    (exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))))
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr'.1.le).1 hlt).le

/-- **Cramér–Chernoff bound with the rate function, lower tail.** For independent random
variables `X i`, `i ∈ s`, dominated on `Set.Iic 0` by an integrable random variable `Y` under a
probability measure `Q`, every level `x ≤ E[Y]` and every real `r ≤ I(x)`, where `I` is the rate
function of `Y`, `P(∑ i ∈ s, X i ≤ #s x) ≤ exp (-(#s r))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_of_le_rateFunction [IsProbabilityMeasure Q]
    (h_indep : iIndepFun X P) (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Iic 0))
    (hY : Integrable Y Q) (hx : x ≤ Q[Y]) (hr : ENNReal.ofReal r ≤ rateFunction Y Q x) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ #s * x} ≤ exp (-(#s * r)) := by
  obtain ⟨h_indep', hX', hY'⟩ := h_indep.neg_of_mgfDominatedOn_Iic hX hY
  have h := h_indep'.measureReal_sum_ge_le_exp_of_le_rateFunction hX' hY' (x := -x)
    (by rw [integral_neg]; linarith)
    (by rwa [← Pi.neg_def, rateFunction_neg, neg_neg])
  simpa only [sum_neg_distrib, mul_neg, neg_le_neg_iff] using h

/-! ### Deviations of the empirical mean measured by the rate function -/

/-- For a nonempty `s` and every real `c`, the probability that the empirical mean `μ̂` of the
`X i` is at least `E[Y]` with `c ≤ I(μ̂)` is at most `exp (-(#s c))`. -/
private lemma iIndepFun.measureReal_integral_le_and_le_rateFunction_le_exp
    [IsProbabilityMeasure Q] (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Ici 0)) (hY : Integrable Y Q)
    (hs : s.Nonempty) (c : ℝ) :
    P.real {ω | Q[Y] ≤ (∑ i ∈ s, X i ω) / #s ∧
        ENNReal.ofReal c ≤ rateFunction Y Q ((∑ i ∈ s, X i ω) / #s)} ≤ exp (-(#s * c)) := by
  have := h_indep.isProbabilityMeasure
  have hn : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  -- the levels `y ≥ E[Y]` with `c ≤ I(y)` form a set `U` closed upwards, since `I` is monotone
  -- above the mean, and the empirical mean exceeds each level of `U` with small probability
  set U : Set ℝ := {y | Q[Y] ≤ y ∧ ENNReal.ofReal c ≤ rateFunction Y Q y}
  have hU_bdd : BddBelow U := ⟨Q[Y], fun _ hy ↦ hy.1⟩
  have h_tail (y : ℝ) (hy : y ∈ U) :
      P.real {ω | y ≤ (∑ i ∈ s, X i ω) / #s} ≤ exp (-(#s * c)) := by
    simp_rw [le_div_iff₀ hn, mul_comm y]
    exact h_indep.measureReal_sum_ge_le_exp_of_le_rateFunction hX hY hy.1 hy.2
  rcases U.eq_empty_or_nonempty with hU | hU
  · -- if `U` is empty, so is the event
    refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
      (by simp only [measureReal_empty]; exact (exp_pos _).le : P.real ∅ ≤ _)
    exact (Set.eq_empty_iff_forall_notMem.1 hU _ hω).elim
  by_cases ha : sInf U ∈ U
  · -- if `U` has a least element `a`, the event is contained in `{a ≤ μ̂}`
    exact (measureReal_mono (s₂ := {ω | sInf U ≤ (∑ i ∈ s, X i ω) / #s})
      (fun ω hω ↦ csInf_le hU_bdd hω) (measure_ne_top _ _)).trans (h_tail _ ha)
  -- otherwise the event is contained in `{a < μ̂}`, the increasing union of the events
  -- `{y k ≤ μ̂}` for levels `y k ∈ U` decreasing to `a = inf U`
  obtain ⟨y, hy_anti, hy_tendsto, hy_mem⟩ := exists_seq_tendsto_sInf hU hU_bdd
  have h_sub : {ω | Q[Y] ≤ (∑ i ∈ s, X i ω) / #s ∧
      ENNReal.ofReal c ≤ rateFunction Y Q ((∑ i ∈ s, X i ω) / #s)} ⊆
        ⋃ k, {ω | y k ≤ (∑ i ∈ s, X i ω) / #s} := by
    intro ω hω
    have hlt : sInf U < (∑ i ∈ s, X i ω) / #s :=
      (csInf_le hU_bdd hω).lt_of_ne fun h ↦ ha (h ▸ hω)
    obtain ⟨k, hk⟩ := (hy_tendsto.eventually (gt_mem_nhds hlt)).exists
    exact Set.mem_iUnion.2 ⟨k, hk.le⟩
  have h_mono : Monotone fun k ↦ {ω | y k ≤ (∑ i ∈ s, X i ω) / #s} :=
    fun k l hkl ω hω ↦ (hy_anti hkl).trans hω
  refine (measureReal_mono h_sub (measure_ne_top _ _)).trans ?_
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (exp_pos _).le
    (le_of_tendsto' (tendsto_measure_iUnion_atTop h_mono) fun k ↦ ?_)
  rw [Function.comp_apply, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (exp_pos _).le,
    ← measureReal_def]
  exact h_tail _ (hy_mem k)

/-- **Deviations of the empirical mean above the mean, measured by the rate function.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.Ici 0` by an integrable random
variable `Y` under a probability measure `Q`, with empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`, and
every real `z`, `P(E[Y] ≤ μ̂, z ≤ #s I(μ̂)) ≤ exp (-z)`, where `I` is the rate function of `Y`. -/
theorem iIndepFun.measureReal_integral_le_and_le_card_mul_rateFunction_le_exp
    [IsProbabilityMeasure Q] (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Ici 0)) (hY : Integrable Y Q) (z : ℝ) :
    P.real {ω | Q[Y] ≤ (∑ i ∈ s, X i ω) / #s ∧
        ENNReal.ofReal z ≤ #s * rateFunction Y Q ((∑ i ∈ s, X i ω) / #s)} ≤ exp (-z) := by
  have := h_indep.isProbabilityMeasure
  rcases le_or_gt z 0 with hz | hz
  · exact measureReal_le_one.trans (one_le_exp (neg_nonneg.2 hz))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · -- with no variable the event is empty, since `0 < z`
    simp [ENNReal.ofReal_pos.2 hz |>.ne', (exp_pos _).le]
  have hn : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  -- the event is contained in that of the rate function at least `z / #s`
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    ((h_indep.measureReal_integral_le_and_le_rateFunction_le_exp hX hY hs (z / #s)).trans_eq
      (by rw [mul_div_cancel₀ _ hn.ne']))
  refine fun ω hω ↦ ⟨hω.1, ?_⟩
  rw [ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_natCast]
  exact ENNReal.div_le_of_le_mul' hω.2

/-- **Deviations of the empirical mean below the mean, measured by the rate function.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.Iic 0` by an integrable random
variable `Y` under a probability measure `Q`, with empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`, and
every real `z`, `P(μ̂ ≤ E[Y], z ≤ #s I(μ̂)) ≤ exp (-z)`, where `I` is the rate function of `Y`. -/
theorem iIndepFun.measureReal_le_integral_and_le_card_mul_rateFunction_le_exp
    [IsProbabilityMeasure Q] (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q (Set.Iic 0)) (hY : Integrable Y Q) (z : ℝ) :
    P.real {ω | (∑ i ∈ s, X i ω) / #s ≤ Q[Y] ∧
        ENNReal.ofReal z ≤ #s * rateFunction Y Q ((∑ i ∈ s, X i ω) / #s)} ≤ exp (-z) := by
  obtain ⟨h_indep', hX', hY'⟩ := h_indep.neg_of_mgfDominatedOn_Iic hX hY
  have h := h_indep'.measureReal_integral_le_and_le_card_mul_rateFunction_le_exp hX' hY' z
  have h_rate (y : ℝ) : rateFunction (fun ω ↦ -Y ω) Q y = rateFunction Y Q (-y) := by
    rw [← Pi.neg_def, rateFunction_neg]
  simpa only [sum_neg_distrib, neg_div, integral_neg, neg_le_neg_iff, h_rate, neg_neg] using h

/-- **Two-sided deviations of the empirical mean, measured by the rate function.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.univ` by an integrable random
variable `Y` under a probability measure `Q`, with empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`, and
every real `z`, `P(z ≤ #s I(μ̂)) ≤ 2 exp (-z)`, where `I` is the rate function of `Y`. -/
theorem iIndepFun.measureReal_le_card_mul_rateFunction_le_two_mul_exp [IsProbabilityMeasure Q]
    (h_indep : iIndepFun X P) (hX : ∀ i ∈ s, MGFDominatedOn (X i) P Y Q Set.univ)
    (hY : Integrable Y Q) (z : ℝ) :
    P.real {ω | ENNReal.ofReal z ≤ #s * rateFunction Y Q ((∑ i ∈ s, X i ω) / #s)} ≤
      2 * exp (-z) := by
  have := h_indep.isProbabilityMeasure
  have h_up := h_indep.measureReal_integral_le_and_le_card_mul_rateFunction_le_exp
    (fun i hi ↦ (hX i hi).mono (Set.subset_univ _)) hY z
  have h_low := h_indep.measureReal_le_integral_and_le_card_mul_rateFunction_le_exp
    (fun i hi ↦ (hX i hi).mono (Set.subset_univ _)) hY z
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans ((add_le_add h_up h_low).trans_eq (two_mul _).symm))
  rcases le_total Q[Y] ((∑ i ∈ s, X i ω) / #s) with h | h
  · exact Or.inl ⟨h, hω⟩
  · exact Or.inr ⟨h, hω⟩

/-! ### From an upper tail bound to the events of the KL-UCB analysis -/

/-- **The events of the analysis of a suboptimal arm, for one sample size.** Let `S` be a real
random variable under a probability measure `P` (the sum of `s` rewards), let `f` be antitone on
`Set.Iic c` (a divergence `f(·) = d(·, c)` to a level `c`), and let `a ≤ c` with
`f(a) = ENNReal.ofReal D` and `L ≥ 0`. If `P(s a ≤ S) ≤ B`, then the probability that `s = 0`, or
`c ≤ S / s`, or `f(S / s) ≤ L / s` is at most `1` if `s D ≤ L`, and at most `B` otherwise: off the
upper tail, `S / s < a ≤ c`, so `f(S / s) ≥ D > L / s`. This is the per-term bound of
[LS, Lemma 10.8]. -/
theorem measureReal_eq_zero_or_le_div_or_apply_div_le_le_ite [IsZeroOrProbabilityMeasure P]
    {S : Ω → ℝ} {f : ℝ → ℝ≥0∞} {a c D L B : ℝ} {s : ℕ} (hf : AntitoneOn f (Set.Iic c))
    (hac : a ≤ c) (hfa : f a = ENNReal.ofReal D) (hL : 0 ≤ L)
    (h_tail : P.real {ω | s * a ≤ S ω} ≤ B) :
    P.real {ω | s = 0 ∨ c ≤ S ω / s ∨ f (S ω / s) ≤ ENNReal.ofReal (L / s)} ≤
      if s * D ≤ L then 1 else B := by
  split_ifs with hsD
  · exact measureReal_le_one
  have hs : s ≠ 0 := by
    rintro rfl
    simp only [CharP.cast_eq_zero, zero_mul] at hsD
    exact hsD hL
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
  -- off the upper tail, `S / s < a ≤ c`, so that `D ≤ f(S / s)` and `L / s < D`
  refine le_trans (measureReal_mono fun ω hω ↦ ?_) h_tail
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra! hlt
  have hx : S ω / s < a := by rwa [div_lt_iff₀ hs', mul_comm]
  rcases hω with h0 | hcx | hf_le
  · exact hs h0
  · linarith
  · refine hsD ?_
    have h1 : f a ≤ f (S ω / s) :=
      hf (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hac) hx.le
    rw [hfa] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans hf_le)
    rw [le_div_iff₀ hs'] at h2
    linarith

end ProbabilityTheory
