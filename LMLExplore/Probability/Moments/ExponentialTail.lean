/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Probability.Moments.Basic

/-!
# Sums of independent random variables with exponential tails

A real random variable `X` has an *exponential tail* if `P(y ≤ X) ≤ exp (-y)` for every `y ≥ 0`,
as `log (1 / W)` does for a random variable `W` with `P(W ≤ w) ≤ w` on `[0, 1]`. Such a variable
has the moment generating function of a standard exponential law at most:
`E[exp (t X)] ≤ 1 / (1 - t)` for `0 ≤ t < 1`. For `k` independent such variables and `x ≥ k`,
the Chernoff bound at `t = 1 - k / x` then gives the tail bound of a sum of `k` standard
exponential variables, `P(x ≤ X₁ + ⋯ + X_k) ≤ (x / k) ^ k exp (k - x)` [LS, Exercise 5.16].

This bound is the source of the union-bound thresholds of generalized likelihood ratio stopping
rules [LS, Proposition 33.9]. Let `S i n` be independent processes indexed by `i ∈ ι`, with
`k = card ι`, and let `g` be monotone, such that for each `i`, the process `S i` crosses the
boundary `g n + y` at some `n` with probability at most `exp (-y)`. Then the probability that for
some indices `n : ι → ℕ`, the sum `∑ i, S i (n i)` exceeds `k g(∑ i, n i) + x` is at most
`(x / k) ^ k exp (k - x)`. In a bandit model, `S i n` is a statistic of the first `n` rewards of
the arm `i`, `n` is the vector of the numbers of pulls of the arms at some round, and `∑ i, n i`
is that round.

## Main statements

* `LMLExplore.lintegral_exp_mul_le_inv_one_sub`, `LMLExplore.integrable_exp_mul_of_measure_le`,
  `LMLExplore.mgf_le_inv_one_sub`: a random variable with an exponential tail has
  `E[exp (t X)] ≤ 1 / (1 - t)` for `0 ≤ t < 1`.
* `LMLExplore.measure_le_sum_le_div_pow_mul_exp`: for independent random variables `X i`,
  `i ∈ s`, with exponential tails and `x ≥ #s`,
  `P(x ≤ ∑ i ∈ s, X i) ≤ (x / #s) ^ #s exp (#s - x)` [LS, Exercise 5.16].
* `LMLExplore.measure_exists_card_mul_add_le_sum_le`: [LS, Proposition 33.9], the maximal form
  over all indices `n : ι → ℕ`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Exercise 5.16 and Proposition 33.9.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Finset

open scoped ENNReal

namespace LMLExplore

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {t : ℝ}

/-! ### One random variable with an exponential tail -/

/-- **Exponential moments from an exponential tail.** If `P(y ≤ X) ≤ exp (-y)` for every
`y ≥ 0`, then `E[exp (t X)] ≤ 1 / (1 - t)` for `0 ≤ t < 1`, the moment generating function of the
standard exponential law. -/
theorem lintegral_exp_mul_le_inv_one_sub (hXm : AEMeasurable X P)
    (hX : ∀ y, 0 ≤ y → P {ω | y ≤ X ω} ≤ ENNReal.ofReal (exp (-y))) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    ∫⁻ ω, ENNReal.ofReal (exp (t * X ω)) ∂P ≤ ENNReal.ofReal (1 - t)⁻¹ := by
  rcases ht0.eq_or_lt with rfl | ht
  · simp
  -- the layer cake formula for `exp (t X)`
  rw [lintegral_eq_lintegral_meas_lt P (ae_of_all _ fun _ ↦ (exp_pos _).le)
    (hXm.const_mul t).exp]
  -- above the level `1`, the tail of `exp (t X)` is at most `u ^ (-1 / t)`
  have h_tail (u : ℝ) (hu : 1 < u) :
      P {ω | u < exp (t * X ω)} ≤ ENNReal.ofReal (1 * u ^ (-t⁻¹)) := by
    have hu0 : 0 < u := one_pos.trans hu
    calc P {ω | u < exp (t * X ω)}
    _ ≤ P {ω | log u / t ≤ X ω} := measure_mono fun ω (hω : u < exp (t * X ω)) ↦ by
      rw [Set.mem_ofPred_eq, div_le_iff₀ ht, mul_comm]
      exact ((log_lt_iff_lt_exp hu0).2 hω).le
    _ ≤ ENNReal.ofReal (exp (-(log u / t))) := hX _ (div_nonneg (log_nonneg hu.le) ht.le)
    _ = ENNReal.ofReal (1 * u ^ (-t⁻¹)) := by
      rw [one_mul, rpow_def_of_pos hu0, div_eq_mul_inv, ← mul_neg]
  -- split the levels at `1`: below, bound the probability by `1`; above, by `u ^ (-1 / t)`
  refine (lintegral_Ioi_measure_lt_le_of_le_rpow one_pos zero_le_one
    (neg_lt_neg ((one_lt_inv₀ ht).2 ht1)) h_tail).trans_eq ?_
  have h1t : 1 - t ≠ 0 := (sub_pos.2 ht1).ne'
  rw [one_rpow, one_mul, show -t⁻¹ + 1 = -(1 - t) / t by field_simp; ring]
  congr 1
  field_simp
  ring

/-- A random variable with an exponential tail, `P(y ≤ X) ≤ exp (-y)` for every `y ≥ 0`, has
exponential moments of every order `0 ≤ t < 1`. -/
theorem integrable_exp_mul_of_measure_le (hXm : AEMeasurable X P)
    (hX : ∀ y, 0 ≤ y → P {ω | y ≤ X ω} ≤ ENNReal.ofReal (exp (-y))) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    Integrable (fun ω ↦ exp (t * X ω)) P :=
  (lintegral_ofReal_ne_top_iff_integrable (hXm.const_mul t).exp.aestronglyMeasurable
    (ae_of_all _ fun _ ↦ (exp_pos _).le)).1
    ((lintegral_exp_mul_le_inv_one_sub hXm hX ht0 ht1).trans_lt ENNReal.ofReal_lt_top).ne

/-- **Moment generating function from an exponential tail.** If `P(y ≤ X) ≤ exp (-y)` for every
`y ≥ 0`, then `mgf X P t ≤ 1 / (1 - t)` for `0 ≤ t < 1`. -/
theorem mgf_le_inv_one_sub (hXm : AEMeasurable X P)
    (hX : ∀ y, 0 ≤ y → P {ω | y ≤ X ω} ≤ ENNReal.ofReal (exp (-y))) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    mgf X P t ≤ (1 - t)⁻¹ := by
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (exp_pos _).le)
    (hXm.const_mul t).exp.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (inv_nonneg.2 (sub_pos.2 ht1).le)
    (lintegral_exp_mul_le_inv_one_sub hXm hX ht0 ht1)

/-! ### Sums of independent random variables with exponential tails -/

/-- **Tail of a sum of independent variables with exponential tails** [LS, Exercise 5.16]. Let
`X i`, `i ∈ s`, be independent random variables with `P(y ≤ X i) ≤ exp (-y)` for every `y ≥ 0`.
Then for `x ≥ #s`, `P(x ≤ ∑ i ∈ s, X i) ≤ (x / #s) ^ #s exp (#s - x)`, the Chernoff bound for a
sum of `#s` independent standard exponential variables. The condition `x ≥ #s` cannot be dropped:
for `0 ≤ x < #s` the right-hand side is less than `1`, while `P(x ≤ ∑ i ∈ s, X i) = 1` for `x = 0`
and nonnegative variables. -/
theorem measure_le_sum_le_div_pow_mul_exp {X : ι → Ω → ℝ} (h_indep : iIndepFun X P)
    (hXm : ∀ i, Measurable (X i)) {s : Finset ι}
    (hX : ∀ i ∈ s, ∀ y, 0 ≤ y → P {ω | y ≤ X i ω} ≤ ENNReal.ofReal (exp (-y))) {x : ℝ}
    (hx : #s ≤ x) :
    P {ω | x ≤ ∑ i ∈ s, X i ω} ≤ ENNReal.ofReal ((x / #s) ^ #s * exp (#s - x)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · -- for no variables, the event `x ≤ 0` is sure for `x = 0` and impossible for `x > 0`
    simp only [Finset.card_empty, CharP.cast_eq_zero, pow_zero, one_mul, zero_sub,
      sum_empty] at hx ⊢
    rcases hx.eq_or_lt with rfl | hx
    · simp
    · simp [hx.not_ge]
  have hk : (0 : ℝ) < #s := mod_cast hs.card_pos
  have hx0 : 0 < x := hk.trans_le hx
  -- the Chernoff bound at `t = 1 - #s / x`
  set t := 1 - #s / x with ht
  have ht0 : 0 ≤ t := sub_nonneg.2 ((div_le_one hx0).2 hx)
  have ht1 : t < 1 := sub_lt_self _ (div_pos hk hx0)
  have h_int : ∀ i ∈ s, Integrable (fun ω ↦ exp (t * X i ω)) P := fun i hi ↦
    integrable_exp_mul_of_measure_le (hXm i).aemeasurable (hX i hi) ht0 ht1
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc P.real {ω | x ≤ ∑ i ∈ s, X i ω}
  _ ≤ exp (-t * x) * mgf (∑ i ∈ s, X i) P t := by
    simpa only [Finset.sum_apply] using
      measure_ge_le_exp_mul_mgf x ht0 (h_indep.integrable_exp_mul_sum hXm h_int)
  _ = exp (-t * x) * ∏ i ∈ s, mgf (X i) P t := by rw [h_indep.mgf_sum hXm]
  _ ≤ exp (-t * x) * ∏ _ ∈ s, (1 - t)⁻¹ := by
    gcongr with i hi
    · exact fun i _ ↦ mgf_nonneg
    · exact mgf_le_inv_one_sub (hXm i).aemeasurable (hX i hi) ht0 ht1
  _ = (x / #s) ^ #s * exp (#s - x) := by
    rw [prod_const, mul_comm (exp _), ht, sub_sub_cancel, inv_div]
    congr 2
    field_simp
    ring

/-- **Union-bound deviations of independent processes over all indices** [LS, Proposition 33.9].
Let `S i`, `i ∈ ι`, be independent real processes indexed by `ℕ`, with `k = card ι`, and let `g`
be monotone. Suppose that for each `i` and `y ≥ 0`, the probability that `g n + y ≤ S i n` for
some `n` is at most `exp (-y)`. Then for `x ≥ k`, the probability that
`k g(∑ i, n i) + x ≤ ∑ i, S i (n i)` for some indices `n : ι → ℕ` is at most
`(x / k) ^ k exp (k - x)`. -/
theorem measure_exists_card_mul_add_le_sum_le [Fintype ι] {S : ι → ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun i ω n ↦ S i n ω) P) (hSm : ∀ i n, Measurable (S i n))
    {g : ℕ → ℝ} (hg : Monotone g)
    (hS : ∀ i y, 0 ≤ y → P {ω | ∃ n, g n + y ≤ S i n ω} ≤ ENNReal.ofReal (exp (-y)))
    {x : ℝ} (hx : Fintype.card ι ≤ x) :
    P {ω | ∃ n : ι → ℕ, Fintype.card ι * g (∑ i, n i) + x ≤ ∑ i, S i (n i) ω} ≤
      ENNReal.ofReal ((x / Fintype.card ι) ^ Fintype.card ι * exp (Fintype.card ι - x)) := by
  -- the largest excess `S i n - g n` of the process `i` over the indices `n ≤ N`
  let sup (N : ℕ) (f : ℕ → ℝ) : ℝ := (range (N + 1)).sup' nonempty_range_add_one fun n ↦ f n - g n
  have h_sup (N : ℕ) : Measurable (sup N) :=
    Finset.measurable_range_sup'' fun n _ ↦ (measurable_pi_apply n).sub_const _
  set M : ℕ → ι → Ω → ℝ := fun N i ω ↦ sup N fun n ↦ S i n ω
  have hMm (N : ℕ) (i : ι) : Measurable (M N i) :=
    (h_sup N).comp (Measurable.of_eval fun n ↦ hSm i n)
  have hM_indep (N : ℕ) : iIndepFun (M N) P := h_indep.comp (fun _ ↦ sup N) fun _ ↦ h_sup N
  -- each excess has an exponential tail
  have hM (N : ℕ) (i : ι) (y : ℝ) (hy : 0 ≤ y) :
      P {ω | y ≤ M N i ω} ≤ ENNReal.ofReal (exp (-y)) := by
    have h_sub : {ω | y ≤ M N i ω} ⊆ {ω | ∃ n, g n + y ≤ S i n ω} := fun ω hω ↦ by
      obtain ⟨n, -, hn⟩ := exists_mem_eq_sup' nonempty_range_add_one fun n ↦ S i n ω - g n
      refine ⟨n, ?_⟩
      simp only [Set.mem_ofPred_eq, M, sup] at hω
      linarith
    exact (measure_mono h_sub).trans (hS i y hy)
  -- the event is the increasing union over `N` of its restrictions to the indices `n ≤ N`
  set E : ℕ → Set Ω := fun N ↦ {ω | ∃ n : ι → ℕ, (∀ i, n i ≤ N) ∧
    Fintype.card ι * g (∑ i, n i) + x ≤ ∑ i, S i (n i) ω}
  have hE_mono : Monotone E := fun N N' hN ω ⟨n, hnN, hω⟩ ↦ ⟨n, fun i ↦ (hnN i).trans hN, hω⟩
  have hE : {ω | ∃ n : ι → ℕ, Fintype.card ι * g (∑ i, n i) + x ≤ ∑ i, S i (n i) ω} =
      ⋃ N, E N := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨∑ i, n i, n, fun i ↦ single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (mem_univ i), hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  rw [hE, hE_mono.measure_iUnion]
  refine iSup_le fun N ↦ (measure_mono (t := {ω | x ≤ ∑ i, M N i ω}) ?_).trans
    (measure_le_sum_le_div_pow_mul_exp (hM_indep N) (hMm N) (fun i _ ↦ hM N i)
      (by rwa [card_univ]))
  rintro ω ⟨n, hnN, hω⟩
  -- on the event, `∑ i, S i (n i) ≤ ∑ i, M N i + k g(∑ i, n i)`, hence `x ≤ ∑ i, M N i`
  have h1 : ∑ i, (S i (n i) ω - g (n i)) ≤ ∑ i, M N i ω := sum_le_sum fun i _ ↦
    le_sup' (fun n ↦ S i n ω - g n) (mem_range.2 (Nat.lt_succ_of_le (hnN i)))
  have h2 : ∑ i, g (n i) ≤ ∑ _ : ι, g (∑ j, n j) := sum_le_sum fun i _ ↦
    hg (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i))
  rw [sum_sub_distrib] at h1
  rw [sum_const, card_univ, nsmul_eq_mul] at h2
  rw [Set.mem_ofPred_eq]
  linarith

end LMLExplore
