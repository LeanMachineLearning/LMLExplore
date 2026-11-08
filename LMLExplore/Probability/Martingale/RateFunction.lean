/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Martingale.MGFBound
public import LMLExplore.Probability.Moments.RateFunction

/-!
# Self-normalized deviations of selected variables, measured by the rate function

Let `ℱ` be a filtration on a standard Borel space, `X` a real process with `X k`
`ℱ (k + 1)`-measurable, and `w` a process of selection indicators in `{0, 1}` adapted to `ℱ`, so
that whether `X k` is selected is known before `X k` is drawn. After `t` rounds,
`N t = ∑ k < t, w k` variables have been selected, with sum `S t = ∑ k < t, w k X k` and mean
`μ̂ t = S t / N t`. Suppose that, given `ℱ k`, the moment generating function of `X k` is bounded
on the nonnegative parameters by that of a real random variable `Y` with mean `m` and rate
function `I` (the variables are *conditionally dominated above* by `Y`). Then the deviation
`N t I(μ̂ t)` of the selected mean above `m` is uniformly small along all the rounds
[GC11, Theorem 10]: for `x > 0` and `n ≥ 2`,
`P(∃ t, 1 ≤ N t ≤ n, m < μ̂ t, x ≤ N t I(μ̂ t)) ≤ e ⌈x log n⌉ exp (-x)`.
Since `N t ≤ t`, this contains the bound on the rounds `t ≤ n` of [GC11]. The same holds below
the mean for variables conditionally dominated below by `Y`.

The proof peels the possible numbers of selected variables along a geometric grid of ratio
`c > 1`. On the slice `c ^ k ≤ N t < c ^ (k + 1)`, the deviation `x ≤ N t I(μ̂ t)` forces
`I(μ̂ t) > x / c ^ (k + 1)`, and the exponential supermartingale of
`LMLExplore.measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound`, at a parameter `λ ≥ 0` with
`λ q - log E[exp (λ Y)] > x / c ^ (k + 1)` for a level `q ≤ μ̂ t`, bounds the probability of the
slice by `exp (-x / c)`. The rate function need not attain its supremum, and the levels at which
it exceeds `x / c ^ (k + 1)` need not have a least element, so the parameter is chosen for each
rational such level `q`; by lower semicontinuity every mean of the slice lies above one of them,
and the events attached to these levels form a countable directed family, whose union has
probability the supremum of theirs. With `⌊log n / log c⌋₊ + 1` slices this gives the bound
`(⌊log n / log c⌋₊ + 1) exp (-x / c)` for every ratio `c > 1`, and the ratio `c = x / (x - 1)`
gives [GC11, Theorem 10].

## Main statements

* `LMLExplore.measure_exists_le_sum_and_gt_and_lt_rateFunction_le`: the bound
  `P(∃ t, a ≤ N t, m < μ̂ t, r < I(μ̂ t)) ≤ exp (-a r)` on one slice.
* `LMLExplore.measure_exists_gt_and_le_mul_rateFunction_le_mul`,
  `LMLExplore.measure_exists_lt_and_le_mul_rateFunction_le_mul`: the peeling bound
  `(⌊log n / log c⌋₊ + 1) exp (-x / c)` for every ratio `c > 1`, above and below the mean.
* `LMLExplore.measure_exists_gt_and_le_mul_rateFunction_le`,
  `LMLExplore.measure_exists_lt_and_le_mul_rateFunction_le`: [GC11, Theorem 10], the bound
  `e ⌈x log n⌉ exp (-x)`, above and below the mean.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10 (for independent variables bounded in `[0, 1]`, with the binary
  relative entropy in place of the rate function).
* S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probability Surveys 17 (2020), for the exponential
  supermartingales of conditionally dominated variables.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set

open scoped ENNReal

namespace LMLExplore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {ℱ : Filtration ℕ mΩ} {X w : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

/-- **Time-uniform Chernoff bound with the rate function, for at least `a` selected variables.**
Let `X k` be `ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that
of `Y` on the nonnegative parameters given `ℱ k`, and let the selection indicators `w` be adapted
with values in `{0, 1}`. For `a > 0` and `r ≥ 0`, the probability that, at some round, at least `a`
variables are selected, with mean `μ̂` above the mean of `Y` and `r < I(μ̂)` for the rate function
`I` of `Y`, is at most `exp (-(a r))`. -/
theorem measure_exists_le_sum_and_gt_and_lt_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) :
    P {ω | ∃ n, a ≤ ∑ k ∈ range n, w k ω ∧
      Q[Y] < (∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω ∧
      ENNReal.ofReal r <
        rateFunction Y Q ((∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω)} ≤
      ENNReal.ofReal (exp (-(a * r))) := by
  -- the rational levels above the mean at which the rate function exceeds `r`, and the events
  -- that at least `a` variables are selected with mean above such a level
  let ι := {q : ℚ // Q[Y] < (q : ℝ) ∧ ENNReal.ofReal r < rateFunction Y Q q}
  let G : ι → Set Ω := fun q ↦ {ω | ∃ n, a ≤ ∑ k ∈ range n, w k ω ∧
    (q.1 : ℝ) ≤ (∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω}
  -- by lower semicontinuity, every mean of rate above `r` is above such a level
  have h_sub : {ω | ∃ n, a ≤ ∑ k ∈ range n, w k ω ∧
      Q[Y] < (∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω ∧
      ENNReal.ofReal r < rateFunction Y Q
        ((∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω)} ⊆ ⋃ q, G q := by
    rintro ω ⟨n, han, hm, hrate⟩
    have h_open : IsOpen (Ioi Q[Y] ∩ rateFunction Y Q ⁻¹' Ioi (ENNReal.ofReal r)) :=
      isOpen_Ioi.inter ((lowerSemicontinuous_rateFunction Y Q).isOpen_preimage _)
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (h_open.mem_nhds ⟨hm, hrate⟩)
    obtain ⟨q, hlq, hqy⟩ := exists_rat_btwn hl
    have hq := hlu ⟨hlq, hqy.trans hu⟩
    exact mem_iUnion.2 ⟨⟨q, hq.1, hq.2⟩, n, han, hqy.le⟩
  -- the events decrease with the level, so they form a directed family
  have h_dir : Directed (· ⊆ ·) G := by
    intro i j
    rcases le_total (i.1 : ℝ) j.1 with h | h
    · exact ⟨i, subset_rfl, fun ω ⟨n, hn, hq⟩ ↦ ⟨n, hn, h.trans hq⟩⟩
    · exact ⟨j, fun ω ⟨n, hn, hq⟩ ↦ ⟨n, hn, h.trans hq⟩, subset_rfl⟩
  -- each event is controlled by the exponential supermartingale at a well-chosen parameter
  have h_G (q : ι) : P (G q) ≤ ENNReal.ofReal (exp (-(a * r))) := by
    obtain ⟨q, hmq, hrq⟩ := q
    rw [rateFunction_eq_iSup_nonneg hY hmq.le, lt_biSup_iff] at hrq
    obtain ⟨t, ⟨ht, ht0⟩, hrt⟩ := hrq
    have hrt' : r < t * q - cgf Y Q t := ((ENNReal.ofReal_lt_ofReal_iff').1 hrt).1
    refine le_trans (measure_mono ?_)
      (measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound hX hψ hw hw01 cgf_zero
        ⟨mem_Ici.2 le_rfl, by simp [integrableExpSet]⟩ ⟨ht0, ht⟩ (a * r))
    rintro ω ⟨n, han, hq⟩
    refine ⟨n, ?_⟩
    have hN : 0 < ∑ k ∈ range n, w k ω := ha.trans_le han
    calc a * r
    _ ≤ a * (t * q - cgf Y Q t) := mul_le_mul_of_nonneg_left hrt'.le ha.le
    _ ≤ (∑ k ∈ range n, w k ω) * (t * q - cgf Y Q t) :=
      mul_le_mul_of_nonneg_right han (hr.trans hrt'.le)
    _ ≤ (∑ k ∈ range n, w k ω) *
        (t * ((∑ k ∈ range n, w k ω * X k ω) / ∑ k ∈ range n, w k ω) - cgf Y Q t) := by
      gcongr
    _ = t * ∑ k ∈ range n, w k ω * X k ω - (∑ k ∈ range n, w k ω) * cgf Y Q t := by
      field_simp
  calc _ ≤ P (⋃ q, G q) := measure_mono h_sub
  _ = ⨆ q, P (G q) := h_dir.measure_iUnion
  _ ≤ ENNReal.ofReal (exp (-(a * r))) := iSup_le h_G

/-- **Peeling bound for the self-normalized deviations above the mean.** Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonnegative parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, a ratio `c > 1`, `x > 0` and `n : ℕ`, the probability that `1 ≤ N t ≤ n`, `μ̂ t` is above
the mean of `Y` and `x ≤ N t I(μ̂ t)` at some round `t` is at most
`(⌊log n / log c⌋₊ + 1) exp (-x / c)`. -/
theorem measure_exists_gt_and_le_mul_rateFunction_le_mul
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) {c x : ℝ}
    (hc : 1 < c) (hx : 0 < x) (n : ℕ) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      (⌊log n / log c⌋₊ + 1 : ℕ) * ENNReal.ofReal (exp (-(x / c))) := by
  have hc0 : 0 < c := one_pos.trans hc
  -- the slice `c ^ k ≤ N t < c ^ (k + 1)`, on which the rate function exceeds `x / c ^ (k + 1)`
  let E : ℕ → Set Ω := fun k ↦ {ω | ∃ t, c ^ k ≤ ∑ k ∈ range t, w k ω ∧
    Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
    ENNReal.ofReal (x / c ^ (k + 1)) <
      rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)}
  have h_sub : {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ⊆
      ⋃ k ∈ range (⌊log n / log c⌋₊ + 1), E k := by
    rintro ω ⟨t, h1, hn, hm, hrate⟩
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near h1 hc
    refine mem_iUnion₂.2 ⟨k, ?_, t, hk, hm, ?_⟩
    · -- the slices meeting `N t ≤ n` are those with `c ^ k ≤ n`
      rw [Finset.mem_range, Nat.lt_succ_iff]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ (log_pos hc), ← log_pow]
      exact log_le_log (pow_pos hc0 k) (hk.trans hn)
    · -- `x ≤ N t I(μ̂ t)` with `N t < c ^ (k + 1)` forces `x / c ^ (k + 1) < I(μ̂ t)`
      by_contra! h
      have h' : ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) ≤
          ENNReal.ofReal (∑ k ∈ range t, w k ω) * ENNReal.ofReal (x / c ^ (k + 1)) := by
        gcongr
      refine (hrate.trans h').not_gt ?_
      rw [← ENNReal.ofReal_mul (zero_le_one.trans h1), ENNReal.ofReal_lt_ofReal_iff hx,
        ← mul_div_assoc, div_lt_iff₀ (pow_pos hc0 _)]
      exact mul_lt_mul_of_pos_right hk' hx |>.trans_eq (mul_comm _ _)
  calc _ ≤ P (⋃ k ∈ range (⌊log n / log c⌋₊ + 1), E k) := measure_mono h_sub
  _ ≤ ∑ k ∈ range (⌊log n / log c⌋₊ + 1), P (E k) := measure_biUnion_finset_le _ _
  _ ≤ ∑ k ∈ range (⌊log n / log c⌋₊ + 1), ENNReal.ofReal (exp (-(x / c))) := by
    refine sum_le_sum fun k _ ↦ ?_
    have h_eq : c ^ k * (x / c ^ (k + 1)) = x / c := by
      field_simp
      ring
    rw [← h_eq]
    exact measure_exists_le_sum_and_gt_and_lt_rateFunction_le hX hψ hw hw01 hY (pow_pos hc0 k)
      (by positivity)
  _ = (⌊log n / log c⌋₊ + 1 : ℕ) * ENNReal.ofReal (exp (-(x / c))) := by
    rw [sum_const, card_range, nsmul_eq_mul]

omit [StandardBorelSpace Ω] in
/-- The ratio `c = x / (x - 1)` turns the peeling bounds `(⌊log n / log c⌋₊ + 1) exp (-x / c)` into
the bound `e ⌈x log n⌉ exp (-x)` of [GC11, Theorem 10], for `x > 0` and `n ≥ 2`; for `x ≤ 1` this
bound is at least `1`. -/
private lemma measure_le_exp_one_mul_ceil_mul_exp {E : Set Ω} {x : ℝ} {n : ℕ} (hx : 0 < x)
    (hn : 1 < n)
    (hE : ∀ c, 1 < c → P E ≤ (⌊log n / log c⌋₊ + 1 : ℕ) * ENNReal.ofReal (exp (-(x / c)))) :
    P E ≤ ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)) := by
  have hlogn : 0 < log n := log_pos (by exact_mod_cast hn)
  rcases le_or_gt x 1 with hx1 | hx1
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ ⌈x * log n⌉₊ := by exact_mod_cast Nat.one_le_ceil_iff.2 (mul_pos hx hlogn)
    have h2 : 1 ≤ exp 1 * exp (-x) := by
      rw [← exp_add]
      exact one_le_exp (by linarith)
    calc (1 : ℝ) ≤ ⌈x * log n⌉₊ * (exp 1 * exp (-x)) := one_le_mul_of_one_le_of_one_le h1 h2
    _ = exp 1 * ⌈x * log n⌉₊ * exp (-x) := by ring
  have hx0 : 0 < x - 1 := by linarith
  have hc : 1 < x / (x - 1) := (one_lt_div hx0).2 (by linarith)
  -- `log (x / (x - 1)) = -log (1 - 1 / x) > 1 / x`
  have hlogc : 1 < x * log (x / (x - 1)) := by
    have h := log_lt_sub_one_of_pos (div_pos hx0 hx) ((div_lt_one hx).2 (by linarith)).ne
    rw [← inv_div, log_inv]
    have h_eq : (x - 1) / x - 1 = -(1 / x) := by
      field_simp
      ring
    rw [h_eq] at h
    have := mul_lt_mul_of_pos_left h hx
    rw [mul_neg, mul_one_div_cancel hx.ne'] at this
    linarith
  have hL : log n / log (x / (x - 1)) < x * log n := by
    rw [div_lt_iff₀ (log_pos hc)]
    nlinarith
  have hD : ((⌊log n / log (x / (x - 1))⌋₊ + 1 : ℕ) : ℝ) ≤ ⌈x * log n⌉₊ := by
    have h0 : 0 ≤ log n / log (x / (x - 1)) := div_nonneg hlogn.le (log_pos hc).le
    have h : (⌊log n / log (x / (x - 1))⌋₊ : ℝ) < ⌈x * log n⌉₊ :=
      (Nat.floor_le h0).trans_lt (hL.trans_le (Nat.le_ceil _))
    exact_mod_cast Nat.cast_lt.1 h
  refine (hE _ hc).trans ?_
  have hxc : x / (x / (x - 1)) = x - 1 := by
    field_simp
  rw [hxc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((⌊log n / log (x / (x - 1))⌋₊ + 1 : ℕ) : ℝ) * exp (-(x - 1))
  _ ≤ ⌈x * log n⌉₊ * exp (-(x - 1)) := mul_le_mul_of_nonneg_right hD (exp_pos _).le
  _ = exp 1 * ⌈x * log n⌉₊ * exp (-x) := by
    rw [mul_comm (exp 1), mul_assoc, ← exp_add]
    ring_nf

/-- **Self-normalized deviations above the mean** [GC11, Theorem 10]. Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonnegative parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, `x > 0` and `n ≥ 2`, the probability that `1 ≤ N t ≤ n`, `μ̂ t` is above the mean of `Y`
and `x ≤ N t I(μ̂ t)` at some round `t` is at most `e ⌈x log n⌉ exp (-x)`. -/
theorem measure_exists_gt_and_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) {x : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : 1 < n) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)) :=
  measure_le_exp_one_mul_ceil_mul_exp hx hn fun _ hc ↦
    measure_exists_gt_and_le_mul_rateFunction_le_mul hX hψ hw hw01 hY hc hx n

/-- **Peeling bound for the self-normalized deviations below the mean.** Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonpositive parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, a ratio `c > 1`, `x > 0` and `n : ℕ`, the probability that `1 ≤ N t ≤ n`, `μ̂ t` is below
the mean of `Y` and `x ≤ N t I(μ̂ t)` at some round `t` is at most
`(⌊log n / log c⌋₊ + 1) exp (-x / c)`. -/
theorem measure_exists_lt_and_le_mul_rateFunction_le_mul
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Iic 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) {c x : ℝ}
    (hc : 1 < c) (hx : 0 < x) (n : ℕ) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      (⌊log n / log c⌋₊ + 1 : ℕ) * ENNReal.ofReal (exp (-(x / c))) := by
  -- the deviations of `X` below the mean of `Y` are those of `-X` above the mean of `-Y`
  have hψ' (n : ℕ) : HasCondMGFBound (ℱ n) (ℱ.le n) (-X n) (cgf (-Y) Q)
      (Ici 0 ∩ integrableExpSet (-Y) Q) P := by
    refine (hψ n).neg.mono (fun t ⟨ht0, ht⟩ ↦ ⟨neg_nonpos.2 ht0, ?_⟩) fun t _ ↦ cgf_neg.ge
    simpa [integrableExpSet] using ht
  refine le_trans (measure_mono ?_) (measure_exists_gt_and_le_mul_rateFunction_le_mul
    (X := fun n ↦ -X n) (fun n ↦ (hX n).neg) hψ' hw hw01 hY.neg hc hx n)
  rintro ω ⟨t, h1, hn, hm, hrate⟩
  refine ⟨t, h1, hn, ?_, ?_⟩
  · simpa [integral_neg, neg_div] using hm
  · simpa [neg_div] using hrate

/-- **Self-normalized deviations below the mean** [GC11, Theorem 10]. Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonpositive parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, `x > 0` and `n ≥ 2`, the probability that `1 ≤ N t ≤ n`, `μ̂ t` is below the mean of `Y`
and `x ≤ N t I(μ̂ t)` at some round `t` is at most `e ⌈x log n⌉ exp (-x)`. -/
theorem measure_exists_lt_and_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Iic 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) {x : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : 1 < n) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)) :=
  measure_le_exp_one_mul_ceil_mul_exp hx hn fun _ hc ↦
    measure_exists_lt_and_le_mul_rateFunction_le_mul hX hψ hw hw01 hY hc hx n

end LMLExplore
