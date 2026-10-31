/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import LMLExplore.Probability.Distributions.Bernoulli
public import TauCeti.InformationTheory.KullbackLeibler.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Pinsker
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The binary relative entropy

The binary relative entropy `d(p, q)` is the Kullback–Leibler divergence between the Bernoulli
laws of means `p` and `q`. For `p, q ∈ [0, 1]` it is
`d(p, q) = p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`, with the conventions `0 log 0 = 0`
and `d(p, q) = ∞` when `q ∈ {0, 1}` and `p ≠ q`. It is the rate function of the Chernoff bounds
for `[0, 1]`-valued random variables, and the quantity in the KL-UCB index and in the
Lai–Robbins lower bound for Bernoulli bandits.

We define `klBer p q : ℝ≥0∞` as `klDiv` of the two Bernoulli laws on `{0, 1} ⊆ ℝ`, so that it
takes the value `∞` exactly where `d(p, q)` does, and the real-valued `klBerReal p q` by the
closed form above. For `p, q ∈ [0, 1]`, the two agree wherever `klBer p q` is finite.

The upper confidence level `U(p, c)` is the largest `q ∈ [p, 1]` with `d(p, q) ≤ c`: evaluated at
an empirical mean `p` and an exploration level `c` divided by a number of samples, it is the index
of the KL-UCB algorithm, and the Chernoff bounds in relative-entropy form control the probability
that it lies below the true mean.

## Main definitions

* `LMLExplore.klBer p q`: the binary relative entropy in `ℝ≥0∞`, the arguments being clamped to
  `[0, 1]`.
* `LMLExplore.klBerReal p q`: the real number `p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`.
* `LMLExplore.klUpper p c`: the upper confidence level `U(p, c) = max {q ∈ [p, 1] | d(p, q) ≤ c}`
  of the KL-UCB algorithm, for `c : ℝ≥0∞`.

## Main statements

* `LMLExplore.klDiv_bernoulliMeasure`: `D(Ber(1, 0, p), Ber(1, 0, q)) = klBer p q`.
* `LMLExplore.klBer_ne_top_iff`: for `p, q ∈ [0, 1]`, `klBer p q` is finite if and only if
  `q = 0 → p = 0` and `q = 1 → p = 1`.
* `LMLExplore.klBer_eq_ofReal_klBerReal`, `LMLExplore.toReal_klBer`: for `p, q ∈ [0, 1]`, where it
  is finite, `klBer p q` is given by the closed form `klBerReal p q`.
* `LMLExplore.klBer_eq_zero_iff`: for `p, q ∈ [0, 1]`, `klBer p q = 0` if and only if `p = q`.
* `LMLExplore.klBer_one_sub_one_sub`, `LMLExplore.klBerReal_one_sub_one_sub`:
  `d(1 - p, 1 - q) = d(p, q)`.
* `LMLExplore.ofReal_two_mul_sq_le_klBer`, `LMLExplore.two_mul_sq_le_klBerReal`: Pinsker's
  inequality `2 (p - q)² ≤ d(p, q)` for `p, q ∈ [0, 1]`.
* `LMLExplore.klBer_le_ofReal_sq_sub_div`, `LMLExplore.klBerReal_le_sq_sub_div`: the reverse
  bound `d(p, q) ≤ (p - q)² / (q (1 - q))` for `p ∈ [0, 1]` and `q ∈ (0, 1)`.
* `LMLExplore.continuousOn_klBer`: `d` is continuous on `[0, 1] × (0, 1)`.
* `LMLExplore.strictMonoOn_klBer`, `LMLExplore.strictAntiOn_klBer`: for `p ∈ [0, 1]`,
  `q ↦ d(p, q)` is strictly increasing on `[p, 1]` and strictly decreasing on `[0, p]`;
  `LMLExplore.klBer_le_max` is the resulting quasi-convexity in `q`.
* `LMLExplore.antitoneOn_klBer_left`: `p ↦ d(p, q)` is antitone on `(-∞, q]`.
* `LMLExplore.lowerSemicontinuous_klBer`, `LMLExplore.measurable_klBer`: `d` is jointly lower
  semicontinuous and measurable.
* `LMLExplore.le_klUpper_iff`: for `q ∈ [p, 1]`, `q ≤ U(p, c)` if and only if `d(p, q) ≤ c`;
  `LMLExplore.klUpper_mem_Icc` and `LMLExplore.klBer_klUpper_le` say that the maximum is attained.
* `LMLExplore.le_klUpper_iff_of_le_one`: for `p ≤ 1` and every real `r`, `r ≤ U(p, c)` if and only
  if `r ≤ p`, or `r ≤ 1` and `d(p, r) ≤ c`; `LMLExplore.le_or_klBer_le_of_le_klUpper` is the
  forward direction for every real `p`.
* `LMLExplore.klUpper_mono`, `LMLExplore.measurable_klUpper`: `U` is monotone in both arguments
  and jointly measurable.
* `LMLExplore.klUpper_le_min`: `U(p, c) ≤ min 1 (p + √(c / 2))`, by Pinsker's inequality.
* `LMLExplore.klUpper_zero`, `LMLExplore.klUpper_one_left`, `LMLExplore.tendsto_klUpper_nhds_top`:
  `U(p, 0) = p`, `U(1, c) = 1` and `U(p, c) → 1` as `c → ∞`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Definition 10.1, Lemma 10.2, Algorithm 8 and Theorem 14.1.
* A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and beyond*,
  COLT 2011, for the upper confidence level `U(p, c)`.
* The derivative, monotonicity and quasi-convexity proofs are adapted from the formalization in
  the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`).
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Real unitInterval Filter Topology
open scoped ENNReal NNReal

namespace LMLExplore

/-- The **binary relative entropy** `d(p, q)`: the Kullback–Leibler divergence between the
Bernoulli laws on `{0, 1} ⊆ ℝ` with means `p` and `q`, the arguments being first clamped to
`[0, 1]` by `Set.projIcc`. For `p, q ∈ [0, 1]` it is
`p log (p / q) + (1 - p) log ((1 - p) / (1 - q))` when this is finite, and `∞` when `q ∈ {0, 1}`
and `p ≠ q`. -/
noncomputable def klBer (p q : ℝ) : ℝ≥0∞ :=
  klDiv Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one p)
    Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one q)

/-- The real-valued binary relative entropy `p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`.
For `p, q ∈ [0, 1]` it is the value of `klBer p q` whenever the latter is finite
(`LMLExplore.toReal_klBer`). -/
noncomputable def klBerReal (p q : ℝ) : ℝ :=
  p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

variable {p q : ℝ}

/-- The relative entropy between two real Bernoulli laws on `{0, 1}` is the binary relative
entropy of their parameters. -/
@[simp]
theorem klDiv_bernoulliMeasure (p q : I) :
    klDiv Ber((1 : ℝ), 0, p) Ber((1 : ℝ), 0, q) = klBer p q := by
  simp [klBer]

theorem klBer_def (p q : ℝ) :
    klBer p q = klDiv Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one p)
      Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one q) := by
  rw [klBer]

theorem klBerReal_def (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  rw [klBerReal]

/-- On `[0, 1]`, `klBer p q` is the relative entropy of the Bernoulli laws of parameters `p`
and `q`. -/
theorem klBer_of_mem_Icc (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    klBer p q = klDiv Ber((1 : ℝ), 0, ⟨p, hp⟩) Ber((1 : ℝ), 0, ⟨q, hq⟩) := by
  rw [klBer_def, Set.projIcc_of_mem _ hp, Set.projIcc_of_mem _ hq]

@[simp]
theorem klBer_self (p : ℝ) : klBer p p = 0 := by
  rw [klBer_def, klDiv_self]

@[simp]
theorem klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  simp [klBerReal_def]

/-- `d(1, q) = -log q`. -/
@[simp]
theorem klBerReal_one_left (q : ℝ) : klBerReal 1 q = -log q := by
  simp [klBerReal_def]

/-- For `p, q ∈ [0, 1]`, `klBer p q` is finite if and only if `p` vanishes when `q` does and
`p = 1` when `q = 1`. -/
theorem klBer_ne_top_iff (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    klBer p q ≠ ∞ ↔ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  rw [klBer_of_mem_Icc hp hq, klDiv_ne_top_iff,
    and_iff_left (integrable_bernoulliMeasure _ _ _ _),
    bernoulliMeasure_absolutelyContinuous_iff one_ne_zero]
  simp [← Subtype.coe_inj]

/-- For `p, q ∈ [0, 1]`, `klBer p q = ∞` exactly when `q ∈ {0, 1}` and `p ≠ q`. -/
theorem klBer_eq_top_iff (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    klBer p q = ∞ ↔ q = 0 ∧ p ≠ 0 ∨ q = 1 ∧ p ≠ 1 := by
  rw [← not_iff_not, ← ne_eq, klBer_ne_top_iff hp hq]
  tauto

/-- The binary relative entropy is finite when the second argument lies in `(0, 1)`. -/
theorem klBer_ne_top (hq : q ∈ Set.Ioo 0 1) : klBer p q ≠ ∞ := by
  rw [klBer_def, Set.projIcc_of_mem _ (Set.Ioo_subset_Icc_self hq)]
  exact klDiv_ne_top_iff.2 ⟨bernoulliMeasure_absolutelyContinuous
    (fun h ↦ absurd (congrArg Subtype.val h) hq.1.ne')
    (fun h ↦ absurd (congrArg Subtype.val h) hq.2.ne), integrable_bernoulliMeasure _ _ _ _⟩

/-- For `p, q ∈ [0, 1]`, where it is finite, the real part of `klBer p q` is the closed form
`klBerReal p q = p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`. -/
theorem toReal_klBer (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) (h : klBer p q ≠ ∞) :
    (klBer p q).toReal = klBerReal p q := by
  obtain ⟨h0, h1⟩ := (klBer_ne_top_iff hp hq).1 h
  rw [klBer_of_mem_Icc hp hq] at h ⊢
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 h
  rw [toReal_klDiv hac hint, integral_bernoulliMeasure]
  simp only [probReal_univ, add_sub_cancel_right, smul_eq_mul, klBerReal_def]
  congr 1
  · rcases eq_or_ne q 0 with rfl | hq0
    · simp [h0 rfl]
    rw [Measure.llr_eq_log_real_div_real_singleton _ _ _
      (by simpa [← Subtype.coe_inj] using hq0) (measure_ne_top _ _)]
    simp
  · rcases eq_or_ne q 1 with rfl | hq1
    · simp [h1 rfl]
    have hν : Ber((1 : ℝ), 0, ⟨q, hq⟩) {0} ≠ 0 := by
      rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton 0) (by norm_num) rfl,
        Ne, ENNReal.coe_eq_zero, unitInterval.toNNReal_eq_zero, symm_eq_zero]
      exact fun h ↦ hq1 (congrArg Subtype.val h)
    rw [Measure.llr_eq_log_real_div_real_singleton _ _ _ hν (measure_ne_top _ _)]
    simp

/-- **Closed form of the binary relative entropy**: for `p, q ∈ [0, 1]`, where it is finite,
`klBer p q` is `p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`. -/
theorem klBer_eq_ofReal_klBerReal (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (h : klBer p q ≠ ∞) : klBer p q = ENNReal.ofReal (klBerReal p q) := by
  rw [← toReal_klBer hp hq h, ENNReal.ofReal_toReal h]

/-- **Pinsker's inequality** for Bernoulli laws: `2 (p - q)² ≤ d(p, q)` for `p, q ∈ [0, 1]`. -/
theorem ofReal_two_mul_sq_le_klBer (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klBer p q := by
  have h := TauCeti.two_mul_sq_measureReal_sub_le_klDiv (μ := Ber((1 : ℝ), 0, ⟨p, hp⟩))
    (ν := Ber((1 : ℝ), 0, ⟨q, hq⟩)) (measurableSet_singleton 1)
  rwa [bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton 1) rfl
      (by norm_num), bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton 1) rfl
      (by norm_num), ← klBer_of_mem_Icc hp hq] at h

/-- **Pinsker's inequality** for the real-valued binary relative entropy: for `p, q ∈ [0, 1]`, where
`klBer p q` is finite, `2 (p - q)² ≤ klBerReal p q`. -/
theorem two_mul_sq_le_klBerReal (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (h : klBer p q ≠ ∞) : 2 * (p - q) ^ 2 ≤ klBerReal p q := by
  rw [← toReal_klBer hp hq h]
  exact (ENNReal.ofReal_le_iff_le_toReal h).1 (ofReal_two_mul_sq_le_klBer hp hq)

/-- For `p, q ∈ [0, 1]`, the real-valued binary relative entropy is nonnegative where `klBer p q`
is finite. -/
theorem klBerReal_nonneg (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) (h : klBer p q ≠ ∞) :
    0 ≤ klBerReal p q :=
  (by positivity : (0 : ℝ) ≤ 2 * (p - q) ^ 2).trans (two_mul_sq_le_klBerReal hp hq h)

/-- On `[0, 1]`, the binary relative entropy vanishes only on the diagonal. -/
theorem klBer_eq_zero_iff (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    klBer p q = 0 ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ klBer_self p⟩
  have := ofReal_two_mul_sq_le_klBer hp hq
  rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  nlinarith [sq_nonneg (p - q)]

/-- The binary relative entropy is at most the `χ²`-divergence of the two Bernoulli laws:
for `p ∈ [0, 1]` and `q ∈ (0, 1)`, `klBerReal p q ≤ (p - q)² / (q (1 - q))`. -/
theorem klBerReal_le_sq_sub_div (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Ioo 0 1) :
    klBerReal p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  have key {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a * log (a / b) ≤ a * (a / b - 1) := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    exact mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by positivity)) ha.le
  have hq' : 0 < 1 - q := sub_pos.2 hq.2
  calc klBerReal p q ≤ p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) :=
        add_le_add (key hp.1 hq.1) (key (sub_nonneg.2 hp.2) hq')
    _ = (p - q) ^ 2 / (q * (1 - q)) := by
        have := hq.1.ne'
        have := hq'.ne'
        field_simp
        ring

/-- The binary relative entropy is at most the `χ²`-divergence of the two Bernoulli laws:
for `p ∈ [0, 1]` and `q ∈ (0, 1)`, `d(p, q) ≤ (p - q)² / (q (1 - q))`. -/
theorem klBer_le_ofReal_sq_sub_div (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Ioo 0 1) :
    klBer p q ≤ ENNReal.ofReal ((p - q) ^ 2 / (q * (1 - q))) := by
  rw [klBer_eq_ofReal_klBerReal hp (Set.Ioo_subset_Icc_self hq) (klBer_ne_top hq)]
  exact ENNReal.ofReal_le_ofReal (klBerReal_le_sq_sub_div hp hq)

/-- Clamping the arguments to `[0, 1]` does not change the binary relative entropy. -/
@[simp]
theorem klBer_projIcc (p q : ℝ) :
    klBer (Set.projIcc 0 1 zero_le_one p) (Set.projIcc 0 1 zero_le_one q) = klBer p q := by
  simp only [klBer_def, Set.projIcc_val]

/-- The binary relative entropy is invariant under exchanging the roles of the two outcomes:
`d(1 - p, 1 - q) = d(p, q)`. -/
@[simp]
theorem klBer_one_sub_one_sub (p q : ℝ) : klBer (1 - p) (1 - q) = klBer p q := by
  have h (r : I) : Ber((1 : ℝ), 0, σ r) = Ber((1 : ℝ), 0, r).map (1 - ·) := by
    rw [map_bernoulliMeasure, bernoulliMeasure_symm]
    simp
  rw [klBer_def, klBer_def, ← symm_projIcc, ← symm_projIcc, h, h]
  exact klDiv_map_measurableEmbedding _ _ (MeasurableEquiv.subLeft (1 : ℝ)).measurableEmbedding

/-- The real-valued binary relative entropy is invariant under exchanging the roles of the two
outcomes. -/
@[simp]
theorem klBerReal_one_sub_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  rw [klBerReal_def, klBerReal_def, sub_sub_cancel, sub_sub_cancel, add_comm]

/-! ### Continuity and monotonicity -/

/-- Away from `q ∈ {0, 1}`, `klBerReal p q` is the binary cross-entropy
`-(p log q + (1 - p) log (1 - q))` minus the binary entropy of `p`. -/
theorem klBerReal_eq_neg_binEntropy_sub (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = -binEntropy p - (p * log q + (1 - p) * log (1 - q)) := by
  have key {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * log a - a * log b := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rw [log_div ha hb, mul_sub]
  rw [klBerReal_def, key hq0, key (sub_ne_zero.2 hq1.symm)]
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  ring

/-- The real-valued binary relative entropy is jointly continuous on `ℝ × (0, 1)`. -/
theorem continuousOn_klBerReal :
    ContinuousOn (Function.uncurry klBerReal) (Set.univ ×ˢ Set.Ioo 0 1) := by
  have hlog : ContinuousOn (fun x : ℝ × ℝ ↦ log x.2) (Set.univ ×ˢ Set.Ioo 0 1) :=
    continuous_snd.continuousOn.log fun x hx ↦ hx.2.1.ne'
  have hlog' : ContinuousOn (fun x : ℝ × ℝ ↦ log (1 - x.2)) (Set.univ ×ˢ Set.Ioo 0 1) :=
    (continuous_const.sub continuous_snd).continuousOn.log fun x hx ↦ (sub_pos.2 hx.2.2).ne'
  refine ContinuousOn.congr (f := fun x : ℝ × ℝ ↦
      -binEntropy x.1 - (x.1 * log x.2 + (1 - x.1) * log (1 - x.2))) ?_
    fun x hx ↦ klBerReal_eq_neg_binEntropy_sub hx.2.1.ne' hx.2.2.ne
  exact (binEntropy_continuous.comp continuous_fst).neg.continuousOn.sub
    ((continuous_fst.continuousOn.mul hlog).add
      ((continuous_const.sub continuous_fst).continuousOn.mul hlog'))

/-- The binary relative entropy is jointly continuous on `[0, 1] × (0, 1)`. -/
theorem continuousOn_klBer :
    ContinuousOn (Function.uncurry klBer) (Set.Icc 0 1 ×ˢ Set.Ioo 0 1) := by
  refine (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_klBerReal.mono
    (Set.prod_mono (Set.subset_univ _) subset_rfl))).congr fun x hx ↦ ?_
  exact klBer_eq_ofReal_klBerReal hx.1 (Set.Ioo_subset_Icc_self hx.2) (klBer_ne_top hx.2)

/-- The derivative of `q ↦ klBerReal p q` on `(0, 1)` is `(q - p) / (q (1 - q))`. -/
theorem hasDerivAt_klBerReal (p : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    HasDerivAt (klBerReal p) ((q - p) / (q * (1 - q))) q := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.2 hq.2).ne'
  have h : HasDerivAt (fun x ↦ -binEntropy p - (p * log x + (1 - p) * log (1 - x)))
      (-(p * q⁻¹ + (1 - p) * (-1 / (1 - q)))) q :=
    (((hasDerivAt_log hq0).const_mul p).add
      ((((hasDerivAt_id' q).const_sub 1).log hq1).const_mul (1 - p))).const_sub _
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp
    ring
  · filter_upwards [isOpen_Ioo.mem_nhds hq] with x hx
    exact klBerReal_eq_neg_binEntropy_sub hx.1.ne' hx.2.ne

/-- On the right of `p`, `q ↦ klBerReal p q` is strictly increasing on `(0, 1)`. -/
theorem strictMonoOn_klBerReal (p : ℝ) :
    StrictMonoOn (klBerReal p) (Set.Ici p ∩ Set.Ioo 0 1) := by
  have hint : interior (Set.Ici p ∩ Set.Ioo 0 1) = Set.Ioi p ∩ Set.Ioo 0 1 := by
    rw [interior_inter, interior_Ici, isOpen_Ioo.interior_eq]
  refine strictMonoOn_of_hasDerivWithinAt_pos ((convex_Ici p).inter (convex_Ioo 0 1))
    (f' := fun x ↦ (x - p) / (x * (1 - x)))
    (fun x hx ↦ (hasDerivAt_klBerReal p hx.2).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hasDerivAt_klBerReal p (hint ▸ hx).2).hasDerivWithinAt) fun x hx ↦ ?_
  rw [hint] at hx
  exact div_pos (sub_pos.2 hx.1) (mul_pos hx.2.1 (sub_pos.2 hx.2.2))

/-- On the left of `p`, `q ↦ klBerReal p q` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_klBerReal (p : ℝ) :
    StrictAntiOn (klBerReal p) (Set.Iic p ∩ Set.Ioo 0 1) := by
  have hint : interior (Set.Iic p ∩ Set.Ioo 0 1) = Set.Iio p ∩ Set.Ioo 0 1 := by
    rw [interior_inter, interior_Iic, isOpen_Ioo.interior_eq]
  refine strictAntiOn_of_hasDerivWithinAt_neg ((convex_Iic p).inter (convex_Ioo 0 1))
    (f' := fun x ↦ (x - p) / (x * (1 - x)))
    (fun x hx ↦ (hasDerivAt_klBerReal p hx.2).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hasDerivAt_klBerReal p (hint ▸ hx).2).hasDerivWithinAt) fun x hx ↦ ?_
  rw [hint] at hx
  exact div_neg_of_neg_of_pos (sub_neg.2 hx.1) (mul_pos hx.2.1 (sub_pos.2 hx.2.2))

/-- For `p ∈ [0, 1]`, `q ↦ klBer p q` is strictly increasing on `[p, 1]`. -/
theorem strictMonoOn_klBer (hp : p ∈ Set.Icc 0 1) : StrictMonoOn (klBer p) (Set.Icc p 1) := by
  intro q₁ hq₁ q₂ hq₂ h
  have hq₁' : q₁ ∈ Set.Icc 0 1 := ⟨hp.1.trans hq₁.1, hq₁.2⟩
  have hq₂' : q₂ ∈ Set.Icc 0 1 := ⟨hp.1.trans hq₂.1, hq₂.2⟩
  rcases hq₁.1.eq_or_lt with rfl | hpq₁
  · rw [klBer_self, pos_iff_ne_zero, ne_eq, klBer_eq_zero_iff hp hq₂']
    exact h.ne
  have hq₁01 : q₁ ∈ Set.Ioo 0 1 := ⟨hp.1.trans_lt hpq₁, h.trans_le hq₂.2⟩
  rcases hq₂.2.eq_or_lt with rfl | hq₂1
  · rw [(klBer_eq_top_iff hp hq₂').2 (Or.inr ⟨rfl, (hpq₁.trans hq₁01.2).ne⟩)]
    exact (klBer_ne_top hq₁01).lt_top
  have hq₂01 : q₂ ∈ Set.Ioo 0 1 := ⟨hq₁01.1.trans h, hq₂1⟩
  rw [klBer_eq_ofReal_klBerReal hp hq₁' (klBer_ne_top hq₁01),
    klBer_eq_ofReal_klBerReal hp hq₂' (klBer_ne_top hq₂01),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (klBerReal_nonneg hp hq₁' (klBer_ne_top hq₁01))]
  exact strictMonoOn_klBerReal p ⟨hq₁.1, hq₁01⟩ ⟨hq₂.1, hq₂01⟩ h

/-- For `p ∈ [0, 1]`, `q ↦ klBer p q` is strictly decreasing on `[0, p]`. -/
theorem strictAntiOn_klBer (hp : p ∈ Set.Icc 0 1) : StrictAntiOn (klBer p) (Set.Icc 0 p) := by
  intro q₁ hq₁ q₂ hq₂ h
  rw [← klBer_one_sub_one_sub p q₁, ← klBer_one_sub_one_sub p q₂]
  exact strictMonoOn_klBer ⟨sub_nonneg.2 hp.2, sub_le_self _ hp.1⟩
    ⟨sub_le_sub_left hq₂.2 1, sub_le_self _ hq₂.1⟩ ⟨sub_le_sub_left hq₁.2 1, sub_le_self _ hq₁.1⟩
    (sub_lt_sub_left h 1)

/-- **Quasi-convexity** of the binary relative entropy in its second argument: on an interval
`[q₁, q₂]`, `klBer p` is at most the larger of its values at the endpoints. -/
theorem klBer_le_max {q₁ q₂ : ℝ} (h₁ : q₁ ≤ q) (h₂ : q ≤ q₂) :
    klBer p q ≤ max (klBer p q₁) (klBer p q₂) := by
  rw [← klBer_projIcc p q, ← klBer_projIcc p q₁, ← klBer_projIcc p q₂]
  set p' := Set.projIcc 0 1 zero_le_one p
  have h₁' := Set.monotone_projIcc zero_le_one h₁
  have h₂' := Set.monotone_projIcc zero_le_one h₂
  set r := Set.projIcc 0 1 zero_le_one q
  set r₁ := Set.projIcc 0 1 zero_le_one q₁
  set r₂ := Set.projIcc 0 1 zero_le_one q₂
  rcases le_total (r : ℝ) p' with hqp | hpq
  · exact le_max_of_le_left ((strictAntiOn_klBer p'.2).antitoneOn ⟨r₁.2.1, h₁'.trans hqp⟩
      ⟨r.2.1, hqp⟩ h₁')
  · exact le_max_of_le_right ((strictMonoOn_klBer p'.2).monotoneOn ⟨hpq, r.2.2⟩
      ⟨hpq.trans h₂', r₂.2.2⟩ h₂')

/-- For every real `p`, `q ↦ klBer p q` is monotone on `[p, ∞)`. -/
theorem monotoneOn_klBer (p : ℝ) : MonotoneOn (klBer p) (Set.Ici p) := by
  intro q₁ hq₁ q₂ hq₂ h
  rw [← klBer_projIcc p q₁, ← klBer_projIcc p q₂]
  exact (strictMonoOn_klBer (Set.projIcc 0 1 zero_le_one p).2).monotoneOn
    ⟨Set.monotone_projIcc zero_le_one hq₁, (Set.projIcc 0 1 zero_le_one q₁).2.2⟩
    ⟨Set.monotone_projIcc zero_le_one hq₂, (Set.projIcc 0 1 zero_le_one q₂).2.2⟩
    (Set.monotone_projIcc zero_le_one h)

/-! ### Monotonicity in the first argument -/

/-- For `p, q ∉ {0, 1}`, the derivative of `p ↦ klBerReal p q` at `p` is the difference of
log-odds `(log p - log (1 - p)) - (log q - log (1 - q))`. -/
theorem hasDerivAt_klBerReal_left (hp0 : p ≠ 0) (hp1 : p ≠ 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (fun p ↦ klBerReal p q) (log p - log (1 - p) - (log q - log (1 - q))) p := by
  have h : HasDerivAt (fun x ↦ -binEntropy x - (x * log q + (1 - x) * log (1 - q)))
      (-(log (1 - p) - log p) - (1 * log q + -1 * log (1 - q))) p :=
    (hasDerivAt_binEntropy hp0 hp1).neg.sub
      (((hasDerivAt_id' p).mul_const _).add (((hasDerivAt_id' p).const_sub 1).mul_const _))
  rw [funext fun x ↦ klBerReal_eq_neg_binEntropy_sub (p := x) hq0 hq1]
  exact h.congr_deriv (by ring)

/-- For `q ∈ (0, 1)`, `p ↦ klBerReal p q` is strictly decreasing on `[0, q]`. -/
theorem strictAntiOn_klBerReal_left (hq : q ∈ Set.Ioo 0 1) :
    StrictAntiOn (fun p ↦ klBerReal p q) (Set.Icc 0 q) := by
  have hcont : Continuous fun p ↦ klBerReal p q :=
    continuousOn_klBerReal.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ ↦ ⟨trivial, hq⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 q) hcont.continuousOn
    (f' := fun p ↦ log p - log (1 - p) - (log q - log (1 - q))) (fun x hx ↦ ?_) fun x hx ↦ ?_
  all_goals rw [interior_Icc] at hx
  · exact (hasDerivAt_klBerReal_left hx.1.ne' (hx.2.trans hq.2).ne hq.1.ne'
      hq.2.ne).hasDerivWithinAt
  · have h₁ := log_lt_log hx.1 hx.2
    have h₂ := log_lt_log (sub_pos.2 hq.2) (sub_lt_sub_left hx.2 1)
    linarith

/-- For every real `q`, `p ↦ klBer p q` is antitone on `(-∞, q]`: moving the first argument
towards the second decreases the binary relative entropy. -/
theorem antitoneOn_klBer_left (q : ℝ) : AntitoneOn (fun p ↦ klBer p q) (Set.Iic q) := by
  -- The case of `p₁ ≤ p₂ ≤ q` in `[0, 1]`.
  have key {p₁ p₂ q : ℝ} (hp₁ : 0 ≤ p₁) (h₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ q) (hq : q ≤ 1) :
      klBer p₂ q ≤ klBer p₁ q := by
    have hp₁' : p₁ ∈ Set.Icc 0 1 := ⟨hp₁, h₁₂.trans (hp₂.trans hq)⟩
    have hp₂' : p₂ ∈ Set.Icc 0 1 := ⟨hp₁.trans h₁₂, hp₂.trans hq⟩
    rcases (hp₁.trans (h₁₂.trans hp₂)).eq_or_lt with rfl | hq0
    · rw [le_antisymm hp₂ (hp₁.trans h₁₂), le_antisymm (h₁₂.trans hp₂) hp₁]
    rcases hq.eq_or_lt with rfl | hq1
    · rcases hp₂.eq_or_lt with rfl | hp₂1
      · simp
      rw [(klBer_eq_top_iff hp₁' ⟨zero_le_one, le_rfl⟩).2
        (Or.inr ⟨rfl, (h₁₂.trans_lt hp₂1).ne⟩)]
      exact le_top
    have hq' : q ∈ Set.Ioo 0 1 := ⟨hq0, hq1⟩
    rw [klBer_eq_ofReal_klBerReal hp₁' (Set.Ioo_subset_Icc_self hq') (klBer_ne_top hq'),
      klBer_eq_ofReal_klBerReal hp₂' (Set.Ioo_subset_Icc_self hq') (klBer_ne_top hq')]
    exact ENNReal.ofReal_le_ofReal <| (strictAntiOn_klBerReal_left hq').antitoneOn
      ⟨hp₁, h₁₂.trans hp₂⟩ ⟨hp₁.trans h₁₂, hp₂⟩ h₁₂
  intro p₁ hp₁ p₂ hp₂ h
  simp only
  rw [← klBer_projIcc p₁ q, ← klBer_projIcc p₂ q]
  exact key (Set.projIcc 0 1 zero_le_one p₁).2.1 (Set.monotone_projIcc zero_le_one h)
    (Set.monotone_projIcc zero_le_one hp₂) (Set.projIcc 0 1 zero_le_one q).2.2

/-! ### Semicontinuity and measurability -/

/-- The binary relative entropy is jointly lower semicontinuous. -/
theorem lowerSemicontinuous_klBer : LowerSemicontinuous (Function.uncurry klBer) := by
  let B : ℝ → ProbabilityMeasure ℝ := fun p ↦
    ⟨Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one p), inferInstance⟩
  have hB : Continuous B := by
    refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.2 fun f ↦ ?_
    simp only [B, ProbabilityMeasure.coe_mk, integral_bernoulliMeasure, smul_eq_mul]
    have : Continuous fun p : ℝ ↦ (Set.projIcc 0 1 zero_le_one p : ℝ) :=
      continuous_subtype_val.comp continuous_projIcc
    fun_prop
  convert TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure.comp
    ((hB.comp continuous_fst).prodMk (hB.comp continuous_snd)) using 1
  ext ⟨p, q⟩
  -- The right-hand side is `klDiv (B p) (B q)` with the coercions of `B p` and `B q` unfolded,
  -- which `simp` does not reduce under the coercion to measures.
  exact klBer_def p q

/-- The binary relative entropy is jointly measurable. -/
theorem measurable_klBer : Measurable (Function.uncurry klBer) :=
  lowerSemicontinuous_klBer.measurable

@[fun_prop]
theorem _root_.Measurable.klBer {α : Type*} {mα : MeasurableSpace α} {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x ↦ klBer (f x) (g x) := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    measurable_klBer.comp (hf.prodMk hg)

/-! ### The upper confidence level -/

/-- The **upper confidence level** `U(p, c) = max {q ∈ [p, 1] | d(p, q) ≤ c}` of the KL-UCB
algorithm: the largest mean `q ≥ p` of a Bernoulli law within relative entropy `c` of the
Bernoulli law of mean `p`. For `p ≤ 1` the maximum is attained (`LMLExplore.klUpper_mem_Icc`,
`LMLExplore.klBer_klUpper_le`); for `p > 1` the set is empty and `klUpper p c = 0`. -/
noncomputable def klUpper (p : ℝ) (c : ℝ≥0∞) : ℝ :=
  sSup {q | q ∈ Set.Icc p 1 ∧ klBer p q ≤ c}

theorem klUpper_def (p : ℝ) (c : ℝ≥0∞) :
    klUpper p c = sSup {q | q ∈ Set.Icc p 1 ∧ klBer p q ≤ c} := by
  rw [klUpper]

variable {r : ℝ} {c c' : ℝ≥0∞}

/-- For `p ≤ 1`, `klUpper p c` belongs to the set it is the supremum of. -/
private lemma klUpper_mem (hp : p ≤ 1) (c : ℝ≥0∞) :
    klUpper p c ∈ {q | q ∈ Set.Icc p 1 ∧ klBer p q ≤ c} := by
  have hclosed : IsClosed {q | q ∈ Set.Icc p 1 ∧ klBer p q ≤ c} := isClosed_Icc.inter
    ((lowerSemicontinuous_klBer.comp (continuous_const.prodMk continuous_id)).isClosed_preimage c)
  rw [klUpper_def]
  exact hclosed.csSup_mem ⟨p, ⟨le_rfl, hp⟩, by simp⟩ ⟨1, fun q hq ↦ hq.1.2⟩

/-- For `p ≤ 1`, the upper confidence level lies in `[p, 1]`. -/
theorem klUpper_mem_Icc (hp : p ≤ 1) (c : ℝ≥0∞) : klUpper p c ∈ Set.Icc p 1 :=
  (klUpper_mem hp c).1

/-- For `p ≤ 1`, the upper confidence level is at relative entropy at most `c` from `p`:
`d(p, U(p, c)) ≤ c`. -/
theorem klBer_klUpper_le (hp : p ≤ 1) (c : ℝ≥0∞) : klBer p (klUpper p c) ≤ c :=
  (klUpper_mem hp c).2

/-- **Characterization of the upper confidence level**: a point `q ∈ [p, 1]` is at most
`klUpper p c` if and only if `d(p, q) ≤ c`. -/
theorem le_klUpper_iff (hq : q ∈ Set.Icc p 1) : q ≤ klUpper p c ↔ klBer p q ≤ c := by
  have hp := hq.1.trans hq.2
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (monotoneOn_klBer p hq.1 (klUpper_mem_Icc hp c).1 h).trans (klBer_klUpper_le hp c)
  · rw [klUpper_def]
    exact le_csSup ⟨1, fun r hr ↦ hr.1.2⟩ ⟨hq, h⟩

/-- For `p > 1`, the set defining `klUpper p c` is empty and `klUpper p c = 0`. -/
theorem klUpper_of_one_lt (hp : 1 < p) (c : ℝ≥0∞) : klUpper p c = 0 := by
  have h : {q | q ∈ Set.Icc p 1 ∧ klBer p q ≤ c} = ∅ :=
    Set.eq_empty_of_forall_notMem fun q hq ↦ (hp.trans_le (hq.1.1.trans hq.1.2)).false
  rw [klUpper_def, h, Real.sSup_empty]

/-- The upper confidence level is monotone in both arguments. -/
theorem klUpper_mono {p p' : ℝ} (hp : p ≤ p') (hp' : p' ≤ 1) (hc : c ≤ c') :
    klUpper p c ≤ klUpper p' c' := by
  rcases le_total (klUpper p c) p' with h | h
  · exact h.trans (klUpper_mem_Icc hp' c').1
  rw [le_klUpper_iff ⟨h, (klUpper_mem_Icc (hp.trans hp') c).2⟩]
  exact (antitoneOn_klBer_left _ (klUpper_mem_Icc (hp.trans hp') c).1 h hp).trans
    ((klBer_klUpper_le (hp.trans hp') c).trans hc)

/-- The upper confidence level is monotone in the level `c`, for every real `p`. -/
theorem monotone_klUpper (p : ℝ) : Monotone (klUpper p) := by
  intro c c' hc
  rcases le_or_gt p 1 with hp | hp
  · exact klUpper_mono le_rfl hp hc
  · rw [klUpper_of_one_lt hp, klUpper_of_one_lt hp]

/-- `U(p, 0) = p`. -/
@[simp]
theorem klUpper_zero (hp : p ∈ Set.Icc 0 1) : klUpper p 0 = p := by
  have hU := klUpper_mem_Icc hp.2 0
  have h := klBer_klUpper_le hp.2 0
  rw [nonpos_iff_eq_zero, klBer_eq_zero_iff hp ⟨hp.1.trans hU.1, hU.2⟩] at h
  exact h.symm

/-- `U(1, c) = 1`. -/
@[simp]
theorem klUpper_one_left (c : ℝ≥0∞) : klUpper 1 c = 1 :=
  le_antisymm (klUpper_mem_Icc le_rfl c).2 (klUpper_mem_Icc le_rfl c).1

/-- `U(p, ∞) = 1` for `p ≤ 1`. -/
@[simp]
theorem klUpper_top (hp : p ≤ 1) : klUpper p ∞ = 1 :=
  le_antisymm (klUpper_mem_Icc hp ∞).2 ((le_klUpper_iff ⟨hp, le_rfl⟩).2 le_top)

/-- `U(p, c) → 1` as `c → ∞`. -/
theorem tendsto_klUpper_nhds_top (hp : p ≤ 1) : Tendsto (klUpper p) (𝓝 ∞) (𝓝 1) := by
  rcases hp.eq_or_lt with rfl | hp
  · exact tendsto_const_nhds.congr fun c ↦ (klUpper_one_left c).symm
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦
    Eventually.of_forall fun c ↦ (klUpper_mem_Icc hp.le c).2.trans_lt ha⟩
  -- A point `q ∈ [p, 1)` above `a`, at finite relative entropy from `p`.
  set q := max p ((max a 0 + 1) / 2)
  have hq0 : 0 < q := lt_max_of_lt_right (by positivity)
  have hq1 : q < 1 := max_lt hp (by linarith [max_lt ha one_pos])
  have haq : a < q := lt_max_of_lt_right (by linarith [le_max_left a 0])
  filter_upwards [Ioi_mem_nhds (klBer_ne_top (p := p) ⟨hq0, hq1⟩).lt_top] with c hc
  exact haq.trans_le ((le_klUpper_iff ⟨le_max_left _ _, hq1.le⟩).2 (le_of_lt hc))

/-- **Pinsker bound on the upper confidence level**: the KL-UCB index is at most the Hoeffding
index, `U(p, c) ≤ min 1 (p + √(c / 2))`. -/
theorem klUpper_le_min (hp : p ∈ Set.Icc 0 1) (c : ℝ≥0) :
    klUpper p c ≤ min 1 (p + √((c : ℝ) / 2)) := by
  have hU := klUpper_mem_Icc hp.2 c
  refine le_min hU.2 ?_
  have h := (ofReal_two_mul_sq_le_klBer hp ⟨hp.1.trans hU.1, hU.2⟩).trans (klBer_klUpper_le hp.2 c)
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal] at h
  have : klUpper p c - p ≤ √((c : ℝ) / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- For `p ≤ 1`, `r ≤ klUpper p c` if and only if `r ≤ p`, or `r ≤ 1` and `d(p, r) ≤ c`. -/
theorem le_klUpper_iff_of_le_one (hp : p ≤ 1) :
    r ≤ klUpper p c ↔ r ≤ p ∨ r ≤ 1 ∧ klBer p r ≤ c := by
  rcases le_or_gt r p with hrp | hrp
  · exact iff_of_true (hrp.trans (klUpper_mem_Icc hp c).1) (Or.inl hrp)
  rw [or_iff_right hrp.not_ge]
  refine ⟨fun h ↦ ?_, fun h ↦ (le_klUpper_iff ⟨hrp.le, h.1⟩).2 h.2⟩
  have hr1 := h.trans (klUpper_mem_Icc hp c).2
  exact ⟨hr1, (le_klUpper_iff ⟨hrp.le, hr1⟩).1 h⟩

/-- For every real `p`, if `r ≤ klUpper p c` then `r ≤ p`, or `r ≤ 1` and `d(p, r) ≤ c`. For
`p ≤ 1` this is one direction of `LMLExplore.le_klUpper_iff_of_le_one`; for `p > 1`,
`klUpper p c = 0 < p`. -/
theorem le_or_klBer_le_of_le_klUpper (h : r ≤ klUpper p c) : r ≤ p ∨ r ≤ 1 ∧ klBer p r ≤ c := by
  rcases le_or_gt p 1 with hp | hp
  · exact (le_klUpper_iff_of_le_one hp).1 h
  · rw [klUpper_of_one_lt hp] at h
    exact Or.inl (h.trans (zero_le_one.trans hp.le))

/-- The upper confidence level is jointly measurable in `(p, c)`. -/
theorem measurable_klUpper : Measurable (Function.uncurry klUpper) := by
  refine measurable_of_Ici fun r ↦ ?_
  have h : Function.uncurry klUpper ⁻¹' Set.Ici r =
      {x | x.1 ≤ 1} ∩ ({x | r ≤ x.1} ∪ {x | r ≤ 1} ∩ {x | klBer x.1 r ≤ x.2}) ∪
        {x | 1 < x.1} ∩ {_x | r ≤ 0} := by
    ext ⟨p, c⟩
    simp only [Set.mem_preimage, Function.uncurry_apply_pair, Set.mem_Ici, Set.mem_union,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    rcases le_or_gt p 1 with hp | hp
    · simp [le_klUpper_iff_of_le_one hp, hp, hp.not_gt]
    · simp [klUpper_of_one_lt hp, hp, hp.not_ge]
  rw [h]
  exact ((measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_le measurable_const measurable_fst).union ((MeasurableSet.const _).inter
      (measurableSet_le (measurable_fst.klBer measurable_const) measurable_snd)))).union
    ((measurableSet_lt measurable_const measurable_fst).inter (MeasurableSet.const _))

@[fun_prop]
theorem _root_.Measurable.klUpper {α : Type*} {mα : MeasurableSpace α} {f : α → ℝ}
    {g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ klUpper (f x) (g x) := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    measurable_klUpper.comp (hf.prodMk hg)

end LMLExplore
