/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.Bernoulli
public import TauCeti.InformationTheory.KullbackLeibler.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Pinsker
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule

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

## Main definitions

* `LMLExplore.klBer p q`: the binary relative entropy in `ℝ≥0∞`, the arguments being clamped to
  `[0, 1]`.
* `LMLExplore.klBerReal p q`: the real number `p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`.

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

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Definition 10.1, Lemma 10.2 (b) and Theorem 14.1.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Real unitInterval
open scoped ENNReal

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

end LMLExplore
