/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TwoSample.Exponential
import LMLExplore.Probability.Distributions.Gamma
import LMLExplore.Probability.Kernel.Composition.MeasureComp
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.Measurability
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# The reverse information projection of two exponential observations is no finite mixture

Two independent observations have the laws `Exp(l₁)` and `Exp(l₂)`, and the null hypothesis is
the set of the products `Exp(l) ⊗ Exp(l)`, `l > 0`, of the two-sample test with a common nuisance
parameter of [HGLLA24]. The reverse information projection of `Exp(l₁) ⊗ Exp(l₂)` on the null is
the law under which the sum of the two observations has its law under `Exp(l₁) ⊗ Exp(l₂)` and,
given the sum `s`, the first observation is uniform on `[0, s]`
(`ProbabilityTheory.ripr_prod_expMeasure`, in `LMLExplore.EValues.TwoSample.Exponential`), a
continuous mixture of members of the null. For `l₁ ≠ l₂`, no finite combination of members of the
null is equal to it, against the conjecture of [HGLLA24, §5.2]; this refutation is
[EVR26, Note 28].

## Main statements

* `ProbabilityTheory.sum_smul_prod_expMeasure_ne_ripr`: no finite combination of members of the
  null is the reverse information projection.

## Implementation notes

A finite combination of the laws `Gamma(2, l)` has a density `∑ c l * l ^ 2 * x * exp (- l x)`,
which decays either too slowly or too fast at infinity compared to the density
`l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)` of the law of the sum under
`Exp(l₁) ⊗ Exp(l₂)`.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471, §5.2.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, paper project
  `RemyDegenne/evalues_research` (2026), Note 28.
-/

public section

open MeasureTheory Set Filter Real TauCeti.Probability

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {l₁ l₂ : ℝ}

/-- The density of the sum is nonnegative on `[0, ∞)`. -/
private lemma sumDensity_nonneg (h₁ : 0 < l₁) (h₂ : 0 < l₂) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁) := by
  rcases le_total l₁ l₂ with h | h
  · exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (exp_le_exp.mpr
      (by nlinarith)))) (sub_nonneg.mpr h)
  · exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith)))) (sub_nonpos.mpr h)

/-- A nonnegative finite combination of the functions `x ↦ l ^ 2 * x * exp (- l x)`, `l > 0`, is
not `C (exp (- a x) - exp (- b x))` on `(0, ∞)` for `a < b` and `C > 0`: at infinity, the terms
with `l ≤ a` decay too slowly and the other ones too fast. -/
private lemma not_forall_sum_eq_mul_sub {a b C : ℝ} (hab : a < b) (hC : 0 < C) (s : Finset ℝ)
    (c : ℝ → ℝ) (hc : ∀ l ∈ s, 0 ≤ c l) (hs : ∀ l ∈ s, 0 < l) :
    ¬ ∀ x > 0, ∑ l ∈ s, c l * (l ^ 2 * x * exp (-(l * x))) =
      C * (exp (-(a * x)) - exp (-(b * x))) := by
  intro h
  have hterm : ∀ x > 0, ∀ l ∈ s, 0 ≤ c l * (l ^ 2 * x * exp (-(l * x))) := fun x hx l hl ↦ by
    have := hc l hl
    positivity
  -- the coefficients of the rates `l ≤ a` vanish
  have h0 : ∀ l ∈ s, l ≤ a → c l = 0 := by
    intro l hl hla
    by_contra hcl
    have hcl' : 0 < c l * l ^ 2 := mul_pos ((hc l hl).lt_of_ne' hcl) (pow_pos (hs l hl) 2)
    set x := 2 * C / (c l * l ^ 2) with hx_def
    have hx : 0 < x := by positivity
    have h1 := Finset.single_le_sum (hterm x hx) hl
    rw [h x hx] at h1
    have h2 : C * exp (-(a * x)) ≤ C * exp (-(l * x)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hC.le
    have h3 : 0 < C * exp (-(b * x)) := mul_pos hC (exp_pos _)
    have h4 : 0 < C * exp (-(l * x)) := mul_pos hC (exp_pos _)
    have h5 : c l * (l ^ 2 * x * exp (-(l * x))) = 2 * (C * exp (-(l * x))) := by
      have := (hs l hl).ne'
      rw [hx_def]
      field_simp
    linarith
  -- multiply by `exp (a x)` and let `x` tend to infinity
  have hlim : Tendsto (fun x ↦ ∑ l ∈ s, c l * l ^ 2 * (x * exp (-((l - a) * x)))) atTop
      (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _l ∈ s, 0 by simp]
    refine tendsto_finsetSum _ fun l hl ↦ ?_
    by_cases hla : l ≤ a
    · simp [h0 l hl hla]
    have hε : 0 < l - a := sub_pos.mpr (not_le.mp hla)
    have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Tendsto.const_mul_atTop hε tendsto_id)).const_mul (c l * l ^ 2 / (l - a))
    rw [mul_zero] at this
    refine this.congr fun x ↦ ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  have hlim' : Tendsto (fun x ↦ C * (1 - exp (-((b - a) * x)))) atTop (𝓝 C) := by
    have : Tendsto (fun x ↦ exp (-((b - a) * x))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (sub_pos.mpr hab) tendsto_id)
    simpa using (this.const_sub 1).const_mul C
  refine hC.ne (tendsto_nhds_unique (hlim.congr' ?_) hlim')
  filter_upwards [eventually_gt_atTop 0] with x hx
  have key : ∀ l, exp (-((l - a) * x)) = exp (-(l * x)) * exp (a * x) := fun l ↦ by
    rw [← exp_add]
    ring_nf
  have ha : exp (-(a * x)) * exp (a * x) = 1 := by
    rw [← exp_add]
    simp
  calc ∑ l ∈ s, c l * l ^ 2 * (x * exp (-((l - a) * x)))
  _ = (∑ l ∈ s, c l * (l ^ 2 * x * exp (-(l * x)))) * exp (a * x) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [key]
    ring
  _ = C * (1 - exp (-((b - a) * x))) := by
    rw [h x hx, key b]
    linear_combination C * ha

/-- **No finite combination of members of the null is the reverse information projection.** For
distinct positive rates `l₁, l₂`, no finite combination of the laws `Exp(l) ⊗ Exp(l)` is the
reverse information projection of `Exp(l₁) ⊗ Exp(l₂)` on the null of the products
`Exp(l) ⊗ Exp(l)`, `l > 0`. In particular it is not a mixture of two members of the null, against
the conjecture of [HGLLA24, §5.2]; this refutation is [EVR26, Note 28]. -/
theorem sum_smul_prod_expMeasure_ne_ripr (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂)
    (s : Finset ℝ) (w : ℝ → ℝ≥0∞) :
    ∑ l ∈ s, w l • (expMeasure l).prod (expMeasure l) ≠
      ripr ((expMeasure l₁).prod (expMeasure l₂))
        (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  rw [ripr_prod_expMeasure h₁ h₂]
  intro heq
  set s' := s.filter (0 < ·) with hs'
  have hs'pos : ∀ l ∈ s', 0 < l := fun l hl ↦ (Finset.mem_filter.mp hl).2
  -- the laws of the sum agree
  have hsum : ∀ A, MeasurableSet A → ∑ l ∈ s', w l * gammaMeasure 2 l A =
      ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) A := by
    intro A hA
    have h1 := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ ((fun x ↦ x.1 + x.2) ⁻¹' A)) heq
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul] at h1
    rw [← Measure.map_apply (by fun_prop) hA,
      map_comp_eq_of_ae_eq (by fun_prop) (ae_of_all _ Kernel.ae_add_segmentUniform)] at h1
    rw [← h1, hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    split_ifs with hl
    · rw [← map_add_prod_expMeasure_self hl, Measure.map_apply (by fun_prop) hA]
    · simp [expMeasure_of_nonpos (not_lt.mp hl)]
  -- so the weights are finite
  have hw : ∀ l ∈ s', w l ≠ ∞ := by
    have hmass := hsum univ MeasurableSet.univ
    rw [measure_univ, Finset.sum_congr rfl fun l hl ↦ by
      have := isProbabilityMeasure_gammaMeasure two_pos (hs'pos l hl)
      rw [measure_univ, mul_one]] at hmass
    exact fun l hl ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      (hmass ▸ Finset.single_le_sum (fun _ _ ↦ zero_le) hl)
  -- and the densities of the laws of the sum agree on `(0, ∞)`
  have hae : (fun x ↦ ∑ l ∈ s', w l * gammaPDF 2 l x) =ᵐ[volume.restrict (Ioi 0)]
      fun x ↦ ENNReal.ofReal (l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Finset.measurable_fun_sum _ fun l _ ↦ (measurable_gammaPDF 2 l).const_mul _)
      (by fun_prop) fun A hA _ ↦ ?_
    rw [lintegral_finsetSum _ fun l _ ↦ (measurable_gammaPDF 2 l).const_mul _,
      ← withDensity_apply _ hA, ← map_add_prod_expMeasure_eq_withDensity h₁ h₂ h, ← hsum A hA]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [lintegral_const_mul _ (measurable_gammaPDF 2 l), ← withDensity_apply _ hA,
      ← gammaMeasure_eq_withDensity_restrict_Ioi]
  have hreal : ∀ x ∈ Ioi (0 : ℝ),
      ∑ l ∈ s', (w l).toReal * (l ^ 2 * x * exp (-(l * x))) =
        l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi (by fun_prop) (by fun_prop)
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx (hx0 : 0 < x)
    rw [← ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun l hl ↦
      have := hs'pos l hl; by positivity) (sumDensity_nonneg h₁ h₂ hx0.le), ← hx,
      ENNReal.ofReal_sum_of_nonneg fun l hl ↦ have := hs'pos l hl; by positivity]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hw l hl),
      gammaPDF_two hx0.le]
  -- the density of the law of the sum is symmetric in the two rates: order them
  obtain ⟨a, b, hab, ha, hdens⟩ : ∃ a b, a < b ∧ 0 < a ∧ ∀ x,
      l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁) =
        a * b / (b - a) * (exp (-(a * x)) - exp (-(b * x))) := by
    have h12 : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h
    have h21 : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr h.symm
    rcases h.lt_or_gt with h' | h'
    · exact ⟨l₁, l₂, h', h₁, fun x ↦ by ring⟩
    · refine ⟨l₂, l₁, h', h₂, fun x ↦ ?_⟩
      field_simp
      ring
  exact not_forall_sum_eq_mul_sub hab (div_pos (mul_pos ha (ha.trans hab)) (sub_pos.mpr hab)) s'
    (fun l ↦ (w l).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg) hs'pos fun x hx ↦ by
      rw [hreal x hx, hdens]

end ProbabilityTheory
