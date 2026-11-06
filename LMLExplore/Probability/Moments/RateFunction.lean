/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import LMLExplore.Probability.Moments.IntegrableExpMul
public import TauCeti.Analysis.Convex.Conjugate

/-!
# The Cramér rate function

The Cramér rate function of a real random variable `X` under a measure `P` is
`I(x) = sup_t (t x - Λ(t))`, where `Λ = cgf X P` is the cumulant generating function of `X` and the
supremum runs over the parameters `t ∈ integrableExpSet X P` at which `exp (t X)` is integrable.
It is valued in `ℝ≥0∞`: every term is replaced by its positive part, which for a probability
measure does not change the supremum, since the term at `t = 0` vanishes. It is the
Legendre–Fenchel conjugate of `Λ` extended by `+∞` outside `integrableExpSet X P`
(`LMLExplore.coe_rateFunction_eq_fenchelConjugate`), and the exponent of the Cramér–Chernoff
bounds on the deviations of the empirical means of independent copies of `X`. For the statistic
of an exponential family under the member of mean `μ`, it is the divergence `d(x, μ)` between the
members of means `x` and `μ`, and it extends that divergence to the levels `x` outside the means
of the family.

The rate function is convex and lower semicontinuous. For a probability measure and an integrable
`X`, it vanishes at the mean `E[X]`, is antitone below the mean and monotone above it: above the
mean only the nonnegative parameters matter, below it only the nonpositive ones. If `X ≤ x`
almost surely, then `I(x) = -log P(X = x)`, which is `+∞` when `P(X = x) = 0`: the rate function is
infinite beyond the essential supremum of `X`, and symmetrically below its essential infimum.

## Main definitions

* `LMLExplore.rateFunction X P x`: the Cramér rate function
  `I(x) = ⨆ t ∈ integrableExpSet X P, ENNReal.ofReal (t x - cgf X P t)`.

## Main statements

* `LMLExplore.coe_rateFunction_eq_fenchelConjugate`: the rate function is the Fenchel conjugate,
  for the pairing `(t, x) ↦ t x`, of the cumulant generating function extended by `⊤`.
* `LMLExplore.rateFunction_neg`, `LMLExplore.rateFunction_congr_ae`,
  `ProbabilityTheory.IdentDistrib.rateFunction_eq`: the rate function of `-X` at `x` is that of
  `X` at `-x`, and the rate function only depends on the law of `X`.
* `LMLExplore.convexOn_rateFunction`, `LMLExplore.lowerSemicontinuous_rateFunction`: it is convex
  and lower semicontinuous.
* `LMLExplore.mul_integral_le_cgf`: Jensen's inequality `t E[X] ≤ cgf X P t`.
* `LMLExplore.rateFunction_integral`: the rate function vanishes at the mean.
* `LMLExplore.rateFunction_eq_iSup_nonneg`, `LMLExplore.rateFunction_eq_iSup_nonpos`: above the
  mean it is the supremum over the nonnegative parameters, below the mean over the nonpositive
  ones.
* `LMLExplore.monotoneOn_rateFunction`, `LMLExplore.antitoneOn_rateFunction`: it is monotone
  above the mean and antitone below it.
* `LMLExplore.rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le`,
  `LMLExplore.rateFunction_eq_top_of_ae_le`: if `X ≤ x` almost surely, then
  `I(x) = -log P(X = x)`, and `I(x) = ⊤` when `P(X = x) = 0`; the lower-side versions are
  `LMLExplore.rateFunction_eq_ofReal_neg_log_measureReal_of_ae_ge` and
  `LMLExplore.rateFunction_eq_top_of_ae_ge`.
* `LMLExplore.rateFunction_eq_top_of_ae_lt`, `LMLExplore.rateFunction_eq_top_of_ae_gt`: the rate
  function is infinite at the levels `x` with `X < x` almost surely, or `x < X` almost surely.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Section 2.2.
* A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Section 2.2.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped ENNReal NNReal Topology

namespace LMLExplore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : Ω → ℝ}
  {P : Measure Ω} {t x y : ℝ} {r : ℝ≥0∞}

/-! ### Definition and characterization -/

/-- The **Cramér rate function** `I(x) = sup_t (t x - Λ(t))` of a real random variable `X` under a
measure `P`, where `Λ = cgf X P`, the supremum over the parameters `t ∈ integrableExpSet X P`,
valued in `ℝ≥0∞`. -/
noncomputable def rateFunction (X : Ω → ℝ) (P : Measure Ω) (x : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ integrableExpSet X P, ENNReal.ofReal (t * x - cgf X P t)

lemma rateFunction_def (X : Ω → ℝ) (P : Measure Ω) (x : ℝ) :
    rateFunction X P x = ⨆ t ∈ integrableExpSet X P, ENNReal.ofReal (t * x - cgf X P t) :=
  (rfl)

lemma ofReal_le_rateFunction (ht : t ∈ integrableExpSet X P) (x : ℝ) :
    ENNReal.ofReal (t * x - cgf X P t) ≤ rateFunction X P x :=
  le_iSup₂ (f := fun t (_ : t ∈ integrableExpSet X P) ↦ ENNReal.ofReal (t * x - cgf X P t)) t ht

lemma rateFunction_le_iff :
    rateFunction X P x ≤ r ↔ ∀ t ∈ integrableExpSet X P, ENNReal.ofReal (t * x - cgf X P t) ≤ r :=
  iSup₂_le_iff

open Classical in
/-- The rate function is the Legendre–Fenchel conjugate (Tau Ceti's `fenchelConjugate`), for the
pairing `(t, x) ↦ t * x`, of the cumulant generating function extended by `⊤` outside
`integrableExpSet X P`. -/
theorem coe_rateFunction_eq_fenchelConjugate [IsZeroOrProbabilityMeasure P] (x : ℝ) :
    (rateFunction X P x : EReal) = TauCeti.fenchelConjugate (LinearMap.mul ℝ ℝ)
      (fun t ↦ if t ∈ integrableExpSet X P then (cgf X P t : EReal) else ⊤) x := by
  set f : ℝ → EReal := fun t ↦ if t ∈ integrableExpSet X P then (cgf X P t : EReal) else ⊤
  -- Each term of the conjugate is the real term `t x - cgf X P t`, or `⊥` outside the set.
  have h_term (t : ℝ) (ht : t ∈ integrableExpSet X P) :
      ((LinearMap.mul ℝ ℝ t x : ℝ) : EReal) - f t = ((t * x - cgf X P t : ℝ) : EReal) := by
    simp [f, ht]
  have h_nonneg : 0 ≤ TauCeti.fenchelConjugate (LinearMap.mul ℝ ℝ) f x := by
    have h0 : (0 : ℝ) ∈ integrableExpSet X P := by simp [integrableExpSet]
    calc (0 : EReal) = ((0 * x - cgf X P 0 : ℝ) : EReal) := by simp [cgf_zero]
    _ = ((LinearMap.mul ℝ ℝ 0 x : ℝ) : EReal) - f 0 := (h_term 0 h0).symm
    _ ≤ _ := TauCeti.sub_le_fenchelConjugate _ f 0 x
  refine le_antisymm ?_ (TauCeti.fenchelConjugate_le _ fun t ↦ ?_)
  · rw [← EReal.coe_toENNReal h_nonneg, EReal.coe_ennreal_le_coe_ennreal_iff, rateFunction_le_iff]
    intro t ht
    rw [← EReal.real_coe_toENNReal, ← h_term t ht]
    exact EReal.toENNReal_le_toENNReal (TauCeti.sub_le_fenchelConjugate _ f t x)
  · by_cases ht : t ∈ integrableExpSet X P
    · rw [h_term t ht]
      refine le_trans ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2 (ofReal_le_rateFunction ht x))
      rw [EReal.coe_ennreal_ofReal]
      exact le_max_left (a := ((t * x - cgf X P t : ℝ) : EReal)) (b := 0)
    · simp [f, ht]

/-- The rate function of `-X` at `x` is the rate function of `X` at `-x`. -/
@[simp]
lemma rateFunction_neg (X : Ω → ℝ) (P : Measure Ω) (x : ℝ) :
    rateFunction (-X) P x = rateFunction X P (-x) := by
  have h_mem (t : ℝ) : t ∈ integrableExpSet (-X) P ↔ -t ∈ integrableExpSet X P := by
    simp [integrableExpSet]
  rw [rateFunction_def, rateFunction_def, ← (Equiv.neg ℝ).iSup_comp]
  refine iSup_congr fun t ↦ ?_
  simp only [Equiv.neg_apply, h_mem, cgf_neg, neg_neg, neg_mul, mul_neg]

/-- The rate function only depends on `X` up to `P`-almost everywhere equality. -/
lemma rateFunction_congr_ae {Y : Ω → ℝ} (h : X =ᵐ[P] Y) : rateFunction X P = rateFunction Y P := by
  have h_set : integrableExpSet X P = integrableExpSet Y P := by
    ext t
    refine integrable_congr ?_
    filter_upwards [h] with ω hω
    rw [hω]
  have h_cgf (t : ℝ) : cgf X P t = cgf Y P t := by rw [cgf, cgf, mgf_congr h]
  ext x
  simp_rw [rateFunction_def, h_set, h_cgf]

/-- The rate function only depends on the law of `X`. -/
lemma _root_.ProbabilityTheory.IdentDistrib.rateFunction_eq {P' : Measure Ω'} {Y : Ω' → ℝ}
    (h : IdentDistrib X Y P P') : rateFunction X P = rateFunction Y P' := by
  have h_set : integrableExpSet X P = integrableExpSet Y P' := by
    ext t
    exact (h.comp (measurable_exp.comp (measurable_const_mul t))).integrable_iff
  have h_cgf (t : ℝ) : cgf X P t = cgf Y P' t := by rw [cgf, cgf, mgf_congr_identDistrib h]
  ext x
  simp_rw [rateFunction_def, h_set, h_cgf]

/-! ### Convexity and lower semicontinuity -/

/-- The rate function is convex. -/
theorem convexOn_rateFunction (X : Ω → ℝ) (P : Measure Ω) :
    ConvexOn ℝ≥0 univ (rateFunction X P) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ ?_⟩
  rw [rateFunction_le_iff]
  intro t ht
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  calc ENNReal.ofReal (t * (a • x + b • y) - cgf X P t)
      = ENNReal.ofReal (a * (t * x - cgf X P t) + b * (t * y - cgf X P t)) := by
        congr 1
        rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]
        linear_combination (cgf X P t) * hab'
  _ ≤ ENNReal.ofReal (a * (t * x - cgf X P t)) + ENNReal.ofReal (b * (t * y - cgf X P t)) :=
        ENNReal.ofReal_add_le
  _ = a • ENNReal.ofReal (t * x - cgf X P t) + b • ENNReal.ofReal (t * y - cgf X P t) := by
        rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def,
          ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  _ ≤ a • rateFunction X P x + b • rateFunction X P y := by
        gcongr <;> exact ofReal_le_rateFunction ht _

/-- The rate function is lower semicontinuous, as a supremum of continuous functions. -/
theorem lowerSemicontinuous_rateFunction (X : Ω → ℝ) (P : Measure Ω) :
    LowerSemicontinuous (rateFunction X P) := by
  have h_eq : rateFunction X P = fun x ↦ ⨆ t ∈ integrableExpSet X P,
      ENNReal.ofReal (t * x - cgf X P t) := funext (rateFunction_def X P)
  rw [h_eq]
  exact lowerSemicontinuous_biSup fun t _ ↦ (ENNReal.continuous_ofReal.comp
    ((continuous_const.mul continuous_id).sub continuous_const)).lowerSemicontinuous

/-! ### The rate function around the mean -/

/-- **Jensen's inequality for the cumulant generating function**: `t E[X] ≤ cgf X P t` at every
parameter `t` where `exp (t X)` is integrable. -/
theorem mul_integral_le_cgf [IsProbabilityMeasure P] (hX : Integrable X P)
    (ht : t ∈ integrableExpSet X P) : t * P[X] ≤ cgf X P t := by
  have h_jensen : exp (∫ ω, t * X ω ∂P) ≤ ∫ ω, exp (t * X ω) ∂P :=
    convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall fun _ ↦ mem_univ _) (hX.const_mul t) ht
  rw [integral_const_mul] at h_jensen
  rw [cgf, mgf, ← log_exp (t * P[X])]
  exact log_le_log (exp_pos _) h_jensen

/-- The terms of the rate function at negative parameters vanish above the mean. -/
private lemma ofReal_mul_sub_cgf_eq_zero_of_integral_le [IsProbabilityMeasure P]
    (hX : Integrable X P) (ht : t ∈ integrableExpSet X P) (h : 0 ≤ t * (P[X] - x)) :
    ENNReal.ofReal (t * x - cgf X P t) = 0 := by
  rw [ENNReal.ofReal_eq_zero]
  linarith [mul_integral_le_cgf hX ht]

/-- The rate function vanishes at the mean. -/
theorem rateFunction_integral [IsProbabilityMeasure P] (hX : Integrable X P) :
    rateFunction X P P[X] = 0 := by
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_) zero_le
  rw [ofReal_mul_sub_cgf_eq_zero_of_integral_le hX ht (by simp)]

/-- Above the mean, the rate function is the supremum over the nonnegative parameters. -/
theorem rateFunction_eq_iSup_nonneg [IsProbabilityMeasure P] (hX : Integrable X P)
    (hx : P[X] ≤ x) :
    rateFunction X P x =
      ⨆ t ∈ integrableExpSet X P ∩ Ici 0, ENNReal.ofReal (t * x - cgf X P t) := by
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_)
    (biSup_mono fun t ht ↦ ht.1)
  rcases le_or_gt 0 t with h0 | h0
  · exact le_iSup₂ (f := fun t (_ : t ∈ integrableExpSet X P ∩ Ici 0) ↦
      ENNReal.ofReal (t * x - cgf X P t)) t ⟨ht, h0⟩
  · rw [ofReal_mul_sub_cgf_eq_zero_of_integral_le hX ht
      (mul_nonneg_of_nonpos_of_nonpos h0.le (by linarith))]
    exact zero_le

/-- Below the mean, the rate function is the supremum over the nonpositive parameters. -/
theorem rateFunction_eq_iSup_nonpos [IsProbabilityMeasure P] (hX : Integrable X P)
    (hx : x ≤ P[X]) :
    rateFunction X P x =
      ⨆ t ∈ integrableExpSet X P ∩ Iic 0, ENNReal.ofReal (t * x - cgf X P t) := by
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_)
    (biSup_mono fun t ht ↦ ht.1)
  rcases le_or_gt t 0 with h0 | h0
  · exact le_iSup₂ (f := fun t (_ : t ∈ integrableExpSet X P ∩ Iic 0) ↦
      ENNReal.ofReal (t * x - cgf X P t)) t ⟨ht, h0⟩
  · rw [ofReal_mul_sub_cgf_eq_zero_of_integral_le hX ht (mul_nonneg h0.le (by linarith))]
    exact zero_le

/-- The rate function is monotone above the mean. -/
theorem monotoneOn_rateFunction [IsProbabilityMeasure P] (hX : Integrable X P) :
    MonotoneOn (rateFunction X P) (Ici P[X]) := by
  intro x hx y hy hxy
  rw [rateFunction_eq_iSup_nonneg hX hx, rateFunction_eq_iSup_nonneg hX hy]
  exact iSup₂_mono fun t ht ↦ ENNReal.ofReal_le_ofReal
    (by linarith [mul_le_mul_of_nonneg_left hxy (mem_Ici.1 ht.2)])

/-- The rate function is antitone below the mean. -/
theorem antitoneOn_rateFunction [IsProbabilityMeasure P] (hX : Integrable X P) :
    AntitoneOn (rateFunction X P) (Iic P[X]) := by
  intro x hx y hy hxy
  rw [rateFunction_eq_iSup_nonpos hX hx, rateFunction_eq_iSup_nonpos hX hy]
  exact iSup₂_mono fun t ht ↦ ENNReal.ofReal_le_ofReal
    (by linarith [mul_le_mul_of_nonpos_left hxy (mem_Iic.1 ht.2)])

/-! ### The rate function at the essential supremum and beyond -/

section Boundary

variable [IsProbabilityMeasure P]

/-- The term `t x - cgf X P t` of the rate function is `-log E[exp (t (X - x))]`. -/
private lemma mul_sub_cgf_eq_neg_log (ht : t ∈ integrableExpSet X P) (x : ℝ) :
    t * x - cgf X P t = -log (∫ ω, exp (t * (X ω - x)) ∂P) := by
  have h_eq : ∫ ω, exp (t * (X ω - x)) ∂P = mgf X P t * exp (-(t * x)) := by
    rw [mgf, ← integral_mul_const]
    congr with ω
    rw [← exp_add]
    ring_nf
  rw [h_eq, log_mul (mgf_pos ht).ne' (exp_pos _).ne', log_exp, cgf]
  ring

/-- The rate function at `x` is at least the limit of `-log E[exp (t (X - x))]` as `t → ∞`. -/
private lemma tendsto_ofReal_neg_log_integral_le (hX : Measurable X) (h : ∀ᵐ ω ∂P, X ω ≤ x)
    {l : ℝ≥0∞}
    (hl : Tendsto (fun t ↦ ENNReal.ofReal (-log (∫ ω, exp (t * (X ω - x)) ∂P))) atTop (𝓝 l)) :
    l ≤ rateFunction X P x := by
  refine le_of_tendsto hl ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [← mul_sub_cgf_eq_neg_log (integrable_exp_mul_of_le t x ht hX.aemeasurable h)]
  exact ofReal_le_rateFunction (integrable_exp_mul_of_le t x ht hX.aemeasurable h) x

private lemma rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le_of_measurable
    (hX : Measurable X) (h : ∀ᵐ ω ∂P, X ω ≤ x) (hx : P {ω | X ω = x} ≠ 0) :
    rateFunction X P x = ENNReal.ofReal (-log (P.real {ω | X ω = x})) := by
  have hp : 0 < P.real {ω | X ω = x} := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hx (measure_ne_top _ _)
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_)
    (tendsto_ofReal_neg_log_integral_le hX h ?_)
  · -- `E[exp (t (X - x))] ≥ P(X = x)` at every parameter.
    rw [mul_sub_cgf_eq_neg_log ht]
    refine ENNReal.ofReal_le_ofReal (neg_le_neg (log_le_log hp ?_))
    have hmeas : MeasurableSet {ω | X ω = x} := hX (measurableSet_singleton x)
    rw [← integral_indicator_one hmeas]
    refine integral_mono (integrable_const 1 |>.indicator hmeas)
      (integrable_exp_mul_sub ht x) fun ω ↦ ?_
    by_cases hω : ω ∈ {ω | X ω = x}
    · have : X ω = x := hω
      simp [this]
    · rw [indicator_of_notMem hω]
      exact (exp_pos _).le
  · exact ENNReal.tendsto_ofReal ((tendsto_integral_exp_mul_sub hX.aemeasurable h).log hp.ne').neg

private lemma rateFunction_eq_top_of_ae_le_of_measurable (hX : Measurable X)
    (h : ∀ᵐ ω ∂P, X ω ≤ x) (hx : P {ω | X ω = x} = 0) : rateFunction X P x = ⊤ := by
  refine top_le_iff.1 (tendsto_ofReal_neg_log_integral_le hX h ?_)
  refine ENNReal.tendsto_ofReal_atTop.comp (tendsto_neg_atBot_atTop.comp
    (tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)))
  · have h_lim := tendsto_integral_exp_mul_sub hX.aemeasurable h
    rwa [measureReal_def, hx, ENNReal.toReal_zero] at h_lim
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact integral_exp_pos
      (integrable_exp_mul_sub (integrable_exp_mul_of_le t x ht hX.aemeasurable h) x)

/-- If `X ≤ x` almost surely and `P(X = x) > 0`, then the rate function at `x` is
`-log P(X = x)`. -/
theorem rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le (hX : AEMeasurable X P)
    (h : ∀ᵐ ω ∂P, X ω ≤ x) (hx : P {ω | X ω = x} ≠ 0) :
    rateFunction X P x = ENNReal.ofReal (-log (P.real {ω | X ω = x})) := by
  have h' : ∀ᵐ ω ∂P, hX.mk X ω ≤ x := by
    filter_upwards [h, hX.ae_eq_mk] with ω hω h_eq
    rwa [← h_eq]
  have h_eq : P {ω | hX.mk X ω = x} = P {ω | X ω = x} :=
    measure_congr (hX.ae_eq_mk.symm.preimage {x})
  rw [rateFunction_congr_ae hX.ae_eq_mk, measureReal_def, ← h_eq, ← measureReal_def]
  exact rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le_of_measurable hX.measurable_mk h'
    (by rwa [h_eq])

/-- If `X ≤ x` almost surely and `P(X = x) = 0`, then the rate function at `x` is infinite. -/
theorem rateFunction_eq_top_of_ae_le (hX : AEMeasurable X P) (h : ∀ᵐ ω ∂P, X ω ≤ x)
    (hx : P {ω | X ω = x} = 0) : rateFunction X P x = ⊤ := by
  have h' : ∀ᵐ ω ∂P, hX.mk X ω ≤ x := by
    filter_upwards [h, hX.ae_eq_mk] with ω hω h_eq
    rwa [← h_eq]
  rw [rateFunction_congr_ae hX.ae_eq_mk]
  exact rateFunction_eq_top_of_ae_le_of_measurable hX.measurable_mk h'
    ((measure_congr (hX.ae_eq_mk.symm.preimage {x})).trans hx)

/-- Beyond the essential supremum of `X`, the rate function is infinite. -/
theorem rateFunction_eq_top_of_ae_lt (hX : AEMeasurable X P) (h : ∀ᵐ ω ∂P, X ω < x) :
    rateFunction X P x = ⊤ := by
  refine rateFunction_eq_top_of_ae_le hX (h.mono fun _ ↦ le_of_lt)
    (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [h] with ω hω
  exact hω.ne

private lemma setOf_neg_eq (X : Ω → ℝ) (x : ℝ) : {ω | (-X) ω = -x} = {ω | X ω = x} := by
  ext ω
  simp

/-- If `x ≤ X` almost surely and `P(X = x) > 0`, then the rate function at `x` is
`-log P(X = x)`. -/
theorem rateFunction_eq_ofReal_neg_log_measureReal_of_ae_ge (hX : AEMeasurable X P)
    (h : ∀ᵐ ω ∂P, x ≤ X ω) (hx : P {ω | X ω = x} ≠ 0) :
    rateFunction X P x = ENNReal.ofReal (-log (P.real {ω | X ω = x})) := by
  rw [← neg_neg x, ← rateFunction_neg,
    rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le hX.neg (h.mono fun _ ↦ neg_le_neg)
      (by rwa [setOf_neg_eq]),
    setOf_neg_eq, neg_neg]

/-- If `x ≤ X` almost surely and `P(X = x) = 0`, then the rate function at `x` is infinite. -/
theorem rateFunction_eq_top_of_ae_ge (hX : AEMeasurable X P) (h : ∀ᵐ ω ∂P, x ≤ X ω)
    (hx : P {ω | X ω = x} = 0) : rateFunction X P x = ⊤ := by
  rw [← neg_neg x, ← rateFunction_neg]
  exact rateFunction_eq_top_of_ae_le hX.neg (h.mono fun _ ↦ neg_le_neg) (by rwa [setOf_neg_eq])

/-- Below the essential infimum of `X`, the rate function is infinite. -/
theorem rateFunction_eq_top_of_ae_gt (hX : AEMeasurable X P) (h : ∀ᵐ ω ∂P, x < X ω) :
    rateFunction X P x = ⊤ := by
  rw [← neg_neg x, ← rateFunction_neg]
  exact rateFunction_eq_top_of_ae_lt hX.neg (h.mono fun _ ↦ neg_lt_neg)

end Boundary

end LMLExplore
