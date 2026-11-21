/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Calibrator
public import LMLExplore.Order.Filter.CompleteClass
public import Mathlib.Probability.Independence.Basic

/-!
# Combining a p-value and an e-value

A p-value `p` and an e-value `E` for the same null are combined by a function
`F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞` of the pair. As for calibrators and merging functions, the combiners are
the bets of a null on the space of values: `peNull`, the joint laws of a p-value and an e-value
(a super-uniform first marginal and a second coordinate of mean at most `1`), or `indepPENull`,
the products of such marginals. A **p-and-e-to-e combiner** for one of them is an e-variable for
it that is antitone in the p-value and monotone in the e-value; a **p-and-e-to-p combiner** is a
p-variable that is monotone in the p-value and antitone in the e-value. The laws of `(p, E)` under
the members of any null are in `peNull`, and in `indepPENull` when `p` and `E` are independent, so
combiners combine p-variables and e-variables on every measurable space.

Ignatiadis, Wang and Ramdas [IWR24, Theorem 3.1] give four admissible combiners, one for each of
the four questions (independent or arbitrarily dependent inputs, an e-value or a p-value as
output), for an admissible calibrator `h`:
* the product `h p * e`, with `0 * ∞ = ∞`, for independent inputs, to an e-value;
* the quotient `min (p / e) 1` for independent inputs, to a p-value;
* the mean `w h p + (1 - w) e`, `0 < w < 1`, for arbitrary dependence, to an e-value;
* the Bonferroni combination `min (2 min p e⁻¹) 1` for arbitrary dependence, to a p-value.

Admissibility is domination on `[0, 1] × [0, ∞]`, the domain of the combiners of [IWR24]: p-values
above `1` carry no evidence, and a combiner may be improved there without changing it on that
domain (for instance `h p * e` vanishes for `p > 1`), so domination is only asked there. For the
e-combiners it is `Filter.IsAdmissible` along `𝓟 (Iic 1 ×ˢ univ)`; for the p-combiners, which
are better when smaller, it is the dual statement that a combiner below the given one on
`[0, 1] × [0, ∞]` equals it there. The proofs follow [IWR24, Supplement]: a combiner that strictly
improves on one of the four somewhere is improved on a rectangle of positive probability under the
uniform law and a law of mean `1`, which makes it invalid.

## Main definitions

* `ProbabilityTheory.peNull`, `ProbabilityTheory.indepPENull`: the nulls of the pairs of a
  p-value and an e-value, arbitrarily dependent or independent.
* `ProbabilityTheory.IsPEToECombiner 𝒩 F`, `ProbabilityTheory.IsPEToPCombiner 𝒩 F`: combiners to
  an e-value and to a p-value for the null `𝒩` of pairs.
* `ProbabilityTheory.prodCombiner h`, `ProbabilityTheory.quotCombiner`,
  `ProbabilityTheory.meanCombiner h w`, `ProbabilityTheory.bonferroniCombiner`: the four
  combiners of [IWR24, §3.1].

## Main statements

* `ProbabilityTheory.IsEVar.comp_isPVar_isEVar`, `ProbabilityTheory.IsPVar.comp_isPVar_isEVar` and
  their versions `_of_indepFun`: combiners combine p-variables and e-variables of every null.
* `ProbabilityTheory.isPEToECombiner_prodCombiner`, `ProbabilityTheory.isAdmissible_prodCombiner`:
  the product combiner is valid and admissible for independent inputs.
* `ProbabilityTheory.isPEToPCombiner_quotCombiner`,
  `ProbabilityTheory.IsPEToPCombiner.eventuallyEq_quotCombiner_of_le`: the quotient combiner is
  valid and admissible for independent inputs.
* `ProbabilityTheory.isPEToECombiner_meanCombiner`, `ProbabilityTheory.isAdmissible_meanCombiner`:
  the mean combiner is valid and admissible for arbitrary dependence.
* `ProbabilityTheory.isPEToPCombiner_bonferroniCombiner`,
  `ProbabilityTheory.IsPEToPCombiner.eventuallyEq_bonferroniCombiner_of_le`: the Bonferroni
  combiner is valid and admissible for arbitrary dependence.

## References

* [IWR24] N. Ignatiadis, R. Wang and A. Ramdas, *E-values as unnormalized weights in multiple
  testing*, Biometrika 111 (2024), arXiv:2204.12447v6: §3.1, Theorem 3.1 and its proof in the
  Supplement.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {P : Measure Ω}
  {p E : Ω → ℝ≥0∞} {μ ν ρ : Measure ℝ≥0∞} {𝒩 𝒩' : Set (Measure (ℝ≥0∞ × ℝ≥0∞))}
  {f g h : ℝ≥0∞ → ℝ≥0∞} {F G : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞} {w : ℝ≥0∞}

/-! ### The nulls of the joint laws of a p-value and an e-value -/

/-- The null of the joint laws of a p-value and an e-value with **arbitrary dependence**: the
measures on `ℝ≥0∞ × ℝ≥0∞` whose first marginal is super-uniform and whose second coordinate has
mean at most `1`. These are the laws of `(p, E)` for a p-variable `p` and an e-variable `E`
(`ProbabilityTheory.map_mem_peNull`). -/
def peNull : Set (Measure (ℝ≥0∞ × ℝ≥0∞)) :=
  {μ | μ.map Prod.fst ∈ superUniformNull ∧ ∫⁻ x, x.2 ∂μ ≤ 1}

/-- The null of the joint laws of an **independent** p-value and e-value: the products of a
super-uniform law and a probability measure on `ℝ≥0∞` of mean at most `1`. These are the laws of
`(p, E)` for a p-variable `p` and an e-variable `E` independent of it
(`ProbabilityTheory.map_mem_indepPENull`). -/
noncomputable def indepPENull : Set (Measure (ℝ≥0∞ × ℝ≥0∞)) :=
  image2 Measure.prod superUniformNull {ρ | IsProbabilityMeasure ρ ∧ ∫⁻ x, x ∂ρ ≤ 1}

@[simp]
theorem mem_peNull {μ : Measure (ℝ≥0∞ × ℝ≥0∞)} :
    μ ∈ peNull ↔ μ.map Prod.fst ∈ superUniformNull ∧ ∫⁻ x, x.2 ∂μ ≤ 1 :=
  Iff.rfl

theorem mem_indepPENull {μ : Measure (ℝ≥0∞ × ℝ≥0∞)} :
    μ ∈ indepPENull ↔ ∃ ν ∈ superUniformNull, ∃ ρ : Measure ℝ≥0∞,
      (IsProbabilityMeasure ρ ∧ ∫⁻ x, x ∂ρ ≤ 1) ∧ ν.prod ρ = μ :=
  Iff.rfl

theorem prod_mem_indepPENull (hν : ν ∈ superUniformNull) [IsProbabilityMeasure ρ]
    (hρ : ∫⁻ x, x ∂ρ ≤ 1) : ν.prod ρ ∈ indepPENull :=
  mem_image2_of_mem hν ⟨inferInstance, hρ⟩

theorem isProbabilityMeasure_of_mem_peNull {μ : Measure (ℝ≥0∞ × ℝ≥0∞)} (hμ : μ ∈ peNull) :
    IsProbabilityMeasure μ := by
  have := isProbabilityMeasure_of_mem_superUniformNull hμ.1
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- An independent pair is a pair. -/
theorem indepPENull_subset_peNull : indepPENull ⊆ peNull := by
  rintro _ ⟨ν, hν, ρ, ⟨hρ, hρ1⟩, rfl⟩
  have := isProbabilityMeasure_of_mem_superUniformNull hν
  refine ⟨by rwa [Measure.map_fst_prod, measure_univ, one_smul], ?_⟩
  simpa [lintegral_prod _ (by fun_prop : AEMeasurable (fun x : ℝ≥0∞ × ℝ≥0∞ ↦ x.2) _)]

/-- The first coordinate is a p-variable for the null of the pairs. -/
theorem isPVar_fst_peNull : IsPVar Prod.fst peNull where
  measure_le_le μ hμ α := by
    have h := measure_Iic_le_of_mem_superUniformNull hμ.1 α
    rwa [Measure.map_apply measurable_fst measurableSet_Iic] at h

/-- The second coordinate is an e-variable for the null of the pairs. -/
theorem isEVar_snd_peNull : IsEVar Prod.snd peNull where
  lintegral_le_one _ hμ := hμ.2

/-- The law of a p-variable and an e-variable under a probability measure of the null is in
`peNull`. -/
theorem map_mem_peNull (hp : IsPVar p S) (hE : IsEVar E S) (hP : P ∈ S) [IsProbabilityMeasure P] :
    P.map (fun ω ↦ (p ω, E ω)) ∈ peNull := by
  have h_meas : Measurable fun ω ↦ (p ω, E ω) := hp.measurable.prodMk hE.measurable
  refine ⟨?_, ?_⟩
  · rw [Measure.map_map measurable_fst h_meas]
    exact hp.map_mem_superUniformNull hP
  · rw [lintegral_map measurable_snd h_meas]
    exact hE.lintegral_le_one hP

/-- The law of a p-variable and an e-variable independent of it, under a probability measure of
the null, is in `indepPENull`. -/
theorem map_mem_indepPENull (hp : IsPVar p S) (hE : IsEVar E S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (hpE : IndepFun p E P) :
    P.map (fun ω ↦ (p ω, E ω)) ∈ indepPENull := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hp.measurable.aemeasurable
    hE.measurable.aemeasurable).1 hpE]
  refine prod_mem_indepPENull (hp.map_mem_superUniformNull hP) ?_
  rw [lintegral_map (f := fun x ↦ x) measurable_id hE.measurable]
  exact hE.lintegral_le_one hP

/-- The laws of a p-variable and an e-variable under the members of a null of probability
measures are pairs. -/
theorem mapNull_subset_peNull (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S)
    (hE : IsEVar E S) : mapNull (fun ω ↦ (p ω, E ω)) S ⊆ peNull := by
  intro μ hμ
  obtain ⟨P, hP, rfl⟩ := mem_mapNull.1 hμ
  have := hS P hP
  exact map_mem_peNull hp hE hP

/-- The laws of a p-variable and an e-variable independent of it under the members of a null of
probability measures are independent pairs. -/
theorem mapNull_subset_indepPENull (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S)
    (hE : IsEVar E S) (hpE : ∀ P ∈ S, IndepFun p E P) :
    mapNull (fun ω ↦ (p ω, E ω)) S ⊆ indepPENull := by
  intro μ hμ
  obtain ⟨P, hP, rfl⟩ := mem_mapNull.1 hμ
  have := hS P hP
  exact map_mem_indepPENull hp hE hP (hpE P hP)

/-! ### Combiners -/

/-- A **p-and-e-to-e combiner** for a null `𝒩` of joint laws of a p-value and an e-value is a
function `F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞`, antitone in the p-value and monotone in the e-value, that is an
e-variable for `𝒩`. For `𝒩 = peNull` it turns every p-variable and e-variable of every null of
probability measures into an e-variable (`ProbabilityTheory.IsEVar.comp_isPVar_isEVar`); for
`𝒩 = indepPENull` it does so when they are independent
(`ProbabilityTheory.IsEVar.comp_isPVar_isEVar_of_indepFun`). These are the pe/e and the i-pe/e
combiners of [IWR24, §3.1]. -/
structure IsPEToECombiner (𝒩 : Set (Measure (ℝ≥0∞ × ℝ≥0∞))) (F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) :
    Prop where
  antitone_fst (e : ℝ≥0∞) : Antitone fun p ↦ F (p, e)
  monotone_snd (p : ℝ≥0∞) : Monotone fun e ↦ F (p, e)
  isEVar : IsEVar F 𝒩

/-- A **p-and-e-to-p combiner** for a null `𝒩` of joint laws of a p-value and an e-value is a
function `F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞`, monotone in the p-value and antitone in the e-value, that is a
p-variable for `𝒩`. For `𝒩 = peNull` it turns every p-variable and e-variable of every null of
probability measures into a p-variable (`ProbabilityTheory.IsPVar.comp_isPVar_isEVar`); for
`𝒩 = indepPENull` it does so when they are independent
(`ProbabilityTheory.IsPVar.comp_isPVar_isEVar_of_indepFun`). These are the pe/p and the i-pe/p
combiners of [IWR24, §3.1]. -/
structure IsPEToPCombiner (𝒩 : Set (Measure (ℝ≥0∞ × ℝ≥0∞))) (F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) :
    Prop where
  monotone_fst (e : ℝ≥0∞) : Monotone fun p ↦ F (p, e)
  antitone_snd (p : ℝ≥0∞) : Antitone fun e ↦ F (p, e)
  isPVar : IsPVar F 𝒩

/-- A combiner for a null is a combiner for every smaller null: a combiner for arbitrary
dependence is one for independent inputs. -/
theorem IsPEToECombiner.anti_set (h𝒩 : 𝒩' ⊆ 𝒩) (hF : IsPEToECombiner 𝒩 F) :
    IsPEToECombiner 𝒩' F :=
  ⟨hF.antitone_fst, hF.monotone_snd, hF.isEVar.anti_set h𝒩⟩

/-- A combiner for a null is a combiner for every smaller null: a combiner for arbitrary
dependence is one for independent inputs. -/
theorem IsPEToPCombiner.anti_set (h𝒩 : 𝒩' ⊆ 𝒩) (hF : IsPEToPCombiner 𝒩 F) :
    IsPEToPCombiner 𝒩' F :=
  ⟨hF.monotone_fst, hF.antitone_snd, hF.isPVar.anti_set h𝒩⟩

/-- **An e-variable for the pairs combines a p-variable and an e-variable**: for a null of
probability measures, `F (p, E)` is an e-variable for every p-variable `p` and e-variable `E`,
whatever their dependence. -/
theorem IsEVar.comp_isPVar_isEVar (hF : IsEVar F peNull) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hp : IsPVar p S) (hE : IsEVar E S) : IsEVar (fun ω ↦ F (p ω, E ω)) S :=
  (isEVar_mapNull_iff (hp.measurable.prodMk hE.measurable) hF.measurable).1
    (hF.anti_set (mapNull_subset_peNull hS hp hE))

/-- **An e-variable for the independent pairs combines an independent p-variable and
e-variable**: for a null of probability measures, `F (p, E)` is an e-variable for every
p-variable `p` and e-variable `E` independent under every member of the null. -/
theorem IsEVar.comp_isPVar_isEVar_of_indepFun (hF : IsEVar F indepPENull)
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S) (hE : IsEVar E S)
    (hpE : ∀ P ∈ S, IndepFun p E P) : IsEVar (fun ω ↦ F (p ω, E ω)) S :=
  (isEVar_mapNull_iff (hp.measurable.prodMk hE.measurable) hF.measurable).1
    (hF.anti_set (mapNull_subset_indepPENull hS hp hE hpE))

/-- **A p-variable for the pairs combines a p-variable and an e-variable**: for a null of
probability measures, `F (p, E)` is a p-variable for every p-variable `p` and e-variable `E`,
whatever their dependence. -/
theorem IsPVar.comp_isPVar_isEVar (hF : IsPVar F peNull) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hp : IsPVar p S) (hE : IsEVar E S) : IsPVar (fun ω ↦ F (p ω, E ω)) S :=
  (isPVar_mapNull_iff (hp.measurable.prodMk hE.measurable) hF.measurable).1
    (hF.anti_set (mapNull_subset_peNull hS hp hE))

/-- **A p-variable for the independent pairs combines an independent p-variable and
e-variable**: for a null of probability measures, `F (p, E)` is a p-variable for every
p-variable `p` and e-variable `E` independent under every member of the null. -/
theorem IsPVar.comp_isPVar_isEVar_of_indepFun (hF : IsPVar F indepPENull)
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S) (hE : IsEVar E S)
    (hpE : ∀ P ∈ S, IndepFun p E P) : IsPVar (fun ω ↦ F (p ω, E ω)) S :=
  (isPVar_mapNull_iff (hp.measurable.prodMk hE.measurable) hF.measurable).1
    (hF.anti_set (mapNull_subset_indepPENull hS hp hE hpE))

/-! ### The product combiner -/

/-- The **product combiner** `(p, e) ↦ h p * e` of a calibrator `h`, with the convention
`0 * ∞ = ∞` of [IWR24, §3.1]: its value is `∞` as soon as `h p` or `e` is. It is a combiner for
independent inputs (`ProbabilityTheory.isPEToECombiner_prodCombiner`), and an admissible one
when `h` is admissible (`ProbabilityTheory.isAdmissible_prodCombiner`). -/
noncomputable def prodCombiner (h : ℝ≥0∞ → ℝ≥0∞) (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  if h x.1 = ∞ ∨ x.2 = ∞ then ∞ else h x.1 * x.2

theorem prodCombiner_def (h : ℝ≥0∞ → ℝ≥0∞) (x : ℝ≥0∞ × ℝ≥0∞) :
    prodCombiner h x = if h x.1 = ∞ ∨ x.2 = ∞ then ∞ else h x.1 * x.2 :=
  (rfl)

@[simp]
theorem prodCombiner_of_ne_top {p e : ℝ≥0∞} (hp : h p ≠ ∞) (he : e ≠ ∞) :
    prodCombiner h (p, e) = h p * e := by
  simp [prodCombiner_def, hp, he]

@[simp]
theorem prodCombiner_top_right (p : ℝ≥0∞) : prodCombiner h (p, ∞) = ∞ := by
  simp [prodCombiner_def]

theorem prodCombiner_of_eq_top {p : ℝ≥0∞} (hp : h p = ∞) (e : ℝ≥0∞) :
    prodCombiner h (p, e) = ∞ := by
  simp [prodCombiner_def, hp]

theorem measurable_prodCombiner (hh : Measurable h) : Measurable (prodCombiner h) := by
  have h_set : MeasurableSet {x : ℝ≥0∞ × ℝ≥0∞ | h x.1 = ∞ ∨ x.2 = ∞} :=
    ((measurableSet_singleton ∞).preimage (hh.comp measurable_fst)).union
      ((measurableSet_singleton ∞).preimage measurable_snd)
  exact Measurable.ite h_set measurable_const ((hh.comp measurable_fst).mul measurable_snd)

/-- Against a product law whose first factor gives no mass to `0`, the product combiner of a
calibrator integrates to the product of the integrals. -/
theorem lintegral_prodCombiner_prod (hh : IsPToECalibrator h) [SFinite ρ] (hν : ν {0} = 0)
    (hρ : ∫⁻ x, x ∂ρ ≠ ∞) :
    ∫⁻ x, prodCombiner h x ∂ν.prod ρ = (∫⁻ x, h x ∂ν) * ∫⁻ x, x ∂ρ := by
  rw [← lintegral_prod_mul (g := fun x ↦ x) hh.measurable.aemeasurable aemeasurable_id]
  have hν' : ∀ᵐ q ∂ν, q ≠ 0 := measure_eq_zero_iff_ae_notMem.1 hν
  have hρ' : ∀ᵐ e ∂ρ, e < ∞ := ae_lt_top measurable_id hρ
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν',
    Measure.quasiMeasurePreserving_snd.ae hρ'] with x hx₁ hx₂
  have hhx : h x.1 ≠ ∞ := ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 hx₁) (hh.le_inv x.1)
  simp [prodCombiner_def, hhx, hx₂.ne]

/-- **The product combiner is valid for independent inputs** [IWR24, Theorem 3.1]: for a
calibrator `h`, `h p * e` is an e-variable for independent p-values and e-values, since `h p` is
an e-variable independent of `e`. -/
theorem isPEToECombiner_prodCombiner (hh : IsPToECalibrator h) :
    IsPEToECombiner indepPENull (prodCombiner h) where
  antitone_fst e a b hab := by
    by_cases ha : h a = ∞ ∨ e = ∞
    · simp [prodCombiner_def, ha]
    · simp only [not_or] at ha
      have hb : h b ≠ ∞ := ne_top_of_le_ne_top ha.1 (hh.antitone hab)
      dsimp only
      rw [prodCombiner_of_ne_top ha.1 ha.2, prodCombiner_of_ne_top hb ha.2]
      exact mul_le_mul_left (hh.antitone hab) e
  monotone_snd q a b hab := by
    by_cases hb : h q = ∞ ∨ b = ∞
    · simp [prodCombiner_def, hb]
    · simp only [not_or] at hb
      have ha : a ≠ ∞ := ne_top_of_le_ne_top hb.2 hab
      dsimp only
      rw [prodCombiner_of_ne_top hb.1 ha, prodCombiner_of_ne_top hb.1 hb.2]
      exact mul_le_mul_right hab (h q)
  isEVar := by
    refine ⟨measurable_prodCombiner hh.measurable, ?_⟩
    rintro _ ⟨ν, hν, ρ, ⟨hρ, hρ1⟩, rfl⟩
    have := isProbabilityMeasure_of_mem_superUniformNull hν
    have hν0 : ν {0} = 0 := nonpos_iff_eq_zero.1 ((measure_mono (by simp)).trans
      (measure_Iic_le_of_mem_superUniformNull hν 0))
    rw [lintegral_prodCombiner_prod hh hν0 (ne_top_of_le_ne_top ENNReal.one_ne_top hρ1)]
    exact mul_le_one' ((isPToECalibrator_iff_isEVar_superUniformNull.1 hh).2.2.lintegral_le_one
      hν) hρ1

/-! ### The quotient combiner -/

/-- The **quotient combiner** `(p, e) ↦ min (p / e) 1` [IWR24, §3.1], with `p / 0 = ∞` for
`p ≠ 0` and `0 / 0 = 0`. It is a p-combiner for independent inputs
(`ProbabilityTheory.isPEToPCombiner_quotCombiner`), and an admissible one
(`ProbabilityTheory.IsPEToPCombiner.eventuallyEq_quotCombiner_of_le`). -/
noncomputable def quotCombiner (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  min (x.1 / x.2) 1

theorem quotCombiner_def (x : ℝ≥0∞ × ℝ≥0∞) : quotCombiner x = min (x.1 / x.2) 1 :=
  (rfl)

theorem measurable_quotCombiner : Measurable quotCombiner := by
  unfold quotCombiner
  fun_prop

/-- **The quotient combiner is valid for independent inputs** [IWR24, Theorem 3.1]:
`P (p ≤ α E) ≤ α E [E] ≤ α` for a p-variable `p` independent of an e-variable `E`. -/
theorem isPEToPCombiner_quotCombiner : IsPEToPCombiner indepPENull quotCombiner where
  monotone_fst e a b hab := min_le_min_right 1 (ENNReal.div_le_div_right hab e)
  antitone_snd q a b hab := min_le_min_right 1 (ENNReal.div_le_div_left hab q)
  isPVar := by
    refine ⟨measurable_quotCombiner, ?_⟩
    rintro _ ⟨ν, hν, ρ, ⟨hρ, hρ1⟩, rfl⟩ α
    have := isProbabilityMeasure_of_mem_superUniformNull hν
    rcases le_or_gt 1 α with hα | hα
    · exact prob_le_one.trans hα
    have h_set : {x : ℝ≥0∞ × ℝ≥0∞ | quotCombiner x ≤ α} = {x | x.1 / x.2 ≤ α} := by
      ext x
      simp [quotCombiner_def, min_le_iff, not_le.2 hα]
    have hα_top : α ≠ ∞ := ne_top_of_lt hα
    rw [h_set, Measure.prod_apply_symm (measurableSet_le (by fun_prop) measurable_const)]
    calc ∫⁻ e, ν ((fun q ↦ (q, e)) ⁻¹' {x | x.1 / x.2 ≤ α}) ∂ρ
        ≤ ∫⁻ e, α * e ∂ρ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_lt_top measurable_id (ne_top_of_le_ne_top ENNReal.one_ne_top hρ1)]
            with e he
          have h_pre : (fun q ↦ (q, e)) ⁻¹' {x : ℝ≥0∞ × ℝ≥0∞ | x.1 / x.2 ≤ α} = Iic (α * e) := by
            ext q
            simpa using ENNReal.div_le_iff_le_mul (.inr hα_top) (.inl he.ne)
          rw [h_pre]
          exact measure_Iic_le_of_mem_superUniformNull hν _
      _ = α * ∫⁻ e, e ∂ρ := lintegral_const_mul α measurable_id
      _ ≤ α := mul_le_of_le_one_right' hρ1

/-! ### The mean combiner -/

/-- The **mean combiner** `(p, e) ↦ w h p + (1 - w) e` of a calibrator `h` and a weight
`w ≤ 1` [IWR24, §3.1]. It is a combiner for arbitrary dependence
(`ProbabilityTheory.isPEToECombiner_meanCombiner`), and an admissible one when `h` is admissible
and `0 < w < 1` (`ProbabilityTheory.isAdmissible_meanCombiner`). -/
noncomputable def meanCombiner (h : ℝ≥0∞ → ℝ≥0∞) (w : ℝ≥0∞) (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  w * h x.1 + (1 - w) * x.2

theorem meanCombiner_def (h : ℝ≥0∞ → ℝ≥0∞) (w : ℝ≥0∞) (x : ℝ≥0∞ × ℝ≥0∞) :
    meanCombiner h w x = w * h x.1 + (1 - w) * x.2 :=
  (rfl)

/-- The integral of the mean combiner is the weighted mean of the integrals of `h` against the
first marginal and of the second coordinate. -/
theorem lintegral_meanCombiner (hh : Measurable h) (w : ℝ≥0∞) (μ : Measure (ℝ≥0∞ × ℝ≥0∞)) :
    ∫⁻ x, meanCombiner h w x ∂μ =
      w * ∫⁻ q, h q ∂μ.map Prod.fst + (1 - w) * ∫⁻ x, x.2 ∂μ := by
  simp_rw [meanCombiner_def]
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ measurable_snd, lintegral_map hh measurable_fst]

/-- **The mean combiner is valid for arbitrary dependence** [IWR24, Theorem 3.1]: a weighted
mean of the e-variables `h p` and `E` is an e-variable. -/
theorem isPEToECombiner_meanCombiner (hh : IsPToECalibrator h) (hw : w ≤ 1) :
    IsPEToECombiner peNull (meanCombiner h w) where
  antitone_fst e a b hab := add_le_add_left (mul_le_mul_right (hh.antitone hab) w) _
  monotone_snd q a b hab := add_le_add_right (mul_le_mul_right hab _) _
  isEVar := by
    refine ⟨by unfold meanCombiner; have := hh.measurable; fun_prop, fun μ hμ ↦ ?_⟩
    rw [lintegral_meanCombiner hh.measurable]
    calc w * ∫⁻ q, h q ∂μ.map Prod.fst + (1 - w) * ∫⁻ x, x.2 ∂μ ≤ w * 1 + (1 - w) * 1 :=
          add_le_add (mul_le_mul_right ((isPToECalibrator_iff_isEVar_superUniformNull.1
            hh).2.2.lintegral_le_one hμ.1) w) (mul_le_mul_right hμ.2 _)
      _ = 1 := by rw [mul_one, mul_one, add_tsub_cancel_of_le hw]

/-! ### The Bonferroni combiner -/

/-- The **Bonferroni combiner** `(p, e) ↦ min (2 min p e⁻¹) 1` [IWR24, §3.1]: Bonferroni's
correction of the p-variables `p` and `e⁻¹`. It is a p-combiner for arbitrary dependence
(`ProbabilityTheory.isPEToPCombiner_bonferroniCombiner`), and an admissible one
(`ProbabilityTheory.IsPEToPCombiner.eventuallyEq_bonferroniCombiner_of_le`). -/
noncomputable def bonferroniCombiner (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  min (2 * min x.1 x.2⁻¹) 1

theorem bonferroniCombiner_def (x : ℝ≥0∞ × ℝ≥0∞) :
    bonferroniCombiner x = min (2 * min x.1 x.2⁻¹) 1 :=
  (rfl)

/-- **The Bonferroni combiner is valid for arbitrary dependence** [IWR24, Theorem 3.1]: `e⁻¹` is
a p-variable by Markov's inequality, and Bonferroni's correction of two p-variables is one. -/
theorem isPEToPCombiner_bonferroniCombiner : IsPEToPCombiner peNull bonferroniCombiner where
  monotone_fst _ _ _ hab := min_le_min_right 1 (mul_le_mul_right (min_le_min_right _ hab) 2)
  antitone_snd _ _ _ hab :=
    min_le_min_right 1 (mul_le_mul_right (min_le_min_left _ (ENNReal.inv_le_inv.2 hab)) 2)
  isPVar := (isPVar_fst_peNull.two_mul_min isEVar_snd_peNull.isPVar_inv).min_one
    fun _ hμ ↦ (isProbabilityMeasure_of_mem_peNull hμ).measure_univ.le

/-! ### Admissibility of the e-combiners -/

/-- The uniform law on `[0, 1]`, as a law on `ℝ≥0∞`. -/
private noncomputable def unif : Measure ℝ≥0∞ :=
  (volume.restrict (Icc (0 : ℝ) 1)).map ENNReal.ofReal

private lemma unif_mem : unif ∈ superUniformNull :=
  map_ofReal_mem_superUniformNull

private instance : IsProbabilityMeasure unif :=
  isProbabilityMeasure_of_mem_superUniformNull unif_mem

private lemma unif_Iic (a : ℝ≥0∞) : unif (Iic a) = min a 1 := by
  rw [unif, Measure.map_apply ENNReal.measurable_ofReal measurableSet_Iic]
  exact volume_restrict_Icc_ofReal_le a

private lemma unif_Ioc {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≤ 1) : unif (Ioc a b) = b - a := by
  have h := measure_union (μ := unif) (Iic_disjoint_Ioc (le_refl a) (c := b)) measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hab, unif_Iic, unif_Iic, min_eq_left hb, min_eq_left (hab.trans hb),
    add_comm] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hab.trans hb)) h.symm

private lemma ae_unif_le_one : ∀ᵐ q ∂unif, q ≤ 1 := by
  rw [unif, ae_map_iff (p := (· ≤ 1)) ENNReal.measurable_ofReal.aemeasurable measurableSet_Iic]
  exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ ENNReal.ofReal_le_one.2 hx.2

private lemma lintegral_unif (hf : Measurable f) :
    ∫⁻ q, f q ∂unif = ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) :=
  lintegral_map hf ENNReal.measurable_ofReal

/-- Every finite `e` is charged by a probability measure on `ℝ≥0∞` of mean `1`. -/
private lemma exists_lintegral_id_eq_one {e : ℝ≥0∞} (he : e ≠ ∞) :
    ∃ ρ : Measure ℝ≥0∞, IsProbabilityMeasure ρ ∧ ∫⁻ x, x ∂ρ = 1 ∧ ρ {e} ≠ 0 := by
  rcases le_or_gt e 1 with he1 | he1
  · -- the law with weights `1 / 2` on `e` and on `2 - e`
    refine ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac e + (2⁻¹ : ℝ≥0∞) • Measure.dirac (2 - e),
      ⟨by simp [ENNReal.inv_two_add_inv_two]⟩,
      ?_, ?_⟩
    · have h2 : e + (2 - e) = 2 := add_tsub_cancel_of_le (he1.trans one_le_two)
      simp [lintegral_add_measure, ← mul_add, h2, ENNReal.inv_mul_cancel two_ne_zero
        ENNReal.ofNat_ne_top]
    · simp
  · -- the law with weights `1 / e` on `e` and `1 - 1 / e` on `0`
    have he0 : e ≠ 0 := (zero_lt_one.trans he1).ne'
    refine ⟨e⁻¹ • Measure.dirac e + (1 - e⁻¹) • Measure.dirac 0, ⟨?_⟩, ?_, ?_⟩
    · simp [add_tsub_cancel_of_le (ENNReal.inv_le_one.2 he1.le)]
    · simp [lintegral_add_measure, ENNReal.inv_mul_cancel he0 he]
    · simp [he0, he]

/-- **The admissibility argument of [IWR24, Theorem 3.1] for e-combiners.** Let `F` be antitone
in the p-value, infinite at `p = 0` and at `e = ∞`, upper semicontinuous in the p-value, and of
integral `1` against the product of the uniform law and every law of mean `1`. Then every
combiner for independent inputs that dominates `F` on `[0, 1] × [0, ∞]` equals `F` there: where it
exceeds `F` at `(p, e)`, it exceeds `F` on `(p', p] × {e}`, and so has integral more than `1`
against the uniform law times a law of mean `1` charging `e`. -/
private lemma eventuallyLE_of_isPEToECombiner (hF_anti : ∀ e, Antitone fun p ↦ F (p, e))
    (hF_top : ∀ p e, p = 0 ∨ e = ∞ → F (p, e) = ∞)
    (hF_usc : ∀ p e, p ≠ 0 → e ≠ ∞ → UpperSemicontinuousAt (fun q ↦ F (q, e)) p)
    (hF_int : ∀ ρ : Measure ℝ≥0∞, IsProbabilityMeasure ρ → ∫⁻ x, x ∂ρ = 1 →
      ∫⁻ x, F x ∂unif.prod ρ = 1)
    (hG : IsPEToECombiner indepPENull G) (hFG : F ≤ᶠ[𝓟 (Iic 1 ×ˢ univ)] G) :
    G ≤ᶠ[𝓟 (Iic 1 ×ˢ univ)] F := by
  simp only [EventuallyLE, eventually_principal] at hFG ⊢
  rintro ⟨p, e⟩ ⟨hp1, -⟩
  by_contra hlt
  rw [not_le] at hlt
  have hp0 : p ≠ 0 := by rintro rfl; simp [hF_top 0 e (.inl rfl)] at hlt
  have he : e ≠ ∞ := by rintro rfl; simp [hF_top p ∞ (.inr rfl)] at hlt
  -- by upper semicontinuity, `F (·, e) < G (p, e)` at some `p' < p`
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 hp0⟩
  obtain ⟨p', hp'F, hp'p : p' < p⟩ := ((((hF_usc p e hp0 he) _ hlt).filter_mono
    (nhdsWithin_le_nhds (s := Iio p))).and self_mem_nhdsWithin).exists
  have hp'p : p' < p := hp'p
  obtain ⟨ρ, hρ, hρ1, hρe⟩ := exists_lintegral_id_eq_one he
  -- `G ≥ F + c` on `A = (p', p] × {e}`, almost surely under `unif.prod ρ`
  set c := G (p, e) - F (p', e)
  have hc : c ≠ 0 := (tsub_pos_of_lt hp'F).ne'
  set A := Ioc p' p ×ˢ ({e} : Set ℝ≥0∞)
  have hA : MeasurableSet A := measurableSet_Ioc.prod (measurableSet_singleton e)
  have h_le : ∀ᵐ x ∂unif.prod ρ, F x + A.indicator (fun _ ↦ c) x ≤ G x := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_unif_le_one] with x hx
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA]
      obtain ⟨q, e'⟩ := x
      simp only [A, mem_prod, mem_Ioc, mem_singleton_iff] at hxA
      obtain ⟨⟨hx₁, hx₂⟩, rfl⟩ := hxA
      calc F (q, e') + c ≤ F (p', e') + c := add_le_add_left (hF_anti e' hx₁.le) c
        _ = G (p, e') := add_tsub_cancel_of_le hp'F.le
        _ ≤ G (q, e') := hG.antitone_fst e' hx₂
    · rw [indicator_of_notMem hxA, add_zero]
      exact hFG x ⟨hx, mem_univ _⟩
  -- so its integral is more than `1`
  have h_int := (lintegral_mono_ae h_le).trans
    (hG.isEVar.lintegral_le_one (prod_mem_indepPENull unif_mem hρ1.le))
  rw [lintegral_add_right _ (measurable_const.indicator hA), hF_int ρ hρ hρ1,
    lintegral_indicator_const hA, Measure.prod_prod, unif_Ioc hp'p.le hp1] at h_int
  have h_zero : c * ((p - p') * ρ {e}) = 0 :=
    nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left ENNReal.one_ne_top (by simpa using h_int))
  simp only [mul_eq_zero, hc, hρe, or_false, false_or] at h_zero
  exact not_le.2 hp'p (tsub_eq_zero_iff_le.1 h_zero)

/-- **The product combiner is admissible** [IWR24, Theorem 3.1]: for an admissible calibrator
`h`, no combiner for independent inputs dominates `prodCombiner h` strictly on
`[0, 1] × [0, ∞]`. -/
theorem isAdmissible_prodCombiner (hh : IsAdmissiblePToECalibrator h) :
    IsAdmissible (𝓟 (Iic 1 ×ˢ univ)) {G | IsPEToECombiner indepPENull G} (prodCombiner h) := by
  obtain ⟨hh, h_usc, h_top, h_int⟩ := isAdmissiblePToECalibrator_iff.1 hh
  refine ⟨isPEToECombiner_prodCombiner hh, fun G hG hFG ↦
    eventuallyLE_of_isPEToECombiner (isPEToECombiner_prodCombiner hh).antitone_fst ?_ ?_ ?_ hG
      hFG⟩
  · rintro p e (rfl | rfl)
    · exact prodCombiner_of_eq_top h_top e
    · exact prodCombiner_top_right p
  · intro p e hp0 he
    have hhp : h p ≠ ∞ := ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 hp0) (hh.le_inv p)
    -- `prodCombiner h (·, e)` is `h` followed by a monotone map continuous at `h p`
    have h_eq : (fun q ↦ prodCombiner h (q, e)) = (fun x ↦ if x = ∞ then ∞ else x * e) ∘ h := by
      ext q
      by_cases hq : h q = ∞ <;> simp [prodCombiner_def, hq, he]
    rw [h_eq]
    refine ContinuousAt.comp_upperSemicontinuousAt ?_ (h_usc p) fun x y hxy ↦ ?_
    · refine (ENNReal.continuous_mul_const he).continuousAt.congr ?_
      filter_upwards [Iio_mem_nhds hhp.lt_top] with x hx
      simp [(mem_Iio.1 hx).ne]
    · by_cases hy : y = ∞
      · simp [hy]
      · simp [hy, ne_top_of_le_ne_top hy hxy, mul_le_mul_left hxy e]
  · intro ρ hρ hρ1
    have hunif0 : unif {0} = 0 := nonpos_iff_eq_zero.1 ((measure_mono (by simp)).trans
      (measure_Iic_le_of_mem_superUniformNull unif_mem 0))
    rw [lintegral_prodCombiner_prod hh hunif0 (by simp [hρ1]), hρ1, mul_one,
      lintegral_unif hh.measurable, h_int]

/-- **The mean combiner is admissible** [IWR24, Theorem 3.1]: for an admissible calibrator `h`
and `0 < w < 1`, no combiner for arbitrary dependence dominates `meanCombiner h w` strictly on
`[0, 1] × [0, ∞]`. -/
theorem isAdmissible_meanCombiner (hh : IsAdmissiblePToECalibrator h) (hw0 : w ≠ 0)
    (hw1 : w < 1) :
    IsAdmissible (𝓟 (Iic 1 ×ˢ univ)) {G | IsPEToECombiner peNull G} (meanCombiner h w) := by
  obtain ⟨hh, h_usc, h_top, h_int⟩ := isAdmissiblePToECalibrator_iff.1 hh
  have hM := isPEToECombiner_meanCombiner hh hw1.le
  refine ⟨hM, fun G hG hFG ↦ eventuallyLE_of_isPEToECombiner hM.antitone_fst ?_ ?_ ?_
    (hG.anti_set indepPENull_subset_peNull) hFG⟩
  · rintro p e (rfl | rfl)
    · simp [meanCombiner_def, h_top, hw0]
    · simp [meanCombiner_def, (tsub_pos_of_lt hw1).ne']
  · intro p e _ he
    -- `meanCombiner h w (·, e)` is `h` followed by a continuous monotone map
    have h_eq : (fun q ↦ meanCombiner h w (q, e)) = (fun x ↦ w * x + (1 - w) * e) ∘ h := by
      ext q
      simp [meanCombiner_def]
    rw [h_eq]
    exact ((ENNReal.continuous_const_mul (ne_top_of_lt hw1)).add continuous_const).continuousAt
      |>.comp_upperSemicontinuousAt (h_usc p) fun x y hxy ↦
        add_le_add_left (mul_le_mul_right hxy w) _
  · intro ρ hρ hρ1
    rw [lintegral_meanCombiner hh.measurable, Measure.map_fst_prod, measure_univ, one_smul,
      lintegral_unif hh.measurable, h_int, lintegral_prod _ (by fun_prop)]
    simp [hρ1, add_tsub_cancel_of_le hw1.le]

/-! ### Admissibility of the p-combiners -/

/-- The weights of the two-point law of the admissibility argument for the quotient combiner:
given `0 < a < 1`, `0 < e` and `a e < p`, a law `θ δ_e + (1 - θ) δ_b` of mean at most `1` with
`a b ≤ 1` and `a < p θ + a b (1 - θ)`. -/
private lemma exists_twoPoint_quot {a e p : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (he : 0 < e)
    (hae : a * e < p) :
    ∃ θ b : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 0 ≤ b ∧ a * b ≤ 1 ∧ b ≠ e ∧ θ * e + (1 - θ) * b ≤ 1 ∧
      a < p * θ + a * b * (1 - θ) := by
  rcases le_or_gt 1 e with he1 | he1
  · -- weight `1 / e` on `e` and the rest on `0`
    refine ⟨e⁻¹, 0, by positivity, inv_le_one_of_one_le₀ he1, le_rfl, by simp, he.ne, ?_, ?_⟩
    · simp [inv_mul_cancel₀ he.ne']
    · rw [mul_zero, zero_mul, add_zero, ← div_eq_mul_inv, lt_div_iff₀ he]
      exact hae
  · -- weight `(1 - a) / (1 - a e)` on `e` and the rest on `1 / a`
    have hae1 : 0 < 1 - a * e := by nlinarith
    refine ⟨(1 - a) / (1 - a * e), a⁻¹, by apply div_nonneg <;> linarith,
      (div_le_one hae1).2 (by nlinarith), by positivity, by rw [mul_inv_cancel₀ ha0.ne'],
      (lt_trans he1 (one_lt_inv₀ ha0 |>.2 ha1)).ne', ?_, ?_⟩
    · rw [div_mul_eq_mul_div, one_sub_div hae1.ne']
      field_simp
      nlinarith
    · rw [mul_inv_cancel₀ ha0.ne', one_mul, one_sub_div hae1.ne', mul_div_assoc',
        ← add_div, lt_div_iff₀ hae1]
      nlinarith [mul_pos (sub_pos.2 ha1) (sub_pos.2 hae)]

/-- The core of the admissibility of the quotient combiner [IWR24, Theorem 3.1]: a combiner for
independent inputs that is at most `min (p / e) 1` on `[0, 1] × [0, ∞]` cannot be at most `a` at
`(p, e)` with `a e < p`. Against the uniform law and the two-point law of `exists_twoPoint_quot`,
it would be at most `a` with probability more than `a`. -/
private lemma false_of_le_quotCombiner (hG : IsPEToPCombiner indepPENull G)
    (hGQ : ∀ x ∈ Iic 1 ×ˢ univ, G x ≤ quotCombiner x) {p e a : ℝ} (hp1 : p ≤ 1) (ha0 : 0 < a)
    (ha1 : a < 1) (he : 0 < e) (hae : a * e < p)
    (hGa : G (ENNReal.ofReal p, ENNReal.ofReal e) ≤ ENNReal.ofReal a) : False := by
  obtain ⟨θ, b, hθ0, hθ1, hb0, hab, hbe, hmean, hbound⟩ := exists_twoPoint_quot ha0 ha1 he hae
  set ρ := ENNReal.ofReal θ • Measure.dirac (ENNReal.ofReal e) +
    ENNReal.ofReal (1 - θ) • Measure.dirac (ENNReal.ofReal b)
  have hρ : IsProbabilityMeasure ρ :=
    ⟨by simp [ρ, ← ENNReal.ofReal_add hθ0 (sub_nonneg.2 hθ1)]⟩
  have hρ1 : ∫⁻ x, x ∂ρ ≤ 1 := by
    simp only [ρ, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_mul (sub_nonneg.2 hθ1),
      ← ENNReal.ofReal_add (mul_nonneg hθ0 he.le) (mul_nonneg (sub_nonneg.2 hθ1) hb0)]
    exact ENNReal.ofReal_le_one.2 hmean
  have hne : ENNReal.ofReal b ≠ ENNReal.ofReal e := by
    rwa [Ne, ENNReal.ofReal_eq_ofReal_iff hb0 he.le]
  -- `G ≤ a` on `[0, p] × {e}` and on `[0, a b] × {b}`
  have h_sub : Iic (ENNReal.ofReal p) ×ˢ {ENNReal.ofReal e} ∪
      Iic (ENNReal.ofReal (a * b)) ×ˢ {ENNReal.ofReal b} ⊆ {x | G x ≤ ENNReal.ofReal a} := by
    rintro ⟨q, e'⟩ (⟨hq, he'⟩ | ⟨hq, he'⟩) <;> rw [mem_singleton_iff] at he' <;> subst he'
    · exact (hG.monotone_fst _ hq).trans hGa
    · have hq1 : q ≤ 1 := hq.trans (ENNReal.ofReal_le_one.2 hab)
      calc G (q, ENNReal.ofReal b) ≤ quotCombiner (q, ENNReal.ofReal b) :=
            hGQ _ ⟨hq1, mem_univ _⟩
        _ ≤ q / ENNReal.ofReal b := min_le_left _ _
        _ ≤ ENNReal.ofReal a :=
            ENNReal.div_le_of_le_mul (hq.trans_eq (ENNReal.ofReal_mul ha0.le))
  have h_le := (measure_mono (μ := unif.prod ρ) h_sub).trans
    (hG.isPVar.measure_le_le _ (prod_mem_indepPENull unif_mem hρ1) (ENNReal.ofReal a))
  rw [measure_union (disjoint_prod.2 (.inr (disjoint_singleton.2 hne.symm)))
    (measurableSet_Iic.prod (measurableSet_singleton _)), Measure.prod_prod, Measure.prod_prod,
    unif_Iic, unif_Iic, min_eq_left (ENNReal.ofReal_le_one.2 hp1),
    min_eq_left (ENNReal.ofReal_le_one.2 hab)] at h_le
  simp only [ρ, add_apply, smul_apply, smul_eq_mul, Measure.dirac_apply,
    indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one,
    indicator_of_notMem (mt mem_singleton_iff.1 hne),
    indicator_of_notMem (mt mem_singleton_iff.1 hne.symm), mul_zero,
    add_zero, zero_add] at h_le
  have hp0 : 0 < p := (mul_pos ha0 he).trans hae
  rw [← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_mul (mul_nonneg ha0.le hb0),
    ← ENNReal.ofReal_add (mul_nonneg hp0.le hθ0)
      (mul_nonneg (mul_nonneg ha0.le hb0) (sub_nonneg.2 hθ1)),
    ENNReal.ofReal_le_ofReal_iff ha0.le] at h_le
  linarith

/-- **The quotient combiner is admissible** [IWR24, Theorem 3.1]: a p-combiner for independent
inputs that is at most `quotCombiner` on `[0, 1] × [0, ∞]` equals it there. -/
theorem IsPEToPCombiner.eventuallyEq_quotCombiner_of_le (hG : IsPEToPCombiner indepPENull G)
    (hGQ : G ≤ᶠ[𝓟 (Iic 1 ×ˢ univ)] quotCombiner) : G =ᶠ[𝓟 (Iic 1 ×ˢ univ)] quotCombiner := by
  refine hGQ.antisymm ?_
  have hGQ' := hGQ
  simp only [EventuallyLE, eventually_principal] at hGQ' ⊢
  rintro ⟨p, e⟩ ⟨hp1, -⟩
  by_contra hlt
  rw [not_le] at hlt
  have hp1 : p ≤ 1 := mem_Iic.1 hp1
  -- reduce to `p ≤ e`, replacing `e` by `max e p`
  set e₁ := max e p
  have hQ : quotCombiner (p, e₁) = quotCombiner (p, e) := by
    rcases le_total p e with h | h
    · simp [e₁, max_eq_left h]
    · rcases eq_or_ne p 0 with rfl | hp0
      · simp [quotCombiner_def]
      have hp_top : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
      simp only [quotCombiner_def, e₁, max_eq_right h, ENNReal.div_self hp0 hp_top, min_self]
      exact (min_eq_right ((ENNReal.le_div_iff_mul_le (.inr hp0) (.inr hp_top)).2
        (by rwa [one_mul]))).symm
  have hlt₁ : G (p, e₁) < quotCombiner (p, e₁) :=
    hQ ▸ (hG.antitone_snd p (le_max_left e p)).trans_lt hlt
  have hp0 : p ≠ 0 := by rintro rfl; simp [quotCombiner_def] at hlt₁
  have he₁ : e₁ ≠ ∞ := by intro h; simp [quotCombiner_def, h] at hlt₁
  have he₁0 : e₁ ≠ 0 := ne_bot_of_le_ne_bot hp0 (le_max_right e p)
  have hp_top : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hdiv : p / e₁ ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_max_right e p)
  rw [quotCombiner_def, min_eq_left hdiv] at hlt₁
  obtain ⟨α, hGα, hα⟩ := exists_between hlt₁
  have hα0 : α ≠ 0 := (pos_of_gt hGα).ne'
  have hα_top : α ≠ ∞ := ne_top_of_lt (hα.trans_le hdiv)
  have hαe : α * e₁ < p := (ENNReal.lt_div_iff_mul_lt (.inl he₁0) (.inl he₁)).1 hα
  refine false_of_le_quotCombiner hG hGQ' (p := p.toReal) (e := e₁.toReal) (a := α.toReal)
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1))
    (ENNReal.toReal_pos hα0 hα_top) ?_ (ENNReal.toReal_pos he₁0 he₁) ?_ ?_
  · exact (ENNReal.toReal_lt_toReal hα_top ENNReal.one_ne_top).2 (hα.trans_le hdiv) |>.trans_eq
      ENNReal.toReal_one
  · rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hα_top he₁) hp_top).2 hαe
  · rw [ENNReal.ofReal_toReal hp_top, ENNReal.ofReal_toReal he₁, ENNReal.ofReal_toReal hα_top]
    exact hGα.le

/-- The e-variable of the admissibility argument for the Bonferroni combiner, on `[0, 1]` with
the uniform law: `q⁻¹` on `(a, q]`, `a⁻¹` on `(q, q + a² / q]` and `0` elsewhere. -/
private noncomputable def bonferroniEVar (a q x : ℝ) : ℝ≥0∞ :=
  (Ioc a q).indicator (fun _ ↦ ENNReal.ofReal q⁻¹) x +
    (Ioc q (q + a ^ 2 / q)).indicator (fun _ ↦ ENNReal.ofReal a⁻¹) x

private lemma measurable_bonferroniEVar (a q : ℝ) : Measurable (bonferroniEVar a q) :=
  (measurable_const.indicator measurableSet_Ioc).add (measurable_const.indicator measurableSet_Ioc)

/-- For `0 < a < q ≤ 1 / 2`, `q + a² / q ≤ 1`. -/
private lemma add_sq_div_le_one {q a : ℝ} (ha : 0 < a) (haq : a < q) (hq : q ≤ 2⁻¹) :
    q + a ^ 2 / q ≤ 1 := by
  have : a ^ 2 / q < q := by rw [div_lt_iff₀ (ha.trans haq)]; nlinarith
  linarith

/-- For `0 < a < q ≤ 1 / 2`, the uniform law on `[0, 1]` and `bonferroniEVar a q`, which has
mean `1`, form a pair of a p-variable and an e-variable. -/
private lemma map_mem_peNull_bonferroniEVar {q a : ℝ} (ha : 0 < a) (haq : a < q)
    (hq : q ≤ 2⁻¹) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun x ↦ (ENNReal.ofReal x, bonferroniEVar a q x)) ∈
      peNull := by
  have hq0 : 0 < q := ha.trans haq
  have hφ : Measurable fun x ↦ (ENNReal.ofReal x, bonferroniEVar a q x) :=
    ENNReal.measurable_ofReal.prodMk (measurable_bonferroniEVar a q)
  have h_vol {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) :
      volume.restrict (Icc (0 : ℝ) 1) (Ioc s t) = ENNReal.ofReal (t - s) := by
    rw [Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.2 fun x (hx : x ∈ Ioc s t) ↦ mem_Icc.2 ⟨hs.trans hx.1.le, hx.2.trans ht⟩,
      Real.volume_Ioc]
  refine ⟨?_, ?_⟩
  · rw [Measure.map_map measurable_fst hφ]
    exact map_ofReal_mem_superUniformNull
  · rw [lintegral_map measurable_snd hφ]
    simp_rw [bonferroniEVar]
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator_const measurableSet_Ioc, lintegral_indicator_const measurableSet_Ioc,
      h_vol ha.le (by linarith), h_vol hq0.le (add_sq_div_le_one ha haq hq),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (mul_nonneg (inv_pos.2 hq0).le (sub_nonneg.2 haq.le))
        (mul_nonneg (inv_pos.2 ha).le (by rw [add_sub_cancel_left]; positivity))]
    refine ENNReal.ofReal_le_one.2 (le_of_eq ?_)
    field_simp
    ring

/-- The core of the admissibility of the Bonferroni combiner [IWR24, Theorem 3.1]: a combiner for
arbitrary dependence that is at most `min (2 min p e⁻¹) 1` on `[0, 1] × [0, ∞]` cannot be at most
`2 a` at `(q, q⁻¹)` with `0 < a < q ≤ 1 / 2`. Under the uniform law on `[0, 1]` and
`bonferroniEVar a q`, it would be at most `2 a` on `[0, q + a² / q]`, of probability
`q + a² / q > 2 a`. -/
private lemma false_of_le_bonferroniCombiner (hG : IsPEToPCombiner peNull G)
    (hGB : ∀ x ∈ Iic 1 ×ˢ univ, G x ≤ bonferroniCombiner x) {q a : ℝ} (ha : 0 < a)
    (haq : a < q) (hq : q ≤ 2⁻¹)
    (hGa : G (ENNReal.ofReal q, ENNReal.ofReal q⁻¹) ≤ ENNReal.ofReal (2 * a)) : False := by
  have hq0 : 0 < q := ha.trans haq
  set c := q + a ^ 2 / q
  have hc : c ≤ 1 := add_sq_div_le_one ha haq hq
  set Eb := bonferroniEVar a q
  -- `G ≤ 2 a` on `[0, c]`
  have h_sub : Icc 0 c ⊆ {x | G (ENNReal.ofReal x, Eb x) ≤ ENNReal.ofReal (2 * a)} := by
    intro x hx
    obtain ⟨hx0, hxc⟩ := mem_Icc.1 hx
    have hx1 : ENNReal.ofReal x ∈ Iic 1 := ENNReal.ofReal_le_one.2 (hxc.trans hc)
    rcases le_or_gt x a with hxa | hax
    · have hEbx : Eb x = 0 := by
        simp [Eb, bonferroniEVar,
          indicator_of_notMem (fun h ↦ (not_lt.2 hxa) (mem_Ioc.1 h).1 : x ∉ Ioc a q),
          indicator_of_notMem
            (fun h ↦ (not_lt.2 (hxa.trans haq.le)) (mem_Ioc.1 h).1 : x ∉ Ioc q (q + a ^ 2 / q))]
      refine (hGB _ ⟨hx1, mem_univ _⟩).trans ?_
      simp only [hEbx, bonferroniCombiner_def, ENNReal.inv_zero, min_top_right]
      refine (min_le_left _ _).trans ?_
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hxa) 2
    rcases le_or_gt x q with hxq | hqx
    · have hEbx : Eb x = ENNReal.ofReal q⁻¹ := by
        simp [Eb, bonferroniEVar, indicator_of_mem (mem_Ioc.2 ⟨hax, hxq⟩),
          indicator_of_notMem (fun h ↦ (not_lt.2 hxq) (mem_Ioc.1 h).1 : x ∉ Ioc q (q + a ^ 2 / q))]
      simp only [mem_ofPred_eq, hEbx]
      exact (hG.monotone_fst _ (ENNReal.ofReal_le_ofReal hxq)).trans hGa
    · have hEbx : Eb x = ENNReal.ofReal a⁻¹ := by
        simp [Eb, bonferroniEVar,
          indicator_of_notMem (fun h ↦ (not_lt.2 (mem_Ioc.1 h).2) hqx : x ∉ Ioc a q),
          indicator_of_mem (mem_Ioc.2 ⟨hqx, hxc⟩ : x ∈ Ioc q (q + a ^ 2 / q))]
      refine (hGB _ ⟨hx1, mem_univ _⟩).trans ?_
      simp only [hEbx, bonferroniCombiner_def, ← ENNReal.ofReal_inv_of_pos (inv_pos.2 ha), inv_inv]
      refine (min_le_left _ _).trans ?_
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      exact mul_le_mul_right (min_le_right _ _) 2
  -- so `G ≤ 2 a` with probability at least `c > 2 a`
  have h_le := hG.isPVar.measure_le_le _ (map_mem_peNull_bonferroniEVar ha haq hq)
    (ENNReal.ofReal (2 * a))
  rw [Measure.map_apply (ENNReal.measurable_ofReal.prodMk (measurable_bonferroniEVar a q))
    (measurableSet_le hG.isPVar.measurable measurable_const)] at h_le
  have h_ge := (measure_mono (μ := volume.restrict (Icc (0 : ℝ) 1)) h_sub).trans h_le
  rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.2 (Icc_subset_Icc_right hc),
    Real.volume_Icc, sub_zero, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h_ge
  have : 0 < (q - a) ^ 2 / q := by have := sub_pos.2 haq; positivity
  have h_eq : c - 2 * a = (q - a) ^ 2 / q := by simp only [c]; field_simp; ring
  linarith

/-- **The Bonferroni combiner is admissible** [IWR24, Theorem 3.1]: a p-combiner for arbitrary
dependence that is at most `bonferroniCombiner` on `[0, 1] × [0, ∞]` equals it there. -/
theorem IsPEToPCombiner.eventuallyEq_bonferroniCombiner_of_le (hG : IsPEToPCombiner peNull G)
    (hGB : G ≤ᶠ[𝓟 (Iic 1 ×ˢ univ)] bonferroniCombiner) :
    G =ᶠ[𝓟 (Iic 1 ×ˢ univ)] bonferroniCombiner := by
  refine hGB.antisymm ?_
  have hGB' := hGB
  simp only [EventuallyLE, eventually_principal] at hGB' ⊢
  rintro ⟨p, e⟩ -
  by_contra hlt
  rw [not_le] at hlt
  -- reduce to the point `(p₀, p₀⁻¹)` with `p₀ = min (min p e⁻¹) 2⁻¹`
  set p₀ := min (min p e⁻¹) 2⁻¹
  have hB : bonferroniCombiner (p, e) = 2 * p₀ := by
    simp only [bonferroniCombiner_def, p₀, mul_min,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
  have hlt₀ : G (p₀, p₀⁻¹) < 2 * p₀ :=
    ((hG.antitone_snd p₀ (ENNReal.le_inv_iff_le_inv.1 ((min_le_left _ _).trans
      (min_le_right _ _)))).trans (hG.monotone_fst e ((min_le_left _ _).trans
        (min_le_left _ _)))).trans_lt (hB ▸ hlt)
  obtain ⟨α, hGα, hα⟩ := exists_between hlt₀
  have hp₀ : p₀ ≤ 2⁻¹ := min_le_right _ _
  have hp₀_top : p₀ ≠ ∞ := ne_top_of_le_ne_top (by simp) hp₀
  have h2p₀ : 2 * p₀ ≤ 1 := (mul_le_mul_right hp₀ 2).trans_eq
    (ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top)
  have hα_top : α ≠ ∞ := ne_top_of_lt (hα.trans_le h2p₀)
  have hα0 : 0 < α.toReal := ENNReal.toReal_pos (pos_of_gt hGα).ne' hα_top
  have h2α : α.toReal < 2 * p₀.toReal := by
    have := (ENNReal.toReal_lt_toReal hα_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp₀_top)).2 hα
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  refine false_of_le_bonferroniCombiner hG hGB' (q := p₀.toReal) (a := α.toReal / 2)
    (half_pos hα0) (by linarith) (by simpa using (ENNReal.toReal_le_toReal hp₀_top (by simp)).2 hp₀)
    ?_
  rw [ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_toReal hp₀_top,
    mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_toReal hα_top]
  exact hGα.le

end ProbabilityTheory
