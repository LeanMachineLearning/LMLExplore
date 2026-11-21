/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.MeasureTheory.Integral.Bochner.Set
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pivotal exact e-variables

An e-variable `X` for a null `S` is *exact* if `E_P X = 1` for every `P ∈ S`, and *pivotal* if
its law is the same under every `P ∈ S`. Zhang, Ramdas and Wang [ZRW24] ask when a pivotal exact
e-variable with uniformly positive e-power `inf_{Q ∈ 𝒬} E_Q log X > 0` against an alternative `𝒬`
exists (their Conjecture 6.8), and expect the answer to be the separation condition
`0 ∉ closure (span S + conv 𝒬)` in total variation of their Theorem 6.7, under joint
atomlessness. With external randomization, that is for the laws `P ⊗ Leb` on `𝓧 × [0, 1]`, the
answer for bounded e-variables is [EVR26, Note 26, Theorem 1]:

* a bounded measurable `h` with `∫ h dP = 0` for `P ∈ S` and `∫ h dQ ≥ ε > 0` for `Q ∈ 𝒬` (a
  separating function, the dual form of the separation condition) gives an event `B` of
  `𝓧 × [0, 1]` of probability `1 / 2` under every `P ⊗ Leb`, `P ∈ S`, and of probability at least
  `1 / 2 + κ` under every `Q ⊗ Leb`, `Q ∈ 𝒬`; the two-valued variable `1 + η (2 · 1_B - 1)` is
  then a pivotal exact e-variable with e-power at least `2 η κ - (2 / 3) η ^ 2`;
* conversely, a bounded exact e-variable with uniformly positive e-power gives a separating
  function, and forces every signed combination `S' + Q'` (`S'` in the span of `S`, `Q'` in the
  convex hull of `𝒬`) to have total variation bounded away from `0`, with no pivotality needed.

So a separating function exists exactly when a bounded pivotal exact e-variable of the
randomized space has uniformly positive e-power (`exists_isExactEVar_isPivotal_prod_iff`). The
separating function is the separation condition after a Hahn–Banach step in `L¹` of a dominating
measure, which is not formalized here. Without boundedness, the "only if" direction fails, even
for a simple null (`LMLExplore.EValues.Pivotal.Counterexample`).

## Main definitions

* `ProbabilityTheory.IsPivotal X S`: `X` has the same law under every member of `S`.
* `ProbabilityTheory.randomizedEvent f`: the event `{(x, u) | u ≤ f x}` of `𝓧 × [0, 1]`, for
  `f : 𝓧 → [0, 1]`.
* `ProbabilityTheory.twoPointEVar B η`: the two-valued variable `1 + η (2 · 1_B - 1)`.

## Main statements

* `ProbabilityTheory.measureReal_prod_randomizedEvent`: `(P ⊗ Leb) {u ≤ f x} = ∫ f dP`.
* `ProbabilityTheory.exists_measurableSet_measureReal_prod_eq_half`: the event of probability
  `1 / 2` under the null built from a separating function.
* `ProbabilityTheory.isExactEVar_twoPointEVar`, `ProbabilityTheory.isPivotal_twoPointEVar`,
  `ProbabilityTheory.le_eintegral_log_twoPointEVar`: the two-valued variable is a pivotal exact
  e-variable, with a lower bound on its e-power.
* `ProbabilityTheory.exists_isExactEVar_isPivotal_twoPointEVar` [EVR26, Note 26, Theorem 1,
  (1) ⇒ (2)], from a separating function.
* `ProbabilityTheory.le_mul_tvDist_of_isExactEVar`,
  `ProbabilityTheory.le_mul_tvDist_of_isExactEVar_of_le_eintegral_log` [EVR26, Note 26,
  Theorem 1, (3) ⇒ (1), bounded case; ZRW24, Theorem 6.7, "only if"].
* `ProbabilityTheory.exists_isExactEVar_isPivotal_prod_iff`: a separating function exists exactly
  when a bounded pivotal exact e-variable of the randomized space has uniformly positive e-power.

## Implementation notes

The randomization is external: the space is `𝓧 × [0, 1]` with the laws `P ⊗ Leb`, a case of the
joint atomlessness condition (JA∞) of [EVR26, Note 26]. Under it the conditional expectation
of the note is not needed: the event `{(x, u) | u ≤ f x}` has probability `∫ f dP` under
`P ⊗ Leb` by Fubini. Finite nonnegative combinations of members of `S` are the elements of
`Submodule.span ℝ≥0 S`, and convex combinations of members of `𝒬` those of `convexHull ℝ≥0 𝒬`; a
signed combination `S' + Q'` is `μ₁ - μ₂ + ν` with `μ₁, μ₂` in the first and `ν` in the second, of
total variation `tvDist (μ₁ + ν) μ₂`.

This file ports and adapts `EValuesResearch/Results/PivotalEVariables.lean` of the paper project
`RemyDegenne/evalues_research`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 26 and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [ZRW24] Z. Zhang, A. Ramdas and R. Wang, *On the existence of powerful p-values and e-values for
  composite hypotheses*, arXiv:2305.16539, Theorem 6.7 and Conjecture 6.8.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal unitInterval

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓩]

/-! ### Pivotal random variables -/

/-- A random variable `X` is **pivotal** for a set of measures `S` if it has the same law under
every member of `S` [ZRW24, §6.2]. -/
def IsPivotal (X : Ω → 𝓨) (S : Set (Measure Ω)) : Prop :=
  ∀ ⦃P⦄, P ∈ S → ∀ ⦃P'⦄, P' ∈ S → P.map X = P'.map X

section IsPivotal

variable {X : Ω → 𝓨} {S T : Set (Measure Ω)}

theorem isPivotal_iff : IsPivotal X S ↔ ∀ P ∈ S, ∀ P' ∈ S, P.map X = P'.map X := Iff.rfl

/-- A measurable random variable is pivotal exactly when each of its events has the same
probability under every member of the null. -/
theorem isPivotal_iff_measure_preimage (hX : Measurable X) :
    IsPivotal X S ↔ ∀ P ∈ S, ∀ P' ∈ S, ∀ s, MeasurableSet s → P (X ⁻¹' s) = P' (X ⁻¹' s) := by
  refine forall₂_congr fun P _ ↦ forall₂_congr fun P' _ ↦ ?_
  rw [Measure.ext_iff]
  exact forall₂_congr fun s hs ↦ by rw [Measure.map_apply hX hs, Measure.map_apply hX hs]

/-- Every random variable is pivotal for a simple null. -/
theorem isPivotal_singleton (X : Ω → 𝓨) (P : Measure Ω) : IsPivotal X {P} := by
  rintro _ rfl _ rfl
  rfl

theorem IsPivotal.anti_set (hST : S ⊆ T) (hX : IsPivotal X T) : IsPivotal X S :=
  fun _ hP _ hP' ↦ hX (hST hP) (hST hP')

/-- A measurable function of a measurable pivotal random variable is pivotal. -/
theorem IsPivotal.comp {g : 𝓨 → 𝓩} (hg : Measurable g) (hX : Measurable X)
    (hpiv : IsPivotal X S) : IsPivotal (g ∘ X) S := fun _ hP _ hP' ↦ by
  rw [← Measure.map_map hg hX, ← Measure.map_map hg hX, hpiv hP hP']

end IsPivotal

/-! ### The randomized event -/

/-- The event `{(x, u) | u ≤ f x}` of the randomized space `𝓧 × [0, 1]`: under `P ⊗ Leb`, its
conditional probability given `x` is `f x` ([EVR26, Note 26, proof of Theorem 1, (1) ⇒ (2)]). -/
def randomizedEvent (f : 𝓧 → I) : Set (𝓧 × I) :=
  {p | p.2 ≤ f p.1}

@[simp]
theorem mem_randomizedEvent {f : 𝓧 → I} {p : 𝓧 × I} : p ∈ randomizedEvent f ↔ p.2 ≤ f p.1 :=
  Iff.rfl

theorem measurableSet_randomizedEvent {f : 𝓧 → I} (hf : Measurable f) :
    MeasurableSet (randomizedEvent f) :=
  measurableSet_le measurable_snd (hf.comp measurable_fst)

/-- Under `P ⊗ Leb`, the event `{(x, u) | u ≤ f x}` has measure `∫⁻ x, f x ∂P`. -/
theorem prod_randomizedEvent (P : Measure 𝓧) {f : 𝓧 → I} (hf : Measurable f) :
    P.prod volume (randomizedEvent f) = ∫⁻ x, ENNReal.ofReal (f x) ∂P := by
  rw [Measure.prod_apply (measurableSet_randomizedEvent hf)]
  exact lintegral_congr fun x ↦ unitInterval.volume_Iic (f x)

/-- **The randomized event** ([EVR26, Note 26, proof of Theorem 1, (1) ⇒ (2)]): for a
measurable `f : 𝓧 → [0, 1]`, the event `{(x, u) | u ≤ f x}` has probability `∫ f dP` under
`P ⊗ Leb`, for every measure `P`. -/
theorem measureReal_prod_randomizedEvent (P : Measure 𝓧) {f : 𝓧 → I} (hf : Measurable f) :
    (P.prod volume).real (randomizedEvent f) = ∫ x, (f x : ℝ) ∂P := by
  rw [measureReal_def, prod_randomizedEvent P hf, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x ↦ (f x).2.1) (measurable_subtype_coe.comp hf).aestronglyMeasurable]

/-! ### An event of probability one half under the null -/

/-- The function `(1 + h / c) / 2`, projected to `[0, 1]`, of the proof of [EVR26, Note 26,
Theorem 1, (1) ⇒ (2)]. -/
private noncomputable def halfShift (h : 𝓧 → ℝ) (c : ℝ) (x : 𝓧) : I :=
  projIcc 0 1 zero_le_one (1 / 2 + h x / (2 * c))

private lemma measurable_halfShift {h : 𝓧 → ℝ} (hh : Measurable h) (c : ℝ) :
    Measurable (halfShift h c) :=
  continuous_projIcc.measurable.comp (measurable_const.add (hh.div_const _))

/-- Where `|h x| ≤ c`, the projection in `halfShift` does nothing. -/
private lemma coe_halfShift {h : 𝓧 → ℝ} {c : ℝ} {x : 𝓧} (hx : |h x| ≤ c) :
    (halfShift h c x : ℝ) = 1 / 2 + h x / (2 * c) := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hx
  have hle : |h x / (2 * c)| ≤ 1 / 2 := by
    rcases hc.eq_or_lt with rfl | hc
    · simp
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_le_iff₀ (by linarith)]
    linarith
  rw [abs_le] at hle
  rw [halfShift, projIcc_of_mem _ ⟨by linarith, by linarith⟩]

/-- The event `{(x, u) | u ≤ halfShift h c x}` has probability `1 / 2 + (∫ h dP) / (2 c)` under
`P ⊗ Leb`. -/
private lemma measureReal_prod_randomizedEvent_halfShift {P : Measure 𝓧} [IsProbabilityMeasure P]
    {h : 𝓧 → ℝ} (hh : Measurable h) {c : ℝ} (hc : ∀ᵐ x ∂P, |h x| ≤ c) :
    (P.prod volume).real (randomizedEvent (halfShift h c)) =
      1 / 2 + (∫ x, h x ∂P) / (2 * c) := by
  have hint : Integrable h P := .of_bound hh.aestronglyMeasurable c (by simpa using hc)
  rw [measureReal_prod_randomizedEvent P (measurable_halfShift hh c),
    integral_congr_ae (hc.mono fun x hx ↦ coe_halfShift hx),
    integral_add (integrable_const _) (hint.div_const _), integral_const, integral_div]
  simp

/-- **An event of probability one half under the null** ([EVR26, Note 26, Theorem 1,
(1) ⇒ (2)], from a separating function): if a measurable `h`, bounded by `c` almost everywhere
for every measure of `S ∪ 𝒬`, has `∫ h dP = 0` for `P ∈ S` and `∫ h dQ ≥ ε` for `Q ∈ 𝒬`, then the
randomized space `𝓧 × [0, 1]` has an event of probability `1 / 2` under every `P ⊗ Leb`, `P ∈ S`,
and of probability at least `1 / 2 + ε / (2 c)` under every `Q ⊗ Leb`, `Q ∈ 𝒬`. -/
theorem exists_measurableSet_measureReal_prod_eq_half {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsProbabilityMeasure Q)
    {h : 𝓧 → ℝ} (hh : Measurable h) {c ε : ℝ} (hc : ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |h x| ≤ c)
    (hhS : ∀ P ∈ S, ∫ x, h x ∂P = 0) (hh𝒬 : ∀ Q ∈ 𝒬, ε ≤ ∫ x, h x ∂Q) :
    ∃ B : Set (𝓧 × I), MeasurableSet B ∧ (∀ P ∈ S, (P.prod volume).real B = 1 / 2) ∧
      ∀ Q ∈ 𝒬, 1 / 2 + ε / (2 * c) ≤ (Q.prod volume).real B := by
  refine ⟨randomizedEvent (halfShift h c), measurableSet_randomizedEvent
    (measurable_halfShift hh c), fun P hP ↦ ?_, fun Q hQ ↦ ?_⟩
  · have := hS P hP
    rw [measureReal_prod_randomizedEvent_halfShift hh (hc P (.inl hP)), hhS P hP]
    simp
  · have := h𝒬 Q hQ
    rw [measureReal_prod_randomizedEvent_halfShift hh (hc Q (.inr hQ))]
    obtain ⟨x, hx⟩ := (hc Q (.inr hQ)).exists
    have hc : 0 ≤ 2 * c := by linarith [(abs_nonneg (h x)).trans hx]
    gcongr
    exact hh𝒬 Q hQ

/-! ### The two-valued e-variable -/

/-- The two-valued variable `1 + η (2 · 1_B - 1)`, equal to `1 + η` on `B` and to `1 - η` off `B`
([EVR26, Note 26, Theorem 1 (2)]). -/
noncomputable def twoPointEVar (B : Set Ω) (η : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + η * (2 * B.indicator 1 ω - 1))

section TwoPoint

variable {B : Set Ω} {η : ℝ} {ω : Ω}

@[simp]
theorem twoPointEVar_of_mem (η : ℝ) (hω : ω ∈ B) :
    twoPointEVar B η ω = ENNReal.ofReal (1 + η) := by
  rw [twoPointEVar, indicator_of_mem hω]
  norm_num

@[simp]
theorem twoPointEVar_of_notMem (η : ℝ) (hω : ω ∉ B) :
    twoPointEVar B η ω = ENNReal.ofReal (1 - η) := by
  rw [twoPointEVar, indicator_of_notMem hω]
  congr 1
  ring

theorem measurable_twoPointEVar (hB : MeasurableSet B) (η : ℝ) :
    Measurable (twoPointEVar B η) :=
  (measurable_const.add (measurable_const.mul
    ((measurable_const.mul (measurable_one.indicator hB)).sub measurable_const))).ennreal_ofReal

/-- For `η ≥ 0`, the two-valued variable is at most `1 + η`. -/
theorem twoPointEVar_le (hη : 0 ≤ η) (B : Set Ω) (ω : Ω) :
    twoPointEVar B η ω ≤ ENNReal.ofReal (1 + η) := by
  by_cases hω : ω ∈ B
  · rw [twoPointEVar_of_mem η hω]
  · rw [twoPointEVar_of_notMem η hω]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The expectation of `1 + η (2 · 1_B - 1)` is `(1 + η) P(B) + (1 - η) P(Bᶜ)`. -/
theorem lintegral_twoPointEVar (P : Measure Ω) (hB : MeasurableSet B) (η : ℝ) :
    ∫⁻ ω, twoPointEVar B η ω ∂P =
      ENNReal.ofReal (1 + η) * P B + ENNReal.ofReal (1 - η) * P Bᶜ := by
  have h : twoPointEVar B η = fun ω ↦ B.indicator (fun _ ↦ ENNReal.ofReal (1 + η)) ω +
      Bᶜ.indicator (fun _ ↦ ENNReal.ofReal (1 - η)) ω := by
    ext ω
    by_cases hω : ω ∈ B <;> simp [hω, twoPointEVar_of_mem, twoPointEVar_of_notMem]
  rw [h, lintegral_add_left (measurable_const.indicator hB), lintegral_indicator_const hB,
    lintegral_indicator_const hB.compl]

/-- **The two-valued e-variable is exact** ([EVR26, Note 26, Theorem 1 (2)]): for an event `B` of
probability `1 / 2` under every member of a null of probability measures and `|η| ≤ 1`, the
variable `1 + η (2 · 1_B - 1)` is an exact e-variable. -/
theorem isExactEVar_twoPointEVar {S : Set (Measure Ω)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hB : MeasurableSet B) (hSB : ∀ P ∈ S, P.real B = 1 / 2) (hη : |η| ≤ 1) :
    IsExactEVar (twoPointEVar B η) S := by
  refine .of_lintegral_eq_one (measurable_twoPointEVar hB η) fun P hP ↦ ?_
  have := hS P hP
  rw [abs_le] at hη
  rw [lintegral_twoPointEVar P hB, ← ENNReal.toReal_eq_one_iff,
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + η),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - η), ← measureReal_def,
    probReal_compl_eq_one_sub hB, hSB P hP]
  ring

/-- **The two-valued e-variable is pivotal** ([EVR26, Note 26, Theorem 1 (2)]): for an event `B`
with the same probability under every member of a null of probability measures, the variable
`1 + η (2 · 1_B - 1)` has the same law under every member of the null. -/
theorem isPivotal_twoPointEVar {S : Set (Measure Ω)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hB : MeasurableSet B) (hSB : ∀ P ∈ S, ∀ P' ∈ S, P B = P' B) (η : ℝ) :
    IsPivotal (twoPointEVar B η) S := by
  refine (isPivotal_iff_measure_preimage (measurable_twoPointEVar hB η)).2
    fun P hP P' hP' s _ ↦ ?_
  have := hS P hP
  have := hS P' hP'
  -- the preimage of `s` is `∅`, `B`, `Bᶜ` or the whole space
  have hpre : twoPointEVar B η ⁻¹' s = ∅ ∨ twoPointEVar B η ⁻¹' s = B ∨
      twoPointEVar B η ⁻¹' s = Bᶜ ∨ twoPointEVar B η ⁻¹' s = univ := by
    by_cases ha : ENNReal.ofReal (1 + η) ∈ s <;> by_cases hb : ENNReal.ofReal (1 - η) ∈ s <;>
      [refine .inr (.inr (.inr ?_)); refine .inr (.inl ?_); refine .inr (.inr (.inl ?_));
        refine .inl ?_] <;>
      ext ω <;> by_cases hω : ω ∈ B <;> simp [hω, ha, hb]
  rcases hpre with h | h | h | h <;> rw [h]
  · simp
  · exact hSB P hP P' hP'
  · rw [prob_compl_eq_one_sub hB, prob_compl_eq_one_sub hB, hSB P hP P' hP']
  · simp

/-- The logarithm of `1 + η (2 · 1_B - 1)` for `|η| < 1`. -/
private lemma log_twoPointEVar (B : Set Ω) (hη : |η| < 1) (ω : Ω) :
    ENNReal.log (twoPointEVar B η ω) =
      ((Real.log (1 - η) + B.indicator (fun _ ↦ Real.log (1 + η) - Real.log (1 - η)) ω : ℝ) :
        EReal) := by
  rw [abs_lt] at hη
  by_cases hω : ω ∈ B
  · rw [twoPointEVar_of_mem η hω, ENNReal.log_ofReal_of_pos (by linarith), indicator_of_mem hω]
    congr 1
    ring
  · rw [twoPointEVar_of_notMem η hω, ENNReal.log_ofReal_of_pos (by linarith),
      indicator_of_notMem hω, add_zero]

/-- **The e-power of the two-valued e-variable** ([EVR26, Note 26, Theorem 1 (2)]): for an event
`B` of probability at least `1 / 2 + κ` under a probability measure `Q`, with `κ ≥ 0`, and
`0 ≤ η ≤ 1 / 2`, `E_Q log (1 + η (2 · 1_B - 1)) ≥ 2 η κ - (2 / 3) η ^ 2`. -/
theorem le_eintegral_log_twoPointEVar {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hB : MeasurableSet B) {κ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hκ : 0 ≤ κ)
    (hQB : 1 / 2 + κ ≤ Q.real B) :
    ((2 * η * κ - 2 / 3 * η ^ 2 : ℝ) : EReal) ≤
      ∫ᵉ ω, ENNReal.log (twoPointEVar B η ω) ∂Q := by
  have hη1 : |η| < 1 := by rw [abs_of_nonneg hη0]; linarith
  have hint : Integrable (fun ω ↦ Real.log (1 - η) +
      B.indicator (fun _ ↦ Real.log (1 + η) - Real.log (1 - η)) ω) Q :=
    (integrable_const _).add ((integrable_const _).indicator hB)
  rw [eintegral_congr (log_twoPointEVar B hη1), eintegral_eq_integral hint,
    EReal.coe_le_coe_iff, integral_const_add_indicator_const _ _ hB, smul_eq_mul]
  -- `E_Q log X = (log (1 + η) + log (1 - η)) / 2 + (Q(B) - 1 / 2) (log (1 + η) - log (1 - η))`
  have hL := Real.two_mul_le_log_one_add_sub_log_one_sub hη0 (by linarith)
  have hsum := Real.neg_four_div_three_mul_sq_le_log_one_add_add_log_one_sub
    (by rwa [abs_of_nonneg hη0])
  have h1 : 0 ≤ (Q.real B - 1 / 2 - κ) * (Real.log (1 + η) - Real.log (1 - η)) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ κ * (Real.log (1 + η) - Real.log (1 - η) - 2 * η) :=
    mul_nonneg hκ (by linarith)
  nlinarith

end TwoPoint

/-- **A pivotal exact e-variable from a separating function** ([EVR26, Note 26, Theorem 1,
(1) ⇒ (2)]): if a measurable `h`, bounded by `c` almost everywhere for every measure of `S ∪ 𝒬`,
has `∫ h dP = 0` for `P ∈ S` and `∫ h dQ ≥ ε` for `Q ∈ 𝒬`, then the randomized space
`𝓧 × [0, 1]` has an event `B` such that, for every `0 ≤ η ≤ 1 / 2`, the two-valued variable
`1 + η (2 · 1_B - 1)` is a pivotal exact e-variable for the laws `P ⊗ Leb`, `P ∈ S`, with
`E log ≥ 2 η κ - (2 / 3) η ^ 2` under every `Q ⊗ Leb`, `Q ∈ 𝒬`, where `κ = ε / (2 c)`. -/
theorem exists_isExactEVar_isPivotal_twoPointEVar {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsProbabilityMeasure Q)
    {h : 𝓧 → ℝ} (hh : Measurable h) {c ε : ℝ} (hc : ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |h x| ≤ c)
    (hhS : ∀ P ∈ S, ∫ x, h x ∂P = 0) (hh𝒬 : ∀ Q ∈ 𝒬, ε ≤ ∫ x, h x ∂Q) :
    ∃ B : Set (𝓧 × I), MeasurableSet B ∧ ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 2 →
      IsExactEVar (twoPointEVar B η) ((fun P ↦ P.prod volume) '' S) ∧
      IsPivotal (twoPointEVar B η) ((fun P ↦ P.prod volume) '' S) ∧
      ∀ Q ∈ 𝒬, ((2 * η * (ε / (2 * c)) - 2 / 3 * η ^ 2 : ℝ) : EReal) ≤
        ∫ᵉ ω, ENNReal.log (twoPointEVar B η ω) ∂(Q.prod volume) := by
  -- the event: from `h` when `ε / (2 c) ≥ 0`, from `0` otherwise
  obtain ⟨B, hB, hBS, hB𝒬⟩ : ∃ B : Set (𝓧 × I), MeasurableSet B ∧
      (∀ P ∈ S, (P.prod volume).real B = 1 / 2) ∧
      ∀ Q ∈ 𝒬, 1 / 2 + max (ε / (2 * c)) 0 ≤ (Q.prod volume).real B := by
    rcases le_total 0 (ε / (2 * c)) with hε | hε
    · obtain ⟨B, hB, h1, h2⟩ := exists_measurableSet_measureReal_prod_eq_half hS h𝒬 hh hc hhS hh𝒬
      exact ⟨B, hB, h1, fun Q hQ ↦ by rw [max_eq_left hε]; exact h2 Q hQ⟩
    · obtain ⟨B, hB, h1, h2⟩ := exists_measurableSet_measureReal_prod_eq_half
        (h := fun _ ↦ 0) (c := 0) (ε := 0) hS h𝒬 measurable_const (by simp) (by simp) (by simp)
      exact ⟨B, hB, h1, fun Q hQ ↦ by simpa [max_eq_right hε] using h2 Q hQ⟩
  have hS' : ∀ P ∈ (fun P ↦ P.prod (volume : Measure I)) '' S, IsProbabilityMeasure P := by
    rintro _ ⟨P, hP, rfl⟩
    have := hS P hP
    infer_instance
  refine ⟨B, hB, fun η hη0 hη ↦ ⟨?_, ?_, fun Q hQ ↦ ?_⟩⟩
  · exact isExactEVar_twoPointEVar hS' hB (by rintro _ ⟨P, hP, rfl⟩; exact hBS P hP)
      (by rw [abs_le]; constructor <;> linarith)
  · refine isPivotal_twoPointEVar hS' hB ?_ η
    rintro _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩
    have := hS P hP
    have := hS P' hP'
    rw [← ofReal_measureReal, ← ofReal_measureReal, hBS P hP, hBS P' hP']
  · have := h𝒬 Q hQ
    calc ((2 * η * (ε / (2 * c)) - 2 / 3 * η ^ 2 : ℝ) : EReal)
    _ ≤ ((2 * η * max (ε / (2 * c)) 0 - 2 / 3 * η ^ 2 : ℝ) : EReal) := by
      rw [EReal.coe_le_coe_iff]
      gcongr
      exact le_max_left _ _
    _ ≤ ∫ᵉ ω, ENNReal.log (twoPointEVar B η ω) ∂(Q.prod volume) :=
      le_eintegral_log_twoPointEVar hB hη0 hη (le_max_right _ _) (hB𝒬 Q hQ)

/-! ### Bounded exact e-variables force the separation -/

/-- **The e-power is at most the expected gain**: `E_Q log X ≤ E_Q (X - 1)` for
`X : Ω → ℝ≥0∞` that is almost everywhere finite with `X - 1` integrable under `Q`. -/
theorem le_integral_toReal_sub_one_of_le_eintegral_log {Q : Measure Ω} {X : Ω → ℝ≥0∞}
    (hXQ : ∀ᵐ x ∂Q, X x ≠ ∞) (hint : Integrable (fun x ↦ (X x).toReal - 1) Q) {c : ℝ}
    (hc : (c : EReal) ≤ ∫ᵉ x, ENNReal.log (X x) ∂Q) :
    c ≤ ∫ x, ((X x).toReal - 1) ∂Q := by
  have hae : ∀ᵐ x ∂Q, (X x : EReal) - 1 = (((X x).toReal - 1 : ℝ) : EReal) := by
    filter_upwards [hXQ] with x hx
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hx, EReal.coe_one]
  have h := hc.trans (eintegral_mono fun x ↦ ENNReal.log_le_sub_one (X x))
  rwa [eintegral_congr_ae hae, eintegral_eq_integral hint, EReal.coe_le_coe_iff] at h

/-- **A bounded exact e-variable with positive power separates the null from the alternative**
([EVR26, Note 26, Theorem 1, (3) ⇒ (1)], bounded case; [ZRW24, Theorem 6.7], "only if"): let `X`
be an exact e-variable for a null `S` of probability measures, with `|X - 1| ≤ M` almost
everywhere for every measure of `S ∪ 𝒬`, and `E_Q (X - 1) ≥ c` for every `Q ∈ 𝒬`. For finite
nonnegative combinations `μ₁, μ₂` of members of `S` and a convex combination `ν` of members of
`𝒬`, the signed measure `μ₁ - μ₂ + ν` has total variation at least `c / M`. Pivotality is not
needed. -/
theorem le_mul_tvDist_of_isExactEVar {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsFiniteMeasure Q) {X : 𝓧 → ℝ≥0∞}
    (hX : IsExactEVar X S) {M c : ℝ} (hXM : ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |(X x).toReal - 1| ≤ M)
    (hc : ∀ Q ∈ 𝒬, c ≤ ∫ x, ((X x).toReal - 1) ∂Q)
    {μ₁ μ₂ ν : Measure 𝓧} (hμ₁ : μ₁ ∈ Submodule.span ℝ≥0 S) (hμ₂ : μ₂ ∈ Submodule.span ℝ≥0 S)
    (hν : ν ∈ convexHull ℝ≥0 𝒬) :
    c ≤ M * tvDist (μ₁ + ν) μ₂ := by
  have hf : Measurable fun x ↦ (X x).toReal - 1 := hX.measurable.ennreal_toReal.sub_const 1
  have hS0 : ∀ P ∈ S, ∫ x, ((X x).toReal - 1) ∂P = 0 := fun P hP ↦
    have := hS P hP
    hX.integral_toReal_sub_one_eq_zero hP
  have hSf : ∀ P ∈ S, IsFiniteMeasure P := fun P hP ↦ have := hS P hP; inferInstance
  have hSM : ∀ P ∈ S, ∀ᵐ x ∂P, |(X x).toReal - 1| ≤ M := fun P hP ↦ hXM P (.inl hP)
  have h𝒬M : ∀ Q ∈ 𝒬, ∀ᵐ x ∂Q, |(X x).toReal - 1| ≤ M := fun Q hQ ↦ hXM Q (.inr hQ)
  have hSi : ∀ P ∈ S, Integrable (fun x ↦ (X x).toReal - 1) P := fun P hP ↦
    have := hSf P hP
    .of_bound hf.aestronglyMeasurable M (by simpa using hSM P hP)
  have h𝒬i : ∀ Q ∈ 𝒬, Integrable (fun x ↦ (X x).toReal - 1) Q := fun Q hQ ↦
    have := h𝒬 Q hQ
    .of_bound hf.aestronglyMeasurable M (by simpa using h𝒬M Q hQ)
  have := isFiniteMeasure_of_mem_span hSf hμ₁
  have := isFiniteMeasure_of_mem_span hSf hμ₂
  have := isFiniteMeasure_of_mem_convexHull h𝒬 hν
  have h1M := ae_of_mem_span hSM hμ₁
  have hνM := ae_of_mem_convexHull h𝒬M hν
  -- the integral of `X - 1` against `μ₁ - μ₂ + ν` is at least `c`
  have key := norm_integral_sub_integral_le_mul_tvDist (μ := μ₁ + ν) (ν := μ₂)
    hf.aestronglyMeasurable hf.aestronglyMeasurable
    ((ae_add_measure_iff.2 ⟨h1M, hνM⟩).mono fun x hx ↦ by rwa [Real.norm_eq_abs])
    ((ae_of_mem_span hSM hμ₂).mono fun x hx ↦ by rwa [Real.norm_eq_abs])
  rw [integral_add_measure (integrable_of_mem_span hSi hμ₁)
    (.of_bound hf.aestronglyMeasurable M (by simpa using hνM)),
    integral_eq_zero_of_mem_span hSi hS0 hμ₁,
    integral_eq_zero_of_mem_span hSi hS0 hμ₂, zero_add, sub_zero, Real.norm_eq_abs] at key
  exact (le_integral_of_mem_convexHull h𝒬i hc hν).trans ((le_abs_self _).trans key)

/-- **A bounded exact e-variable with positive e-power separates the null from the alternative**
([EVR26, Note 26, Theorem 1, (3) ⇒ (1)], bounded case): let `X` be an exact e-variable for a null
`S` of probability measures, with `|X - 1| ≤ M` almost everywhere for every measure of `S ∪ 𝒬`,
finite almost everywhere for every measure of `𝒬`, and `E_Q log X ≥ c` for every `Q ∈ 𝒬`. For
finite nonnegative combinations `μ₁, μ₂` of members of `S` and a convex combination `ν` of
members of `𝒬`, the signed measure `μ₁ - μ₂ + ν` has total variation at least `c / M`. -/
theorem le_mul_tvDist_of_isExactEVar_of_le_eintegral_log {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsFiniteMeasure Q) {X : 𝓧 → ℝ≥0∞}
    (hX : IsExactEVar X S) {M c : ℝ} (hXM : ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |(X x).toReal - 1| ≤ M)
    (hX𝒬 : ∀ Q ∈ 𝒬, ∀ᵐ x ∂Q, X x ≠ ∞)
    (hc : ∀ Q ∈ 𝒬, (c : EReal) ≤ ∫ᵉ x, ENNReal.log (X x) ∂Q)
    {μ₁ μ₂ ν : Measure 𝓧} (hμ₁ : μ₁ ∈ Submodule.span ℝ≥0 S) (hμ₂ : μ₂ ∈ Submodule.span ℝ≥0 S)
    (hν : ν ∈ convexHull ℝ≥0 𝒬) :
    c ≤ M * tvDist (μ₁ + ν) μ₂ :=
  le_mul_tvDist_of_isExactEVar hS h𝒬 hX hXM (fun Q hQ ↦ have := h𝒬 Q hQ
    le_integral_toReal_sub_one_of_le_eintegral_log (hX𝒬 Q hQ)
      (.of_bound (hX.measurable.ennreal_toReal.sub_const 1).aestronglyMeasurable M
        (by simpa using hXM Q (.inr hQ))) (hc Q hQ)) hμ₁ hμ₂ hν

/-! ### The characterization with external randomization -/

/-- **A separating function from a bounded exact e-variable of the randomized space**: let `S` be
a null of probability measures and `𝒬` an alternative of finite measures. If
`X : 𝓧 × [0, 1] → ℝ≥0∞`, bounded by `K` almost everywhere for every `P ⊗ Leb`, `P ∈ S ∪ 𝒬`, is an
exact e-variable for the laws `P ⊗ Leb`, `P ∈ S`, with `E log X ≥ c` under every `Q ⊗ Leb`,
`Q ∈ 𝒬`, then `h x = ∫ (X (x, u) - 1) du` is bounded by `max K 1` almost everywhere for every
member of `S ∪ 𝒬`, has `∫ h dP = 0` for `P ∈ S` and `∫ h dQ ≥ c` for `Q ∈ 𝒬`. -/
theorem exists_integral_eq_zero_of_isExactEVar_prod {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsFiniteMeasure Q)
    {X : 𝓧 × I → ℝ≥0∞} (hX : IsExactEVar X ((fun P ↦ P.prod volume) '' S)) {K : ℝ≥0}
    (hXK : ∀ P ∈ S ∪ 𝒬, ∀ᵐ p ∂(P.prod volume), X p ≤ K) {c : ℝ}
    (hc : ∀ Q ∈ 𝒬, (c : EReal) ≤ ∫ᵉ p, ENNReal.log (X p) ∂(Q.prod volume)) :
    ∃ h : 𝓧 → ℝ, Measurable h ∧ (∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |h x| ≤ max (K : ℝ) 1) ∧
      (∀ P ∈ S, ∫ x, h x ∂P = 0) ∧ ∀ Q ∈ 𝒬, c ≤ ∫ x, h x ∂Q := by
  set f : 𝓧 × I → ℝ := fun p ↦ (X p).toReal - 1
  have hf : Measurable f := hX.measurable.ennreal_toReal.sub_const 1
  have hfin : ∀ P ∈ S ∪ 𝒬, IsFiniteMeasure P := fun P hP ↦
    hP.elim (fun hP ↦ have := hS P hP; inferInstance) (h𝒬 P)
  -- `X ≤ K` gives `X < ∞` and `|X - 1| ≤ max K 1`
  have hfM : ∀ P ∈ S ∪ 𝒬, ∀ᵐ p ∂(P.prod volume), X p ≠ ∞ ∧ |f p| ≤ max (K : ℝ) 1 := by
    intro P hP
    filter_upwards [hXK P hP] with p hp
    have hp' : (X p).toReal ≤ K := ENNReal.toReal_le_of_le_ofReal K.coe_nonneg (by simpa using hp)
    refine ⟨ne_top_of_le_ne_top ENNReal.coe_ne_top hp, abs_sub_le_iff.2 ⟨?_, ?_⟩⟩
    · linarith [le_max_left (K : ℝ) 1]
    · linarith [le_max_right (K : ℝ) 1, (X p).toReal_nonneg]
  have hint : ∀ P ∈ S ∪ 𝒬, Integrable f (P.prod volume) := fun P hP ↦
    have := hfin P hP
    .of_bound hf.aestronglyMeasurable _
      ((hfM P hP).mono fun _ hp ↦ (Real.norm_eq_abs _).trans_le hp.2)
  refine ⟨fun x ↦ ∫ u, f (x, u),
    (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable,
    fun P hP ↦ ?_, fun P hP ↦ ?_, fun Q hQ ↦ ?_⟩
  · filter_upwards [Measure.ae_ae_of_ae_prod (hfM P hP)] with x hx
    simpa using norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
      (hx.mono fun u hu ↦ (Real.norm_eq_abs _).trans_le hu.2)
  · have := hS P hP
    rw [← integral_prod f (hint P (.inl hP))]
    exact hX.integral_toReal_sub_one_eq_zero ⟨P, hP, rfl⟩
  · have := h𝒬 Q hQ
    rw [← integral_prod f (hint Q (.inr hQ))]
    exact le_integral_toReal_sub_one_of_le_eintegral_log ((hfM Q (.inr hQ)).mono fun _ hp ↦ hp.1)
      (hint Q (.inr hQ)) (hc Q hQ)

/-- **Pivotal exact e-variables with external randomization** ([EVR26, Note 26, Theorem 1], for
bounded e-variables; [ZRW24, Conjecture 6.8], with the separation condition in its dual form):
for nulls `S` and alternatives `𝒬` of probability measures on `𝓧`, there is a bounded pivotal
exact e-variable for the laws `P ⊗ Leb` on `𝓧 × [0, 1]`, `P ∈ S`, with uniformly positive
e-power `inf_{Q ∈ 𝒬} E_{Q ⊗ Leb} log X > 0`, exactly when there is a separating function: a
measurable `h`, bounded almost everywhere for every member of `S ∪ 𝒬`, with `∫ h dP = 0` for
`P ∈ S` and `inf_{Q ∈ 𝒬} ∫ h dQ > 0`. -/
theorem exists_isExactEVar_isPivotal_prod_iff {S 𝒬 : Set (Measure 𝓧)}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (h𝒬 : ∀ Q ∈ 𝒬, IsProbabilityMeasure Q) :
    (∃ X : 𝓧 × I → ℝ≥0∞, IsExactEVar X ((fun P ↦ P.prod volume) '' S) ∧
      IsPivotal X ((fun P ↦ P.prod volume) '' S) ∧
      (∃ K : ℝ≥0, ∀ P ∈ S ∪ 𝒬, ∀ᵐ p ∂(P.prod volume), X p ≤ K) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ Q ∈ 𝒬, (c : EReal) ≤ ∫ᵉ p, ENNReal.log (X p) ∂(Q.prod volume)) ↔
    ∃ h : 𝓧 → ℝ, Measurable h ∧ (∃ M : ℝ, ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |h x| ≤ M) ∧
      (∀ P ∈ S, ∫ x, h x ∂P = 0) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ Q ∈ 𝒬, ε ≤ ∫ x, h x ∂Q := by
  constructor
  · rintro ⟨X, hX, -, ⟨K, hXK⟩, c, hc0, hc⟩
    obtain ⟨h, hh, hhM, hhS, hh𝒬⟩ := exists_integral_eq_zero_of_isExactEVar_prod hS
      (fun Q hQ ↦ have := h𝒬 Q hQ; inferInstance) hX hXK hc
    exact ⟨h, hh, ⟨_, hhM⟩, hhS, c, hc0, hh𝒬⟩
  · rintro ⟨h, hh, ⟨M, hM⟩, hhS, ε, hε, hh𝒬⟩
    -- a bound `M' ≥ 1`, the margin `κ = ε / (2 M')` and the step `η = min (1 / 2) κ`
    set M' := max M 1
    have hM' : ∀ P ∈ S ∪ 𝒬, ∀ᵐ x ∂P, |h x| ≤ M' := fun P hP ↦
      (hM P hP).mono fun x hx ↦ hx.trans (le_max_left _ _)
    have hκ : 0 < ε / (2 * M') := div_pos hε (by linarith [le_max_right M 1])
    set η := min (1 / 2) (ε / (2 * M'))
    have hη0 : 0 < η := lt_min (by norm_num) hκ
    obtain ⟨B, hB, hX⟩ := exists_isExactEVar_isPivotal_twoPointEVar hS h𝒬 hh hM' hhS hh𝒬
    obtain ⟨hexact, hpiv, hlog⟩ := hX η hη0.le (min_le_left _ _)
    refine ⟨twoPointEVar B η, hexact, hpiv, ⟨2, fun P _ ↦ ae_of_all _ fun p ↦ ?_⟩,
      2 * η * (ε / (2 * M')) - 2 / 3 * η ^ 2, ?_, hlog⟩
    · refine (twoPointEVar_le hη0.le B p).trans ?_
      rw [ENNReal.coe_ofNat, ← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal (by linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * M'))])
    · nlinarith [min_le_right (1 / 2 : ℝ) (ε / (2 * M'))]

end ProbabilityTheory
