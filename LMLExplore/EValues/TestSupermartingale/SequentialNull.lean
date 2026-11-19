/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.EValues.TestSupermartingale.Predictor
public import LMLExplore.Probability.Process.Filtration
public import Mathlib.Probability.ProductMeasure
public import Statlib.EValues.NumeraireExistence

/-!
# The sequential null of a set of laws, and products of its e-variables

Let `S₁` be a set of measures on an observation space `𝓧`, and let `X k` be observations
in `𝓧`, each measurable for `ℱ (k + 1)` for a filtration `ℱ`. The *sequential null*
`ProbabilityTheory.sequentialNull S₁ X ℱ` is the set of the probability measures under which the
conditional law of every observation `X k` given the past `ℱ k` lies in `S₁` almost surely
(`ProbabilityTheory.HasCondLaw`). It contains the laws of the independent sequences with laws in
`S₁`, in particular the i.i.d. laws of the members of `S₁`, but also every law under which each
observation is drawn from a member of `S₁` chosen, in any way, from the past.

Against this null, the e-variables for `S₁` can be multiplied along the observations: if, before
round `k`, the statistician chooses an e-variable `r k ω` for `S₁` from the past, then
`r k ω (X k ω)` is a conditional e-variable given `ℱ k` for every member of the sequential null,
so that the product `∏ k < n, r k ω (X k ω)` is a test supermartingale for the sequential null, by
the products of sequential e-variables [GdHK24, Proposition 2]
(`ProbabilityTheory.isTestSupermartingale_prod`). With the numeraire `X* = numeraire Q₁ S₁` of an
alternative `Q₁` (Statlib's `ProbabilityTheory.numeraire`), which for a finite measure `Q₁` is the
log-optimal e-variable for `S₁` under `Q₁`, this gives the product of the numeraires
`∏ k < n, X* (X k ω)`. Ville's inequality for test supermartingales
(`ProbabilityTheory.IsTestSupermartingale.measure_exists_inv_le_le`) then bounds by `α` the type I
error of the test that rejects as soon as the product reaches `α⁻¹`, uniformly over time
[GdHK24, Corollary 1].

The product of the numeraires generalizes the test supermartingale of [KG22, Theorem 12], stated
there for i.i.d. data and a null `S₁` of densities containing the reverse information projection
of the alternative on its convex hull, in which case the numeraire is a likelihood ratio. Here
`S₁` is any set of measures, the observation space is arbitrary, and the null
contains every law whose conditional laws given the past lie in `S₁`.

## Main definitions

* `ProbabilityTheory.sequentialNull S₁ X ℱ`: the probability measures under which the conditional
  law of each `X k` given `ℱ k` lies in `S₁` almost surely.

## Main statements

* `ProbabilityTheory.mem_sequentialNull_of_indep`: a probability measure under which every
  observation is independent of the past, with a law in `S₁`, belongs to the sequential null.
* `ProbabilityTheory.infinitePi_mem_sequentialNull`: the law of a sequence of independent
  observations with laws in `S₁` belongs to the sequential null of the coordinates and the
  filtration of the strict past.
* `ProbabilityTheory.isCondEVar_comp_sequentialNull`,
  `ProbabilityTheory.isExactCondEVar_comp_sequentialNull`: an e-variable for `S₁` chosen from the
  past, at the next observation, is a conditional e-variable for the sequential null.
* `ProbabilityTheory.isTestSupermartingale_prod_sequentialNull`: products of e-variables for `S₁`
  chosen from the past are test supermartingales for the sequential null;
  `ProbabilityTheory.isTestMartingale_prod_sequentialNull`: test martingales for exact
  e-variables.
* `ProbabilityTheory.isTestSupermartingale_prod_numeraire_sequentialNull`: the product of the
  numeraires is a test supermartingale for the sequential null.

## References

* [GdHK24] P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86
  (2024), arXiv:1906.07801.
* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid E-values*, Int. J. Approx.
  Reason. 141 (2022).
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {ℱ : Filtration ℕ mΩ}
  {X Y : ℕ → Ω → 𝓧} {S₁ T₁ : Set (Measure 𝓧)} {P : Measure Ω}

/-! ### The sequential null -/

/-- The **sequential null** of a set `S₁` of laws on `𝓧`, for the observations `X k` and the
filtration `ℱ`: the probability measures under which every observation `X k` has a conditional law
`κ` given `ℱ k` with `κ ω ∈ S₁` for almost every `ω`. -/
def sequentialNull (S₁ : Set (Measure 𝓧)) (X : ℕ → Ω → 𝓧) (ℱ : Filtration ℕ mΩ) :
    Set (Measure Ω) :=
  {P | IsProbabilityMeasure P ∧
    ∀ k, ∃ κ : Ω → Measure 𝓧, HasCondLaw (X k) κ (ℱ k) P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁}

/-- Membership in the sequential null. -/
theorem mem_sequentialNull_iff :
    P ∈ sequentialNull S₁ X ℱ ↔ IsProbabilityMeasure P ∧
      ∀ k, ∃ κ : Ω → Measure 𝓧, HasCondLaw (X k) κ (ℱ k) P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ :=
  Iff.rfl

/-- The members of the sequential null are probability measures. -/
theorem isProbabilityMeasure_of_mem_sequentialNull (hP : P ∈ sequentialNull S₁ X ℱ) :
    IsProbabilityMeasure P :=
  hP.1

/-- Under a member of the sequential null, every observation has a conditional law given the past
that lies in `S₁` almost surely. -/
theorem exists_hasCondLaw_of_mem_sequentialNull (hP : P ∈ sequentialNull S₁ X ℱ) (k : ℕ) :
    ∃ κ : Ω → Measure 𝓧, HasCondLaw (X k) κ (ℱ k) P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ :=
  hP.2 k

/-- The sequential null grows with the set of laws. -/
@[gcongr]
theorem sequentialNull_mono (h : S₁ ⊆ T₁) : sequentialNull S₁ X ℱ ⊆ sequentialNull T₁ X ℱ :=
  fun _ hP ↦ ⟨hP.1, fun k ↦ (hP.2 k).imp fun _ hκ ↦ ⟨hκ.1, hκ.2.mono fun _ hω ↦ h hω⟩⟩

/-- The sequential null of the empty set of laws is empty. -/
@[simp]
theorem sequentialNull_empty : sequentialNull (∅ : Set (Measure 𝓧)) X ℱ = ∅ := by
  refine eq_empty_of_forall_notMem fun P hP ↦ ?_
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, -, hκ⟩ := exists_hasCondLaw_of_mem_sequentialNull hP 0
  obtain ⟨_, h⟩ := hκ.exists
  exact h

/-- **Congruence.** The sequential null of observations that agree almost surely under `P`
contains `P` exactly when the sequential null of the other observations does. -/
theorem mem_sequentialNull_congr (h : ∀ k, X k =ᵐ[P] Y k) :
    P ∈ sequentialNull S₁ X ℱ ↔ P ∈ sequentialNull S₁ Y ℱ := by
  have key : ∀ {X Y : ℕ → Ω → 𝓧}, (∀ k, X k =ᵐ[P] Y k) →
      P ∈ sequentialNull S₁ X ℱ → P ∈ sequentialNull S₁ Y ℱ := fun h hP ↦
    ⟨hP.1, fun k ↦ (hP.2 k).imp fun _ hκ ↦ ⟨hκ.1.congr (h k), hκ.2⟩⟩
  exact ⟨key h, key fun k ↦ (h k).symm⟩

/-- **Independent observations.** A probability measure under which every observation `X k` is
independent of the past `ℱ k`, with a law in `S₁`, belongs to the sequential null. This contains
the laws of independent sequences, and of i.i.d. sequences, with laws in `S₁`. -/
theorem mem_sequentialNull_of_indep [IsProbabilityMeasure P] (hX : ∀ k, AEMeasurable (X k) P)
    (hind : ∀ k, Indep (MeasurableSpace.comap (X k) m𝓧) (ℱ k) P)
    (hmap : ∀ k, P.map (X k) ∈ S₁) :
    P ∈ sequentialNull S₁ X ℱ :=
  ⟨inferInstance, fun k ↦ ⟨fun _ ↦ P.map (X k),
    hasCondLaw_of_indep (ℱ.le k) (hind k) ⟨hX k, rfl⟩, .of_forall fun _ ↦ hmap k⟩⟩

/-- **Independent sequences.** The law `Measure.infinitePi μ` of a sequence of independent
observations on `ℕ → 𝓧`, with laws `μ k ∈ S₁`, belongs to the sequential null of the coordinates
and the filtration of the strict past `Filtration.naturalLT`. With `μ k = μ₀` for every `k`, this
contains the i.i.d. laws of the members of `S₁`. -/
theorem infinitePi_mem_sequentialNull {μ : ℕ → Measure 𝓧} [∀ k, IsProbabilityMeasure (μ k)]
    (hμ : ∀ k, μ k ∈ S₁) :
    Measure.infinitePi μ ∈ sequentialNull S₁ (fun k (ω : ℕ → 𝓧) ↦ ω k)
      (Filtration.naturalLT (fun k (ω : ℕ → 𝓧) ↦ ω k) measurable_pi_apply) :=
  mem_sequentialNull_of_indep (fun k ↦ (measurable_pi_apply k).aemeasurable)
    (Filtration.indep_naturalLT_infinitePi μ) fun k ↦ (Measure.infinitePi_map_eval μ k).symm ▸ hμ k

/-! ### Products of e-variables -/

variable {r : ℕ → Ω → 𝓧 → ℝ≥0∞}

/-- **One round against the sequential null.** Let `S₁` be a set of measures, let `X k` be
measurable, and let `r ω` be an e-variable for `S₁` for every `ω`, jointly measurable
for `ℱ k` and `𝓧`. Then `r ω (X k ω)` is a conditional e-variable given `ℱ k` for the
sequential null `sequentialNull S₁ X ℱ`. -/
theorem isCondEVar_comp_sequentialNull {r : Ω → 𝓧 → ℝ≥0∞} {k : ℕ} (hX : Measurable (X k))
    (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r)) (hr1 : ∀ ω, IsEVar (r ω) S₁) :
    IsCondEVar (fun ω ↦ r ω (X k ω)) (ℱ k) (sequentialNull S₁ X ℱ) := by
  refine ⟨measurable_comp_prodMk (ℱ.le k) hX hr, fun P hP s hs ↦ ?_⟩
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP k
  rw [hκ.setLIntegral_comp (ℱ.le k) hr hs, ← hκ.setLIntegral_measure_univ (ℱ.le k) hs]
  exact lintegral_mono_ae (ae_restrict_of_ae (hκS.mono fun ω hω ↦
    (hr1 ω).lintegral_le_measure_univ _ hω))

/-- **One round against the sequential null, exact case.** Let `S₁` be a set of measures,
let `X k` be measurable, and let `r ω` be an exact e-variable for `S₁` for
every `ω`, jointly measurable for `ℱ k` and `𝓧`. Then `r ω (X k ω)` is an exact conditional
e-variable given `ℱ k` for the sequential null `sequentialNull S₁ X ℱ`. -/
theorem isExactCondEVar_comp_sequentialNull {r : Ω → 𝓧 → ℝ≥0∞} {k : ℕ} (hX : Measurable (X k))
    (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r)) (hr1 : ∀ ω, IsExactEVar (r ω) S₁) :
    IsExactCondEVar (fun ω ↦ r ω (X k ω)) (ℱ k) (sequentialNull S₁ X ℱ) := by
  refine ⟨measurable_comp_prodMk (ℱ.le k) hX hr, fun P hP s hs ↦ ?_⟩
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP k
  rw [hκ.setLIntegral_comp (ℱ.le k) hr hs, ← hκ.setLIntegral_measure_univ (ℱ.le k) hs]
  exact lintegral_congr_ae (ae_restrict_of_ae (hκS.mono fun ω hω ↦
    (hr1 ω).lintegral_eq_measure_univ _ hω))

/-- **Products of e-variables chosen from the past are test supermartingales for the sequential
null** [GdHK24, Proposition 2]. Let `S₁` be a set of measures, let `X k` be
`ℱ (k + 1)`-measurable, and let `r k ω` be an e-variable for `S₁` for every `ω`, jointly measurable
for `ℱ k` and `𝓧`. Then `∏ k < n, r k ω (X k ω)` is a test supermartingale for the sequential
null `sequentialNull S₁ X ℱ`. -/
theorem isTestSupermartingale_prod_sequentialNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k ω, IsEVar (r k ω) S₁) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ (sequentialNull S₁ X ℱ) :=
  isTestSupermartingale_prod (fun _ ↦ isProbabilityMeasure_of_mem_sequentialNull)
    (measurable_succ_comp hX hr) fun k ↦
      isCondEVar_comp_sequentialNull ((hX k).mono (ℱ.le _) le_rfl) (hr k) (hr1 k)

/-- **Products of exact e-variables chosen from the past are test martingales for the sequential
null.** Let `S₁` be a set of measures, let `X k` be `ℱ (k + 1)`-measurable, and let
`r k ω` be an exact e-variable for `S₁` for every `ω`, jointly measurable for `ℱ k` and `𝓧`. Then
`∏ k < n, r k ω (X k ω)` is a test martingale for the sequential null `sequentialNull S₁ X ℱ`. -/
theorem isTestMartingale_prod_sequentialNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k ω, IsExactEVar (r k ω) S₁) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ (sequentialNull S₁ X ℱ) :=
  isTestMartingale_prod (fun _ ↦ isProbabilityMeasure_of_mem_sequentialNull)
    (measurable_succ_comp hX hr) fun k ↦
      isExactCondEVar_comp_sequentialNull ((hX k).mono (ℱ.le _) le_rfl) (hr k)
        (hr1 k)

/-- **Products of copies of an e-variable are test supermartingales for the sequential null.** If
`e` is an e-variable for a set `S₁` of measures and `X k` is `ℱ (k + 1)`-measurable,
then `∏ k < n, e (X k ω)` is a test supermartingale for the sequential null
`sequentialNull S₁ X ℱ`. -/
theorem IsEVar.isTestSupermartingale_prod_sequentialNull {e : 𝓧 → ℝ≥0∞} (he : IsEVar e S₁)
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, e (X k ω)) ℱ (sequentialNull S₁ X ℱ) :=
  ProbabilityTheory.isTestSupermartingale_prod_sequentialNull (r := fun _ _ ↦ e) hX
    (fun _ ↦ he.measurable.comp measurable_snd) fun _ _ ↦ he

/-- **The product of the numeraires is a test supermartingale for the sequential null.** For a
set `S₁` of measures, an alternative `Q₁` and `ℱ (k + 1)`-measurable observations
`X k`, the product `∏ k < n, X* (X k ω)` of the numeraire `X* = numeraire Q₁ S₁` (Statlib's
`ProbabilityTheory.numeraire`, for a finite measure `Q₁` the log-optimal e-variable for `S₁` under
`Q₁`) is a test supermartingale for the sequential null `sequentialNull S₁ X ℱ` [KG22,
Theorem 12]. -/
theorem isTestSupermartingale_prod_numeraire_sequentialNull (Q₁ : Measure 𝓧)
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, numeraire Q₁ S₁ (X k ω)) ℱ
      (sequentialNull S₁ X ℱ) :=
  (isEVar_numeraire Q₁ S₁).isTestSupermartingale_prod_sequentialNull hX

end ProbabilityTheory
