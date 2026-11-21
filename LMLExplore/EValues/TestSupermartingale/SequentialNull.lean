/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.EValues.TestSupermartingale.Predictor
public import LMLExplore.Probability.Process.Filtration
public import Mathlib.Probability.ProductMeasure
public import Statlib.EValues.NumeraireExistence

/-!
# The sequential null of one-step nulls, and products of its e-variables

Let `X k` be observations in a space `𝓧`, each measurable for `ℱ (k + 1)` for a filtration `ℱ`,
and let `S₁ k ω` be a set of measures on `𝓧` for every round `k` and every `ω`: a *one-step null*,
which may depend on the round and on the past. The *sequential null*
`ProbabilityTheory.sequentialNull S₁ X ℱ` is the set of the probability measures under which every
observation `X k` has a conditional distribution `κ` given the past `ℱ k`, a kernel from
`(Ω, ℱ k)` (Mathlib's `HasCondDistrib (X k) id κ P`), with `κ ω ∈ S₁ k ω` almost surely.
For a constant one-step null `S₁ k ω = N`, it contains the laws of the independent
sequences with laws in `N`, in particular the i.i.d. laws of the members of `N`, but also every law
under which each observation is drawn from a member of `N` chosen measurably from the past.
The kernels of the definition give conditional laws in the set-integral form
`ProbabilityTheory.HasCondLaw`, in which the proofs below are written. On sequences in a standard
Borel space with the filtration `Filtration.piLT` of the strict past, Mathlib's `condDistrib` of
each coordinate given the previous ones provides the kernels.

Against this null, the e-variables for the one-step nulls can be multiplied along the
observations: if, before round `k`, the statistician chooses an e-variable `r k ω` for `S₁ k ω`
from the past, then `r k ω (X k ω)` is a conditional e-variable given `ℱ k` for every member of
the sequential null, so that the product `∏ k < n, r k ω (X k ω)` is a test supermartingale for the
sequential null, by the products of sequential e-variables [GdHK24, Proposition 2]
(`ProbabilityTheory.isTestSupermartingale_prod`). With the numeraire `X* = numeraire Q₁ N` of an
alternative `Q₁` for a constant one-step null `N` (Statlib's `ProbabilityTheory.numeraire`), which
for a finite measure `Q₁` is the log-optimal e-variable for `N` under `Q₁`, this gives the product
of the numeraires `∏ k < n, X* (X k ω)`. Ville's inequality for test supermartingales
(`ProbabilityTheory.IsTestSupermartingale.measure_exists_inv_le_le`) then bounds by `α` the type I
error of the test that rejects as soon as the product reaches `α⁻¹`, uniformly over time
[GdHK24, Corollary 1].

The product of the numeraires generalizes the test supermartingale of [KG22, Theorem 12], stated
there for i.i.d. data and a null of densities containing the reverse information projection of the
alternative on its convex hull, in which case the numeraire is a likelihood ratio. Here `N` is any
set of measures, the observation space is arbitrary, and the null contains every law with a
conditional distribution (a kernel from `(Ω, ℱ k)`) given the past with values in `N`.

The nulls of a constant one-step null `N` form a chain, for a null `N` of probability measures:
the i.i.d. null `iidNull N` and the
independent null `indepNull N` of the coordinates are contained in the sequential null, which is
contained in the *null of conditional bets* `ProbabilityTheory.condEVarNull 𝓔 X ℱ` of any set `𝓔`
of e-variables for `N`: the probability measures under which every `e (X k)`, `e ∈ 𝓔`, is a
conditional e-variable given `ℱ k`. A validity statement is made for the largest of these nulls
for which it holds.

## Main definitions

* `ProbabilityTheory.sequentialNull S₁ X ℱ`: the probability measures under which each `X k` has a
  conditional distribution given `ℱ k` that lies in `S₁ k ω` almost surely.
* `ProbabilityTheory.condEVarNull 𝓔 X ℱ`: the probability measures under which every bet
  `e (X k)`, `e ∈ 𝓔`, is a conditional e-variable given `ℱ k`.

## Main statements

* `ProbabilityTheory.exists_hasCondLaw_of_mem_sequentialNull`,
  `ProbabilityTheory.mem_sequentialNull_of_hasCondLaw`: membership through conditional laws in
  the set-integral form.
* `ProbabilityTheory.mem_sequentialNull_of_indep`: a probability measure under which every
  observation is independent of the past, with a law in the one-step null, belongs to the
  sequential null.
* `ProbabilityTheory.infinitePi_mem_sequentialNull`: the law of a sequence of independent
  observations with laws in the one-step nulls belongs to the sequential null of the coordinates
  and the filtration `Filtration.piLT` of the strict past.
* `ProbabilityTheory.mem_sequentialNull_pi_of_ae_condDistrib_mem`: a law on sequences in a
  standard Borel space whose `condDistrib` of each coordinate given the previous ones lies in the
  one-step null belongs to the sequential null of the coordinates.
* `ProbabilityTheory.isCondEVar_comp_sequentialNull`,
  `ProbabilityTheory.isExactCondEVar_comp_sequentialNull`: an e-variable for the one-step null
  chosen from the past, at the next observation, is a conditional e-variable for the sequential
  null.
* `ProbabilityTheory.isTestSupermartingale_prod_sequentialNull`: products of e-variables for the
  one-step nulls chosen from the past are test supermartingales for the sequential null;
  `ProbabilityTheory.isTestMartingale_prod_sequentialNull`: test martingales for exact
  e-variables.
* `ProbabilityTheory.isTestSupermartingale_prod_numeraire_sequentialNull`: the product of the
  numeraires is a test supermartingale for the sequential null of a constant one-step null.
* `ProbabilityTheory.iidNull_subset_sequentialNull`,
  `ProbabilityTheory.indepNull_subset_sequentialNull`,
  `ProbabilityTheory.sequentialNull_subset_condEVarNull`: the chain
  `iidNull N ⊆ indepNull N ⊆ sequentialNull (fun _ _ ↦ N) X ℱ ⊆ condEVarNull 𝓔 X ℱ`, for the
  coordinates with `Filtration.piLT`, a null `N` of probability measures and bets `𝓔` that are
  e-variables for `N`; the last inclusion holds, for measurable observations `X k`, for every
  one-step null whose e-variables include `𝓔`.
* `ProbabilityTheory.isTestSupermartingale_prod_condEVarNull`: products of bets of `𝓔` are test
  supermartingales for the null of conditional bets `𝓔`.

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
  {X Y : ℕ → Ω → 𝓧} {S₁ T₁ : ℕ → Ω → Set (Measure 𝓧)} {P : Measure Ω}

/-! ### The sequential null -/

/-- The **sequential null** of one-step nulls `S₁ k ω`, which may depend on the round `k` and on the
past `ω`, for the observations `X k` and the filtration `ℱ`: the probability measures `P` such
that, for every round `k`, some kernel `κ` from `(Ω, ℱ k)` is a conditional distribution of `X k`
given `ℱ k` (Mathlib's `HasCondDistrib (X k) id κ P`, with `id` the identity of `Ω` into
`(Ω, ℱ k)`) with `κ ω ∈ S₁ k ω` for almost every `ω`. -/
def sequentialNull (S₁ : ℕ → Ω → Set (Measure 𝓧)) (X : ℕ → Ω → 𝓧) (ℱ : Filtration ℕ mΩ) :
    Set (Measure Ω) :=
  {P | IsProbabilityMeasure P ∧ ∀ k, ∃ κ : Kernel[ℱ k] Ω 𝓧,
    HasCondDistrib (m𝓧 := ℱ k) (X k) id κ P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ k ω}

/-- Membership in the sequential null. -/
theorem mem_sequentialNull_iff :
    P ∈ sequentialNull S₁ X ℱ ↔ IsProbabilityMeasure P ∧ ∀ k, ∃ κ : Kernel[ℱ k] Ω 𝓧,
      HasCondDistrib (m𝓧 := ℱ k) (X k) id κ P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ k ω :=
  Iff.rfl

/-- The members of the sequential null are probability measures. -/
theorem isProbabilityMeasure_of_mem_sequentialNull (hP : P ∈ sequentialNull S₁ X ℱ) :
    IsProbabilityMeasure P :=
  hP.1

/-- Under a member of the sequential null, every observation has a conditional distribution given
the past that lies in the one-step null almost surely. -/
theorem exists_hasCondDistrib_of_mem_sequentialNull (hP : P ∈ sequentialNull S₁ X ℱ) (k : ℕ) :
    ∃ κ : Kernel[ℱ k] Ω 𝓧, HasCondDistrib (m𝓧 := ℱ k) (X k) id κ P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ k ω :=
  hP.2 k

/-- Under a member of the sequential null, every observation has a conditional law given the past
(`ProbabilityTheory.HasCondLaw`, the set-integral identity) that lies in the one-step null almost
surely. -/
theorem exists_hasCondLaw_of_mem_sequentialNull (hP : P ∈ sequentialNull S₁ X ℱ) (k : ℕ) :
    ∃ κ : Ω → Measure 𝓧, HasCondLaw (X k) κ (ℱ k) P ∧ ∀ᵐ ω ∂P, κ ω ∈ S₁ k ω := by
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondDistrib_of_mem_sequentialNull hP k
  exact ⟨κ, hκ.hasCondLaw, hκS⟩

/-- **Membership from conditional laws.** A probability measure under which every observation has
an s-finite conditional law given the past, that lies in the one-step null almost surely, belongs
to the sequential null. -/
theorem mem_sequentialNull_of_hasCondLaw [IsProbabilityMeasure P] (hX : ∀ k, AEMeasurable (X k) P)
    (κ : (k : ℕ) → Kernel[ℱ k] Ω 𝓧) [∀ k, IsSFiniteKernel (κ k)]
    (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P) (hκS : ∀ k, ∀ᵐ ω ∂P, κ k ω ∈ S₁ k ω) :
    P ∈ sequentialNull S₁ X ℱ :=
  ⟨inferInstance, fun k ↦
    ⟨κ k, (hasCondDistrib_id_iff_hasCondLaw (ℱ.le k) (hX k)).2 (hκ k), hκS k⟩⟩

/-- The sequential null grows with the one-step nulls. -/
@[gcongr]
theorem sequentialNull_mono (h : S₁ ≤ T₁) : sequentialNull S₁ X ℱ ⊆ sequentialNull T₁ X ℱ :=
  fun _ hP ↦ ⟨hP.1, fun k ↦ (hP.2 k).imp fun _ hκ ↦ ⟨hκ.1, hκ.2.mono fun ω hω ↦ h k ω hω⟩⟩

/-- The sequential null of the empty one-step nulls is empty. -/
@[simp]
theorem sequentialNull_empty : sequentialNull (fun _ _ ↦ (∅ : Set (Measure 𝓧))) X ℱ = ∅ := by
  refine eq_empty_of_forall_notMem fun P hP ↦ ?_
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, -, hκ⟩ := exists_hasCondDistrib_of_mem_sequentialNull hP 0
  obtain ⟨_, h⟩ := hκ.exists
  exact h

/-- **Congruence.** The sequential null of observations that agree almost surely under `P`
contains `P` exactly when the sequential null of the other observations does. -/
theorem mem_sequentialNull_congr (h : ∀ k, X k =ᵐ[P] Y k) :
    P ∈ sequentialNull S₁ X ℱ ↔ P ∈ sequentialNull S₁ Y ℱ := by
  have key : ∀ {X Y : ℕ → Ω → 𝓧}, (∀ k, X k =ᵐ[P] Y k) →
      P ∈ sequentialNull S₁ X ℱ → P ∈ sequentialNull S₁ Y ℱ := fun h hP ↦
    ⟨hP.1, fun k ↦ (hP.2 k).imp fun _ hκ ↦ ⟨hκ.1.congr .rfl (h k).symm, hκ.2⟩⟩
  exact ⟨key h, key fun k ↦ (h k).symm⟩

/-- **Independent observations.** A probability measure under which every observation `X k` is
independent of the past `ℱ k`, with a law in the one-step null almost surely, belongs to the
sequential null. This contains the laws of independent sequences, and of i.i.d. sequences, with
laws in the one-step null. -/
theorem mem_sequentialNull_of_indep [IsProbabilityMeasure P] (hX : ∀ k, AEMeasurable (X k) P)
    (hind : ∀ k, Indep (MeasurableSpace.comap (X k) m𝓧) (ℱ k) P)
    (hmap : ∀ k, ∀ᵐ ω ∂P, P.map (X k) ∈ S₁ k ω) :
    P ∈ sequentialNull S₁ X ℱ :=
  ⟨inferInstance, fun k ↦ ⟨_, hasCondDistrib_id_const_of_indep (ℱ.le k) (hind k) ⟨hX k, rfl⟩,
    hmap k⟩⟩

/-- **Independent sequences.** The law `Measure.infinitePi μ` of a sequence of independent
observations on `ℕ → 𝓧`, with laws `μ k ∈ S₁ k ω` for almost every `ω`, belongs to the
sequential null of the coordinates and the filtration `Filtration.piLT` of the strict past. With
`μ k = μ₀` for every `k`, this contains the i.i.d. laws of the members of a one-step null. -/
theorem infinitePi_mem_sequentialNull {S₁ : ℕ → (ℕ → 𝓧) → Set (Measure 𝓧)} {μ : ℕ → Measure 𝓧}
    [∀ k, IsProbabilityMeasure (μ k)] (hμ : ∀ k, ∀ᵐ ω ∂Measure.infinitePi μ, μ k ∈ S₁ k ω) :
    Measure.infinitePi μ ∈ sequentialNull S₁ (fun k ω ↦ ω k) Filtration.piLT :=
  mem_sequentialNull_of_indep (fun k ↦ (measurable_pi_apply k).aemeasurable)
    (by rw [Filtration.piLT_eq_naturalLT]; exact Filtration.indep_naturalLT_infinitePi μ) fun k ↦
      (hμ k).mono fun _ h ↦ (Measure.infinitePi_map_eval μ k).symm ▸ h

/-- **The sequential null of the coordinates, from Mathlib's conditional distributions.** On
sequences in a standard Borel space, with the coordinates and the filtration `Filtration.piLT` of
the strict past, a probability measure `P` belongs to the sequential null as soon as, at every
round `k`, Mathlib's `condDistrib` of the coordinate `ω k` given the first `k` coordinates, at
`initSeg k ω`, lies in the one-step null `S₁ k ω` for `P`-almost every `ω`. -/
theorem mem_sequentialNull_pi_of_ae_condDistrib_mem [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    {S₁ : ℕ → (ℕ → 𝓧) → Set (Measure 𝓧)} {P : Measure (ℕ → 𝓧)} [IsProbabilityMeasure P]
    (h : ∀ k, ∀ᵐ ω ∂P, condDistrib (fun ω ↦ ω k) (initSeg k) P (initSeg k ω) ∈ S₁ k ω) :
    P ∈ sequentialNull S₁ (fun k ω ↦ ω k) Filtration.piLT :=
  ⟨inferInstance, fun k ↦ ⟨_, hasCondDistrib_piLT_condDistrib P k, h k⟩⟩

/-! ### Products of e-variables -/

variable {r : ℕ → Ω → 𝓧 → ℝ≥0∞}

/-- **One round against the sequential null.** Let `X k` be measurable, and let `r ω` be an
e-variable for the one-step null `S₁ k ω` for every `ω`, jointly measurable for `ℱ k` and `𝓧`.
Then `r ω (X k ω)` is a conditional e-variable given `ℱ k` for the sequential null
`sequentialNull S₁ X ℱ`. -/
theorem isCondEVar_comp_sequentialNull {r : Ω → 𝓧 → ℝ≥0∞} {k : ℕ} (hX : Measurable (X k))
    (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r)) (hr1 : ∀ ω, IsEVar (r ω) (S₁ k ω)) :
    IsCondEVar (fun ω ↦ r ω (X k ω)) (ℱ k) (sequentialNull S₁ X ℱ) := by
  refine ⟨hr.comp_prodMk_of_le (ℱ.le k) hX, fun P hP s hs ↦ ?_⟩
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP k
  rw [hκ.setLIntegral_comp (ℱ.le k) hr hs, ← setLIntegral_one]
  exact lintegral_mono_ae (ae_restrict_of_ae (hκS.mono fun ω hω ↦ (hr1 ω).lintegral_le_one hω))

/-- **One round against the sequential null, exact case.** Let `X k` be measurable, and let
`r ω` be an exact e-variable for the one-step null `S₁ k ω` for every `ω`, jointly measurable
for `ℱ k` and `𝓧`. Then `r ω (X k ω)` is an exact conditional e-variable given `ℱ k` for the
sequential null `sequentialNull S₁ X ℱ`. -/
theorem isExactCondEVar_comp_sequentialNull {r : Ω → 𝓧 → ℝ≥0∞} {k : ℕ} (hX : Measurable (X k))
    (hr : Measurable[(ℱ k).prod m𝓧] (Function.uncurry r))
    (hr1 : ∀ ω, IsExactEVar (r ω) (S₁ k ω)) :
    IsExactCondEVar (fun ω ↦ r ω (X k ω)) (ℱ k) (sequentialNull S₁ X ℱ) := by
  refine ⟨hr.comp_prodMk_of_le (ℱ.le k) hX, fun P hP s hs ↦ ?_⟩
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP k
  rw [hκ.setLIntegral_comp (ℱ.le k) hr hs, ← setLIntegral_one]
  exact lintegral_congr_ae (ae_restrict_of_ae (hκS.mono fun ω hω ↦ (hr1 ω).lintegral_eq_one hω))

/-- **Products of e-variables chosen from the past are test supermartingales for the sequential
null** [GdHK24, Proposition 2]. Let `X k` be `ℱ (k + 1)`-measurable, and let `r k ω` be an
e-variable for the one-step null `S₁ k ω` for every `ω`, jointly measurable for `ℱ k` and `𝓧`.
Then `∏ k < n, r k ω (X k ω)` is a test supermartingale for the sequential null
`sequentialNull S₁ X ℱ`. -/
theorem isTestSupermartingale_prod_sequentialNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k ω, IsEVar (r k ω) (S₁ k ω)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ (sequentialNull S₁ X ℱ) :=
  isTestSupermartingale_prod
    (fun _ hP ↦ (isProbabilityMeasure_of_mem_sequentialNull hP).measure_univ.le)
    (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hX k)) fun k ↦
      isCondEVar_comp_sequentialNull ((hX k).mono (ℱ.le _) le_rfl) (hr k) (hr1 k)

/-- **Products of exact e-variables chosen from the past are test martingales for the sequential
null.** Let `X k` be `ℱ (k + 1)`-measurable, and let `r k ω` be an exact e-variable for the
one-step null `S₁ k ω` for every `ω`, jointly measurable for `ℱ k` and `𝓧`. Then
`∏ k < n, r k ω (X k ω)` is a test martingale for the sequential null `sequentialNull S₁ X ℱ`. -/
theorem isTestMartingale_prod_sequentialNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k ω, IsExactEVar (r k ω) (S₁ k ω)) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ (sequentialNull S₁ X ℱ) :=
  isTestMartingale_prod (fun _ hP ↦ (isProbabilityMeasure_of_mem_sequentialNull hP).measure_univ.le)
    (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hX k)) fun k ↦
      isExactCondEVar_comp_sequentialNull ((hX k).mono (ℱ.le _) le_rfl) (hr k)
        (hr1 k)

/-- **Products of copies of an e-variable are test supermartingales for the sequential null.** If
`e` is an e-variable for a set `N` of measures and `X k` is `ℱ (k + 1)`-measurable,
then `∏ k < n, e (X k ω)` is a test supermartingale for the sequential null
`sequentialNull (fun _ _ ↦ N) X ℱ` of the constant one-step null `N`. -/
theorem IsEVar.isTestSupermartingale_prod_sequentialNull {N : Set (Measure 𝓧)} {e : 𝓧 → ℝ≥0∞}
    (he : IsEVar e N) (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, e (X k ω)) ℱ
      (sequentialNull (fun _ _ ↦ N) X ℱ) :=
  ProbabilityTheory.isTestSupermartingale_prod_sequentialNull (r := fun _ _ ↦ e) hX
    (fun _ ↦ he.measurable.comp measurable_snd) fun _ _ ↦ he

/-- **The product of the numeraires is a test supermartingale for the sequential null.** For a
set `N` of measures of mass at most `1`, an alternative `Q₁` and `ℱ (k + 1)`-measurable
observations `X k`, the product `∏ k < n, X* (X k ω)` of the numeraire `X* = numeraire Q₁ N`
(Statlib's `ProbabilityTheory.numeraire`, for a finite measure `Q₁` the log-optimal e-variable for
`N` under `Q₁`) is a test supermartingale for the sequential null
`sequentialNull (fun _ _ ↦ N) X ℱ` of the constant one-step null `N` [KG22, Theorem 12]. -/
theorem isTestSupermartingale_prod_numeraire_sequentialNull {N : Set (Measure 𝓧)}
    (Q₁ : Measure 𝓧) (hN : ∀ P ∈ N, P Set.univ ≤ 1) (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, numeraire Q₁ N (X k ω)) ℱ
      (sequentialNull (fun _ _ ↦ N) X ℱ) :=
  (isEVar_numeraire Q₁ hN).isTestSupermartingale_prod_sequentialNull hX

/-! ### The chain of nulls -/

/-- **Independent sequences form a sub-null of the sequential null.** For a null `N` of
probability measures, the laws of the independent sequences with laws in `N` belong to the
sequential null of the constant one-step null `N`, for the coordinates and the filtration
`Filtration.piLT` of the strict past. -/
theorem indepNull_subset_sequentialNull {N : Set (Measure 𝓧)}
    (hN : ∀ Q ∈ N, IsProbabilityMeasure Q) :
    indepNull N ⊆ sequentialNull (fun _ _ ↦ N) (fun k ω ↦ ω k) Filtration.piLT := by
  intro μ hμ
  obtain ⟨Q, hQ, rfl⟩ := mem_indepNull.1 hμ
  have := fun k ↦ hN _ (hQ k)
  exact infinitePi_mem_sequentialNull fun k ↦ .of_forall fun _ ↦ hQ k

/-- **I.i.d. sequences form a sub-null of the sequential null.** For a null `N` of probability
measures, the i.i.d. laws of the members of `N` belong to the sequential null of the constant
one-step null `N`, for the coordinates and the filtration `Filtration.piLT` of the strict past. -/
theorem iidNull_subset_sequentialNull {N : Set (Measure 𝓧)}
    (hN : ∀ Q ∈ N, IsProbabilityMeasure Q) :
    iidNull N ⊆ sequentialNull (fun _ _ ↦ N) (fun k ω ↦ ω k) Filtration.piLT :=
  (iidNull_subset_indepNull N).trans (indepNull_subset_sequentialNull hN)

/-- The **null of conditional bets** `𝓔` on the observations `X k`: the probability measures under
which, for every round `k` and every bet `e ∈ 𝓔`, `e (X k)` is a conditional e-variable given the
past `ℱ k`. This is the dual form of the sequential null: for measurable observations `X k`, it
contains the sequential null of every one-step null for which the bets of `𝓔` are e-variables
(`ProbabilityTheory.sequentialNull_subset_condEVarNull`). -/
def condEVarNull (𝓔 : Set (𝓧 → ℝ≥0∞)) (X : ℕ → Ω → 𝓧) (ℱ : Filtration ℕ mΩ) :
    Set (Measure Ω) :=
  {P | IsProbabilityMeasure P ∧ ∀ k, ∀ e ∈ 𝓔, IsCondEVar (fun ω ↦ e (X k ω)) (ℱ k) {P}}

variable {𝓔 𝓕 : Set (𝓧 → ℝ≥0∞)}

/-- Membership in the null of conditional bets. -/
theorem mem_condEVarNull_iff :
    P ∈ condEVarNull 𝓔 X ℱ ↔
      IsProbabilityMeasure P ∧ ∀ k, ∀ e ∈ 𝓔, IsCondEVar (fun ω ↦ e (X k ω)) (ℱ k) {P} :=
  Iff.rfl

/-- The members of the null of conditional bets are probability measures. -/
theorem isProbabilityMeasure_of_mem_condEVarNull (hP : P ∈ condEVarNull 𝓔 X ℱ) :
    IsProbabilityMeasure P :=
  hP.1

/-- The null of conditional bets shrinks as the set of bets grows. -/
@[gcongr]
theorem condEVarNull_anti (h : 𝓔 ⊆ 𝓕) : condEVarNull 𝓕 X ℱ ⊆ condEVarNull 𝓔 X ℱ :=
  fun _ hP ↦ ⟨hP.1, fun k e he ↦ hP.2 k e (h he)⟩

/-- **A bet at the next observation is a conditional e-variable for the null of conditional
bets.** -/
theorem isCondEVar_comp_condEVarNull {e : 𝓧 → ℝ≥0∞} (he : e ∈ 𝓔) {k : ℕ}
    (hmeas : Measurable fun ω ↦ e (X k ω)) :
    IsCondEVar (fun ω ↦ e (X k ω)) (ℱ k) (condEVarNull 𝓔 X ℱ) :=
  ⟨hmeas, fun P hP ↦ (hP.2 k e he).setLIntegral_le P (mem_singleton P)⟩

/-- **The sequential null is contained in the null of its conditional bets.** If the observations
are measurable and every bet of `𝓔` is an e-variable for every one-step null `S₁ k ω`, then the
sequential null `sequentialNull S₁ X ℱ` is contained in the null of conditional bets `𝓔`. -/
theorem sequentialNull_subset_condEVarNull (hX : ∀ k, Measurable (X k))
    (h𝓔 : ∀ e ∈ 𝓔, ∀ k ω, IsEVar e (S₁ k ω)) :
    sequentialNull S₁ X ℱ ⊆ condEVarNull 𝓔 X ℱ := by
  intro P hP
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  refine ⟨this, fun k e he ↦ ?_⟩
  -- `Ω` is nonempty under a probability measure, and a point `ω₀` yields the measurability of `e`
  -- from the e-variable `e` for `S₁ k ω₀`.
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  exact (isCondEVar_comp_sequentialNull (ℱ := ℱ) (r := fun _ ↦ e) (hX k)
    ((h𝓔 e he k ω₀).measurable.comp measurable_snd) fun ω ↦ h𝓔 e he k ω).anti_set
    (singleton_subset_iff.2 hP)

/-- **Products of conditional bets are test supermartingales for the null of conditional bets.**
If `X k` is `ℱ (k + 1)`-measurable and `e k ∈ 𝓔` is measurable for every `k`, then
`∏ k < n, e k (X k ω)` is a test supermartingale for `condEVarNull 𝓔 X ℱ`. -/
theorem isTestSupermartingale_prod_condEVarNull {e : ℕ → 𝓧 → ℝ≥0∞}
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (he : ∀ k, e k ∈ 𝓔) (he_meas : ∀ k, Measurable (e k)) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, e k (X k ω)) ℱ (condEVarNull 𝓔 X ℱ) :=
  isTestSupermartingale_prod
    (fun _ hP ↦ (isProbabilityMeasure_of_mem_condEVarNull hP).measure_univ.le)
    (fun k ↦ (he_meas k).comp (hX k)) fun k ↦
      isCondEVar_comp_condEVarNull (he k) ((he_meas k).comp ((hX k).mono (ℱ.le _) le_rfl))

end ProbabilityTheory
