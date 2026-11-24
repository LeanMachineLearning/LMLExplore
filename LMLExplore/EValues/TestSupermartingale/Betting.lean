/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
import LMLExplore.MeasureTheory.Measure.Convex
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The supermartingales of an i.i.d. null are betting supermartingales

Let `S₁` be a set of probability measures on `𝓧`, and consider a nonnegative process `M` adapted
to the strict past `Filtration.piLT` of the coordinates of `ℕ → 𝓧`, so that `M (n + 1) ω` is a
function of the first `n + 1` observations. Its *one-step condition* at a past `ω` of length `n`
is that, for every `ν ∈ S₁`,
`∫⁻ y, M (n + 1) (Function.update ω n y) ∂ν ≤ M n ω`: whatever the next observation `y` and its
law in `S₁`, the process does not grow in expectation. A process with this property at every past
is a *betting supermartingale*: its one-step ratios `M (n + 1) (Function.update ω n ·) / M n ω`
are e-variables for `S₁`, chosen from the past.

The one-step condition is pointwise, at every past, and it makes `M` a supermartingale under every
law under which each observation, given the past, has a conditional law in `S₁`: the sequential
null of `S₁` (`ProbabilityTheory.isENNSupermartingale_sequentialNull_of_lintegral_update_le`).
This null is much larger than the i.i.d. null `iidNull S₁`, and a supermartingale under the i.i.d.
laws only sees the pasts that these laws charge. Still, for a convex `S₁` in which every point is
an atom of some member, the two nulls have the same supermartingales [EVR26, Note 31, Theorem 1 and
its corollary]: at a past `ω`, take `ρ ∈ S₁` charging the observations of `ω`, and the
supermartingale inequality on the cylinder of `ω`, which has positive probability under the i.i.d.
law of `(1 - a) • ρ + a • ν ∈ S₁`, gives the one-step condition for `(1 - a) • ρ + a • ν`, hence
`a * ∫⁻ y, M (n + 1) (Function.update ω n y) ∂ν ≤ M n ω` for every `a < 1`. Compare the
fork-convexity principle of [RRLK22, Theorem 13], which carries the supermartingales of a null to
its closed fork-convex hull: here the convexity and atom hypotheses reach the larger sequential
null. Under these hypotheses, an e-process of the i.i.d. null that is not an e-process of the
sequential null is never a test supermartingale.

For a convex `S₁` containing every Dirac mass, as the set of all laws on `𝓧`, the one-step
condition at the Dirac mass of the actual observation gives `M (n + 1) ω ≤ M n ω`: every
supermartingale of the i.i.d. null is nonincreasing along every sequence, and every test
supermartingale is at most `1` everywhere [RRLK22, Theorem 17], so that no test supermartingale
has any power. For the i.i.d. coins, the e-processes are not so limited: the process equal to
`1` at time `0`, to `𝟙{ω 0 = false}` at time `1`, and to `4 • 𝟙{ω 0 = false, ω 1 = true}` from
time `2` on (`ProbabilityTheory.coinEProcess`) is an e-process, which reaches `4` and so is not a
supermartingale [EVR26, Note 31, Theorem 5 (3)].

## Main definitions

* `ProbabilityTheory.coinEProcess`: the e-process
  `1, 𝟙{ω 0 = false}, 4 • 𝟙{ω 0 = false, ω 1 = true}` on binary sequences.

## Main statements

* `ProbabilityTheory.isENNSupermartingale_sequentialNull_of_lintegral_update_le`: a process with
  the one-step condition is a supermartingale for the sequential null.
* `ProbabilityTheory.IsENNSupermartingale.lintegral_update_le_of_infinitePi`: a supermartingale
  under the i.i.d. law of `μ` satisfies the one-step condition for `μ` at every past charged by
  `μ`.
* `ProbabilityTheory.IsENNSupermartingale.lintegral_update_le_of_iidNull`: for a convex null in
  which every point is an atom of a member, a supermartingale for the i.i.d. null satisfies the
  one-step condition at every past.
* `ProbabilityTheory.isENNSupermartingale_iidNull_iff`,
  `ProbabilityTheory.isENNSupermartingale_iidNull_iff_sequentialNull`,
  `ProbabilityTheory.isTestSupermartingale_iidNull_iff_sequentialNull`: under these hypotheses,
  the supermartingales and the test supermartingales of the i.i.d. null are those of the
  sequential null, and are characterized by the one-step condition.
* `ProbabilityTheory.IsENNSupermartingale.isEVar_div_update_of_iidNull`: their one-step ratios
  are e-variables for the one-step null.
* `ProbabilityTheory.IsENNSupermartingale.antitone_of_iidNull`,
  `ProbabilityTheory.IsTestSupermartingale.le_one_of_iidNull`: for a convex null containing the
  Dirac masses, the supermartingales of the i.i.d. null are nonincreasing, and its test
  supermartingales are at most `1`.
* `ProbabilityTheory.isEProcess_coinEProcess`,
  `ProbabilityTheory.not_isENNSupermartingale_coinEProcess`: an e-process for the i.i.d. coins
  that reaches `4`, and so is not a supermartingale.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 31,
  *E-processes for i.i.d. nulls: what supermartingales cannot see, and an exact admissibility
  criterion*, Theorems 1 and 5 (`results/31-iid-eprocesses.md`).
* [RRLK22] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Testing exchangeability: fork-convexity,
  supermartingales and e-processes*, Int. J. Approx. Reason. 141 (2022), arXiv:2102.00630.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
  {S₁ : Set (Measure 𝓧)}

/-! ### Sufficiency: the one-step condition -/

/-- **Betting supermartingales are supermartingales for the sequential null.** Let `M` be
adapted to `Filtration.piLT` and satisfy the one-step condition at every past `ω` of length `n`:
`∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω` for every `ν` in the one-step null `S₁ n ω`. Then
`M` is a supermartingale under every law under which each observation has, given the past, a
conditional law in the one-step null: the sequential null of `S₁`. -/
theorem isENNSupermartingale_sequentialNull_of_lintegral_update_le
    {S₁ : ℕ → (ℕ → 𝓧) → Set (Measure 𝓧)} (hM : Adapted Filtration.piLT M)
    (h : ∀ n ω, ∀ ν ∈ S₁ n ω, ∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω) :
    IsENNSupermartingale M Filtration.piLT
      (sequentialNull S₁ (fun k ω ↦ ω k) Filtration.piLT) := by
  refine ⟨hM, fun P hP n s hs ↦ ?_⟩
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP n
  calc ∫⁻ ω in s, M (n + 1) ω ∂P = ∫⁻ ω in s, M (n + 1) (update ω n (ω n)) ∂P := by
        simp only [update_eq_self]
    _ = ∫⁻ ω in s, ∫⁻ y, M (n + 1) (update ω n y) ∂(κ ω) ∂P :=
        hκ.setLIntegral_comp (Filtration.le _ n) (hM.measurable_uncurry_update_piLT n) hs
    _ ≤ ∫⁻ ω in s, M n ω ∂P :=
        lintegral_mono_ae (ae_restrict_of_ae (hκS.mono fun ω hω ↦ h n ω _ hω))

/-! ### Necessity at the pasts charged by an i.i.d. law -/

variable [MeasurableSingletonClass 𝓧]

/-- **The one-step condition at a charged past.** A supermartingale for `Filtration.piLT` under
the i.i.d. law of a probability measure `μ` satisfies the one-step condition for `μ` at every past
`ω` of length `n` whose observations are atoms of `μ`:
`∫⁻ y, M (n + 1) (update ω n y) ∂μ ≤ M n ω`. -/
theorem IsENNSupermartingale.lintegral_update_le_of_infinitePi {μ : Measure 𝓧}
    [IsProbabilityMeasure μ]
    (hM : IsENNSupermartingale M Filtration.piLT {Measure.infinitePi fun _ : ℕ ↦ μ}) {n : ℕ}
    {ω : ℕ → 𝓧} (hω : ∀ i < n, μ {ω i} ≠ 0) :
    ∫⁻ y, M (n + 1) (update ω n y) ∂μ ≤ M n ω := by
  let P := Measure.infinitePi fun _ : ℕ ↦ μ
  -- the cylinder of the past `ω`, an event of positive probability at time `n`
  set C := {ω' : ℕ → 𝓧 | ∀ i < n, ω' i = ω i}
  have hC : MeasurableSet[Filtration.piLT n] C := by
    have : C = ⋂ i : Fin n, (fun ω' : ℕ → 𝓧 ↦ ω' i) ⁻¹' {ω i} := by
      ext ω'
      simp [C, Fin.forall_iff]
    rw [this]
    exact MeasurableSet.iInter fun i ↦
      Filtration.measurable_piLT_apply i.isLt (measurableSet_singleton _)
  have hPC : P C ≠ 0 := by
    have : C = Set.pi (Finset.range n : Set ℕ) fun i ↦ {ω i} := by
      ext ω'
      simp [C]
    rw [this, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
    exact Finset.prod_ne_zero_iff.2 fun i hi ↦ hω i (Finset.mem_range.1 hi)
  -- the conditional law of the next observation given the past is `μ`
  obtain ⟨κ, hκ, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull
    (infinitePi_mem_sequentialNull (S₁ := fun _ _ ↦ {μ}) (μ := fun _ ↦ μ) fun _ ↦
      .of_forall fun _ ↦ rfl) n
  have h1 : ∫⁻ ω' in C, M (n + 1) ω' ∂P = (∫⁻ y, M (n + 1) (update ω n y) ∂μ) * P C := by
    calc ∫⁻ ω' in C, M (n + 1) ω' ∂P = ∫⁻ ω' in C, M (n + 1) (update ω' n (ω' n)) ∂P := by
          simp only [update_eq_self]
      _ = ∫⁻ ω' in C, ∫⁻ y, M (n + 1) (update ω' n y) ∂(κ ω') ∂P :=
          hκ.setLIntegral_comp (Filtration.le _ n) (hM.adapted.measurable_uncurry_update_piLT n)
            hC
      _ = ∫⁻ ω' in C, ∫⁻ y, M (n + 1) (update ω n y) ∂μ ∂P := by
          refine setLIntegral_congr_fun_ae (Filtration.le _ n C hC)
            (hκS.mono fun ω' hκω' hω' ↦ ?_)
          rw [mem_singleton_iff.1 hκω']
          exact lintegral_congr fun y ↦ (hM.adapted (n + 1)).apply_update_eq_of_piLT hω' y
      _ = _ := setLIntegral_const _ _
  have h0 : ∫⁻ ω' in C, M n ω' ∂P = M n ω * P C := by
    rw [setLIntegral_congr_fun (Filtration.le _ n C hC)
      fun ω' hω' ↦ (hM.adapted n).dependsOn_of_piLT fun i hi ↦ hω' i hi, setLIntegral_const]
  have key := hM.setLIntegral_succ_le P rfl n C hC
  rw [h1, h0] at key
  exact (ENNReal.mul_le_mul_iff_left hPC (measure_ne_top P C)).1 key

/-- **The supermartingales of an i.i.d. null are betting supermartingales**
[EVR26, Note 31, Theorem 1 and its corollary]. Let `S₁` be a convex set of probability measures
in which every point of `𝓧` is an atom of some member. A supermartingale for `Filtration.piLT`
under the i.i.d. law of every member of `S₁` satisfies the one-step condition at every past `ω` of
length `n` and for every `ν ∈ S₁`: `∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω`. -/
theorem IsENNSupermartingale.lintegral_update_le_of_iidNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hatom : ∀ x, ∃ P ∈ S₁, P {x} ≠ 0)
    (hM : IsENNSupermartingale M Filtration.piLT (iidNull S₁)) (n : ℕ) (ω : ℕ → 𝓧)
    {ν : Measure 𝓧} (hν : ν ∈ S₁) :
    ∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω := by
  classical
  obtain ⟨ρ, hρ, hρω⟩ := hconv.exists_mem_forall_measure_ne_zero ⟨ν, hν⟩
    (s := Finset.range n) (A := fun i ↦ {ω i}) fun i _ ↦ hatom (ω i)
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  -- the mixture `μ = (1 - a) • ρ + a • ν` charges the past and puts the weight `a` on `ν`
  have ha' : 1 - a ≠ 0 := (tsub_pos_of_lt ha).ne'
  have hμ : (1 - a) • ρ + a • ν ∈ S₁ := hconv hρ hν zero_le zero_le (tsub_add_cancel_of_le ha.le)
  have := hS₁ _ hμ
  have hμω : ∀ i < n, ((1 - a) • ρ + a • ν) {ω i} ≠ 0 := fun i hi ↦ by
    simp only [add_apply, smul_apply, smul_eq_mul, ne_eq, add_eq_zero,
      mul_eq_zero, not_and, not_or]
    exact fun h ↦ absurd h (by
      simpa [ha'] using hρω i (Finset.mem_range.2 hi))
  have h := lintegral_update_le_of_infinitePi
    (hM.anti_set (singleton_subset_iff.2 (infinitePi_mem_iidNull hμ))) hμω
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure] at h
  exact le_add_self.trans h

/-- **The supermartingales of an i.i.d. null are the betting supermartingales**
[EVR26, Note 31, Theorem 1 and its corollary]. For a convex set `S₁` of probability measures in
which every point of `𝓧` is an atom of some member, an adapted process is a supermartingale for
`Filtration.piLT` under the i.i.d. law of every member of `S₁` exactly when it satisfies the
one-step condition `∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω` at every past `ω` and for every
`ν ∈ S₁`. -/
theorem isENNSupermartingale_iidNull_iff (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hatom : ∀ x, ∃ P ∈ S₁, P {x} ≠ 0)
    (hM : Adapted Filtration.piLT M) :
    IsENNSupermartingale M Filtration.piLT (iidNull S₁) ↔
      ∀ n ω, ∀ ν ∈ S₁, ∫⁻ y, M (n + 1) (update ω n y) ∂ν ≤ M n ω :=
  ⟨fun h n ω _ hν ↦ h.lintegral_update_le_of_iidNull hconv hS₁ hatom n ω hν, fun h ↦
    (isENNSupermartingale_sequentialNull_of_lintegral_update_le (S₁ := fun _ _ ↦ S₁) hM
      h).anti_set (iidNull_subset_sequentialNull hS₁)⟩

/-- **An i.i.d. null and its sequential null have the same supermartingales**
[EVR26, Note 31, Theorem 1 and its corollary]. For a convex set `S₁` of
probability measures in which every point of `𝓧` is an atom of some member, a process is a
supermartingale for `Filtration.piLT` under the i.i.d. laws of the members of `S₁` exactly when
it is one under every law whose observations have, given the past, conditional laws in `S₁`. -/
theorem isENNSupermartingale_iidNull_iff_sequentialNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hatom : ∀ x, ∃ P ∈ S₁, P {x} ≠ 0) :
    IsENNSupermartingale M Filtration.piLT (iidNull S₁) ↔
      IsENNSupermartingale M Filtration.piLT
        (sequentialNull (fun _ _ ↦ S₁) (fun k ω ↦ ω k) Filtration.piLT) :=
  ⟨fun h ↦ isENNSupermartingale_sequentialNull_of_lintegral_update_le h.adapted fun n ω _ hν ↦
    h.lintegral_update_le_of_iidNull hconv hS₁ hatom n ω hν,
    fun h ↦ h.anti_set (iidNull_subset_sequentialNull hS₁)⟩

/-- **An i.i.d. null and its sequential null have the same test supermartingales**
[EVR26, Note 31, Theorem 1 and its corollary]. For a convex set `S₁` of
probability measures in which every point of `𝓧` is an atom of some member, the test
supermartingales for `Filtration.piLT` of the i.i.d. null of `S₁` are those of its sequential
null. -/
theorem isTestSupermartingale_iidNull_iff_sequentialNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hatom : ∀ x, ∃ P ∈ S₁, P {x} ≠ 0) :
    IsTestSupermartingale M Filtration.piLT (iidNull S₁) ↔
      IsTestSupermartingale M Filtration.piLT
        (sequentialNull (fun _ _ ↦ S₁) (fun k ω ↦ ω k) Filtration.piLT) := by
  refine ⟨fun h ↦ ⟨(isENNSupermartingale_iidNull_iff_sequentialNull hconv hS₁ hatom).1
    h.toIsENNSupermartingale, fun P hP ↦ ?_⟩,
    fun h ↦ h.anti_set (iidNull_subset_sequentialNull hS₁)⟩
  -- the initial value is a constant, which is at most `1` under an i.i.d. law
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, -, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP 0
  obtain ⟨ω₀, hω₀⟩ := hκS.exists
  have hS₁' := hS₁ _ hω₀
  have hconst : ∀ ω, M 0 ω = M 0 ω₀ := fun ω ↦
    (h.adapted 0).apply_eq_of_piLT_zero ω ω₀
  have h1 := h.lintegral_zero_le _ (infinitePi_mem_iidNull hω₀)
  simp only [hconst, lintegral_const, measure_univ, mul_one] at h1 ⊢
  exact h1

/-- **The one-step ratios of a supermartingale of an i.i.d. null are e-variables**
[EVR26, Note 31, corollary of Theorem 1]. For a convex set `S₁` of probability measures in which
every point of `𝓧` is an atom of some member, and a supermartingale `M` for `Filtration.piLT`
under the i.i.d. laws of the members of `S₁`, the ratio
`y ↦ M (n + 1) (update ω n y) / M n ω`, with `0 / 0 = 0` and `x / ∞ = 0`, is an e-variable for
`S₁` at every past `ω` of length `n`: `M` bets on each observation an e-variable for `S₁` chosen
from the past. -/
theorem IsENNSupermartingale.isEVar_div_update_of_iidNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hatom : ∀ x, ∃ P ∈ S₁, P {x} ≠ 0)
    (hM : IsENNSupermartingale M Filtration.piLT (iidNull S₁)) (n : ℕ) (ω : ℕ → 𝓧) :
    IsEVar (fun y ↦ M (n + 1) (update ω n y) / M n ω) S₁ := by
  have hmeas : Measurable fun y ↦ M (n + 1) (update ω n y) :=
    (hM.measurable (n + 1)).comp (measurable_update ω)
  refine ⟨hmeas.div_const _, fun ν hν ↦ ?_⟩
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const _ hmeas]
  calc (∫⁻ y, M (n + 1) (update ω n y) ∂ν) * (M n ω)⁻¹ ≤ M n ω * (M n ω)⁻¹ := by
        gcongr
        exact hM.lintegral_update_le_of_iidNull hconv hS₁ hatom n ω hν
    _ ≤ 1 := ENNReal.mul_inv_le_one _

/-! ### Nulls containing the Dirac masses -/

/-- **The supermartingales of an i.i.d. null containing the Dirac masses are nonincreasing**
[RRLK22, Theorem 17; EVR26, Note 31, Theorem 5 (1)]. For a convex set `S₁` of probability
measures that contains the Dirac mass of every point of `𝓧`, for instance the set of all
probability measures on `𝓧`, every supermartingale for `Filtration.piLT` under the i.i.d. laws of
the members of `S₁` is nonincreasing along every sequence. -/
theorem IsENNSupermartingale.antitone_of_iidNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hdirac : ∀ x, Measure.dirac x ∈ S₁)
    (hM : IsENNSupermartingale M Filtration.piLT (iidNull S₁)) : Antitone M := by
  refine antitone_nat_of_succ_le fun n ω ↦ ?_
  have h := hM.lintegral_update_le_of_iidNull hconv hS₁
    (fun x ↦ ⟨_, hdirac x, by simp⟩) n ω (hdirac (ω n))
  rwa [lintegral_dirac, update_eq_self] at h

/-- **The test supermartingales of an i.i.d. null containing the Dirac masses are powerless**
[RRLK22, Theorem 17; EVR26, Note 31, Theorem 5 (1)]. For a convex set `S₁` of probability
measures that contains the Dirac mass of every point of `𝓧`, for instance the set of all
probability measures on `𝓧`, every test supermartingale for `Filtration.piLT` and the i.i.d. null
of `S₁` is at most `1` everywhere: the sequential test that rejects when it reaches a level above
`1` never rejects. -/
theorem IsTestSupermartingale.le_one_of_iidNull (hconv : Convex ℝ≥0∞ S₁)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hdirac : ∀ x, Measure.dirac x ∈ S₁)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) (n : ℕ) (ω : ℕ → 𝓧) :
    M n ω ≤ 1 := by
  refine (hM.antitone_of_iidNull hconv hS₁ hdirac (Nat.zero_le n) ω).trans ?_
  have hconst : ∀ ω', M 0 ω' = M 0 ω := fun ω' ↦
    (hM.adapted 0).apply_eq_of_piLT_zero ω' ω
  have h1 := hM.lintegral_zero_le _ (infinitePi_mem_iidNull (hdirac (ω 0)))
  simpa [hconst] using h1

/-! ### An e-process for the i.i.d. coins -/

/-- For a probability measure `μ` on `Bool`, `4 * μ {false} * μ {true} ≤ 1`. -/
private lemma four_mul_measure_false_mul_measure_true_le_one (μ : Measure Bool)
    [IsProbabilityMeasure μ] : 4 * (μ {false} * μ {true}) ≤ 1 := by
  have hsum : μ {false} + μ {true} = 1 := by
    rw [← measure_univ (μ := μ), ← Finset.coe_univ, ← sum_measure_singleton, Fintype.sum_bool,
      add_comm]
  rw [← ENNReal.coe_toNNReal (measure_ne_top μ {false}),
    ← ENNReal.coe_toNNReal (measure_ne_top μ {true})] at hsum ⊢
  have hsum' : (μ {false}).toNNReal + (μ {true}).toNNReal = 1 := by exact_mod_cast hsum
  have h := four_mul_le_sq_add (μ {false}).toNNReal (μ {true}).toNNReal
  rw [hsum', one_pow, mul_assoc] at h
  exact_mod_cast h

/-- **The e-process of the i.i.d. coins** [EVR26, Note 31, Theorem 5 (3)]: on binary sequences,
the process equal to `1` at time `0`, to `𝟙{ω 0 = false}` at time `1` and to
`4 • 𝟙{ω 0 = false, ω 1 = true}` from time `2` on. -/
noncomputable def coinEProcess (n : ℕ) (ω : ℕ → Bool) : ℝ≥0∞ :=
  if n = 0 then 1 else if n = 1 then (if ω 0 = false then 1 else 0)
  else if ω 0 = false ∧ ω 1 = true then 4 else 0

@[simp]
lemma coinEProcess_zero (ω : ℕ → Bool) : coinEProcess 0 ω = 1 := by
  simp [coinEProcess]

@[simp]
lemma coinEProcess_one (ω : ℕ → Bool) : coinEProcess 1 ω = if ω 0 = false then 1 else 0 := by
  simp [coinEProcess]

@[simp]
lemma coinEProcess_add_two (n : ℕ) (ω : ℕ → Bool) :
    coinEProcess (n + 2) ω = if ω 0 = false ∧ ω 1 = true then 4 else 0 := by
  simp [coinEProcess]

/-- A bounded stopping time of `Filtration.piLT` either stops `coinEProcess` at a value at most `1`
on every binary sequence, or at a value at most its value `4 • 𝟙{ω 0 = false, ω 1 = true}` at
time `2` on every binary sequence. -/
private lemma stoppedValue_coinEProcess_le {τ : (ℕ → Bool) → WithTop ℕ}
    (hτ : IsStoppingTime Filtration.piLT τ) {N : ℕ} (hτN : ∀ ω, τ ω ≤ N) :
    (∀ ω, stoppedValue coinEProcess τ ω ≤ 1) ∨
      ∀ ω, stoppedValue coinEProcess τ ω ≤ coinEProcess 2 ω := by
  -- every bounded stopping time is finite, at a time `k` with `coinEProcess k ω` its stopped value
  have hk : ∀ ω, ∃ k : ℕ, τ ω = k ∧ stoppedValue coinEProcess τ ω = coinEProcess k ω := fun ω ↦ by
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτN ω))
    exact ⟨k, hk.symm, stoppedValue_of_eq_natCast hk.symm⟩
  by_cases hτ0 : ∃ ω, τ ω = ((0 : ℕ) : WithTop ℕ)
  · -- a time that stops at `0` somewhere stops at `0` everywhere
    obtain ⟨ω₀, hω₀⟩ := hτ0
    refine .inl fun ω ↦ ?_
    rw [stoppedValue_of_eq_natCast (hτ.eq_of_forall_lt hω₀ fun i hi ↦ absurd hi (by omega)),
      coinEProcess_zero]
  have hτ0' : ∀ ω (k : ℕ), τ ω = k → k ≠ 0 := fun ω k h hk0 ↦ hτ0 ⟨ω, by rw [h, hk0]⟩
  by_cases hτ1 : ∃ ω, ω 0 = false ∧ τ ω = ((1 : ℕ) : WithTop ℕ)
  · -- the time stops at `1` on every sequence starting with `false`
    obtain ⟨ω₀, hω₀f, hω₀⟩ := hτ1
    refine .inl fun ω ↦ ?_
    obtain ⟨k, hτk, hk⟩ := hk ω
    rw [hk]
    have := hτ0' ω k hτk
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | h2
    · rw [coinEProcess_one]
      split_ifs <;> simp
    · have hω0 : ω 0 = true := by
        by_contra hω0
        have h1 := hτ.eq_of_forall_lt hω₀ fun i hi ↦ by
          obtain rfl : i = 0 := by omega
          simpa [hω₀f] using hω0
        rw [hτk] at h1
        have : k = 1 := by exact_mod_cast h1
        omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h2
      simp [hω0]
  · push Not at hτ1
    refine .inr fun ω ↦ ?_
    obtain ⟨k, hτk, hk⟩ := hk ω
    rw [hk]
    have := hτ0' ω k hτk
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | h2
    · cases hω0 : ω 0
      · exact absurd hτk (hτ1 ω hω0)
      · simp [hω0]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h2
      simp

/-- Under the i.i.d. law of a coin `μ`, the value `4 • 𝟙{ω 0 = false, ω 1 = true}` of
`coinEProcess` at time `2` has expectation `4 * (μ {false} * μ {true})`. -/
private lemma lintegral_coinEProcess_two (μ : Measure Bool) [IsProbabilityMeasure μ] :
    ∫⁻ ω, coinEProcess 2 ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ) = 4 * (μ {false} * μ {true}) := by
  have hA : {ω : ℕ → Bool | ω 0 = false ∧ ω 1 = true} =
      Set.pi (({0, 1} : Finset ℕ) : Set ℕ) fun i ↦ if i = 0 then {false} else {true} := by
    ext ω
    simp
  have hF : coinEProcess 2 = {ω : ℕ → Bool | ω 0 = false ∧ ω 1 = true}.indicator fun _ ↦ 4 := by
    ext ω
    simp only [coinEProcess_add_two 0 ω, indicator, mem_ofPred_eq]
  have ht : ∀ i ∈ (({0, 1} : Finset ℕ) : Set ℕ),
      MeasurableSet (if i = 0 then {false} else ({true} : Set Bool)) := fun _ _ ↦ by
    split_ifs <;> exact measurableSet_singleton _
  rw [hF, hA, lintegral_indicator_const (.pi (Finset.countable_toSet _) ht),
    Measure.infinitePi_pi _ ht, Finset.prod_pair zero_ne_one]
  simp

/-- **An e-process for the i.i.d. coins that no test supermartingale matches**
[EVR26, Note 31, Theorem 5 (3)]. The process `coinEProcess`, equal on binary sequences to `1` at
time `0`, to `𝟙{ω 0 = false}` at time `1` and to `4 • 𝟙{ω 0 = false, ω 1 = true}` from time `2`
on, is an e-process for `Filtration.piLT` and the i.i.d. laws of all the coins. It reaches `4`,
while every test supermartingale of this null is at most `1`
(`ProbabilityTheory.IsTestSupermartingale.le_one_of_iidNull`). -/
theorem isEProcess_coinEProcess :
    IsEProcess coinEProcess Filtration.piLT
      (iidNull {P : Measure Bool | IsProbabilityMeasure P}) := by
  have h0 : MeasurableSet[Filtration.piLT 1] {ω : ℕ → Bool | ω 0 = false} :=
    Filtration.measurable_piLT_apply (X := fun _ : ℕ ↦ Bool) zero_lt_one
      (measurableSet_singleton false)
  have hA : ∀ n, MeasurableSet[Filtration.piLT (n + 2)]
      {ω : ℕ → Bool | ω 0 = false ∧ ω 1 = true} := fun n ↦
    (Filtration.measurable_piLT_apply (X := fun _ : ℕ ↦ Bool) (by omega)
      (measurableSet_singleton false)).inter
      (Filtration.measurable_piLT_apply (X := fun _ : ℕ ↦ Bool) (by omega)
        (measurableSet_singleton true))
  refine IsEProcess.of_lintegral_le_one (fun n ↦ ?_) fun τ hτ N hτN P hP ↦ ?_
  · unfold coinEProcess
    rcases n with _ | _ | n
    · simp
    · simpa using Measurable.ite h0 measurable_const measurable_const
    · simpa using Measurable.ite (hA n) measurable_const measurable_const
  obtain ⟨μ, hμ, rfl⟩ := mem_iidNull.1 hP
  have : IsProbabilityMeasure μ := hμ
  rcases stoppedValue_coinEProcess_le hτ hτN with h | h
  · exact (lintegral_mono h).trans (by simp)
  · exact (lintegral_mono h).trans ((lintegral_coinEProcess_two μ).trans_le
      (four_mul_measure_false_mul_measure_true_le_one μ))

/-- **The e-process of the i.i.d. coins is not a supermartingale** [EVR26, Note 31,
Theorem 5 (3)]: `coinEProcess` is not a supermartingale for `Filtration.piLT` under the i.i.d.
laws of all the coins, since it increases from `1` to `4` on the sequences starting with
`false, true`. -/
theorem not_isENNSupermartingale_coinEProcess :
    ¬ IsENNSupermartingale coinEProcess Filtration.piLT
      (iidNull {P : Measure Bool | IsProbabilityMeasure P}) := by
  intro h
  have := h.antitone_of_iidNull convex_setOfPred_isProbabilityMeasure (fun _ h ↦ h)
    (fun x ↦ (inferInstance : IsProbabilityMeasure (Measure.dirac x))) (by omega : 1 ≤ 2)
    fun i ↦ if i = 0 then false else true
  norm_num at this

end ProbabilityTheory
