/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
public import LMLExplore.Probability.Distributions.ProdBernoulli
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.ConvexPieces
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.InformationTheory.KullbackLeibler.Finite
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import LMLExplore.Probability.Process.LevelCrossing
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import TauCeti.Probability.StrongLaw

/-!
# The plug-in intersection–union test for a union of convex pieces of coins

An observation is a vector of independent coins indexed by a finite type `ι`, with law
`prodBernoulli θ`; the observations are the coordinates of `ℕ → ι → Bool`, with the filtration
`Filtration.piLT` of the past observations. The null is a union of convex pieces: the laws
`prodBernoulli θ` for `θ` in `C j`, `j` in a type `κ`, each `C j` a convex set of parameters in
the cube `[0, 1] ^ ι`. For every `φ` in the open cube, let `lam j φ ∈ C j`, in the open cube, be a
minimizer of `θ ↦ KL(prodBernoulli φ ‖ prodBernoulli θ)` over `C j`: a projection of `φ` on the
piece. When the alternative `prodBernoulli ψ` is known, the minimum over `j` of the likelihood
ratio processes of `prodBernoulli ψ` against `prodBernoulli (lam j ψ)` is an e-process that grows
at the rate `KL_inf` (`ProbabilityTheory.isEProcess_minLikelihoodRatio_prodBernoulli`,
`ProbabilityTheory.ae_tendsto_log_minLikelihoodRatio_prodBernoulli_div`). When it is not, it is
estimated: let `ψhat k` be an estimate with values in the open cube that is a function
of the observations before `k`. The plug-in likelihood ratio process against the piece `j` is
`∏ k < n, prodBernoulli (ψhat k) {X k} / prodBernoulli (lam j (ψhat k)) {X k}`, and the plug-in
intersection–union process `M n` is its minimum over `j` [EVR26, Note 32, Statement 4].

**Validity, whatever the estimate.** Given the past, the estimate `ψhat k` is fixed, and the factor
of round `k` is the likelihood ratio of `prodBernoulli (ψhat k)` against its projection on the
piece, an e-variable for the laws of the piece
(`ProbabilityTheory.isEVar_prodBernoulli_div_prodBernoulli`). The plug-in likelihood ratio process
against the piece `j` is then a test supermartingale for the sequential null of the piece: for
every law under which every observation, given the past, has a law of the piece
(`ProbabilityTheory.isTestSupermartingale_prod_sequentialNull`). The minimum `M` is below each of
them, so it is an e-process for the union over `j` of the sequential nulls of the pieces, which
contains the i.i.d. laws of the coins with parameters in the union of the pieces, and its test at
`α⁻¹` has level `α`. No measurability of the projections is needed: on the finite alphabet of the
coins, a function of the first `n` observations is measurable at time `n`.

**Growth, for a consistent estimate.** Let `κ` be finite, `ψ` be in the open cube, and `ψhat k`
tend to `ψ` almost surely under the i.i.d. law of `prodBernoulli ψ`. Then almost surely
`(1/n) log (M n)` tends to `KL_inf`, the smallest relative entropy from `prodBernoulli ψ` to the
union of the pieces, and the first time `τ α` that `M` reaches `α⁻¹` has
`τ α / log (1/α) → 1 / KL_inf` as `α → 0`, with `1 / 0 = ∞`. The upper bound
`limsup (1/n) log (M n) ≤ KL_inf` holds for every e-process for the i.i.d. null, at the bipolar
rate (`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`), which is `KL_inf` for a
union of convex pieces (`ProbabilityTheory.bipolarRate_prodBernoulli_iUnion_eq_klInf`). For the
lower bound, the logarithm of the plug-in likelihood ratio against the piece `j` is the sum of
three terms:
* the oracle term `∑ k < n, log (P_ψ {X k} / P_{lam j ψ} {X k})`, which grows like
  `n KL(P_ψ ‖ P_{lam j ψ})` by the strong law of large numbers;
* the estimation term `∑ k < n, (log P_{ψhat k} {X k} - log P_ψ {X k})`, which is `o(n)` since the
  masses are continuous in the parameters;
* the projection term `∑ k < n, (log P_{lam j ψ} {X k} - log P_{lam j (ψhat k)} {X k})`, which is
  eventually at least `-ε n` for every `ε > 0`: given the past, its terms have the nonnegative mean
  `KL(P_ψ ‖ P_{lam j (ψhat k)}) - KL(P_ψ ‖ P_{lam j ψ})`, by the minimality of `lam j ψ`; the
  projections of the estimates near `ψ` stay in a cube `[δ, 1 - δ] ^ ι`, where the terms are
  bounded, and exponential test supermartingales with Ville's inequality bound their sum below.
No continuity of the projections and no closedness of the pieces are needed.

## Main definitions

* `ProbabilityTheory.plugInLikelihoodRatio ψhat lam`: the likelihood ratio process of the
  estimated coins against their projection by `lam`.
* `ProbabilityTheory.minPlugInLikelihoodRatio ψhat lam`: its minimum over the pieces.

## Main statements

* `ProbabilityTheory.adapted_minPlugInLikelihoodRatio`: for predictable estimates, the plug-in
  intersection–union process is adapted, with no measurability of the projections.
* `ProbabilityTheory.isTestSupermartingale_plugInLikelihoodRatio`
  [EVR26, Note 32, Statement 4]: the plug-in likelihood ratio process against a convex piece is a
  test supermartingale for the sequential null of the piece, whatever the estimate.
* `ProbabilityTheory.isEProcess_minPlugInLikelihoodRatio`,
  `ProbabilityTheory.isLevelStoppingTime_hittingAfter_minPlugInLikelihoodRatio`
  [EVR26, Note 32, Statement 4]: the minimum over the pieces is an e-process for the union of the
  sequential nulls of the pieces, and its test at `α⁻¹` has level `α`.
* `ProbabilityTheory.ae_tendsto_log_minPlugInLikelihoodRatio_div`,
  `ProbabilityTheory.ae_tendsto_hittingAfter_minPlugInLikelihoodRatio_div_log`
  [EVR26, Note 32, Statement 4]: for a consistent estimate, `(1/n) log (M n)` tends to `KL_inf`
  and `τ α / log (1/α)` to `1 / KL_inf`, almost surely.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/ConvexPiecesTests.lean` and
`EValuesResearch/Results/ConvexPiecesTestsAux.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore: the validity is stated for
the sequential nulls of the pieces, which may touch the faces of the cube, and is derived from the
products of e-variables chosen from the past against the sequential null.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter Set LMLExplore
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι κ : Type*} [Fintype ι]

/-! ### The plug-in likelihood ratio processes -/

/-- The likelihood ratio process of the estimated coins against their projection on a piece: at
time `n`, the product over the past observations `k < n` of the ratios
`prodBernoulli (ψhat k ω) {ω k} / prodBernoulli (lam (ψhat k ω)) {ω k}`, where `ψhat k ω` is an
estimate of the parameter from the observations before `k` and `lam` the projection on the
piece. -/
noncomputable def plugInLikelihoodRatio (ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ)
    (lam : (ι → ℝ) → ι → ℝ) (n : ℕ) (ω : ℕ → ι → Bool) : ℝ≥0∞ :=
  ∏ k ∈ Finset.range n, prodBernoulli (ψhat k ω) {ω k} / prodBernoulli (lam (ψhat k ω)) {ω k}

/-- The value of `plugInLikelihoodRatio`. -/
theorem plugInLikelihoodRatio_def (ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ)
    (lam : (ι → ℝ) → ι → ℝ) (n : ℕ) (ω : ℕ → ι → Bool) :
    plugInLikelihoodRatio ψhat lam n ω =
      ∏ k ∈ Finset.range n, prodBernoulli (ψhat k ω) {ω k} / prodBernoulli (lam (ψhat k ω)) {ω k} :=
  (rfl)

/-- The **plug-in intersection–union process** of [EVR26, Note 32, Statement 4]: the minimum over
the pieces `j` of the plug-in likelihood ratio processes against the projections `lam j`. -/
noncomputable def minPlugInLikelihoodRatio (ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ)
    (lam : κ → (ι → ℝ) → ι → ℝ) (n : ℕ) (ω : ℕ → ι → Bool) : ℝ≥0∞ :=
  ⨅ j, plugInLikelihoodRatio ψhat (lam j) n ω

/-- The value of `minPlugInLikelihoodRatio`. -/
theorem minPlugInLikelihoodRatio_def (ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ)
    (lam : κ → (ι → ℝ) → ι → ℝ) (n : ℕ) (ω : ℕ → ι → Bool) :
    minPlugInLikelihoodRatio ψhat lam n ω = ⨅ j, plugInLikelihoodRatio ψhat (lam j) n ω :=
  (rfl)

/-- The plug-in intersection–union process is at most each plug-in likelihood ratio process. -/
theorem minPlugInLikelihoodRatio_le (ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ)
    (lam : κ → (ι → ℝ) → ι → ℝ) (j : κ) (n : ℕ) (ω : ℕ → ι → Bool) :
    minPlugInLikelihoodRatio ψhat lam n ω ≤ plugInLikelihoodRatio ψhat (lam j) n ω :=
  iInf_le _ j

variable {ψhat : ℕ → (ℕ → ι → Bool) → ι → ℝ}

omit [Fintype ι] in
/-- On the finite alphabet of the coins, a function of the observations before `n` is measurable
at time `n` of `Filtration.piLT`. -/
private lemma measurable_piLT_of_dependsOn_of_finite [Finite ι] {Z : Type*} [MeasurableSpace Z]
    {f : (ℕ → ι → Bool) → Z} {n : ℕ} (hf : DependsOn f (Iio n)) :
    Measurable[Filtration.piLT n] f :=
  Filtration.measurable_piLT_of_dependsOn (hf.measurable_of_countable (finite_Iio n)) hf

/-- With predictable estimates, the plug-in likelihood ratio at time `n` only depends on the
first `n` observations. -/
private lemma dependsOn_plugInLikelihoodRatio
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (lam : (ι → ℝ) → ι → ℝ) (n : ℕ) :
    DependsOn (plugInLikelihoodRatio ψhat lam n) (Iio n) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  have hk' : k < n := Finset.mem_range.1 hk
  have hψ : ψhat k x = ψhat k y :=
    (hψhat k).dependsOn_of_piLT fun i hi ↦ hxy i (mem_Iio.2 ((mem_Iio.1 hi).trans hk'))
  rw [hψ, hxy k (mem_Iio.2 hk')]

/-- With predictable estimates, the plug-in intersection–union process is adapted to the
filtration `Filtration.piLT` of the past observations, with no measurability of the projections:
on the finite alphabet of the coins, a function of the first `n` observations is measurable at
time `n`. -/
theorem adapted_minPlugInLikelihoodRatio
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (lam : κ → (ι → ℝ) → ι → ℝ) :
    Adapted Filtration.piLT (minPlugInLikelihoodRatio ψhat lam) := fun n ↦
  measurable_piLT_of_dependsOn_of_finite fun _ _ hxy ↦
    iInf_congr fun j ↦ dependsOn_plugInLikelihoodRatio hψhat (lam j) n hxy

/-! ### Validity -/

/-- **The plug-in likelihood ratio against the projection on a convex piece is a test
supermartingale, whatever the estimate** [EVR26, Note 32, Statement 4]. Let `C` be a convex set of
parameters in the cube `[0, 1] ^ ι`, `lam φ ∈ C`, in the open cube, a minimizer over `C` of
`θ ↦ KL(prodBernoulli φ ‖ prodBernoulli θ)` for every `φ` in the open cube, and `ψhat k` an
estimate with values in the open cube that is a function of the observations before `k`. The
plug-in likelihood ratio process is a test supermartingale for the sequential null of the laws of
the coins with parameters in `C`: for every law under which every observation, given the past, has
such a law. Given the past, its factor is the likelihood ratio of
`ProbabilityTheory.isEVar_prodBernoulli_div_prodBernoulli`, with the alternative `ψhat k` fixed. -/
theorem isTestSupermartingale_plugInLikelihoodRatio {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hC01 : C ⊆ univ.pi fun _ ↦ Icc 0 1) {lam : (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ C)
    (hmin : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) C (lam φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) :
    IsTestSupermartingale (plugInLikelihoodRatio ψhat lam) Filtration.piLT
      (sequentialNull (fun _ _ ↦ prodBernoulli '' C) (fun k ω ↦ ω k) Filtration.piLT) := by
  refine isTestSupermartingale_prod_sequentialNull
    (r := fun k ω y ↦ prodBernoulli (ψhat k ω) {y} / prodBernoulli (lam (ψhat k ω)) {y})
    (fun k ↦ Filtration.measurable_piLT_apply k.lt_succ_self) (fun k ↦ ?_) fun k ω ↦
      isEVar_prodBernoulli_div_prodBernoulli hC hC01 _ (hlam01 _ (hψhat01 k ω))
        (hlam _ (hψhat01 k ω)) (hmin _ (hψhat01 k ω))
  -- the factor is a function of the past and of the observation, on a finite alphabet
  refine @measurable_from_prod_countable_left _ _ _ (Filtration.piLT k) _ _ _ _ _ fun y ↦ ?_
  refine measurable_piLT_of_dependsOn_of_finite fun x x' hxx' ↦ ?_
  simp only [Function.uncurry_apply_pair]
  rw [(hψhat k).dependsOn_of_piLT hxx']

/-- **The plug-in intersection–union process is an e-process, whatever the estimate**
[EVR26, Note 32, Statement 4]. Under the hypotheses of
`isTestSupermartingale_plugInLikelihoodRatio` for each piece `C j`, the minimum over `j` of the
plug-in likelihood ratio processes is an e-process for every law under which the observations are
drawn sequentially from the laws of one piece: under such a law it is below a test
supermartingale. This contains the i.i.d. laws of the coins with parameters in the union of the
`C j`. -/
theorem isEProcess_minPlugInLikelihoodRatio {C : κ → Set (ι → ℝ)} (hC : ∀ j, Convex ℝ (C j))
    (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1) {lam : κ → (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ C j)
    (hmin : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) (C j) (lam j φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) :
    IsEProcess (minPlugInLikelihoodRatio ψhat lam) Filtration.piLT
      (⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT) := by
  refine isEProcess_iff_forall_singleton.2 ⟨adapted_minPlugInLikelihoodRatio hψhat lam,
    fun P hP ↦ ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hP
  have hE := ((isTestSupermartingale_plugInLikelihoodRatio (hC j) (hC01 j) (hlam01 j) (hlam j)
    (hmin j) hψhat hψhat01).isEProcess fun P hP ↦
      have := isProbabilityMeasure_of_mem_sequentialNull hP; inferInstance).anti_set
    (singleton_subset_iff.2 hj)
  exact hE.mono (adapted_minPlugInLikelihoodRatio hψhat lam) fun n ω ↦
    minPlugInLikelihoodRatio_le ψhat lam j n ω

/-- **The plug-in intersection–union test has level `α`, whatever the estimate**
[EVR26, Note 32, Statement 4]. Under the hypotheses of `isEProcess_minPlugInLikelihoodRatio`,
the test that rejects the first time the minimum of the plug-in likelihood ratios reaches `α⁻¹`
has level `α` for every law under which the observations are drawn sequentially from the laws of
one piece. -/
theorem isLevelStoppingTime_hittingAfter_minPlugInLikelihoodRatio {C : κ → Set (ι → ℝ)}
    (hC : ∀ j, Convex ℝ (C j)) (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1)
    {lam : κ → (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ C j)
    (hmin : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) (C j) (lam j φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) (α : ℝ≥0∞) :
    IsLevelStoppingTime (hittingAfter (minPlugInLikelihoodRatio ψhat lam) (Ici α⁻¹) 0)
      Filtration.piLT
      (⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT)
      α :=
  (isEProcess_minPlugInLikelihoodRatio hC hC01 hlam01 hlam hmin hψhat
    hψhat01).isLevelStoppingTime_hittingAfter α

/-! ### Growth for a consistent estimate -/

/-- The i.i.d. laws of the coins with parameters in a union of pieces are drawn sequentially from
the laws of one piece. -/
private lemma iidNull_prodBernoulli_iUnion_subset {C : κ → Set (ι → ℝ)} :
    iidNull (prodBernoulli '' ⋃ j, C j) ⊆
      ⋃ j, sequentialNull (fun _ _ ↦ prodBernoulli '' C j) (fun k ω ↦ ω k) Filtration.piLT := by
  intro μ hμ
  obtain ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩ := mem_iidNull.1 hμ
  obtain ⟨j, hj⟩ := mem_iUnion.1 hθ
  exact mem_iUnion.2 ⟨j, iidNull_subset_sequentialNull (by rintro _ ⟨θ, -, rfl⟩; infer_instance)
    (infinitePi_mem_iidNull (mem_image_of_mem _ hj))⟩

/-- The real mass of a point under `prodBernoulli θ`, for `θ` in the closed cube. -/
private lemma measureReal_prodBernoulli_singleton {θ : ι → ℝ}
    (hθ : θ ∈ univ.pi fun _ ↦ Icc 0 1) (x : ι → Bool) :
    (prodBernoulli θ).real {x} = ∏ i, if x i then θ i else 1 - θ i := by
  rw [Measure.real, prodBernoulli_singleton hθ,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ ↦ ?_)]
  have := hθ i (mem_univ i)
  split_ifs <;> linarith [this.1, this.2]

/-- Every point has a positive real mass under `prodBernoulli θ`, for `θ` in the open cube. -/
private lemma measureReal_prodBernoulli_singleton_pos {θ : ι → ℝ}
    (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) (x : ι → Bool) : 0 < (prodBernoulli θ).real {x} :=
  ENNReal.toReal_pos (prodBernoulli_singleton_ne_zero hθ x) (measure_ne_top _ _)

omit [Fintype ι] in
/-- The open cube is in the closed cube. -/
private lemma mem_pi_Icc_of_mem_pi_Ioo {θ : ι → ℝ} (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) :
    θ ∈ univ.pi fun _ ↦ Icc (0 : ℝ) 1 :=
  fun i _ ↦ Ioo_subset_Icc_self (hθ i trivial)

/-- **The logarithm of the plug-in intersection–union process** is the minimum of the sums of the
real log-likelihood ratios: all the masses are positive, the estimates and the projections being
in the open cube. -/
private lemma log_minPlugInLikelihoodRatio_eq [Fintype κ] [Nonempty κ]
    {lam : κ → (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) (n : ℕ) (ω : ℕ → ι → Bool) :
    ENNReal.log (minPlugInLikelihoodRatio ψhat lam n ω) =
      ((Finset.univ.inf' Finset.univ_nonempty fun j ↦ ∑ k ∈ Finset.range n,
        Real.log ((prodBernoulli (ψhat k ω)).real {ω k} /
          (prodBernoulli (lam j (ψhat k ω))).real {ω k}) : ℝ) : EReal) := by
  set S : κ → ℝ := fun j ↦ ∑ k ∈ Finset.range n, Real.log ((prodBernoulli (ψhat k ω)).real {ω k} /
    (prodBernoulli (lam j (ψhat k ω))).real {ω k})
  -- each product of ratios is the exponential of the sum of the logarithms of the real ratios
  have hprod (j : κ) :
      plugInLikelihoodRatio ψhat (lam j) n ω = ENNReal.ofReal (Real.exp (S j)) := by
    rw [plugInLikelihoodRatio_def, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have ha := measureReal_prodBernoulli_singleton_pos (hψhat01 k ω) (ω k)
    have hb := measureReal_prodBernoulli_singleton_pos (hlam01 j _ (hψhat01 k ω)) (ω k)
    rw [Real.exp_log (div_pos ha hb), ENNReal.ofReal_div_of_pos hb,
      ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty S
  have hM : minPlugInLikelihoodRatio ψhat lam n ω = ENNReal.ofReal (Real.exp (S j₀)) := by
    simp_rw [minPlugInLikelihoodRatio_def, hprod]
    refine le_antisymm (iInf_le _ j₀) (le_iInf fun j ↦ ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_))
    rw [← hj₀]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  rw [hM, ENNReal.log_ofReal]
  simp only [(Real.exp_pos (S j₀)).not_ge, ite_false, Real.log_exp]
  rw [hj₀]

/-- **The strong law for the log-likelihood ratio** of `prodBernoulli ψ` against `prodBernoulli η`,
for `η` in the open cube: almost surely under the i.i.d. law of `prodBernoulli ψ`, the sums over
`k < n` of the log-likelihood ratios, divided by `n`, tend to the relative entropy
`KL(prodBernoulli ψ ‖ prodBernoulli η)`. -/
private lemma ae_tendsto_sum_log_div (ψ : ι → ℝ) {η : ι → ℝ}
    (hη : η ∈ univ.pi fun _ ↦ Ioo 0 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, Real.log ((prodBernoulli ψ).real {ω k} /
          (prodBernoulli η).real {ω k})) / n) atTop
        (𝓝 (klDiv (prodBernoulli ψ) (prodBernoulli η)).toReal) := by
  have h := TauCeti.Probability.strong_law_ae_infinitePi (prodBernoulli ψ)
    (f := fun x ↦ Real.log ((prodBernoulli ψ).real {x} / (prodBernoulli η).real {x}))
    Integrable.of_finite
  rw [integral_log_measureReal_div_eq_toReal_klDiv (prodBernoulli_absolutelyContinuous ψ hη)] at h
  filter_upwards [h] with ω hω
  simpa only [smul_eq_mul, inv_mul_eq_div] using hω

/-- **A consistent estimate costs `o(n)`.** If the parameters `φ k`, in the open cube, tend to `ψ`
in the open cube, the sums over `k < n` of `log P_{φ k} {ω k} - log P_ψ {ω k}` are `o(n)`, on every
sequence `ω`: the masses of the finitely many points are continuous in the parameters. -/
private lemma tendsto_sum_log_sub_div {ψ : ι → ℝ} (hψ : ψ ∈ univ.pi fun _ ↦ Ioo 0 1)
    {φ : ℕ → ι → ℝ} (hφ01 : ∀ k, φ k ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hφ : Tendsto φ atTop (𝓝 ψ)) (ω : ℕ → ι → Bool) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, (Real.log ((prodBernoulli (φ k)).real {ω k}) -
      Real.log ((prodBernoulli ψ).real {ω k}))) / n) atTop (𝓝 0) := by
  classical
  set g : (ι → Bool) → (ι → ℝ) → ℝ := fun x θ ↦ Real.log (∏ i, if x i then θ i else 1 - θ i)
  have hmass (θ : ι → ℝ) (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) (x : ι → Bool) :
      Real.log ((prodBernoulli θ).real {x}) = g x θ := by
    rw [measureReal_prodBernoulli_singleton (mem_pi_Icc_of_mem_pi_Ioo hθ)]
  have hcont (x : ι → Bool) : Tendsto (fun k ↦ g x (φ k)) atTop (𝓝 (g x ψ)) := by
    have hc : Continuous fun θ : ι → ℝ ↦ ∏ i, if x i then θ i else 1 - θ i :=
      continuous_finsetProd _ fun i _ ↦ by split_ifs <;> fun_prop
    have hpos : 0 < ∏ i, if x i then ψ i else 1 - ψ i := by
      rw [← measureReal_prodBernoulli_singleton (mem_pi_Icc_of_mem_pi_Ioo hψ)]
      exact measureReal_prodBernoulli_singleton_pos hψ x
    exact (ContinuousAt.comp (g := Real.log)
      (f := fun θ : ι → ℝ ↦ ∏ i, if x i then θ i else 1 - θ i) (Real.continuousAt_log hpos.ne')
      hc.continuousAt).tendsto.comp hφ
  set w : ℕ → ℝ := fun k ↦ ∑ x, |g x (φ k) - g x ψ|
  have hw : Tendsto w atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) fun x _ ↦ ((hcont x).sub_const (g x ψ)).abs
  refine squeeze_zero_norm' ?_ hw.cesaro
  filter_upwards with n
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, div_eq_inv_mul]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [hmass _ (hφ01 k), hmass _ hψ]
  exact Finset.single_le_sum (f := fun x ↦ |g x (φ k) - g x ψ|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ (ω k))

omit [Fintype ι] in
/-- A positive lower bound on the coordinates of a point of the open cube and on their
complements. -/
private lemma exists_pos_forall_le_and_le_one_sub [Finite ι] {θ : ι → ℝ}
    (hθ : θ ∈ univ.pi fun _ ↦ Ioo 0 1) : ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ θ i ∧ a ≤ 1 - θ i := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i ↦ isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty fun i ↦ min (θ i) (1 - θ i), ?_, fun i ↦ ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro i _
    exact lt_min (hθ i trivial).1 (by linarith [(hθ i trivial).2])
  · have := Finset.inf'_le (fun i ↦ min (θ i) (1 - θ i)) (Finset.mem_univ i)
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩

/-- **The projections of parameters near `ψ` stay away from the faces of the cube.** For
projections `lam φ` in the open cube and `ψ` in the open cube, there is `δ > 0` such that `lam ψ`
and the projections `lam φ` of the parameters `φ` of the open cube near `ψ` have their coordinates
in `[δ, 1 - δ]`: by minimality, `KL(P_φ ‖ P_{lam φ}) ≤ KL(P_φ ‖ P_{lam ψ})`, which stays bounded
near `ψ`. -/
private lemma exists_forall_eventually_mem_Icc_lam {C : Set (ι → ℝ)} {lam : (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ C)
    (hmin : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) C (lam φ))
    {ψ : ι → ℝ} (hψ : ψ ∈ univ.pi fun _ ↦ Ioo 0 1) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, lam ψ i ∈ Icc δ (1 - δ)) ∧
      ∀ᶠ φ in 𝓝 ψ, φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1) →
        ∀ i, lam φ i ∈ Icc δ (1 - δ) := by
  set η := lam ψ with hη
  have hηC : η ∈ C := hlam ψ hψ
  have hη01 : η ∈ univ.pi fun _ ↦ Ioo 0 1 := hlam01 ψ hψ
  obtain ⟨a, ha0, ha⟩ := exists_pos_forall_le_and_le_one_sub hψ
  obtain ⟨b, hb0, hb⟩ := exists_pos_forall_le_and_le_one_sub hη01
  set B : ℝ := (klDiv (prodBernoulli ψ) (prodBernoulli η)).toReal + 1 with hB
  set δ₁ : ℝ := Real.exp (-((B + Real.log 2) / (a / 2))) with hδ₁
  refine ⟨min δ₁ b, lt_min (Real.exp_pos _) hb0,
    fun i ↦ ⟨min_le_of_right_le (hb i).1, by linarith [min_le_right δ₁ b, (hb i).2]⟩, ?_⟩
  have hN1 : ∀ᶠ φ in 𝓝 ψ, ∀ i, a / 2 < φ i ∧ a / 2 < 1 - φ i := by
    refine Filter.eventually_all.2 fun i ↦ ?_
    refine (((continuous_apply i).tendsto ψ).eventually (lt_mem_nhds (by linarith [(ha i).1]))).and
      ?_
    exact (((continuous_const.sub (continuous_apply i)).tendsto ψ).eventually
      (lt_mem_nhds (show a / 2 < 1 - ψ i by linarith [(ha i).2])))
  have hN2 : ∀ᶠ φ in 𝓝 ψ, klDiv (prodBernoulli φ) (prodBernoulli η) < ENNReal.ofReal B := by
    have hcont : Continuous fun φ : ι → ℝ ↦ ∑ i, klBer (φ i) (η i) :=
      continuous_finsetSum _ fun i _ ↦ (continuous_klBer_left (hη01 i trivial)).comp
        (continuous_apply i)
    have hlt : ∑ i, klBer (ψ i) (η i) < ENNReal.ofReal B := by
      rw [← klDiv_prodBernoulli, ← ENNReal.ofReal_toReal (klDiv_prodBernoulli_ne_top ψ hη01), hB]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    filter_upwards [(hcont.tendsto ψ).eventually (gt_mem_nhds hlt)] with φ hφ
    rwa [klDiv_prodBernoulli]
  filter_upwards [hN1, hN2] with φ h1 h2 hφ i
  have hθi := hlam01 φ hφ i trivial
  have hφi := hφ i trivial
  have hKL : klDiv (prodBernoulli φ) (prodBernoulli (lam φ)) < ENNReal.ofReal B :=
    ((hmin φ hφ) hηC).trans_lt h2
  rw [klDiv_prodBernoulli] at hKL
  have hi : klBer (φ i) (lam φ i) < ENNReal.ofReal B :=
    (Finset.single_le_sum (f := fun j ↦ klBer (φ j) (lam φ j)) (fun j _ ↦ zero_le)
      (Finset.mem_univ i)).trans_lt hKL
  rw [klBer_eq_ofReal_klBerReal (Ioo_subset_Icc_self hφi) (Ioo_subset_Icc_self hθi)
    (klBer_ne_top hθi), ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hi
  have hlow := mul_neg_log_le_klBerReal_add_log_two (Ioo_subset_Icc_self hφi) hθi
  have hlow' := mul_neg_log_le_klBerReal_add_log_two
    (p := 1 - φ i) (q := 1 - lam φ i) ⟨by linarith [hφi.2], by linarith [hφi.1]⟩
    ⟨by linarith [hθi.2], by linarith [hθi.1]⟩
  rw [klBerReal_one_sub] at hlow'
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 < (B + Real.log 2) / (a / 2) := by positivity
  -- `-log θ ≤ (B + log 2) / (a / 2)`, hence `θ ≥ δ₁`
  have key : ∀ p q : ℝ, a / 2 < p → q ∈ Ioo (0 : ℝ) 1 → p * -Real.log q ≤ B + Real.log 2 →
      δ₁ ≤ q := by
    intro p q hp hq h
    have hq0 : 0 ≤ -Real.log q := neg_nonneg.2 (Real.log_nonpos hq.1.le hq.2.le)
    have h' : -Real.log q ≤ (B + Real.log 2) / (a / 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [hδ₁, ← Real.exp_log hq.1]
    exact Real.exp_le_exp.2 (by linarith)
  refine ⟨(min_le_left _ _).trans (key (φ i) (lam φ i) (h1 i).1 hθi (by linarith)), ?_⟩
  have := key (1 - φ i) (1 - lam φ i) (h1 i).2 ⟨by linarith [hθi.2], by linarith [hθi.1]⟩
    (by linarith)
  linarith [min_le_left δ₁ b]

/-- **The plug-in projections lose nothing to first order.** For predictable estimates `ψhat k`
tending to `ψ` almost surely under the i.i.d. law of `prodBernoulli ψ`, the sums over `k < n` of
`log P_{lam ψ} {ω k} - log P_{lam (ψhat k)} {ω k}` are eventually at least `-ε n` for every
`ε > 0`, almost surely: given the past, each term has the nonnegative mean
`KL(P_ψ ‖ P_{lam (ψhat k)}) - KL(P_ψ ‖ P_{lam ψ})`, and the terms are eventually bounded. -/
private lemma ae_forall_eventually_neg_mul_le_sum_log_sub {C : Set (ι → ℝ)}
    {lam : (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam φ ∈ C)
    (hmin : ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) C (lam φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) {ψ : ι → ℝ}
    (hψ : ψ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hcons : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun k ↦ ψhat k ω) atTop (𝓝 ψ)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, -ε * n ≤ ∑ k ∈ Finset.range n,
        (Real.log ((prodBernoulli (lam ψ)).real {ω k}) -
          Real.log ((prodBernoulli (lam (ψhat k ω))).real {ω k})) := by
  classical
  set P := prodBernoulli ψ with hP
  set η := lam ψ with hη
  have hηC : η ∈ C := hlam ψ hψ
  have hη01 : η ∈ univ.pi fun _ ↦ Ioo 0 1 := hlam01 ψ hψ
  obtain ⟨δ, hδ0, hηδ, hev⟩ := exists_forall_eventually_mem_Icc_lam hlam01 hlam hmin hψ
  -- the projection, replaced by `η` when it leaves the cube `[δ, 1 - δ] ^ ι`
  set good : (ι → ℝ) → Prop := fun θ ↦ ∀ i, θ i ∈ Icc δ (1 - δ)
  set θ' : (ι → ℝ) → ι → ℝ := fun φ ↦ if good (lam φ) then lam φ else η with hθ'
  have hθ'C (φ : ι → ℝ) (hφ : φ ∈ univ.pi fun _ ↦ Ioo 0 1) : θ' φ ∈ C := by
    simp only [hθ']
    split_ifs
    exacts [hlam φ hφ, hηC]
  have hθ'01 (φ : ι → ℝ) (hφ : φ ∈ univ.pi fun _ ↦ Ioo 0 1) :
      θ' φ ∈ univ.pi fun _ ↦ Ioo 0 1 := by
    simp only [hθ']
    split_ifs
    exacts [hlam01 φ hφ, hη01]
  have hθ'δ (φ : ι → ℝ) : good (θ' φ) := by
    simp only [hθ']
    split_ifs with h
    exacts [h, hηδ]
  -- the masses of the points under a law of the cube `[δ, 1 - δ] ^ ι`
  have hlogmass (θ : ι → ℝ) (hθ : good θ) (x : ι → Bool) :
      (Fintype.card ι : ℝ) * Real.log δ ≤ Real.log ((prodBernoulli θ).real {x}) ∧
        Real.log ((prodBernoulli θ).real {x}) ≤ 0 := by
    have hθ01 : θ ∈ univ.pi fun _ ↦ Icc (0 : ℝ) 1 := fun i _ ↦
      ⟨hδ0.le.trans (hθ i).1, (hθ i).2.trans (by linarith)⟩
    have hf (i : ι) : δ ≤ (if x i then θ i else 1 - θ i) ∧ (if x i then θ i else 1 - θ i) ≤ 1 := by
      split_ifs <;> constructor <;> linarith [(hθ i).1, (hθ i).2]
    rw [measureReal_prodBernoulli_singleton hθ01]
    have hlow : δ ^ Fintype.card ι ≤ ∏ i, if x i then θ i else 1 - θ i := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ hδ0.le) fun i _ ↦ (hf i).1
    have hup : ∏ i, (if x i then θ i else 1 - θ i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ ↦ hδ0.le.trans (hf i).1) fun i _ ↦ (hf i).2
    refine ⟨?_, Real.log_nonpos (Finset.prod_nonneg fun i _ ↦ hδ0.le.trans (hf i).1) hup⟩
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hlow
  have hcardδ : 0 ≤ (Fintype.card ι : ℝ) * -Real.log δ := by
    rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
    · simp
    · exact mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.2 (Real.log_nonpos hδ0.le
        (by linarith [(hηδ i).1, (hηδ i).2])))
  set L : ℝ := (Fintype.card ι : ℝ) * -Real.log δ + 1
  have hL1 : 1 ≤ L := by linarith
  set D' : (ι → ℝ) → (ι → Bool) → ℝ := fun φ x ↦ Real.log ((prodBernoulli η).real {x}) -
    Real.log ((prodBernoulli (θ' φ)).real {x}) with hD'
  have hD'L (φ : ι → ℝ) (x : ι → Bool) : |D' φ x| ≤ L := by
    have h1 := hlogmass η hηδ x
    have h2 := hlogmass (θ' φ) (hθ'δ φ) x
    rw [abs_le]
    constructor <;> simp only [hD'] <;> nlinarith
  -- given the past, the terms have a nonnegative mean, by the minimality of `η`
  have hsum1 : ∑ y, P.real {y} = 1 := by simp
  have hmean (φ : ι → ℝ) (hφ : φ ∈ univ.pi fun _ ↦ Ioo 0 1) :
      0 ≤ ∑ x, P.real {x} * D' φ x := by
    have hθ01 := hθ'01 φ hφ
    have hle : (klDiv P (prodBernoulli η)).toReal ≤ (klDiv P (prodBernoulli (θ' φ))).toReal :=
      ENNReal.toReal_mono (klDiv_prodBernoulli_ne_top ψ hθ01) ((hmin ψ hψ) (hθ'C φ hφ))
    have hsplit : ∑ x, P.real {x} * D' φ x =
        ∫ x, Real.log (P.real {x} / (prodBernoulli (θ' φ)).real {x}) ∂P -
          ∫ x, Real.log (P.real {x} / (prodBernoulli η).real {x}) ∂P := by
      rw [← integral_sub Integrable.of_finite Integrable.of_finite,
        integral_fintype Integrable.of_finite]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [smul_eq_mul, Real.log_div (measureReal_prodBernoulli_singleton_pos hψ x).ne'
          (measureReal_prodBernoulli_singleton_pos hθ01 x).ne',
        Real.log_div (measureReal_prodBernoulli_singleton_pos hψ x).ne'
          (measureReal_prodBernoulli_singleton_pos hη01 x).ne']
      simp only [hD']
      ring
    rw [hsplit, integral_log_measureReal_div_eq_toReal_klDiv
        (prodBernoulli_absolutelyContinuous ψ hθ01),
      integral_log_measureReal_div_eq_toReal_klDiv (prodBernoulli_absolutelyContinuous ψ hη01)]
    linarith
  -- the one-step bound of the exponential process
  have hg1 (s : ℝ) (hs : 0 < s) (hsL : s * L ≤ 1) (φ : ι → ℝ)
      (hφ : φ ∈ univ.pi fun _ ↦ Ioo 0 1) :
      ∫⁻ y, ENNReal.ofReal (Real.exp (-s * D' φ y - s ^ 2 * L ^ 2)) ∂P ≤ 1 := by
    rw [lintegral_fintype]
    have hterm (y : ι → Bool) : ENNReal.ofReal (Real.exp (-s * D' φ y - s ^ 2 * L ^ 2)) * P {y} =
        ENNReal.ofReal (Real.exp (-s * D' φ y - s ^ 2 * L ^ 2) * P.real {y}) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal (measure_ne_top _ _)]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ by positivity), ENNReal.ofReal_le_one]
    have hexp (y : ι → Bool) : Real.exp (-s * D' φ y) ≤ 1 - s * D' φ y + s ^ 2 * L ^ 2 := by
      have hD := hD'L φ y
      have hab : |-s * D' φ y| ≤ 1 := by
        rw [abs_mul, abs_neg, abs_of_pos hs]
        nlinarith [abs_nonneg (D' φ y)]
      have h := Real.abs_exp_sub_one_sub_id_le hab
      have hD2 : D' φ y ^ 2 ≤ L ^ 2 := sq_le_sq' (abs_le.1 hD).1 (abs_le.1 hD).2
      have hsq : (-s * D' φ y) ^ 2 ≤ s ^ 2 * L ^ 2 := by
        calc (-s * D' φ y) ^ 2 = s ^ 2 * D' φ y ^ 2 := by ring
          _ ≤ s ^ 2 * L ^ 2 := by gcongr
      linarith [(abs_le.1 h).2]
    calc ∑ y, Real.exp (-s * D' φ y - s ^ 2 * L ^ 2) * P.real {y}
        = Real.exp (-(s ^ 2 * L ^ 2)) * ∑ y, P.real {y} * Real.exp (-s * D' φ y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [sub_eq_add_neg, Real.exp_add]
          ring
      _ ≤ Real.exp (-(s ^ 2 * L ^ 2)) * ∑ y, P.real {y} * (1 - s * D' φ y + s ^ 2 * L ^ 2) := by
          gcongr with y
          exact hexp y
      _ = Real.exp (-(s ^ 2 * L ^ 2)) * (1 + s ^ 2 * L ^ 2 - s * ∑ y, P.real {y} * D' φ y) := by
          congr 1
          have (y : ι → Bool) : P.real {y} * (1 - s * D' φ y + s ^ 2 * L ^ 2) =
              P.real {y} * (1 + s ^ 2 * L ^ 2) - s * (P.real {y} * D' φ y) := by ring
          simp_rw [this]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum1, one_mul]
      _ ≤ Real.exp (-(s ^ 2 * L ^ 2)) * (1 + s ^ 2 * L ^ 2) := by
          gcongr
          nlinarith [hmean φ hφ]
      _ ≤ 1 := by
          calc Real.exp (-(s ^ 2 * L ^ 2)) * (1 + s ^ 2 * L ^ 2)
              ≤ Real.exp (-(s ^ 2 * L ^ 2)) * Real.exp (s ^ 2 * L ^ 2) := by
                gcongr
                linarith [Real.add_one_le_exp (s ^ 2 * L ^ 2)]
            _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- the exponential test supermartingales, for `s m = 1 / ((m + 1) L)`
  set sm : ℕ → ℝ := fun m ↦ 1 / ((m + 1) * L) with hsm
  have hsm0 (m : ℕ) : 0 < sm m := by
    simp only [hsm]
    positivity
  have hsmL (m : ℕ) : sm m * L ≤ 1 := by
    simp only [hsm]
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set g : ℕ → ℕ → (ℕ → ι → Bool) → (ι → Bool) → ℝ≥0∞ := fun m k ω y ↦
    ENNReal.ofReal (Real.exp (-sm m * D' (ψhat k ω) y - sm m ^ 2 * L ^ 2)) with hg
  have hW (m : ℕ) : IsTestSupermartingale (fun n ω ↦ ∏ k ∈ Finset.range n, g m k ω (ω k))
      Filtration.piLT {Measure.infinitePi fun _ : ℕ ↦ P} := by
    refine (isTestSupermartingale_prod_sequentialNull (S₁ := fun _ _ ↦ {P}) (r := g m)
      (fun k ↦ Filtration.measurable_piLT_apply k.lt_succ_self) (fun k ↦ ?_) fun k ω ↦
        ⟨measurable_of_countable _, fun ν hν ↦ ?_⟩).anti_set (singleton_subset_iff.2
          (infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦ rfl))
    · refine @measurable_from_prod_countable_left _ _ _ (Filtration.piLT k) _ _ _ _ _
        fun y ↦ measurable_piLT_of_dependsOn_of_finite fun x x' hxx' ↦ ?_
      simp only [Function.uncurry_apply_pair, hg]
      rw [(hψhat k).dependsOn_of_piLT hxx']
    · rw [mem_singleton_iff.1 hν]
      exact hg1 (sm m) (hsm0 m) (hsmL m) _ (hψhat01 k ω)
  -- Ville's inequality: almost surely, each of them is bounded
  have hbdd : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ P), ∀ m, ∃ N : ℕ, ∀ n,
      ∏ k ∈ Finset.range n, g m k ω (ω k) < N := by
    rw [ae_all_iff]
    intro m
    have hE := (hW m).isEProcess (by rintro _ rfl; infer_instance)
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun N ↦ ?_) zero_le
    refine (measure_mono fun ω hω ↦ ?_).trans
      ((hE.isLevelStoppingTime_hittingAfter (N : ℝ≥0∞)⁻¹).measure_lt_top_le _ rfl)
    simp only [mem_ofPred_eq, not_exists, not_forall, not_lt] at hω
    obtain ⟨n, hn⟩ := hω N
    simp only [mem_ofPred_eq, inv_inv]
    exact lt_of_le_of_lt (hittingAfter_le_of_mem (Nat.zero_le n) (mem_Ici.2 hn))
      (WithTop.coe_lt_top n)
  filter_upwards [hcons, hbdd] with ω hc hb ε hε
  -- eventually the projection is in the cube, and is not replaced
  have hgoodk : ∀ᶠ k in atTop, θ' (ψhat k ω) = lam (ψhat k ω) := by
    filter_upwards [hc.eventually hev] with k hk
    simp only [hθ']
    split_ifs with h
    · rfl
    · exact absurd (hk (hψhat01 k ω)) h
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hgoodk
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * L / ε)
  obtain ⟨N, hN⟩ := hb m
  set s := sm m with hs
  have hs0 := hsm0 m
  have hsL2 : s * L ^ 2 ≤ ε / 2 := by
    have hm1 : 2 * L < ε * (m + 1) := by
      have := (div_lt_iff₀ hε).1 hm
      nlinarith
    have : s * L ^ 2 = L / (m + 1) := by
      simp only [hs, hsm]
      field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  set Dk : ℕ → ℝ := fun k ↦ Real.log ((prodBernoulli (lam ψ)).real {ω k}) -
    Real.log ((prodBernoulli (lam (ψhat k ω))).real {ω k}) with hDkdef
  have hDk (k : ℕ) (hk : k₀ ≤ k) : Dk k - D' (ψhat k ω) (ω k) = 0 := by
    simp only [hDkdef, hD', hk₀ k hk, hη]
    ring
  set R₀ : ℝ := ∑ k ∈ Finset.range k₀, |Dk k - D' (ψhat k ω) (ω k)|
  have hdiff (n : ℕ) : -R₀ ≤ ∑ k ∈ Finset.range n, (Dk k - D' (ψhat k ω) (ω k)) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (min_le_left n k₀)) fun k hk hk' ↦ hDk k
      (by simp only [Finset.mem_range, lt_min_iff, not_and, not_lt] at hk hk'; exact hk' hk)]
    calc -R₀ ≤ -∑ k ∈ Finset.range (min n k₀), |Dk k - D' (ψhat k ω) (ω k)| :=
          neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (min_le_right _ _)) fun _ _ _ ↦ abs_nonneg _)
      _ ≤ _ := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_le_sum fun k _ ↦ neg_abs_le _
  -- the truncated sum, from the bound on the exponential process
  have hlower (n : ℕ) : -(Real.log N) / s - n * (s * L ^ 2) ≤
      ∑ k ∈ Finset.range n, D' (ψhat k ω) (ω k) := by
    have h := hN n
    have hW_eq : ∏ k ∈ Finset.range n, g m k ω (ω k) = ENNReal.ofReal (Real.exp
        (∑ k ∈ Finset.range n, (-s * D' (ψhat k ω) (ω k) - s ^ 2 * L ^ 2))) := by
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
    rw [hW_eq] at h
    have hN0 : (0 : ℝ) < N := by
      have h0 : (0 : ℝ≥0∞) < N := lt_of_le_of_lt zero_le h
      exact_mod_cast h0
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff hN0] at h
    have h' := (Real.lt_log_iff_exp_lt hN0).2 h
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum] at h'
    have : -(Real.log N) / s ≤ ∑ k ∈ Finset.range n, D' (ψhat k ω) (ω k) + n * (s * L ^ 2) := by
      rw [div_le_iff₀ hs0]
      nlinarith
    linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * (Real.log N / s + R₀) / ε ≤ n₀ := exists_nat_ge _
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hn' : 2 * (Real.log N / s + R₀) ≤ ε * n :=
    (div_le_iff₀' hε).1 (hn₀.trans (by exact_mod_cast hn))
  have hsplit : ∑ k ∈ Finset.range n, Dk k = ∑ k ∈ Finset.range n, D' (ψhat k ω) (ω k) +
      ∑ k ∈ Finset.range n, (Dk k - D' (ψhat k ω) (ω k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hnL := mul_le_mul_of_nonneg_left hsL2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h1 := hlower n
  have h2 := hdiff n
  have hneg : -(Real.log N) / s = -(Real.log N / s) := by ring
  change -ε * n ≤ ∑ k ∈ Finset.range n, Dk k
  rw [hsplit]
  nlinarith

/-- **With a consistent estimate, the plug-in intersection–union process grows at the rate
`KL_inf`, almost surely** [EVR26, Note 32, Statement 4]. Under the hypotheses of
`isEProcess_minPlugInLikelihoodRatio`, with finitely many pieces, let `ψ` be in the open cube and
the estimates `ψhat k` tend to `ψ` almost surely under the i.i.d. law of `prodBernoulli ψ`.
Almost surely, `(1/n) log` of the minimum of the plug-in likelihood ratios tends to the smallest
relative entropy `KL_inf` from `prodBernoulli ψ` to the laws of the coins with parameters in the
union of the `C j`. -/
theorem ae_tendsto_log_minPlugInLikelihoodRatio_div [Finite κ] {C : κ → Set (ι → ℝ)}
    (hC : ∀ j, Convex ℝ (C j)) (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1)
    {lam : κ → (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ C j)
    (hmin : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) (C j) (lam j φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) {ψ : ι → ℝ}
    (hψ : ψ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hcons : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun k ↦ ψhat k ω) atTop (𝓝 ψ)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun n : ℕ ↦ ENNReal.log (minPlugInLikelihoodRatio ψhat lam n ω) / (n : EReal))
        atTop (𝓝 (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j))) := by
  classical
  have := Fintype.ofFinite κ
  set K := klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j) with hK
  have hS : ∀ P ∈ prodBernoulli '' ⋃ j, C j, IsProbabilityMeasure P := by
    rintro _ ⟨θ, -, rfl⟩
    infer_instance
  -- the upper bound of every e-process, at the bipolar rate, which is `KL_inf`
  have hup := IsEProcess.ae_limsup_log_div_le_bipolarRate (prodBernoulli ψ) hS
    ((isEProcess_minPlugInLikelihoodRatio hC hC01 hlam01 hlam hmin hψhat hψhat01).anti_set
      iidNull_prodBernoulli_iUnion_subset)
  rw [bipolarRate_prodBernoulli_iUnion_eq_klInf hC hC01 ψ (fun j ↦ hlam01 j ψ hψ)
    (fun j ↦ hlam j ψ hψ) fun j ↦ hmin j ψ hψ] at hup
  -- the lower bound
  have hlow : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      K ≤ liminf (fun n : ℕ ↦ ENNReal.log (minPlugInLikelihoodRatio ψhat lam n ω) / (n : EReal))
        atTop := by
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · refine .of_forall fun ω ↦ ?_
      have hnull : prodBernoulli '' ⋃ j, C j = ∅ := by simp
      rw [hK, hnull, klInf_empty]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [minPlugInLikelihoodRatio_def, iInf_of_empty, ENNReal.log_top,
        EReal.top_div_of_pos_ne_top (by exact_mod_cast hn) (EReal.natCast_ne_top n)]
    -- `KL_inf` is at most the relative entropy to each oracle projection `lam j ψ`
    set K₀ := Finset.univ.inf' Finset.univ_nonempty fun j ↦
      (klDiv (prodBernoulli ψ) (prodBernoulli (lam j ψ))).toReal
    have hKK₀ : K ≤ K₀ := by
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun j ↦
        (klDiv (prodBernoulli ψ) (prodBernoulli (lam j ψ))).toReal
      rw [show K₀ = _ from hj₀,
        EReal.coe_ennreal_toReal (klDiv_prodBernoulli_ne_top ψ (hlam01 j₀ ψ hψ)),
        ← klIntegral_eq_klDiv (by simp)]
      exact klInf_le_klIntegral (mem_image_of_mem _ (mem_iUnion.2 ⟨j₀, hlam j₀ ψ hψ⟩))
    have hD := fun j ↦ ae_forall_eventually_neg_mul_le_sum_log_sub (hlam01 j) (hlam j) (hmin j)
      hψhat hψhat01 hψ hcons
    filter_upwards [ae_all_iff.2 fun j ↦ ae_tendsto_sum_log_div ψ (hlam01 j ψ hψ), hcons,
      ae_all_iff.2 hD] with ω hO hc hDω
    have hV := tendsto_sum_log_sub_div hψ (fun k ↦ hψhat01 k ω) hc ω
    refine hKK₀.trans (le_of_forall_lt_imp_le_of_dense fun c hc' ↦ ?_)
    induction c using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hc' (not_lt.2 le_top)
    | coe r =>
    have hr : r < K₀ := EReal.coe_lt_coe_iff.1 hc'
    set ε := (K₀ - r) / 3 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop 1,
      Filter.eventually_all.2 fun j ↦ (hO j).eventually (eventually_ge_nhds (by linarith :
        (klDiv (prodBernoulli ψ) (prodBernoulli (lam j ψ))).toReal - ε <
          (klDiv (prodBernoulli ψ) (prodBernoulli (lam j ψ))).toReal)),
      hV.eventually (eventually_ge_nhds (by linarith : -ε < 0)),
      Filter.eventually_all.2 fun j ↦ hDω j ε hε0] with n hn hOn hVn hDn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [log_minPlugInLikelihoodRatio_eq hlam01 hψhat01, ← EReal.coe_natCast, ← EReal.coe_div,
      EReal.coe_le_coe_iff, le_div_iff₀ hn0, Finset.le_inf'_iff]
    intro j _
    -- the plug-in sum is the oracle sum, the estimation term and the projection term
    have hsplit : ∑ k ∈ Finset.range n, Real.log ((prodBernoulli (ψhat k ω)).real {ω k} /
        (prodBernoulli (lam j (ψhat k ω))).real {ω k}) =
        ∑ k ∈ Finset.range n, Real.log ((prodBernoulli ψ).real {ω k} /
          (prodBernoulli (lam j ψ)).real {ω k}) +
        ∑ k ∈ Finset.range n, (Real.log ((prodBernoulli (ψhat k ω)).real {ω k}) -
          Real.log ((prodBernoulli ψ).real {ω k})) +
        ∑ k ∈ Finset.range n, (Real.log ((prodBernoulli (lam j ψ)).real {ω k}) -
          Real.log ((prodBernoulli (lam j (ψhat k ω))).real {ω k})) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Real.log_div (measureReal_prodBernoulli_singleton_pos (hψhat01 k ω) _).ne'
          (measureReal_prodBernoulli_singleton_pos (hlam01 j _ (hψhat01 k ω)) _).ne',
        Real.log_div (measureReal_prodBernoulli_singleton_pos hψ _).ne'
          (measureReal_prodBernoulli_singleton_pos (hlam01 j ψ hψ) _).ne']
      ring
    have hOj : n * (K₀ - ε) ≤ ∑ k ∈ Finset.range n, Real.log ((prodBernoulli ψ).real {ω k} /
        (prodBernoulli (lam j ψ)).real {ω k}) := by
      have h1 := (le_div_iff₀ hn0).1 (hOn j)
      have h2 : K₀ ≤ (klDiv (prodBernoulli ψ) (prodBernoulli (lam j ψ))).toReal :=
        Finset.inf'_le _ (Finset.mem_univ j)
      nlinarith
    have hVj := (le_div_iff₀ hn0).1 hVn
    have hDj := hDn j
    rw [hsplit]
    nlinarith
  filter_upwards [hup, hlow] with ω h1 h2
  exact tendsto_of_le_liminf_of_limsup_le h2 h1

/-- **With a consistent estimate, the plug-in intersection–union test makes
`log (1/α) / KL_inf` observations to first order, almost surely** [EVR26, Note 32, Statement 4].
Under the hypotheses of `ae_tendsto_log_minPlugInLikelihoodRatio_div`, almost surely, the first
time `τ α` at which the minimum of the plug-in likelihood ratios reaches `α⁻¹` satisfies
`τ α / log (1/α) → 1 / KL_inf` as `α → 0`, in `ℝ≥0∞`. When `KL_inf = 0`, the limit is `⊤`. The
lower bound holds for every family of nested sequential tests of level `α`
(`ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div_log`), and the upper bound follows
from the growth of the process (`ProbabilityTheory.limsup_toENNReal_hittingAfter_div_log_le`). -/
theorem ae_tendsto_hittingAfter_minPlugInLikelihoodRatio_div_log [Finite κ]
    {C : κ → Set (ι → ℝ)} (hC : ∀ j, Convex ℝ (C j)) (hC01 : ∀ j, C j ⊆ univ.pi fun _ ↦ Icc 0 1)
    {lam : κ → (ι → ℝ) → ι → ℝ}
    (hlam01 : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hlam : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1), lam j φ ∈ C j)
    (hmin : ∀ j, ∀ φ ∈ univ.pi (fun _ : ι ↦ Ioo (0 : ℝ) 1),
      IsMinOn (fun θ ↦ klDiv (prodBernoulli φ) (prodBernoulli θ)) (C j) (lam j φ))
    (hψhat : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ι → Bool)) ψhat)
    (hψhat01 : ∀ k ω, ψhat k ω ∈ univ.pi fun _ ↦ Ioo 0 1) {ψ : ι → ℝ}
    (hψ : ψ ∈ univ.pi fun _ ↦ Ioo 0 1)
    (hcons : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun k ↦ ψhat k ω) atTop (𝓝 ψ)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ψ),
      Tendsto (fun α : ℝ≥0∞ ↦
          ENat.toENNReal (hittingAfter (minPlugInLikelihoodRatio ψhat lam) (Ici α⁻¹) 0 ω) /
            (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
        (𝓝 (klInf (prodBernoulli ψ) (prodBernoulli '' ⋃ j, C j)).toENNReal⁻¹) := by
  have hS : ∀ P ∈ prodBernoulli '' ⋃ j, C j, IsProbabilityMeasure P := by
    rintro _ ⟨θ, -, rfl⟩
    infer_instance
  have hlow := ae_inv_toENNReal_bipolarRate_le_liminf_div_log (prodBernoulli ψ) hS
    (τ := fun α ↦ hittingAfter (minPlugInLikelihoodRatio ψhat lam) (Ici α⁻¹) 0) one_pos
    (fun α _ ↦ (isLevelStoppingTime_hittingAfter_minPlugInLikelihoodRatio hC hC01 hlam01 hlam
      hmin hψhat hψhat01 α).anti_set iidNull_prodBernoulli_iUnion_subset)
    (fun ω α _ α' _ hαα' ↦ hittingAfter_anti _ _
      (Ici_subset_Ici.2 (ENNReal.inv_le_inv.2 hαα')) ω)
  rw [bipolarRate_prodBernoulli_iUnion_eq_klInf hC hC01 ψ (fun j ↦ hlam01 j ψ hψ)
    (fun j ↦ hlam j ψ hψ) fun j ↦ hmin j ψ hψ] at hlow
  filter_upwards [ae_tendsto_log_minPlugInLikelihoodRatio_div hC hC01 hlam01 hlam hmin hψhat
    hψhat01 hψ hcons, hlow] with ω h1 h2
  exact tendsto_of_le_liminf_of_limsup_le h2
    (limsup_toENNReal_hittingAfter_div_log_le h1.liminf_eq.ge)

end ProbabilityTheory
