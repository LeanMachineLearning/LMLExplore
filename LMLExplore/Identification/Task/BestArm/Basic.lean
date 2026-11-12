/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.Classical
public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.TopTwo.Basic
public import LMLExplore.Bandits.Instances
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian
public import LMLExplore.Order.Basic
public import LMLExplore.Order.CompleteLattice.Basic
public import LMLExplore.Algebra.Order.Field.Basic

/-!
# The alternatives of best arm identification and the cost of the alternatives

For best arm identification on vectors of means (`baiTask ν id`), the alternatives to an arm `a`
are the vectors of means with a unique best arm `b ≠ a` (`mem_alt_baiTask_iff`, for any mean
functional). This set is not closed: its limits include the vectors where `a` ties with another
best arm, which have no correct answer. The cost of the alternatives
`D(μ, w, ¬a) = inf_{λ ∈ ¬a} ∑ b, w b KL(ν_b(μ), ν_b(λ))` is an infimum over this set, and the
analysis of best arm identification of Garivier and Kaufmann (2016) computes it on the closed set
`{λ | ∃ b ≠ a, λ a ≤ λ b}` of the vectors whose largest mean is attained at an arm `b ≠ a`, one
arm `b` at a time.

The admissible models of an identification problem are the vectors whose means lie in the mean
sets of the arm families (the means of an exponential family form an open interval), that is
`(baiTask ν id).restrict S` for an open set `S` of vectors of means. Within `S`, the closure of the
alternatives to `a` is the closed set above, and when the transportation cost is continuous there,
the cost of the alternatives is the infimum of the cost over it. Dually, the closure within `S` of
the answer set of `a`, the vectors with unique best arm `a`, is the set of the vectors of `S` whose
largest mean is attained at `a`, so that the closures of the answer sets cover `S`. The openness of
the answer sets and this covering are two of the conditions of [D23, Assumption 1] on the answer
sets under which the static proportions algorithms of fixed-budget identification have an explicit
error exponent.
These answer-set lemmas are adapted from the formalization Degenne2023Existence
(`github.com/RemyDegenne/Degenne2023Existence`, file
`Degenne2023Existence/ForLMLExplore/Identification/Task/BestArm.lean`, commit
`b34f7d32c926876cb38dfd51eba1474d44940bb1`, by Rémy Degenne, Apache 2.0) of [D23].

When the arms belong to an exponential family with divergence `d` and `a` is a best arm of `μ`,
the infimum for the arm `b` is the cost of moving the means of `a` and `b` to their mean weighted
by the allocation (attained there when `w a + w b > 0`), which gives the closed form of the cost of
the alternatives used to compute the optimal allocations of best arm identification
[GK16, Lemma 3]. With two arms `a` and `b`, the game is solved by the mean `z` between `μ b` and
`μ a` at the same divergence from both: `D(μ, ¬a) = d(μ a, z) = d(μ b, z)` [KCG16, Section 3].
This closed form is continuous in the model and the allocation, so that, at every vector of means
with a unique best arm, the value of the answer and the characteristic time are continuous, and the
optimal allocations upper hemicontinuous [DK19, Lemmas 28–29]
(`LMLExplore/Identification/Task/Continuity.lean`).

At a vector of means `μ` of the family with unique best arm `a`, the optimal allocation is unique
[GK16, Theorem 5]: there is a single allocation `w*(μ, ¬a)` maximizing `D(μ, w, ¬a)`. It gives a
positive proportion to every arm [GK16, Proposition 6], and the costs
`w a d(μ a, m_b) + w b d(μ b, m_b)` of all the pairs `(a, b)`, `b ≠ a`, are equal at it
[GK16, Lemma 4]. Together with the upper hemicontinuity of the optimal
allocations, this makes every selection of the optimal allocations continuous at `μ`
[GK16, Proposition 6], as the analysis of Track-and-Stop requires. With at least two arms, the
optimal allocation is characterized by these equal costs and the scalar equation
`∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1` for the weighted means
`m_b = (w a μ a + w b μ b) / (w a + w b)` [GK16, Theorem 5]. This characterization is adapted from
the formalization Garivier2016Optimal (`github.com/RemyDegenne/Garivier2016Optimal`, file
`Garivier2016Optimal/ForLMLExplore/Identification/Task/BestArmScalar.lean`, commit
`25fa4a8c0924ffe015f41f22aff90acc9a270076`, by Rémy Degenne, Apache 2.0) of [GK16].

For Gaussian arms with a common variance `σ2`, the divergence is `d(x, y) = (x - y)² / (2 σ2)`, so
that `D(μ, w, ¬a) = min_{b ≠ a} (w a w b / (w a + w b)) (μ a - μ b)² / (2 σ2)`, and two arms with
`μ b < μ a` have characteristic time `T*(μ) = 8 σ2 / (μ a - μ b)²` with the unique optimal
allocation `(1/2, 1/2)`. With more arms and a unique best arm `a`, the characteristic time is
within a factor `2` of the complexity `H(μ) = ∑ c, 2 σ2 / Δ_c²`, where `Δ_b = μ a - μ b` for
`b ≠ a` and `Δ_a = min_{b ≠ a} Δ_b`: `H(μ) ≤ T*(μ) ≤ 2 H(μ)` [GK16, Section 2.2].

## Main statements

* `LMLExplore.Identification.mem_alt_baiTask_iff`: the alternatives to `a` are the vectors with a
  unique best arm `b ≠ a`.
* `LMLExplore.Identification.mem_answerSet_baiTask_iff`,
  `LMLExplore.Identification.isOpen_answerSet_baiTask`: the vectors of means for which `a` is
  correct, those with unique best arm `a`, form an open set;
  `LMLExplore.Identification.isOpen_answerSet_baiTask_restrict` is the same within an open set `S`
  of vectors of means.
* `LMLExplore.Identification.closure_alt_baiTask_restrict_inter`: for `S` open, the closure of the
  alternatives to `a` within `S` is `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`;
  `LMLExplore.Identification.closure_alt_baiTask` is the case `S = univ`.
* `LMLExplore.Identification.closure_answerSet_baiTask_restrict_inter`: for `S` open, the closure
  of the answer set of `a` within `S` is `{λ | ∀ b, λ b ≤ λ a} ∩ S`;
  `LMLExplore.Identification.closure_answerSet_baiTask` is the case `S = univ`, and
  `LMLExplore.Identification.subset_iUnion_closure_answerSet_baiTask_restrict` states that the
  closures of the answer sets cover `S`.
* `LMLExplore.Identification.charTime_baiTask_eq_inv_answerValue`,
  `LMLExplore.Identification.charTime_baiTask_restrict_eq_inv_answerValue`: if `a` is the unique
  best arm of `θ`, then `T*(θ) = D(θ, ¬a)⁻¹`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf`: for `S` open and a transportation
  cost continuous on `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`,
  `D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`: for arms in an
  exponential family with divergence `d`, a best arm `a` of `μ` and a nonnegative allocation `w`,
  `D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` on the vectors of means of the
  family, with `m_b = (w a μ a + w b μ b) / (w a + w b)` [GK16, Lemma 3];
  `LMLExplore.Identification.altCost_baiTask_restrict_eq_inf` is the same closed form as a
  `Finset.inf`.
* `LMLExplore.Identification.continuousOn_altCost_baiTask_restrict`: for arms in an exponential
  family, `(μ, w) ↦ D(μ, w, ¬a)` is continuous on the vectors of means of the family with best arm
  `a` and the nonnegative allocations;
  `LMLExplore.Identification.continuousOn_altCost_baiTask_restrict_left` is the continuity in the
  allocation alone at a fixed vector of means, and
  `LMLExplore.Identification.continuousWithinAt_altCost_baiTask_restrict` the continuity within
  `univ ×ˢ simplex α` at a vector of means with unique best arm `a`.
* `LMLExplore.Identification.continuousAt_answerValue_baiTask_restrict`,
  `LMLExplore.Identification.upperHemicontinuousAt_optAlloc_baiTask_restrict`,
  `LMLExplore.Identification.continuousAt_charTime_baiTask_restrict`: for arms in an exponential
  family, at a vector of means with unique best arm `a`, `D(·, ¬a)` and `T*` are continuous and the
  optimal allocations `w*(·, ¬a)` are upper hemicontinuous [DK19, Lemmas 28–29].
* `LMLExplore.Identification.answerValue_baiTask_restrict_pos`: for arms in an exponential family,
  the value `D(μ, ¬a)` of the unique best arm `a` of `μ` is positive.
* `LMLExplore.Identification.exists_optAlloc_baiTask_restrict_eq_singleton`,
  `LMLExplore.Identification.subsingleton_optAlloc_baiTask_restrict`: for arms in an exponential
  family and a vector of means with unique best arm `a`, the optimal allocation `w*(μ, ¬a)` exists
  and is unique [GK16, Theorem 5].
* `LMLExplore.Identification.pos_of_mem_optAlloc_baiTask_restrict`: the optimal allocation has
  positive entries [GK16, Proposition 6].
* `LMLExplore.Identification.betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc`: for
  `β > 0`, a `β`-optimal allocation `w` (`LMLExplore/Identification/Task/TopTwo/Basic.lean`)
  equalizes the costs of the pairs, `D_β(μ, ¬a) = β d(μ a, m_b) + w b d(μ b, m_b)` for every
  `b ≠ a` [R16, Proposition 7].
* `LMLExplore.Identification.answerValue_baiTask_restrict_eq_of_mem_optAlloc`: the costs of all the
  pairs `(a, b)` equal `D(μ, ¬a)` at the optimal allocation [GK16, Lemma 4], the case `β = w a` of
  the previous statement.
* `LMLExplore.Identification.continuousAt_of_mem_optAlloc_baiTask_restrict`: every selection of the
  optimal allocations is continuous at a vector of means with a unique best arm [GK16,
  Proposition 6].
* `LMLExplore.Identification.mem_optAlloc_baiTask_restrict_iff`: with at least two arms, an
  allocation `w` is the optimal allocation iff it lies in the simplex, `w a > 0`, the costs of the
  pairs `(a, b)` are equal and `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1` [GK16, Theorem 5];
  `LMLExplore.Identification.sum_div_eq_one_of_mem_optAlloc_baiTask_restrict` and
  `LMLExplore.Identification.mem_optAlloc_baiTask_restrict_of_sum_div_eq_one` are its two
  directions, the second without the assumption of a second arm.
* `LMLExplore.Identification.answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq`,
  `LMLExplore.Identification.charTime_baiTask_restrict_eq_inv_expFamilyDiv_of_forall_eq_or_eq`:
  for two arms `a` and `b` in an exponential family with `μ b ≤ μ a` and a mean `z` between them
  with `d(μ a, z) = d(μ b, z)`, `D(μ, ¬a) = d(μ a, z)` and (for `μ b < μ a`)
  `T*(μ) = d(μ a, z)⁻¹`.
* `LMLExplore.Identification.altCost_baiTask_gaussianBandit`: for Gaussian arms with variance
  `σ2 ≠ 0`, `D(μ, w, ¬a) = min_{b ≠ a} (w a w b / (w a + w b)) (μ a - μ b)² / (2 σ2)`.
* `LMLExplore.Identification.answerValue_baiTask_gaussianBandit_of_forall_eq_or_eq`,
  `LMLExplore.Identification.charTime_baiTask_gaussianBandit_of_forall_eq_or_eq`,
  `LMLExplore.Identification.optAlloc_baiTask_gaussianBandit_of_forall_eq_or_eq`: for two Gaussian
  arms with `μ b ≤ μ a`, `D(μ, ¬a) = (μ a - μ b)² / (8 σ2)`, and with `μ b < μ a`,
  `T*(μ) = 8 σ2 / (μ a - μ b)²` and `w*(μ, ¬a) = {(1/2, 1/2)}`.
* `LMLExplore.Identification.le_charTime_baiTask_gaussianBandit`,
  `LMLExplore.Identification.charTime_baiTask_gaussianBandit_le`: for Gaussian arms with variance
  `σ2 ≠ 0` and a unique best arm, `H(μ) ≤ T*(μ) ≤ 2 H(μ)` [GK16, Section 2.2].
* `LMLExplore.Identification.charTime_baiTask_gaussianBandit_ne_zero`,
  `LMLExplore.Identification.charTime_baiTask_gaussianBandit_ne_top`: for Gaussian arms with
  variance `σ2 ≠ 0`, a unique best arm and at least two arms, `0 < T*(μ) < ∞`.
* `LMLExplore.Identification.le_answerValue_baiTask_gaussianBandit`,
  `LMLExplore.Identification.answerValue_baiTask_gaussianBandit_le`: the same bounds on the value,
  `1 / (2 H(μ)) ≤ D(μ, ¬a) ≤ 1 / H(μ)`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2, Lemmas 3–4, Theorem 5 and Proposition 6.
* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Section 3.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Lemmas 28 and 29.
* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2, Assumption 1.
* [R16] D. Russo, *Simple Bayesian algorithms for best arm identification*, COLT 2016;
  Operations Research 68 (2020). Proposition 7 in the numbering of arXiv:1602.08448v4.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} {a : α}

section MeanFunctional

variable (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (mean : Θ → α → ℝ) {θ : Θ}

/-- The alternatives to the arm `a` in best arm identification are the models with a unique best
arm `b ≠ a`. -/
lemma mem_alt_baiTask_iff :
    θ ∈ (baiTask ν mean).alt a ↔ ∃ b ≠ a, ∀ c ≠ b, mean θ c < mean θ b := by
  simp only [IdentTask.mem_alt_iff, M_baiTask, correct_baiTask, Set.mem_ofPred_eq, not_forall,
    not_lt, exists_prop]
  constructor
  · rintro ⟨⟨b, hb⟩, c, hca, hc⟩
    refine ⟨b, ?_, hb⟩
    rintro rfl
    exact (hb c hca).not_ge hc
  · rintro ⟨b, hba, hb⟩
    exact ⟨⟨b, hb⟩, b, hba, (hb a hba.symm).le⟩

/-- The models for which the arm `a` is correct in best arm identification are those with unique
best arm `a`. -/
lemma mem_answerSet_baiTask_iff :
    θ ∈ (baiTask ν mean).answerSet a ↔ ∀ b ≠ a, mean θ b < mean θ a := by
  rw [IdentTask.mem_answerSet_iff, M_baiTask, correct_baiTask]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨a, h⟩, h⟩⟩

variable [Fintype α]

/-- If `a` is the unique best arm of `θ`, then `T*(θ) = D(θ, ¬a)⁻¹` in best arm identification
restricted to any set `S` of models. -/
theorem charTime_baiTask_restrict_eq_inv_answerValue (S : Set Θ)
    (ha : ∀ b ≠ a, mean θ b < mean θ a) :
    ((baiTask ν mean).restrict S).charTime θ =
      (((baiTask ν mean).restrict S).answerValue θ a)⁻¹ :=
  IdentTask.charTime_eq_inv_answerValue _ (by
    rw [IdentTask.correct_restrict]
    exact (correct_baiTask_eq_singleton_iff ν mean).2 ha)

/-- If `a` is the unique best arm of `θ`, then `T*(θ) = D(θ, ¬a)⁻¹` in best arm
identification. -/
theorem charTime_baiTask_eq_inv_answerValue (ha : ∀ b ≠ a, mean θ b < mean θ a) :
    (baiTask ν mean).charTime θ = ((baiTask ν mean).answerValue θ a)⁻¹ :=
  IdentTask.charTime_eq_inv_answerValue _ ((correct_baiTask_eq_singleton_iff ν mean).2 ha)

end MeanFunctional

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {S : Set (α → ℝ)}
  {μ' : α → ℝ}

/-- The vectors of means with unique best arm `a` form an open set. -/
lemma isOpen_answerSet_baiTask [Finite α] (a : α) : IsOpen ((baiTask ν id).answerSet a) := by
  have h : (baiTask ν id).answerSet a = ⋂ b ∈ ({a}ᶜ : Set α), {μ' | μ' b < μ' a} := by
    ext μ'
    rw [mem_answerSet_baiTask_iff]
    simp
  rw [h]
  exact (Set.toFinite _).isOpen_biInter fun b _ ↦
    isOpen_lt (continuous_apply b) (continuous_apply a)

/-- For an open set `S` of vectors of means, the models of best arm identification restricted to
`S` with unique best arm `a` form an open set. -/
lemma isOpen_answerSet_baiTask_restrict [Finite α] (hS : IsOpen S) (a : α) :
    IsOpen (((baiTask ν id).restrict S).answerSet a) := by
  rw [IdentTask.answerSet_restrict]
  exact (isOpen_answerSet_baiTask ν a).inter hS

section Closure

variable [Finite α]

omit [Finite α] in
/-- For a neighbourhood `S` of a vector of means `μ'` whose largest mean is attained at the arm
`a`, the vector `μ'` lies in the closure of the answer set of `a` of `(baiTask ν id).restrict S`,
the vectors of `S` with unique best arm `a`. -/
lemma mem_closure_answerSet_baiTask_restrict (hS : S ∈ 𝓝 μ') (hμ' : ∀ b, μ' b ≤ μ' a) :
    μ' ∈ closure (((baiTask ν id).restrict S).answerSet a) := by
  classical
  -- The path `t ↦ μ' + t • Pi.single a 1` tends to `μ'` and lies in the answer set of `a` for
  -- small `t > 0`: raising the largest mean makes `a` the unique best arm.
  set f : ℝ → α → ℝ := fun t ↦ μ' + t • Pi.single a 1 with hf
  have hf_tendsto : Tendsto f (𝓝[>] 0) (𝓝 μ') := by
    have hf_cont : Continuous f := by fun_prop
    simpa [hf] using hf_cont.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto hf_tendsto ?_
  filter_upwards [hf_tendsto.eventually hS, self_mem_nhdsWithin] with t htS ht
  rw [IdentTask.answerSet_restrict]
  refine ⟨(mem_answerSet_baiTask_iff ν id).2 fun b hb ↦ ?_, htS⟩
  simpa [hf, Pi.single_apply, hb] using (hμ' b).trans_lt (lt_add_of_pos_right _ ht)

/-- For a neighbourhood `S` of a vector of means `μ'` in which some arm `b ≠ a` has mean at least
that of `a`, the vector `μ'` lies in the closure of the alternatives to `a` of
`(baiTask ν id).restrict S`. -/
lemma mem_closure_alt_baiTask_restrict (hS : S ∈ 𝓝 μ')
    (hμ' : ∃ b ≠ a, μ' a ≤ μ' b) : μ' ∈ closure (((baiTask ν id).restrict S).alt a) := by
  -- An arm `b ≠ a` with the largest mean.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, ∀ c, μ' c ≤ μ' b := by
    obtain ⟨b, hba, hab⟩ := hμ'
    have : Nonempty α := ⟨a⟩
    obtain ⟨d, hd⟩ := Finite.exists_max μ'
    by_cases hda : d = a
    · exact ⟨b, hba, fun c ↦ (hda ▸ hd c).trans hab⟩
    · exact ⟨d, hda, hd⟩
  -- The closure of the answer set of `b` is contained in that of the alternatives to `a`.
  refine closure_mono (fun θ hθ ↦ ?_) (mem_closure_answerSet_baiTask_restrict ν hS hb)
  rw [IdentTask.answerSet_restrict] at hθ
  rw [IdentTask.alt_restrict]
  exact ⟨(mem_alt_baiTask_iff ν id).2 ⟨b, hba, (mem_answerSet_baiTask_iff ν id).1 hθ.1⟩, hθ.2⟩

/-- For an open set `S` of vectors of means, the closure within `S` of the alternatives to the arm
`a` in best arm identification restricted to `S` is the set of the vectors of `S` in which some
arm `b ≠ a` has mean at least that of `a`, that is, whose largest mean is attained at an arm
`b ≠ a`. -/
theorem closure_alt_baiTask_restrict_inter (hS : IsOpen S) (a : α) :
    closure (((baiTask ν id).restrict S).alt a) ∩ S = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := by
  refine Set.Subset.antisymm (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨?_, hμ'S⟩)
    (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨mem_closure_alt_baiTask_restrict ν (hS.mem_nhds hμ'S) hμ', hμ'S⟩)
  -- The set is closed, as a finite union of the closed sets `{μ' | μ' a ≤ μ' b}`, `b ≠ a`, and it
  -- contains the alternatives.
  have h_closed : IsClosed {μ' : α → ℝ | ∃ b ≠ a, μ' a ≤ μ' b} := by
    simp only [Set.ofPred_exists]
    refine isClosed_iUnion_of_finite fun b ↦ ?_
    by_cases hba : b = a
    · simp [hba]
    · simpa [hba] using isClosed_le (continuous_apply a) (continuous_apply b)
  refine closure_minimal (fun μ'' hμ'' ↦ ?_) h_closed hμ'
  rw [IdentTask.alt_restrict] at hμ''
  obtain ⟨b, hba, hb⟩ := (mem_alt_baiTask_iff ν id).1 hμ''.1
  exact ⟨b, hba, (hb a hba.symm).le⟩

/-- The closure of the alternatives to the arm `a` in best arm identification is the set of the
vectors of means in which some arm `b ≠ a` has mean at least that of `a`, that is, whose largest
mean is attained at an arm `b ≠ a`. -/
theorem closure_alt_baiTask (a : α) :
    closure ((baiTask ν id).alt a) = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} := by
  simpa using closure_alt_baiTask_restrict_inter ν isOpen_univ a

omit [Finite α] in
/-- For an open set `S` of vectors of means, the closure within `S` of the answer set of the arm
`a` in best arm identification restricted to `S` is the set of the vectors of `S` whose largest
mean is attained at `a`. -/
theorem closure_answerSet_baiTask_restrict_inter (hS : IsOpen S) (a : α) :
    closure (((baiTask ν id).restrict S).answerSet a) ∩ S = {μ' | ∀ b, μ' b ≤ μ' a} ∩ S := by
  refine Set.Subset.antisymm (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨?_, hμ'S⟩)
    (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨mem_closure_answerSet_baiTask_restrict ν (hS.mem_nhds hμ'S) hμ', hμ'S⟩)
  -- The set is closed, as an intersection of the closed sets `{μ' | μ' b ≤ μ' a}`, and it
  -- contains the answer set.
  have h_closed : IsClosed {μ' : α → ℝ | ∀ b, μ' b ≤ μ' a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b ↦ isClosed_le (continuous_apply b) (continuous_apply a)
  refine closure_minimal (fun μ'' hμ'' ↦ ?_) h_closed hμ'
  rw [IdentTask.answerSet_restrict] at hμ''
  intro b
  rcases eq_or_ne b a with rfl | hba
  · exact le_rfl
  · exact ((mem_answerSet_baiTask_iff ν id).1 hμ''.1 b hba).le

omit [Finite α] in
/-- The closure of the answer set of the arm `a` in best arm identification is the set of the
vectors of means whose largest mean is attained at `a`. -/
theorem closure_answerSet_baiTask (a : α) :
    closure ((baiTask ν id).answerSet a) = {μ' | ∀ b, μ' b ≤ μ' a} := by
  simpa using closure_answerSet_baiTask_restrict_inter ν isOpen_univ a

/-- For an open set `S` of vectors of means, the closures of the answer sets of best arm
identification restricted to `S` cover `S`: every vector of `S` is a limit of vectors of `S` whose
unique best arm is one of its arms of largest mean. -/
theorem subset_iUnion_closure_answerSet_baiTask_restrict [Nonempty α] (hS : IsOpen S) :
    S ⊆ ⋃ a, closure (((baiTask ν id).restrict S).answerSet a) := fun μ' hμ' ↦ by
  obtain ⟨a, ha⟩ := Finite.exists_max μ'
  exact Set.mem_iUnion.2 ⟨a, mem_closure_answerSet_baiTask_restrict ν (hS.mem_nhds hμ') ha⟩

end Closure

variable [Fintype α]

/-- For an open set `S` of vectors of means and a transportation cost from `μ` continuous on the
vectors of `S` in which some arm `b ≠ a` has mean at least that of `a`, the cost of the
alternatives to `a` in best arm identification restricted to `S` is
`D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}` [GK16, Section 2]. -/
theorem altCost_baiTask_restrict_eq_iInf (hS : IsOpen S) {μ : α → ℝ} {w : α → ℝ}
    (hc : ContinuousOn ((baiTask ν id).cost w μ) ({μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S)) :
    ((baiTask ν id).restrict S).altCost μ w a =
      ⨅ (b) (_ : b ≠ a) (μ' ∈ S) (_ : μ' a ≤ μ' b), (baiTask ν id).cost w μ μ' := by
  have h_eq := closure_alt_baiTask_restrict_inter ν hS a
  have h_alt : ((baiTask ν id).restrict S).alt a ⊆ {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := fun μ' hμ' ↦
    h_eq ▸ ⟨subset_closure hμ', ((baiTask ν id).alt_restrict a ▸ hμ').2⟩
  rw [IdentTask.altCost_eq_biInf_of_subset_closure _ h_alt (fun μ' hμ' ↦ (h_eq.symm.subset hμ').1)
    (by rwa [IdentTask.cost_restrict]), IdentTask.cost_restrict]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, iInf_and, iInf_exists]
  -- Bring the arm `b` and the condition `b ≠ a` in front, then swap the two conditions on `μ'`.
  rw [iInf_comm]
  refine iInf_congr fun b ↦ ?_
  rw [iInf_comm]
  exact iInf_congr fun _ ↦ iInf_congr fun _ ↦ iInf_comm

section ExpFamily

/-! ### Arms in an exponential family -/

variable {ρ : Measure 𝓨} {T : 𝓨 → ℝ} {μ w : α → ℝ}

/-- Moving the means of two arms `a ≠ b` of `μ` to a common mean `z` of the family gives a vector
of means of the family in which `b` is at least as good as `a`, at transportation cost
`w a d(μ a, z) + w b d(μ b, z)` from `μ`. -/
private lemma iInf_cost_baiTask_le (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hw : 0 ≤ w) {b : α} (hba : b ≠ a) {z : ℝ} (hz : z ∈ ρ.expFamilyMeans T) :
    ⨅ μ' ∈ {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T}, ⨅ (_ : μ' a ≤ μ' b),
        (baiTask ν id).cost w μ μ' ≤
      ENNReal.ofReal (w a * ρ.expFamilyDiv T (μ a) z + w b * ρ.expFamilyDiv T (μ b) z) := by
  classical
  set μ' := Function.update (Function.update μ a z) b z
  have hμ' (c : α) : μ' c ∈ ρ.expFamilyMeans T := by
    simp only [μ', Function.update_apply]
    split_ifs
    exacts [hz, hz, hμ c]
  refine (iInf₂_le μ' hμ').trans (iInf_le_of_le (by simp [μ', hba.symm]) ?_)
  rw [IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv (ρ := fun _ ↦ ρ) (T := fun _ ↦ T)
      (ν_baiTask ν id) hν hw hμ',
    ← Finset.sum_subset (Finset.subset_univ {a, b}) fun c _ hc ↦ ?_, Finset.sum_pair hba.symm,
    ← ENNReal.ofReal_add (mul_nonneg (hw a) (expFamilyDiv_nonneg (hμ a) (hμ' a)))
      (mul_nonneg (hw b) (expFamilyDiv_nonneg (hμ b) (hμ' b)))]
  · simp [μ', hba.symm]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [μ', hc.1, hc.2, expFamilyDiv_self]

/-- **The cost of the alternatives in best arm identification with arms in an exponential
family** [GK16, Lemma 3]. Let the arm laws of best arm identification belong to an exponential
family with divergence `d`, in the sense that `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` for all vectors
of means `μ'` of the family (for example when `ν μ' c` is the member of mean `μ' c`, by
`klDiv_expFamily_natParam`), and let `a` be a best arm of `μ`. Then on the vectors of means of the
family, for every nonnegative allocation `w`,
`D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)` is the mean of `μ a` and `μ b` weighted by `w`, so that
the cost of the pair `(a, b)` is `expFamilyPairCost ρ T (μ a) (μ b) (w a) (w b)`: the cost of the
alternatives in which `b` beats `a` is approached by moving both means to `m_b`. -/
theorem altCost_baiTask_restrict_eq_iInf_expFamilyPairCost
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
      ⨅ (b) (_ : b ≠ a), ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b)) := by
  classical
  have hw' (c : α) : 0 ≤ w c := hw c
  set S := {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T} with hS_def
  have hS : IsOpen S := by
    rw [hS_def, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun c ↦ (isOpen_expFamilyMeans hT).preimage (continuous_apply c)
  have h_cost {μ' : α → ℝ} (hμ' : μ' ∈ S) :
      (baiTask ν id).cost w μ μ' = ENNReal.ofReal (∑ c, w c * ρ.expFamilyDiv T (μ c) (μ' c)) := by
    rw [IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv (ρ := fun _ ↦ ρ) (T := fun _ ↦ T)
      (ν_baiTask ν id) hν hw hμ', ENNReal.ofReal_sum_of_nonneg fun c _ ↦
        mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))]
  -- The cost is continuous on the vectors of means of the family, so that the alternatives can
  -- be replaced by their closure, in which `b` is at least as good as `a` for some `b ≠ a`.
  have hc : ContinuousOn ((baiTask ν id).cost w μ) S := by
    refine (baiTask ν id).continuousOn_cost (fun c ↦ ?_) w
    have h := ENNReal.continuous_ofReal.comp_continuousOn ((continuousOn_expFamilyDiv hT).comp
      (f := fun μ' : α → ℝ ↦ (μ c, μ' c)) (s := S) (by fun_prop) fun μ' hμ' ↦ ⟨hμ c, hμ' c⟩)
    exact h.congr fun μ' hμ' ↦ by rw [ν_baiTask, hν μ' hμ' c]; rfl
  rw [altCost_baiTask_restrict_eq_iInf ν hS (hc.mono Set.inter_subset_right)]
  refine iInf_congr fun b ↦ iInf_congr fun hba ↦ le_antisymm ?_ ?_
  · -- Upper bound: move the means of `a` and `b` to the weighted mean `m_b`, a mean of the
    -- family (or to `μ a` if both weights vanish).
    rw [expFamilyPairCost_def]
    rcases (add_nonneg (hw a) (hw b)).eq_or_lt with hW | hW
    · obtain ⟨hwa, hwb⟩ : w a = 0 ∧ w b = 0 :=
        ⟨by linarith [hw' a, hw' b], by linarith [hw' a, hw' b]⟩
      simpa [hwa, hwb, hS_def] using iInf_cost_baiTask_le ν hμ hν hw hba (hμ a)
    exact iInf_cost_baiTask_le ν hμ hν hw hba
      (div_mem_expFamilyMeans (hμ a) (hμ b) (hw a) (hw b) hW)
  · -- Lower bound: drop the arms other than `a` and `b`, then move both means to `m_b`.
    refine le_iInf₂ fun μ' hμ' ↦ le_iInf fun hab ↦ ?_
    rw [h_cost hμ']
    refine ENNReal.ofReal_le_ofReal ((expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv
      hT (hμ a) (hμ b) (ha b) (hw a) (hw b) (hμ' a) (hμ' b) hab).trans ?_)
    rw [← Finset.sum_pair (f := fun c ↦ w c * ρ.expFamilyDiv T (μ c) (μ' c)) hba.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ ↦
      mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))

/-! #### Two arms -/

variable {b : α}

omit [Fintype α] in
/-- With two arms `a` and `b` and `μ b < μ a`, the arm `a` is the only correct answer of best arm
identification. -/
private lemma correct_baiTask_of_forall_eq_or_eq (hα : ∀ c, c = a ∨ c = b)
    (hμ : μ b < μ a) : (baiTask ν id).correct μ = {a} := by
  refine (correct_baiTask_eq_singleton_iff ν id).2 ?_
  intro d hd
  obtain rfl := (hα d).resolve_left hd
  exact hμ

/-- **The game value of two arms in an exponential family** [KCG16, Section 3]. For two arms `a`
and `b` whose laws belong to an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), with `μ b ≤ μ a`, and a mean `z` between
`μ b` and `μ a` at the same divergence from both, `d(μ a, z) = d(μ b, z)`, the value of the game of
the answer `a` is `D(μ, ¬a) = d(μ a, z)`. Such a `z` exists by `exists_mem_Icc_expFamilyDiv_eq`. -/
theorem answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hba : b ≠ a) (hα : ∀ c, c = a ∨ c = b) (hμab : μ b ≤ μ a) {z : ℝ}
    (hz : z ∈ Set.Icc (μ b) (μ a))
    (hd : ρ.expFamilyDiv T (μ a) z = ρ.expFamilyDiv T (μ b) z) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ a =
      ENNReal.ofReal (ρ.expFamilyDiv T (μ a) z) := by
  classical
  have ha := apply_le_of_forall_eq_or_eq hα hμab
  have hz_mem : z ∈ ρ.expFamilyMeans T := Icc_subset_expFamilyMeans (hμ b) (hμ a) hz
  -- With two arms, the cost of the alternatives is the cost of moving both means to `m_b`.
  have h_alt {w : α → ℝ} (hw : w ∈ simplex α) :
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
        ENNReal.ofReal (w a * ρ.expFamilyDiv T (μ a) (w a * μ a + w b * μ b) +
          w b * ρ.expFamilyDiv T (μ b) (w a * μ a + w b * μ b)) := by
    rw [altCost_baiTask_restrict_eq_iInf_expFamilyPairCost ν hT hμ hν ha fun c ↦
      (mem_simplex_iff.1 hw).1 c, iInf_ne_eq_of_forall_eq_or_eq hba hα, expFamilyPairCost_def,
      add_eq_one_of_mem_simplex hba.symm hα hw, div_one]
  rw [IdentTask.answerValue_def]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · -- Upper bound: the weighted mean minimizes the weighted divergence, in particular against `z`.
    have hsum := add_eq_one_of_mem_simplex hba.symm hα hw
    have hwa : 0 ≤ w a := (mem_simplex_iff.1 hw).1 a
    have hwb : 0 ≤ w b := (mem_simplex_iff.1 hw).1 b
    have hm_mem : w a * μ a + w b * μ b ∈ ρ.expFamilyMeans T := by
      simpa [hsum] using div_mem_expFamilyMeans (hμ a) (hμ b) hwa hwb (by rw [hsum]; exact one_pos)
    rw [h_alt hw]
    refine ENNReal.ofReal_le_ofReal ((mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq hwa hwb
      (by rw [hsum, one_mul]) hm_mem hz_mem).trans_eq ?_)
    rw [← hd, ← add_mul, hsum, one_mul]
  · -- Lower bound: the allocation whose weighted mean is `z`.
    rcases hμab.eq_or_lt with heq | hlt
    · have hza : z = μ a := le_antisymm hz.2 (heq ▸ hz.1)
      rw [hza, expFamilyDiv_self, ENNReal.ofReal_zero]
      exact zero_le
    set t := (z - μ b) / (μ a - μ b) with ht_def
    have hΔ : 0 < μ a - μ b := sub_pos.2 hlt
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hz.1) hΔ.le
    have ht1 : t ≤ 1 := (div_le_one hΔ).2 (by linarith [hz.2])
    set w : α → ℝ := fun c ↦ if c = a then t else 1 - t with hw_def
    have hwa : w a = t := by simp [hw_def]
    have hwb : w b = 1 - t := by simp [hw_def, hba]
    have hw : w ∈ simplex α := mem_simplex_iff.2 ⟨fun c ↦ by
      simp only [hw_def]; split_ifs <;> linarith, by
      rw [Fintype.sum_eq_add a b hba.symm fun c hc ↦ absurd (hα c) (not_or.2 hc), hwa, hwb]
      ring⟩
    have hm : w a * μ a + w b * μ b = z := by
      rw [hwa, hwb, ht_def]
      field_simp
      ring
    refine le_iSup₂_of_le w hw (le_of_eq ?_)
    rw [h_alt hw, hm, ← hd, ← add_mul, add_eq_one_of_mem_simplex hba.symm hα hw, one_mul]

/-- **The characteristic time of two arms in an exponential family** [KCG16, Section 3]. For two
arms `a` and `b` whose laws belong to an exponential family with divergence `d`, with
`μ b < μ a`, and a mean `z` between `μ b` and `μ a` with `d(μ a, z) = d(μ b, z)`,
`T*(μ) = d(μ a, z)⁻¹`. -/
theorem charTime_baiTask_restrict_eq_inv_expFamilyDiv_of_forall_eq_or_eq
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hba : b ≠ a) (hα : ∀ c, c = a ∨ c = b) (hμab : μ b < μ a) {z : ℝ}
    (hz : z ∈ Set.Icc (μ b) (μ a))
    (hd : ρ.expFamilyDiv T (μ a) z = ρ.expFamilyDiv T (μ b) z) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ =
      (ENNReal.ofReal (ρ.expFamilyDiv T (μ a) z))⁻¹ := by
  rw [IdentTask.charTime_eq_inv_answerValue _
      (by rw [IdentTask.correct_restrict]; exact correct_baiTask_of_forall_eq_or_eq ν hα hμab),
    answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq ν hT hμ hν hba hα hμab.le hz hd]

/-! #### Continuity in the model and the allocation -/

/-- The closed form [GK16, Lemma 3] of the cost of the alternatives as a finite infimum:
`D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))`, as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`, written with `Finset.inf` so that strict
inequalities with it reduce to the pairs `(a, b)` (`Finset.lt_inf_iff`). -/
theorem altCost_baiTask_restrict_eq_inf [DecidableEq α] (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
      (Finset.univ.filter (· ≠ a)).inf fun b ↦
        ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b)) := by
  rw [altCost_baiTask_restrict_eq_iInf_expFamilyPairCost ν hT hμ hν ha hw, Finset.inf_eq_iInf]
  simp

/-- The closed form [GK16, Lemma 3] of the cost of the alternatives is continuous in the model
and the allocation, on the vectors of means of the family and the nonnegative allocations. -/
private lemma continuousOn_inf_expFamilyPairCost [DecidableEq α] (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (a : α) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦ (Finset.univ.filter (· ≠ a)).inf fun b ↦
        ENNReal.ofReal (ρ.expFamilyPairCost T (p.1 a) (p.1 b) (p.2 a) (p.2 b)))
      ({μ | ∀ c, μ c ∈ ρ.expFamilyMeans T} ×ˢ Set.Ici 0) := by
  refine ContinuousOn.finset_inf_apply fun b _ ↦ ENNReal.continuous_ofReal.comp_continuousOn ?_
  refine (continuousOn_expFamilyPairCost hT).comp
    (f := fun p : (α → ℝ) × (α → ℝ) ↦ ((p.1 a, p.1 b), (p.2 a, p.2 b))) (by fun_prop) ?_
  rintro ⟨μ, w⟩ ⟨hμ, hw⟩
  exact ⟨⟨hμ a, hμ b⟩, hw a, hw b⟩

/-- **Continuity of the cost of the alternatives in best arm identification**, for arms in an
exponential family with divergence `d` (in the sense that `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` for
all vectors of means `μ`, `μ'` of the family): on the vectors of means of the family with best arm
`a`, `(μ, w) ↦ D(μ, w, ¬a)` is continuous in the model and the nonnegative allocation. -/
theorem continuousOn_altCost_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c))) (a : α) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost p.1 p.2 a)
      ({μ | (∀ c, μ c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ b ≤ μ a} ×ˢ Set.Ici 0) := by
  classical
  -- The closed form `min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` [GK16, Lemma 3] is a
  -- finite infimum of continuous functions.
  refine ((continuousOn_inf_expFamilyPairCost hT a).mono
    (Set.prod_mono (fun _ ↦ And.left) subset_rfl)).congr fun p ⟨⟨hμ, ha⟩, hw⟩ ↦ ?_
  exact altCost_baiTask_restrict_eq_inf ν hT hμ (hν p.1 · hμ) ha hw

/-- **Continuity of the cost of the alternatives in the allocation**, for arms in an exponential
family with divergence `d` (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`): at a
vector of means `μ` of the family with best arm `a`, `w ↦ D(μ, w, ¬a)` is continuous on the
nonnegative allocations. -/
theorem continuousOn_altCost_baiTask_restrict_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) :
    ContinuousOn (fun w ↦
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a)
      (Set.Ici 0) := by
  classical
  exact ((continuousOn_inf_expFamilyPairCost hT a).comp (f := fun w ↦ (μ, w)) (by fun_prop)
    fun _ hw ↦ ⟨hμ, hw⟩).congr fun w hw ↦ altCost_baiTask_restrict_eq_inf ν hT hμ hν ha hw

/-- **Continuity of the cost of the alternatives near a model**, for arms in an exponential family
with divergence `d` (as in `continuousOn_altCost_baiTask_restrict`): at a vector of means `μ` of
the family with unique best arm `a`, `(μ', w) ↦ D(μ', w, ¬a)` is continuous within
`univ ×ˢ simplex α` at `(μ, w)` for every allocation `w` of the simplex. This is the continuity
hypothesis of the continuity of the value and of the upper hemicontinuity of the optimal
allocations (`IdentTask.continuousWithinAt_answerValue`,
`IdentTask.upperHemicontinuousWithinAt_optAlloc`) and the hypothesis `h_cont` of the sample
complexity bound of C-Track-and-Stop
(`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`). At `w = w μ`, its
`.lowerSemicontinuousWithinAt` gives the hypothesis `h_lsc` of the bound of Track-and-Stop
(`IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`). -/
theorem continuousWithinAt_altCost_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) (hw : w ∈ simplex α) :
    ContinuousWithinAt (fun p : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost p.1 p.2 a)
      (Set.univ ×ˢ simplex α) (μ, w) := by
  have h_best : (baiTask ν id).answerSet a ∈ 𝓝 μ :=
    (isOpen_answerSet_baiTask ν a).mem_nhds ((mem_answerSet_baiTask_iff ν id).2 ha)
  have h_nhds : {μ' : α → ℝ | (∀ c, μ' c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ' b ≤ μ' a} ∈ 𝓝 μ :=
    (eventually_all.2 fun c ↦ (continuous_apply c).continuousAt.preimage_mem_nhds
      (expFamilyMeans_mem_nhds hT (hμ c))).and
      (mem_of_superset h_best fun _ hμ' ↦
        apply_le_of_forall_ne_lt ((mem_answerSet_baiTask_iff ν id).1 hμ'))
  have h_mem : {μ' : α → ℝ | (∀ c, μ' c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ' b ≤ μ' a} ×ˢ Set.Ici 0 ∈
      𝓝[Set.univ ×ˢ simplex α] (μ, w) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact prod_mem_prod h_nhds (mem_of_superset self_mem_nhdsWithin simplex_subset_nonneg)
  exact ((continuousOn_altCost_baiTask_restrict ν hT hν a) _
    ⟨mem_of_mem_nhds h_nhds, simplex_subset_nonneg hw⟩).mono_of_mem_nhdsWithin h_mem

/-- **Continuity of the value of the answer `a` in best arm identification** [DK19, Lemma 28], for
arms in an exponential family with divergence `d` (as in
`continuousOn_altCost_baiTask_restrict`): at a vector of means `μ` of the family with unique best
arm `a`, the value `μ' ↦ D(μ', ¬a)` of the game of the answer `a` is continuous. -/
theorem continuousAt_answerValue_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) :
    ContinuousAt (fun μ' ↦
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ' a) μ := by
  rw [← continuousWithinAt_univ]
  exact IdentTask.continuousWithinAt_answerValue _ fun _ hw ↦
    continuousWithinAt_altCost_baiTask_restrict ν hT hν hμ ha hw

/-- **Upper hemicontinuity of the optimal allocations of best arm identification**
[DK19, Lemma 28], for arms in an exponential family with divergence `d` (as in
`continuousOn_altCost_baiTask_restrict`): at a vector of means `μ` of the family with unique best
arm `a`, the optimal allocations `μ' ↦ w*(μ', ¬a)` are upper hemicontinuous: for every open set
`U ⊇ w*(μ, ¬a)`, `w*(μ', ¬a) ⊆ U` for `μ'` close enough to `μ`. Since `w*(μ, ¬a)` is a single
allocation [GK16, Theorem 5], this gives the continuity of the optimal allocation at `μ`
[GK16, Proposition 6], `continuousAt_of_mem_optAlloc_baiTask_restrict`. -/
theorem upperHemicontinuousAt_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) :
    UpperHemicontinuousAt (fun μ' ↦
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ' a) μ := by
  rw [← upperHemicontinuousWithinAt_univ_iff]
  exact IdentTask.upperHemicontinuousWithinAt_optAlloc _ fun _ hw ↦
    continuousWithinAt_altCost_baiTask_restrict ν hT hν hμ ha hw

/-- **Continuity of the characteristic time of best arm identification** [DK19, Lemma 29], for
arms in an exponential family with divergence `d` (as in
`continuousOn_altCost_baiTask_restrict`): the characteristic time `T*` is continuous at every
vector of means of the family with a unique best arm. -/
theorem continuousAt_charTime_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) :
    ContinuousAt ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ := by
  -- Near `μ`, the arm `a` is the unique best arm, so `T*(μ') = D(μ', ¬a)⁻¹`.
  have h_eq : (fun μ' ↦ (((baiTask ν id).restrict
        {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ' a)⁻¹) =ᶠ[𝓝 μ]
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime := by
    filter_upwards [(isOpen_answerSet_baiTask ν a).mem_nhds ((mem_answerSet_baiTask_iff ν id).2 ha)]
      with μ' hμ'
    exact (charTime_baiTask_restrict_eq_inv_answerValue ν id _
      ((mem_answerSet_baiTask_iff ν id).1 hμ')).symm
  exact ((continuousAt_answerValue_baiTask_restrict ν hT hν hμ ha).inv).congr h_eq

/-! #### The optimal allocation -/

/-- In best arm identification with arms in an exponential family (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), the value `D(μ, ¬a)` of the game of the
unique best arm `a` of `μ` is positive, so that the characteristic time `T*(μ) = D(μ, ¬a)⁻¹` is
finite. -/
theorem answerValue_baiTask_restrict_pos (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) :
    0 < ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ a := by
  classical
  have ha' := apply_le_of_forall_ne_lt ha
  -- The uniform allocation collects positive information against every alternative.
  have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨a⟩)
  set u : α → ℝ := fun _ ↦ (Fintype.card α : ℝ)⁻¹
  have : Nonempty α := ⟨a⟩
  have hu : u ∈ simplex α := uniform_mem_simplex α
  refine lt_of_lt_of_le ?_ (IdentTask.altCost_le_answerValue _ hu)
  rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' (mem_simplex_iff.1 hu).1,
    Finset.lt_inf_iff ENNReal.zero_lt_top]
  intro b hb
  exact ENNReal.ofReal_pos.2 (expFamilyPairCost_pos (hμ a) (hμ b)
    (ha b (Finset.mem_filter.1 hb).2).ne' (inv_pos.2 hK) (inv_pos.2 hK))

/-- **The optimal allocations of best arm identification have positive entries**
[GK16, Proposition 6].
For arms in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`) and
a vector of means `μ` of the family with unique best arm `a`, every optimal allocation `w*(μ, ¬a)`
gives a positive proportion to every arm. -/
theorem pos_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a)
    (c : α) : 0 < w c := by
  classical
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨hws, hD⟩ := (IdentTask.mem_optAlloc_iff _).1 hw
  rw [mem_simplex_iff] at hws
  refine (hws.1 c).lt_of_ne' fun hc ↦ ?_
  -- Some arm `b ≠ a` has `w a = 0` or `w b = 0`, so that the pair `(a, b)` costs nothing.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, w a = 0 ∨ w b = 0 := by
    by_cases hca : c = a
    · subst hca
      obtain ⟨b, hb⟩ : ∃ b, b ≠ c := by
        by_contra! h
        have h_sum := hws.2
        rw [Fintype.sum_eq_single c fun b hb ↦ (hb (h b)).elim, hc] at h_sum
        exact zero_ne_one h_sum
      exact ⟨b, hb, Or.inl hc⟩
    · exact ⟨c, hca, Or.inr hc⟩
  have h0 : ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a = 0 := by
    rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hws.1]
    refine le_antisymm ((Finset.inf_le (Finset.mem_filter.2 ⟨Finset.mem_univ b, hba⟩)).trans ?_)
      zero_le
    rw [expFamilyPairCost_eq_zero hb, ENNReal.ofReal_zero]
  exact (answerValue_baiTask_restrict_pos ν hT hμ hν ha).ne' (hD ▸ h0)

/-- **The `β`-optimal allocations of best arm identification equalize the costs of the pairs of
arms** [R16, Proposition 7]. For arms in an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the family with
unique best arm `a`, `β > 0` and a `β`-optimal allocation `w` of the answer `a` with the arm `a`,
the minimum `D(μ, w, ¬a) = min_{b ≠ a} (β d(μ a, m_b) + w b d(μ b, m_b))` is attained at every arm
`b ≠ a`: `D_β(μ, ¬a) = β d(μ a, m_b) + w b d(μ b, m_b)` for every `b ≠ a`, with
`m_b = (β μ a + w b μ b) / (β + w b)`. -/
theorem betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc {β : ℝ}
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : 0 < β)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (hba : b ≠ a) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaAnswerValue μ a a β =
      ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ b) β (w b)) := by
  classical
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨hws, hwa, hV⟩ := task.mem_betaOptAlloc_iff.1 hw
  have hw0 := (mem_simplex_iff.1 hws).1
  -- The `β`-value is the cost of the alternatives at `w`, the minimum of the costs of the pairs.
  have h_inf : task.betaAnswerValue μ a a β = (Finset.univ.filter (· ≠ a)).inf fun c ↦
      ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ c) β (w c)) := by
    rw [← hV, altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0, hwa]
  have hmem {c : α} (hc : c ≠ a) : c ∈ Finset.univ.filter (· ≠ a) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩
  refine le_antisymm (h_inf ▸ Finset.inf_le (hmem hba)) (not_lt.1 fun h ↦ ?_)
  -- Otherwise the `β`-value `D = ofReal D'` is finite, and `D' < cost of (a, b)`.
  have hD_top : task.betaAnswerValue μ a a β ≠ ∞ := (h.trans ENNReal.ofReal_lt_top).ne
  set D' := (task.betaAnswerValue μ a a β).toReal with hD'_def
  have hD_eq : task.betaAnswerValue μ a a β = ENNReal.ofReal D' :=
    (ENNReal.ofReal_toReal hD_top).symm
  have hD'_le {c : α} (hc : c ≠ a) : D' ≤ ρ.expFamilyPairCost T (μ a) (μ c) β (w c) :=
    ENNReal.toReal_le_of_le_ofReal (expFamilyPairCost_nonneg (hμ a) (hμ c) hβ.le (hw0 c))
      (h_inf ▸ Finset.inf_le (hmem hc))
  have hD'_lt : D' < ρ.expFamilyPairCost T (μ a) (μ b) β (w b) :=
    (ENNReal.ofReal_lt_ofReal_iff'.1 (hD_eq ▸ h)).1
  -- The pair `(a, b)` costs more than nothing, so that `w b > 0`.
  have hwb : 0 < w b := by
    refine (hw0 b).lt_of_ne' fun h0 ↦ ?_
    rw [h0, expFamilyPairCost_eq_zero (Or.inr rfl)] at hD'_lt
    exact hD'_lt.not_ge ENNReal.toReal_nonneg
  -- The arms other than `a` and `b`.
  set R := Finset.univ.filter fun c ↦ c ≠ a ∧ c ≠ b with hR_def
  have hmemR {c : α} : c ∈ R ↔ c ≠ a ∧ c ≠ b := by simp [hR_def]
  rcases R.eq_empty_or_nonempty with hR | hR
  · -- If `b` is the only arm other than `a`, the `β`-value is the cost of `(a, b)`.
    have h_eq : Finset.univ.filter (· ≠ a) = {b} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine ⟨fun hc ↦ by_contra fun hcb ↦ ?_, fun hcb ↦ hcb ▸ hba⟩
      simpa [hR] using hmemR.2 ⟨hc, hcb⟩
    rw [h_inf, h_eq, Finset.inf_singleton] at h
    exact h.false
  -- Removing a little weight `s` from the arm `b` keeps the cost of `(a, b)` above `D'`, by
  -- continuity.
  have h_cont : ContinuousAt (fun s ↦ ρ.expFamilyPairCost T (μ a) (μ b) β (w b - s)) 0 := by
    have hc := (continuousOn_expFamilyPairCost hT (ρ := ρ)).continuousAt
      (x := ((μ a, μ b), (β, w b))) (prod_mem_nhds
        (prod_mem_nhds (expFamilyMeans_mem_nhds hT (hμ a)) (expFamilyMeans_mem_nhds hT (hμ b)))
        (prod_mem_nhds (Ici_mem_nhds hβ) (Ici_mem_nhds hwb)))
    have hf : ContinuousAt (fun s : ℝ ↦ ((μ a, μ b), (β, w b - s))) 0 := by fun_prop
    exact hc.comp_of_eq hf (by simp)
  obtain ⟨s, hs_lt, hs⟩ := ((h_cont.eventually (lt_mem_nhds (by simpa using hD'_lt))).filter_mono
    nhdsWithin_le_nhds |>.and (Ioo_mem_nhdsGT hwb)).exists
  -- The allocation `v` moves the weight `s` from the arm `b` to the arms other than `a` and `b`,
  -- in equal parts `r`.
  set r : ℝ := s / R.card with hr_def
  have hr : 0 < r := div_pos hs.1 (Nat.cast_pos.2 hR.card_pos)
  set v : α → ℝ := w - Pi.single b s + (R : Set α).indicator (fun _ ↦ r) with hv_def
  have hv : v ∈ simplex α := sub_single_add_indicator_mem_simplex hws hs.1.le hs.2.le hR
  have hv0 := (mem_simplex_iff.1 hv).1
  have hvR {c : α} (hc : c ∈ R) : v c = w c + r := by
    simp [hv_def, Set.indicator_of_mem (Finset.mem_coe.2 hc), (hmemR.1 hc).2]
  have hvb : v b = w b - s := by simp [hv_def, hmemR]
  have hva : v a = β := by simp [hv_def, hmemR, hba.symm, hwa]
  -- Every pair costs more than `D'` at `v`, contradicting the `β`-optimality of `w`.
  have h_lt : task.betaAnswerValue μ a a β < task.altCost μ v a := by
    rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hv0, hva, Finset.lt_inf_iff hD_top.lt_top]
    intro c hc
    have hca := (Finset.mem_filter.1 hc).2
    rw [hD_eq, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (ENNReal.toReal_nonneg)]
    by_cases hcb : c = b
    · subst hcb
      rw [hvb]
      exact hs_lt
    · have hcR : c ∈ R := hmemR.2 ⟨hca, hcb⟩
      rw [hvR hcR]
      exact (hD'_le hca).trans_lt (strictMonoOn_expFamilyPairCost (hμ a) (hμ c) (ha c hca).ne' hβ
        (Set.mem_Ici.2 (hw0 c)) (Set.mem_Ici.2 (add_nonneg (hw0 c) hr.le)) (by linarith))
  exact (task.altCost_le_betaAnswerValue hv hva).not_gt h_lt

/-- **The optimal allocations of best arm identification equalize the costs of the pairs of
arms** [GK16, Lemma 4]. For arms in an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the family with
unique best arm `a` and an optimal allocation `w`, the minimum
`D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` is attained at every arm `b ≠ a`:
`D(μ, ¬a) = w a d(μ a, m_b) + w b d(μ b, m_b)` for every `b ≠ a`, with
`m_b = (w a μ a + w b μ b) / (w a + w b)`. -/
theorem answerValue_baiTask_restrict_eq_of_mem_optAlloc (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a)
    (hba : b ≠ a) :
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ a =
      ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b)) := by
  rw [← IdentTask.betaAnswerValue_eq_answerValue_of_mem_optAlloc _ hw a]
  exact betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc ν hT hμ hν ha
    (pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw a)
    (IdentTask.mem_betaOptAlloc_of_mem_optAlloc _ hw a) hba

/-- **The optimal allocation of best arm identification is unique** [GK16, Theorem 5]. For arms
in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`) and a vector
of means `μ` of the family with unique best arm `a`, there is at most one optimal allocation
`w*(μ, ¬a)`. -/
theorem subsingleton_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) :
    (((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a).Subsingleton :=
    by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  intro w hw w' hw'
  have hw'' : (fun c ↦ (w c + w' c) / 2) ∈ task.optAlloc μ a := by
    convert task.convex_optAlloc μ a hw hw' (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) using 1
    funext c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hv0 {v : α → ℝ} (hv : v ∈ task.optAlloc μ a) : ∀ c, 0 ≤ v c :=
    (mem_simplex_iff.1 ((IdentTask.mem_optAlloc_iff _).1 hv).1).1
  have hv1 {v : α → ℝ} (hv : v ∈ task.optAlloc μ a) : ∑ c, v c = 1 :=
    (mem_simplex_iff.1 ((IdentTask.mem_optAlloc_iff _).1 hv).1).2
  have hpos := pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw
  have hpos' := pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw'
  -- The three allocations equalize the costs of all the pairs `(a, b)`, at the same value.
  have h_eq {v : α → ℝ} (hv : v ∈ task.optAlloc μ a) {b : α} (hba : b ≠ a) :
      task.answerValue μ a = ENNReal.ofReal (ρ.expFamilyPairCost T (μ a) (μ b) (v a) (v b)) :=
    answerValue_baiTask_restrict_eq_of_mem_optAlloc ν hT hμ hν ha hv hba
  have h_nonneg {v : α → ℝ} (hv : v ∈ task.optAlloc μ a) (b : α) :
      0 ≤ ρ.expFamilyPairCost T (μ a) (μ b) (v a) (v b) :=
    expFamilyPairCost_nonneg (hμ a) (hμ b) (hv0 hv a) (hv0 hv b)
  -- For each arm `b`, the weights of `a` and `b` are proportional in `w` and `w'`.
  have h_prop (b : α) : w a * w' b = w' a * w b := by
    rcases eq_or_ne b a with rfl | hba
    · ring
    refine mul_eq_mul_of_expFamilyPairCost_midpoint_eq (hμ a) (hμ b) (ha b hba).ne' (hv0 hw a)
      (hv0 hw b) (hv0 hw' a) (hv0 hw' b) (add_pos (hpos a) (hpos b)) (add_pos (hpos' a) (hpos' b))
      ?_ ?_
    · exact (ENNReal.ofReal_eq_ofReal_iff (h_nonneg hw'' b) (h_nonneg hw b)).1
        ((h_eq hw'' hba).symm.trans (h_eq hw hba))
    · exact (ENNReal.ofReal_eq_ofReal_iff (h_nonneg hw'' b) (h_nonneg hw' b)).1
        ((h_eq hw'' hba).symm.trans (h_eq hw' hba))
  -- Summing over `b`, the weights of `a` agree, hence all the weights do.
  have h_a : w a = w' a := by
    have h := Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) ↦ h_prop b
    rwa [← Finset.mul_sum, ← Finset.mul_sum, hv1 hw, hv1 hw', mul_one, mul_one] at h
  funext b
  have h := h_prop b
  rw [h_a] at h
  exact (mul_left_cancel₀ (h_a ▸ hpos a).ne' h).symm

/-- **The optimal allocation of best arm identification** [GK16, Theorem 5]. For arms in an
exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`) and a vector of
means `μ` of the family with unique best arm `a`, there is exactly one optimal allocation
`w*(μ, ¬a)`. It has positive entries (`pos_of_mem_optAlloc_baiTask_restrict`) and equalizes the
costs of the pairs of arms (`answerValue_baiTask_restrict_eq_of_mem_optAlloc`). -/
theorem exists_optAlloc_baiTask_restrict_eq_singleton (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) :
    ∃ w, ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a = {w} := by
  have ha' := apply_le_of_forall_ne_lt ha
  have : Nonempty α := ⟨a⟩
  -- The cost of the alternatives is continuous in the allocation, so that an optimal allocation
  -- exists.
  obtain ⟨w, hw⟩ := IdentTask.optAlloc_nonempty _
    ((continuousOn_altCost_baiTask_restrict_left ν hT hμ hν ha').mono
      simplex_subset_nonneg).upperSemicontinuousOn
  exact ⟨w, (subsingleton_optAlloc_baiTask_restrict ν hT hμ hν ha).eq_singleton_of_mem hw⟩

/-- **Continuity of the optimal allocation of best arm identification** [GK16, Proposition 6]. For
arms in an exponential family with divergence `d` (as in `continuousOn_altCost_baiTask_restrict`)
and a vector of means `μ` of the family with unique best arm `a`, every selection `f` of the
optimal allocations near `μ`, `f μ' ∈ w*(μ', ¬a)`, is continuous at `μ`. -/
theorem continuousAt_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) {f : (α → ℝ) → α → ℝ}
    (hf : ∀ᶠ μ' in 𝓝 μ,
      f μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ' a) :
    ContinuousAt f μ :=
  (upperHemicontinuousAt_optAlloc_baiTask_restrict ν hT hν hμ ha).continuousAt_of_eventually_mem
    (subsingleton_optAlloc_baiTask_restrict ν hT hμ (hν μ · hμ) ha) hf

/-! #### The scalar equation of the optimal allocation -/

section ScalarEquation

/-! The cost of a pair `(a, b)` is the minimum over the means `z` of
`w a d(μ a, z) + w b d(μ b, z)`, a minimum of functions linear in the allocation. When the scalar
equation holds, a combination of these linear bounds certifies optimality; at the optimum, a
perturbation of the allocation increasing every pair cost to first order exists unless the equation
holds. -/

open Finset

/-- A perturbation of an allocation `w` with positive entries along a direction `u` of total
weight `0` that increases the cost of every pair `(a, b)`, `b ≠ a`, to first order, in the sense
that `u a d(μ a, m_b) + u b d(μ b, m_b) > 0` for the weighted means `m_b` at `w`, gives an
allocation `w + t u` of the simplex at which the cost of the alternatives is larger. -/
private lemma exists_mem_simplex_altCost_baiTask_restrict_lt (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) {b₀ : α} (hb₀ : b₀ ≠ a) (hw : ∀ c, 0 < w c) (hw1 : ∑ c, w c = 1)
    {u : α → ℝ} (hu_sum : ∑ c, u c = 0)
    (hu : ∀ b ≠ a,
      0 < u a * ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) +
        u b * ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))) :
    ∃ v ∈ simplex α,
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a <
        ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ v a := by
  classical
  have hmem {b : α} : b ∈ univ.filter (· ≠ a) ↔ b ≠ a := by simp
  -- The allocations `w + t u`, and the first-order increase `G b t` of the cost of the pair
  -- `(a, b)`, evaluated at the weighted mean of `w + t u`.
  set v : ℝ → α → ℝ := fun t c ↦ w c + t * u c with hv_def
  have hv_cont (c : α) : ContinuousAt (fun t ↦ v t c) 0 := by fun_prop
  set G : α → ℝ → ℝ := fun b t ↦
    u a * ρ.expFamilyDiv T (μ a) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
      u b * ρ.expFamilyDiv T (μ b) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) with hG_def
  have hG_cont (b : α) : ContinuousAt (G b) 0 := by
    have hW : 0 < w a + w b := add_pos (hw a) (hw b)
    have hp : ContinuousAt (fun t ↦ (v t a, v t b)) 0 := (hv_cont a).prodMk (hv_cont b)
    have hp0 : (v 0 a, v 0 b) = (w a, w b) := by simp [hv_def]
    exact (continuousAt_const.mul ((continuousAt_expFamilyDiv_div hT (hμ a) (hμ a) (hμ b)
        (hw a).le (hw b).le hW).comp_of_eq hp hp0)).add
      (continuousAt_const.mul ((continuousAt_expFamilyDiv_div hT (hμ b) (hμ a) (hμ b)
        (hw a).le (hw b).le hW).comp_of_eq hp hp0))
  -- For small `t > 0`, `w + t u` has positive entries and every `G b t` is positive.
  have h_ev : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ c, 0 < v t c) ∧ ∀ b ∈ univ.filter (· ≠ a), 0 < G b t := by
    refine (eventually_all.2 fun c ↦ (hv_cont c).eventually (lt_mem_nhds ?_)).and
      ((eventually_all_finset _).2 fun b hb ↦ (hG_cont b).eventually (lt_mem_nhds ?_))
    · simpa [hv_def] using hw c
    · simpa [hG_def, hv_def] using hu b (hmem.1 hb)
  obtain ⟨t, ⟨hv_pos, hG_pos⟩, ht⟩ :=
    ((h_ev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  rw [Set.mem_Ioi] at ht
  refine ⟨v t, mem_simplex_iff.2 ⟨fun c ↦ (hv_pos c).le, ?_⟩, ?_⟩
  · simp only [hv_def, sum_add_distrib, ← mul_sum, hu_sum, mul_zero, add_zero, hw1]
  -- The cost of the pair `(a, b)` at `w + t u` is `w a d(μ a, m'_b) + w b d(μ b, m'_b) + t G b t`
  -- for the weighted mean `m'_b` at `w + t u`, and the first two terms are at least the cost of
  -- the pair at `w`.
  have h_lt {b : α} (hba : b ≠ a) :
      ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) <
        ρ.expFamilyPairCost T (μ a) (μ b) (v t a) (v t b) := by
    have h_le := expFamilyPairCost_le_of_mem_expFamilyMeans (hμ a) (hμ b) (hw a).le (hw b).le
      (div_mem_expFamilyMeans (hμ a) (hμ b) (hv_pos a).le (hv_pos b).le
        (add_pos (hv_pos a) (hv_pos b)))
    have h_eq : w a * ρ.expFamilyDiv T (μ a) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
        w b * ρ.expFamilyDiv T (μ b) ((v t a * μ a + v t b * μ b) / (v t a + v t b)) +
          t * G b t = ρ.expFamilyPairCost T (μ a) (μ b) (v t a) (v t b) := by
      rw [expFamilyPairCost_def]
      simp only [hG_def, hv_def]
      ring
    linarith [mul_pos ht (hG_pos b (hmem.2 hba))]
  -- So every pair costs more at `w + t u` than the cost of the alternatives at `w`, which is
  -- finite since there is a pair `(a, b₀)`.
  rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha fun c ↦ (hw c).le,
    altCost_baiTask_restrict_eq_inf ν hT hμ hν ha fun c ↦ (hv_pos c).le,
    Finset.lt_inf_iff ((Finset.inf_le (hmem.2 hb₀)).trans_lt ENNReal.ofReal_lt_top)]
  intro b hb
  refine (Finset.inf_le hb).trans_lt ((ENNReal.ofReal_lt_ofReal_iff ?_).2 (h_lt (hmem.1 hb)))
  exact (expFamilyPairCost_nonneg (hμ a) (hμ b) (hw a).le (hw b).le).trans_lt (h_lt (hmem.1 hb))

variable [DecidableEq α]

/-- **The optimal allocation solves the scalar equation** [GK16, Theorem 5]. For arms in an
exponential family with divergence `d` (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`),
a vector of means `μ` of the family with unique best arm `a` and at least one other arm `b₀`, the
optimal allocation `w` satisfies `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`. -/
theorem sum_div_eq_one_of_mem_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) {b₀ : α} (hb₀ : b₀ ≠ a)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a) :
    ∑ b ∈ univ.erase a, ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
      ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1 := by
  obtain ⟨hws, hwD⟩ := (IdentTask.mem_optAlloc_iff _).1 hw
  have hw1 := (mem_simplex_iff.1 hws).2
  have hpos := pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw
  have hmem {b : α} : b ∈ univ.erase a ↔ b ≠ a := by simp
  -- The divergences `A b = d(μ a, m_b)` and `B b = d(μ b, m_b) > 0` at `w`.
  set A : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b))
  set B : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))
  have hB {b : α} (hba : b ≠ a) : 0 < B b :=
    expFamilyDiv_div_pos (hμ a) (hμ b) (ha b hba).ne' (hpos a) (hpos b).le
  set F := ∑ b ∈ univ.erase a, A b / B b with hF_def
  set S := ∑ b ∈ univ.erase a, 1 / B b with hS_def
  by_contra hF
  have hF1 : F - 1 ≠ 0 := sub_ne_zero.2 hF
  -- If `F ≠ 1`, the direction `u` with `u a = S / (F - 1)` and `u a A b + u b B b = 1` for every
  -- `b ≠ a` keeps the sum of the weights, and increases the cost of every pair to first order.
  set u : α → ℝ := fun c ↦ if c = a then S / (F - 1) else (1 - A c * (S / (F - 1))) / B c
    with hu_def
  have hua : u a = S / (F - 1) := by simp [hu_def]
  have hu_b {b : α} (hba : b ≠ a) : u a * A b + u b * B b = 1 := by
    rw [hua]
    simp only [hu_def, hba, ↓reduceIte]
    field_simp [(hB hba).ne']
    ring
  have hu_sum : ∑ c, u c = 0 := by
    rw [← add_sum_erase _ _ (mem_univ a), hua]
    have h_erase : ∑ c ∈ univ.erase a, u c =
        ∑ c ∈ univ.erase a, (1 / B c - S / (F - 1) * (A c / B c)) := by
      refine sum_congr rfl fun c hc ↦ ?_
      have hca := hmem.1 hc
      simp only [hu_def, hca, ↓reduceIte]
      field_simp [(hB hca).ne']
    rw [h_erase, sum_sub_distrib, ← mul_sum, ← hS_def, ← hF_def]
    field_simp
    ring
  -- So `w` is not optimal.
  obtain ⟨v, hv, h_lt⟩ := exists_mem_simplex_altCost_baiTask_restrict_lt ν hT hμ hν
    (apply_le_of_forall_ne_lt ha) hb₀ hpos hw1 hu_sum fun b hba ↦ (hu_b hba).symm ▸ one_pos
  exact (IdentTask.altCost_le_answerValue _ hv).not_gt (hwD ▸ h_lt)

/-- **An allocation solving the scalar equation is optimal** [GK16, Theorem 5]. For arms in an
exponential family with divergence `d` (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`)
and a vector of means `μ` of the family with unique best arm `a`, an allocation `w` of the simplex
with `w a > 0` that equalizes the costs `w a d(μ a, m_b) + w b d(μ b, m_b)` of the pairs `(a, b)`,
`b ≠ a`, and satisfies `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`, is an optimal allocation. -/
theorem mem_optAlloc_baiTask_restrict_of_sum_div_eq_one (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hw : w ∈ simplex α) (hwa : 0 < w a)
    (h_eq : ∀ b ≠ a, ∀ c ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) =
      ρ.expFamilyPairCost T (μ a) (μ c) (w a) (w c))
    (h_sum : ∑ b ∈ univ.erase a,
      ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
        ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1) :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a := by
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hw
  have hmem {b : α} : b ∈ univ.erase a ↔ b ≠ a := by simp
  have h_filter : univ.filter (· ≠ a) = univ.erase a := filter_ne' univ a
  -- The sum is not empty, since it equals `1`.
  obtain ⟨b₀, hb₀⟩ := nonempty_of_sum_ne_zero (h_sum ▸ one_ne_zero)
  set A : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b))
  set B : α → ℝ := fun b ↦ ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))
  have hB {b : α} (hba : b ≠ a) : 0 < B b :=
    expFamilyDiv_div_pos (hμ a) (hμ b) (ha b hba).ne' hwa (hw0 b)
  -- For every allocation `x`, the combination of the linear bounds `x a A b + x b B b` on the
  -- costs of the pairs with the weights `1 / B b` is `x a ∑_{b ≠ a} A b / B b + ∑_{b ≠ a} x b = 1`.
  have h_comb (x : α → ℝ) (hx : ∑ c, x c = 1) :
      ∑ b ∈ univ.erase a, (x a * A b + x b * B b) / B b = 1 := by
    have h : ∀ b ∈ univ.erase a, (x a * A b + x b * B b) / B b = x a * (A b / B b) + x b :=
      fun b hb ↦ by field_simp [(hB (hmem.1 hb)).ne']
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, h_sum, mul_one,
      sum_erase_eq_sub (mem_univ a), hx]
    ring
  -- The common value `D` of the costs of the pairs at `w`, at which the linear bounds are tight.
  set D := ρ.expFamilyPairCost T (μ a) (μ b₀) (w a) (w b₀)
  have hD {b : α} (hba : b ≠ a) : ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) = D :=
    h_eq b hba b₀ (hmem.1 hb₀)
  have hD_sum : ∑ b ∈ univ.erase a, D / B b = 1 := by
    rw [← h_comb w hw1]
    refine sum_congr rfl fun b hb ↦ ?_
    rw [← hD (hmem.1 hb), expFamilyPairCost_def]
  rw [IdentTask.mem_optAlloc_iff_isMaxOn]
  refine ⟨hw, isMaxOn_iff.2 fun v hv ↦ ?_⟩
  obtain ⟨hv0, hv1⟩ := mem_simplex_iff.1 hv
  -- Some pair costs at most `D` at `v`, otherwise the combination of the linear bounds at `v`
  -- would exceed its value `1` at `w`.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (v a) (v b) ≤ D := by
    by_contra! h
    have h_lt : ∑ b ∈ univ.erase a, D / B b <
        ∑ b ∈ univ.erase a, (v a * A b + v b * B b) / B b := by
      refine sum_lt_sum_of_nonempty ⟨b₀, hb₀⟩ fun b hb ↦ ?_
      have hba := hmem.1 hb
      refine div_lt_div_of_pos_right ((h b hba).trans_le ?_) (hB hba)
      exact expFamilyPairCost_le_of_mem_expFamilyMeans (hμ a) (hμ b) (hv0 a) (hv0 b)
        (div_mem_expFamilyMeans (hμ a) (hμ b) (hw0 a) (hw0 b)
          (add_pos_of_pos_of_nonneg hwa (hw0 b)))
    rw [hD_sum, h_comb v hv1] at h_lt
    exact h_lt.false
  rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hv0,
    altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0]
  refine (Finset.inf_le (h_filter ▸ hmem.2 hba)).trans (Finset.le_inf fun c hc ↦ ?_)
  rw [hD (mem_filter.1 hc).2]
  exact ENNReal.ofReal_le_ofReal hb

/-- **The optimal allocation of best arm identification from a scalar equation**
[GK16, Theorem 5]. For arms in an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means `μ` of the family with
unique best arm `a` and at least one other arm `b₀`, an allocation `w` is optimal if and only if it
is in the simplex, `w a > 0`, the costs `w a d(μ a, m_b) + w b d(μ b, m_b)` of the pairs `(a, b)`,
`b ≠ a`, are equal, and `∑_{b ≠ a} d(μ a, m_b) / d(μ b, m_b) = 1`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)`. Written with `x = w / w a`, this is the equation
`F(y) = 1` of [GK16, Theorem 5] for the common value `y` of `d(μ a, m_b) + x b d(μ b, m_b)`. -/
theorem mem_optAlloc_baiTask_restrict_iff (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) {b₀ : α} (hb₀ : b₀ ≠ a) :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ a ↔
      w ∈ simplex α ∧ 0 < w a ∧
        (∀ b ≠ a, ∀ c ≠ a, ρ.expFamilyPairCost T (μ a) (μ b) (w a) (w b) =
          ρ.expFamilyPairCost T (μ a) (μ c) (w a) (w c)) ∧
        ∑ b ∈ univ.erase a,
          ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) /
            ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b)) = 1 := by
  refine ⟨fun hw ↦ ⟨((IdentTask.mem_optAlloc_iff _).1 hw).1,
    pos_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hw a, fun b hba c hca ↦ ?_,
    sum_div_eq_one_of_mem_optAlloc_baiTask_restrict ν hT hμ hν ha hb₀ hw⟩,
    fun ⟨hws, hwa, h_eq, h_sum⟩ ↦
      mem_optAlloc_baiTask_restrict_of_sum_div_eq_one ν hT hμ hν ha hws hwa h_eq h_sum⟩
  have hw0 := (mem_simplex_iff.1 ((IdentTask.mem_optAlloc_iff _).1 hw).1).1
  refine (ENNReal.ofReal_eq_ofReal_iff (expFamilyPairCost_nonneg (hμ a) (hμ b) (hw0 a) (hw0 b))
    (expFamilyPairCost_nonneg (hμ a) (hμ c) (hw0 a) (hw0 c))).1 ?_
  rw [← answerValue_baiTask_restrict_eq_of_mem_optAlloc ν hT hμ hν ha hw hba,
    answerValue_baiTask_restrict_eq_of_mem_optAlloc ν hT hμ hν ha hw hca]

end ScalarEquation

end ExpFamily

section Gaussian

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {μ w : α → ℝ} {σ2 : ℝ≥0}

/-- **The cost of the alternatives in Gaussian best arm identification** [GK16, Section 2.2]. For
Gaussian arms with a common variance `σ2 ≠ 0`, a best arm `a` of `μ` and a nonnegative allocation
`w`, `D(μ, w, ¬a) = min_{b ≠ a} (w a w b / (w a + w b)) (μ a - μ b)² / (2 σ2)`. -/
theorem altCost_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0) (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    (baiTask (Bandits.gaussianBandit · σ2) id).altCost μ w a =
      ⨅ (b) (_ : b ≠ a),
        ENNReal.ofReal (w a * w b / (w a + w b) * (μ a - μ b) ^ 2 / (2 * σ2)) := by
  rw [← (baiTask (Bandits.gaussianBandit · σ2) id).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    altCost_baiTask_restrict_eq_iInf_expFamilyPairCost _ (not_ae_eq_const_gaussianReal 0 hσ2)
      (fun c ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 (μ c))
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ') ha hw]
  refine iInf_congr fun b ↦ iInf_congr fun _ ↦ congrArg ENNReal.ofReal ?_
  have hσ2' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
  have hwa : 0 ≤ w a := hw a
  have hwb : 0 ≤ w b := hw b
  rw [expFamilyPairCost_def, expFamilyDiv_gaussianReal 0 hσ2, expFamilyDiv_gaussianReal 0 hσ2]
  rcases eq_or_ne (w a + w b) 0 with hW | hW
  · obtain ⟨hwa, hwb⟩ : w a = 0 ∧ w b = 0 := ⟨by linarith, by linarith⟩
    simp [hwa, hwb]
  · field_simp
    ring

/-! #### Two Gaussian arms -/

variable {b : α}

/-- **The game value of two Gaussian arms** [KCG16, Section 3]. For two Gaussian arms `a` and `b`
with a common variance `σ2 ≠ 0` and `μ b ≤ μ a`, `D(μ, ¬a) = (μ a - μ b)² / (8 σ2)`: the mean at
the same divergence from `μ a` and `μ b` is `(μ a + μ b) / 2`. -/
theorem answerValue_baiTask_gaussianBandit_of_forall_eq_or_eq (hσ2 : σ2 ≠ 0) (hba : b ≠ a)
    (hα : ∀ c, c = a ∨ c = b) (hμ : μ b ≤ μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).answerValue μ a =
      ENNReal.ofReal ((μ a - μ b) ^ 2 / (8 * σ2)) := by
  have hσ2' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
  rw [← (baiTask (Bandits.gaussianBandit · σ2) id).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq _
      (not_ae_eq_const_gaussianReal 0 hσ2) (fun c ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 (μ c))
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ') hba hα hμ
      (z := (μ a + μ b) / 2) ⟨by linarith, by linarith⟩
      (by rw [expFamilyDiv_gaussianReal 0 hσ2, expFamilyDiv_gaussianReal 0 hσ2]; ring),
    expFamilyDiv_gaussianReal 0 hσ2]
  congr 1
  field_simp
  ring

/-- **The characteristic time of two Gaussian arms** [KCG16, Section 3]. For two Gaussian arms `a`
and `b` with a common variance `σ2 ≠ 0` and `μ b < μ a`, `T*(μ) = 8 σ2 / (μ a - μ b)²`. -/
theorem charTime_baiTask_gaussianBandit_of_forall_eq_or_eq (hσ2 : σ2 ≠ 0) (hba : b ≠ a)
    (hα : ∀ c, c = a ∨ c = b) (hμ : μ b < μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).charTime μ =
      ENNReal.ofReal (8 * σ2 / (μ a - μ b) ^ 2) := by
  have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  have hΔ : 0 < (μ a - μ b) ^ 2 := pow_pos (sub_pos.2 hμ) 2
  rw [IdentTask.charTime_eq_inv_answerValue _ (correct_baiTask_of_forall_eq_or_eq _ hα hμ),
    answerValue_baiTask_gaussianBandit_of_forall_eq_or_eq hσ2 hba hα hμ.le,
    ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]

/-- **The optimal allocation of two Gaussian arms** [KCG16, Section 3]. For two Gaussian arms `a`
and `b` with a common variance `σ2 ≠ 0` and `μ b < μ a`, the only optimal allocation is
`w*(μ, ¬a) = (1/2, 1/2)`. -/
theorem optAlloc_baiTask_gaussianBandit_of_forall_eq_or_eq (hσ2 : σ2 ≠ 0) (hba : b ≠ a)
    (hα : ∀ c, c = a ∨ c = b) (hμ : μ b < μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc μ a = {fun _ ↦ 1 / 2} := by
  have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  have ha := apply_le_of_forall_eq_or_eq hα hμ.le
  -- With two arms, the cost of the alternatives is `w a w b (μ a - μ b)² / (2 σ2)`.
  have h_alt {w : α → ℝ} (hw : w ∈ simplex α) :
      (baiTask (Bandits.gaussianBandit · σ2) id).altCost μ w a =
        ENNReal.ofReal (w a * w b * (μ a - μ b) ^ 2 / (2 * σ2)) := by
    rw [altCost_baiTask_gaussianBandit hσ2 ha fun c ↦ (mem_simplex_iff.1 hw).1 c,
      iInf_ne_eq_of_forall_eq_or_eq hba hα, add_eq_one_of_mem_simplex hba.symm hα hw, div_one]
  have h_half : (fun _ ↦ 1 / 2 : α → ℝ) ∈ simplex α :=
    mem_simplex_iff.2 ⟨fun _ ↦ by norm_num, by
      rw [Fintype.sum_eq_add a b hba.symm fun c hc ↦ absurd (hα c) (not_or.2 hc)]; norm_num⟩
  ext w
  rw [IdentTask.mem_optAlloc_iff, Set.mem_singleton_iff,
    answerValue_baiTask_gaussianBandit_of_forall_eq_or_eq hσ2 hba hα hμ.le]
  constructor
  · rintro ⟨hw, h⟩
    have hwa : 0 ≤ w a := (mem_simplex_iff.1 hw).1 a
    have hwb : 0 ≤ w b := (mem_simplex_iff.1 hw).1 b
    have hsum := add_eq_one_of_mem_simplex hba.symm hα hw
    rw [h_alt hw, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h
    -- The equality `w a w b = 1 / 4` with `w a + w b = 1` forces `w a = w b = 1 / 2`.
    have hD : 0 < (μ a - μ b) ^ 2 / (2 * σ2) := by
      have := pow_pos (sub_pos.2 hμ) 2
      positivity
    have hprod : w a * w b = 1 / 4 := mul_right_cancel₀ hD.ne' (by convert h using 1 <;> ring)
    have hab : w a = w b := by nlinarith [sq_nonneg (w a - w b)]
    funext c
    rcases hα c with rfl | rfl <;> linarith
  · rintro rfl
    refine ⟨h_half, ?_⟩
    rw [h_alt h_half]
    congr 1
    ring

/-! #### The complexity `H(μ)` -/

variable [DecidableEq α] {b₀ : α}

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Replacing the arm `a` by an arm `b₀ ≠ a` gives an arm other than `a`. -/
private lemma ite_ne (hb₀a : b₀ ≠ a) (c : α) : (if c = a then b₀ else c) ≠ a := by
  split_ifs with hc
  exacts [hb₀a, hc]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- If `a` is the unique best arm of `μ`, then the squared gaps `Δ_c²`, with `Δ_a = Δ_{b₀}`, are
positive. -/
private lemma sq_sub_ite_pos (hb₀a : b₀ ≠ a) (ha : ∀ b ≠ a, μ b < μ a) (c : α) :
    0 < (μ a - μ (if c = a then b₀ else c)) ^ 2 :=
  pow_pos (sub_pos.2 (ha _ (ite_ne hb₀a c))) 2

omit [MeasurableSingletonClass α] in
/-- The complexity `H(μ) = ∑ c, 2 σ2 / Δ_c²`, where the gap `Δ_a` of `a` is that of `b₀`, as a
single sum over the arms. -/
private lemma sum_div_sq_ite (σ2 : ℝ) :
    2 * σ2 / (μ a - μ b₀) ^ 2 + ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2 =
      ∑ c, 2 * σ2 / (μ a - μ (if c = a then b₀ else c)) ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun c hc ↦ by simp [Finset.ne_of_mem_erase hc]

omit [MeasurableSingletonClass α] in
/-- The complexity `H(μ)` of a vector of means with unique best arm `a` is positive. -/
private lemma sum_div_sq_pos (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a) (ha : ∀ b ≠ a, μ b < μ a) :
    0 < 2 * σ2 / (μ a - μ b₀) ^ 2 + ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2 :=
  add_pos_of_pos_of_nonneg (div_pos (by positivity) (pow_pos (sub_pos.2 (ha b₀ hb₀a)) 2))
    (Finset.sum_nonneg fun _ _ ↦ by positivity)

omit [MeasurableSingletonClass α] in
/-- The complexity `H(μ)` of a vector of means with unique best arm `a`, as a single sum over the
arms, is positive. -/
private lemma sum_div_sq_ite_pos (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a) (ha : ∀ b ≠ a, μ b < μ a) :
    0 < ∑ c, 2 * σ2 / (μ a - μ (if c = a then b₀ else c)) ^ 2 := by
  rw [← sum_div_sq_ite]
  exact sum_div_sq_pos hσ2 hb₀a ha

/-- **Upper bound on the game value of Gaussian best arm identification** [GK16, Section 2.2]. For
Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of `μ` and an arm `b₀ ≠ a`,
`D(μ, ¬a) ≤ 1 / H(μ)`, where `H(μ) = ∑ c, 2 σ2 / Δ_c²` with the gaps `Δ_b = μ a - μ b` for `b ≠ a`
and `Δ_a = Δ_{b₀}`. The bound is the smallest when `b₀` is a second best arm, for which
`Δ_a = min_{b ≠ a} Δ_b`. -/
theorem answerValue_baiTask_gaussianBandit_le (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).answerValue μ a ≤
      ENNReal.ofReal (2 * σ2 / (μ a - μ b₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2)⁻¹ := by
  have hH := sum_div_sq_ite_pos hσ2 hb₀a ha
  rw [sum_div_sq_ite]
  set s : α → α := fun c ↦ if c = a then b₀ else c
  set H := ∑ c, 2 * σ2 / (μ a - μ (s c)) ^ 2
  have hs (c : α) : s c ≠ a := ite_ne hb₀a c
  rw [IdentTask.answerValue_def]
  refine iSup₂_le fun w hw ↦ ?_
  obtain ⟨hw_nonneg, hw_sum⟩ := mem_simplex_iff.1 hw
  rw [altCost_baiTask_gaussianBandit hσ2 (apply_le_of_forall_ne_lt ha) hw_nonneg]
  -- Since `∑ c, w c = 1 = ∑ c, (2 σ2 / Δ_c²) / H`, some arm `c` has `w c ≤ (2 σ2 / Δ_c²) / H`.
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le ⟨a, Finset.mem_univ a⟩
    (f := w) (g := fun c ↦ 2 * σ2 / (μ a - μ (s c)) ^ 2 / H) (by
      rw [hw_sum, ← Finset.sum_div, div_self hH.ne'])
  -- The cost of the alternatives with best arm `s c` is at most `w c Δ_c² / (2 σ2) ≤ 1 / H`, since
  -- `w a w b / (w a + w b)` is at most `w a` and `w b`, and `c` is `a` or `s c`.
  refine (iInf₂_le (s c) (hs c)).trans (ENNReal.ofReal_le_ofReal ?_)
  have h_le : w a * w (s c) / (w a + w (s c)) ≤ w c := by
    by_cases hca : c = a
    · subst hca
      exact mul_div_add_le_left (hw_nonneg _) (hw_nonneg _)
    · rw [show s c = c by simp [s, hca]]
      exact mul_div_add_le_right (hw_nonneg _) (hw_nonneg _)
  have hΔ : μ a - μ (s c) ≠ 0 := (sub_pos.2 (ha _ (hs c))).ne'
  calc w a * w (s c) / (w a + w (s c)) * (μ a - μ (s c)) ^ 2 / (2 * σ2)
  _ ≤ 2 * σ2 / (μ a - μ (s c)) ^ 2 / H * (μ a - μ (s c)) ^ 2 / (2 * σ2) := by
    gcongr ?_ * _ / _
    exact h_le.trans hc
  _ = H⁻¹ := by
    field_simp

/-- **Lower bound on the game value of Gaussian best arm identification** [GK16, Section 2.2]. For
Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of `μ` and a second best arm
`b₀`, `1 / (2 H(μ)) ≤ D(μ, ¬a)`, where `H(μ) = ∑ c, 2 σ2 / Δ_c²` with the gaps `Δ_b = μ a - μ b`
for `b ≠ a` and `Δ_a = Δ_{b₀} = min_{b ≠ a} Δ_b`. -/
theorem le_answerValue_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) (hb₀ : ∀ b ≠ a, μ b ≤ μ b₀) :
    ENNReal.ofReal (2 * (2 * σ2 / (μ a - μ b₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2))⁻¹ ≤
      (baiTask (Bandits.gaussianBandit · σ2) id).answerValue μ a := by
  have hH := sum_div_sq_ite_pos hσ2 hb₀a ha
  rw [sum_div_sq_ite]
  set s : α → α := fun c ↦ if c = a then b₀ else c
  set H := ∑ c, 2 * σ2 / (μ a - μ (s c)) ^ 2
  have hΔ (c : α) : 0 < (μ a - μ (s c)) ^ 2 := sq_sub_ite_pos hb₀a ha c
  have hsa : s a = b₀ := by simp [s]
  -- The allocation proportional to `Δ_c⁻²`.
  set w : α → ℝ := fun c ↦ 2 * σ2 / (μ a - μ (s c)) ^ 2 / H with hw_def
  have hw : w ∈ simplex α := mem_simplex_iff.2
    ⟨fun c ↦ by have := hΔ c; positivity, by rw [← Finset.sum_div, div_self hH.ne']⟩
  refine le_trans ?_ (IdentTask.altCost_le_answerValue _ hw)
  rw [altCost_baiTask_gaussianBandit hσ2 (apply_le_of_forall_ne_lt ha) (mem_simplex_iff.1 hw).1]
  refine le_iInf₂ fun b hb ↦ ENNReal.ofReal_le_ofReal ?_
  -- With `x = Δ_a² ≤ y = Δ_b²`, the cost of `b` is `y / (H (x + y)) ≥ 1 / (2 H)`.
  have hsb : s b = b := by simp [s, hb]
  have hx := hΔ a
  have hy := hΔ b
  rw [hsa] at hx
  rw [hsb] at hy
  have hxy : (μ a - μ b₀) ^ 2 ≤ (μ a - μ b) ^ 2 :=
    pow_le_pow_left₀ (sub_pos.2 (ha b₀ hb₀a)).le (by linarith [hb₀ b hb]) 2
  have key : w a * w b / (w a + w b) * (μ a - μ b) ^ 2 / (2 * σ2) =
      (μ a - μ b) ^ 2 / (H * ((μ a - μ b₀) ^ 2 + (μ a - μ b) ^ 2)) := by
    simp only [hw_def, hsa, hsb]
    generalize (μ a - μ b₀) ^ 2 = x at hx
    generalize (μ a - μ b) ^ 2 = y at hy
    field_simp
    ring
  rw [key, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Lower bound on the characteristic time of Gaussian best arm identification**
[GK16, Section 2.2]. For Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of
`μ` and an arm `b₀ ≠ a`, `H(μ) ≤ T*(μ)`, where `H(μ) = ∑ c, 2 σ2 / Δ_c²` with the gaps
`Δ_b = μ a - μ b` for `b ≠ a` and `Δ_a = Δ_{b₀}`. The bound is the largest when `b₀` is a second
best arm, for which `Δ_a = min_{b ≠ a} Δ_b`. -/
theorem le_charTime_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) :
    ENNReal.ofReal (2 * σ2 / (μ a - μ b₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2) ≤
      (baiTask (Bandits.gaussianBandit · σ2) id).charTime μ := by
  rw [charTime_baiTask_eq_inv_answerValue _ id ha,
    ← inv_inv (ENNReal.ofReal _), ← ENNReal.ofReal_inv_of_pos (sum_div_sq_pos hσ2 hb₀a ha),
    ENNReal.inv_le_inv]
  exact answerValue_baiTask_gaussianBandit_le hσ2 hb₀a ha

/-- **Upper bound on the characteristic time of Gaussian best arm identification**
[GK16, Section 2.2]. For Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of
`μ` and a second best arm `b₀`, `T*(μ) ≤ 2 H(μ)`, where `H(μ) = ∑ c, 2 σ2 / Δ_c²` with the gaps
`Δ_b = μ a - μ b` for `b ≠ a` and `Δ_a = Δ_{b₀} = min_{b ≠ a} Δ_b`. -/
theorem charTime_baiTask_gaussianBandit_le (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) (hb₀ : ∀ b ≠ a, μ b ≤ μ b₀) :
    (baiTask (Bandits.gaussianBandit · σ2) id).charTime μ ≤
      ENNReal.ofReal (2 * (2 * σ2 / (μ a - μ b₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2)) := by
  rw [charTime_baiTask_eq_inv_answerValue _ id ha,
    ← inv_inv (ENNReal.ofReal (2 * _)),
    ← ENNReal.ofReal_inv_of_pos (mul_pos two_pos (sum_div_sq_pos hσ2 hb₀a ha)), ENNReal.inv_le_inv]
  exact le_answerValue_baiTask_gaussianBandit hσ2 hb₀a ha hb₀

omit [DecidableEq α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of `μ` and another arm
`b₀ ≠ a`, the characteristic time `T*(μ)` is positive: it is at least `H(μ) > 0`. -/
theorem charTime_baiTask_gaussianBandit_ne_zero (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).charTime μ ≠ 0 := by
  classical
  exact ((ENNReal.ofReal_pos.2 (sum_div_sq_pos hσ2 hb₀a ha)).trans_le
      (le_charTime_baiTask_gaussianBandit hσ2 hb₀a ha)).ne'

omit [DecidableEq α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of `μ` and another arm
`b₀ ≠ a`, the characteristic time `T*(μ)` is finite: it is at most `2 H(μ)` for a second best
arm. -/
theorem charTime_baiTask_gaussianBandit_ne_top (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) :
    (baiTask (Bandits.gaussianBandit · σ2) id).charTime μ ≠ ∞ := by
  classical
  obtain ⟨b₁, hb₁, hb₁max⟩ :=
    (Finset.univ.erase a).exists_max_image μ ⟨b₀, Finset.mem_erase.2 ⟨hb₀a, Finset.mem_univ _⟩⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (charTime_baiTask_gaussianBandit_le hσ2
    (Finset.ne_of_mem_erase hb₁) ha fun b hb ↦
      hb₁max b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩))

end Gaussian

end LMLExplore.Identification
