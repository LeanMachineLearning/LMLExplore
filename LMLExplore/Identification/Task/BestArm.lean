/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.MeanVector
public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Bandits.Instances
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian
public import LMLExplore.Order.Basic
public import LMLExplore.Order.CompleteLattice.Basic
public import LMLExplore.Algebra.Order.Field.Basic

/-!
# The alternatives of best arm identification and the cost of the alternatives

For best arm identification (`baiTask ν`), the alternatives to an arm `a` are the vectors of means
with a unique best arm `b ≠ a`. This set is not closed: its limits include the vectors where `a`
ties with another best arm, which have no correct answer. The cost of the alternatives
`D(μ, w, ¬a) = inf_{λ ∈ ¬a} ∑ b, w b KL(ν_b(μ), ν_b(λ))` is an infimum over this set, and the
analysis of best arm identification of Garivier and Kaufmann (2016) computes it on the closed set
`{λ | ∃ b ≠ a, λ a ≤ λ b}` of the vectors whose largest mean is attained at an arm `b ≠ a`, one
arm `b` at a time.

The admissible models of an identification problem are the vectors whose means lie in the mean
sets of the arm families (the means of an exponential family form an open interval), that is
`(baiTask ν).restrict S` for an open set `S` of vectors of means. Within `S`, the closure of the
alternatives to `a` is the closed set above, and when the transportation cost is continuous there,
the cost of the alternatives is the infimum of the cost over it.

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
  correct, those with unique best arm `a`, form an open set.
* `LMLExplore.Identification.closure_alt_baiTask_restrict_inter`: for `S` open, the closure of the
  alternatives to `a` within `S` is `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`;
  `LMLExplore.Identification.closure_alt_baiTask` is the case `S = univ`.
* `LMLExplore.Identification.charTime_baiTask_eq_inv_answerValue`,
  `LMLExplore.Identification.charTime_baiTask_restrict_eq_inv_answerValue`: if `a` is the unique
  best arm of `μ`, then `T*(μ) = D(μ, ¬a)⁻¹`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf`: for `S` open and a transportation
  cost continuous on `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`,
  `D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf_expFamilyDiv`: for arms in an
  exponential family with divergence `d`, a best arm `a` of `μ` and a nonnegative allocation `w`,
  `D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` on the vectors of means of the
  family, with `m_b = (w a μ a + w b μ b) / (w a + w b)` [GK16, Lemma 3].
* `LMLExplore.Identification.continuousOn_altCost_baiTask_restrict`: for arms in an exponential
  family, `(μ, w) ↦ D(μ, w, ¬a)` is continuous on the vectors of means of the family with best arm
  `a` and the nonnegative allocations.
* `LMLExplore.Identification.continuousAt_answerValue_baiTask_restrict`,
  `LMLExplore.Identification.upperHemicontinuousAt_optAlloc_baiTask_restrict`,
  `LMLExplore.Identification.continuousAt_charTime_baiTask_restrict`: for arms in an exponential
  family, at a vector of means with unique best arm `a`, `D(·, ¬a)` and `T*` are continuous and the
  optimal allocations `w*(·, ¬a)` are upper hemicontinuous [DK19, Lemmas 28–29].
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
* `LMLExplore.Identification.le_answerValue_baiTask_gaussianBandit`,
  `LMLExplore.Identification.answerValue_baiTask_gaussianBandit_le`: the same bounds on the value,
  `1 / (2 H(μ)) ≤ D(μ, ¬a) ≤ 1 / H(μ)`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2, Lemmas 3–4 and Proposition 6.
* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Section 3.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Lemmas 28 and 29.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {S : Set (α → ℝ)} {a : α}
  {μ' : α → ℝ}

/-- The alternatives to the arm `a` in best arm identification are the vectors of means with a
unique best arm `b ≠ a`. -/
lemma mem_alt_baiTask_iff : μ' ∈ (baiTask ν).alt a ↔ ∃ b ≠ a, ∀ c ≠ b, μ' c < μ' b := by
  simp only [IdentTask.mem_alt_iff, M_baiTask, correct_baiTask, Set.mem_ofPred_eq, not_forall,
    not_lt, exists_prop]
  constructor
  · rintro ⟨⟨b, hb⟩, c, hca, hc⟩
    refine ⟨b, ?_, hb⟩
    rintro rfl
    exact (hb c hca).not_ge hc
  · rintro ⟨b, hba, hb⟩
    exact ⟨⟨b, hb⟩, b, hba, (hb a hba.symm).le⟩

/-- The vectors of means for which the arm `a` is correct in best arm identification are those
with unique best arm `a`. -/
lemma mem_answerSet_baiTask_iff : μ' ∈ (baiTask ν).answerSet a ↔ ∀ b ≠ a, μ' b < μ' a := by
  rw [IdentTask.mem_answerSet_iff, M_baiTask, correct_baiTask]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨a, h⟩, h⟩⟩

/-- The vectors of means with unique best arm `a` form an open set. -/
lemma isOpen_answerSet_baiTask [Finite α] (a : α) : IsOpen ((baiTask ν).answerSet a) := by
  have h : (baiTask ν).answerSet a = ⋂ b ∈ ({a}ᶜ : Set α), {μ' | μ' b < μ' a} := by
    ext μ'
    rw [mem_answerSet_baiTask_iff]
    simp
  rw [h]
  exact (Set.toFinite _).isOpen_biInter fun b _ ↦
    isOpen_lt (continuous_apply b) (continuous_apply a)

section Closure

variable [Finite α]

/-- For a neighbourhood `S` of a vector of means `μ'` in which some arm `b ≠ a` has mean at least
that of `a`, the vector `μ'` lies in the closure of the alternatives to `a` of
`(baiTask ν).restrict S`. -/
lemma mem_closure_alt_baiTask_restrict (hS : S ∈ 𝓝 μ')
    (hμ' : ∃ b ≠ a, μ' a ≤ μ' b) : μ' ∈ closure (((baiTask ν).restrict S).alt a) := by
  classical
  -- An arm `b ≠ a` with the largest mean.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, ∀ c, μ' c ≤ μ' b := by
    obtain ⟨b, hba, hab⟩ := hμ'
    have : Nonempty α := ⟨a⟩
    obtain ⟨d, hd⟩ := Finite.exists_max μ'
    by_cases hda : d = a
    · exact ⟨b, hba, fun c ↦ (hda ▸ hd c).trans hab⟩
    · exact ⟨d, hda, hd⟩
  -- The path `t ↦ μ' + t • Pi.single b 1` tends to `μ'` and lies in the alternatives for small
  -- `t > 0`: raising the largest mean makes `b` the unique best arm.
  set f : ℝ → α → ℝ := fun t ↦ μ' + t • Pi.single b 1 with hf
  have hf_tendsto : Tendsto f (𝓝[>] 0) (𝓝 μ') := by
    have hf_cont : Continuous f := by fun_prop
    simpa [hf] using hf_cont.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto hf_tendsto ?_
  filter_upwards [hf_tendsto.eventually hS, self_mem_nhdsWithin] with t htS ht
  rw [IdentTask.alt_restrict]
  refine ⟨(mem_alt_baiTask_iff ν).2 ⟨b, hba, fun c hcb ↦ ?_⟩, htS⟩
  simpa [hf, Pi.single_apply, hcb] using (hb c).trans_lt (lt_add_of_pos_right _ ht)

/-- For an open set `S` of vectors of means, the closure within `S` of the alternatives to the arm
`a` in best arm identification restricted to `S` is the set of the vectors of `S` in which some
arm `b ≠ a` has mean at least that of `a`, that is, whose largest mean is attained at an arm
`b ≠ a`. -/
theorem closure_alt_baiTask_restrict_inter (hS : IsOpen S) (a : α) :
    closure (((baiTask ν).restrict S).alt a) ∩ S = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := by
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
  obtain ⟨b, hba, hb⟩ := (mem_alt_baiTask_iff ν).1 hμ''.1
  exact ⟨b, hba, (hb a hba.symm).le⟩

/-- The closure of the alternatives to the arm `a` in best arm identification is the set of the
vectors of means in which some arm `b ≠ a` has mean at least that of `a`, that is, whose largest
mean is attained at an arm `b ≠ a`. -/
theorem closure_alt_baiTask (a : α) :
    closure ((baiTask ν).alt a) = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} := by
  simpa using closure_alt_baiTask_restrict_inter ν isOpen_univ a

end Closure

variable [Fintype α]

/-- If `a` is the unique best arm of `μ'`, then `T*(μ') = D(μ', ¬a)⁻¹` in best arm identification
restricted to any set `S` of vectors of means. -/
theorem charTime_baiTask_restrict_eq_inv_answerValue (S : Set (α → ℝ))
    (ha : ∀ b ≠ a, μ' b < μ' a) :
    ((baiTask ν).restrict S).charTime μ' = (((baiTask ν).restrict S).answerValue μ' a)⁻¹ :=
  IdentTask.charTime_eq_inv_answerValue _ (by
    rw [IdentTask.correct_restrict]
    refine (subsingleton_correct_baiTask ν μ').eq_singleton_of_mem ?_
    rw [correct_baiTask]
    exact ha)

/-- If `a` is the unique best arm of `μ'`, then `T*(μ') = D(μ', ¬a)⁻¹` in best arm
identification. -/
theorem charTime_baiTask_eq_inv_answerValue (ha : ∀ b ≠ a, μ' b < μ' a) :
    (baiTask ν).charTime μ' = ((baiTask ν).answerValue μ' a)⁻¹ :=
  IdentTask.charTime_eq_inv_answerValue _
    ((subsingleton_correct_baiTask ν μ').eq_singleton_of_mem (by rw [correct_baiTask]; exact ha))

/-- For an open set `S` of vectors of means and a transportation cost from `μ` continuous on the
vectors of `S` in which some arm `b ≠ a` has mean at least that of `a`, the cost of the
alternatives to `a` in best arm identification restricted to `S` is
`D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}` [GK16, Section 2]. -/
theorem altCost_baiTask_restrict_eq_iInf (hS : IsOpen S) {μ : α → ℝ} {w : α → ℝ}
    (hc : ContinuousOn ((baiTask ν).cost w μ) ({μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S)) :
    ((baiTask ν).restrict S).altCost μ w a =
      ⨅ (b) (_ : b ≠ a) (μ' ∈ S) (_ : μ' a ≤ μ' b), (baiTask ν).cost w μ μ' := by
  have h_eq := closure_alt_baiTask_restrict_inter ν hS a
  have h_alt : ((baiTask ν).restrict S).alt a ⊆ {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := fun μ' hμ' ↦
    h_eq ▸ ⟨subset_closure hμ', ((baiTask ν).alt_restrict a ▸ hμ').2⟩
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

/-- On the vectors of means of an exponential family, the transportation cost from `μ` to `μ'` is
`∑ c, w c d(μ c, μ' c)` when the divergences between the arm laws are those of the family. -/
private lemma cost_baiTask_eq_ofReal_sum (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ ρ.expFamilyMeans T) :
    (baiTask ν).cost w μ μ' = ENNReal.ofReal (∑ c, w c * ρ.expFamilyDiv T (μ c) (μ' c)) := by
  rw [IdentTask.cost_def, ENNReal.ofReal_sum_of_nonneg fun c _ ↦
    mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [ν_baiTask, hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- Moving the means of two arms `a ≠ b` of `μ` to a common mean `z` of the family gives a vector
of means of the family in which `b` is at least as good as `a`, at transportation cost
`w a d(μ a, z) + w b d(μ b, z)` from `μ`. -/
private lemma iInf_cost_baiTask_le (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hw : 0 ≤ w) {b : α} (hba : b ≠ a) {z : ℝ} (hz : z ∈ ρ.expFamilyMeans T) :
    ⨅ μ' ∈ {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T}, ⨅ (_ : μ' a ≤ μ' b),
        (baiTask ν).cost w μ μ' ≤
      ENNReal.ofReal (w a * ρ.expFamilyDiv T (μ a) z + w b * ρ.expFamilyDiv T (μ b) z) := by
  classical
  set μ' := Function.update (Function.update μ a z) b z
  have hμ' (c : α) : μ' c ∈ ρ.expFamilyMeans T := by
    simp only [μ', Function.update_apply]
    split_ifs
    exacts [hz, hz, hμ c]
  refine (iInf₂_le μ' hμ').trans (iInf_le_of_le (by simp [μ', hba.symm]) ?_)
  rw [cost_baiTask_eq_ofReal_sum ν hμ hν hw hμ',
    ← Finset.sum_subset (Finset.subset_univ {a, b}) fun c _ hc ↦ ?_, Finset.sum_pair hba.symm]
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
`m_b = (w a μ a + w b μ b) / (w a + w b)` is the mean of `μ a` and `μ b` weighted by `w`: the
cost of the alternatives in which `b` beats `a` is approached by moving both means to `m_b`. -/
theorem altCost_baiTask_restrict_eq_iInf_expFamilyDiv
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
      ⨅ (b) (_ : b ≠ a), ENNReal.ofReal
        (w a * ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) +
          w b * ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))) := by
  classical
  have hw' (c : α) : 0 ≤ w c := hw c
  set S := {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T} with hS_def
  have hS : IsOpen S := by
    rw [hS_def, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun c ↦ (isOpen_expFamilyMeans hT).preimage (continuous_apply c)
  have h_cost {μ' : α → ℝ} (hμ' : μ' ∈ S) := cost_baiTask_eq_ofReal_sum ν hμ hν hw hμ'
  -- The cost is continuous on the vectors of means of the family, so that the alternatives can
  -- be replaced by their closure, in which `b` is at least as good as `a` for some `b ≠ a`.
  have hc : ContinuousOn ((baiTask ν).cost w μ) S := by
    refine (baiTask ν).continuousOn_cost (fun c ↦ ?_) w
    have h := ENNReal.continuous_ofReal.comp_continuousOn ((continuousOn_expFamilyDiv hT).comp
      (f := fun μ' : α → ℝ ↦ (μ c, μ' c)) (s := S) (by fun_prop) fun μ' hμ' ↦ ⟨hμ c, hμ' c⟩)
    exact h.congr fun μ' hμ' ↦ by rw [ν_baiTask, hν μ' hμ' c]; rfl
  rw [altCost_baiTask_restrict_eq_iInf ν hS (hc.mono Set.inter_subset_right)]
  refine iInf_congr fun b ↦ iInf_congr fun hba ↦ le_antisymm ?_ ?_
  · -- Upper bound: move the means of `a` and `b` to the weighted mean `m_b`, a mean of the
    -- family (or to `μ a` if both weights vanish).
    rcases (add_nonneg (hw a) (hw b)).eq_or_lt with hW | hW
    · obtain ⟨hwa, hwb⟩ : w a = 0 ∧ w b = 0 :=
        ⟨by linarith [hw' a, hw' b], by linarith [hw' a, hw' b]⟩
      simpa [hwa, hwb, hS_def] using iInf_cost_baiTask_le ν hμ hν hw hba (hμ a)
    exact iInf_cost_baiTask_le ν hμ hν hw hba
      (div_mem_expFamilyMeans (hμ a) (hμ b) (hw a) (hw b) hW)
  · -- Lower bound: drop the arms other than `a` and `b`, then move both means to `m_b`.
    refine le_iInf₂ fun μ' hμ' ↦ le_iInf fun hab ↦ ?_
    rw [h_cost hμ']
    refine ENNReal.ofReal_le_ofReal ((mul_expFamilyDiv_add_mul_expFamilyDiv_le hT (hμ a) (hμ b)
      (ha b) (hw a) (hw b) (hμ' a) (hμ' b) hab).trans ?_)
    rw [← Finset.sum_pair (f := fun c ↦ w c * ρ.expFamilyDiv T (μ c) (μ' c)) hba.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ ↦
      mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))

/-! #### Two arms -/

variable {b : α}

omit [Fintype α] in
/-- With two arms `a` and `b` and `μ b < μ a`, the arm `a` is the only correct answer of best arm
identification. -/
private lemma correct_baiTask_of_forall_eq_or_eq (hα : ∀ c, c = a ∨ c = b)
    (hμ : μ b < μ a) : (baiTask ν).correct μ = {a} := by
  refine (subsingleton_correct_baiTask ν μ).eq_singleton_of_mem ?_
  rw [correct_baiTask]
  intro d hd
  obtain rfl := (hα d).resolve_left hd
  exact hμ

/-- **The game value of two arms in an exponential family** [KCG16, Section 3]. For two arms `a`
and `b` whose laws belong to an exponential family with divergence `d` (as in
`altCost_baiTask_restrict_eq_iInf_expFamilyDiv`), with `μ b ≤ μ a`, and a mean `z` between `μ b`
and `μ a` at the same divergence from both, `d(μ a, z) = d(μ b, z)`, the value of the game of the
answer `a` is `D(μ, ¬a) = d(μ a, z)`. Such a `z` exists by `exists_mem_Icc_expFamilyDiv_eq`. -/
theorem answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hba : b ≠ a) (hα : ∀ c, c = a ∨ c = b) (hμab : μ b ≤ μ a) {z : ℝ}
    (hz : z ∈ Set.Icc (μ b) (μ a))
    (hd : ρ.expFamilyDiv T (μ a) z = ρ.expFamilyDiv T (μ b) z) :
    ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ a =
      ENNReal.ofReal (ρ.expFamilyDiv T (μ a) z) := by
  classical
  have ha := apply_le_of_forall_eq_or_eq hα hμab
  have hz_mem : z ∈ ρ.expFamilyMeans T := Icc_subset_expFamilyMeans (hμ b) (hμ a) hz
  -- With two arms, the cost of the alternatives is the cost of moving both means to `m_b`.
  have h_alt {w : α → ℝ} (hw : w ∈ simplex α) :
      ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
        ENNReal.ofReal (w a * ρ.expFamilyDiv T (μ a) (w a * μ a + w b * μ b) +
          w b * ρ.expFamilyDiv T (μ b) (w a * μ a + w b * μ b)) := by
    rw [altCost_baiTask_restrict_eq_iInf_expFamilyDiv ν hT hμ hν ha fun c ↦
      (mem_simplex_iff.1 hw).1 c, iInf_ne_eq_of_forall_eq_or_eq hba hα,
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
    ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ =
      (ENNReal.ofReal (ρ.expFamilyDiv T (μ a) z))⁻¹ := by
  rw [IdentTask.charTime_eq_inv_answerValue _
      (by rw [IdentTask.correct_restrict]; exact correct_baiTask_of_forall_eq_or_eq ν hα hμab),
    answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq ν hT hμ hν hba hα hμab.le hz hd]

/-! #### Continuity in the model and the allocation -/

/-- **Continuity of the cost of the alternatives in best arm identification**, for arms in an
exponential family with divergence `d` (in the sense that `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` for
all vectors of means `μ`, `μ'` of the family): on the vectors of means of the family with best arm
`a`, `(μ, w) ↦ D(μ, w, ¬a)` is continuous in the model and the nonnegative allocation. -/
theorem continuousOn_altCost_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c))) (a : α) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost p.1 p.2 a)
      ({μ | (∀ c, μ c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ b ≤ μ a} ×ˢ Set.Ici 0) := by
  classical
  -- The closed form `min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` [GK16, Lemma 3] is a
  -- finite infimum of continuous functions.
  set G : α → (α → ℝ) × (α → ℝ) → ℝ≥0∞ := fun b p ↦ ENNReal.ofReal
    (p.2 a * ρ.expFamilyDiv T (p.1 a) ((p.2 a * p.1 a + p.2 b * p.1 b) / (p.2 a + p.2 b)) +
      p.2 b * ρ.expFamilyDiv T (p.1 b) ((p.2 a * p.1 a + p.2 b * p.1 b) / (p.2 a + p.2 b)))
  have hG : ContinuousOn (fun p ↦ (Finset.univ.filter (· ≠ a)).inf (G · p))
      ({μ | (∀ c, μ c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ b ≤ μ a} ×ˢ Set.Ici 0) := by
    refine ContinuousOn.finset_inf_apply fun b _ ↦ ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine (continuousOn_mul_expFamilyDiv_add_mul_expFamilyDiv hT).comp
      (f := fun p : (α → ℝ) × (α → ℝ) ↦ ((p.1 a, p.1 b), (p.2 a, p.2 b))) (by fun_prop) ?_
    rintro ⟨μ, w⟩ ⟨⟨hμ, -⟩, hw⟩
    exact ⟨⟨hμ a, hμ b⟩, hw a, hw b⟩
  refine hG.congr fun p ⟨⟨hμ, ha⟩, hw⟩ ↦ ?_
  rw [altCost_baiTask_restrict_eq_iInf_expFamilyDiv ν hT hμ (hν p.1 · hμ) ha hw]
  simp [G, Finset.inf_eq_iInf]

/-- Under the hypotheses of `continuousOn_altCost_baiTask_restrict`, at a vector of means `μ` of
the family with unique best arm `a`, `(μ', w) ↦ D(μ', w, ¬a)` is continuous within
`univ ×ˢ simplex α` at `(μ, w)` for every allocation `w` of the simplex. -/
private lemma continuousWithinAt_altCost_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) (hw : w ∈ simplex α) :
    ContinuousWithinAt (fun p : (α → ℝ) × (α → ℝ) ↦
        ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost p.1 p.2 a)
      (Set.univ ×ˢ simplex α) (μ, w) := by
  have h_best : (baiTask ν).answerSet a ∈ 𝓝 μ :=
    (isOpen_answerSet_baiTask ν a).mem_nhds ((mem_answerSet_baiTask_iff ν).2 ha)
  have h_nhds : {μ' : α → ℝ | (∀ c, μ' c ∈ ρ.expFamilyMeans T) ∧ ∀ b, μ' b ≤ μ' a} ∈ 𝓝 μ :=
    (eventually_all.2 fun c ↦ (continuous_apply c).continuousAt.preimage_mem_nhds
      (expFamilyMeans_mem_nhds hT (hμ c))).and
      (mem_of_superset h_best fun μ' hμ' b ↦ (eq_or_ne b a).elim (fun h ↦ h ▸ le_rfl)
        fun hb ↦ ((mem_answerSet_baiTask_iff ν).1 hμ' b hb).le)
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
      ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ' a) μ := by
  rw [← continuousWithinAt_univ]
  exact IdentTask.continuousWithinAt_answerValue _ fun _ hw ↦
    continuousWithinAt_altCost_baiTask_restrict ν hT hν hμ ha hw

/-- **Upper hemicontinuity of the optimal allocations of best arm identification**
[DK19, Lemma 28], for arms in an exponential family with divergence `d` (as in
`continuousOn_altCost_baiTask_restrict`): at a vector of means `μ` of the family with unique best
arm `a`, the optimal allocations `μ' ↦ w*(μ', ¬a)` are upper hemicontinuous: for every open set
`U ⊇ w*(μ, ¬a)`, `w*(μ', ¬a) ⊆ U` for `μ'` close enough to `μ`. When `w*(μ, ¬a)` is a single
allocation [GK16, Lemma 4], this is the continuity of the optimal allocation at `μ`
[GK16, Proposition 6]. -/
theorem upperHemicontinuousAt_optAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a) :
    UpperHemicontinuousAt (fun μ' ↦
      ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ' a) μ := by
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
    ContinuousAt ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ := by
  -- Near `μ`, the arm `a` is the unique best arm, so `T*(μ') = D(μ', ¬a)⁻¹`.
  have h_eq : (fun μ' ↦ (((baiTask ν).restrict
        {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).answerValue μ' a)⁻¹) =ᶠ[𝓝 μ]
      ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime := by
    filter_upwards [(isOpen_answerSet_baiTask ν a).mem_nhds ((mem_answerSet_baiTask_iff ν).2 ha)]
      with μ' hμ'
    exact (charTime_baiTask_restrict_eq_inv_answerValue ν _
      ((mem_answerSet_baiTask_iff ν).1 hμ')).symm
  exact ((continuousAt_answerValue_baiTask_restrict ν hT hν hμ ha).inv).congr h_eq

end ExpFamily

section Gaussian

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {μ w : α → ℝ} {σ2 : ℝ≥0}

omit [Fintype α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the vectors of means of the exponential
family of `𝒩(0, σ2)` are all the vectors: best arm identification restricted to them is best arm
identification. -/
private lemma restrict_baiTask_gaussianBandit [Countable α] (hσ2 : σ2 ≠ 0) :
    (baiTask (Bandits.gaussianBandit · σ2)).restrict
        {μ' : α → ℝ | ∀ c, μ' c ∈ (gaussianReal 0 σ2).expFamilyMeans id} =
      baiTask (Bandits.gaussianBandit · σ2) := by
  simp [expFamilyMeans_gaussianReal 0 hσ2]

omit [Fintype α] in
/-- The arm laws of a Gaussian bandit with variance `σ2 ≠ 0` are members of the exponential family
of `𝒩(0, σ2)`: their divergences are those of the family. -/
private lemma klDiv_gaussianBandit_eq_ofReal_expFamilyDiv [Countable α] (hσ2 : σ2 ≠ 0)
    (μ μ' : α → ℝ) (c : α) :
    klDiv (Bandits.gaussianBandit μ σ2 c) (Bandits.gaussianBandit μ' σ2 c) =
      ENNReal.ofReal ((gaussianReal 0 σ2).expFamilyDiv id (μ c) (μ' c)) := by
  rw [Bandits.klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2]

/-- **The cost of the alternatives in Gaussian best arm identification** [GK16, Section 2.2]. For
Gaussian arms with a common variance `σ2 ≠ 0`, a best arm `a` of `μ` and a nonnegative allocation
`w`, `D(μ, w, ¬a) = min_{b ≠ a} (w a w b / (w a + w b)) (μ a - μ b)² / (2 σ2)`. -/
theorem altCost_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0) (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    (baiTask (Bandits.gaussianBandit · σ2)).altCost μ w a =
      ⨅ (b) (_ : b ≠ a),
        ENNReal.ofReal (w a * w b / (w a + w b) * (μ a - μ b) ^ 2 / (2 * σ2)) := by
  rw [← restrict_baiTask_gaussianBandit hσ2, altCost_baiTask_restrict_eq_iInf_expFamilyDiv _
    (not_ae_eq_const_gaussianReal 0 hσ2) (fun c ↦ by simp [hσ2])
    (fun μ' _ ↦ klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ') ha hw]
  refine iInf_congr fun b ↦ iInf_congr fun _ ↦ congrArg ENNReal.ofReal ?_
  have hσ2' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
  have hwa : 0 ≤ w a := hw a
  have hwb : 0 ≤ w b := hw b
  rw [expFamilyDiv_gaussianReal 0 hσ2, expFamilyDiv_gaussianReal 0 hσ2]
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
    (baiTask (Bandits.gaussianBandit · σ2)).answerValue μ a =
      ENNReal.ofReal ((μ a - μ b) ^ 2 / (8 * σ2)) := by
  have hσ2' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
  rw [← restrict_baiTask_gaussianBandit hσ2,
    answerValue_baiTask_restrict_eq_expFamilyDiv_of_forall_eq_or_eq _
      (not_ae_eq_const_gaussianReal 0 hσ2) (fun c ↦ by simp [hσ2])
      (fun μ' _ ↦ klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ') hba hα hμ
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
    (baiTask (Bandits.gaussianBandit · σ2)).charTime μ =
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
    (baiTask (Bandits.gaussianBandit · σ2)).optAlloc μ a = {fun _ ↦ 1 / 2} := by
  have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  have ha := apply_le_of_forall_eq_or_eq hα hμ.le
  -- With two arms, the cost of the alternatives is `w a w b (μ a - μ b)² / (2 σ2)`.
  have h_alt {w : α → ℝ} (hw : w ∈ simplex α) :
      (baiTask (Bandits.gaussianBandit · σ2)).altCost μ w a =
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

omit [Fintype α] [MeasurableSingletonClass α] in
/-- If `a` is the unique best arm of `μ`, then every arm has mean at most `μ a`. -/
private lemma forall_le_of_forall_ne_lt (ha : ∀ b ≠ a, μ b < μ a) (b : α) : μ b ≤ μ a := by
  rcases eq_or_ne b a with rfl | hb
  exacts [le_rfl, (ha b hb).le]

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
    (baiTask (Bandits.gaussianBandit · σ2)).answerValue μ a ≤
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
  rw [altCost_baiTask_gaussianBandit hσ2 (forall_le_of_forall_ne_lt ha) hw_nonneg]
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
      (baiTask (Bandits.gaussianBandit · σ2)).answerValue μ a := by
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
  rw [altCost_baiTask_gaussianBandit hσ2 (forall_le_of_forall_ne_lt ha) (mem_simplex_iff.1 hw).1]
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
      (baiTask (Bandits.gaussianBandit · σ2)).charTime μ := by
  rw [charTime_baiTask_eq_inv_answerValue _ ha,
    ← inv_inv (ENNReal.ofReal _), ← ENNReal.ofReal_inv_of_pos (sum_div_sq_pos hσ2 hb₀a ha),
    ENNReal.inv_le_inv]
  exact answerValue_baiTask_gaussianBandit_le hσ2 hb₀a ha

/-- **Upper bound on the characteristic time of Gaussian best arm identification**
[GK16, Section 2.2]. For Gaussian arms with a common variance `σ2 ≠ 0`, a unique best arm `a` of
`μ` and a second best arm `b₀`, `T*(μ) ≤ 2 H(μ)`, where `H(μ) = ∑ c, 2 σ2 / Δ_c²` with the gaps
`Δ_b = μ a - μ b` for `b ≠ a` and `Δ_a = Δ_{b₀} = min_{b ≠ a} Δ_b`. -/
theorem charTime_baiTask_gaussianBandit_le (hσ2 : σ2 ≠ 0) (hb₀a : b₀ ≠ a)
    (ha : ∀ b ≠ a, μ b < μ a) (hb₀ : ∀ b ≠ a, μ b ≤ μ b₀) :
    (baiTask (Bandits.gaussianBandit · σ2)).charTime μ ≤
      ENNReal.ofReal (2 * (2 * σ2 / (μ a - μ b₀) ^ 2 +
        ∑ b ∈ Finset.univ.erase a, 2 * σ2 / (μ a - μ b) ^ 2)) := by
  rw [charTime_baiTask_eq_inv_answerValue _ ha,
    ← inv_inv (ENNReal.ofReal (2 * _)),
    ← ENNReal.ofReal_inv_of_pos (mul_pos two_pos (sum_div_sq_pos hσ2 hb₀a ha)), ENNReal.inv_le_inv]
  exact le_answerValue_baiTask_gaussianBandit hσ2 hb₀a ha hb₀

end Gaussian

end LMLExplore.Identification
