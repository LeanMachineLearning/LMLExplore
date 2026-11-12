/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical

/-!
# The cost of the alternatives of top-`m` identification

In top-`m` identification (`topMTask ν id m`), the correct answer of a vector of means `μ` is the
set `s` of its `m` arms with the largest means, on the vectors where these means are larger than
the other ones. Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`
in the mean parametrization, and let `b` be an arm outside `s` with the largest mean outside `s`
(the `(m + 1)`-th largest mean) and `b'` an arm of `s` with the smallest mean in `s` (the `m`-th
largest mean).

* An arm `a ∈ s` leaves the top-`m` set once its mean drops below `μ b`. Moving it to `μ b - t`
  (and the other arms outside `s`, except `b`, down by `t`, to keep the `m` largest means
  separated from the other ones) gives an alternative to `s` for every `t > 0`. As `t → 0`, these
  alternatives converge to the vector in which only the mean of `a` moved, to `μ b`, so that
  `D(μ, w, ¬s) ≤ w a d_a(μ a, μ b)`.
* Symmetrically, an arm `a ∉ s` enters the top-`m` set once its mean exceeds `μ b'`, and
  `D(μ, w, ¬s) ≤ w a d_a(μ a, μ b')`.

Each of these bounds involves a single arm. Through the change of measure
`kl(δ, 1 - δ) ≤ D(μ, n, ¬s)` for the expected numbers of pulls `n` of a `δ`-correct algorithm
(`LMLExplore.Identification.IdentTask.IsDeltaCorrect.klBer_le_altCost`), they give a lower bound on
the expected number of pulls of every arm, whose sum is the lower bound of Kaufmann, Cappé and
Garivier on the sample complexity of top-`m` identification [KCG16, Theorem 4]
(`LMLExplore/Identification/TopMLowerBound.lean`).

## Main statements

* `LMLExplore.Identification.altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_mem`: for
  `a ∈ s`, `D(μ, w, ¬s) ≤ w a d_a(μ a, μ b)`.
* `LMLExplore.Identification.altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_notMem`: for
  `a ∉ s`, `D(μ, w, ¬s) ≤ w a d_a(μ a, μ b')`.

## References

* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), proof of Theorem 4.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  [DecidableEq α] {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {μ w : α → ℝ} {m : ℕ} {s : Finset α}
  {a b : α} (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

omit [Fintype α] in
/-- Moving an arm `a ∈ s` of `μ` to `μ b - t`, where `b ∉ s` has the largest mean outside `s`,
and the other arms outside `s` but `b` down by `t > 0`, gives an alternative to `s` in top-`m`
identification: in the new vector, `b` has replaced `a` in the top-`m` set. -/
private lemma update_shift_mem_alt_topMTask_of_mem (hs : s ∈ (topMTask ν id m).correct μ)
    (ha : a ∈ s) (hb : b ∉ s) (hb_max : ∀ c ∉ s, μ c ≤ μ b) {t : ℝ} (ht : 0 < t) :
    Function.update (fun c ↦ if c ∈ s ∨ c = b then μ c else μ c - t) a (μ b - t) ∈
      (topMTask ν id m).alt s := by
  simp only [correct_topMTask, Set.mem_ofPred_eq, id_eq] at hs
  obtain ⟨hcard, hsep⟩ := hs
  rw [IdentTask.mem_alt_iff, M_topMTask, correct_topMTask, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  simp only [id_eq]
  have hba : b ≠ a := fun h ↦ hb (h ▸ ha)
  refine ⟨⟨insert b (s.erase a), ?_, fun x hx y hy ↦ ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hb]), Finset.card_erase_add_one ha, hcard]
  · -- The arms of the new top-`m` set have mean at least `μ b`, the other arms less.
    have hx' : μ b ≤ Function.update (fun c ↦ if c ∈ s ∨ c = b then μ c else μ c - t) a
        (μ b - t) x := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simp [Function.update_of_ne hba]
      · obtain ⟨hxa, hxs⟩ := Finset.mem_erase.1 hx
        simpa [Function.update_of_ne hxa, hxs] using (hsep x hxs b hb).le
    refine lt_of_lt_of_le ?_ hx'
    simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hy
    rcases eq_or_ne y a with rfl | hya
    · simpa using ht
    · have hys : y ∉ s := fun h ↦ hya (by_contra fun h' ↦ hy.2 h' h)
      simp only [Function.update_of_ne hya, hys, hy.1, or_self, ite_false]
      linarith [hb_max y hys]
  · have := h a ha b hb
    simp [Function.update_of_ne hba] at this
    linarith

omit [Fintype α] in
/-- Moving an arm `a ∉ s` of `μ` to `μ b + t`, where `b ∈ s` has the smallest mean in `s`, and the
other arms of `s` but `b` up by `t > 0`, gives an alternative to `s` in top-`m` identification: in
the new vector, `a` has replaced `b` in the top-`m` set. -/
private lemma update_shift_mem_alt_topMTask_of_notMem (hs : s ∈ (topMTask ν id m).correct μ)
    (ha : a ∉ s) (hb : b ∈ s) (hb_min : ∀ c ∈ s, μ b ≤ μ c) {t : ℝ} (ht : 0 < t) :
    Function.update (fun c ↦ if c ∉ s ∨ c = b then μ c else μ c + t) a (μ b + t) ∈
      (topMTask ν id m).alt s := by
  simp only [correct_topMTask, Set.mem_ofPred_eq, id_eq] at hs
  obtain ⟨hcard, hsep⟩ := hs
  rw [IdentTask.mem_alt_iff, M_topMTask, correct_topMTask, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  simp only [id_eq]
  have hba : b ≠ a := fun h ↦ ha (h ▸ hb)
  refine ⟨⟨insert a (s.erase b), ?_, fun x hx y hy ↦ ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [ha]), Finset.card_erase_add_one hb, hcard]
  · -- The arms of the new top-`m` set have mean at least `μ b + t`, the other arms at most `μ b`.
    have hx' : μ b + t ≤ Function.update (fun c ↦ if c ∉ s ∨ c = b then μ c else μ c + t) a
        (μ b + t) x := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simp
      · obtain ⟨hxb, hxs⟩ := Finset.mem_erase.1 hx
        have hxa : x ≠ a := fun h ↦ ha (h ▸ hxs)
        simpa [Function.update_of_ne hxa, hxs, hxb] using hb_min x hxs
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (lt_add_of_pos_right _ ht) hx')
    simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hy
    have hya : y ≠ a := hy.1
    rw [Function.update_of_ne hya]
    rcases eq_or_ne y b with rfl | hyb
    · simp
    · have hys : y ∉ s := fun h ↦ hy.2 hyb h
      simpa [hys] using (hsep b hb y hys).le
  · have := h b hb a ha
    simp [Function.update_of_ne hba] at this
    linarith

omit [DecidableEq α] in
/-- **The cost of moving an arm out of the top-`m` set** [KCG16, proof of Theorem 4]. Let the arm
`c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let `μ` be a vector of means
of the families whose top-`m` set is `s`, and let `b ∉ s` be an arm with the largest mean outside
`s`. For `a ∈ s` such that `μ b` is a mean of the family of `a` and every nonnegative allocation
`w`, `D(μ, w, ¬s) ≤ w a d_a(μ a, μ b)` within the vectors of means of the families. -/
theorem altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_mem
    (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν id m).correct μ) (ha : a ∈ s) (hb : b ∉ s)
    (hb_max : ∀ c ∉ s, μ c ≤ μ b) (hba : μ b ∈ (ρ a).expFamilyMeans (T a)) (hw : 0 ≤ w) :
    ((topMTask ν id m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w s ≤
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) (μ b)) := by
  classical
  have hg : Continuous fun t : ℝ ↦
      Function.update (fun c ↦ if c ∈ s ∨ c = b then μ c else μ c - t) a (μ b - t) :=
    continuous_pi fun c ↦ by
      rcases eq_or_ne c a with rfl | hca
      · simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hca]
        split_ifs <;> fun_prop
  exact IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp)
    (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ a hba
    (by simpa using (hg.tendsto 0).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun _ ht ↦
      update_shift_mem_alt_topMTask_of_mem ν hs ha hb hb_max ht)

omit [DecidableEq α] in
/-- **The cost of moving an arm into the top-`m` set** [KCG16, proof of Theorem 4]. Let the arm `c`
belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let `μ` be a vector of means of
the families whose top-`m` set is `s`, and let `b ∈ s` be an arm with the smallest mean in `s`. For
`a ∉ s` such that `μ b` is a mean of the family of `a` and every nonnegative allocation `w`,
`D(μ, w, ¬s) ≤ w a d_a(μ a, μ b)` within the vectors of means of the families. -/
theorem altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_notMem
    (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν id m).correct μ) (ha : a ∉ s) (hb : b ∈ s)
    (hb_min : ∀ c ∈ s, μ b ≤ μ c) (hba : μ b ∈ (ρ a).expFamilyMeans (T a)) (hw : 0 ≤ w) :
    ((topMTask ν id m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w s ≤
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) (μ b)) := by
  classical
  have hg : Continuous fun t : ℝ ↦
      Function.update (fun c ↦ if c ∉ s ∨ c = b then μ c else μ c + t) a (μ b + t) :=
    continuous_pi fun c ↦ by
      rcases eq_or_ne c a with rfl | hca
      · simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hca]
        split_ifs <;> fun_prop
  exact IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp)
    (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ a hba
    (by simpa using (hg.tendsto 0).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun _ ht ↦
      update_shift_mem_alt_topMTask_of_notMem ν hs ha hb hb_min ht)

end LMLExplore.Identification
