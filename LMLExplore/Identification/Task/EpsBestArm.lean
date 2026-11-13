/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical

/-!
# The alternatives of `ε`-best arm identification and the cost of the alternatives

In `ε`-best arm identification (`epsBaiTask ν id ε`), the correct answers of a vector of means `μ`
are its `ε`-good arms, the arms `a` with `μ b ≤ μ a + ε` for every arm `b`. An arm `a` is thus not
`ε`-good for `μ'` exactly when some arm `b` has `μ' a + ε < μ' b`.

Let the arm `c` have a real divergence `d_c` on an open set `S_c` of means (`IsDivergenceOn`), in
the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for the vectors of means `μ'` in `S`; the arms
of per-arm exponential families, with the divergences of the families in the mean parametrization
on their sets of means, are an instance (`isDivergenceOn_expFamilyDiv`). The admissible models are
the vectors of means in `S`. The arm `a` stops being `ε`-good once one of the following happens:

* the mean of another arm `b` is moved above `μ a + ε`; as the new mean decreases to `μ a + ε`,
  this costs `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)`;
* the mean of `a` is moved below `μ b - ε` for another arm `b`; as the new mean increases to
  `μ b - ε`, this costs `D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)`.

Each of these bounds involves a single arm. Through the change of measure
`kl(δ, 1 - δ) ≤ D(μ, n, ¬a)` for the expected numbers of pulls `n` of a `δ`-correct algorithm
(`LMLExplore.Identification.IdentTask.IsDeltaCorrect.klBer_le_altCost`), they give a lower bound on
the expected number of pulls of every arm, whose sum is a lower bound on the sample complexity of
`ε`-best arm identification, of the order of `K / ε²` for Bernoulli arms [MT04, Theorem 1]
(`LMLExplore/Identification/EpsBestArmLowerBound.lean`).

In multiplicative `ε`-best arm identification (`mulEpsBaiTask ν id ε`, on the vectors of positive
means), the arm `a` is multiplicatively `ε`-good for `μ` when `(1 - ε) μ b ≤ μ a` for every arm `b`.
For `ε < 1` it stops being so once one of the following happens:

* the mean of another arm `b` is moved above `μ a / (1 - ε)`; this costs
  `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a / (1 - ε))`;
* the mean of `a` is moved below `(1 - ε) μ b` for another arm `b`, staying positive; this costs
  `D(μ, w, ¬a) ≤ w a d_a(μ a, (1 - ε) μ b)`.

## Main statements

* `LMLExplore.Identification.mem_alt_epsBaiTask_iff`: a model `θ` is an alternative to `a` iff
  some arm `b` has `mean θ a + ε < mean θ b`, for any mean functional `mean`.
* `LMLExplore.Identification.altCost_epsBaiTask_restrict_le_ofReal_mul_add`: for an arm `b ≠ a`,
  `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)`.
* `LMLExplore.Identification.altCost_epsBaiTask_restrict_le_ofReal_mul_sub`: for an arm `b ≠ a`,
  `D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)`.
* `LMLExplore.Identification.mem_alt_mulEpsBaiTask_iff`: in multiplicative `ε`-best arm
  identification, a model `θ` is an alternative to `a` iff its means are positive and some arm `b`
  has `mean θ a < (1 - ε) * mean θ b`.
* `LMLExplore.Identification.altCost_mulEpsBaiTask_restrict_le_ofReal_mul_div`,
  `LMLExplore.Identification.altCost_mulEpsBaiTask_restrict_le_ofReal_mul_mul`: for
  `ε < 1`, positive means and an arm `b ≠ a`, `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a / (1 - ε))` and
  `D(μ, w, ¬a) ≤ w a d_a(μ a, (1 - ε) * μ b)`.

## References

* [MT04] S. Mannor and J. N. Tsitsiklis, *The sample complexity of exploration in the multi-armed
  bandit problem*, JMLR 5 (2004), Theorem 1.
* [JDK23b] M. Jourdan, R. Degenne and E. Kaufmann, *An ε-best-arm identification algorithm for
  fixed-confidence and beyond*, NeurIPS 2023.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {S : α → Set ℝ} {d : α → ℝ → ℝ → ℝ} {μ μ' w : α → ℝ} {ε : ℝ} {a b : α}

/-- In `ε`-best arm identification, `θ` is an alternative to the arm `a` iff `a` is not `ε`-good
for `θ`: some arm `b` has `mean θ a + ε < mean θ b`. -/
lemma mem_alt_epsBaiTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {θ : Θ} :
    θ ∈ (epsBaiTask ν mean ε).alt a ↔ ∃ b, mean θ a + ε < mean θ b := by
  simp [IdentTask.mem_alt_iff]

/-- In multiplicative `ε`-best arm identification, `θ` is an alternative to the arm `a` iff `θ` has
positive means and `a` is not multiplicatively `ε`-good for `θ`: some arm `b` has
`mean θ a < (1 - ε) * mean θ b`. -/
lemma mem_alt_mulEpsBaiTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {θ : Θ} :
    θ ∈ (mulEpsBaiTask ν mean ε).alt a ↔
      (∀ c, 0 < mean θ c) ∧ ∃ b, mean θ a < (1 - ε) * mean θ b := by
  simp [IdentTask.mem_alt_iff]

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

variable [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **The cost of raising another arm above `μ a + ε`.** Let each arm `c` have a divergence `d_c`
on an open set `S_c` of means, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all
vectors of means `μ'` in `S`, and let `μ` be a vector of means in `S`. For arms `b ≠ a` such that
`μ a + ε ∈ S_b` and every nonnegative allocation `w`, `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)` in
`ε`-best arm identification, within the vectors of means in `S`: moving the mean of `b` above
`μ a + ε` makes `a` not `ε`-good. -/
theorem altCost_epsBaiTask_restrict_le_ofReal_mul_add
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hμ : ∀ c, μ c ∈ S c)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hba : b ≠ a) (hb : μ a + ε ∈ S b) (hw : 0 ≤ w) :
    ((epsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w a ≤
      ENNReal.ofReal (w b * d b (μ b) (μ a + ε)) := by
  classical
  exact IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp) hd hν hw hμ
    b hb (l := 𝓝[>] (μ a + ε))
    (((continuous_const.update b continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx ↦ (mem_alt_epsBaiTask_iff ν id).2
      ⟨b, by simpa [Function.update_of_ne hba.symm] using hx⟩)

omit [DecidableEq α] in
/-- **The cost of lowering `a` below `μ b - ε`.** Let each arm `c` have a divergence `d_c` on an
open set `S_c` of means, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors
of means `μ'` in `S`, and let `μ` be a vector of means in `S`. For arms `b ≠ a` such that
`μ b - ε ∈ S_a` and every nonnegative allocation `w`, `D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)` in
`ε`-best arm identification, within the vectors of means in `S`: moving the mean of `a` below
`μ b - ε` makes `a` not `ε`-good. -/
theorem altCost_epsBaiTask_restrict_le_ofReal_mul_sub
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hμ : ∀ c, μ c ∈ S c)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hba : b ≠ a) (ha : μ b - ε ∈ S a) (hw : 0 ≤ w) :
    ((epsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w a ≤
      ENNReal.ofReal (w a * d a (μ a) (μ b - ε)) := by
  classical
  exact IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp) hd hν hw hμ
    a ha (l := 𝓝[<] (μ b - ε))
    (((continuous_const.update a continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx ↦ (mem_alt_epsBaiTask_iff ν id).2
      ⟨b, by simpa [Function.update_of_ne hba] using (lt_sub_iff_add_lt.1 hx)⟩)

omit [DecidableEq α] in
/-- **The cost of raising another arm above `μ a / (1 - ε)`.** Let each arm `c` have a divergence
`d_c` on an open set `S_c` of means, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for
all vectors of means `μ'` in `S`, and let `μ` be a vector of positive means in `S`. For `ε < 1`,
arms `b ≠ a` such that `μ a / (1 - ε) ∈ S_b` and every nonnegative allocation `w`,
`D(μ, w, ¬a) ≤ w b d_b(μ b, μ a / (1 - ε))` in multiplicative `ε`-best arm identification, within
the vectors of means in `S`: moving the mean of `b` above `μ a / (1 - ε)` makes `a` not
multiplicatively `ε`-good. -/
theorem altCost_mulEpsBaiTask_restrict_le_ofReal_mul_div
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hμ : ∀ c, μ c ∈ S c)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμ_pos : ∀ c, 0 < μ c) (hε : ε < 1) (hba : b ≠ a)
    (hb : μ a / (1 - ε) ∈ S b) (hw : 0 ≤ w) :
    ((mulEpsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w a ≤
      ENNReal.ofReal (w b * d b (μ b) (μ a / (1 - ε))) := by
  classical
  have h1ε : 0 < 1 - ε := sub_pos.2 hε
  refine IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp) hd hν hw hμ
    b hb (l := 𝓝[>] (μ a / (1 - ε)))
    (((continuous_const.update b continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx ↦ (mem_alt_mulEpsBaiTask_iff ν id).2 ⟨?_, b, ?_⟩)
  · -- The new mean `x` of `b` is larger than `μ a / (1 - ε) > 0`.
    have hx : 0 < x := (div_pos (hμ_pos a) h1ε).trans hx
    intro c
    rcases eq_or_ne c b with rfl | hcb
    · simpa using hx
    · simpa [Function.update_of_ne hcb] using hμ_pos c
  · simpa [Function.update_of_ne hba.symm, mul_comm] using (div_lt_iff₀ h1ε).1 hx

omit [DecidableEq α] in
/-- **The cost of lowering `a` below `(1 - ε) * μ b`.** Let each arm `c` have a divergence `d_c`
on an open set `S_c` of means, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all
vectors of means `μ'` in `S`, and let `μ` be a vector of positive means in `S`. For `ε < 1`, arms
`b ≠ a` such that `(1 - ε) * μ b ∈ S_a` and every nonnegative allocation `w`,
`D(μ, w, ¬a) ≤ w a d_a(μ a, (1 - ε) * μ b)` in multiplicative `ε`-best arm identification, within
the vectors of means in `S`: moving the mean of `a` below `(1 - ε) * μ b`, and above `0`, makes `a`
not multiplicatively `ε`-good. -/
theorem altCost_mulEpsBaiTask_restrict_le_ofReal_mul_mul
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hμ : ∀ c, μ c ∈ S c)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμ_pos : ∀ c, 0 < μ c) (hε : ε < 1) (hba : b ≠ a)
    (ha : (1 - ε) * μ b ∈ S a) (hw : 0 ≤ w) :
    ((mulEpsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w a ≤
      ENNReal.ofReal (w a * d a (μ a) ((1 - ε) * μ b)) := by
  classical
  have hpos : 0 < (1 - ε) * μ b := mul_pos (sub_pos.2 hε) (hμ_pos b)
  -- Near `(1 - ε) * μ b > 0` and below it, the new mean `x` of `a` is positive.
  have h_ev : ∀ᶠ x in 𝓝[<] ((1 - ε) * μ b), 0 < x ∧ x < (1 - ε) * μ b :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hpos)).and
      self_mem_nhdsWithin
  refine IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto (by simp) hd hν hw hμ
    a ha (l := 𝓝[<] ((1 - ε) * μ b))
    (((continuous_const.update a continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (h_ev.mono fun x hx ↦ (mem_alt_mulEpsBaiTask_iff ν id).2 ⟨fun c ↦ ?_, b, ?_⟩)
  · rcases eq_or_ne c a with rfl | hca
    · simpa using hx.1
    · simpa [Function.update_of_ne hca] using hμ_pos c
  · simpa [Function.update_of_ne hba] using hx.2

end LMLExplore.Identification
