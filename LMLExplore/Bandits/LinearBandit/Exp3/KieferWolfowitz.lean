/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.OptimalDesign
public import LMLExplore.Bandits.LinearBandit.Exp3.Algorithm

/-!
# Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration

The regret bound `2 √(3 d n log k)` of Exp3 for linear bandits [LS, Theorem 27.1] needs an
exploration distribution `π` whose design operator `V(π) = ∑ b, π b • φ b ⊗ φ b` is invertible
and whose G-value `max_b ⟪φ b, V(π)⁻¹ φ b⟫` is at most the dimension. The Kiefer–Wolfowitz
theorem provides one when the features `φ` span the space. Both hypotheses are discharged here.

The features need not span `E`. Exp3 for linear bandits is run on the span `W` of the features,
with the features `spanFeatures φ` seen as elements of `W` and the Kiefer–Wolfowitz exploration
`kieferWolfowitzExploration φ` of `W`. The learner observes only the losses `⟪φ c, y⟫` of the arms,
which are the losses `⟪φ c, P y⟫` of the orthogonal projection `P y` of the loss vector onto `W`.
So the regret against an adaptive adversary in `E` is the regret against the projected adversary in
`W`. The bound then holds with the dimension `m` of the span of the features in place of `d`, and
`m ≤ d`, with no assumption on the features. This is [LS, Theorem 27.1] together with the
Kiefer–Wolfowitz theorem for sets that need not span the space [LS, Theorem 21.1, Exercise 21.6].

## Main definitions

* `LMLExplore.Bandits.spanFeatures φ`: the features `φ a`, as elements of the span of the features.
* `LMLExplore.Bandits.kieferWolfowitzExploration φ`: a Kiefer–Wolfowitz design on the features in
  their span. Its design operator is invertible on the span and its G-value is at most the
  dimension of the span.
* `LMLExplore.Bandits.linearExp3KieferWolfowitz φ η γ hγ`: Exp3 for linear bandits on the span of
  the features, with the Kiefer–Wolfowitz exploration.

## Main statements

* `inner_ringInverse_sum_smul_rankOne_spanFeatures`: the loss estimates of Exp3 for linear bandits
  on the span of the features are those of [LS, Algorithm 15] in `E` with the Moore–Penrose inverse
  `V⁺` in place of `V⁻¹`, and `linearExp3KieferWolfowitz_eq_linearExp3`: when the features span
  `E`, the algorithm is Exp3 for linear bandits on `E` with the Kiefer–Wolfowitz exploration.
* `LinearExp3.integral_regret_le_kieferWolfowitz`: against an adaptive adversary, with the tuned
  rates, the expected regret of `linearExp3KieferWolfowitz` against every arm is at most
  `2 √(3 m n log k)`, where `m` is the dimension of the span of the features.
* `LinearExp3.integral_regret_le_sqrt_finrank_kieferWolfowitz`: the same expected regret is at most
  `2 √(3 d n log k)`, where `d` is the dimension of `E`.
* `LinearExp3.integral_regret_detFeedback_le_kieferWolfowitz`: the first bound, for every run
  against the environment of an adaptive adversary.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 21 and 27.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning ContinuousLinearMap InnerProductSpace Module
  LMLExplore.OnlineLearning
open scoped InnerProductSpace

namespace LMLExplore.Bandits

variable {α 𝓞 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Exploration

variable (φ : α → E)

/-- The features `φ a`, as elements of the span `Submodule.span ℝ (Set.range φ)` of the features.
They span it (`span_range_spanFeatures`). -/
def spanFeatures (a : α) : Submodule.span ℝ (Set.range φ) :=
  ⟨φ a, Submodule.subset_span (Set.mem_range_self a)⟩

@[simp]
lemma coe_spanFeatures (a : α) : (spanFeatures φ a : E) = φ a := (rfl)

/-- The features span their span. -/
lemma span_range_spanFeatures : Submodule.span ℝ (Set.range (spanFeatures φ)) = ⊤ := by
  have : Set.range (spanFeatures φ) = (↑) ⁻¹' Set.range φ := by
    ext x
    simp [Subtype.ext_iff]
  rw [this, Submodule.span_span_coe_preimage]

/-- The loss of an arm against the orthogonal projection of a loss vector onto the span of the
features is its loss against the loss vector. -/
lemma inner_spanFeatures_orthogonalProjectionOnto
    [(Submodule.span ℝ (Set.range φ)).HasOrthogonalProjection] (a : α) (v : E) :
    ⟪spanFeatures φ a, (Submodule.span ℝ (Set.range φ)).orthogonalProjectionOnto v⟫_ℝ =
      ⟪φ a, v⟫_ℝ := by
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, coe_spanFeatures]

variable [Fintype α] [FiniteDimensional ℝ E] [Nonempty α]

/-- The **Kiefer–Wolfowitz exploration** of the features `φ`: weights `π` in the simplex whose
design operator `V(π) = ∑ b, π b • φ b ⊗ φ b` on the span of the features is invertible, with
`⟪φ b, V(π)⁻¹ φ b⟫ ≤ m` for every arm `b`, where `m` is the dimension of the span. They are chosen
by the Kiefer–Wolfowitz theorem `exists_mem_simplex_inner_ringInverse_le_finrank` on the span. -/
noncomputable def kieferWolfowitzExploration : α → ℝ :=
  (exists_mem_simplex_inner_ringInverse_le_finrank (span_range_spanFeatures φ)).choose

/-- The Kiefer–Wolfowitz exploration is a probability vector. -/
lemma kieferWolfowitzExploration_mem_simplex : kieferWolfowitzExploration φ ∈ simplex α :=
  (exists_mem_simplex_inner_ringInverse_le_finrank (span_range_spanFeatures φ)).choose_spec.1

/-- The design operator of the Kiefer–Wolfowitz exploration is invertible on the span of the
features. -/
lemma isUnit_kieferWolfowitzExploration :
    IsUnit (∑ b, kieferWolfowitzExploration φ b •
      rankOne ℝ (spanFeatures φ b) (spanFeatures φ b)) :=
  (exists_mem_simplex_inner_ringInverse_le_finrank (span_range_spanFeatures φ)).choose_spec.2.1

/-- The G-value of the Kiefer–Wolfowitz exploration is at most the dimension of the span of the
features. -/
lemma inner_ringInverse_kieferWolfowitzExploration_le_finrank (b : α) :
    ⟪spanFeatures φ b, Ring.inverse (∑ b, kieferWolfowitzExploration φ b •
        rankOne ℝ (spanFeatures φ b) (spanFeatures φ b)) (spanFeatures φ b)⟫_ℝ ≤
      finrank ℝ (Submodule.span ℝ (Set.range φ)) :=
  (exists_mem_simplex_inner_ringInverse_le_finrank (span_range_spanFeatures φ)).choose_spec.2.2 b

end Exploration

section Estimate

variable [Fintype α] (φ : α → E) {p : α → ℝ}

/-- On the span of the features, the operator `V(p) = ∑ b, p b • φ b ⊗ φ b` on `E` acts as the
operator `V_W(p) = ∑ b, p b • φ b ⊗ φ b` on the span `W` of the features. -/
lemma coe_sum_smul_rankOne_spanFeatures_apply (p : α → ℝ)
    (v : Submodule.span ℝ (Set.range φ)) :
    ((∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b)) v : E) =
      (∑ b, p b • rankOne ℝ (φ b) (φ b)) v := by
  simp [sum_apply, Submodule.coe_inner]

/-- If the operator `V_W(p) = ∑ b, p b • φ b ⊗ φ b` on the span `W` of the features is
invertible, then `W` lies in the range of the operator `V(p) = ∑ b, p b • φ b ⊗ φ b` on `E`. -/
lemma span_le_range_sum_smul_rankOne
    (hu : IsUnit (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b))) :
    Submodule.span ℝ (Set.range φ) ≤
      LinearMap.range ((∑ b, p b • rankOne ℝ (φ b) (φ b) : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  fun v hv ↦ ⟨Ring.inverse (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b)) ⟨v, hv⟩, by
    rw [coe_coe, ← coe_sum_smul_rankOne_spanFeatures_apply, apply_ringInverse_apply hu,
      Submodule.coe_mk]⟩

variable [FiniteDimensional ℝ E]

/-- **The estimates on the span are those of the Moore–Penrose inverse.** If the operator
`V_W(p) = ∑ b, p b • φ b ⊗ φ b` on the span `W` of the features is invertible, then the weighted
inner products of the features for its inverse are those for the Moore–Penrose inverse `V(p)⁺` of
the operator `V(p) = ∑ b, p b • φ b ⊗ φ b` on `E`: `⟪φ a, V_W(p)⁻¹ φ c⟫ = ⟪φ a, V(p)⁺ φ c⟫`. -/
theorem inner_ringInverse_sum_smul_rankOne_spanFeatures
    (hu : IsUnit (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b))) (a c : α) :
    ⟪spanFeatures φ a, Ring.inverse (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b))
        (spanFeatures φ c)⟫_ℝ =
      ⟪φ a, ((∑ b, p b • rankOne ℝ (φ b) (φ b) : E →L[ℝ] E) : E →ₗ[ℝ] E).moorePenroseInverse
        (φ c)⟫_ℝ := by
  have hsym : ((∑ b, p b • rankOne ℝ (φ b) (φ b) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric :=
    fun x y ↦ by
      simp only [coe_coe, sum_apply, smul_apply, rankOne_apply, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right]
      exact Finset.sum_congr rfl fun b _ ↦ by rw [real_inner_comm x (φ b)]; ring
  -- `φ c` is the image under `V(p)` of `V_W(p)⁻¹ φ c`, which lies in the range of `V(p)`
  have hc : φ c = ((∑ b, p b • rankOne ℝ (φ b) (φ b) : E →L[ℝ] E) : E →ₗ[ℝ] E)
      ↑(Ring.inverse (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b))
        (spanFeatures φ c)) := by
    rw [coe_coe, ← coe_sum_smul_rankOne_spanFeatures_apply, apply_ringInverse_apply hu,
      coe_spanFeatures]
  rw [hc, hsym.moorePenroseInverse_apply_apply_of_mem_range
    (span_le_range_sum_smul_rankOne φ hu (Submodule.coe_mem _)), Submodule.coe_inner,
    coe_spanFeatures]

/-- If the features span `E` and the operator `V_W(p) = ∑ b, p b • φ b ⊗ φ b` on their span is
invertible, then the loss estimates of Exp3 for linear bandits with the features in their span are
those with the features in `E`. -/
theorem linearExp3Estimate_spanFeatures (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
    (hu : IsUnit (∑ b, p b • rankOne ℝ (spanFeatures φ b) (spanFeatures φ b))) :
    linearExp3Estimate (spanFeatures φ) p = linearExp3Estimate φ p := by
  -- `V(p)` is onto, hence invertible, and its Moore–Penrose inverse is its inverse
  have hVu : IsUnit (∑ b, p b • rankOne ℝ (φ b) (φ b)) := by
    rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_range_eq_top, eq_top_iff, ← hspan]
    exact span_le_range_sum_smul_rankOne φ hu
  funext c ℓ a
  rw [linearExp3Estimate_apply, linearExp3Estimate_apply,
    inner_ringInverse_sum_smul_rankOne_spanFeatures φ hu, moorePenroseInverse_eq_ringInverse hVu,
    coe_coe]

end Estimate

section Algorithm

variable [Fintype α] [FiniteDimensional ℝ E] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace 𝓞] (φ : α → E) (η γ : ℝ)

/-- **Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration**: Exp3 for linear
bandits [LS, Algorithm 15] with learning rate `η` and exploration rate `γ ∈ [0, 1]`, run on the
span of the features `φ`, with the features `spanFeatures φ` and the exploration
`kieferWolfowitzExploration φ`. The features need not span `E`. -/
noncomputable def linearExp3KieferWolfowitz (hγ : γ ∈ Set.Icc 0 1) : Algorithm 𝓞 α ℝ :=
  linearExp3 (spanFeatures φ) (kieferWolfowitzExploration φ) η γ
    (kieferWolfowitzExploration_mem_simplex φ) hγ

lemma linearExp3KieferWolfowitz_def (hγ : γ ∈ Set.Icc 0 1) :
    linearExp3KieferWolfowitz (𝓞 := 𝓞) φ η γ hγ =
      linearExp3 (spanFeatures φ) (kieferWolfowitzExploration φ) η γ
        (kieferWolfowitzExploration_mem_simplex φ) hγ := (rfl)

/-- When the features span `E` and the exploration rate is positive, Exp3 for linear bandits with
the Kiefer–Wolfowitz exploration is Exp3 for linear bandits [LS, Algorithm 15] with the features
`φ` in `E` and the exploration `kieferWolfowitzExploration φ`. -/
theorem linearExp3KieferWolfowitz_eq_linearExp3 (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
    (hγ : γ ∈ Set.Icc 0 1) (hγ0 : 0 < γ) :
    linearExp3KieferWolfowitz (𝓞 := 𝓞) φ η γ hγ =
      linearExp3 φ (kieferWolfowitzExploration φ) η γ
        (kieferWolfowitzExploration_mem_simplex φ) hγ := by
  have hsum (n : ℕ) (h : Hist 𝓞 α ℝ n) :
      linearExp3HistSum (spanFeatures φ) (kieferWolfowitzExploration φ) η γ n h =
        linearExp3HistSum φ (kieferWolfowitzExploration φ) η γ n h := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [linearExp3HistSum_succ, linearExp3HistSum_succ, ih,
        linearExp3Estimate_spanFeatures φ hspan (isUnit_sum_smul_rankOne_linearExp3Weights
          (mem_simplex_iff.1 (kieferWolfowitzExploration_mem_simplex φ)).1
          (isUnit_kieferWolfowitzExploration φ) hγ0 hγ.2 _)]
  rw [linearExp3KieferWolfowitz_def, linearExp3_def, linearExp3_def]
  congr 1
  funext n x
  rw [hsum]

end Algorithm

namespace LinearExp3

variable [Fintype α] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] {φ : α → E} {η γ : ℝ}
  {hγ : γ ∈ Set.Icc 0 1}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α}
  {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {y : (n : ℕ) → Hist 𝓞 α ℝ n × 𝓞 → E} {n : ℕ}

/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration against
an adaptive adversary** [LS, Theorem 27.1, Exercise 21.6]. Let `m` be the dimension of the span of
the features `φ`, which need not span `E`, and `k ≥ 2` the number of arms. Let an adaptive
adversary choose at round `t` the loss vector `y t (h, o) ∈ E`, a measurable function of the
history `h` and the observation `o` of round `t` with `|⟪φ c, y t (h, o)⟫| ≤ 1` for every arm `c`,
and let the feedback `Y t` of a run of `linearExp3KieferWolfowitz φ η γ` be the loss
`⟪φ (A t), y t (h, o)⟫` of the arm played. With the learning rate `η = √(log k / (3 m n))` and the
exploration rate `γ = η m`, the expected regret after `n ≥ 1` rounds against every arm is at most
`2 √(3 m n log k)`. -/
theorem integral_regret_le_kieferWolfowitz [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3KieferWolfowitz φ η γ hγ) env P)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) /
      (3 * finrank ℝ (Submodule.span ℝ (Set.range φ)) * n)))
    (hγm : γ = η * finrank ℝ (Submodule.span ℝ (Set.range φ))) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ (Submodule.span ℝ (Set.range φ)) * n *
        Real.log (Fintype.card α)) := by
  rcases subsingleton_or_nontrivial (Submodule.span ℝ (Set.range φ)) with hW | hW
  · -- all the features vanish, so does the regret
    have hφ (a : α) : φ a = 0 := by
      simpa using congrArg Subtype.val (Subsingleton.elim (spanFeatures φ a) 0)
    simp only [hφ, inner_zero_left, sub_self, sum_const_zero, integral_zero]
    positivity
  -- the run is a run of Exp3 for linear bandits on `W` against the projected adversary
  rw [linearExp3KieferWolfowitz_def] at h
  have key := integral_regret_le_two_mul_sqrt_three
    (y := fun t x ↦ (Submodule.span ℝ (Set.range φ)).orthogonalProjectionOnto (y t x)) h
    (isUnit_kieferWolfowitzExploration φ)
    (inner_ringInverse_kieferWolfowitzExploration_le_finrank φ) hk hn hη hγm
    (fun t ht ↦ (Submodule.span ℝ _).orthogonalProjectionOnto.continuous.measurable.comp
      (hy t ht))
    (fun t ht x c ↦ by rw [inner_spanFeatures_orthogonalProjectionOnto]; exact hy1 t ht x c)
    (fun t ht ↦ by simp only [inner_spanFeatures_orthogonalProjectionOnto]; exact hY t ht) b
  simp only [inner_spanFeatures_orthogonalProjectionOnto] at key
  exact key

/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration against
an adaptive adversary, in terms of the dimension of the space** [LS, Theorem 27.1]. Under the
hypotheses of `LinearExp3.integral_regret_le_kieferWolfowitz`, on a space of dimension `d`, the
expected regret against every arm is at most `2 √(3 d n log k)`. -/
theorem integral_regret_le_sqrt_finrank_kieferWolfowitz [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3KieferWolfowitz φ η γ hγ) env P)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) /
      (3 * finrank ℝ (Submodule.span ℝ (Set.range φ)) * n)))
    (hγm : γ = η * finrank ℝ (Submodule.span ℝ (Set.range φ))) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ E * n * Real.log (Fintype.card α)) := by
  refine (integral_regret_le_kieferWolfowitz h hk hn hη hγm hy hy1 hY b).trans ?_
  have hm : (finrank ℝ (Submodule.span ℝ (Set.range φ)) : ℝ) ≤ finrank ℝ E :=
    Nat.cast_le.2 (Submodule.finrank_le _)
  have hlog : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg (by exact_mod_cast hk.le)
  gcongr

/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration, for
every run against an adaptive adversary** [LS, Theorem 27.1, Exercise 21.6]. Let an adaptive
adversary choose at round `t` the loss vector `y t (h, o) ∈ E`, a measurable function of the
history `h` and of the observation `o` of round `t`, drawn from arbitrary observation kernels `obs`,
with `|⟪φ c, y t (h, o)⟫| ≤ 1` for every arm `c`, and let its environment
`Environment.detFeedback obs (fun t x ↦ ⟪φ x.2, y t x.1⟫) _` return the loss of the arm played.
With the rates of `LinearExp3.integral_regret_le_kieferWolfowitz`, every run of
`linearExp3KieferWolfowitz φ η γ` against it has expected regret at most `2 √(3 m n log k)` against
every arm, where `m` is the dimension of the span of the features. -/
theorem integral_regret_detFeedback_le_kieferWolfowitz [IsProbabilityMeasure P]
    {obs : (n : ℕ) → Kernel (Hist 𝓞 α ℝ n) 𝓞} [∀ n, IsMarkovKernel (obs n)]
    {hf : ∀ n, Measurable fun x : (Hist 𝓞 α ℝ n × 𝓞) × α ↦ ⟪φ x.2, y n x.1⟫_ℝ}
    (h : IsAlgEnvSeq O A Y (linearExp3KieferWolfowitz φ η γ hγ)
      (Environment.detFeedback obs (fun n x ↦ ⟪φ x.2, y n x.1⟫_ℝ) hf) P)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) /
      (3 * finrank ℝ (Submodule.span ℝ (Set.range φ)) * n)))
    (hγm : γ = η * finrank ℝ (Submodule.span ℝ (Set.range φ))) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ (Submodule.span ℝ (Set.range φ)) * n *
        Real.log (Fintype.card α)) :=
  integral_regret_le_kieferWolfowitz h hk hn hη hγm hy hy1
    (fun t _ ↦ h.feedback_detFeedback_ae_eq t) b

end LinearExp3

end LMLExplore.Bandits
