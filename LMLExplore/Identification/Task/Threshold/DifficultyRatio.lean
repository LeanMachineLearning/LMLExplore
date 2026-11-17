/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.Threshold.StaticProportions

/-!
# Positivity has maximal difficulty ratio `K`

The minimum threshold task (*positivity* in [D23]) asks whether some arm has a mean below the
threshold `γ`. Against the static-proportions difficulty `H^{sp}`, the smallest maximal difficulty
ratio of a fixed-budget algorithm family for positivity is `K`, the number of arms
[D23, Theorem 6]. So the bound `K` of uniform sampling for every task
(`LMLExplore.Identification.IdentTask.IsStaticProportions.maxRatio_staticDifficulty_le_card`,
[D23, Theorem 5]) cannot be improved, by uniform sampling or by any other family.

* **No family beats `K`.** Let each arm `a` have a divergence `d_a` on an open set `S_a` of means
  (`IsDivergenceOn`), with `γ ∈ S_a`. Take means `ℓ < γ < m`, the model `μ` with all its means
  equal to `m`, and the models `λ⁽ʲ⁾` that move the arm `j` of `μ` to `ℓ`. The lower bound from
  alternatives along the coordinates ([D23, Corollary 4]) and `H^{sp}(λ⁽ʲ⁾) ≤ d_j(γ, ℓ)⁻¹` bound
  the maximal ratio of every family below by `∑ j, d_j(γ, ℓ) / d_j(m, ℓ)`, which tends to `K` as
  `m` decreases to `γ`.
* **Static proportions with the positivity rule reach `(min_a w a)⁻¹`.** For arms in exponential
  families, a static proportions family with proportions `w` that answers whether some empirical
  mean is below `γ` errs only when the empirical means lie in a closed set on which the rate
  function `x ↦ ∑ a, w a dbar_a(x a, μ a)` is at least the cost of the alternatives. Its error
  exponent is then at least this cost, and its maximal ratio at most `(min_a w a)⁻¹`. This needs no
  assumption on the location of the samples, unlike the bound for every task.

## Main statements

* `LMLExplore.Identification.card_le_maxRatio_staticDifficulty_minThresholdTask_restrict`:
  [D23, proof of Theorem 6], every fixed-budget family has maximal difficulty ratio at least `K`.
* `LMLExplore.Identification.limsup_log_errorProb_div_le_neg_iInf_cost_minThresholdTask_restrict`:
  [D23, proof of Theorem 6], the error exponent of static proportions with the positivity rule.
* `LMLExplore.Identification.maxRatio_staticDifficulty_minThresholdTask_restrict_le`:
  [D23, proof of Theorem 6], their maximal difficulty ratio is at most `(min_a w a)⁻¹`.
* `LMLExplore.Identification.iInf_maxRatio_staticDifficulty_minThresholdTask_restrict`:
  [D23, Theorem 6], the infimum over the fixed-budget families of the maximal difficulty ratio is
  `K`.

## Implementation notes

[D23] states the ratios against the oracle difficulty of the static proportions algorithms, which
is `H^{sp}` for regular tasks ([D23, Theorem 1],
`LMLExplore.Identification.IdentTask.oracleDifficulty_staticClass_eq_staticDifficulty`). Its proof
of the lower bound lets the low mean `ℓ` tend to the lower end of the means, which does not give a
ratio tending to `K` in general; letting the high mean `m` decrease to `γ` does.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author), file `D2023/Theorem6.lean`, commit `4be4d55b7a280ce4323561650013981c111301e2`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Learning

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  [MeasurableSingletonClass α] {S : α → Set ℝ} {d : α → ℝ → ℝ → ℝ} {γ : ℝ}

/-! ### No family beats `K` -/

/-- The lower bound `∑ j, d_j(γ, ℓ) / d_j(m, ℓ)` tends to `K` as `m` decreases to `γ`. -/
private lemma tendsto_sum_div_nhdsGT (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) {ℓ : ℝ} (hℓ : ∀ a, ℓ ∈ S a) (hℓγ : ℓ < γ) :
    Tendsto (fun m ↦ ∑ a, d a γ ℓ / d a m ℓ) (𝓝[>] γ) (𝓝 (Fintype.card α)) := by
  have hpos (a : α) : 0 < d a γ ℓ := (hd a).pos (hγ a) (hℓ a) hℓγ.ne'
  have hK : (Fintype.card α : ℝ) = ∑ a : α, d a γ ℓ / d a γ ℓ := by
    simp [div_self (hpos _).ne']
  rw [hK]
  refine (tendsto_finsetSum _ fun a _ ↦ tendsto_const_nhds.div ?_ (hpos a).ne').mono_left
    nhdsWithin_le_nhds
  have hc : ContinuousAt (fun p : ℝ × ℝ ↦ d a p.1 p.2) (γ, ℓ) :=
    (hd a).continuousOn.continuousAt (prod_mem_nhds ((hd a).isOpen.mem_nhds (hγ a))
      ((hd a).isOpen.mem_nhds (hℓ a)))
  exact (ContinuousAt.comp (f := fun x ↦ (x, ℓ)) hc
    (Continuous.prodMk_left ℓ).continuousAt).tendsto

omit [Fintype α] [MeasurableSingletonClass α] in
/-- A vector of means in `S` with some mean below `γ` or all its means above `γ` is an admissible
model of minimum threshold on the vectors of means in `S`. -/
private lemma mem_M_minThresholdTask_restrict (ν : (α → ℝ) → Kernel α 𝓨)
    [∀ μ, IsMarkovKernel (ν μ)] {μ : α → ℝ} (hμ : ∀ c, μ c ∈ S c)
    (h : (∃ a, μ a < γ) ∨ ∀ a, γ < μ a) :
    μ ∈ ((minThresholdTask ν id γ).restrict {μ | ∀ c, μ c ∈ S c}).M := by
  rw [IdentTask.M_restrict, M_minThresholdTask]
  exact ⟨h, hμ⟩

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Two vectors of means in `S` with the same mean at the arm `c` have the same law at `c`: their
divergence there is `d_c(μ c, μ c) = 0`. -/
private lemma apply_eq_of_apply_eq (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]
    (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hν : ∀ μ : α → ℝ, (∀ c, μ c ∈ S c) → ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    {μ μ' : α → ℝ} (hμ : ∀ c, μ c ∈ S c) (hμ' : ∀ c, μ' c ∈ S c) {c : α} (hc : μ' c = μ c) :
    ν μ' c = ν μ c :=
  klDiv_eq_zero_iff.1 (by rw [hν μ hμ μ' hμ' c, hc, (hd c).apply_self (hμ c), ENNReal.ofReal_zero])

/-- `x / y ≤ (H y)⁻¹` in `ℝ≥0∞` for `y > 0` and `H ≤ x⁻¹`. -/
private lemma ofReal_div_le_inv_mul {x y : ℝ} {H : ℝ≥0∞} (hy : 0 < y)
    (hH : H ≤ (ENNReal.ofReal x)⁻¹) : ENNReal.ofReal (x / y) ≤ (H * ENNReal.ofReal y)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos hy, div_eq_mul_inv, ← inv_inv (ENNReal.ofReal x),
    ← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (ENNReal.ofReal_pos.2 hy).ne')]
  exact ENNReal.inv_le_inv.2 (by gcongr)

/-- The lower bound of positivity at fixed means `ℓ < γ < m`: the maximal difficulty ratio of
every fixed-budget family is at least `∑ j, d_j(γ, ℓ) / d_j(m, ℓ)`, by Corollary 4 of [D23] at the
model with all its means equal to `m` and the alternatives that move one arm to `ℓ`. -/
private lemma ofReal_sum_div_le_maxRatio [MeasurableSpace.CountablyGenerated 𝓨]
    (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]
    (hd : ∀ a, IsDivergenceOn (d a) (S a)) (hγ : ∀ a, γ ∈ S a)
    (hν : ∀ μ : α → ℝ, (∀ c, μ c ∈ S c) → ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 Bool} (h𝒜 : IsFixedBudgetFamily 𝒜) {ℓ m : ℝ}
    (hℓ : ∀ a, ℓ ∈ S a) (hℓγ : ℓ < γ) (hm : ∀ a, m ∈ S a) (hγm : γ < m) :
    ENNReal.ofReal (∑ a, d a γ ℓ / d a m ℓ) ≤
      ((minThresholdTask ν id γ).restrict {μ | ∀ c, μ c ∈ S c}).maxRatio
        ((minThresholdTask ν id γ).restrict {μ | ∀ c, μ c ∈ S c}).staticDifficulty 𝒜 := by
  -- The proof sets up the models `μ` and `λ j` and their answers, disposes of the case where the
  -- probability of error at `μ` does not tend to `0` (the ratio at `μ` is then infinite), and
  -- otherwise bounds each term of Corollary 4 below by `d_j(γ, ℓ) / d_j(m, ℓ)`.
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  set task := (minThresholdTask ν id γ).restrict {μ : α → ℝ | ∀ c, μ c ∈ S c} with htask
  have hνt : task.ν = ν := by simp [htask]
  -- The model `μ` has all its means equal to `m`, and `λ j` moves its arm `j` to `ℓ`.
  set μ : α → ℝ := fun _ ↦ m
  have hμc (c : α) : μ c = m := rfl
  set lam : α → α → ℝ := fun j ↦ Function.update μ j ℓ
  have hlam_self (j : α) : lam j j = ℓ := Function.update_self ..
  have hlam_ne {j c : α} (hc : c ≠ j) : lam j c = m := Function.update_of_ne hc ..
  have hlamS (j : α) : ∀ c, lam j c ∈ S c :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2 ⟨hℓ j, fun c _ ↦ hm c⟩
  have hμM : μ ∈ task.M := mem_M_minThresholdTask_restrict ν hm (Or.inr fun _ ↦ hγm)
  have hlamM (j : α) : lam j ∈ task.M :=
    mem_M_minThresholdTask_restrict ν (hlamS j) (Or.inl ⟨j, (hlam_self j).trans_lt hℓγ⟩)
  have hcorr_μ : task.correct μ = {false} := by
    rw [htask, IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq,
      decide_eq_false (not_exists.2 fun a ha ↦ lt_asymm ha hγm)]
  have hcorr_lam (j : α) : task.correct (lam j) = {true} := by
    rw [htask, IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq,
      decide_eq_true ⟨j, (hlam_self j).trans_lt hℓγ⟩]
  have hdγ (j : α) : 0 < d j γ ℓ := (hd j).pos (hγ j) (hℓ j) hℓγ.ne'
  have hdm (j : α) : 0 < d j m ℓ := (hd j).pos (hm j) (hℓ j) (hℓγ.trans hγm).ne'
  by_cases hp : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)
  swap
  · -- If the probability of error at `μ` does not tend to `0`, the ratio at `μ` is infinite, as
    -- `H^{sp}(μ)` is finite.
    have hfin : task.staticDifficulty μ ≠ ∞ := by
      rw [htask, staticDifficulty_minThresholdTask_restrict_false ν hd hγ hm (hν μ hm)
        fun _ ↦ hγm]
      exact ENNReal.ofReal_ne_top
    rw [IdentTask.maxRatio_eq_top hμM hfin hp]
    exact le_top
  -- Corollary 4 at `μ` with the alternatives `λ j`.
  have hcor := IdentTask.sum_inv_le_iSup_asymptoticRatio task task.staticDifficulty h𝒜 hp
    Finset.univ lam
    (fun j _ ↦ by
      rw [hcorr_μ, hcorr_lam j]
      exact Set.disjoint_singleton.2 Bool.false_ne_true)
    (fun j _ c hc ↦ hνt ▸ apply_eq_of_apply_eq ν hd hν hm (hlamS j) (hlam_ne hc))
    (fun j _ ↦ task.staticDifficulty_ne_zero_of_mem_alternatives (by
        rw [task.alternatives_eq_alt (hcorr_lam j), htask, IdentTask.alt_restrict]
        exact ⟨(mem_alt_minThresholdTask_true_iff ν id).2 fun _ ↦ hγm, hm⟩) fun c ↦ by
      rw [hνt, hν (lam j) (hlamS j) μ hm c]
      exact ENNReal.ofReal_ne_top)
    (fun j _ ↦ ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hdγ j)).ne')
      (hlam_self j ▸ staticDifficulty_minThresholdTask_restrict_le_of_lt ν hd hγ (hlamS j)
        (hν (lam j) (hlamS j)) (j := j) ((hlam_self j).trans_lt hℓγ)))
  calc ENNReal.ofReal (∑ a, d a γ ℓ / d a m ℓ) = ∑ j, ENNReal.ofReal (d j γ ℓ / d j m ℓ) :=
        ENNReal.ofReal_sum_of_nonneg fun j _ ↦ (div_pos (hdγ j) (hdm j)).le
    _ ≤ ∑ j, (task.staticDifficulty (lam j) * klDiv (task.ν μ j) (task.ν (lam j) j))⁻¹ := by
        -- `H^{sp}(λ j) ≤ d_j(γ, ℓ)⁻¹` and `KL(ν_j(μ), ν_j(λ j)) = d_j(m, ℓ)`.
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [hνt, hν (lam j) (hlamS j) μ hm j, hlam_self j, hμc j]
        refine ofReal_div_le_inv_mul (hdm j) ?_
        have h := staticDifficulty_minThresholdTask_restrict_le_of_lt ν hd hγ (hlamS j)
          (hν (lam j) (hlamS j)) (j := j) ((hlam_self j).trans_lt hℓγ)
        rwa [hlam_self j] at h
    _ ≤ ⨆ j ∈ Finset.univ, task.asymptoticRatio task.staticDifficulty 𝒜 (lam j) := hcor
    _ ≤ task.maxRatio task.staticDifficulty 𝒜 :=
        iSup₂_le fun j _ ↦ IdentTask.asymptoticRatio_le_maxRatio (hlamM j)

/-- **No family beats `K` for positivity** [D23, proof of Theorem 6]. Let each arm `c` have a
divergence `d_c` on an open set `S_c` of means, in the sense that
`KL(ν_c(μ'), ν_c(μ)) = d_c(μ' c, μ c)` for all vectors of means `μ`, `μ'` in `S`, and let the
threshold `γ` be in every `S_c`. For the minimum threshold task on the vectors of means in `S`,
every fixed-budget algorithm family has maximal difficulty ratio at least `K` to the
static-proportions difficulty. -/
theorem card_le_maxRatio_staticDifficulty_minThresholdTask_restrict
    [MeasurableSpace.CountablyGenerated 𝓨] (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]
    (hd : ∀ a, IsDivergenceOn (d a) (S a)) (hγ : ∀ a, γ ∈ S a)
    (hν : ∀ μ : α → ℝ, (∀ c, μ c ∈ S c) → ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 Bool} (h𝒜 : IsFixedBudgetFamily 𝒜) :
    (Fintype.card α : ℝ≥0∞) ≤
      ((minThresholdTask ν id γ).restrict {μ | ∀ c, μ c ∈ S c}).maxRatio
        ((minThresholdTask ν id γ).restrict {μ | ∀ c, μ c ∈ S c}).staticDifficulty 𝒜 := by
  have hev : ∀ᶠ t in 𝓝 γ, ∀ a, t ∈ S a :=
    eventually_all.2 fun a ↦ (hd a).isOpen.mem_nhds (hγ a)
  -- A mean `ℓ < γ` of every arm, and the limit `m ↓ γ` of the bound at `ℓ < γ < m`.
  have hlo : ∀ᶠ t in 𝓝[<] γ, ∀ a, t ∈ S a := nhdsWithin_le_nhds hev
  obtain ⟨ℓ, hℓ, hℓγ⟩ := (hlo.and self_mem_nhdsWithin).exists
  rw [← ENNReal.ofReal_natCast]
  refine le_of_tendsto (ENNReal.tendsto_ofReal (tendsto_sum_div_nhdsGT hd hγ hℓ hℓγ)) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with m (hm : γ < m) hmS
  exact ofReal_sum_div_le_maxRatio ν hd hγ hν h𝒜 hℓ hℓγ hmS hm

/-! ### Static proportions with the positivity rule -/

variable {ρ : α → Measure ℝ}

omit [MeasurableSingletonClass α] in
/-- If all the levels `x a` are at least `γ`, the rate `∑ a, w a dbar_a(x a, μ a)` is at least the
cost `∑ a, w a d_a(max (μ a) γ, μ a)` of raising the means of `μ` below `γ` to `γ`. -/
private lemma sum_ofReal_mul_expFamilyDiv_max_le (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans id)
    {μ x w : α → ℝ} (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans id) (hw : 0 ≤ w)
    (hx : ∀ a, γ ≤ x a) :
    ∑ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv id (max (μ a) γ) (μ a)) ≤
      ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate id (x a) (μ a) := by
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [ENNReal.ofReal_mul (hw a)]
  gcongr
  rcases le_total (μ a) γ with hb | hb
  · rw [max_eq_right hb, ← Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hγ a) (hμ a)]
    exact Measure.monotoneOn_expFamilyRate_left (hμ a) hb (hb.trans (hx a)) (hx a)
  · rw [max_eq_left hb, Measure.expFamilyDiv_self, ENNReal.ofReal_zero]
    exact zero_le

omit [MeasurableSingletonClass α] in
/-- If all the means of `μ` are above `γ` and some level `x a` is at most `γ`, the rate
`∑ b, w b dbar_b(x b, μ b)` is at least the cost `min_b w b d_b(γ, μ b)` of moving a single arm to
`γ`. -/
private lemma iInf_ofReal_mul_expFamilyDiv_le (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans id)
    {μ x w : α → ℝ} (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans id) (hw : 0 ≤ w)
    (hgt : ∀ a, γ < μ a) {a : α} (ha : x a ≤ γ) :
    ⨅ b, ENNReal.ofReal (w b * (ρ b).expFamilyDiv id γ (μ b)) ≤
      ∑ b, ENNReal.ofReal (w b) * (ρ b).expFamilyRate id (x b) (μ b) := by
  refine (iInf_le _ a).trans (le_trans ?_ (Finset.single_le_sum
    (f := fun c ↦ ENNReal.ofReal (w c) * (ρ c).expFamilyRate id (x c) (μ c))
    (fun _ _ ↦ zero_le) (Finset.mem_univ a)))
  rw [ENNReal.ofReal_mul (hw a), ← Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hγ a) (hμ a)]
  gcongr
  exact Measure.antitoneOn_expFamilyRate_left (hμ a) (ha.trans (hgt a).le) (hgt a).le ha

omit [Fintype α] [MeasurableSingletonClass α] in
/-- For arms in exponential families in the mean parametrization, the divergence between the arms
of two vectors of means is the divergence `d` of the families. -/
private lemma klDiv_eq_ofReal_expFamilyDiv {ν : (α → ℝ) → Kernel α ℝ}
    (hν : ∀ μ : α → ℝ, (∀ a, μ a ∈ (ρ a).expFamilyMeans id) →
      ∀ a, ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (μ : α → ℝ) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans id)
    (μ' : α → ℝ) (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans id) (c : α) :
    klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv id (μ' c) (μ c)) := by
  rw [hν μ' hμ' c, hν μ hμ c, Measure.klDiv_expFamily_natParam (hμ' c) (hμ c)]

/-- **The error exponent of static proportions for positivity** [D23, proof of Theorem 6]. Let the
arm `a` be in the exponential family generated by `ρ a` with the statistic `id`, not almost
everywhere constant, in the mean parametrization, and let the threshold `γ` be a mean of every
family. Let `𝒜` be a static proportions family with proportions `w` for the minimum threshold task
on the vectors of means of the families, whose recommendation rule answers whether some empirical
mean is below `γ`. Then at every admissible model `μ`,
`limsup_T (1 / T) log p_{μ,T} ≤ -inf_{λ ∈ Alt(μ)} ∑ a, w a KL(ν_a(λ), ν_a(μ))`.

The family errs only when the empirical means lie in the closed set where all of them are at least
`γ` (if some mean of `μ` is below `γ`) or some of them is at most `γ` (otherwise), and there the
rate function `x ↦ ∑ a, w a dbar_a(x a, μ a)` is at least the cost of the alternatives. -/
theorem limsup_log_errorProb_div_le_neg_iInf_cost_minThresholdTask_restrict [DecidableEq α]
    (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hν : ∀ μ : α → ℝ, (∀ a, μ a ∈ (ρ a).expFamilyMeans id) →
      ∀ a, ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans id) {rec : (α → ℝ) → Bool}
    (hrec : ∀ x, rec x = true ↔ ∃ a, x a < γ) {𝒜 : ℕ → IdentAlg Unit α ℝ Bool} {w : α → ℝ}
    (h𝒜 : ((minThresholdTask ν id γ).restrict
      {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).IsStaticProportions rec 𝒜 w) {μ : α → ℝ}
    (hμ : μ ∈ ((minThresholdTask ν id γ).restrict {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).M) :
    limsup (fun T : ℕ ↦ ENNReal.log (((minThresholdTask ν id γ).restrict
        {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).errorProb 𝒜 μ T) / T) atTop ≤
      -((⨅ μ' ∈ ((minThresholdTask ν id γ).restrict
          {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).alternatives μ,
        ((minThresholdTask ν id γ).restrict
          {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).cost w μ' μ : ℝ≥0∞) : EReal) := by
  set task := (minThresholdTask ν id γ).restrict {μ : α → ℝ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}
    with htask
  have hνt : task.ν = ν := by simp [htask]
  have hμ' := hμ
  simp only [htask, IdentTask.M_restrict, M_minThresholdTask, Set.mem_inter_iff,
    Set.mem_ofPred_eq, id_eq] at hμ'
  obtain ⟨hμM, hμS⟩ := hμ'
  have hd (a : α) := isDivergenceOn_expFamilyDiv (hρ a)
  have hw : 0 ≤ w := fun a ↦ (h𝒜.pos a).le
  have hi : task.correct μ = {rec μ} := by
    rw [htask, IdentTask.correct_restrict, correct_minThresholdTask]
    ext i
    simp only [id_eq, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    cases i <;> cases h : rec μ <;> simp [← hrec, h]
  have hν0 (a : α) : 0 ∈ interior (integrableExpSet id (task.ν μ a)) := by
    rw [hνt, hν μ hμS a]
    exact Measure.zero_mem_interior_integrableExpSet_expFamily
      (Measure.natParam_mem_interior_integrableExpSet (hμS a))
  refine (h𝒜.limsup_log_errorProb_div_le hμ (hi ▸ measurableSet_singleton _) hν0).trans
    (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 ?_))
  -- On the arms of `μ`, the Cramér rate functions are the extended divergences of the families.
  simp only [hνt, hν μ hμS, ← Measure.expFamilyRate_def]
  rw [task.alternatives_eq_alt hi, hi]
  refine le_iInf₂ fun x hx ↦ ?_
  by_cases h : ∃ a, μ a < γ
  · -- The answer is `true`: the rule errs when all the empirical means are at least `γ`, and the
    -- cost of the alternatives raises every mean of `μ` below `γ` to `γ`.
    have hrμ : rec μ = true := (hrec μ).2 h
    have hsub : {y : α → ℝ | rec y ∉ ({rec μ} : Set Bool)} ⊆ Set.univ.pi fun _ ↦ Set.Ici γ := by
      intro y hy
      rw [Set.mem_ofPred_eq, hrμ, Set.mem_singleton_iff, hrec] at hy
      exact Set.mem_univ_pi.2 fun a ↦ not_lt.1 fun ha ↦ hy ⟨a, ha⟩
    have hx' (a : α) : γ ≤ x a :=
      Set.mem_univ_pi.1 (closure_minimal hsub (isClosed_set_pi fun _ _ ↦ isClosed_Ici) hx) a
    rw [hrμ, htask, iInf_cost_minThresholdTask_restrict_true ν hd hγ hμS
      (klDiv_eq_ofReal_expFamilyDiv hν μ hμS) hw]
    exact sum_ofReal_mul_expFamilyDiv_max_le hγ hμS hw hx'
  · -- The answer is `false`: the rule errs when some empirical mean is below `γ`, and the cost of
    -- the alternatives moves a single arm to `γ`.
    have hgt : ∀ a, γ < μ a := hμM.resolve_left h
    have hrμ : rec μ = false := by
      rw [← Bool.not_eq_true, hrec]
      exact h
    have hF : IsClosed {x : α → ℝ | ∃ a, x a ≤ γ} := by
      simp only [Set.ofPred_exists]
      exact isClosed_iUnion_of_finite fun a ↦ isClosed_le (continuous_apply a) continuous_const
    obtain ⟨a, ha⟩ : ∃ a, x a ≤ γ := by
      refine closure_minimal (fun y hy ↦ ?_) hF hx
      rw [Set.mem_ofPred_eq, hrμ, Set.mem_singleton_iff, Bool.not_eq_false, hrec] at hy
      obtain ⟨b, hb⟩ := hy
      exact ⟨b, hb.le⟩
    rw [hrμ, htask, iInf_cost_minThresholdTask_restrict_false ν hd hγ hμS
      (klDiv_eq_ofReal_expFamilyDiv hν μ hμS) (fun a ↦ (hgt a).le) hw]
    exact iInf_ofReal_mul_expFamilyDiv_le hγ hμS hw hgt ha

/-- **The maximal difficulty ratio of static proportions for positivity**
[D23, proof of Theorem 6]. In the setting of
`limsup_log_errorProb_div_le_neg_iInf_cost_minThresholdTask_restrict`, the static proportions
family `𝒜` with proportions `w` and the positivity rule has maximal difficulty ratio at most
`(min_a w a)⁻¹` to the static-proportions difficulty. -/
theorem maxRatio_staticDifficulty_minThresholdTask_restrict_le [DecidableEq α]
    (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hν : ∀ μ : α → ℝ, (∀ a, μ a ∈ (ρ a).expFamilyMeans id) →
      ∀ a, ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans id) {rec : (α → ℝ) → Bool}
    (hrec : ∀ x, rec x = true ↔ ∃ a, x a < γ) {𝒜 : ℕ → IdentAlg Unit α ℝ Bool} {w : α → ℝ}
    (h𝒜 : ((minThresholdTask ν id γ).restrict
      {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).IsStaticProportions rec 𝒜 w) :
    ((minThresholdTask ν id γ).restrict {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).maxRatio
        ((minThresholdTask ν id γ).restrict
          {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).staticDifficulty 𝒜 ≤
      (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  have : Nonempty α := nonempty_of_mem_simplex h𝒜.mem_simplex
  rw [IdentTask.maxRatio_def]
  refine iSup₂_le fun μ hμ ↦ IdentTask.asymptoticRatio_staticDifficulty_le_of_limsup_le _ ?_
    (IdentTask.limsup_errorComplexity_le_inv_of_limsup_le_neg
      (limsup_log_errorProb_div_le_neg_iInf_cost_minThresholdTask_restrict ν hρ hν hγ hrec h𝒜
        hμ))
  -- The static-proportions difficulty of `μ` is positive, by its closed form.
  simp only [IdentTask.M_restrict, M_minThresholdTask, Set.mem_inter_iff, Set.mem_ofPred_eq,
    id_eq] at hμ
  obtain ⟨hμM, hμS⟩ := hμ
  have hd (a : α) := isDivergenceOn_expFamilyDiv (hρ a)
  rcases hμM with h | h
  · rw [staticDifficulty_minThresholdTask_restrict_true ν hd hγ hμS
      (klDiv_eq_ofReal_expFamilyDiv hν μ hμS) h, ENNReal.inv_ne_zero]
    exact iSup_ne_top fun a ↦ ENNReal.ofReal_ne_top
  · rw [staticDifficulty_minThresholdTask_restrict_false ν hd hγ hμS
      (klDiv_eq_ofReal_expFamilyDiv hν μ hμS) h]
    exact (ENNReal.ofReal_pos.2 (sum_inv_pos fun a ↦ (hd a).pos (hγ a) (hμS a) (h a).ne)).ne'

/-- **Positivity has maximal difficulty ratio `K`** [D23, Theorem 6]. Let the arm `a` be in the
exponential family generated by `ρ a` with the statistic `id`, not almost everywhere constant, in
the mean parametrization, and let the threshold `γ` be a mean of every family. For the minimum
threshold task on the vectors of means of the families, the infimum over the fixed-budget algorithm
families of the maximal difficulty ratio to the static-proportions difficulty is `K`, the number of
arms. Uniform sampling with the positivity rule attains it. -/
theorem iInf_maxRatio_staticDifficulty_minThresholdTask_restrict [Nonempty α]
    (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)] (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hν : ∀ μ : α → ℝ, (∀ a, μ a ∈ (ρ a).expFamilyMeans id) →
      ∀ a, ν μ a = (ρ a).expFamily id ((ρ a).natParam id (μ a)))
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans id) :
    ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ Bool) (_ : IsFixedBudgetFamily 𝒜),
      ((minThresholdTask ν id γ).restrict {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).maxRatio
        ((minThresholdTask ν id γ).restrict
          {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).staticDifficulty 𝒜 = Fintype.card α := by
  classical
  refine le_antisymm ?_ (le_iInf₂ fun 𝒜 h𝒜 ↦
    card_le_maxRatio_staticDifficulty_minThresholdTask_restrict ν
      (fun a ↦ isDivergenceOn_expFamilyDiv (hρ a)) hγ (klDiv_eq_ofReal_expFamilyDiv hν) h𝒜)
  -- Uniform sampling, recommending whether some empirical mean is below `γ`.
  set rec : (α → ℝ) → Bool := fun x ↦ decide (∃ a, x a < γ)
  have hrec (x : α → ℝ) : rec x = true ↔ ∃ a, x a < γ := decide_eq_true_iff
  have hrecm : Measurable rec := by
    refine measurable_to_bool ?_
    have : rec ⁻¹' {true} = ⋃ a, {x | x a < γ} := by
      ext x
      simp [hrec]
    rw [this]
    exact MeasurableSet.iUnion fun a ↦ measurableSet_lt (measurable_pi_apply a) measurable_const
  obtain ⟨𝒜, h𝒜⟩ := ((minThresholdTask ν id γ).restrict
    {μ | ∀ a, μ a ∈ (ρ a).expFamilyMeans id}).exists_isStaticProportions hrecm
    (w := fun _ ↦ (Fintype.card α : ℝ)⁻¹) (fun _ ↦ by positivity)
    (mem_simplex_iff.1 (uniform_mem_simplex α)).2
  refine (iInf₂_le 𝒜 h𝒜.isFixedBudgetFamily).trans
    ((maxRatio_staticDifficulty_minThresholdTask_restrict_le ν hρ hν hγ hrec h𝒜).trans_eq ?_)
  rw [iInf_const, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
    ENNReal.ofReal_natCast, inv_inv]

end LMLExplore.Identification
