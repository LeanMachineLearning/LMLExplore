/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.DifficultyRatio
public import LMLExplore.Identification.Task.BestArm.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Difficulty ratios of Gaussian best arm identification with many arms

For best arm identification with `K` Gaussian arms of common variance `σ2`, every consistent
fixed-budget algorithm family `𝒜` has maximal difficulty ratio at least `log K / 24` to the
characteristic time `T*`: some admissible model `θ` has `limsup_T h_{θ,T}(𝒜) / T*(θ) ≥ log K / 24`,
with `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))` the error complexity. In particular, for every
`c`, once `log K > 24 c`, no consistent family has asymptotic difficulty ratio at most `c` to `T*`
at every admissible model.

This is the lower bound of [D23, Theorem 8]. For Gaussian arms of the same variance the divergences
are symmetric, so that `T*` is the static-proportions difficulty `H^{sp}`, which is at least the
oracle difficulty `H_𝒞` of every class `𝒞` of algorithm families containing the static proportions
algorithms [D23, Theorem 1]. A ratio to `T*` is then at most the ratio to `H_𝒞`, and the bound of
this file gives [D23, Theorem 8]: no such class admits a complexity when `K` is large.

The bound is the lower bound from alternatives along the coordinates
(`LMLExplore.Identification.IdentTask.sum_inv_le_iSup_asymptoticRatio`, [D23, Corollary 4]) at the
model `μ` with the means `0, -1, …, -(K - 1)`, with the alternatives `λ⁽ʲ⁾` that move the arm `j`
of mean `-m` to `m`. The gaps of `λ⁽ʲ⁾` are `m` at the arm of mean `0` and `m + l` at the arms of
mean `-l`, so that `T*(λ⁽ʲ⁾) ≤ 12 σ2 / m` by the bound `T* ≤ 2 H` of [GK16], while
`KL(𝒩(-m, σ2), 𝒩(m, σ2)) = 2 m² / σ2`. The bound of Corollary 4 is then at least
`∑_{m = 1}^{K - 1} 1 / (24 m) ≥ log K / 24`.

## Main statements

* `LMLExplore.Identification.ofReal_log_card_div_le_maxRatio_charTime_baiTask_gaussianBandit`:
  [D23, proof of Theorem 8], `log K / 24 ≤ sup_θ R_{T*,∞}(𝒜, θ)` for every consistent
  fixed-budget family `𝒜`.

## Implementation notes

[D23] takes the means `0, -2, …, -K`, bounds the ratio to `H_Δ` (with `H_Δ ≤ T* ≤ 2 H_Δ` [GK16])
below by `(3 / 40) log K` and states the bound `(3 / 80) log K`; its last inequality fails for
`K = 2`. The means `0, -1, …, -(K - 1)` give the larger constant `1 / 24` for every `K`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author), file `Degenne2023Existence/D2023/Theorem8.lean`, commit
  `4be4d55b7a280ce4323561650013981c111301e2`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory Learning

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- For a numbering `e` of the arms, `∑_{b} 1 / (m + e b)² ≤ 2 / m` for every integer `m ≥ 1`. -/
private lemma sum_inv_sq_add_le (e : α ≃ Fin (Fintype.card α)) {m : ℕ} (hm : 1 ≤ m) :
    ∑ b, (((m : ℝ) + (e b : ℕ)) ^ 2)⁻¹ ≤ 2 / m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  calc ∑ b, ((((k + 1 : ℕ) : ℝ) + (e b : ℕ)) ^ 2)⁻¹
      = ∑ i ∈ Finset.range (Fintype.card α), ((((k + 1 : ℕ) : ℝ) + i) ^ 2)⁻¹ := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = ∑ i ∈ Finset.Ioo k (k + 1 + Fintype.card α), ((i : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range,
          Nat.add_sub_cancel_left]
        exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
    _ ≤ 2 / (k + 1) := sum_Ioo_inv_sq_le k _
    _ = 2 / ((k + 1 : ℕ) : ℝ) := by push_cast; ring

omit [Fintype α] [MeasurableSingletonClass α] in
/-- In a numbering `e` of the arms, every arm other than the arm `a₀` of number `0` has a positive
number. -/
private lemma one_le_rank {n : ℕ} (e : α ≃ Fin n) {a₀ a : α} (ha₀ : (e a₀ : ℕ) = 0)
    (ha : a ≠ a₀) : 1 ≤ (e a : ℕ) :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ ha (e.injective (Fin.ext (h.trans ha₀.symm)))

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Let `μ` have the means `μ a = -e a` for a numbering `e` of the arms, and let `j` be an arm other
than the arm `a₀` of number `0`. Moving the arm `j` to the mean `e j` makes it the unique best arm,
and `a₀` a second best arm. -/
private lemma update_rank_lt_and_le [DecidableEq α] {n : ℕ} (e : α ≃ Fin n) {μ : α → ℝ}
    (hμ : ∀ a, μ a = -((e a : ℕ) : ℝ)) {a₀ j : α} (ha₀ : (e a₀ : ℕ) = 0) (hj : j ≠ a₀) :
    (∀ b ≠ j, Function.update μ j (e j : ℕ) b < Function.update μ j (e j : ℕ) j) ∧
      ∀ b ≠ j, Function.update μ j (e j : ℕ) b ≤ Function.update μ j (e j : ℕ) a₀ := by
  have hj' : (1 : ℝ) ≤ (e j : ℕ) := by exact_mod_cast one_le_rank e ha₀ hj
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · simp only [Function.update_self, Function.update_of_ne hb, hμ]
    linarith [(Nat.cast_nonneg (e b : ℕ) : (0 : ℝ) ≤ (e b : ℕ))]
  · simp [Function.update_of_ne hb, Function.update_of_ne hj.symm, hμ, ha₀]

/-- In Gaussian best arm identification, let `μ` have the means `μ a = -e a` for a numbering `e` of
the arms, and let `j` be an arm other than the arm `a₀` of number `0`, with `m = e j`. The model
`λ` that moves the arm `j` to `m`
satisfies `T*(λ) KL(𝒩(μ j, σ2), 𝒩(λ j, σ2)) ≤ 24 m`: `T*(λ) ≤ 12 σ2 / m` by the bound `T* ≤ 2 H`
of [GK16], and the divergence is `2 m² / σ2`. -/
private lemma charTime_update_mul_klDiv_le [DecidableEq α] (hσ2 : σ2 ≠ 0)
    (e : α ≃ Fin (Fintype.card α)) {μ : α → ℝ} (hμ : ∀ a, μ a = -((e a : ℕ) : ℝ)) {a₀ j : α}
    (ha₀ : (e a₀ : ℕ) = 0) (hj : j ≠ a₀) :
    (baiTask (Bandits.gaussianBandit · σ2) id).charTime (Function.update μ j (e j : ℕ)) *
        klDiv (gaussianReal (μ j) σ2) (gaussianReal (e j : ℕ) σ2) ≤
      ENNReal.ofReal (24 * (e j : ℕ)) := by
  obtain ⟨hlam_lt, hlam_le⟩ := update_rank_lt_and_le e hμ ha₀ hj
  set m : ℕ := (e j : ℕ)
  have hm : 1 ≤ m := one_le_rank e ha₀ hj
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hσ2' : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  set lam := Function.update μ j (m : ℝ) with hlam_def
  have hlj : lam j = m := by simp [hlam_def]
  have hlam (b : α) (hb : b ≠ j) : lam b = -((e b : ℕ) : ℝ) := by simp [hlam_def, hb, hμ]
  -- The bound `T* ≤ 2 H` with `H(λ) ≤ 6 σ2 / m`.
  have hH : 2 * (σ2 : ℝ) / (lam j - lam a₀) ^ 2 +
      ∑ b ∈ Finset.univ.erase j, 2 * σ2 / (lam j - lam b) ^ 2 ≤ 6 * σ2 / m := by
    have h1 : 2 * (σ2 : ℝ) / (lam j - lam a₀) ^ 2 ≤ 2 * σ2 / m := by
      rw [hlj, hlam a₀ hj.symm, ha₀, Nat.cast_zero, neg_zero, sub_zero]
      gcongr
      nlinarith [(Nat.one_le_cast.2 hm : (1 : ℝ) ≤ m)]
    have h2 : ∑ b ∈ Finset.univ.erase j, 2 * (σ2 : ℝ) / (lam j - lam b) ^ 2 ≤
        2 * (σ2 : ℝ) * (2 / m) := by
      calc ∑ b ∈ Finset.univ.erase j, 2 * (σ2 : ℝ) / (lam j - lam b) ^ 2
          = ∑ b ∈ Finset.univ.erase j, 2 * σ2 * (((m : ℝ) + (e b : ℕ)) ^ 2)⁻¹ := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            rw [hlj, hlam b (Finset.ne_of_mem_erase hb), sub_neg_eq_add,
              div_eq_mul_inv]
        _ ≤ ∑ b, 2 * (σ2 : ℝ) * (((m : ℝ) + (e b : ℕ)) ^ 2)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ ↦ by positivity
        _ ≤ 2 * σ2 * (2 / m) := by
            rw [← Finset.mul_sum]
            gcongr
            exact sum_inv_sq_add_le e hm
    calc _ ≤ 2 * (σ2 : ℝ) / m + 2 * σ2 * (2 / m) := add_le_add h1 h2
      _ = 6 * σ2 / m := by ring
  have hT : (baiTask (Bandits.gaussianBandit · σ2) id).charTime lam ≤
      ENNReal.ofReal (12 * σ2 / m) :=
    (charTime_baiTask_gaussianBandit_le hσ2 hj.symm hlam_lt hlam_le).trans
      (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hH zero_le_two).trans_eq (by ring)))
  have hKL : klDiv (gaussianReal (μ j) σ2) (gaussianReal (m : ℝ) σ2) =
      ENNReal.ofReal (2 * (m : ℝ) ^ 2 / σ2) := by
    rw [klDiv_gaussianReal_gaussianReal_same_var hσ2, hμ]
    congr 1
    field_simp
    ring
  rw [hKL]
  calc (baiTask (Bandits.gaussianBandit · σ2) id).charTime lam *
        ENNReal.ofReal (2 * (m : ℝ) ^ 2 / σ2)
      ≤ ENNReal.ofReal (12 * σ2 / m) * ENNReal.ofReal (2 * (m : ℝ) ^ 2 / σ2) := by gcongr
    _ = ENNReal.ofReal (24 * m) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- For a numbering `e` of the `K` arms and an arm `a₀` of number `0`,
`log K ≤ ∑_{j ≠ a₀} 1 / e j`, the harmonic number `H_{K - 1}`. -/
private lemma log_card_le_sum_inv [DecidableEq α] (e : α ≃ Fin (Fintype.card α)) {a₀ : α}
    (ha₀ : (e a₀ : ℕ) = 0) :
    Real.log (Fintype.card α) ≤ ∑ j ∈ Finset.univ.erase a₀, (((e j : ℕ) : ℝ))⁻¹ := by
  rw [Finset.sum_erase _ (by simp [ha₀])]
  have hsum : ∑ j, (((e j : ℕ) : ℝ))⁻¹ =
      ∑ i ∈ Finset.range (Fintype.card α), ((i : ℝ))⁻¹ := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [hsum]
  rcases Nat.eq_zero_or_eq_succ_pred (Fintype.card α) with hK | hK
  · simp [hK]
  rw [hK, Finset.sum_range_succ', Nat.cast_zero, inv_zero, add_zero]
  calc Real.log ((Fintype.card α).pred.succ : ℝ)
      ≤ harmonic (Fintype.card α).pred := log_add_one_le_harmonic _
    _ = _ := by simp [harmonic]

/-- **Lower bound on the difficulty ratio in Gaussian best arm identification**
[D23, proof of Theorem 8]. For best arm identification with Gaussian arms of common variance
`σ2 ≠ 0`, every consistent fixed-budget algorithm family `𝒜` has maximal difficulty ratio at least
`log K / 24` to the characteristic time `T*`, with `K` the number of arms:
`log K / 24 ≤ sup_{θ ∈ M} limsup_T h_{θ,T}(𝒜) / T*(θ)`. -/
theorem ofReal_log_card_div_le_maxRatio_charTime_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    {𝒜 : ℕ → IdentAlg Unit α ℝ α} (h𝒜 : IsFixedBudgetFamily 𝒜)
    (hcons : (baiTask (Bandits.gaussianBandit · σ2) id).IsConsistent 𝒜) :
    ENNReal.ofReal (Real.log (Fintype.card α) / 24) ≤
      (baiTask (Bandits.gaussianBandit · σ2) id).maxRatio
        (baiTask (Bandits.gaussianBandit · σ2) id).charTime 𝒜 := by
  classical
  set task := baiTask (Bandits.gaussianBandit · σ2) (id : (α → ℝ) → α → ℝ)
  -- For `K ≤ 1`, the bound is `0`.
  rcases lt_or_ge (Fintype.card α) 2 with hK | hK
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos
      (Nat.cast_nonneg _) (by exact_mod_cast Nat.lt_succ_iff.1 hK)) (by norm_num))]
    exact zero_le
  -- The arms are numbered `e a = 0, …, K - 1`, and `a₀` has number `0`.
  set e := Fintype.equivFin α
  set a₀ := e.symm ⟨0, by omega⟩
  have ha₀ : (e a₀ : ℕ) = 0 := by simp [a₀]
  -- The model `μ` has the means `μ a = -e a`, and `λ j` moves the arm `j` to `e j`.
  set μ : α → ℝ := fun a ↦ -((e a : ℕ) : ℝ)
  set lam : α → α → ℝ := fun j ↦ Function.update μ j (e j : ℕ)
  have hμ_lt (b : α) (hb : b ≠ a₀) : μ b < μ a₀ := by
    have : (1 : ℝ) ≤ (e b : ℕ) := by exact_mod_cast one_le_rank e ha₀ hb
    simp only [μ, ha₀, Nat.cast_zero, neg_zero]
    linarith
  have hlam_lt (j : α) (hj : j ≠ a₀) := (update_rank_lt_and_le e (fun _ ↦ rfl) ha₀ hj).1
  have hcorrect_lam (j : α) (hj : j ≠ a₀) : task.correct (lam j) = {j} :=
    (correct_baiTask_eq_singleton_iff _ id).2 (hlam_lt j hj)
  have hlamM (j : α) (hj : j ≠ a₀) : lam j ∈ task.M := by
    rw [M_baiTask]
    exact ⟨j, hlam_lt j hj⟩
  set s := Finset.univ.erase a₀
  -- Corollary 4 at `μ` with the alternatives `λ j`, `j ≠ a₀`.
  have hcor := task.sum_inv_le_iSup_asymptoticRatio task.charTime h𝒜
    (IdentTask.isConsistent_iff.1 hcons μ (by rw [M_baiTask]; exact ⟨a₀, hμ_lt⟩)) s lam
    (fun j hj ↦ by
      rw [(correct_baiTask_eq_singleton_iff _ id).2 hμ_lt,
        hcorrect_lam j (Finset.ne_of_mem_erase hj)]
      exact Set.disjoint_singleton.2 (Finset.ne_of_mem_erase hj).symm)
    (fun j _ b hb ↦ by simp [task, lam, hb, μ])
    (fun j hj ↦ charTime_baiTask_gaussianBandit_ne_zero hσ2 (Finset.ne_of_mem_erase hj).symm
      (hlam_lt j (Finset.ne_of_mem_erase hj)))
    (fun j hj ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (Finset.ne_of_mem_erase hj).symm
      (hlam_lt j (Finset.ne_of_mem_erase hj)))
  calc ENNReal.ofReal (Real.log (Fintype.card α) / 24)
      ≤ ENNReal.ofReal (∑ j ∈ s, (24 * ((e j : ℕ) : ℝ))⁻¹) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp_rw [mul_inv, ← Finset.mul_sum]
        linarith [log_card_le_sum_inv e ha₀]
    _ = ∑ j ∈ s, (ENNReal.ofReal (24 * (e j : ℕ)))⁻¹ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have : (0 : ℝ) < (e j : ℕ) := by
          exact_mod_cast one_le_rank e ha₀ (Finset.ne_of_mem_erase hj)
        rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    _ ≤ ∑ j ∈ s, (task.charTime (lam j) * klDiv (task.ν μ j) (task.ν (lam j) j))⁻¹ := by
        refine Finset.sum_le_sum fun j hj ↦ ENNReal.inv_le_inv.2 ?_
        simpa [task, lam] using charTime_update_mul_klDiv_le hσ2 e (fun _ ↦ rfl) ha₀
          (Finset.ne_of_mem_erase hj)
    _ ≤ ⨆ j ∈ s, task.asymptoticRatio task.charTime 𝒜 (lam j) := hcor
    _ = ⨆ θ ∈ lam '' s, task.asymptoticRatio task.charTime 𝒜 θ := by
        rw [iSup_image]
        simp only [Finset.mem_coe]
    _ ≤ task.maxRatio task.charTime 𝒜 := by
        refine IdentTask.iSup_asymptoticRatio_le_maxRatio ?_
        rintro _ ⟨j, hj, rfl⟩
        exact hlamM j (Finset.ne_of_mem_erase hj)

end LMLExplore.Identification
