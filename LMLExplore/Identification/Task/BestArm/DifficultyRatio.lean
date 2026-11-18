/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.DifficultyRatio
public import LMLExplore.Identification.Task.BestArm.Basic
public import LMLExplore.Identification.Task.BestArm.StaticProportions
import LMLExplore.Analysis.PSeries
import LMLExplore.InformationTheory.KullbackLeibler.KLFun
import LMLExplore.Logic.Equiv.Fin
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Difficulty ratios in best arm identification

Two results of [D23] on the absence of a complexity in fixed-budget best arm identification, for
a class `𝒞` of algorithm families containing the static proportions algorithms. With Gaussian
arms, the file proves that every consistent fixed-budget family has maximal difficulty ratio at
least `log K / 24` to the characteristic time `T*`, from which [D23, Theorem 8] follows: when the
number `K` of arms is large, no consistent fixed-budget family attains the oracle difficulty `H_𝒞`
of the class at every model. With two Bernoulli arms, the file proves that no fixed-budget family
attains `H_𝒞` at every model [D23, Theorem 10]. Both apply the lower bound from alternatives
along the coordinates (`LMLExplore.Identification.IdentTask.sum_inv_le_iSup_asymptoticRatio`,
[D23, Corollary 4]) at a well-chosen model `μ`, with alternatives `λ⁽ʲ⁾` that differ from `μ` at
the arm `j` only.

**Gaussian arms.** For best arm identification with `K` Gaussian arms of common variance `σ2`,
every consistent fixed-budget algorithm family `𝒜` has maximal difficulty ratio at least
`log K / 24` to the characteristic time `T*`: some admissible model `θ` has
`limsup_T h_{θ,T}(𝒜) / T*(θ) ≥ log K / 24`, with `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))` the error
complexity. In particular, for every `c`, once `log K > 24 c`, no consistent family has asymptotic
difficulty ratio at most `c` to `T*` at every admissible model. For Gaussian arms of the same
variance the divergences are symmetric, so that `T*` is the static-proportions difficulty
`H^{sp}`, which is at least the oracle difficulty `H_𝒞` [D23, Theorem 1]. A ratio to `T*` is then
at most the ratio to `H_𝒞`, and this bound gives [D23, Theorem 8].

The bound takes the model `μ` with the means `0, -1, …, -(K - 1)`, with the alternatives `λ⁽ʲ⁾`
that move the arm `j` of mean `-m` to `m`. The gaps of `λ⁽ʲ⁾` are `m` at the arm of mean `0` and
`m + l` at the arms of mean `-l`, so that `T*(λ⁽ʲ⁾) ≤ 12 σ2 / m` by the bound `T* ≤ 2 H` of
[GK16], while `KL(𝒩(-m, σ2), 𝒩(m, σ2)) = 2 m² / σ2`. The bound of Corollary 4 is then at least
`∑_{m = 1}^{K - 1} 1 / (24 m) ≥ log K / 24`.

**Two Bernoulli arms.** For best arm identification on the Bernoulli bandits with two arms and
means in `(0, 1)`, the infimum over the fixed-budget families of the maximal difficulty ratio to
`H_𝒞` is larger than `1` [D23, Theorem 10]. Corollary 4 at `μ(x) = (x (1 + x), x)`, with the
alternatives `λ⁽⁰⁾ = (x / 2, x)` and `λ⁽¹⁾ = (x (1 + x), 1 / 2)`, and the static-proportions
difficulty of two Bernoulli arms [D23, Lemma 9] bound the maximal ratio to `H^{sp}` below by
`d(z₀, x) / d(x (1 + x), x / 2) + d(z₁, 1 / 2) / d(x, 1 / 2)`, with `z₀` and `z₁` the Chernoff
points of `λ⁽⁰⁾` and `λ⁽¹⁾`. As `x → 0⁺`, the second term tends to `1`, while the first is at least
`klFun (4 / 5) > 0` for `x ≤ 1 / 20`. Since `H_𝒞 ≤ H^{sp}` at the admissible models
[D23, Theorem 1], the ratio to `H_𝒞` is at least the ratio to `H^{sp}`.

## Main statements

* `LMLExplore.Identification.ofReal_log_card_div_le_maxRatio_charTime_baiTask_gaussianBandit`:
  [D23, proof of Theorem 8], `log K / 24 ≤ sup_θ R_{T*,∞}(𝒜, θ)` for every consistent
  fixed-budget family `𝒜`.
* `LMLExplore.Identification.one_lt_iInf_maxRatio_baiTask_bernoulliBandit_two`: [D23, Theorem 10],
  `1 < inf_𝒜 sup_μ R_{H_𝒞,∞}(𝒜, μ)` for two Bernoulli arms.

## Implementation notes

For Theorem 8, [D23] takes the means `0, -2, …, -K`, bounds the ratio to `H_Δ` (with
`H_Δ ≤ T* ≤ 2 H_Δ` [GK16]) below by `(3 / 40) log K` and states the bound `(3 / 80) log K`; its
last inequality fails for `K = 2`. The means `0, -1, …, -(K - 1)` give the larger constant
`1 / 24` for every `K`.

For Theorem 10, [D23] computes the limit of the bound of Corollary 4 as `x → 0`, about `1.22`; the
proof here only bounds it below by `1 + klFun (4 / 5)`, which suffices for the strict inequality.
The paper lets `x` range over `(0, 1 / 2)`, but `λ⁽¹⁾` is an alternative to `μ(x)` only for
`x (1 + x) < 1 / 2`; the proof uses some `x ∈ (0, 1 / 20]`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author), files `Degenne2023Existence/D2023/Theorem8.lean`, commit
  `4be4d55b7a280ce4323561650013981c111301e2`, and `Degenne2023Existence/D2023/Theorem10.lean`,
  commit `b34f7d32c926876cb38dfd51eba1474d44940bb1`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory Learning

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-! ### Gaussian arms with many arms -/

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Let `μ` have the means `μ a = -e a` for a numbering `e` of the arms, and let `j` be an arm other
than the arm `a₀` of number `0`. Moving the arm `j` to the mean `e j` makes it the unique best arm,
and `a₀` a second best arm. -/
private lemma update_rank_lt_and_le [DecidableEq α] {n : ℕ} (e : α ≃ Fin n) {μ : α → ℝ}
    (hμ : ∀ a, μ a = -((e a : ℕ) : ℝ)) {a₀ j : α} (ha₀ : (e a₀ : ℕ) = 0) (hj : j ≠ a₀) :
    (∀ b ≠ j, Function.update μ j (e j : ℕ) b < Function.update μ j (e j : ℕ) j) ∧
      ∀ b ≠ j, Function.update μ j (e j : ℕ) b ≤ Function.update μ j (e j : ℕ) a₀ := by
  have hj' : (1 : ℝ) ≤ (e j : ℕ) := by exact_mod_cast e.one_le_numbering ha₀ hj
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
  have hm : 1 ≤ m := e.one_le_numbering ha₀ hj
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
            exact e.sum_inv_sq_add_numbering_le hm
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
    have : (1 : ℝ) ≤ (e b : ℕ) := by exact_mod_cast e.one_le_numbering ha₀ hb
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
    (fun j hj ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (hlam_lt j (Finset.ne_of_mem_erase hj)))
  calc ENNReal.ofReal (Real.log (Fintype.card α) / 24)
      ≤ ENNReal.ofReal (∑ j ∈ s, (24 * ((e j : ℕ) : ℝ))⁻¹) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp_rw [mul_inv, ← Finset.mul_sum]
        linarith [e.log_card_le_sum_inv_numbering ha₀]
    _ = ∑ j ∈ s, (ENNReal.ofReal (24 * (e j : ℕ)))⁻¹ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have : (0 : ℝ) < (e j : ℕ) := by
          exact_mod_cast e.one_le_numbering ha₀ (Finset.ne_of_mem_erase hj)
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

/-! ### Two Bernoulli arms -/

/-- The Chernoff point `z₀` of the Bernoulli means `(x / 2, x)` (Lemma 9) is in `(0, 4 x / 5]` for
`x ∈ (0, 1 / 20]`: it is `-log u / (log 2 - log u)` with `u = (1 - x) / (1 - x / 2)`, and
`-log u ≤ x / (2 (1 - x))`. -/
private lemma chernoffPoint_half_mem_Ioc {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 20) :
    0 < Real.log ((1 - x) / (1 - x / 2)) / Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x)) ∧
      Real.log ((1 - x) / (1 - x / 2)) / Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x)) ≤
        4 / 5 * x := by
  set u := (1 - x) / (1 - x / 2) with hu
  have h1x : 0 < 1 - x := by linarith
  have h2x : 0 < 1 - x / 2 := by linarith
  have hu0 : 0 < u := div_pos h1x h2x
  have hu1 : u < 1 := (div_lt_one h2x).2 (by linarith)
  have hv : x / 2 * (1 - x) / ((1 - x / 2) * x) = u / 2 := by
    rw [hu]
    field_simp
  have hlogu : Real.log u < 0 := Real.log_neg hu0 hu1
  have hlog2 := Real.log_two_gt_d9
  -- `-log u ≤ x / (2 (1 - x))`
  have hlogu' : -Real.log u ≤ x / 2 / (1 - x) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hu0)
    rw [Real.log_inv] at this
    refine this.trans_eq ?_
    rw [hu]
    field_simp
    ring
  have hz : Real.log u / Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x)) =
      -Real.log u / (Real.log 2 - Real.log u) := by
    rw [hv, Real.log_div hu0.ne' two_ne_zero, ← neg_div_neg_eq, neg_sub]
  rw [hz]
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  have h5 : x / 2 / (1 - x) ≤ 4 / 5 * x * Real.log 2 := by
    rw [div_le_iff₀ h1x]
    have : 1 / 2 < 4 / 5 * Real.log 2 * (1 - x) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left this hx0]
  nlinarith

/-- For `x ∈ (0, 1 / 20]`, `d(x (1 + x), x / 2) ≤ x`, by the bound of the binary relative entropy
by the `χ²`-divergence. -/
private lemma klBer_mul_one_add_half_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 20) :
    klBer (x * (1 + x)) (x / 2) ≤ ENNReal.ofReal x := by
  have hp : x * (1 + x) ∈ Set.Icc 0 1 := ⟨by positivity, by nlinarith⟩
  have hq : x / 2 ∈ Set.Ioo 0 1 := ⟨by positivity, by linarith⟩
  refine (klBer_le_ofReal_sq_sub_div hp hq).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ (mul_pos hq.1 (sub_pos.2 hq.2))]
  have h6 : (1 / 2 + x) ^ 2 ≤ 1 / 2 - x / 4 := by nlinarith
  calc (x * (1 + x) - x / 2) ^ 2 = x ^ 2 * (1 / 2 + x) ^ 2 := by ring
    _ ≤ x ^ 2 * (1 / 2 - x / 4) := mul_le_mul_of_nonneg_left h6 (sq_nonneg x)
    _ = x * (x / 2 * (1 - x / 2)) := by ring

/-- **The first term of the bound** [D23, proof of Theorem 10]. For `x ∈ (0, 1 / 20]`, with `z₀`
the Chernoff point of the Bernoulli means `(x / 2, x)` (Lemma 9),
`klFun (4 / 5) ≤ d(z₀, x) / d(x (1 + x), x / 2)`: `0 < z₀ ≤ 4 x / 5`, so that
`d(z₀, x) ≥ x klFun (z₀ / x) ≥ x klFun (4 / 5)`, and `d(x (1 + x), x / 2) ≤ x`. -/
private lemma ofReal_klFun_le_klBer_mul_inv_klBer {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 20) :
    ENNReal.ofReal (klFun (4 / 5)) ≤
      klBer (Real.log ((1 - x) / (1 - x / 2)) / Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x))) x *
        (klBer (x * (1 + x)) (x / 2))⁻¹ := by
  obtain ⟨hz0, hzx⟩ := chernoffPoint_half_mem_Ioc hx0 hx
  set z := Real.log ((1 - x) / (1 - x / 2)) / Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x))
  have hx1 : x ∈ Set.Ioo 0 1 := ⟨hx0, by linarith⟩
  -- the numerator is at least `x klFun (4 / 5)`
  have hnum : ENNReal.ofReal (x * klFun (4 / 5)) ≤ klBer z x := by
    rw [klBer_eq_ofReal_klBerReal ⟨hz0.le, by linarith⟩ (Set.Ioo_subset_Icc_self hx1)
      (klBer_ne_top hx1)]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left ?_ hx0.le).trans
      (mul_klFun_div_le_klBerReal (by linarith) hx0.ne' hx1.2))
    exact strictAntiOn_klFun.antitoneOn ⟨div_nonneg hz0.le hx0.le, (div_le_one hx0).2 (by linarith)⟩
      (by norm_num) ((div_le_iff₀ hx0).2 (by linarith))
  calc ENNReal.ofReal (klFun (4 / 5))
      = ENNReal.ofReal (x * klFun (4 / 5)) * (ENNReal.ofReal x)⁻¹ := by
        rw [ENNReal.ofReal_mul hx0.le, mul_comm (ENNReal.ofReal x), mul_assoc,
          ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hx0).ne' ENNReal.ofReal_ne_top, mul_one]
    _ ≤ klBer z x * (klBer (x * (1 + x)) (x / 2))⁻¹ := by
        gcongr
        exact klBer_mul_one_add_half_le hx0 hx

/-- **The second term of the bound** [D23, proof of Theorem 10]. With `z₁(x)` the Chernoff point
of the Bernoulli means `(x (1 + x), 1 / 2)` (Lemma 9), `d(z₁(x), 1 / 2) / d(x, 1 / 2) → 1` as
`x → 0⁺`: `z₁(x) → 0`, and both relative entropies tend to `d(0, 1 / 2) = log 2`. -/
private lemma tendsto_klBer_mul_inv_klBer_half :
    Tendsto (fun x : ℝ ↦ klBer (Real.log ((1 - 1 / 2) / (1 - x * (1 + x))) /
        Real.log (x * (1 + x) * (1 - 1 / 2) / ((1 - x * (1 + x)) * (1 / 2)))) (1 / 2) *
      (klBer x (1 / 2))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h12 : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hg : Continuous fun p : ℝ ↦ klBer p (1 / 2) := continuous_klBer_left h12
  have h0 : klBer 0 (1 / 2) ≠ 0 := by
    rw [Ne, klBer_eq_zero_iff (by norm_num) (by norm_num)]
    norm_num
  -- the Chernoff point tends to `0`: its denominator tends to `-∞`
  have hz : Tendsto (fun x : ℝ ↦ Real.log ((1 - 1 / 2) / (1 - x * (1 + x))) /
      Real.log (x * (1 + x) * (1 - 1 / 2) / ((1 - x * (1 + x)) * (1 / 2)))) (𝓝[>] 0) (𝓝 0) := by
    refine Tendsto.div_atBot (a := Real.log ((1 - 1 / 2) / (1 - 0 * (1 + 0)))) ?_ ?_
    · have : ContinuousAt (fun x : ℝ ↦ Real.log ((1 - 1 / 2) / (1 - x * (1 + x)))) 0 := by
        fun_prop (disch := norm_num)
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    · refine Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
      · have : ContinuousAt (fun x : ℝ ↦
            x * (1 + x) * (1 - 1 / 2) / ((1 - x * (1 + x)) * (1 / 2))) 0 := by
          fun_prop (disch := norm_num)
        simpa using this.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
        have : 0 < 1 - x * (1 + x) := by nlinarith [hx.1, hx.2]
        exact Set.mem_Ioi.2 (div_pos (mul_pos (mul_pos hx.1 (by linarith [hx.1])) (by norm_num))
          (mul_pos this (by norm_num)))
  have := ENNReal.Tendsto.div ((hg.tendsto 0).comp hz) (Or.inl h0)
    ((hg.tendsto 0).mono_left nhdsWithin_le_nhds) (Or.inl (klBer_ne_top h12))
  rwa [ENNReal.div_self h0 (klBer_ne_top h12)] at this

/-- **The bound exceeds `1`** [D23, proof of Theorem 10]. Some `x ∈ (0, 1 / 20]` satisfies
`1 < klFun (4 / 5) + d(z₁(x), 1 / 2) / d(x, 1 / 2)`, with `z₁(x)` the Chernoff point of the
Bernoulli means `(x (1 + x), 1 / 2)`: the second term tends to `1` as `x → 0⁺`, and
`klFun (4 / 5) > 0`. -/
private lemma exists_one_lt_ofReal_klFun_add :
    ∃ x : ℝ, 0 < x ∧ x ≤ 1 / 20 ∧ 1 < ENNReal.ofReal (klFun (4 / 5)) +
      klBer (Real.log ((1 - 1 / 2) / (1 - x * (1 + x))) /
        Real.log (x * (1 + x) * (1 - 1 / 2) / ((1 - x * (1 + x)) * (1 / 2)))) (1 / 2) *
      (klBer x (1 / 2))⁻¹ := by
  have hpos : 0 < klFun (4 / 5) := by
    refine (klFun_nonneg (by norm_num)).lt_of_ne fun h ↦ ?_
    have := (klFun_eq_zero_iff (by norm_num : (0 : ℝ) ≤ 4 / 5)).1 h.symm
    norm_num at this
  have hlt : (1 : ℝ≥0∞) < ENNReal.ofReal (klFun (4 / 5)) + 1 := by
    rw [add_comm]
    exact ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.ofReal_pos.2 hpos).ne'
  obtain ⟨x, hx, hx'⟩ := (((tendsto_klBer_mul_inv_klBer_half.const_add
    (ENNReal.ofReal (klFun (4 / 5)))).eventually (lt_mem_nhds hlt)).and
    (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 20))).exists
  exact ⟨x, hx'.1, hx'.2, hx⟩

/-- In best arm identification on the Bernoulli bandits with two arms and means in `(0, 1)`, a
vector of means with distinct arms has a positive and finite static-proportions difficulty, by
Lemma 9. -/
private lemma staticDifficulty_baiTask_bernoulliBandit_two_ne_zero_ne_top {θ : Fin 2 → ℝ}
    (hθ : ∀ c, θ c ∈ Set.Ioo 0 1) (hθ01 : θ 0 ≠ θ 1) :
    ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty θ ≠ 0 ∧
      ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty θ ≠ ∞ := by
  obtain ⟨h0, h1⟩ := inv_staticDifficulty_baiTask_bernoulliBandit_two hθ hθ01 rfl
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.inv_ne_top, h0]
    exact klBer_ne_top (hθ 0)
  · rw [← ENNReal.inv_ne_zero, h0]
    exact klBer_ne_zero_of_klBer_eq (Set.Ioo_subset_Icc_self (hθ 0))
      (Set.Ioo_subset_Icc_self (hθ 1)) hθ01 (h0.symm.trans h1)

/-- In best arm identification on the Bernoulli bandits with two arms and means in `(0, 1)`, the
term of Corollary 4 at a vector of means `θ'` with distinct arms splits as
`(H^{sp}(θ') d(θ j, θ' j))⁻¹ = H^{sp}(θ')⁻¹ d(θ j, θ' j)⁻¹`. -/
private lemma inv_staticDifficulty_mul_klDiv_baiTask_bernoulliBandit_two {θ θ' : Fin 2 → ℝ}
    (hθ' : ∀ c, θ' c ∈ Set.Ioo 0 1) (hθ'01 : θ' 0 ≠ θ' 1) (j : Fin 2) :
    (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty θ' *
        klDiv (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
          Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).ν θ j)
          (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
            Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
              {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).ν θ' j))⁻¹ =
      (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty θ')⁻¹ * (klBer (θ j) (θ' j))⁻¹ := by
  obtain ⟨h0, htop⟩ := staticDifficulty_baiTask_bernoulliBandit_two_ne_zero_ne_top hθ' hθ'01
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl htop)]
  simp [Bandits.bernoulliBandit_apply]

/-- In best arm identification on the Bernoulli bandits with two arms and means in `(0, 1)`, a
vector of means in `(0, 1)²` with the unique best arm `a` is admissible, with correct answer
`a` only. -/
private lemma mem_M_and_correct_eq_baiTask_bernoulliBandit_two {θ : Fin 2 → ℝ}
    (hθ : ∀ c, θ c ∈ Set.Ioo 0 1) {a : Fin 2} (ha : ∀ b ≠ a, θ b < θ a) :
    θ ∈ ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).M ∧
      ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).correct θ = {a} := by
  refine ⟨?_, ?_⟩
  · rw [IdentTask.M_restrict, M_baiTask]
    exact ⟨⟨a, ha⟩, hθ⟩
  · rw [IdentTask.correct_restrict, correct_baiTask_eq_singleton_iff]
    exact ha

/-- **The bound of Corollary 4 in two-armed Bernoulli best arm identification**
[D23, proof of Theorem 10]. For `x ∈ (0, 1 / 20]` and every fixed-budget family `𝒜`, the maximal
difficulty ratio to the static-proportions difficulty is at least
`d(z₀, x) / d(x (1 + x), x / 2) + d(z₁, 1 / 2) / d(x, 1 / 2)`, with `z₀` and `z₁` the Chernoff
points of `(x / 2, x)` and `(x (1 + x), 1 / 2)`: Corollary 4 at `μ = (x (1 + x), x)` with the
alternatives `λ⁽⁰⁾ = (x / 2, x)` and `λ⁽¹⁾ = (x (1 + x), 1 / 2)`, and Lemma 9 at `λ⁽⁰⁾`, `λ⁽¹⁾`. -/
private lemma klBer_add_klBer_le_maxRatio_baiTask_bernoulliBandit_two {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ 1 / 20) {𝒜 : ℕ → IdentAlg Unit (Fin 2) ℝ (Fin 2)} (h𝒜 : IsFixedBudgetFamily 𝒜) :
    klBer (Real.log ((1 - x) / (1 - x / 2)) /
          Real.log (x / 2 * (1 - x) / ((1 - x / 2) * x))) x * (klBer (x * (1 + x)) (x / 2))⁻¹ +
        klBer (Real.log ((1 - 1 / 2) / (1 - x * (1 + x))) /
          Real.log (x * (1 + x) * (1 - 1 / 2) / ((1 - x * (1 + x)) * (1 / 2)))) (1 / 2) *
          (klBer x (1 / 2))⁻¹ ≤
      ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).maxRatio
        ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
          Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
            {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticDifficulty 𝒜 := by
  set task := (baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
    Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1} with htask
  -- The model `μ = (x (1 + x), x)`, with best arm `0`, and the alternatives `λ 0 = (x / 2, x)`
  -- and `λ 1 = (x (1 + x), 1 / 2)`, with best arm `1`.
  set μ : Fin 2 → ℝ := ![x * (1 + x), x]
  set lam : Fin 2 → Fin 2 → ℝ := ![![x / 2, x], ![x * (1 + x), 1 / 2]]
  have hxx : x * (1 + x) ∈ Set.Ioo 0 1 := ⟨by positivity, by nlinarith⟩
  have hx1 : x ∈ Set.Ioo 0 1 := ⟨hx0, by linarith⟩
  have hx2 : x / 2 ∈ Set.Ioo 0 1 := ⟨by positivity, by linarith⟩
  have h12 : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hμI : ∀ c, μ c ∈ Set.Ioo 0 1 := Fin.forall_fin_two.2 ⟨hxx, hx1⟩
  have hlamI : ∀ j c, lam j c ∈ Set.Ioo 0 1 :=
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hx2, hx1⟩, Fin.forall_fin_two.2 ⟨hxx, h12⟩⟩
  have hμ10 : μ 1 < μ 0 := by
    simp only [μ, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith
  have hlam10 : ∀ j, lam j 0 < lam j 1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [lam, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · simp only [lam, Matrix.cons_val_one, Matrix.cons_val_zero]
      nlinarith
  obtain ⟨hμM, hcorrect_μ⟩ := mem_M_and_correct_eq_baiTask_bernoulliBandit_two hμI
    (a := 0) fun b hb ↦ by fin_cases b; exacts [absurd rfl hb, hμ10]
  have hlamM (j : Fin 2) := mem_M_and_correct_eq_baiTask_bernoulliBandit_two (hlamI j)
    (a := 1) fun b hb ↦ by fin_cases b; exacts [hlam10 j, absurd rfl hb]
  have hH (j : Fin 2) :=
    staticDifficulty_baiTask_bernoulliBandit_two_ne_zero_ne_top (hlamI j) (hlam10 j).ne
  -- If the probability of error at `μ` does not tend to `0`, the maximal ratio is infinite.
  by_cases hp : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)
  swap
  · exact le_top.trans_eq (task.maxRatio_eq_top hμM
      (staticDifficulty_baiTask_bernoulliBandit_two_ne_zero_ne_top hμI hμ10.ne').2 hp).symm
  -- Corollary 4 at `μ` with the alternatives `λ 0` and `λ 1`, and Lemma 9 at `λ 0` and `λ 1`.
  have hcor := task.sum_inv_le_iSup_asymptoticRatio task.staticDifficulty h𝒜 hp Finset.univ lam
    (fun j _ ↦ by
      rw [hcorrect_μ, (hlamM j).2]
      exact Set.disjoint_singleton.2 (by decide))
    (fun j _ a ha ↦ by
      simp only [htask, IdentTask.ν_restrict, ν_baiTask, Bandits.bernoulliBandit_apply]
      congr 3
      fin_cases j <;> fin_cases a
      exacts [absurd rfl ha, rfl, rfl, absurd rfl ha])
    (fun j _ ↦ (hH j).1) (fun j _ ↦ (hH j).2)
  rw [Fin.sum_univ_two,
    inv_staticDifficulty_mul_klDiv_baiTask_bernoulliBandit_two (hlamI 0) (hlam10 0).ne,
    inv_staticDifficulty_mul_klDiv_baiTask_bernoulliBandit_two (hlamI 1) (hlam10 1).ne,
    (inv_staticDifficulty_baiTask_bernoulliBandit_two (hlamI 0) (hlam10 0).ne rfl).2,
    (inv_staticDifficulty_baiTask_bernoulliBandit_two (hlamI 1) (hlam10 1).ne rfl).2] at hcor
  exact hcor.trans (iSup₂_le fun j _ ↦ task.asymptoticRatio_le_maxRatio (hlamM j).1)

/-- **No complexity in best arm identification with two Bernoulli arms** [D23, Theorem 10]. For
best arm identification on the Bernoulli bandits with two arms and means in `(0, 1)`, and a class
`𝒞` of algorithm families containing the static proportions algorithms, the infimum over the
fixed-budget algorithm families of the maximal difficulty ratio to the oracle difficulty of `𝒞` is
larger than `1`: `1 < inf_𝒜 sup_{μ ∈ M} R_{H_𝒞,∞}(𝒜, μ)`. No fixed-budget algorithm family
attains the oracle difficulty of the class at every admissible model. -/
theorem one_lt_iInf_maxRatio_baiTask_bernoulliBandit_two
    (𝒞 : Set (ℕ → IdentAlg Unit (Fin 2) ℝ (Fin 2)))
    (h𝒞 : ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
          {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).staticClass id ⊆ 𝒞) :
    1 < ⨅ (𝒜 : ℕ → IdentAlg Unit (Fin 2) ℝ (Fin 2)) (_ : IsFixedBudgetFamily 𝒜),
      ((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
        Set.projIcc 0 1 zero_le_one (μ c)) id).restrict {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).maxRatio
        (((baiTask (fun μ : Fin 2 → ℝ ↦ Bandits.bernoulliBandit fun c ↦
          Set.projIcc 0 1 zero_le_one (μ c)) id).restrict
            {μ | ∀ c, μ c ∈ Set.Ioo 0 1}).oracleDifficulty 𝒞) 𝒜 := by
  obtain ⟨x, hx0, hx20, hx⟩ := exists_one_lt_ofReal_klFun_add
  refine hx.trans_le (le_iInf₂ fun 𝒜 h𝒜 ↦ ?_)
  calc _ ≤ _ := add_le_add_left (ofReal_klFun_le_klBer_mul_inv_klBer hx0 hx20) _
    _ ≤ _ := klBer_add_klBer_le_maxRatio_baiTask_bernoulliBandit_two hx0 hx20 h𝒜
    -- `H_𝒞 ≤ H_{𝒞^{sp}} = H^{sp}` at the admissible models [D23, Theorem 1]
    _ ≤ _ := IdentTask.maxRatio_le_of_le _ 𝒜 fun θ hθ ↦
      (IdentTask.oracleDifficulty_anti _ h𝒞 θ).trans
        (oracleDifficulty_staticClass_baiTask_bernoulliBandit hθ).le

end LMLExplore.Identification
