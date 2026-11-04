/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.OnlineLearning.ExponentialWeights
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Probability.Moments.SubGaussian

/-!
# AdaHedge

AdaHedge [dRvEGK14] is exponential weights on a finite set `α` of `K` experts whose learning rate
tunes itself from the observed losses, with no prior knowledge of their range. At round `t`, for
the cumulative loss vector `L_t = ∑ s < t, ℓ s`, it plays the exponential weights
`w_t = softmax (-(η_t • L_t))` with the learning rate `η_t = log K / Δ_t`, where `Δ_t` is the
cumulative *mixability gap* of the previous rounds. The mixability gap of a round is the
difference `⟨w_t, ℓ_t⟩ - m_t ≥ 0` between the loss of the weights and their *mix loss*
`m_t = -(1/η_t) log ∑ a, w_t a exp (-η_t ℓ_t a)`. While `Δ_t = 0`, in particular at the first
round, the learning rate is infinite and AdaHedge follows the leader: it plays the uniform
distribution on the experts of minimal cumulative loss, with mix loss the smallest loss of these
experts.

The analysis rests on two facts. The mix losses telescope: for a fixed learning rate `η`, the mix
loss of the exponential weights is the increment of the potential
`Φ_η(L) = -(1/η) log ((1/K) ∑ a, exp (-η L a))` (`mixLoss_softmax`), which is at most
`L a + log K / η` and nonincreasing in `η` (`hedgePotential_le_of_le`). Since the learning rates of
AdaHedge decrease, the total mix loss is at most `min_a L_n a + Δ_n`, so that the regret is at most
`2 Δ_n`. The mixability gap of a round is at most the range `b_t` of the losses of the round and,
by Hoeffding's lemma, at most `η_t b_t ^ 2 / 8`; this gives
`Δ_n ^ 2 ≤ (log K / 4) ∑ t < n, b t ^ 2 + (max_t b_t) Δ_n`. The regret of AdaHedge is therefore at
most `√((∑ t < n, b t ^ 2) log K) + 2 max_{t < n} b t`. This implies the bound
`√((∑ t < n, b t ^ 2) log K) + max_{t < n} b t (4/3 log K + 2)` used for the `w`-player of the
pure exploration games of [DKM19, Lemma 3].

## Main definitions

* `LMLExplore.OnlineLearning.mixLoss η w ℓ`: the mix loss `-(1/η) log ∑ a, w a exp (-η ℓ a)`.
* `LMLExplore.OnlineLearning.hedgePotential η L`: the potential
  `-(1/η) log ((1/K) ∑ a, exp (-η L a))` of exponential weights.
* `LMLExplore.OnlineLearning.leaders L`, `LMLExplore.OnlineLearning.ftlWeights L`: the experts of
  minimal cumulative loss and the uniform distribution on them (follow the leader).
* `LMLExplore.OnlineLearning.adaHedgeGap y t`: the cumulative mixability gap `Δ_t` of AdaHedge
  after `t` rounds with the losses `y`.
* `LMLExplore.OnlineLearning.adaHedge y t`: the weights played by AdaHedge at round `t`.

## Main statements

* `log_sum_mul_exp_le`: Hoeffding's lemma for a probability vector `w` and values `ℓ` in an
  interval `[lo, hi]`, `log ∑ a, w a exp (t ℓ a) ≤ t ⟨w, ℓ⟩ + t ^ 2 (hi - lo) ^ 2 / 8`.
* `mixLoss_le_sum_mul`, `sum_mul_le_mixLoss_add`: `⟨w, ℓ⟩ - η (hi - lo) ^ 2 / 8 ≤ m ≤ ⟨w, ℓ⟩`.
* `mixLoss_softmax`: the mix loss of exponential weights is the increment of the potential.
* `hedgePotential_le_of_le`: the potential is nonincreasing in the learning rate.
* `adaHedge_mem_simplex`: AdaHedge plays probability vectors.
* `sum_adaHedge_regret_le_two_mul_adaHedgeGap`: the regret of AdaHedge is at most `2 Δ_n`.
* `adaHedgeGap_le`: `Δ_n ≤ B + √((∑ t < n, b t ^ 2) log K) / 2` for loss ranges `b t ≤ B`.
* `sum_adaHedge_regret_le`: the regret bound `√((∑ t < n, b t ^ 2) log K) + 2 B`.

The definitions of AdaHedge (its state, the follow-the-leader weights and the mix loss at an
infinite learning rate) are adapted from the formalization of [DKM19] in the LMLPapers project
(same author), which states the regret bound without proof.

## References

* [dRvEGK14] S. de Rooij, T. van Erven, P. D. Grünwald and W. M. Koolen, *Follow the leader if you
  can, hedge if you must*, JMLR 15 (2014), Section 2.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemma 3.
-/

public section

open Finset Real MeasureTheory ProbabilityTheory

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

/-! ### Hoeffding's lemma for probability vectors -/

/-- **Hoeffding's lemma** for a probability vector. If `w` is a probability vector and the values
`ℓ a` lie in `[lo, hi]`, then `log ∑ a, w a exp (t ℓ a) ≤ t ⟨w, ℓ⟩ + t ^ 2 (hi - lo) ^ 2 / 8`. -/
theorem log_sum_mul_exp_le {w : α → ℝ} (hw : w ∈ simplex α) {ℓ : α → ℝ} {lo hi : ℝ}
    (hℓ : ∀ a, ℓ a ∈ Set.Icc lo hi) (t : ℝ) :
    log (∑ a, w a * exp (t * ℓ a)) ≤ t * ∑ a, w a * ℓ a + t ^ 2 * (hi - lo) ^ 2 / 8 := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  have _ := isProbabilityMeasure_weightedMeasure hw
  have hint (f : α → ℝ) : ∫ a, f a ∂(weightedMeasure w) = ∑ a, w a * f a := by
    simp [integral_weightedMeasure_eq_sum (mem_simplex_iff.1 hw).1]
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := weightedMeasure w)
    (measurable_of_countable ℓ).aemeasurable (ae_of_all _ hℓ)).mgf_le t
  simp only [mgf, hint] at h
  set m := ∑ a, w a * ℓ a
  have hsplit : ∑ a, w a * exp (t * (ℓ a - m)) = exp (-(t * m)) * ∑ a, w a * exp (t * ℓ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [mul_sub, sub_eq_add_neg, exp_add]
    ring
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ ↦ (0 : ℝ)) (g := w)
    (by simp [(mem_simplex_iff.1 hw).2])
  have hpos : 0 < ∑ a, w a * exp (t * ℓ a) :=
    Finset.sum_pos' (fun b _ ↦ mul_nonneg ((mem_simplex_iff.1 hw).1 b) (exp_pos _).le)
      ⟨a, mem_univ a, mul_pos ha (exp_pos _)⟩
  rw [hsplit, ← le_div_iff₀' (exp_pos _), ← exp_sub] at h
  rw [log_le_iff_le_exp hpos]
  refine h.trans_eq (congrArg exp ?_)
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat,
    div_pow, sq_abs]
  ring

/-! ### The mix loss and the potential of exponential weights -/

/-- The **mix loss** `-(1/η) log ∑ a, w a exp (-η ℓ a)` of the loss vector `ℓ` under the weights
`w`, at the learning rate `η`. -/
noncomputable def mixLoss (η : ℝ) (w ℓ : α → ℝ) : ℝ :=
  -η⁻¹ * log (∑ a, w a * exp (-η * ℓ a))

lemma mixLoss_def (η : ℝ) (w ℓ : α → ℝ) :
    mixLoss η w ℓ = -η⁻¹ * log (∑ a, w a * exp (-η * ℓ a)) := (rfl)

/-- The mix loss is at most the loss `⟨w, ℓ⟩` of the weights, by Jensen's inequality. -/
lemma mixLoss_le_sum_mul {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η) (ℓ : α → ℝ) :
    mixLoss η w ℓ ≤ ∑ a, w a * ℓ a := by
  have hw' := mem_simplex_iff.1 hw
  have h := convexOn_exp.map_sum_le (t := univ) (w := w) (p := fun a ↦ -η * ℓ a)
    (fun a _ ↦ hw'.1 a) hw'.2 (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have hsum : ∑ a, w a * (-η * ℓ a) = -η * ∑ a, w a * ℓ a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [hsum] at h
  have hlog : -η * ∑ a, w a * ℓ a ≤ log (∑ a, w a * exp (-η * ℓ a)) := by
    rw [← log_exp (-η * ∑ a, w a * ℓ a)]
    exact log_le_log (exp_pos _) h
  have h' := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hη.le)
  rw [show η⁻¹ * (-η * ∑ a, w a * ℓ a) = -∑ a, w a * ℓ a by field_simp] at h'
  rw [mixLoss_def, neg_mul]
  linarith

/-- The mix loss is at least `⟨w, ℓ⟩ - η (hi - lo) ^ 2 / 8` for losses in `[lo, hi]`, by Hoeffding's
lemma. -/
lemma sum_mul_le_mixLoss_add {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η)
    {ℓ : α → ℝ} {lo hi : ℝ} (hℓ : ∀ a, ℓ a ∈ Set.Icc lo hi) :
    ∑ a, w a * ℓ a ≤ mixLoss η w ℓ + η * (hi - lo) ^ 2 / 8 := by
  have h := log_sum_mul_exp_le hw hℓ (-η)
  rw [mixLoss_def]
  have h' : η⁻¹ * log (∑ a, w a * exp (-η * ℓ a)) ≤
      η⁻¹ * (-η * ∑ a, w a * ℓ a + (-η) ^ 2 * (hi - lo) ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left h (inv_nonneg.2 hη.le)
  have he : η⁻¹ * (-η * ∑ a, w a * ℓ a + (-η) ^ 2 * (hi - lo) ^ 2 / 8) =
      -∑ a, w a * ℓ a + η * (hi - lo) ^ 2 / 8 := by
    field_simp
  linarith

/-- The mix loss of losses at least `lo` is at least `lo`. -/
lemma le_mixLoss {w : α → ℝ} (hw : w ∈ simplex α) {η : ℝ} (hη : 0 < η) {ℓ : α → ℝ} {lo : ℝ}
    (hℓ : ∀ a, lo ≤ ℓ a) :
    lo ≤ mixLoss η w ℓ := by
  have hw' := mem_simplex_iff.1 hw
  have hle : ∑ a, w a * exp (-η * ℓ a) ≤ exp (-η * lo) := by
    calc ∑ a, w a * exp (-η * ℓ a) ≤ ∑ a, w a * exp (-η * lo) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left
            (exp_le_exp.2 (by nlinarith [hℓ a])) (hw'.1 a)
      _ = exp (-η * lo) := by rw [← Finset.sum_mul, hw'.2, one_mul]
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ ↦ (0 : ℝ)) (g := w)
    (by simp [hw'.2])
  have hpos : 0 < ∑ a, w a * exp (-η * ℓ a) :=
    Finset.sum_pos' (fun b _ ↦ mul_nonneg (hw'.1 b) (exp_pos _).le)
      ⟨a, mem_univ a, mul_pos ha (exp_pos _)⟩
  have hlog : log (∑ a, w a * exp (-η * ℓ a)) ≤ -η * lo := by
    rw [← log_exp (-η * lo)]
    exact log_le_log hpos hle
  rw [mixLoss_def]
  have : η⁻¹ * log (∑ a, w a * exp (-η * ℓ a)) ≤ η⁻¹ * (-η * lo) :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hη.le)
  rw [show η⁻¹ * (-η * lo) = -lo by field_simp] at this
  linarith

/-- The potential `-(1/η) log ((1/K) ∑ a, exp (-η L a))` of exponential weights with learning rate
`η` at the cumulative loss vector `L`, with `K` the cardinality of `α`. -/
noncomputable def hedgePotential (η : ℝ) (L : α → ℝ) : ℝ :=
  -η⁻¹ * log ((∑ a, exp (-η * L a)) / Fintype.card α)

lemma hedgePotential_def (η : ℝ) (L : α → ℝ) :
    hedgePotential η L = -η⁻¹ * log ((∑ a, exp (-η * L a)) / Fintype.card α) := (rfl)

/-- The mix loss of the exponential weights `softmax (-(η • L))` is the increment
`Φ_η(L + ℓ) - Φ_η(L)` of the potential. -/
lemma mixLoss_softmax [Nonempty α] (η : ℝ) (L ℓ : α → ℝ) :
    mixLoss η (softmax (-(η • L))) ℓ = hedgePotential η (L + ℓ) - hedgePotential η L := by
  have hZ : 0 < ∑ a, exp (-η * L a) := Finset.sum_pos (fun a _ ↦ exp_pos _) univ_nonempty
  have hZ' : 0 < ∑ a, exp (-η * (L + ℓ) a) := Finset.sum_pos (fun a _ ↦ exp_pos _) univ_nonempty
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ a, softmax (-(η • L)) a * exp (-η * ℓ a) =
      (∑ a, exp (-η * (L + ℓ) a)) / ∑ a, exp (-η * L a) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [softmax_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, mul_add,
      neg_mul, exp_add]
    ring
  rw [mixLoss_def, hsum, hedgePotential_def, hedgePotential_def, log_div hZ'.ne' hZ.ne',
    log_div hZ'.ne' hK.ne', log_div hZ.ne' hK.ne']
  ring

/-- The potential is at most `L a + log K / η` for every expert `a`. -/
lemma hedgePotential_le {η : ℝ} (hη : 0 < η) (L : α → ℝ) (a : α) :
    hedgePotential η L ≤ L a + log (Fintype.card α) / η := by
  have : Nonempty α := ⟨a⟩
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hle : exp (-η * L a) ≤ ∑ b, exp (-η * L b) :=
    Finset.single_le_sum (f := fun b ↦ exp (-η * L b)) (fun b _ ↦ (exp_pos _).le) (mem_univ a)
  have hlog : -η * L a - log (Fintype.card α) ≤ log ((∑ b, exp (-η * L b)) / Fintype.card α) := by
    rw [log_div (Finset.sum_pos (fun b _ ↦ exp_pos _) univ_nonempty).ne' hK.ne',
      ← log_exp (-η * L a)]
    exact sub_le_sub_right (log_le_log (exp_pos _) hle) _
  rw [hedgePotential_def]
  have : η⁻¹ * (-η * L a - log (Fintype.card α)) ≤
      η⁻¹ * log ((∑ b, exp (-η * L b)) / Fintype.card α) :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hη.le)
  rw [show η⁻¹ * (-η * L a - log (Fintype.card α)) = -(L a + log (Fintype.card α) / η) by
    field_simp; ring] at this
  linarith

/-- The potential is at least every lower bound of the cumulative losses. -/
lemma le_hedgePotential [Nonempty α] {η : ℝ} (hη : 0 < η) {L : α → ℝ} {x : ℝ}
    (hL : ∀ a, x ≤ L a) :
    x ≤ hedgePotential η L := by
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (∑ a, exp (-η * L a)) / Fintype.card α :=
    div_pos (Finset.sum_pos (fun a _ ↦ exp_pos _) univ_nonempty) hK
  have hle : (∑ a, exp (-η * L a)) / Fintype.card α ≤ exp (-η * x) := by
    rw [div_le_iff₀ hK]
    calc ∑ a, exp (-η * L a) ≤ ∑ _a : α, exp (-η * x) :=
          Finset.sum_le_sum fun a _ ↦ exp_le_exp.2 (by nlinarith [hL a])
      _ = exp (-η * x) * Fintype.card α := by simp [mul_comm]
  have hlog : log ((∑ a, exp (-η * L a)) / Fintype.card α) ≤ -η * x := by
    rw [← log_exp (-η * x)]
    exact log_le_log hpos hle
  rw [hedgePotential_def]
  have : η⁻¹ * log ((∑ a, exp (-η * L a)) / Fintype.card α) ≤ η⁻¹ * (-η * x) :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hη.le)
  rw [show η⁻¹ * (-η * x) = -x by field_simp] at this
  linarith

/-- The potential is nonincreasing in the learning rate: for `0 < η' ≤ η`,
`Φ_η(L) ≤ Φ_η'(L)`. This is the power mean inequality. -/
lemma hedgePotential_le_of_le [Nonempty α] {η η' : ℝ} (hη' : 0 < η') (hη : η' ≤ η)
    (L : α → ℝ) :
    hedgePotential η L ≤ hedgePotential η' L := by
  have hη0 : 0 < η := hη'.trans_le hη
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  set p := η / η' with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hη', one_mul]; exact hη
  -- the power mean inequality for the weights `1/K` and the values `exp (-η' L a)`
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow univ (fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (fun a ↦ exp (-η' * L a)) (fun _ _ ↦ inv_nonneg.2 hK.le)
    (by simp [Finset.card_univ, hK.ne']) (fun _ _ ↦ (exp_pos _).le) hp1
  have hpow (a : α) : exp (-η' * L a) ^ p = exp (-η * L a) := by
    rw [← exp_mul, hp]
    congr 1
    field_simp
  simp only [hpow, ← Finset.mul_sum] at hmean
  have hpos' : 0 < (Fintype.card α : ℝ)⁻¹ * ∑ a, exp (-η' * L a) :=
    mul_pos (inv_pos.2 hK) (Finset.sum_pos (fun a _ ↦ exp_pos _) univ_nonempty)
  have hlog := log_le_log (rpow_pos_of_pos hpos' p) hmean
  rw [log_rpow hpos'] at hlog
  rw [hedgePotential_def, hedgePotential_def, div_eq_inv_mul, div_eq_inv_mul]
  have : η⁻¹ * (p * log ((Fintype.card α : ℝ)⁻¹ * ∑ a, exp (-η' * L a))) ≤
      η⁻¹ * log ((Fintype.card α : ℝ)⁻¹ * ∑ a, exp (-η * L a)) :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hη0.le)
  rw [show η⁻¹ * (p * log ((Fintype.card α : ℝ)⁻¹ * ∑ a, exp (-η' * L a))) =
      η'⁻¹ * log ((Fintype.card α : ℝ)⁻¹ * ∑ a, exp (-η' * L a)) by
    rw [hp]; field_simp] at this
  linarith

/-! ### Follow the leader -/

section Leaders

/-- The *leaders* of the cumulative loss vector `L`: the experts of minimal cumulative loss. -/
noncomputable def leaders (L : α → ℝ) : Finset α := {a | ∀ b, L a ≤ L b}

@[simp]
lemma mem_leaders {L : α → ℝ} {a : α} : a ∈ leaders L ↔ ∀ b, L a ≤ L b := by
  simp [leaders]

/-- If all the experts have the same cumulative loss, they are all leaders. -/
lemma leaders_eq_univ {L : α → ℝ} (hL : ∀ a b, L a = L b) : leaders L = univ :=
  Finset.eq_univ_of_forall fun a ↦ mem_leaders.2 fun b ↦ (hL a b).le

/-- The *follow-the-leader weights*: the uniform distribution on the leaders of `L`. -/
noncomputable def ftlWeights (L : α → ℝ) (a : α) : ℝ :=
  if ∀ b, L a ≤ L b then ((#(leaders L) : ℕ) : ℝ)⁻¹ else 0

lemma ftlWeights_def (L : α → ℝ) (a : α) :
    ftlWeights L a = if ∀ b, L a ≤ L b then ((#(leaders L) : ℕ) : ℝ)⁻¹ else 0 := (rfl)

/-- The loss of the follow-the-leader weights is the average loss of the leaders. -/
lemma sum_ftlWeights_mul (L ℓ : α → ℝ) :
    ∑ a, ftlWeights L a * ℓ a = ((#(leaders L) : ℕ) : ℝ)⁻¹ * ∑ a ∈ leaders L, ℓ a := by
  simp_rw [ftlWeights_def, ite_mul, zero_mul, leaders, Finset.sum_filter, Finset.mul_sum,
    mul_ite, mul_zero]

variable [Nonempty α]

lemma leaders_nonempty (L : α → ℝ) : (leaders L).Nonempty := by
  obtain ⟨a, ha⟩ := Finite.exists_min L
  exact ⟨a, mem_leaders.2 ha⟩

lemma ftlWeights_mem_simplex (L : α → ℝ) : ftlWeights L ∈ simplex α := by
  have hcard : (0 : ℝ) < (#(leaders L) : ℕ) := by exact_mod_cast (leaders_nonempty L).card_pos
  refine mem_simplex_iff.2 ⟨fun a ↦ ?_, ?_⟩
  · rw [ftlWeights_def]
    split_ifs
    exacts [inv_nonneg.2 hcard.le, le_rfl]
  · have h := sum_ftlWeights_mul L (fun _ ↦ 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
    rw [h, inv_mul_cancel₀ hcard.ne']

end Leaders

/-! ### AdaHedge -/

section AdaHedge

/-- The weights of AdaHedge in the state `(Δ, L)`, with `Δ` the cumulative mixability gap and `L`
the cumulative loss vector: the exponential weights `softmax (-(η • L))` with learning rate
`η = log K / Δ`, or the follow-the-leader weights when `Δ = 0` (infinite learning rate). -/
noncomputable def adaHedgeWeights (Δ : ℝ) (L : α → ℝ) : α → ℝ :=
  if Δ = 0 then ftlWeights L else softmax (-((log (Fintype.card α) / Δ) • L))

@[simp]
lemma adaHedgeWeights_of_eq_zero (L : α → ℝ) : adaHedgeWeights 0 L = ftlWeights L := by
  simp [adaHedgeWeights]

lemma adaHedgeWeights_of_ne_zero {Δ : ℝ} (hΔ : Δ ≠ 0) (L : α → ℝ) :
    adaHedgeWeights Δ L = softmax (-((log (Fintype.card α) / Δ) • L)) := by
  simp [adaHedgeWeights, hΔ]

variable [Nonempty α]

lemma adaHedgeWeights_mem_simplex (Δ : ℝ) (L : α → ℝ) : adaHedgeWeights Δ L ∈ simplex α := by
  rw [adaHedgeWeights]
  split_ifs
  exacts [ftlWeights_mem_simplex L, softmax_mem_simplex _]

/-- The mix loss of AdaHedge in the state `(Δ, L)` for the loss vector `ℓ`: the mix loss of its
weights at the learning rate `log K / Δ`, or the smallest loss of the leaders when `Δ = 0`. -/
noncomputable def adaHedgeMixLoss (Δ : ℝ) (L ℓ : α → ℝ) : ℝ :=
  if Δ = 0 then (leaders L).inf' (leaders_nonempty L) ℓ
  else mixLoss (log (Fintype.card α) / Δ) (adaHedgeWeights Δ L) ℓ

@[simp]
lemma adaHedgeMixLoss_of_eq_zero (L ℓ : α → ℝ) :
    adaHedgeMixLoss 0 L ℓ = (leaders L).inf' (leaders_nonempty L) ℓ := by
  simp [adaHedgeMixLoss]

lemma adaHedgeMixLoss_of_ne_zero {Δ : ℝ} (hΔ : Δ ≠ 0) (L ℓ : α → ℝ) :
    adaHedgeMixLoss Δ L ℓ = mixLoss (log (Fintype.card α) / Δ) (adaHedgeWeights Δ L) ℓ := by
  simp [adaHedgeMixLoss, hΔ]

/-- The cumulative mixability gap `Δ_t` of AdaHedge after `t` rounds with the losses `y`:
`Δ_0 = 0` and `Δ_{t+1} = Δ_t + ⟨w_t, y t⟩ - m_t`, with `w_t` the weights and `m_t` the mix loss of
AdaHedge at round `t`. -/
noncomputable def adaHedgeGap (y : ℕ → α → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => adaHedgeGap y t +
      (∑ a, adaHedgeWeights (adaHedgeGap y t) (∑ s ∈ range t, y s) a * y t a -
        adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t))

/-- **AdaHedge** [dRvEGK14]: the weights played at round `t` against the losses `y`, the
exponential weights of the cumulative losses `∑ s < t, y s` with the learning rate
`log K / Δ_t`, or the follow-the-leader weights while `Δ_t = 0`. -/
noncomputable def adaHedge (y : ℕ → α → ℝ) (t : ℕ) : α → ℝ :=
  adaHedgeWeights (adaHedgeGap y t) (∑ s ∈ range t, y s)

lemma adaHedge_def (y : ℕ → α → ℝ) (t : ℕ) :
    adaHedge y t = adaHedgeWeights (adaHedgeGap y t) (∑ s ∈ range t, y s) := (rfl)

@[simp]
lemma adaHedgeGap_zero (y : ℕ → α → ℝ) : adaHedgeGap y 0 = 0 := (rfl)

lemma adaHedgeGap_succ (y : ℕ → α → ℝ) (t : ℕ) :
    adaHedgeGap y (t + 1) = adaHedgeGap y t + (∑ a, adaHedge y t a * y t a -
      adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t)) := (rfl)

/-- The cumulative mixability gap is the sum of the mixability gaps of the rounds. -/
lemma adaHedgeGap_eq_sum (y : ℕ → α → ℝ) (n : ℕ) :
    adaHedgeGap y n = ∑ t ∈ range n, (∑ a, adaHedge y t a * y t a -
      adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ← ih, adaHedgeGap_succ]

lemma adaHedge_mem_simplex (y : ℕ → α → ℝ) (t : ℕ) : adaHedge y t ∈ simplex α :=
  adaHedgeWeights_mem_simplex _ _

/-- The mixability gap of a round of follow the leader is nonnegative. -/
private lemma sum_ftlWeights_mul_sub_inf'_nonneg (L ℓ : α → ℝ) :
    0 ≤ ∑ a, ftlWeights L a * ℓ a - (leaders L).inf' (leaders_nonempty L) ℓ := by
  have hcard : (0 : ℝ) < (#(leaders L) : ℕ) := by exact_mod_cast (leaders_nonempty L).card_pos
  rw [sum_ftlWeights_mul, sub_nonneg, le_inv_mul_iff₀ hcard]
  calc ((#(leaders L) : ℕ) : ℝ) * (leaders L).inf' (leaders_nonempty L) ℓ
      = ∑ _a ∈ leaders L, (leaders L).inf' (leaders_nonempty L) ℓ := by simp
    _ ≤ ∑ a ∈ leaders L, ℓ a := Finset.sum_le_sum fun a ha ↦ Finset.inf'_le ℓ ha

/-- The mixability gap of a round is nonnegative, for a nonnegative gap `Δ` whose learning rate
`log K / Δ` is positive when `Δ ≠ 0`. -/
private lemma adaHedge_gap_step_nonneg {Δ : ℝ} (hΔ : Δ ≠ 0 → 0 < log (Fintype.card α) / Δ)
    (L ℓ : α → ℝ) :
    0 ≤ ∑ a, adaHedgeWeights Δ L a * ℓ a - adaHedgeMixLoss Δ L ℓ := by
  by_cases h0 : Δ = 0
  · subst h0
    rw [adaHedgeWeights_of_eq_zero, adaHedgeMixLoss_of_eq_zero]
    exact sum_ftlWeights_mul_sub_inf'_nonneg L ℓ
  · rw [adaHedgeMixLoss_of_ne_zero h0, sub_nonneg]
    exact mixLoss_le_sum_mul (adaHedgeWeights_mem_simplex Δ L) (hΔ h0) ℓ

/-- The mixability gap of a round is at most the range `b` of the losses of the round. -/
private lemma adaHedge_gap_step_le {Δ : ℝ} (hΔ : Δ ≠ 0 → 0 < log (Fintype.card α) / Δ)
    (L : α → ℝ) {ℓ : α → ℝ} {lo b : ℝ} (hℓ : ∀ a, ℓ a ∈ Set.Icc lo (lo + b)) :
    ∑ a, adaHedgeWeights Δ L a * ℓ a - adaHedgeMixLoss Δ L ℓ ≤ b := by
  have hw := mem_simplex_iff.1 (adaHedgeWeights_mem_simplex Δ L)
  have hup : ∑ a, adaHedgeWeights Δ L a * ℓ a ≤ lo + b := by
    calc ∑ a, adaHedgeWeights Δ L a * ℓ a ≤ ∑ a, adaHedgeWeights Δ L a * (lo + b) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hℓ a).2 (hw.1 a)
      _ = lo + b := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hlow : lo ≤ adaHedgeMixLoss Δ L ℓ := by
    by_cases h0 : Δ = 0
    · subst h0
      rw [adaHedgeMixLoss_of_eq_zero]
      exact Finset.le_inf' _ _ fun a _ ↦ (hℓ a).1
    · rw [adaHedgeMixLoss_of_ne_zero h0]
      exact le_mixLoss (adaHedgeWeights_mem_simplex Δ L) (hΔ h0) fun a ↦ (hℓ a).1
  linarith

/-- For `Δ ≠ 0`, the mixability gap of a round is at most `η b ^ 2 / 8` with `η = log K / Δ`, by
Hoeffding's lemma. -/
private lemma adaHedge_gap_step_le_rate {Δ : ℝ} (hΔ : 0 < log (Fintype.card α) / Δ)
    (L : α → ℝ) {ℓ : α → ℝ} {lo b : ℝ} (hℓ : ∀ a, ℓ a ∈ Set.Icc lo (lo + b)) :
    ∑ a, adaHedgeWeights Δ L a * ℓ a - adaHedgeMixLoss Δ L ℓ ≤
      log (Fintype.card α) / Δ * b ^ 2 / 8 := by
  have h0 : Δ ≠ 0 := by rintro rfl; simp at hΔ
  rw [adaHedgeMixLoss_of_ne_zero h0]
  have h := sum_mul_le_mixLoss_add (adaHedgeWeights_mem_simplex Δ L) hΔ hℓ
  rw [add_sub_cancel_left] at h
  linarith

/-- The invariants of AdaHedge: the cumulative gap `Δ_t` is nonnegative, its learning rate
`log K / Δ_t` is positive when `Δ_t ≠ 0`, and all the experts have the same cumulative loss while
`Δ_t = 0`. -/
private lemma adaHedgeGap_invariant (y : ℕ → α → ℝ) (t : ℕ) :
    0 ≤ adaHedgeGap y t ∧ (adaHedgeGap y t ≠ 0 → 0 < log (Fintype.card α) / adaHedgeGap y t) ∧
      (adaHedgeGap y t = 0 → ∀ a b, ∑ s ∈ range t, y s a = ∑ s ∈ range t, y s b) := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨h0, hη, hL⟩ := ih
    set Δ := adaHedgeGap y t
    set L := ∑ s ∈ range t, y s
    set δ := ∑ a, adaHedgeWeights Δ L a * y t a - adaHedgeMixLoss Δ L (y t) with hδ
    have hstep : 0 ≤ δ := adaHedge_gap_step_nonneg hη L (y t)
    have hsucc : adaHedgeGap y (t + 1) = Δ + δ := rfl
    have hLsucc : ∀ a, ∑ s ∈ range (t + 1), y s a = L a + y t a := fun a ↦ by
      simp [L, sum_range_succ]
    by_cases hΔ : Δ = 0
    · -- follow the leader with all the experts tied: the gap is the mean loss minus the minimum
      have hlead : leaders L = univ := leaders_eq_univ fun a b ↦ by
        simpa [L, Finset.sum_apply] using hL hΔ a b
      rw [hΔ, zero_add] at hsucc
      have hδ' : δ = ((Fintype.card α : ℕ) : ℝ)⁻¹ *
          ∑ a, (y t a - univ.inf' univ_nonempty (y t)) := by
        have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
        rw [hδ, hΔ, adaHedgeWeights_of_eq_zero, adaHedgeMixLoss_of_eq_zero, sum_ftlWeights_mul]
        simp only [hlead, card_univ, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        field_simp
      have hterm : ∀ a, 0 ≤ y t a - univ.inf' univ_nonempty (y t) := fun a ↦
        sub_nonneg.2 (Finset.inf'_le _ (mem_univ a))
      refine ⟨hsucc ▸ hstep, fun hne ↦ ?_, fun heq ↦ ?_⟩
      · rw [hsucc] at hne ⊢
        have hδpos : 0 < δ := lt_of_le_of_ne hstep (Ne.symm hne)
        -- a positive gap needs two experts with different losses, so `K ≥ 2`
        obtain ⟨a, -, ha⟩ : ∃ a ∈ univ, 0 < y t a - univ.inf' univ_nonempty (y t) := by
          by_contra hcon
          push Not at hcon
          have : ∑ a, (y t a - univ.inf' univ_nonempty (y t)) ≤ 0 :=
            Finset.sum_nonpos fun a _ ↦ hcon a (mem_univ a)
          rw [hδ'] at hδpos
          nlinarith [inv_pos.2 (show (0 : ℝ) < ((Fintype.card α : ℕ) : ℝ) by
            exact_mod_cast Fintype.card_pos)]
        obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_inf' univ_nonempty (y t)
        have hab : a ≠ b := by rintro rfl; rw [← hb] at ha; simp at ha
        have hK : 1 < Fintype.card α := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
        exact div_pos (log_pos (by exact_mod_cast hK)) hδpos
      · rw [hsucc] at heq
        have hzero : ∀ a, y t a = univ.inf' univ_nonempty (y t) := by
          have hsum : ∑ a, (y t a - univ.inf' univ_nonempty (y t)) = 0 := by
            have hK : (0 : ℝ) < ((Fintype.card α : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
            rw [hδ'] at heq
            rcases mul_eq_zero.1 heq with h | h
            · exact absurd h (inv_ne_zero hK.ne')
            · exact h
          intro a
          have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ hterm a).1 hsum a (mem_univ a)
          linarith
        intro a b
        rw [hLsucc, hLsucc, hzero a, hzero b]
        congr 1
        simpa [L, Finset.sum_apply] using hL hΔ a b
    · -- exponential weights: the gap is positive and grows
      have hΔpos : 0 < Δ := lt_of_le_of_ne h0 (Ne.symm hΔ)
      have hlogK : 0 < log (Fintype.card α) := by
        have := hη hΔ
        rwa [div_pos_iff_of_pos_right hΔpos] at this
      have hpos : 0 < adaHedgeGap y (t + 1) := by rw [hsucc]; linarith
      exact ⟨hpos.le, fun _ ↦ div_pos hlogK hpos, fun h ↦ absurd h hpos.ne'⟩

/-- The cumulative mixability gap of AdaHedge is nonnegative. -/
lemma adaHedgeGap_nonneg (y : ℕ → α → ℝ) (t : ℕ) : 0 ≤ adaHedgeGap y t :=
  (adaHedgeGap_invariant y t).1

/-- The cumulative mixability gap of AdaHedge is nondecreasing, so its learning rate is
nonincreasing. -/
lemma monotone_adaHedgeGap (y : ℕ → α → ℝ) : Monotone (adaHedgeGap y) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  rw [adaHedgeGap_succ, le_add_iff_nonneg_right]
  exact adaHedge_gap_step_nonneg (adaHedgeGap_invariant y t).2.1 _ _

/-- The total mix loss of AdaHedge is at most the potential of the cumulative losses at the current
learning rate, or at most every cumulative loss while the learning rate is infinite. -/
private lemma sum_adaHedgeMixLoss_le (y : ℕ → α → ℝ) (n : ℕ) :
    (adaHedgeGap y n = 0 → ∀ a, ∑ t ∈ range n,
        adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t) ≤
          ∑ t ∈ range n, y t a) ∧
      (adaHedgeGap y n ≠ 0 → ∑ t ∈ range n,
        adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t) ≤
          hedgePotential (log (Fintype.card α) / adaHedgeGap y n) (∑ t ∈ range n, y t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, hη, hL⟩ := adaHedgeGap_invariant y n
    set Δ := adaHedgeGap y n
    set L := ∑ s ∈ range n, y s
    set S := ∑ t ∈ range n, adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t)
    have hmono : Δ ≤ adaHedgeGap y (n + 1) := monotone_adaHedgeGap y n.le_succ
    have hLsucc : ∑ t ∈ range (n + 1), y t = L + y n := sum_range_succ _ _
    simp only [Finset.sum_range_succ]
    by_cases hΔ : Δ = 0
    · -- infinite learning rate, all experts tied: the mix loss is the smallest loss
      have hlead : leaders L = univ := leaders_eq_univ fun a b ↦ by
        simpa [L, Finset.sum_apply] using hL hΔ a b
      have hm : adaHedgeMixLoss Δ L (y n) = univ.inf' univ_nonempty (y n) := by
        rw [hΔ, adaHedgeMixLoss_of_eq_zero]
        simp_rw [hlead]
      have hS : ∀ a, S ≤ L a := fun a ↦ by simpa [L, Finset.sum_apply] using ih.1 hΔ a
      have hle : ∀ a, S + adaHedgeMixLoss Δ L (y n) ≤ (L + y n) a := fun a ↦ by
        rw [hm, Pi.add_apply]
        exact add_le_add (hS a) (Finset.inf'_le (y n) (mem_univ a))
      refine ⟨fun _ a ↦ ?_, fun hne ↦ ?_⟩
      · simpa [L, Finset.sum_apply] using hle a
      · exact le_hedgePotential ((adaHedgeGap_invariant y (n + 1)).2.1 hne) hle
    · -- finite learning rates: the mix loss is the increment of the potential, and the
      -- potential grows when the learning rate decreases
      have hΔpos : 0 < Δ := lt_of_le_of_ne h0 (Ne.symm hΔ)
      have hpos : 0 < adaHedgeGap y (n + 1) := hΔpos.trans_le hmono
      have hlogK : 0 < log (Fintype.card α) := by
        have := hη hΔ
        rwa [div_pos_iff_of_pos_right hΔpos] at this
      have hm : adaHedgeMixLoss Δ L (y n) =
          hedgePotential (log (Fintype.card α) / Δ) (L + y n) -
            hedgePotential (log (Fintype.card α) / Δ) L := by
        rw [adaHedgeMixLoss_of_ne_zero hΔ, adaHedgeWeights_of_ne_zero hΔ, mixLoss_softmax]
      refine ⟨fun h ↦ absurd h hpos.ne', fun _ ↦ ?_⟩
      have hrate : log (Fintype.card α) / adaHedgeGap y (n + 1) ≤ log (Fintype.card α) / Δ :=
        div_le_div_of_nonneg_left hlogK.le hΔpos hmono
      have := hedgePotential_le_of_le (div_pos hlogK hpos) hrate (L + y n)
      have := ih.2 hΔ
      rw [hm]
      linarith

/-- **Regret of AdaHedge** in terms of its cumulative mixability gap: against every expert `a`,
`∑ t < n, (⟨w_t, y t⟩ - y t a) ≤ 2 Δ_n`. -/
theorem sum_adaHedge_regret_le_two_mul_adaHedgeGap (y : ℕ → α → ℝ) (n : ℕ) (a : α) :
    ∑ t ∈ range n, (∑ b, adaHedge y t b * y t b - y t a) ≤ 2 * adaHedgeGap y n := by
  obtain ⟨h0, hη, -⟩ := adaHedgeGap_invariant y n
  have hsplit : ∑ t ∈ range n, (∑ b, adaHedge y t b * y t b - y t a) =
      adaHedgeGap y n + ∑ t ∈ range n,
        adaHedgeMixLoss (adaHedgeGap y t) (∑ s ∈ range t, y s) (y t) -
          ∑ t ∈ range n, y t a := by
    rw [adaHedgeGap_eq_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  by_cases hΔ : adaHedgeGap y n = 0
  · have := (sum_adaHedgeMixLoss_le y n).1 hΔ a
    linarith
  · have hS := (sum_adaHedgeMixLoss_le y n).2 hΔ
    have hpos : 0 < adaHedgeGap y n := lt_of_le_of_ne h0 (Ne.symm hΔ)
    have hlogK : log (Fintype.card α) ≠ 0 := by
      have := hη hΔ
      rw [div_pos_iff_of_pos_right hpos] at this
      exact this.ne'
    have hpot := hedgePotential_le (hη hΔ) (∑ t ∈ range n, y t) a
    rw [div_div_cancel₀ hlogK, Finset.sum_apply] at hpot
    linarith

/-- **The cumulative mixability gap of AdaHedge** [dRvEGK14]. If at each round `t < n` the losses
`y t` have range at most `b t` and `b t ≤ B`, then
`Δ_n ≤ B + √((∑ t < n, b t ^ 2) log K) / 2`. -/
theorem adaHedgeGap_le (y : ℕ → α → ℝ) {n : ℕ} {b : ℕ → ℝ} {B : ℝ}
    (hb : ∀ t < n, ∀ a a', y t a - y t a' ≤ b t) (hB : ∀ t < n, b t ≤ B) (hB0 : 0 ≤ B) :
    adaHedgeGap y n ≤ B + √((∑ t ∈ range n, b t ^ 2) * log (Fintype.card α)) / 2 := by
  have hlogK : 0 ≤ log (Fintype.card α) :=
    log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero)
  -- `Δ_m ^ 2 ≤ (log K / 4) ∑ t < m, b t ^ 2 + B Δ_m`, by induction on `m ≤ n`
  have key : ∀ m ≤ n, adaHedgeGap y m ^ 2 ≤
      log (Fintype.card α) / 4 * ∑ t ∈ range m, b t ^ 2 + B * adaHedgeGap y m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      obtain ⟨h0, hη, -⟩ := adaHedgeGap_invariant y m
      set Δ := adaHedgeGap y m
      set L := ∑ s ∈ range m, y s
      set δ := ∑ a, adaHedgeWeights Δ L a * y m a - adaHedgeMixLoss Δ L (y m) with hδ
      have hsucc : adaHedgeGap y (m + 1) = Δ + δ := rfl
      -- the losses of the round lie in `[lo, lo + b m]`
      set lo := univ.inf' univ_nonempty (y m)
      have hℓ : ∀ a, y m a ∈ Set.Icc lo (lo + b m) := fun a ↦ by
        obtain ⟨a₀, -, ha₀⟩ := Finset.exists_mem_eq_inf' univ_nonempty (y m)
        refine ⟨Finset.inf'_le _ (mem_univ a), ?_⟩
        have := hb m (by omega) a a₀
        rw [← ha₀] at this
        linarith
      have hδ0 : 0 ≤ δ := adaHedge_gap_step_nonneg hη L (y m)
      have hδb : δ ≤ b m := adaHedge_gap_step_le hη L hℓ
      have hbB : b m ≤ B := hB m (by omega)
      have hcross : 2 * Δ * δ ≤ log (Fintype.card α) / 4 * b m ^ 2 := by
        by_cases hΔ : Δ = 0
        · rw [hΔ, mul_zero, zero_mul]
          positivity
        · have hpos : 0 < Δ := lt_of_le_of_ne h0 (Ne.symm hΔ)
          have h := adaHedge_gap_step_le_rate (hη hΔ) L hℓ
          rw [← hδ] at h
          have : 2 * Δ * δ ≤ 2 * Δ * (log (Fintype.card α) / Δ * b m ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left h (by positivity)
          refine this.trans_eq ?_
          field_simp
          ring
      rw [hsucc, sum_range_succ]
      nlinarith
  have hx := key n le_rfl
  set x := adaHedgeGap y n
  set c := √((∑ t ∈ range n, b t ^ 2) * log (Fintype.card α)) / 2
  have hc0 : 0 ≤ c := by positivity
  have hc : c ^ 2 = log (Fintype.card α) / 4 * ∑ t ∈ range n, b t ^ 2 := by
    rw [div_pow, sq_sqrt (mul_nonneg (Finset.sum_nonneg fun t _ ↦ sq_nonneg _) hlogK)]
    ring
  rw [← hc] at hx
  have hx0 : 0 ≤ x := adaHedgeGap_nonneg y n
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **Regret of AdaHedge** [dRvEGK14; DKM19, Lemma 3]. If at each round `t < n` the losses `y t`
have range at most `b t` and `b t ≤ B`, then against every expert `a`,
`∑ t < n, (⟨w_t, y t⟩ - y t a) ≤ √((∑ t < n, b t ^ 2) log K) + 2 B`. The learning rates of
AdaHedge use neither `b` nor `B`. -/
theorem sum_adaHedge_regret_le (y : ℕ → α → ℝ) {n : ℕ} {b : ℕ → ℝ} {B : ℝ}
    (hb : ∀ t < n, ∀ a a', y t a - y t a' ≤ b t) (hB : ∀ t < n, b t ≤ B) (hB0 : 0 ≤ B) (a : α) :
    ∑ t ∈ range n, (∑ a', adaHedge y t a' * y t a' - y t a) ≤
      √((∑ t ∈ range n, b t ^ 2) * log (Fintype.card α)) + 2 * B := by
  have h1 := sum_adaHedge_regret_le_two_mul_adaHedgeGap y n a
  have h2 := adaHedgeGap_le y hb hB hB0
  linarith

end AdaHedge

end LMLExplore.OnlineLearning
