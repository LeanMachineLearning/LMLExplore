/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.OptionalStopping

/-!
# The Robbins–Siegmund theorem

Let `V`, `a`, `b`, `c` be processes with values in `ℝ≥0`, adapted to a filtration `ℱ`, such that
`E[V (n + 1) | ℱ n] + c n ≤ (1 + a n) * V n + b n` almost surely for every `n`, where the
conditional expectation is Mathlib's `MeasureTheory.condLExp` of the coercions to `ℝ≥0∞`. Robbins
and Siegmund [RS71, Theorem 1] proved that, almost surely on the event where `∑ a n` and `∑ b n`
are finite, `V n` converges to a finite limit and `∑ c n` is finite. Such a `V` is an *almost
supermartingale*. The theorem is a convergence tool of stochastic approximation: along the
Robbins–Monro recursion, for instance, the squared distance to the target is an almost
supermartingale.

No integrability is assumed: the conditional expectations are those of `ℝ≥0∞`-valued functions,
which always exist, and the almost sure convergence of `ℝ≥0∞`-valued supermartingales where
their initial value is finite, `ProbabilityTheory.IsENNSupermartingale.ae_exists_tendsto_of_ne_top`,
needs none.

## Main statements

* `LMLExplore.ae_exists_tendsto_and_summable_of_condLExp_add_le`: the Robbins–Siegmund theorem.

## Implementation notes

With the discount `w n = (∏ k < n, (1 + a k))⁻¹`, the partial sums `S n = ∑ k < n, w (k + 1) * b k`
and `D n = ∑ k < n, w (k + 1) * c k`, and a level `M`, the process equal to
`w n * V n + D n + (M - S n)` while `S n ≤ M`, and to `0` afterwards, is an `ℝ≥0∞`-valued
supermartingale, with finite initial value `V 0 + M`. It converges almost surely. On the event
where `∑ a` and `∑ b` are finite, the discounts are bounded below by `exp (-∑ a)` and `S n` stays
below every level `M ≥ ∑ b`, so that `w n * V n + D n` converges. The partial sums `D n` are
then bounded, hence `∑ c` is finite, and `V n` converges.

## References

* [RS71] H. Robbins and D. Siegmund, *A convergence theorem for non negative almost
  supermartingales and some applications*, in *Optimizing Methods in Statistics*, Academic Press
  (1971), 233–257.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal

namespace LMLExplore

namespace RobbinsSiegmund

variable {a b c V : ℕ → ℝ≥0}

/-- The discount `(∏ k < n, (1 + a k))⁻¹`. -/
private noncomputable def disc (a : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := (∏ k ∈ range n, (1 + a k))⁻¹

/-- The discounted partial sums `∑ k < n, disc a (k + 1) * b k`. -/
private noncomputable def dsum (a b : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑ k ∈ range n, disc a (k + 1) * b k

/-- The value at time `n` of the supermartingale of level `M`: `disc a n * V n + dsum a c n +
(M - dsum a b n)` while `dsum a b n ≤ M`, and `0` afterwards. -/
private noncomputable def level (V a b c : ℕ → ℝ≥0) (M : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  if dsum a b n ≤ M then disc a n * V n + dsum a c n + ((M - dsum a b n : ℝ≥0) : ℝ≥0∞) else 0

private lemma disc_succ_mul (n : ℕ) : disc a (n + 1) * (1 + a n) = disc a n := by
  rw [disc, disc, prod_range_succ, mul_inv, inv_mul_cancel_right₀ (by positivity)]

private lemma dsum_succ (n : ℕ) : dsum a b (n + 1) = dsum a b n + disc a (n + 1) * b n :=
  sum_range_succ _ _

private lemma one_le_prod (n : ℕ) : 1 ≤ ∏ k ∈ range n, (1 + a k) :=
  Finset.one_le_prod fun _ _ ↦ le_add_of_nonneg_right zero_le

private lemma disc_le_one (n : ℕ) : disc a n ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_prod n)

private lemma prod_mul_disc_mul (n : ℕ) (x : ℝ≥0) :
    (∏ k ∈ range n, (1 + a k)) * (disc a n * x) = x := by
  rw [disc, ← mul_assoc, mul_inv_cancel₀ (zero_lt_one.trans_le (one_le_prod n)).ne', one_mul]

private lemma dsum_le_sum (n : ℕ) : dsum a b n ≤ ∑ k ∈ range n, b k :=
  sum_le_sum fun _ _ ↦ mul_le_of_le_one_left' (disc_le_one _)

/-- For summable `a`, the products `∏ k < n, (1 + a k)` are bounded by `exp (∑ a)`. -/
private lemma prod_le_exp (ha : Summable a) (n : ℕ) :
    ((∏ k ∈ range n, (1 + a k) : ℝ≥0) : ℝ) ≤ Real.exp (∑' k, (a k : ℝ)) := by
  push_cast
  refine (Real.prod_one_add_le_exp_sum _ fun k ↦ (a k).coe_nonneg).trans
    (Real.exp_le_exp.2 ((NNReal.summable_coe.2 ha).sum_le_tsum _ fun k _ ↦ (a k).coe_nonneg))

/-- The deterministic half of the Robbins–Siegmund theorem: if `∑ a` and `∑ b` are finite and the
process of every level `M` converges to a finite limit, then `V` converges and `∑ c` is
finite. -/
private lemma tendsto_and_summable (ha : Summable a) (hb : Summable b)
    (hZ : ∀ M : ℕ, ∃ L < ∞, Tendsto (level V a b c M) atTop (𝓝 L)) :
    (∃ l, Tendsto V atTop (𝓝 l)) ∧ Summable c := by
  -- The level `M` lies above every partial sum of `b`, hence above every `dsum a b n`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∑' k, b k ≤ M := ⟨⌈∑' k, b k⌉₊, Nat.le_ceil _⟩
  have hSM (n : ℕ) : dsum a b n ≤ M :=
    (dsum_le_sum n).trans ((hb.sum_le_tsum _ fun _ _ ↦ zero_le).trans hM)
  obtain ⟨L, hL, hZL⟩ := hZ M
  -- The process of level `M` is `z n = disc a n * V n + dsum a c n + (M - dsum a b n)`.
  set z : ℕ → ℝ≥0 := fun n ↦ disc a n * V n + dsum a c n + (M - dsum a b n)
  have hz_lim : Tendsto z atTop (𝓝 L.toNNReal) := by
    rw [← ENNReal.tendsto_coe, ENNReal.coe_toNNReal hL.ne]
    refine hZL.congr fun n ↦ ?_
    simp [level, hSM n, z]
  -- The partial sums `dsum a b n` increase and are bounded, so they converge.
  have hS_mono : Monotone (dsum a b) := monotone_nat_of_le_succ fun n ↦ by
    rw [dsum_succ]; exact le_self_add
  have hS_lim := tendsto_atTop_ciSup hS_mono ⟨M, by rintro _ ⟨n, rfl⟩; exact hSM n⟩
  -- Hence `y n = disc a n * V n + dsum a c n` converges.
  have hy_lim : Tendsto (fun n ↦ disc a n * V n + dsum a c n) atTop
      (𝓝 (L.toNNReal - (M - ⨆ n, dsum a b n))) := by
    refine (hz_lim.sub (tendsto_const_nhds.sub hS_lim)).congr fun n ↦ ?_
    simp only [z, add_tsub_cancel_right]
  -- The partial sums `dsum a c n` increase and are bounded, so `∑ k, disc a (k + 1) * c k` is
  -- finite and `disc a n * V n` converges.
  obtain ⟨B, hB⟩ := hy_lim.bddAbove_range
  have hDB (n : ℕ) : dsum a c n ≤ B :=
    le_add_self.trans (hB ⟨n, rfl⟩)
  have hC : Summable fun k ↦ disc a (k + 1) * c k := NNReal.summable_of_sum_range_le hDB
  have hD_lim : Tendsto (dsum a c) atTop (𝓝 (∑' k, disc a (k + 1) * c k)) :=
    hC.hasSum.tendsto_sum_nat
  have hu_lim := (hy_lim.sub hD_lim).congr fun n ↦ add_tsub_cancel_right (disc a n * V n) _
  -- The products `∏ k < n, (1 + a k)` increase and are bounded, so they converge.
  set K : ℝ≥0 := ⟨Real.exp (∑' k, (a k : ℝ)), (Real.exp_pos _).le⟩
  have hβK (n : ℕ) : ∏ k ∈ range n, (1 + a k) ≤ K := by
    rw [← NNReal.coe_le_coe]; exact prod_le_exp ha n
  have hβ_mono : Monotone fun n ↦ ∏ k ∈ range n, (1 + a k) := monotone_nat_of_le_succ fun n ↦ by
    rw [prod_range_succ]; exact le_mul_of_one_le_right' (le_add_of_nonneg_right zero_le)
  have hβ_lim := tendsto_atTop_ciSup hβ_mono ⟨K, by rintro _ ⟨n, rfl⟩; exact hβK n⟩
  refine ⟨⟨_, (hβ_lim.mul hu_lim).congr fun n ↦ prod_mul_disc_mul n (V n)⟩,
    NNReal.summable_of_le (fun k ↦ ?_) (hC.mul_left K)⟩
  calc c k = (∏ i ∈ range (k + 1), (1 + a i)) * (disc a (k + 1) * c k) :=
        (prod_mul_disc_mul (k + 1) (c k)).symm
    _ ≤ K * (disc a (k + 1) * c k) := mul_le_mul_left (hβK _) _

/-- The step of the supermartingale of level `M`, for fixed sequences: if
`p + c n ≤ (1 + a n) * V n + b n`, with `p` in place of the conditional expectation of `V (n + 1)`,
then the value at time `n + 1`, with `p` in place of `V (n + 1)`, is at most the value at
time `n`. -/
private lemma step_le {p : ℝ≥0∞} {M : ℝ≥0} (n : ℕ)
    (hp : p + c n ≤ (((1 + a n) * V n + b n : ℝ≥0) : ℝ≥0∞)) :
    (if dsum a b (n + 1) ≤ M then (disc a (n + 1) : ℝ≥0∞) else 0) * p +
        (if dsum a b (n + 1) ≤ M then
          (dsum a c (n + 1) : ℝ≥0∞) + ((M - dsum a b (n + 1) : ℝ≥0) : ℝ≥0∞) else 0) ≤
      level V a b c M n := by
  split_ifs with h1
  swap
  · simp
  have h0 : dsum a b n + disc a (n + 1) * b n ≤ M := dsum_succ (b := b) n ▸ h1
  rw [level, ite_eq_left (le_self_add.trans h0)]
  have key : (disc a (n + 1) : ℝ≥0∞) * p + disc a (n + 1) * c n ≤
      disc a n * V n + disc a (n + 1) * b n := by
    calc (disc a (n + 1) : ℝ≥0∞) * p + disc a (n + 1) * c n = disc a (n + 1) * (p + c n) := by
          ring
      _ ≤ disc a (n + 1) * (((1 + a n) * V n + b n : ℝ≥0) : ℝ≥0∞) := by gcongr
      _ = disc a n * V n + disc a (n + 1) * b n := by
          rw [← disc_succ_mul n]
          simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_one]
          ring
  have hsub : disc a (n + 1) * b n + (M - dsum a b (n + 1)) = M - dsum a b n := by
    rw [dsum_succ, tsub_add_eq_tsub_tsub]
    exact add_tsub_cancel_of_le (le_tsub_of_add_le_left h0)
  calc (disc a (n + 1) : ℝ≥0∞) * p +
        ((dsum a c (n + 1) : ℝ≥0∞) + ((M - dsum a b (n + 1) : ℝ≥0) : ℝ≥0∞))
      = ((disc a (n + 1) : ℝ≥0∞) * p + disc a (n + 1) * c n) + dsum a c n +
          ((M - dsum a b (n + 1) : ℝ≥0) : ℝ≥0∞) := by
        rw [dsum_succ]
        simp only [ENNReal.coe_add, ENNReal.coe_mul]
        ring
    _ ≤ (disc a n * V n + disc a (n + 1) * b n) + dsum a c n +
          ((M - dsum a b (n + 1) : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = disc a n * V n + dsum a c n + ((M - dsum a b n : ℝ≥0) : ℝ≥0∞) := by
        rw [← hsub]
        simp only [ENNReal.coe_add, ENNReal.coe_mul]
        ring

end RobbinsSiegmund

open RobbinsSiegmund

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {V a b c : ℕ → Ω → ℝ≥0}

/-- The discount `disc a n` of an adapted `a` is known at every time `m ≥ n - 1`. -/
private lemma measurable_disc (ha : Adapted ℱ a) {n m : ℕ} (hnm : n ≤ m + 1) :
    Measurable[ℱ m] fun ω ↦ disc (a · ω) n := by
  unfold disc
  refine Measurable.inv (Finset.measurable_prod _ fun k hk ↦
    measurable_const.add ((ha k).mono (ℱ.mono ?_) le_rfl))
  simp only [mem_range] at hk
  omega

/-- The discounted partial sum `dsum a b n` of adapted `a`, `b` is known at every time
`m ≥ n - 1`. -/
private lemma measurable_dsum (ha : Adapted ℱ a) (hb : Adapted ℱ b) {n m : ℕ} (hnm : n ≤ m + 1) :
    Measurable[ℱ m] fun ω ↦ dsum (a · ω) (b · ω) n := by
  unfold dsum
  refine Finset.measurable_sum _ fun k hk ↦ ?_
  simp only [mem_range] at hk
  exact (measurable_disc ha (by omega)).mul ((hb k).mono (ℱ.mono (by omega)) le_rfl)

/-- The supermartingale of level `M` of the Robbins–Siegmund theorem is an `ℝ≥0∞`-valued
supermartingale. -/
private lemma isENNSupermartingale_level [IsFiniteMeasure P] (hV : Adapted ℱ V)
    (ha : Adapted ℱ a) (hb : Adapted ℱ b) (hc : Adapted ℱ c)
    (h : ∀ n, P⁻[fun ω ↦ (V (n + 1) ω : ℝ≥0∞) | ℱ n] + (fun ω ↦ (c n ω : ℝ≥0∞))
      ≤ᵐ[P] fun ω ↦ (((1 + a n ω) * V n ω + b n ω : ℝ≥0) : ℝ≥0∞)) (M : ℝ≥0) :
    IsENNSupermartingale (fun n ω ↦ level (V · ω) (a · ω) (b · ω) (c · ω) M n) ℱ {P} := by
  refine ⟨fun n ↦ ?_, fun Q hQ n s hs ↦ ?_⟩
  · exact Measurable.ite (measurableSet_le (measurable_dsum ha hb (by omega)) measurable_const)
      ((((measurable_disc ha (by omega)).coe_nnreal_ennreal.mul (hV n).coe_nnreal_ennreal).add
        (measurable_dsum ha hc (by omega)).coe_nnreal_ennreal).add
        (measurable_const.sub (measurable_dsum ha hb (by omega))).coe_nnreal_ennreal)
      measurable_const
  rw [Set.mem_singleton_iff.1 hQ]
  -- The value at time `n + 1` is `g * V (n + 1) + W`, with `g` and `W` known at time `n`.
  set g : Ω → ℝ≥0∞ := fun ω ↦
    if dsum (a · ω) (b · ω) (n + 1) ≤ M then (disc (a · ω) (n + 1) : ℝ≥0∞) else 0
  set W : Ω → ℝ≥0∞ := fun ω ↦ if dsum (a · ω) (b · ω) (n + 1) ≤ M then
    (dsum (a · ω) (c · ω) (n + 1) : ℝ≥0∞) + ((M - dsum (a · ω) (b · ω) (n + 1) : ℝ≥0) : ℝ≥0∞)
    else 0
  have hset : MeasurableSet[ℱ n] {ω | dsum (a · ω) (b · ω) (n + 1) ≤ M} :=
    measurableSet_le (measurable_dsum ha hb le_rfl) measurable_const
  have hg : Measurable[ℱ n] g :=
    Measurable.ite hset (measurable_disc ha le_rfl).coe_nnreal_ennreal measurable_const
  have hW : Measurable W := (Measurable.ite hset
    ((measurable_dsum ha hc le_rfl).coe_nnreal_ennreal.add
      (measurable_const.sub (measurable_dsum ha hb le_rfl)).coe_nnreal_ennreal)
    measurable_const).mono (ℱ.le n) le_rfl
  have hsplit : (fun ω ↦ level (V · ω) (a · ω) (b · ω) (c · ω) M (n + 1)) =
      fun ω ↦ g ω * V (n + 1) ω + W ω := by
    ext ω
    simp only [level, g, W]
    split_ifs <;> simp [add_assoc]
  -- The factor `g` comes out of the conditional expectation given `ℱ n`.
  have hcond := setLIntegral_mul_eq_setLIntegral_mul_of_forall_setLIntegral_eq (ℱ.le n)
    ((hV (n + 1)).mono (ℱ.le _) le_rfl).coe_nnreal_ennreal.aemeasurable
    (measurable_condLExp' (ℱ n) P fun ω ↦ (V (n + 1) ω : ℝ≥0∞)).aemeasurable
    (fun t ht ↦ (setLIntegral_condLExp (ℱ.le n) P _ ht).symm) hg hs
  rw [hsplit, lintegral_add_right _ hW, hcond, ← lintegral_add_right _ hW]
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [h n] with ω hω
  exact step_le n hω

/-- **The Robbins–Siegmund theorem** [RS71, Theorem 1]. Let `V`, `a`, `b`, `c` be adapted
processes with values in `ℝ≥0` such that `E[V (n + 1) | ℱ n] + c n ≤ (1 + a n) * V n + b n`
almost surely for every `n`, with the conditional expectations of the coercions to `ℝ≥0∞`. Then,
almost surely on the event where `∑ a n` and `∑ b n` are finite, `V n` converges to a finite
limit and `∑ c n` is finite. No integrability is assumed. -/
theorem ae_exists_tendsto_and_summable_of_condLExp_add_le [IsFiniteMeasure P] (hV : Adapted ℱ V)
    (ha : Adapted ℱ a) (hb : Adapted ℱ b) (hc : Adapted ℱ c)
    (h : ∀ n, P⁻[fun ω ↦ (V (n + 1) ω : ℝ≥0∞) | ℱ n] + (fun ω ↦ (c n ω : ℝ≥0∞))
      ≤ᵐ[P] fun ω ↦ (((1 + a n ω) * V n ω + b n ω : ℝ≥0) : ℝ≥0∞)) :
    ∀ᵐ ω ∂P, (Summable fun n ↦ a n ω) → (Summable fun n ↦ b n ω) →
      (∃ l : ℝ≥0, Tendsto (fun n ↦ V n ω) atTop (𝓝 l)) ∧ Summable fun n ↦ c n ω := by
  have hconv (M : ℕ) := (isENNSupermartingale_level hV ha hb hc h M).ae_exists_tendsto_of_ne_top
    (Set.mem_singleton P)
  filter_upwards [ae_all_iff.2 hconv] with ω hω ha hb
  refine tendsto_and_summable ha hb fun M ↦ hω M ?_
  simp [level, dsum, disc]

end LMLExplore
