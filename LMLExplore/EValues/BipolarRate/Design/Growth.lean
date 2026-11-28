/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
import LMLExplore.Data.EReal.Inv
import TauCeti.Data.EReal.Operations

/-!
# The growth of the designs proportional to a vector

Finitely many sources `a : α` produce observations, and a design `n : α → ℕ` observes the source
`a` exactly `n a` times (`ProbabilityTheory.designValue`). For a vector `x : α → ℝ≥0` of
proportions, the designs `⌈m (x + ε 𝟙_{supp x})⌉` observe each source of the support of `x` about
`m (x a + ε)` times and the other sources never. Their growth (written D-bar in [EVR26])

  `G x = ⨅ ε > 0, liminf_{m → ∞} designValue μ Λ ⌈m (x + ε 𝟙_{supp x})⌉ / m`

is the constant of the sharp form of the Wald inequality with a design [EVR26, Note 41,
Theorem 1]: an e-variable at a stopping time `τ` of finite mean of an algorithm has expected
logarithm at most `G (𝔼_μ[N τ])`, with `N τ` the vector of the numbers of observations of each
source. `ProbabilityTheory.integral_truncLog_le_designGrowth` proves it for a round that reads a
bounded number of observations, and `Learning.IsAlgEnvSeq.eintegral_log_le_designGrowth` for an
algorithm and the hitting time of a stopping rule. The growth refines
the rate of the designs: `G x ≤ D* * ∑ a, x a` with `D* = designRate μ Λ`, and it is also at most
the entropy bound `⨅ ν ∈ Λ, ∑ a, x a * klDiv (μ a) (ν a)`.

## Main definitions

* `ProbabilityTheory.proportionalDesign x ε m`: the design `⌈m (x + ε 𝟙_{supp x})⌉`.
* `ProbabilityTheory.designGrowth μ Λ x`: the growth `G x` of the designs proportional to `x`.

## Main statements

* `ProbabilityTheory.le_designGrowth_of_forall_sub_le`: `ℓ ≤ G x` as soon as, for every
  `ε > 0`, the value of the design `⌈m (x + ε 𝟙_{supp x})⌉` is at least `m ℓ` up to a constant.
* `ProbabilityTheory.designGrowth_le_sum_mul_of_forall_designValue_le`: if the value of every
  design `n` is at most `∑ a, n a * w a`, then `G x ≤ ∑ a, x a * w a`.
* `ProbabilityTheory.designGrowth_le_designRate_mul`: `G x ≤ D* * ∑ a, x a`.
* `ProbabilityTheory.designGrowth_le_iInf_sum_mul_klDiv`: the entropy bound
  `G x ≤ ⨅ ν ∈ Λ, ∑ a, x a * klDiv (μ a) (ν a)`.
* `ProbabilityTheory.designGrowth_le_mul_bipolarRate_of_forall_ne`: if the instances of `Λ`
  differ from `μ` at the source `a` only, `G x ≤ x a * d`, with `d` the bipolar rate of `μ a`
  against the laws of the source `a` in `Λ`. This is the bound that turns the Wald inequality
  with a design into a lower bound on the number of observations of the source `a`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Sections 1, 2 and 7.
-/

public section

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α 𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : α → Measure 𝓧}
  {Λ : Set (α → Measure 𝓧)} {x y : α → ℝ≥0} {ε : ℝ≥0} {m : ℕ}

/-! ### The designs proportional to a vector -/

/-- The design `⌈m (x + ε 𝟙_{supp x})⌉` proportional to `x : α → ℝ≥0`: it observes a source `a`
with `x a ≠ 0` exactly `⌈m (x a + ε)⌉` times, and the other sources never. -/
noncomputable def proportionalDesign (x : α → ℝ≥0) (ε : ℝ≥0) (m : ℕ) : α → ℕ :=
  fun a ↦ if x a = 0 then 0 else ⌈(m : ℝ≥0) * (x a + ε)⌉₊

lemma proportionalDesign_of_eq_zero {a : α} (h : x a = 0) : proportionalDesign x ε m a = 0 := by
  simp [proportionalDesign, h]

lemma proportionalDesign_of_ne_zero {a : α} (h : x a ≠ 0) :
    proportionalDesign x ε m a = ⌈(m : ℝ≥0) * (x a + ε)⌉₊ := by
  simp [proportionalDesign, h]

@[simp]
lemma proportionalDesign_zero (ε : ℝ≥0) (m : ℕ) : proportionalDesign (0 : α → ℝ≥0) ε m = 0 :=
  funext fun _ ↦ proportionalDesign_of_eq_zero rfl

/-- The design proportional to `x` observes a source `a` with `x a ≠ 0` at least `m (x a + ε)`
times. -/
lemma le_proportionalDesign {a : α} (h : x a ≠ 0) :
    (m : ℝ≥0) * (x a + ε) ≤ proportionalDesign x ε m a := by
  rw [proportionalDesign_of_ne_zero h]
  exact Nat.le_ceil _

/-- The design proportional to `x` observes a source `a` at most `m (x a + ε) + 1` times. -/
lemma proportionalDesign_le (x : α → ℝ≥0) (ε : ℝ≥0) (m : ℕ) (a : α) :
    (proportionalDesign x ε m a : ℝ≥0) ≤ m * (x a + ε) + 1 := by
  by_cases h : x a = 0
  · simp [proportionalDesign_of_eq_zero h]
  · rw [proportionalDesign_of_ne_zero h]
    exact (Nat.ceil_lt_add_one zero_le).le

/-- The design proportional to `x` is monotone in `x`. -/
lemma proportionalDesign_mono (h : x ≤ y) :
    proportionalDesign x ε m ≤ proportionalDesign y ε m := by
  intro a
  by_cases hx : x a = 0
  · simp [proportionalDesign_of_eq_zero hx]
  have hy : y a ≠ 0 := (pos_iff_ne_zero.2 hx |>.trans_le (h a)).ne'
  rw [proportionalDesign_of_ne_zero hx, proportionalDesign_of_ne_zero hy]
  gcongr
  exact h a

/-- `k` copies of the design `⌈q x⌉` proportional to `x`, with no margin, fit in the design
proportional to `x` with margin `ε` and `m` observations, as soon as `1 ≤ q ε` and `k q ≤ m`. -/
lemma nsmul_proportionalDesign_le {q k : ℕ} (hqε : 1 ≤ (q : ℝ≥0) * ε)
    (hkq : (k : ℝ≥0) * q ≤ m) : k • proportionalDesign x 0 q ≤ proportionalDesign x ε m := by
  intro a
  by_cases hx : x a = 0
  · simp [proportionalDesign_of_eq_zero hx]
  rw [Pi.smul_apply, smul_eq_mul, proportionalDesign_of_ne_zero hx,
    proportionalDesign_of_ne_zero hx, add_zero]
  refine Nat.cast_le.1 (le_trans ?_ (Nat.le_ceil ((m : ℝ≥0) * (x a + ε))))
  -- `k ⌈q x a⌉ ≤ k (q x a + 1) ≤ m x a + m ε`
  have hceil : (⌈(q : ℝ≥0) * x a⌉₊ : ℝ≥0) ≤ q * x a + 1 := (Nat.ceil_lt_add_one zero_le).le
  have hkε : (k : ℝ≥0) ≤ m * ε := by
    calc (k : ℝ≥0) ≤ k * (q * ε) := le_mul_of_one_le_right zero_le hqε
    _ = k * q * ε := (mul_assoc _ _ _).symm
    _ ≤ m * ε := by gcongr
  push_cast
  calc (k : ℝ≥0) * ⌈(q : ℝ≥0) * x a⌉₊ ≤ k * (q * x a + 1) := by gcongr
  _ = k * q * x a + k := by ring
  _ ≤ m * x a + m * ε := by gcongr
  _ = m * (x a + ε) := (mul_add _ _ _).symm

/-! ### The growth of the designs proportional to a vector -/

variable [Fintype α]

/-- The growth of the designs proportional to `x : α → ℝ≥0` for the instance `μ` against the set
of instances `Λ`: `G x = ⨅ ε > 0, liminf_{m → ∞} designValue μ Λ ⌈m (x + ε 𝟙_{supp x})⌉ / m`
[EVR26, Note 41, Section 1]. -/
noncomputable def designGrowth (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) :
    EReal :=
  ⨅ (ε : ℝ≥0) (_ : 0 < ε),
    liminf (fun m : ℕ ↦ designValue μ Λ (proportionalDesign x ε m) / (m : EReal)) atTop

lemma designGrowth_def (μ : α → Measure 𝓧) (Λ : Set (α → Measure 𝓧)) (x : α → ℝ≥0) :
    designGrowth μ Λ x = ⨅ (ε : ℝ≥0) (_ : 0 < ε),
      liminf (fun m : ℕ ↦ designValue μ Λ (proportionalDesign x ε m) / (m : EReal)) atTop :=
  (rfl)

/-- **Lower bounds on the growth.** If for every `ε > 0` there is a constant `C` such that the
value of the design `⌈m (x + ε 𝟙_{supp x})⌉` is at least `m ℓ - C` for every `m ≥ 1`, then
`ℓ ≤ designGrowth μ Λ x`. -/
theorem le_designGrowth_of_forall_sub_le {ℓ : ℝ}
    (h : ∀ ε : ℝ≥0, 0 < ε → ∃ C : ℝ, ∀ m : ℕ, 0 < m →
      ((m * ℓ - C : ℝ) : EReal) ≤ designValue μ Λ (proportionalDesign x ε m)) :
    (ℓ : EReal) ≤ designGrowth μ Λ x := by
  refine le_iInf₂ fun ε hε ↦ ?_
  obtain ⟨C, hC⟩ := h ε hε
  -- the lower bounds `ℓ - C / m` of the values per observation tend to `ℓ`
  have h_tendsto : Tendsto (fun m : ℕ ↦ ((ℓ - C / m : ℝ) : EReal)) atTop (𝓝 (ℓ : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto ℓ).comp ?_
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  rw [← h_tendsto.liminf_eq]
  refine liminf_le_liminf ((eventually_gt_atTop 0).mono fun m hm ↦ ?_)
  rw [EReal.coe_le_div_natCast_iff hm]
  convert hC m hm using 2
  field_simp

/-- **Upper bounds on the growth.** If the value of every design `n` is at most
`∑ a, n a * w a`, then the growth of the designs proportional to `x` is at most
`∑ a, x a * w a`, with `0 * ∞ = 0`. -/
theorem designGrowth_le_sum_mul_of_forall_designValue_le {w : α → ℝ≥0∞}
    (h : ∀ n : α → ℕ, designValue μ Λ n ≤ ((∑ a, (n a : ℝ≥0∞) * w a : ℝ≥0∞) : EReal))
    (x : α → ℝ≥0) :
    designGrowth μ Λ x ≤ ((∑ a, (x a : ℝ≥0∞) * w a : ℝ≥0∞) : EReal) := by
  classical
  -- the bound `T ε = ∑ a ∈ supp x, (x a + 2 ε) * w a`, for the designs with `1 ≤ m ε`
  set T : ℝ≥0 → ℝ≥0∞ := fun ε ↦ ∑ a, if x a = 0 then 0 else ((x a + 2 * ε : ℝ≥0) : ℝ≥0∞) * w a
  have hT (ε : ℝ≥0) (hε : 0 < ε) : designGrowth μ Λ x ≤ (T ε : EReal) := by
    refine (iInf₂_le ε hε).trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    obtain ⟨M, hM⟩ := exists_nat_ge (ε⁻¹ : ℝ≥0)
    filter_upwards [eventually_ge_atTop (max M 1)] with m hm
    have hm0 : 0 < m := lt_of_lt_of_le one_pos (le_of_max_le_right hm)
    have hmε : 1 ≤ (m : ℝ≥0) * ε := by
      rw [← inv_le_iff_one_le_mul₀ hε]
      exact hM.trans (Nat.cast_le.2 (le_of_max_le_left hm))
    rw [EReal.div_natCast_le_iff hm0, ← ENNReal.toEReal_natCast, ← EReal.coe_ennreal_mul]
    refine (h _).trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases hx : x a = 0
    · simp [proportionalDesign_of_eq_zero hx]
    simp only [hx, ↓reduceIte]
    rw [← mul_assoc]
    gcongr
    -- the source `a` is observed at most `m (x a + ε) + 1 ≤ m (x a + 2 ε)` times
    have h_le : (proportionalDesign x ε m a : ℝ≥0) ≤ m * (x a + 2 * ε) :=
      (proportionalDesign_le x ε m a).trans (by linear_combination hmε)
    exact_mod_cast h_le
  -- the bounds `T ε` tend to `∑ a, x a * w a` as `ε → 0`
  have h_tendsto : Tendsto (fun ε ↦ (T ε : EReal)) (𝓝[>] 0)
      (𝓝 ((∑ a, (x a : ℝ≥0∞) * w a : ℝ≥0∞) : EReal)) := by
    refine (continuous_coe_ennreal_ereal.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun a _ ↦ ?_
    by_cases hx : x a = 0
    · simp [hx]
    simp only [hx, ↓reduceIte]
    refine ENNReal.Tendsto.mul_const ?_ (Or.inl (ENNReal.coe_ne_zero.2 hx))
    refine ENNReal.tendsto_coe.2 (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    simpa using tendsto_const_nhds.add ((continuous_const_mul 2).tendsto (0 : ℝ≥0))
  exact ge_of_tendsto h_tendsto (eventually_nhdsWithin_of_forall hT)

/-- The growth of the designs proportional to `x` is at most the rate of the designs times the
number `∑ a, x a` of observations per unit of `m`, `G x ≤ D* * ∑ a, x a`, with `⊤ * 0 = 0`
[EVR26, Note 41, Section 1]. -/
theorem designGrowth_le_designRate_mul (hΛ : Λ.Nonempty) (x : α → ℝ≥0) :
    designGrowth μ Λ x ≤ designRate μ Λ * ((∑ a, (x a : ℝ) : ℝ) : EReal) := by
  have hd := EReal.coe_toENNReal (designRate_nonneg μ Λ)
  -- the bound with constant weights `D*` is `D* * ∑ a, x a`, up to casts
  have h_eq : ((∑ a, (x a : ℝ≥0∞) * (designRate μ Λ).toENNReal : ℝ≥0∞) : EReal) =
      designRate μ Λ * ((∑ a, (x a : ℝ) : ℝ) : EReal) := by
    rw [← Finset.sum_mul, EReal.coe_ennreal_mul, hd, mul_comm]
    norm_cast
  refine (designGrowth_le_sum_mul_of_forall_designValue_le (fun n ↦ ?_) x).trans_eq h_eq
  rw [← Finset.sum_mul, EReal.coe_ennreal_mul, hd]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [designValue_zero μ hΛ]
  · exact_mod_cast designValue_le_mul_designRate μ Λ hn

/-- **The entropy bound.** The growth of the designs proportional to `x` is at most the infimum
over the instances `ν` of `Λ` of `∑ a, x a * klDiv (μ a) (ν a)` [EVR26, Note 41, Section 2]. -/
theorem designGrowth_le_iInf_sum_mul_klDiv [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (x : α → ℝ≥0) :
    designGrowth μ Λ x ≤
      ((⨅ ν ∈ Λ, ∑ a, (x a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  simp only [EReal.coe_ennreal_iInf]
  refine le_iInf₂ fun ν hν ↦ ?_
  have := hΛ ν hν
  exact designGrowth_le_sum_mul_of_forall_designValue_le
    (fun n ↦ designValue_le_sum_mul_klDiv hν n) x

/-- The growth of the designs is nonnegative against instances of measures of mass at most
`1`. -/
lemma designGrowth_nonneg (μ : α → Measure 𝓧) (hΛ : ∀ ν ∈ Λ, ∀ a, ν a Set.univ ≤ 1)
    (x : α → ℝ≥0) : 0 ≤ designGrowth μ Λ x :=
  le_iInf₂ fun _ _ ↦ le_liminf_of_le (by isBoundedDefault) (.of_forall fun _ ↦
    EReal.div_nonneg (designValue_nonneg μ hΛ _) (by positivity))

/-- The growth of the designs proportional to `0` is `0` when the set of instances is not
empty. -/
@[simp]
lemma designGrowth_zero (μ : α → Measure 𝓧) (hΛ : Λ.Nonempty) :
    designGrowth μ Λ (0 : α → ℝ≥0) = 0 := by
  have h (ε : ℝ≥0) : liminf (fun m : ℕ ↦
      designValue μ Λ (proportionalDesign (0 : α → ℝ≥0) ε m) / (m : EReal)) atTop = 0 := by
    simp [designValue_zero μ hΛ]
  simp only [designGrowth_def, h]
  exact le_antisymm (iInf₂_le 1 one_pos) (le_iInf₂ fun _ _ ↦ le_rfl)

/-- The growth of the designs proportional to `x` is monotone in `x`. -/
lemma designGrowth_mono [∀ a, IsProbabilityMeasure (μ a)]
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (h : x ≤ y) :
    designGrowth μ Λ x ≤ designGrowth μ Λ y :=
  iInf₂_mono fun _ _ ↦ liminf_le_liminf (.of_forall fun _ ↦ EReal.div_le_div_right_of_nonneg
    (by positivity) (designValue_mono hΛ (proportionalDesign_mono h)))

/-- The growth of the designs proportional to `x` is antitone in the set of instances. -/
@[gcongr]
lemma designGrowth_anti {Λ' : Set (α → Measure 𝓧)} (h : Λ ⊆ Λ') :
    designGrowth μ Λ' x ≤ designGrowth μ Λ x :=
  iInf₂_mono fun _ _ ↦ liminf_le_liminf (.of_forall fun _ ↦ EReal.div_le_div_right_of_nonneg
    (by positivity) (designValue_anti h))

/-- **One informative source.** If the instances of `Λ` give every source other than `a` the law
it has under `μ`, the growth of the designs proportional to `x` is at most `x a` times the bipolar
rate of the source `a` against its laws in `Λ`, with `0 * ⊤ = 0`: only the observations of the
source `a` count [EVR26, Note 41, Section 7]. -/
theorem designGrowth_le_mul_bipolarRate_of_forall_ne [∀ b, IsProbabilityMeasure (μ b)] {a : α}
    (hΛ : ∀ ν ∈ Λ, ν a Set.univ ≤ 1) (hne : Λ.Nonempty)
    (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = μ b) (x : α → ℝ≥0) :
    designGrowth μ Λ x ≤ ((x a : ℝ) : EReal) * bipolarRate (μ a) ((fun ν ↦ ν a) '' Λ) := by
  classical
  set d := bipolarRate (μ a) ((fun ν ↦ ν a) '' Λ)
  have hd : (d.toENNReal : EReal) = d :=
    EReal.coe_toENNReal (bipolarRate_nonneg (μ a) (Set.forall_mem_image.2 hΛ))
  -- the weights `d` at the source `a` and `0` elsewhere
  have h_sum (y : α → ℝ≥0∞) :
      ((∑ b, y b * (Pi.single a d.toENNReal : α → ℝ≥0∞) b : ℝ≥0∞) : EReal) =
        (y a : EReal) * d := by
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) fun b _ hb ↦ by simp [hb],
      Pi.single_eq_same, EReal.coe_ennreal_mul, hd]
  refine (designGrowth_le_sum_mul_of_forall_designValue_le
    (w := Pi.single a d.toENNReal) (fun n ↦ ?_) x).trans_eq ?_
  · rw [h_sum]
    simpa using designValue_le_mul_bipolarRate_of_forall_ne hΛ hne hΛa n
  · rw [h_sum]
    norm_cast

end ProbabilityTheory
