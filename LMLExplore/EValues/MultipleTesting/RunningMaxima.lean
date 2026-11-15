/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
import Mathlib.Algebra.Order.SuccPred.PartialSups

/-!
# E-BH on the running maxima of test supermartingales

Let `M i`, for `i` in a finite type `ι` of `K` hypotheses, be test supermartingales for one
filtration, and let every hypothesis be true under `P`. The e-BH procedure at level `α` [WR22]
applied to the running maxima `⨆ n, M i n` makes a rejection exactly when some nonempty set `R` of
hypotheses is self-consistent: `K ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`. Since every
hypothesis is true, the false discovery rate of the procedure is the probability of this event.
The running maxima are not e-variables, and the procedure does not control the false discovery
rate at level `α` [TGdH25]. This file and `LMLExplore.EValues.MultipleTesting.RunningMaxima.Three`
bound the inflation: the probability of a rejection is at most `4 * α / 3` for two hypotheses and
at most `3 * α / 2` for three.

## Main statements

* `ProbabilityTheory.measure_exists_selfConsistent_le_of_key`: the potential argument, which
  bounds the probability that e-BH on the running maxima rejects by the initial value of a
  potential built from affine forms satisfying the key inequality.
* `ProbabilityTheory.measure_exists_selfConsistent_iSup_le_of_card_eq_two`: for two hypotheses,
  e-BH on the running maxima rejects with probability at most `4 * α / 3`.

The bound `3 * α / 2` for three hypotheses,
`ProbabilityTheory.measure_exists_selfConsistent_iSup_le_of_card_eq_three`, is in
`LMLExplore.EValues.MultipleTesting.RunningMaxima.Three`.

## Implementation notes

Both bounds come from one potential argument. For a threshold `t < α⁻¹`, each process `M i / t`
carries a flag, the largest level that it has reached so far among finitely many levels (the
partial suprema of a level function). A rejection makes the flags reach a set of winning states at
a finite time; the strict inequality `t < α⁻¹` is needed because the suprema need not be attained.
The potential of a flag state is a minimum of affine forms with nonnegative coefficients in the
current values of the processes. It is a supermartingale as soon as the *key inequality* holds:
each affine form of a state dominates, at every point, the potential of the state reached by
moving to that point. The potential is at least `1` in the winning states, which bounds the
probability that the flags ever win by the initial expectation of the potential. No optional
stopping is needed. The key inequality is checked at real points, cell by cell, by `linarith`.

The rejection event is written out: compound e-values, self-consistent sets and the e-BH
procedure are the subject of Layer 8.2 of the roadmap.

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
* [TGdH25] Y. Tavyrikov, J. J. Goeman and R. de Heide, *Carefree multiple testing with
  e-processes*, arXiv:2501.19360.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {P : Measure Ω}

/-! ### A potential argument for running flags -/

section Potential

variable {ι J : Type*} [Fintype ι]

/-- The minimum over `j` of the affine forms `∑ i, a n j i * X i n + a₀ n j` of supermartingales
`X i`, with `ℱ n`-measurable coefficients, is a supermartingale as soon as each form of time `n`,
evaluated at time `n + 1`, dominates the minimum at time `n + 1`. -/
private lemma isENNSupermartingale_iInf_affine [Finite J] [Nonempty J]
    {X : ι → ℕ → Ω → ℝ≥0∞} (hX : ∀ i, IsENNSupermartingale (X i) ℱ {P})
    {a : ℕ → J → ι → Ω → ℝ≥0∞} {a₀ : ℕ → J → Ω → ℝ≥0∞}
    (ha : ∀ n j i, Measurable[ℱ n] (a n j i)) (ha₀ : ∀ n j, Measurable[ℱ n] (a₀ n j))
    (hY : ∀ n j ω, ⨅ j', (∑ i, a (n + 1) j' i ω * X i (n + 1) ω + a₀ (n + 1) j' ω) ≤
      ∑ i, a n j i ω * X i (n + 1) ω + a₀ n j ω) :
    IsENNSupermartingale (fun n ω ↦ ⨅ j, (∑ i, a n j i ω * X i n ω + a₀ n j ω)) ℱ {P} := by
  have := Fintype.ofFinite J
  set Y : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ⨅ j, (∑ i, a n j i ω * X i n ω + a₀ n j ω)
  have hℓ (n : ℕ) (j : J) : Measurable[ℱ n] fun ω ↦ ∑ i, a n j i ω * X i n ω + a₀ n j ω :=
    (Finset.measurable_sum _ fun i _ ↦ (ha n j i).mul ((hX i).adapted n)).add (ha₀ n j)
  have hYm (n : ℕ) : Measurable[ℱ n] (Y n) := Measurable.iInf (hℓ n)
  refine ⟨hYm, ?_⟩
  rintro P' rfl n s hs
  -- the form `j` attains the minimum at time `n` on `T j`
  set T : J → Set Ω := fun j ↦ {ω | Y n ω = ∑ i, a n j i ω * X i n ω + a₀ n j ω}
  have hT (j : J) : MeasurableSet[ℱ n] (T j) := measurableSet_eq_fun (hYm n) (hℓ n j)
  have hloc (j : J) (t : Set Ω) (ht : MeasurableSet[ℱ n] t) (htT : t ⊆ T j) :
      ∫⁻ ω in t, Y (n + 1) ω ∂P' ≤ ∫⁻ ω in t, Y n ω ∂P' := by
    have hint (m : ℕ) : ∫⁻ ω in t, (∑ i, a n j i ω * X i m ω + a₀ n j ω) ∂P' =
        ∑ i, ∫⁻ ω in t, a n j i ω * X i m ω ∂P' + ∫⁻ ω in t, a₀ n j ω ∂P' := by
      rw [lintegral_add_right _ ((ha₀ n j).mono (ℱ.le n) le_rfl), lintegral_finsetSum]
      exact fun i _ ↦ ((ha n j i).mono (ℱ.le n) le_rfl).mul ((hX i).measurable m)
    calc ∫⁻ ω in t, Y (n + 1) ω ∂P'
        ≤ ∫⁻ ω in t, (∑ i, a n j i ω * X i (n + 1) ω + a₀ n j ω) ∂P' :=
          lintegral_mono fun ω ↦ hY n j ω
      _ ≤ ∫⁻ ω in t, (∑ i, a n j i ω * X i n ω + a₀ n j ω) ∂P' := by
          rw [hint, hint]
          exact add_le_add (Finset.sum_le_sum fun i _ ↦
            (hX i).setLIntegral_mul_succ_le rfl (ha n j i) ht) le_rfl
      _ = ∫⁻ ω in t, Y n ω ∂P' :=
          setLIntegral_congr_fun (ℱ.le n t ht) fun ω hω ↦ (htT hω).symm
  -- glue the inequalities over the finitely many sets `T j`, which cover `Ω`
  have hglue (F : Finset J) : ∀ t, MeasurableSet[ℱ n] t → t ⊆ ⋃ j ∈ F, T j →
      ∫⁻ ω in t, Y (n + 1) ω ∂P' ≤ ∫⁻ ω in t, Y n ω ∂P' := by
    classical
    induction F using Finset.induction_on with
    | empty =>
      intro t _ htF
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
        Set.subset_empty_iff] at htF
      simp [htF]
    | insert j F _ ih =>
      intro t ht htF
      rw [← lintegral_inter_add_sdiff _ t (ℱ.le n _ (hT j)),
        ← lintegral_inter_add_sdiff (fun ω ↦ Y n ω) t (ℱ.le n _ (hT j))]
      refine add_le_add (hloc j _ (ht.inter (hT j)) Set.inter_subset_right)
        (ih _ (ht.diff (hT j)) fun ω hω ↦ ?_)
      have h := htF hω.1
      simp only [Finset.set_biUnion_insert, Set.mem_union] at h
      exact h.resolve_left hω.2
  refine hglue Finset.univ s hs fun ω _ ↦ ?_
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j ↦ ∑ i, a n j i ω * X i n ω + a₀ n j ω)
  exact Set.mem_biUnion (Finset.mem_univ j) (show ω ∈ T j by simp [T, Y, hj])

omit [Fintype ι] in
/-- The running flags `partialSups (fun k i ↦ lev (X i k ω)) n` of adapted processes, the largest
levels reached up to time `n`, are adapted. -/
private lemma measurable_partialSups_lev {X : ι → ℕ → Ω → ℝ≥0∞} {lev : ℝ≥0∞ → ℕ}
    (hlev : Measurable lev) (hX : ∀ i, Adapted ℱ (X i)) (n : ℕ) :
    Measurable[ℱ n] fun ω ↦ partialSups (fun k i ↦ lev (X i k ω)) n := by
  induction n with
  | zero =>
    simp only [partialSups_zero]
    exact @Measurable.of_eval Ω ι (fun _ ↦ ℕ) (ℱ 0) _ _ fun i ↦ hlev.comp (hX i 0)
  | succ n ih =>
    simp only [partialSups_add_one]
    exact @Measurable.of_eval Ω ι (fun _ ↦ ℕ) (ℱ (n + 1)) _ _ fun i ↦ ((measurable_pi_apply i).comp
      (ih.mono (ℱ.mono n.le_succ) le_rfl)).sup (hlev.comp (hX i (n + 1)))

/-- **Potential bound for running flags.** Let `X i` be `ℝ≥0∞`-valued supermartingales with
running flags for a measurable level function `lev`, and let the potential in the flag state `b`
be the minimum over `j` of the affine forms `∑ i, A b j i * z i + A₀ b j`. Suppose the key
inequality: every affine form of a state `b` dominates at every point `z` the potential of the
state `b ⊔ lev z` reached from `b` by moving to `z`. Suppose also that every form is at least `1`
on an upper set `W` of winning states. Then the probability that the flags ever win is at most
the expectation of any form of the state `0`, evaluated at time `0`. -/
private lemma measure_exists_partialSups_mem_le [Finite J] [Nonempty J]
    {X : ι → ℕ → Ω → ℝ≥0∞} (hX : ∀ i, IsENNSupermartingale (X i) ℱ {P})
    {lev : ℝ≥0∞ → ℕ} (hlev : Measurable lev) (A : (ι → ℕ) → J → ι → ℝ≥0∞)
    (A₀ : (ι → ℕ) → J → ℝ≥0∞)
    (hkey : ∀ b j (z : ι → ℝ≥0∞), ⨅ j', (∑ i, A (b ⊔ fun i ↦ lev (z i)) j' i * z i +
      A₀ (b ⊔ fun i ↦ lev (z i)) j') ≤ ∑ i, A b j i * z i + A₀ b j)
    {W : Set (ι → ℕ)} (hW : IsUpperSet W)
    (hW1 : ∀ b ∈ W, ∀ j (z : ι → ℝ≥0∞), 1 ≤ ∑ i, A b j i * z i + A₀ b j) (j : J) :
    P {ω | ∃ n, partialSups (fun k i ↦ lev (X i k ω)) n ∈ W} ≤
      ∫⁻ ω, (∑ i, A 0 j i * X i 0 ω + A₀ 0 j) ∂P := by
  set F : ℕ → Ω → ι → ℕ := fun n ω ↦ partialSups (fun k i ↦ lev (X i k ω)) n
  have hF (n : ℕ) : Measurable[ℱ n] (F n) :=
    measurable_partialSups_lev hlev (fun i ↦ (hX i).adapted) n
  have hY := isENNSupermartingale_iInf_affine hX (a := fun n j i ω ↦ A (F n ω) j i)
    (a₀ := fun n j ω ↦ A₀ (F n ω) j)
    (fun n j i ↦ (measurable_of_countable fun b ↦ A b j i).comp (hF n))
    (fun n j ↦ (measurable_of_countable fun b ↦ A₀ b j).comp (hF n))
    fun n j ω ↦ by simpa only [F, partialSups_add_one] using hkey (F n ω) j fun i ↦ X i (n + 1) ω
  have hmono : Monotone fun n ↦ {ω | F n ω ∈ W} := fun m n hmn ω hω ↦
    hW ((partialSups fun k i ↦ lev (X i k ω)).monotone hmn) hω
  have h0 (ω : Ω) : F 0 ω = (0 : ι → ℕ) ⊔ fun i ↦ lev (X i 0 ω) := by ext i; simp [F]
  calc P {ω | ∃ n, F n ω ∈ W} = ⨆ n, P {ω | F n ω ∈ W} := by
        rw [← hmono.measure_iUnion]
        congr 1
        ext
        simp
    _ ≤ ∫⁻ ω, ⨅ j, (∑ i, A (F 0 ω) j i * X i 0 ω + A₀ (F 0 ω) j) ∂P := iSup_le fun n ↦ calc
        P {ω | F n ω ∈ W} ≤ P {ω | 1 ≤ ⨅ j, (∑ i, A (F n ω) j i * X i n ω + A₀ (F n ω) j)} :=
          measure_mono fun ω hω ↦ le_iInf fun j ↦ hW1 _ hω j _
        _ ≤ ∫⁻ ω, ⨅ j, (∑ i, A (F n ω) j i * X i n ω + A₀ (F n ω) j) ∂P := by
          simpa using mul_meas_ge_le_lintegral₀ (hY.measurable n).aemeasurable 1
        _ ≤ _ := hY.lintegral_le rfl n.zero_le
    _ ≤ ∫⁻ ω, (∑ i, A 0 j i * X i 0 ω + A₀ 0 j) ∂P := lintegral_mono fun ω ↦ by
        simpa only [h0] using hkey 0 j fun i ↦ X i 0 ω

/-- An affine form with nonnegative real coefficients commutes with `ENNReal.ofReal`. -/
private lemma sum_ofReal_mul_ofReal_add_ofReal {c : ι → ℝ} {c₀ : ℝ} {r : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hc₀ : 0 ≤ c₀) (hr : ∀ i, 0 ≤ r i) :
    ∑ i, ENNReal.ofReal (c i) * ENNReal.ofReal (r i) + ENNReal.ofReal c₀ =
      ENNReal.ofReal (∑ i, c i * r i + c₀) := by
  have h : ∀ i ∈ Finset.univ, 0 ≤ c i * r i := fun i _ ↦ mul_nonneg (hc i) (hr i)
  rw [ENNReal.ofReal_add (Finset.sum_nonneg h) hc₀, ENNReal.ofReal_sum_of_nonneg h]
  simp_rw [ENNReal.ofReal_mul (hc _)]

/-- **The key inequality from its real form.** For affine forms with nonnegative real
coefficients, each of which is either at least `1` or has positive coefficients, and with a
constant form `1` in every state, the key inequality of `measure_exists_partialSups_mem_le` holds
in `ℝ≥0∞` as soon as it holds at the points with real coordinates. -/
private lemma key_of_real {lev : ℝ≥0∞ → ℕ}
    {C : (ι → ℕ) → J → ι → ℝ} {C₀ : (ι → ℕ) → J → ℝ} (hC : ∀ b j i, 0 ≤ C b j i)
    (hC₀ : ∀ b j, 0 ≤ C₀ b j) (hpos : ∀ b j, 1 ≤ C₀ b j ∨ ∀ i, 0 < C b j i) {j₀ : J}
    (hj₀ : ∀ b, (∀ i, C b j₀ i = 0) ∧ C₀ b j₀ = 1)
    (hreal : ∀ b j (r : ι → ℝ), (∀ i, 0 ≤ r i) → ∃ j',
      ∑ i, C (b ⊔ fun i ↦ lev (ENNReal.ofReal (r i))) j' i * r i +
        C₀ (b ⊔ fun i ↦ lev (ENNReal.ofReal (r i))) j' ≤ ∑ i, C b j i * r i + C₀ b j)
    (b : ι → ℕ) (j : J) (z : ι → ℝ≥0∞) :
    ⨅ j', (∑ i, ENNReal.ofReal (C (b ⊔ fun i ↦ lev (z i)) j' i) * z i +
      ENNReal.ofReal (C₀ (b ⊔ fun i ↦ lev (z i)) j')) ≤
      ∑ i, ENNReal.ofReal (C b j i) * z i + ENNReal.ofReal (C₀ b j) := by
  by_cases hz : ∃ i, z i = ⊤
  · obtain ⟨i, hi⟩ := hz
    refine (iInf_le _ j₀).trans ?_
    simp only [(hj₀ _).1, (hj₀ _).2, ENNReal.ofReal_zero, zero_mul, Finset.sum_const_zero,
      zero_add, ENNReal.ofReal_one]
    rcases hpos b j with h | h
    · exact (ENNReal.one_le_ofReal.2 h).trans le_add_self
    · calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C b j i) * z i := by
            rw [hi, ENNReal.mul_top (ENNReal.ofReal_pos.2 (h i)).ne']
            exact le_top
        _ ≤ ∑ i, ENNReal.ofReal (C b j i) * z i :=
            Finset.single_le_sum (f := fun i ↦ ENNReal.ofReal (C b j i) * z i)
              (fun _ _ ↦ zero_le) (Finset.mem_univ i)
        _ ≤ _ := le_self_add
  · simp only [not_exists] at hz
    obtain ⟨r, hr, rfl⟩ : ∃ r : ι → ℝ, (∀ i, 0 ≤ r i) ∧ z = fun i ↦ ENNReal.ofReal (r i) :=
      ⟨fun i ↦ (z i).toReal, fun i ↦ ENNReal.toReal_nonneg,
        funext fun i ↦ (ENNReal.ofReal_toReal (hz i)).symm⟩
    obtain ⟨j', hj'⟩ := hreal b j r hr
    refine (iInf_le _ j').trans ?_
    rw [sum_ofReal_mul_ofReal_add_ofReal (hC _ _) (hC₀ _ _) hr,
      sum_ofReal_mul_ofReal_add_ofReal (hC _ _) (hC₀ _ _) hr]
    exact ENNReal.ofReal_le_ofReal hj'

/-- If some nonempty set `R` is self-consistent at level `α` for the running maxima of the
processes `M i`, then for every `t ∈ (0, α⁻¹)` the running flags of the processes `t⁻¹ * M i`
reach every upper set `W` that contains, for each nonempty `s`, the flag state equal to
`K + 1 - #s` on `s` and to `0` elsewhere. Here the level function `lev` satisfies
`K + 1 - k ≤ lev x` whenever `K / k < x`. -/
private lemma exists_partialSups_mem_of_selfConsistent [DecidableEq ι]
    {M : ι → ℕ → Ω → ℝ≥0∞} {α t : ℝ≥0∞} (ht0 : t ≠ 0) (ht : t < α⁻¹) {lev : ℝ≥0∞ → ℕ}
    (hlev : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι → ∀ x, (Fintype.card ι : ℝ≥0∞) / k < x →
      Fintype.card ι + 1 - k ≤ lev x)
    {W : Set (ι → ℕ)} (hW : IsUpperSet W)
    (hWs : ∀ s : Finset ι, s.Nonempty →
      (fun i ↦ if i ∈ s then Fintype.card ι + 1 - s.card else 0) ∈ W)
    {ω : Ω} {R : Finset ι} (hR : R.Nonempty)
    (hRe : ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω) :
    ∃ n, partialSups (fun k i ↦ lev (t⁻¹ * M i k ω)) n ∈ W := by
  have hk1 : 1 ≤ R.card := hR.card_pos
  have hkK : R.card ≤ Fintype.card ι := R.card_le_univ
  have htop : t ≠ ⊤ := (ht.trans_le le_top).ne
  have hK0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hk0 : (R.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq0 : (Fintype.card ι : ℝ≥0∞) / R.card ≠ 0 :=
    (ENNReal.div_pos hK0 (ENNReal.natCast_ne_top _)).ne'
  have hqtop : (Fintype.card ι : ℝ≥0∞) / R.card ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hk0
  -- every member of `R` reaches the level `K + 1 - #R`
  have hreach : ∀ i ∈ R, ∃ n, Fintype.card ι + 1 - R.card ≤ lev (t⁻¹ * M i n ω) := by
    intro i hi
    have hle : (Fintype.card ι : ℝ≥0∞) / (R.card * α) ≤ ⨆ n, M i n ω :=
      ENNReal.div_le_of_le_mul ((hRe i hi).trans_eq (by ring))
    have heq : (Fintype.card ι : ℝ≥0∞) / (R.card * α) = α⁻¹ * (Fintype.card ι / R.card) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hk0)
        (Or.inl (ENNReal.natCast_ne_top _))]
      ring
    have hlt : t * (Fintype.card ι / R.card) < ⨆ n, M i n ω :=
      (ENNReal.mul_lt_mul_left hq0 hqtop ht).trans_le (heq ▸ hle)
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
    refine ⟨n, hlev _ hk1 hkK _ ?_⟩
    rw [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl ht0) (Or.inl htop), mul_comm]
    exact hn
  have hev : ∀ i, ∀ᶠ N in atTop, (if i ∈ R then Fintype.card ι + 1 - R.card else 0) ≤
      partialSups (fun k i ↦ lev (t⁻¹ * M i k ω)) N i := by
    intro i
    by_cases hi : i ∈ R
    · obtain ⟨n, hn⟩ := hreach i hi
      exact eventually_atTop.2 ⟨n, fun N hN ↦ by
        simpa [hi] using hn.trans (le_partialSups_of_le (fun k i ↦ lev (t⁻¹ * M i k ω)) hN i)⟩
    · exact Eventually.of_forall fun N ↦ by simp [hi]
  obtain ⟨N, hN⟩ := (eventually_all.2 hev).exists
  exact ⟨N, hW (fun i ↦ hN i) (hWs R hR)⟩

/-- **E-BH on running maxima, from a potential.** Let `M i` be test supermartingales, `lev` a
measurable level function adapted to the e-BH thresholds, and real affine forms `C b j`,
`C₀ b j` satisfying the key inequality at real points (`hreal`), at least `1` in winning states,
with a constant form `1` in every state. If the form `j` of the initial state has no constant
term and coefficients of sum at most `q`, then e-BH at level `α` on the running maxima rejects
with probability at most `q * α`. -/
theorem measure_exists_selfConsistent_le_of_key [DecidableEq ι] [Finite J] [Nonempty J]
    {M : ι → ℕ → Ω → ℝ≥0∞} (hM : ∀ i, IsTestSupermartingale (M i) ℱ {P}) {lev : ℝ≥0∞ → ℕ}
    (hlev_meas : Measurable lev)
    (hlev : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι → ∀ x, (Fintype.card ι : ℝ≥0∞) / k < x →
      Fintype.card ι + 1 - k ≤ lev x)
    {C : (ι → ℕ) → J → ι → ℝ} {C₀ : (ι → ℕ) → J → ℝ} (hC : ∀ b j i, 0 ≤ C b j i)
    (hC₀ : ∀ b j, 0 ≤ C₀ b j) (hpos : ∀ b j, 1 ≤ C₀ b j ∨ ∀ i, 0 < C b j i) {j₀ : J}
    (hj₀ : ∀ b, (∀ i, C b j₀ i = 0) ∧ C₀ b j₀ = 1)
    (hreal : ∀ b j (r : ι → ℝ), (∀ i, 0 ≤ r i) → ∃ j',
      ∑ i, C (b ⊔ fun i ↦ lev (ENNReal.ofReal (r i))) j' i * r i +
        C₀ (b ⊔ fun i ↦ lev (ENNReal.ofReal (r i))) j' ≤ ∑ i, C b j i * r i + C₀ b j)
    {W : Set (ι → ℕ)} (hW : IsUpperSet W)
    (hWs : ∀ s : Finset ι, s.Nonempty →
      (fun i ↦ if i ∈ s then Fintype.card ι + 1 - s.card else 0) ∈ W)
    (hW1 : ∀ b ∈ W, ∀ j, 1 ≤ C₀ b j) (j : J) (hfresh : C₀ 0 j = 0) {q : ℝ} (hq0 : 0 < q)
    (hq : ∑ i, C 0 j i ≤ q) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset ι, R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤ ENNReal.ofReal q * α := by
  -- at level `0` nothing is rejected
  rcases eq_or_ne α 0 with rfl | hα
  · suffices h : {ω | ∃ R : Finset ι, R.Nonempty ∧
        ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ 0 * R.card * ⨆ n, M i n ω} = ∅ by
      rw [h, measure_empty]
      exact zero_le
    refine Set.eq_empty_of_forall_notMem fun ω ⟨R, ⟨i, hi⟩, hR⟩ ↦ ?_
    have h := hR i hi
    simp only [zero_mul, nonpos_iff_eq_zero, Nat.cast_eq_zero, Fintype.card_eq_zero_iff] at h
    exact h.false i
  rcases eq_or_ne α ⊤ with rfl | hαtop
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hq0).ne']
    exact le_top
  -- the bound `q / t` for every `t ∈ (0, α⁻¹)`
  have ht (t : ℝ≥0∞) (ht0 : t ≠ 0) (ht : t < α⁻¹) :
      P {ω | ∃ R : Finset ι, R.Nonempty ∧
        ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤
        ENNReal.ofReal q * t⁻¹ := by
    have hX (i : ι) : IsENNSupermartingale (fun n ω ↦ t⁻¹ * M i n ω) ℱ {P} :=
      ⟨fun n ↦ ((hM i).adapted n).const_mul _, fun P' hP' n s hs ↦
        (hM i).toIsENNSupermartingale.setLIntegral_mul_succ_le hP' measurable_const hs⟩
    calc P {ω | ∃ R : Finset ι, R.Nonempty ∧
          ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω}
      _ ≤ P {ω | ∃ n, partialSups (fun k i ↦ lev (t⁻¹ * M i k ω)) n ∈ W} :=
          measure_mono fun ω ⟨R, hR, hRe⟩ ↦
            exists_partialSups_mem_of_selfConsistent ht0 ht hlev hW hWs hR hRe
      _ ≤ ∫⁻ ω, (∑ i, ENNReal.ofReal (C 0 j i) * (t⁻¹ * M i 0 ω) +
            ENNReal.ofReal (C₀ 0 j)) ∂P :=
          measure_exists_partialSups_mem_le hX hlev_meas (fun b j i ↦ ENNReal.ofReal (C b j i))
            (fun b j ↦ ENNReal.ofReal (C₀ b j)) (key_of_real hC hC₀ hpos hj₀ hreal) hW
            (fun b hb j _ ↦ (ENNReal.one_le_ofReal.2 (hW1 b hb j)).trans le_add_self) j
      _ = ∑ i, ENNReal.ofReal (C 0 j i) * t⁻¹ * ∫⁻ ω, M i 0 ω ∂P := by
          rw [hfresh, ENNReal.ofReal_zero]
          simp_rw [add_zero]
          rw [lintegral_finsetSum _ fun i _ ↦ ((hM i).measurable 0).const_mul _ |>.const_mul _]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [lintegral_const_mul _ (((hM i).measurable 0).const_mul _),
            lintegral_const_mul _ ((hM i).measurable 0), mul_assoc]
      _ ≤ ∑ i, ENNReal.ofReal (C 0 j i) * t⁻¹ := Finset.sum_le_sum fun i _ ↦ by
          simpa using mul_le_mul_right ((hM i).lintegral_zero_le P rfl)
            (ENNReal.ofReal (C 0 j i) * t⁻¹)
      _ = ENNReal.ofReal (∑ i, C 0 j i) * t⁻¹ := by
          rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hC 0 j i]
      _ ≤ ENNReal.ofReal q * t⁻¹ := by gcongr
  -- let `t` increase to `α⁻¹`
  have hprod : P {ω | ∃ R : Finset ι, R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} * α⁻¹ ≤
      ENNReal.ofReal q := by
    rw [mul_comm]
    refine ENNReal.mul_le_of_forall_lt fun a ha b hb ↦ ?_
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    calc a * b ≤ a * (ENNReal.ofReal q * a⁻¹) := mul_le_mul_right (hb.le.trans (ht a ha0 ha)) a
      _ = ENNReal.ofReal q := by
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel ha0 (ha.trans_le le_top).ne, mul_one]
  calc _ ≤ ENNReal.ofReal q / α⁻¹ :=
        (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.inv_ne_zero.2 hαtop))
          (Or.inl (ENNReal.inv_ne_top.2 hα))).2 hprod
    _ = ENNReal.ofReal q * α := by rw [div_eq_mul_inv, inv_inv]

/-- The rejection event of e-BH on running maxima does not depend on the indexing of the
hypotheses. -/
theorem measure_exists_selfConsistent_le_of_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (M : ι → ℕ → Ω → ℝ≥0∞) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset ι, R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤
    P {ω | ∃ R : Finset κ, R.Nonempty ∧
      ∀ k ∈ R, (Fintype.card κ : ℝ≥0∞) ≤ α * R.card * ⨆ n, M (e.symm k) n ω} := by
  refine measure_mono fun ω ⟨R, hR, hRe⟩ ↦ ⟨R.map e.toEmbedding, hR.map, fun k hk ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hk
  simpa [Fintype.card_congr e] using hRe i hi

end Potential

/-! ### Two hypotheses -/

section Two

/-- The level of a value for two hypotheses, in units of the threshold: `2` from `2` on, `1` on
`[1, 2)` and `0` below `1`. -/
private noncomputable def lev2 (x : ℝ≥0∞) : ℕ := if 2 ≤ x then 2 else if 1 ≤ x then 1 else 0

/-- The level function for two hypotheses is monotone. -/
private lemma monotone_lev2 : Monotone lev2 := by
  intro x y hxy
  unfold lev2
  by_cases hx2 : 2 ≤ x
  · simp [hx2, hx2.trans hxy]
  by_cases hx1 : 1 ≤ x
  · simp only [hx2, hx1, hx1.trans hxy, ite_false, ite_true]
    split_ifs <;> omega
  · simp [hx2, hx1]

/-- The level of a real value for two hypotheses. -/
private lemma lev2_ofReal_cases {x : ℝ} (hx : 0 ≤ x) :
    (lev2 (ENNReal.ofReal x) = 0 ∧ x < 1) ∨ (lev2 (ENNReal.ofReal x) = 1 ∧ 1 ≤ x ∧ x < 2) ∨
      (lev2 (ENNReal.ofReal x) = 2 ∧ 2 ≤ x) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal x ↔ 1 ≤ x := ENNReal.one_le_ofReal
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal x ↔ 2 ≤ x := by
    rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_le_ofReal_iff hx]
  by_cases a : 2 ≤ x
  · exact Or.inr (Or.inr ⟨by simp [lev2, h2.2 a], a⟩)
  by_cases c : 1 ≤ x
  · exact Or.inr (Or.inl ⟨by simp [lev2, mt h2.1 a, h1.2 c], c, not_le.1 a⟩)
  · exact Or.inl ⟨by simp [lev2, mt h2.1 a, mt h1.1 c], not_le.1 c⟩

/-- The flags of two hypotheses win: one flag is `2`, or both are at least `1`. -/
private def Wins2 (b : Fin 2 → ℕ) : Prop := 2 ≤ b 0 ∨ 2 ≤ b 1 ∨ (1 ≤ b 0 ∧ 1 ≤ b 1)

/-- Winning for two hypotheses is decidable. -/
private instance : DecidablePred Wins2 := fun b ↦ by unfold Wins2; infer_instance

/-- The coefficients of the two affine forms of the potential for two hypotheses: the form `0`
is the constant `1`, the form `1` is `2 (x + y) / 3` for fresh flags, `x / 2 + y` once the first
process has reached `1`, and `x + y / 2` once the second has. -/
private noncomputable def coef2 (b : Fin 2 → ℕ) (j : Fin 2) : Fin 2 → ℝ :=
  if j = 0 ∨ Wins2 b then 0 else
    if 1 ≤ b 0 then ![1 / 2, 1] else if 1 ≤ b 1 then ![1, 1 / 2] else ![2 / 3, 2 / 3]

/-- The constant terms of the affine forms of the potential for two hypotheses. -/
private noncomputable def const2 (b : Fin 2 → ℕ) (j : Fin 2) : ℝ :=
  if j = 0 ∨ Wins2 b then 1 else 0

/-- **Key inequality for two hypotheses**, at real points. -/
private lemma key2_real (b : Fin 2 → ℕ) (j : Fin 2) (r : Fin 2 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ∑ i, coef2 (b ⊔ fun i ↦ lev2 (ENNReal.ofReal (r i))) j' i * r i +
      const2 (b ⊔ fun i ↦ lev2 (ENNReal.ofReal (r i))) j' ≤
        ∑ i, coef2 b j i * r i + const2 b j := by
  by_cases hj : j = 0 ∨ Wins2 b
  · exact ⟨0, by simp [coef2, const2, hj]⟩
  have hj1 : j = 1 := by
    rcases not_or.1 hj with ⟨h, -⟩
    fin_cases j
    · exact absurd rfl h
    · rfl
  subst hj1
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have hr0 := hr 0
  have hr1 := hr 1
  simp only [Wins2, not_or, not_and_or, not_le] at hj
  obtain ⟨-, hb0, hb1, hb⟩ := hj
  have hb0' : b 0 = 0 ∨ b 0 = 1 := by omega
  have hb1' : b 1 = 0 ∨ b 1 = 1 := by omega
  rcases lev2_ofReal_cases (hr 0) with ⟨hl0, hx0⟩ | ⟨hl0, hx0, hx0'⟩ | ⟨hl0, hx0⟩ <;>
  rcases lev2_ofReal_cases (hr 1) with ⟨hl1, hx1⟩ | ⟨hl1, hx1, hx1'⟩ | ⟨hl1, hx1⟩ <;>
  rcases hb0' with hb0' | hb0' <;> rcases hb1' with hb1' | hb1' <;>
  simp only [coef2, Fin.isValue, one_ne_zero, Wins2, hb0', nonpos_iff_eq_zero, OfNat.ofNat_ne_zero,
    hb1', and_self, or_self, ↓reduceIte, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, const2, add_zero, Pi.sup_apply, hl0, max_self,
    hl1, or_false, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, lt_self_iff_false,
    Nat.not_ofNat_le_one, Std.le_refl, and_true, one_div, one_mul, zero_le, sup_of_le_left,
    and_false, or_true, sup_of_le_right, Order.lt_one_iff, Nat.one_le_ofNat] at h0 h1 hb <;>
  linarith

/-- The level function for two hypotheses reaches `3 - k` above the e-BH threshold `2 / k`. -/
private lemma le_lev2 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ Fintype.card (Fin 2)) (x : ℝ≥0∞)
    (hx : (Fintype.card (Fin 2) : ℝ≥0∞) / k < x) : Fintype.card (Fin 2) + 1 - k ≤ lev2 x := by
  simp only [Fintype.card_fin] at hk2 hx ⊢
  interval_cases k
  · have : 2 ≤ x := by simpa using hx.le
    simp [lev2, this]
  · have : 1 ≤ x := by
      simpa [ENNReal.div_self (two_ne_zero) ENNReal.ofNat_ne_top] using hx.le
    unfold lev2
    split_ifs <;> omega

/-- The winning flags for two hypotheses form an upper set. -/
private lemma isUpperSet_wins2 : IsUpperSet {b | Wins2 b} := by
  intro a b hab ha
  have h0 : a 0 ≤ b 0 := hab 0
  have h1 : a 1 ≤ b 1 := hab 1
  simp only [Set.mem_ofPred_eq, Wins2] at ha ⊢
  omega

/-- The bound `4 * α / 3` for two test supermartingales indexed by `Fin 2`. -/
private lemma measure_exists_selfConsistent_iSup_fin_two_le {M : Fin 2 → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ {P}) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset (Fin 2), R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card (Fin 2) : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤ 4 * α / 3 := by
  have h := measure_exists_selfConsistent_le_of_key hM monotone_lev2.measurable le_lev2
    (C := coef2) (C₀ := const2)
    (fun b j i ↦ by unfold coef2; split_ifs <;> fin_cases i <;> norm_num)
    (fun b j ↦ by unfold const2; split_ifs <;> norm_num)
    (fun b j ↦ by
      unfold coef2 const2
      split_ifs <;> first | (left; norm_num; done) | (right; intro i; fin_cases i <;> norm_num))
    (j₀ := 0) (fun b ↦ by simp [coef2, const2]) key2_real isUpperSet_wins2
    (by simp only [Fintype.card_fin]; decide)
    (fun b hb j ↦ by simp [const2, show Wins2 b from hb]) 1 (by simp [const2, Wins2])
    (q := 4 / 3) (by norm_num) (by norm_num [coef2, Wins2, Fin.sum_univ_two]) α
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at h
  simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm] using h

end Two

/-! ### The bounds -/

/-- **E-BH on the running maxima of two test supermartingales.** Let `M i` be test
supermartingales for one filtration and nulls `H i`, for two hypotheses, both true under `P`.
E-BH at level `α` applied to the running maxima `⨆ n, M i n` makes a rejection, that is, some
nonempty set `R` of hypotheses has `2 ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`, with
probability at most `4 * α / 3`. The measure `P` need not be a probability measure. -/
theorem measure_exists_selfConsistent_iSup_le_of_card_eq_two {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 2) {H : ι → Set (Measure Ω)} {M : ι → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ (H i)) (hP : ∀ i, P ∈ H i) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset ι, R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤ 4 * α / 3 :=
  (measure_exists_selfConsistent_le_of_equiv (Fintype.equivFinOfCardEq hι) M α).trans
    (measure_exists_selfConsistent_iSup_fin_two_le
      (fun _ ↦ (hM _).anti_set (Set.singleton_subset_iff.2 (hP _))) α)

end ProbabilityTheory
