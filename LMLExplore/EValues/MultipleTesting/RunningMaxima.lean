/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Basic.ENNReal.BigOperators
public import LMLExplore.EValues.MultipleTesting.EBH
public import LMLExplore.Probability.Martingale.TestSupermartingale

/-!
# E-BH on the running maxima of test supermartingales

Let `M i`, for `i` in a finite type `ι` of `K` hypotheses, be test supermartingales for one
filtration, and let every hypothesis be true under `P`. The e-BH procedure at level `α` [WR22]
applied to the running maxima `⨆ n, M i n` makes a rejection,
`(eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty`, exactly when some nonempty set `R` of hypotheses is
self-consistent: `K ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`
(`ProbabilityTheory.eBH_nonempty_iff`). Since every hypothesis is true, the false discovery rate
of the procedure is the probability of this event.
The running maxima are not e-variables, and the procedure does not control the false discovery
rate at level `α` [TGdH25]. This file and `LMLExplore.EValues.MultipleTesting.RunningMaxima.Three`
bound the inflation: the probability of a rejection is at most `4 * α / 3` for two hypotheses and
at most `3 * α / 2` for three [EVR26, Notes 10 and 18].

## Main statements

* `ProbabilityTheory.measure_eBH_nonempty_le_of_key`: the potential argument, which bounds the
  probability that e-BH on the running maxima rejects by the initial value of a potential built
  from affine forms satisfying the key inequality.
* `ProbabilityTheory.measure_eBH_iSup_nonempty_le_of_card_eq_two`: for two hypotheses, e-BH on
  the running maxima rejects with probability at most `4 * α / 3` [EVR26, Note 10, Theorem].

The bound `3 * α / 2` for three hypotheses,
`ProbabilityTheory.measure_eBH_iSup_nonempty_le_of_card_eq_three`, is in
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

The potential argument uses the rejection event only through `ProbabilityTheory.eBH_nonempty_iff`:
some nonempty set `R` is self-consistent, `K ≤ α * #R * E i` for every `i ∈ R` with
`E i = ⨆ n, M i n ω`.

The potential argument, the bound for two hypotheses and the bound for three in
`LMLExplore.EValues.MultipleTesting.RunningMaxima.Three` are adapted from
`EValuesResearch/Results/RunningMaxima.lean` and `EValuesResearch/Results/RunningMaximaAux.lean`
(commit `ffba78a`) in the paper project `RemyDegenne/evalues_research`, which formalizes the
notes [EVR26, Notes 10 and 18].

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
* [TGdH25] Y. Tavyrikov, J. J. Goeman and R. de Heide, *Carefree multiple testing with
  e-processes*, arXiv:2501.19360.
* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 10,
  `results/10-running-maxima-ebh.md`, and Note 18, `results/18-running-maxima-general-k.md`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {P : Measure Ω}

/-! ### A potential argument for running flags -/

section Potential

variable {ι J : Type*} [Fintype ι]

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
  -- the measurable space on `Ω` is `ℱ n`, not the ambient `mΩ`, hence the explicit instance
  have hF (n : ℕ) : Measurable[ℱ n] (F n) :=
    (@measurable_pi_iff Ω ι (fun _ ↦ ℕ) (ℱ n) _ _).2 fun i ↦ by
      convert Adapted.partialSups (fun k ↦ hlev.comp ((hX i).adapted k)) n using 1
      funext ω
      simp only [F, Pi.partialSups_apply, Function.comp_apply]
  have hY := IsENNSupermartingale.iInf_affine hX (a := fun n j i ω ↦ A (F n ω) j i)
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
    rw [← ENNReal.ofReal_sum_mul_add (fun i _ ↦ hC _ _ i) (fun i _ ↦ hr i) (hC₀ _ _),
      ← ENNReal.ofReal_sum_mul_add (fun i _ ↦ hC _ _ i) (fun i _ ↦ hr i) (hC₀ _ _)]
    exact ENNReal.ofReal_le_ofReal hj'

/-- If a nonempty set `R` is self-consistent at level `α` for the running maxima of the
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
    (hRe : IsSelfConsistent (fun i ↦ ⨆ n, M i n ω) α R) :
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
      ENNReal.div_le_of_le_mul ((isSelfConsistent_iff.1 hRe i hi).trans_eq (by ring))
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

/-- **E-BH on running maxima, from a potential.** Let `M i` be test supermartingales and `lev` a
measurable level function adapted to the e-BH thresholds: `K + 1 - k ≤ lev x` whenever
`K / k < x`. Let `C b j`, `C₀ b j` be real affine forms with nonnegative coefficients, each of
which either has constant term at least `1` or has positive coefficients, with a constant form `1`
in every state, and satisfying the key inequality at real points (`hreal`). Let `W` be an upper
set of winning states that contains every e-BH rejection pattern (the state equal to `K + 1 - #s`
on a nonempty `s` and to `0` elsewhere) and on which every form has constant term at least `1`.
If the form `j` of the initial state has no constant term and coefficients of sum at most `q`,
for some `q > 0`, then e-BH at level `α` on the running maxima rejects with probability at most
`ENNReal.ofReal q * α`. -/
theorem measure_eBH_nonempty_le_of_key [DecidableEq ι] [Finite J] [Nonempty J]
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
    P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ ENNReal.ofReal q * α := by
  -- at level `0` nothing is rejected
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  rcases eq_or_ne α ⊤ with rfl | hαtop
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hq0).ne']
    exact le_top
  -- the bound `q / t` for every `t ∈ (0, α⁻¹)`
  have ht (t : ℝ≥0∞) (ht0 : t ≠ 0) (ht : t < α⁻¹) :
      P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ ENNReal.ofReal q * t⁻¹ := by
    have hX (i : ι) : IsENNSupermartingale (fun n ω ↦ t⁻¹ * M i n ω) ℱ {P} :=
      ⟨fun n ↦ ((hM i).adapted n).const_mul _, fun P' hP' n s hs ↦
        (hM i).toIsENNSupermartingale.setLIntegral_mul_succ_le hP' measurable_const hs⟩
    calc P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty}
      _ ≤ P {ω | ∃ n, partialSups (fun k i ↦ lev (t⁻¹ * M i k ω)) n ∈ W} :=
          measure_mono fun ω hω ↦
            have ⟨_, hR, hRe⟩ := eBH_nonempty_iff.1 hω
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
  have hprod : P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} * α⁻¹ ≤ ENNReal.ofReal q := by
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
  simp [coef2, const2, Wins2, hb0', hb1', hl0, hl1, Fin.sum_univ_two] at h0 h1 <;>
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
private lemma measure_eBH_iSup_nonempty_le_fin_two {M : Fin 2 → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ {P}) (α : ℝ≥0∞) :
    P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ 4 * α / 3 := by
  have h := measure_eBH_nonempty_le_of_key hM monotone_lev2.measurable le_lev2
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
E-BH at level `α` applied to the running maxima `⨆ n, M i n` makes a rejection with probability
at most `4 * α / 3` [EVR26, Note 10, Theorem]. The measure `P` need not be a probability
measure. -/
theorem measure_eBH_iSup_nonempty_le_of_card_eq_two {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 2) {H : ι → Set (Measure Ω)} {M : ι → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ (H i)) (hP : ∀ i, P ∈ H i) (α : ℝ≥0∞) :
    P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ 4 * α / 3 := by
  -- relabel the hypotheses by `Fin 2`
  let σ := (Fintype.equivFinOfCardEq hι).symm
  have h := measure_eBH_iSup_nonempty_le_fin_two (M := fun k ↦ M (σ k))
    (fun _ ↦ (hM _).anti_set (Set.singleton_subset_iff.2 (hP _))) α
  have hset : {ω | (eBH (fun k ↦ ⨆ n, M (σ k) n ω) α).Nonempty} =
      {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} :=
    Set.ext fun ω ↦ eBH_comp_equiv_nonempty (e := fun i ↦ ⨆ n, M i n ω) σ
  rwa [hset] at h

end ProbabilityTheory
