/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale

/-!
# E-BH on the running maxima of test martingales: a lower bound for every number of hypotheses

The e-BH procedure at level `α` [WR22] applied to the running maxima `⨆ n, M i n` of `K` test
supermartingales for one filtration makes a rejection exactly when some nonempty set `R` of
hypotheses is self-consistent: `K ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`. For every `K` and
every `α ≤ (K + 1) / (2 * K)`, this file constructs `K` test martingales for one filtration for
which the procedure rejects with probability exactly `2 * K * α / (K + 1)`, with every hypothesis
true. For two and three hypotheses this is `4 * α / 3` and `3 * α / 2`, so the bounds of
`LMLExplore.EValues.MultipleTesting.RunningMaxima` are attained. The procedure does not control
the false discovery rate at level `α` [TGdH25], and its inflation is at least `2 * K / (K + 1)`.

## Main statements

* `ProbabilityTheory.exists_isTestMartingale_measure_exists_selfConsistent_iSup_eq`: `K` test
  martingales for one filtration for which e-BH on the running maxima rejects with probability
  `2 * K * α / (K + 1)`.

## Implementation notes

The construction lives on a finite space: a coin that is `true` with probability
`p = 2 * K * α / (K + 1)`, a uniform cyclic shift of the positions of the processes and uniform
heights `H l ∈ {0, …, K - 1}` of the players at the positions `l`. The player at position `l`
climbs during the times `K * l, …, K * l + K - 1`, which reveal its height. Each process is the
Doob martingale of its terminal value `K / α`, earned when the coin is `true`, nobody before its
position has won and its height is the top one. At height `h` it is then worth `K / ((K - h) α)`,
so e-BH rejects exactly when the coin is `true`. The initial expectations are at most `1` by the
bound `(K - j) / K` on the probability that nobody among the first `j` players wins, which a
cycle lemma gives: among the `K` cyclic shifts of any heights, at most `K - j` leave no win among
the first `j` players.

The Doob martingales are fiber averages on a finite space, for the filtration pulled back from
the information revealed up to each time.

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
* [TGdH25] Y. Tavyrikov, J. J. Goeman and R. de Heide, *Carefree multiple testing with
  e-processes*, arXiv:2501.19360.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Doob martingales on a finite space -/

section FiniteDoob

variable {Ω β : Type*} [Fintype Ω] [DecidableEq β]

/-- The `w`-weighted average of `Z` over the fiber `f ⁻¹' {y}` of a finite space; it is `0` on
a fiber of weight `0`. -/
private noncomputable def fiberAvg (w : Ω → ℝ≥0∞) (f : Ω → β) (Z : Ω → ℝ≥0∞) (y : β) : ℝ≥0∞ :=
  (∑ ω, if f ω = y then w ω * Z ω else 0) / ∑ ω, if f ω = y then w ω else 0

/-- On a union of fibers of `f`, the weighted sums of `Z` and of its fiber averages agree. -/
private lemma sum_mul_fiberAvg {w : Ω → ℝ≥0∞} (hw : ∀ ω, w ω ≠ ⊤) (f : Ω → β) (Z : Ω → ℝ≥0∞)
    (s : Set Ω) [DecidablePred (· ∈ s)] (hs : ∀ ω ω', f ω = f ω' → (ω ∈ s ↔ ω' ∈ s)) :
    ∑ ω, (if ω ∈ s then w ω * fiberAvg w f Z (f ω) else 0) =
      ∑ ω, if ω ∈ s then w ω * Z ω else 0 := by
  set W : β → ℝ≥0∞ := fun y ↦ ∑ ω, if f ω = y then w ω else 0 with hW_def
  have hW (ω : Ω) : w ω ≤ W (f ω) := by
    have := Finset.single_le_sum (s := Finset.univ)
      (f := fun ω' ↦ (if f ω' = f ω then w ω' else 0 : ℝ≥0∞)) (fun _ _ ↦ zero_le)
      (Finset.mem_univ ω)
    simpa using this
  have hWtop (y : β) : W y ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun ω _ ↦ by split_ifs <;> simp [hw]
  calc ∑ ω, (if ω ∈ s then w ω * fiberAvg w f Z (f ω) else 0)
      = ∑ ω, ∑ ω', if ω ∈ s ∧ f ω' = f ω then w ω * (w ω' * Z ω') * (W (f ω'))⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        by_cases h : ω ∈ s
        · simp only [h, ite_true, true_and, fiberAvg, div_eq_mul_inv, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω' _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [h', W, mul_assoc]
          · simp [h']
        · simp [h]
    _ = ∑ ω', ∑ ω, if ω ∈ s ∧ f ω' = f ω then w ω * (w ω' * Z ω') * (W (f ω'))⁻¹ else 0 :=
        Finset.sum_comm
    _ = ∑ ω', if ω' ∈ s then w ω' * Z ω' * (W (f ω') * (W (f ω'))⁻¹) else 0 := by
        refine Finset.sum_congr rfl fun ω' _ ↦ ?_
        by_cases h : ω' ∈ s
        · simp only [h, ite_true]
          rw [hW_def]
          simp only [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [(hs ω ω' h'.symm).2 h, h', mul_left_comm, mul_assoc]
          · simp [h', Ne.symm h']
        · simp only [h, ite_false]
          refine Finset.sum_eq_zero fun ω _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [show ω ∉ s from fun hω ↦ h ((hs ω ω' h'.symm).1 hω)]
          · simp [h']
    _ = ∑ ω', if ω' ∈ s then w ω' * Z ω' else 0 := by
        refine Finset.sum_congr rfl fun ω' _ ↦ ?_
        split_ifs
        · rcases eq_or_ne (W (f ω')) 0 with h0 | h0
          · have : w ω' = 0 := le_antisymm ((hW ω').trans h0.le) zero_le
            simp [this]
          · rw [ENNReal.mul_inv_cancel h0 (hWtop _), mul_one]
        · rfl

omit [Fintype Ω] [DecidableEq β] in
/-- The sets that are measurable for the σ-algebra `MeasurableSpace.comap f ⊤` are the unions of
fibers of `f`. -/
private lemma measurableSet_comap_top_iff {f : Ω → β} {s : Set Ω} :
    MeasurableSet[MeasurableSpace.comap f ⊤] s ↔ ∀ ω ω', f ω = f ω' → (ω ∈ s ↔ ω' ∈ s) := by
  refine ⟨fun ⟨u, _, hu⟩ ω ω' h ↦ by simp [← hu, h], fun h ↦ ⟨f '' s, trivial, ?_⟩⟩
  ext ω
  exact ⟨fun ⟨ω', hω', he⟩ ↦ (h ω' ω he).1 hω', fun hω ↦ ⟨ω, hω, rfl⟩⟩

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The filtration of the information `info t`, for maps `info t` of a finite space that refine
as `t` increases: at time `t`, the σ-algebra `MeasurableSpace.comap (info t) ⊤`. -/
private def fiberFiltration (info : ℕ → Ω → β)
    (hinfo : ∀ t ω ω', info (t + 1) ω = info (t + 1) ω' → info t ω = info t ω') :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq t := MeasurableSpace.comap (info t) ⊤
  mono' := monotone_nat_of_le_succ fun t _ hs ↦ measurableSet_comap_top_iff.2 fun ω ω' h ↦
    measurableSet_comap_top_iff.1 hs ω ω' (hinfo t ω ω' h)
  le' _ s _ := s.toFinite.measurableSet

/-- The lower Lebesgue integral for a finite weighted sum of Dirac masses. -/
private lemma setLIntegral_sum_smul_dirac (w : Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (s : Set Ω)
    [DecidablePred (· ∈ s)] :
    ∫⁻ ω in s, g ω ∂(∑ ω, w ω • Measure.dirac ω) = ∑ ω, if ω ∈ s then w ω * g ω else 0 := by
  rw [← lintegral_indicator s.toFinite.measurableSet, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  by_cases h : ω ∈ s <;> simp [h]

/-- **Doob martingales on a finite space.** The fiber averages of `Z` given refining
maps `info t` form a test martingale for the weighted sum of Dirac masses, as soon as the
weighted sum of `Z` is at most `1`. -/
private lemma isTestMartingale_fiberAvg {w : Ω → ℝ≥0∞} (hw : ∀ ω, w ω ≠ ⊤) (info : ℕ → Ω → β)
    (hinfo : ∀ t ω ω', info (t + 1) ω = info (t + 1) ω' → info t ω = info t ω')
    (Z : Ω → ℝ≥0∞) (hZ : ∑ ω, w ω * Z ω ≤ 1) :
    IsTestMartingale (fun t ω ↦ fiberAvg w (info t) Z (info t ω)) (fiberFiltration info hinfo)
      {∑ ω, w ω • Measure.dirac ω} := by
  classical
  have key (t : ℕ) (s : Set Ω) (hs : ∀ ω ω', info t ω = info t ω' → (ω ∈ s ↔ ω' ∈ s)) :
      ∫⁻ ω in s, fiberAvg w (info t) Z (info t ω) ∂(∑ ω, w ω • Measure.dirac ω) =
        ∫⁻ ω in s, Z ω ∂(∑ ω, w ω • Measure.dirac ω) := by
    rw [setLIntegral_sum_smul_dirac, setLIntegral_sum_smul_dirac]
    exact sum_mul_fiberAvg hw (info t) Z s hs
  refine ⟨fun t U _ ↦ measurableSet_comap_top_iff.2 fun ω ω' h ↦ by simp [h], fun P hP ↦ ?_,
    fun P hP t s hs ↦ ?_⟩
  · rw [Set.mem_singleton_iff] at hP
    subst hP
    rw [← setLIntegral_univ, key 0 Set.univ (by simp), setLIntegral_univ,
      ← setLIntegral_univ, setLIntegral_sum_smul_dirac]
    simpa using hZ
  · rw [Set.mem_singleton_iff] at hP
    subst hP
    have hs' := measurableSet_comap_top_iff.1 hs
    rw [key t s hs', key (t + 1) s fun ω ω' h ↦ hs' ω ω' (hinfo t ω ω' h)]

end FiniteDoob

/-! ### The ladder -/

section Ladder

variable {n : ℕ}

/-- No win among the first `j` positions for the heights `H`: for every `m ≤ n`, fewer than
`n + 1 - m` of the heights `H l`, `l < j`, are at least `m`. With the ranks `n + 1 - H l`, this
says that for no `r` are `r` of the first `j` ranks at most `r`. -/
private def NoWin (H : Fin (n + 1) → Fin (n + 1)) (j : ℕ) : Prop :=
  ∀ m < n + 1, (Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ m ≤ (H l : ℕ)).card <
    n + 1 - m

/-- `NoWin H j` is decidable. -/
private instance (H : Fin (n + 1) → Fin (n + 1)) (j : ℕ) : Decidable (NoWin H j) := by
  unfold NoWin; infer_instance

/-- `NoWin H j` only depends on the heights at the positions `l < j`. -/
private lemma noWin_congr {H H' : Fin (n + 1) → Fin (n + 1)} {j : ℕ}
    (h : ∀ l : Fin (n + 1), (l : ℕ) < j → H' l = H l) : NoWin H' j ↔ NoWin H j := by
  have : ∀ m : ℕ, (Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ m ≤ (H' l : ℕ)) =
      Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ m ≤ (H l : ℕ) := fun m ↦
    Finset.filter_congr fun l _ ↦ by
      constructor <;> rintro ⟨hl, hm⟩ <;> exact ⟨hl, by simpa [h l hl] using hm⟩
  simp only [NoWin, this]

/-- All `n + 1` heights always win. -/
private lemma not_noWin_succ (H : Fin (n + 1) → Fin (n + 1)) : ¬ NoWin H (n + 1) := by
  intro h
  have := h 0 (Nat.succ_pos n)
  rw [Finset.filter_true_of_mem fun l _ ↦ ⟨l.is_lt, Nat.zero_le _⟩] at this
  simp at this

/-- The sample space of the ladder: a coin, a shift of the positions and the heights reached by
the players at the `n + 1` positions. -/
private abbrev LadderΩ (n : ℕ) := Bool × Fin (n + 1) × (Fin (n + 1) → Fin (n + 1))

/-- The information of the ladder at time `t`: the coin, the shift, and, for the position `l`,
the height `H l` capped at `t - (n + 1) l`: the player at position `l` climbs during the times
`(n + 1) l, …, (n + 1) l + n`. -/
private def ladderInfo (n t : ℕ) (ω : LadderΩ n) : Bool × Fin (n + 1) × (Fin (n + 1) → ℕ) :=
  (ω.1, ω.2.1, fun l ↦ min (ω.2.2 l : ℕ) (t - (n + 1) * l))

/-- The information of the ladder increases with time. -/
private lemma ladderInfo_refine (t : ℕ) (ω ω' : LadderΩ n)
    (h : ladderInfo n (t + 1) ω = ladderInfo n (t + 1) ω') :
    ladderInfo n t ω = ladderInfo n t ω' := by
  simp only [ladderInfo, Prod.mk.injEq, funext_iff] at h ⊢
  refine ⟨h.1, h.2.1, fun l ↦ ?_⟩
  have := h.2.2 l
  generalize (n + 1) * (l : ℕ) = a at this ⊢
  omega

/-- The weights of the ladder: the coin is `true` with probability `p`, the shift and the
heights are uniform. -/
private noncomputable def ladderWeight (n : ℕ) (p : ℝ≥0∞) (ω : LadderΩ n) : ℝ≥0∞ :=
  (if ω.1 then p else 1 - p) / (n + 1 : ℝ≥0∞) ^ (n + 2)

/-- The terminal value `a` of the process `i` of the ladder: the coin is `true`, nobody before
its position `i + s` has won, and it climbs to the top height `n`. -/
private noncomputable def ladderValue (n : ℕ) (a : ℝ≥0∞) (i : Fin (n + 1)) (ω : LadderΩ n) : ℝ≥0∞ :=
  if ω.1 = true ∧ NoWin ω.2.2 (i + ω.2.1 : Fin (n + 1)) ∧ ω.2.2 (i + ω.2.1) = Fin.last n then a
  else 0

/-- The process `i` of the ladder at time `t`: the conditional expectation of its terminal
value given the information at time `t`. -/
private noncomputable def ladder (n : ℕ) (p a : ℝ≥0∞) (i : Fin (n + 1)) (t : ℕ) (ω : LadderΩ n) :
    ℝ≥0∞ :=
  fiberAvg (ladderWeight n p) (ladderInfo n t) (ladderValue n a i) (ladderInfo n t ω)

/-- The weights of the ladder are finite. -/
private lemma ladderWeight_ne_top {p : ℝ≥0∞} (hp : p ≠ ⊤) (ω : LadderΩ n) :
    ladderWeight n p ω ≠ ⊤ := by
  unfold ladderWeight
  refine ENNReal.div_ne_top ?_ (pow_ne_zero _ (by simp))
  split_ifs
  exacts [hp, ENNReal.sub_ne_top ENNReal.one_ne_top]

/-- The ladder vanishes when the coin is `false`. -/
private lemma ladder_of_false {p a : ℝ≥0∞} (i : Fin (n + 1)) (t : ℕ) {ω : LadderΩ n}
    (hω : ω.1 = false) : ladder n p a i t ω = 0 := by
  unfold ladder fiberAvg
  refine ENNReal.div_eq_zero_iff.2 (Or.inl (Finset.sum_eq_zero fun ω' _ ↦ ?_))
  split_ifs with h
  · have : ω'.1 = false := by
      have := congrArg Prod.fst h
      simpa [ladderInfo, hω] using this
    simp [ladderValue, this]
  · rfl

/-- A sum over the sample space of the ladder. -/
private lemma sum_ladderΩ (f : LadderΩ n → ℝ≥0∞) : ∑ ω, f ω = ∑ b, ∑ s, ∑ H, f (b, s, H) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]

/-- The number of height vectors satisfying a coordinatewise condition. -/
private lemma card_filter_forall (Q : Fin (n + 1) → Fin (n + 1) → Prop) [∀ l, DecidablePred (Q l)]
    [DecidablePred fun H : Fin (n + 1) → Fin (n + 1) ↦ ∀ l, Q l (H l)] :
    (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ ∀ l, Q l (H l)).card =
      ∏ l, (Finset.univ.filter (Q l)).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext H
  simp [Fintype.mem_piFinset]

/-- The fiber of the information of the ladder at the time `(n + 1) l + H l` at which the player
at position `l` reaches its height `H l`. -/
private lemma ladderInfo_climb_iff (ω ω' : LadderΩ n) (l : Fin (n + 1)) :
    ladderInfo n ((n + 1) * l + ω.2.2 l) ω' = ladderInfo n ((n + 1) * l + ω.2.2 l) ω ↔
      ω'.1 = ω.1 ∧ ω'.2.1 = ω.2.1 ∧ ∀ l' : Fin (n + 1),
        ((l' : ℕ) < l → ω'.2.2 l' = ω.2.2 l') ∧ (l' = l → ω.2.2 l ≤ ω'.2.2 l') := by
  simp only [ladderInfo, Prod.mk.injEq, funext_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun l' ↦ ?_))
  have h1 := (ω.2.2 l').is_lt
  have h2 := (ω'.2.2 l').is_lt
  have h3 := (ω.2.2 l).is_lt
  rw [Fin.ext_iff, Fin.ext_iff, Fin.le_def]
  rcases lt_trichotomy (l' : ℕ) l with hlt | heq | hgt
  · have : (n + 1) * l' + (n + 1) ≤ (n + 1) * l := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    generalize (n + 1) * (l' : ℕ) = A at *
    generalize (n + 1) * (l : ℕ) = B at *
    omega
  · obtain rfl : l' = l := Fin.ext heq
    generalize (n + 1) * (l' : ℕ) = B at *
    omega
  · have : (n + 1) * l + (n + 1) ≤ (n + 1) * l' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hgt
    generalize (n + 1) * (l' : ℕ) = A at *
    generalize (n + 1) * (l : ℕ) = B at *
    omega

/-- **The climbing player.** When the coin is `true` and nobody before the position `l` of the
process `i` has won, the process is worth `a / (n + 1 - H l)` at the time `(n + 1) l + H l` at
which it reaches its height `H l`. -/
private lemma ladder_climb {p a : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (i : Fin (n + 1)) {ω : LadderΩ n}
    (hω : ω.1 = true) (hwin : NoWin ω.2.2 (i + ω.2.1 : Fin (n + 1))) :
    ladder n p a i ((n + 1) * (i + ω.2.1 : Fin (n + 1)) + ω.2.2 (i + ω.2.1)) ω =
      a / ((n + 1 - ω.2.2 (i + ω.2.1) : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, s, H⟩ := ω
  simp only at hω hwin ⊢
  subst hω
  set l : Fin (n + 1) := i + s
  set Q : Fin (n + 1) → Fin (n + 1) → Prop :=
    fun l' v ↦ ((l' : ℕ) < l → v = H l') ∧ (l' = l → H l ≤ v) with hQ
  set c : ℝ≥0∞ := p / (n + 1 : ℝ≥0∞) ^ (n + 2)
  have hc0 : c ≠ 0 := (ENNReal.div_pos hp0 (by simp)).ne'
  have hctop : c ≠ ⊤ := ENNReal.div_ne_top hp (pow_ne_zero _ (by simp))
  -- the weight and the weighted terminal value of the fiber
  have hfib (ω' : LadderΩ n) :
      ladderInfo n ((n + 1) * l + H l) ω' = ladderInfo n ((n + 1) * l + H l) (true, s, H) ↔
        ω'.1 = true ∧ ω'.2.1 = s ∧ ∀ l', Q l' (ω'.2.2 l') :=
    ladderInfo_climb_iff (true, s, H) ω' l
  have hW : (∑ ω' : LadderΩ n, if ladderInfo n ((n + 1) * l + H l) ω' =
      ladderInfo n ((n + 1) * l + H l) (true, s, H) then ladderWeight n p ω' else 0) =
      c * ∏ l', ((Finset.univ.filter (Q l')).card : ℝ≥0∞) := by
    simp_rw [hfib, sum_ladderΩ]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, Finset.sum_const_zero, add_zero,
      ite_and]
    rw [Fintype.sum_eq_single s fun x hx ↦ by simp [hx]]
    simp only [ite_true]
    rw [← Finset.sum_filter]
    simp only [ladderWeight, ite_true, Finset.sum_const, nsmul_eq_mul]
    rw [card_filter_forall, Nat.cast_prod, mul_comm]
  have hN : (∑ ω' : LadderΩ n, if ladderInfo n ((n + 1) * l + H l) ω' =
      ladderInfo n ((n + 1) * l + H l) (true, s, H) then
        ladderWeight n p ω' * ladderValue n a i ω' else 0) =
      c * a * ∏ l', ((Finset.univ.filter fun v ↦ Q l' v ∧ (l' = l → v = Fin.last n)).card :
        ℝ≥0∞) := by
    simp_rw [hfib, sum_ladderΩ]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, Finset.sum_const_zero, add_zero,
      ite_and]
    rw [Fintype.sum_eq_single s fun x hx ↦ by simp [hx]]
    simp only [ite_true]
    have hpt (H' : Fin (n + 1) → Fin (n + 1)) :
        (if ∀ l', Q l' (H' l') then ladderWeight n p (true, s, H') *
          ladderValue n a i (true, s, H') else 0) =
        if ∀ l', Q l' (H' l') ∧ (l' = l → H' l' = Fin.last n) then c * a else 0 := by
      by_cases hR : ∀ l', Q l' (H' l')
      · have hnw : NoWin H' l := (noWin_congr fun l' hl' ↦ (hR l').1 hl').2 hwin
        have hiff : (∀ l', Q l' (H' l') ∧ (l' = l → H' l' = Fin.last n)) ↔ H' l = Fin.last n :=
          ⟨fun h ↦ (h l).2 rfl, fun h l' ↦ ⟨hR l', fun hl ↦ hl ▸ h⟩⟩
        have hl_def : i + s = l := rfl
        rw [ite_eq_left hR, if_congr hiff rfl rfl]
        simp only [ladderWeight, ladderValue, ite_true, true_and, hl_def, hnw]
        by_cases hl : H' l = Fin.last n
        · simp [hl, c]
        · simp [hl]
      · have : ¬ ∀ l', Q l' (H' l') ∧ (l' = l → H' l' = Fin.last n) :=
          fun h ↦ hR fun l' ↦ (h l').1
        simp [hR, this]
    simp_rw [hpt]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_forall fun l' v ↦ Q l' v ∧ (l' = l → v = Fin.last n), Nat.cast_prod, mul_comm]
  -- the cards at the position `l` and elsewhere
  have hQl : (Finset.univ.filter (Q l)).card = n + 1 - H l := by
    rw [← Fin.card_Ici]
    congr 1
    ext v
    simp [Q]
  have hQ'l : (Finset.univ.filter fun v ↦ Q l v ∧ (l = l → v = Fin.last n)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨Fin.last n, ?_⟩
    ext v
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl, IsEmpty.forall_iff,
      forall_const, Finset.mem_singleton]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ Fin.le_last _, h⟩⟩
  have hrest : ∀ l' ∈ Finset.univ.erase l,
      (Finset.univ.filter fun v ↦ Q l' v ∧ (l' = l → v = Fin.last n)).card =
        (Finset.univ.filter (Q l')).card := fun l' hl' ↦ by
    have : l' ≠ l := by simpa using hl'
    congr 1
    exact Finset.filter_congr fun v _ ↦ by simp [this]
  set R : ℕ := ∏ l' ∈ Finset.univ.erase l, (Finset.univ.filter (Q l')).card
  have hR0 : (R : ℝ≥0∞) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun l' hl' ↦ ?_)
    have : l' ≠ l := by simpa using hl'
    exact Finset.card_ne_zero.2 ⟨H l', by simp [Q, this]⟩
  unfold ladder fiberAvg
  rw [hN, hW, ← Nat.cast_prod, ← Nat.cast_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l), Finset.prod_congr rfl hrest, hQl,
    hQ'l, one_mul, Nat.cast_mul]
  rw [show c * a * (R : ℝ≥0∞) = (c * R) * a by ring,
    show c * (((n + 1 - H l : ℕ) : ℝ≥0∞) * R) = (c * R) * ((n + 1 - H l : ℕ) : ℝ≥0∞) by ring]
  exact ENNReal.mul_div_mul_left _ _ (mul_ne_zero hc0 hR0)
    (ENNReal.mul_ne_top hctop (ENNReal.natCast_ne_top _))

/-- The weights of the ladder sum to `1`. -/
private lemma sum_ladderWeight {p : ℝ≥0∞} (hp : p ≤ 1) : ∑ ω, ladderWeight n p ω = 1 := by
  have hK0 : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ 0 := pow_ne_zero _ (by simp)
  have hKtop : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [sum_ladderΩ]
  simp only [ladderWeight, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, ← mul_assoc, ← pow_succ', show n + 1 + 1 = n + 2 from rfl,
    ENNReal.mul_div_cancel hK0 hKtop, ENNReal.mul_div_cancel hK0 hKtop, add_tsub_cancel_of_le hp]

/-- The coin of the ladder is `true` with probability `p`. -/
private lemma sum_ladderWeight_true (p : ℝ≥0∞) :
    ∑ ω : LadderΩ n, (if ω.1 = true then ladderWeight n p ω else 0) = p := by
  have hK0 : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ 0 := pow_ne_zero _ (by simp)
  have hKtop : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [sum_ladderΩ]
  simp only [ladderWeight, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_pi, Finset.prod_const, nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, ← pow_succ', show n + 1 + 1 = n + 2 from rfl,
    ENNReal.mul_div_cancel hK0 hKtop]

/-- The weighted sum of the terminal value of a process of the ladder. -/
private lemma sum_ladderWeight_mul_ladderValue (p a : ℝ≥0∞) (i : Fin (n + 1)) :
    ∑ ω, ladderWeight n p ω * ladderValue n a i ω =
      p / (n + 1 : ℝ≥0∞) ^ (n + 2) * a * ∑ j : Fin (n + 1),
        ((Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
          NoWin H j ∧ H j = Fin.last n).card : ℝ≥0∞) := by
  rw [sum_ladderΩ]
  simp only [ladderValue, Fintype.sum_bool, Bool.false_eq_true, false_and, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero, true_and, ladderWeight, ite_true, mul_ite]
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.addLeft i) _ _ fun s ↦ ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

/-- E-BH rejects on the running maxima of the ladder exactly when the coin is `true`. -/
private lemma exists_selfConsistent_ladder_iff {α p : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ⊤)
    (hp0 : p ≠ 0) (hp : p ≠ ⊤) (ω : LadderΩ n) :
    (∃ R : Finset (Fin (n + 1)), R.Nonempty ∧ ∀ i ∈ R,
      ((n + 1 : ℕ) : ℝ≥0∞) ≤ α * R.card * ⨆ t, ladder n p ((n + 1 : ℕ) / α) i t ω) ↔
      ω.1 = true := by
  constructor
  · rintro ⟨S, ⟨i, hi⟩, hSe⟩
    by_contra hb
    have := hSe i hi
    simp [ladder_of_false i _ (by simpa using hb)] at this
  · intro hb
    obtain ⟨b, s, H⟩ := ω
    simp only at hb
    subst hb
    have hex : ∃ j, ¬ NoWin H j := ⟨n + 1, not_noWin_succ H⟩
    obtain ⟨J, hJ, hlt⟩ : ∃ J, ¬ NoWin H J ∧ ∀ l < J, NoWin H l :=
      ⟨Nat.find hex, Nat.find_spec hex, fun l hl ↦ not_not.1 (Nat.find_min hex hl)⟩
    simp only [NoWin, not_forall, not_lt] at hJ
    obtain ⟨m, hm, hcard⟩ := hJ
    set S := Finset.univ.filter fun i : Fin (n + 1) ↦
      ((i + s : Fin (n + 1)) : ℕ) < J ∧ m ≤ (H (i + s) : ℕ)
    have hS : S.card = (Finset.univ.filter fun l : Fin (n + 1) ↦
        (l : ℕ) < J ∧ m ≤ (H l : ℕ)).card :=
      Finset.card_equiv (Equiv.addRight s) fun i ↦ by simp [S]
    refine ⟨S, ?_, fun i hi ↦ ?_⟩
    · rw [← Finset.card_pos, hS]
      omega
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hclimb := ladder_climb (a := ((n + 1 : ℕ) : ℝ≥0∞) / α) hp0 hp i (ω := (true, s, H))
        rfl (hlt _ hi.1)
      set x : ℕ := n + 1 - H (i + s)
      have hx0 : (x : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by have := (H (i + s)).is_lt; omega)
      have hxS : x ≤ S.card := by rw [hS]; omega
      calc ((n + 1 : ℕ) : ℝ≥0∞)
          = ((n + 1 : ℕ) : ℝ≥0∞) * (α * α⁻¹) * (x * (x : ℝ≥0∞)⁻¹) := by
            rw [ENNReal.mul_inv_cancel hα0 hαtop,
              ENNReal.mul_inv_cancel hx0 (ENNReal.natCast_ne_top _), mul_one, mul_one]
        _ = α * x * (((n + 1 : ℕ) : ℝ≥0∞) / α / x) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
        _ ≤ α * S.card * ⨆ t, ladder n p ((n + 1 : ℕ) / α) i t (true, s, H) :=
            mul_le_mul' (mul_le_mul_right (Nat.cast_le.2 hxS) α) (le_iSup_of_le _ hclimb.ge)

/-! ### The uniformity bound -/

/-- The number of the first `j` players at the height `v`. -/
private def heightCount (H : Fin (n + 1) → Fin (n + 1)) (j v : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ (H l : ℕ) = v).card

/-- The walk that counts, along `0, 1, …, z - 1` read modulo `n + 1`, one per spot minus the
number of the first `j` players at that height. -/
private def freeWalk (H : Fin (n + 1) → Fin (n + 1)) (j z : ℕ) : ℤ :=
  ∑ x ∈ Finset.range z, (1 - (heightCount H j (x % (n + 1)) : ℤ))

/-- Each of the first `j` players has exactly one height. -/
private lemma sum_heightCount (H : Fin (n + 1) → Fin (n + 1)) {j : ℕ} (hj : j ≤ n + 1) :
    ∑ x ∈ Finset.range (n + 1), heightCount H j x = j := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j) (t := Finset.range (n + 1))
    (f := fun l ↦ (H l : ℕ)) fun l _ ↦ Finset.mem_range.2 (H l).is_lt
  simp only [Finset.filter_filter, Fin.card_filter_val_lt, min_eq_right hj] at h
  exact h.symm

/-- A sum over a full period of residues does not depend on the starting point. -/
private lemma sum_range_add_mod (f : ℕ → ℤ) (z : ℕ) :
    ∑ x ∈ Finset.range (n + 1), f ((z + x) % (n + 1)) = ∑ x ∈ Finset.range (n + 1), f x := by
  induction z with
  | zero =>
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [zero_add, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
  | succ z ih =>
    have h1 := Finset.sum_range_succ' (fun x ↦ f ((z + x) % (n + 1))) (n + 1)
    rw [Finset.sum_range_succ, add_zero, Nat.add_mod_right] at h1
    rw [← ih]
    simp only [add_assoc, add_comm 1] at h1 ⊢
    linarith

/-- The walk increases by `n + 1 - j` over a period. -/
private lemma freeWalk_add (H : Fin (n + 1) → Fin (n + 1)) {j : ℕ} (hj : j ≤ n + 1) (z : ℕ) :
    freeWalk H j (z + (n + 1)) = freeWalk H j z + ((n : ℤ) + 1 - j) := by
  unfold freeWalk
  rw [Finset.sum_range_add, sum_range_add_mod (fun x ↦ 1 - (heightCount H j x : ℤ)) z]
  congr 1
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_heightCount H hj]
  simp

/-- Shifting heights modulo `n + 1`. -/
private lemma add_mod_eq_iff {K h u x : ℕ} (hh : h < K) (hu : u < K) (hx : x < K) :
    (h + u) % K = x ↔ h = (x + K - u) % K := by
  have e1 : (h + u) % K = if h + u < K then h + u else h + u - K := by
    split_ifs with h'
    · exact Nat.mod_eq_of_lt h'
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have e2 : (x + K - u) % K = if x < u then x + K - u else x - u := by
    split_ifs with h'
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  rw [e1, e2]
  split_ifs <;> omega

/-- The number of the first `j` players at heights at least `m` after a shift by `u`, from the
walk. -/
private lemma card_shift_eq (H : Fin (n + 1) → Fin (n + 1)) (j : ℕ) {u m : ℕ} (hu : u < n + 1)
    (hm : m < n + 1) :
    ((Finset.univ.filter fun l : Fin (n + 1) ↦
        (l : ℕ) < j ∧ m ≤ ((H l : ℕ) + u) % (n + 1)).card : ℤ) =
      ((n + 1 - m : ℕ) : ℤ) - (freeWalk H j (2 * (n + 1) - u) - freeWalk H j (n + 1 + m - u)) := by
  -- the count as a sum over the shifted heights `x ∈ [m, n]`
  have h1 := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ m ≤ ((H l : ℕ) + u) % (n + 1))
    (t := Finset.Ico m (n + 1)) (f := fun l ↦ ((H l : ℕ) + u) % (n + 1))
    fun l hl ↦ by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl
      exact Finset.mem_Ico.2 ⟨hl.2, Nat.mod_lt _ (Nat.succ_pos n)⟩
  have h2 : ∀ x ∈ Finset.Ico m (n + 1),
      (Finset.filter (fun l ↦ ((H l : ℕ) + u) % (n + 1) = x) (Finset.univ.filter
        fun l : Fin (n + 1) ↦ (l : ℕ) < j ∧ m ≤ ((H l : ℕ) + u) % (n + 1))).card =
        heightCount H j ((x + (n + 1 - u)) % (n + 1)) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    unfold heightCount
    rw [Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun l _ ↦ ?_
    rw [← Nat.add_sub_assoc hu.le, ← add_mod_eq_iff (H l).is_lt hu hx.2]
    constructor
    · rintro ⟨⟨hl, -⟩, h⟩; exact ⟨hl, h⟩
    · rintro ⟨hl, h⟩; exact ⟨⟨hl, h ▸ hx.1⟩, h⟩
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_Ico_add' (fun y ↦ heightCount H j (y % (n + 1))),
    freeWalk, freeWalk, ← Finset.sum_Ico_eq_sub _ (by omega),
    show m + (n + 1 - u) = n + 1 + m - u by omega,
    show n + 1 + (n + 1 - u) = 2 * (n + 1) - u by omega, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sum]
  rw [show 2 * (n + 1) - u - (n + 1 + m - u) = n + 1 - m by omega]
  ring

/-- A finite set of integers whose elements are less than `d` apart has at most `d` elements. -/
private lemma card_le_of_forall_lt_add {S : Finset ℤ} {d : ℤ}
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → y < x + d) :
    S.card ≤ d.toNat := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hsub : S ⊆ Finset.Ico (S.min' hS) (S.min' hS + d) := fun x hx ↦
    Finset.mem_Ico.2 ⟨S.min'_le x hx, h _ (S.min'_mem hS) x hx (S.min'_le x hx)⟩
  calc S.card ≤ (Finset.Ico (S.min' hS) (S.min' hS + d)).card := Finset.card_le_card hsub
    _ = d.toNat := by simp

/-- **Cycle lemma.** For any heights, among the `n + 1` cyclic shifts of the heights at most
`n + 1 - j` leave no win among the first `j` players. -/
private lemma card_shift_noWin_le (H : Fin (n + 1) → Fin (n + 1)) {j : ℕ} (hj : j ≤ n + 1) :
    (Finset.univ.filter fun u : Fin (n + 1) ↦ NoWin (fun l ↦ H l + u) j).card ≤ n + 1 - j := by
  set φ : Fin (n + 1) → ℤ := fun u ↦ freeWalk H j (2 * (n + 1) - u)
  -- a shift `u` is good when the walk at `2 (n + 1) - u` exceeds its last `n + 1` values
  have hgood (u : Fin (n + 1)) (hu : NoWin (fun l ↦ H l + u) j) (m : ℕ) (hm : m < n + 1) :
      freeWalk H j (n + 1 + m - u) < freeWalk H j (2 * (n + 1) - u) := by
    have h := hu m hm
    simp only [Fin.val_add] at h
    have := card_shift_eq H j u.is_lt hm
    omega
  have hper (u : Fin (n + 1)) :
      freeWalk H j (2 * (n + 1) - u) = freeWalk H j (n + 1 - u) + ((n : ℤ) + 1 - j) := by
    rw [← freeWalk_add H hj, show n + 1 - (u : ℕ) + (n + 1) = 2 * (n + 1) - u by omega]
  have hlt (u u' : Fin (n + 1)) (hu' : NoWin (fun l ↦ H l + u') j) (h : u' < u) : φ u < φ u' := by
    have := hgood u' hu' (n + 1 - u + u') (by omega)
    simp only [φ]
    rwa [show n + 1 + (n + 1 - (u : ℕ) + u') - u' = 2 * (n + 1) - u by omega] at this
  have hle (u u' : Fin (n + 1)) (hu : NoWin (fun l ↦ H l + u) j) (h : u' ≤ u) :
      φ u' < φ u + ((n : ℤ) + 1 - j) := by
    have := hgood u hu (u - u') (by omega)
    simp only [φ]
    rw [show n + 1 + ((u : ℕ) - u') - u = n + 1 - u' by omega] at this
    rw [hper u']
    linarith
  set G := Finset.univ.filter fun u : Fin (n + 1) ↦ NoWin (fun l ↦ H l + u) j
  have hinj : Set.InjOn φ G := by
    intro u hu u' hu' h
    simp only [G, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hu'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact (hlt u' u hu h').ne h.symm
    · exact (hlt u u' hu' h').ne h
  have hcard := card_le_of_forall_lt_add (S := G.image φ) (d := (n : ℤ) + 1 - j)
    fun x hx y hy hxy ↦ by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
      rcases le_or_gt u' u with h | h
      · exact hle u u' hu h
      · exact absurd hxy (not_le.2 (hlt u' u hu h))
  rw [Finset.card_image_of_injOn hinj] at hcard
  omega

/-- The heights with no win among the first `j` players are at most a fraction
`(n + 1 - j) / (n + 1)` of all heights. -/
private lemma card_noWin_le (j : ℕ) (hj : j ≤ n + 1) :
    (n + 1) * (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin H j).card ≤
      (n + 1 - j) * (n + 1) ^ (n + 1) := by
  -- the shift by `u` is a bijection of the heights
  have hshift (u : Fin (n + 1)) :
      (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin (fun l ↦ H l + u) j).card =
        (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin H j).card :=
    Finset.card_equiv (Equiv.piCongrRight fun _ ↦ Equiv.addRight u) fun H ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  calc (n + 1) * (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin H j).card
      = ∑ u : Fin (n + 1), (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
          NoWin (fun l ↦ H l + u) j).card := by simp [hshift]
    _ = ∑ H : Fin (n + 1) → Fin (n + 1),
          (Finset.univ.filter fun u : Fin (n + 1) ↦ NoWin (fun l ↦ H l + u) j).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _H : Fin (n + 1) → Fin (n + 1), (n + 1 - j) :=
        Finset.sum_le_sum fun H _ ↦ card_shift_noWin_le H hj
    _ = (n + 1 - j) * (n + 1) ^ (n + 1) := by simp [mul_comm]

/-- **Uniformity bound (cycle lemma).** For uniform heights, nobody among the first `j` players
has won with probability at most `(n + 1 - j) / (n + 1)`; with the top height at position `j`,
this gives the count below. -/
private lemma card_noWin_last_le (j : Fin (n + 1)) :
    (n + 1) ^ 2 * (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
      NoWin H j ∧ H j = Fin.last n).card ≤ (n + 1 - j) * (n + 1) ^ (n + 1) := by
  -- the height at the position `j` is uniform and independent of `NoWin H j`
  have hv (v : Fin (n + 1)) :
      (Finset.filter (fun H : Fin (n + 1) → Fin (n + 1) ↦ H j = v)
        (Finset.univ.filter fun H ↦ NoWin H j)).card =
      (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
        NoWin H j ∧ H j = Fin.last n).card := by
    let e : (Fin (n + 1) → Fin (n + 1)) ≃ (Fin (n + 1) → Fin (n + 1)) :=
      Equiv.piCongrRight fun l ↦ if l = j then Equiv.swap v (Fin.last n) else Equiv.refl _
    refine Finset.card_equiv e fun H ↦ ?_
    have he : ∀ l : Fin (n + 1), (l : ℕ) < j → e H l = H l := fun l hl ↦ by
      have : l ≠ j := fun h ↦ by simp [h] at hl
      simp [e, this]
    have hej : e H j = Equiv.swap v (Fin.last n) (H j) := by simp [e]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [noWin_congr he, hej, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin H j)
    (t := Finset.univ) (f := fun H ↦ H j) fun _ _ ↦ Finset.mem_univ _
  rw [Finset.sum_congr rfl fun v _ ↦ hv v, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  rw [pow_two, mul_assoc, ← hsum]
  exact card_noWin_le j j.is_lt.le

/-- Twice the sum of `n + 1 - i` for `i ≤ n`. -/
private lemma two_mul_sum_range_sub (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), (n + 1 - i) = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [mul_add, ih]
    ring

/-- The sum over the positions of the counts of `card_noWin_last_le`. -/
private lemma two_mul_sum_card_noWin_last_le :
    2 * (n + 1) ^ 2 * ∑ j : Fin (n + 1), (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
      NoWin H j ∧ H j = Fin.last n).card ≤ (n + 2) * (n + 1) ^ (n + 2) := by
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ card_noWin_last_le (n := n) j
  rw [← Finset.mul_sum, ← Finset.sum_mul,
    Fin.sum_univ_eq_sum_range (fun j ↦ n + 1 - j) (n + 1)] at h
  calc 2 * (n + 1) ^ 2 * ∑ j : Fin (n + 1), (Finset.univ.filter
        fun H : Fin (n + 1) → Fin (n + 1) ↦ NoWin H j ∧ H j = Fin.last n).card
      ≤ 2 * ((∑ i ∈ Finset.range (n + 1), (n + 1 - i)) * (n + 1) ^ (n + 1)) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left 2 h
    _ = (n + 2) * (n + 1) ^ (n + 2) := by
        rw [← mul_assoc, two_mul_sum_range_sub]; ring

/-- The terminal values of the ladder have weighted sum at most `1` when
`p * a ≤ 2 (n + 1) ^ 2 / (n + 2)`. -/
private lemma sum_ladderWeight_mul_ladderValue_le {α : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ⊤)
    (i : Fin (n + 1)) :
    ∑ ω, ladderWeight n ((2 * (n + 1) : ℕ) / (n + 1 + 1 : ℕ) * α) ω *
      ladderValue n ((n + 1 : ℕ) / α) i ω ≤ 1 := by
  rw [sum_ladderWeight_mul_ladderValue]
  set A : ℕ := ∑ j : Fin (n + 1), (Finset.univ.filter fun H : Fin (n + 1) → Fin (n + 1) ↦
      NoWin H j ∧ H j = Fin.last n).card
  have hA := two_mul_sum_card_noWin_last_le (n := n)
  rw [← Nat.cast_sum]
  have hK0 : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ 0 := pow_ne_zero _ (by simp)
  have hKtop : (n + 1 : ℝ≥0∞) ^ (n + 2) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hA' : 2 * (n + 1) * (n + 1) * A ≤ (n + 1) ^ (n + 2) * (n + 1 + 1) :=
    calc 2 * (n + 1) * (n + 1) * A = 2 * (n + 1) ^ 2 * A := by ring
      _ ≤ (n + 2) * (n + 1) ^ (n + 2) := hA
      _ = (n + 1) ^ (n + 2) * (n + 1 + 1) := by ring
  calc ((2 * (n + 1) : ℕ) : ℝ≥0∞) / (n + 1 + 1 : ℕ) * α / (n + 1 : ℝ≥0∞) ^ (n + 2) *
        ((n + 1 : ℕ) / α) * (A : ℝ≥0∞)
      = ((2 * (n + 1) : ℕ) : ℝ≥0∞) * (n + 1 : ℕ) * A / (n + 1 + 1 : ℕ) /
          (n + 1 : ℝ≥0∞) ^ (n + 2) * (α * α⁻¹) := by
        simp only [div_eq_mul_inv]; ring
    _ ≤ 1 := by
        rw [ENNReal.mul_inv_cancel hα0 hαtop, mul_one, ENNReal.div_le_iff hK0 hKtop, one_mul,
          ENNReal.div_le_iff (by simp) (ENNReal.natCast_ne_top _)]
        exact_mod_cast hA'

end Ladder

/-! ### The construction -/

/-- **E-BH on the running maxima of test martingales rejects with probability
`2 * K * α / (K + 1)`.** For every `K` and every level `α ≤ (K + 1) / (2 * K)` there are `K`
test martingales `M i` for one filtration, under a probability measure `P`, for which e-BH at
level `α` on the running maxima makes a rejection, that is, some nonempty set `R` of hypotheses
has `K ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`, with probability `2 * K * α / (K + 1)`. Every
hypothesis `{P}` is true. For two and three hypotheses this attains the bounds
`ProbabilityTheory.measure_exists_selfConsistent_iSup_le_of_card_eq_two` and
`ProbabilityTheory.measure_exists_selfConsistent_iSup_le_of_card_eq_three`. -/
theorem exists_isTestMartingale_measure_exists_selfConsistent_iSup_eq (K : ℕ) {α : ℝ≥0∞}
    (hα : α ≤ (K + 1) / (2 * K)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
      (M : Fin K → ℕ → Ω → ℝ≥0∞), IsProbabilityMeasure P ∧
      (∀ i, IsTestMartingale (M i) ℱ {P}) ∧
      P {ω | ∃ R : Finset (Fin K), R.Nonempty ∧
        ∀ i ∈ R, (K : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} = 2 * K * α / (K + 1) := by
  -- no hypotheses, or level `0`: constant test martingales, no rejection
  by_cases hK : K = 0 ∨ α = 0
  · refine ⟨Unit, inferInstance, Measure.dirac (), ⊥, fun _ _ _ ↦ 1, inferInstance,
      fun _ ↦ isTestMartingale_one fun P hP ↦ by rw [Set.mem_singleton_iff.1 hP]; infer_instance,
      ?_⟩
    have : {ω : Unit | ∃ R : Finset (Fin K), R.Nonempty ∧
        ∀ i ∈ R, (K : ℝ≥0∞) ≤ α * R.card * ⨆ _ : ℕ, (1 : ℝ≥0∞)} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω ⟨R, ⟨i, hi⟩, hR⟩ ↦ ?_
      rcases hK with rfl | rfl
      · exact i.elim0
      · have h := hR i hi
        simp only [zero_mul, nonpos_iff_eq_zero, Nat.cast_eq_zero] at h
        subst h
        exact i.elim0
    rw [this, measure_empty]
    rcases hK with rfl | rfl <;> simp
  push Not at hK
  obtain ⟨hK0, hα0⟩ := hK
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero hK0)
  have hα' : α ≤ ((n + 1 + 1 : ℕ) : ℝ≥0∞) / ((2 * (n + 1) : ℕ) : ℝ≥0∞) := by
    push_cast at hα ⊢
    exact hα
  have hαtop : α ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hα'
  set p : ℝ≥0∞ := ((2 * (n + 1) : ℕ) : ℝ≥0∞) / ((n + 1 + 1 : ℕ) : ℝ≥0∞) * α with hp_def
  have hp_eq : 2 * ((n + 1 : ℕ) : ℝ≥0∞) * α / (((n + 1 : ℕ) : ℝ≥0∞) + 1) = p := by
    rw [hp_def]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hp1 : p ≤ 1 := by
    calc p ≤ ((2 * (n + 1) : ℕ) : ℝ≥0∞) / ((n + 1 + 1 : ℕ) : ℝ≥0∞) *
          (((n + 1 + 1 : ℕ) : ℝ≥0∞) / ((2 * (n + 1) : ℕ) : ℝ≥0∞)) := mul_le_mul_right hα' _
      _ = 1 := by
        rw [← mul_div_assoc, ENNReal.div_mul_cancel (by simp) (ENNReal.natCast_ne_top _),
          ENNReal.div_self (by simp) (ENNReal.natCast_ne_top _)]
  have hp0 : p ≠ 0 := mul_ne_zero (ENNReal.div_pos (by simp) (ENNReal.natCast_ne_top _)).ne' hα0
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  refine ⟨LadderΩ n, inferInstance, ∑ ω, ladderWeight n p ω • Measure.dirac ω,
    fiberFiltration (ladderInfo n) ladderInfo_refine, ladder n p ((n + 1 : ℕ) / α),
    ⟨?_⟩, fun i ↦ isTestMartingale_fiberAvg (ladderWeight_ne_top hptop) _ ladderInfo_refine _
      (sum_ladderWeight_mul_ladderValue_le hα0 hαtop i), ?_⟩
  · classical
    rw [← setLIntegral_one, setLIntegral_sum_smul_dirac]
    simpa using sum_ladderWeight (n := n) hp1
  · have hset : {ω : LadderΩ n | ∃ R : Finset (Fin (n + 1)), R.Nonempty ∧ ∀ i ∈ R,
        ((n + 1 : ℕ) : ℝ≥0∞) ≤ α * R.card * ⨆ t, ladder n p ((n + 1 : ℕ) / α) i t ω} =
        {ω | ω.1 = true} := by
      ext ω
      exact exists_selfConsistent_ladder_iff hα0 hαtop hp0 hptop ω
    rw [hset, hp_eq, ← setLIntegral_one, setLIntegral_sum_smul_dirac]
    simpa using sum_ladderWeight_true (n := n) p

end ProbabilityTheory
