/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction

/-!
# Upper confidence levels of an exponential family

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic, with open interval of means `M` and
extended divergence `dbar(x, q)` (`MeasureTheory.Measure.expFamilyRate`), defined for every real
level `x` and every mean `q`. The *upper confidence level* at a level `x` and an exploration budget
`c ∈ [0, ∞]` is
`U(x, c) = sup ({x} ∪ {q ∈ M | x ≤ q, dbar(x, q) ≤ c})`,
valued in `EReal`: the largest mean at or above `x` whose member is within extended divergence `c`
of the level `x`, or `x` itself when no such mean exists. It is the index of the KL-UCB algorithm
for the exponential family, at the empirical mean `x` of the observed statistics
[GC11, Section 4; CGMMS13; LS, Chapter 10]. Allowing every real level `x`, not only the means,
covers empirical means outside `M`, such as the empirical means `0` and `1` of Bernoulli
observations.

Since `dbar(x, ·)` is continuous and nondecreasing on the means above `x`, a mean `q ≥ x` lies
below `U(x, c)` exactly when `dbar(x, q) ≤ c`: this is how the confidence level enters the
concentration bounds of KL-UCB.

## Main definitions

* `MeasureTheory.Measure.expFamilyUpper ρ T x c`: the upper confidence level `U(x, c)`.

## Main statements

* `MeasureTheory.Measure.le_expFamilyUpper`: `x ≤ U(x, c)`.
* `MeasureTheory.Measure.expFamilyUpper_le_iff`: the bounds on `U(x, c)`.
* `MeasureTheory.Measure.le_expFamilyUpper_iff`: for a mean `q ≥ x`, `q ≤ U(x, c)` if and only if
  `dbar(x, q) ≤ c`.
* `MeasureTheory.Measure.le_expFamilyRate_of_expFamilyUpper_le`: if `U(x, c) ≤ q` for a mean `q`,
  then `c ≤ dbar(x, q)`.
* `MeasureTheory.Measure.expFamilyUpper_mono`: `U` is monotone in both arguments.
* `MeasureTheory.Measure.measurable_expFamilyUpper`: `U` is jointly measurable in `(x, c)`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011.
* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler
  upper confidence bounds for optimal sequential allocation*, Ann. Statist. 41(3), 2013.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 10.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal Topology

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {x x' q : ℝ}
  {c c' : ℝ≥0∞}

/-- The **upper confidence level** `U(x, c)` of the exponential family of `ρ` and `T`, at a level
`x` and a budget `c`: the supremum in `EReal` of `x` and of the means `q ≥ x` of the family with
extended divergence `dbar(x, q) ≤ c` [GC11, Section 4]. It is at least `x`
(`le_expFamilyUpper`), and a mean `q ≥ x` lies below it exactly when `dbar(x, q) ≤ c`
(`le_expFamilyUpper_iff`). -/
noncomputable def expFamilyUpper (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x : ℝ) (c : ℝ≥0∞) : EReal :=
  sSup (insert (x : EReal)
    ((↑) '' {q | q ∈ ρ.expFamilyMeans T ∧ x ≤ q ∧ ρ.expFamilyRate T x q ≤ c}))

lemma expFamilyUpper_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x : ℝ) (c : ℝ≥0∞) :
    ρ.expFamilyUpper T x c = sSup (insert (x : EReal)
      ((↑) '' {q | q ∈ ρ.expFamilyMeans T ∧ x ≤ q ∧ ρ.expFamilyRate T x q ≤ c})) :=
  (rfl)

/-- The upper confidence level is at least the level: `x ≤ U(x, c)`. -/
lemma le_expFamilyUpper (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x : ℝ) (c : ℝ≥0∞) :
    (x : EReal) ≤ ρ.expFamilyUpper T x c :=
  le_sSup (mem_insert _ _)

/-- A mean `q ≥ x` with `dbar(x, q) ≤ c` lies below the upper confidence level `U(x, c)`. -/
lemma le_expFamilyUpper_of_expFamilyRate_le (hq : q ∈ ρ.expFamilyMeans T) (hxq : x ≤ q)
    (h : ρ.expFamilyRate T x q ≤ c) : (q : EReal) ≤ ρ.expFamilyUpper T x c :=
  le_sSup (mem_insert_of_mem _ ⟨q, ⟨hq, hxq, h⟩, rfl⟩)

/-- **Bounds on the upper confidence level**: `U(x, c) ≤ r` if and only if `x ≤ r` and every mean
`q ≥ x` with `dbar(x, q) ≤ c` is at most `r`. -/
theorem expFamilyUpper_le_iff {r : EReal} :
    ρ.expFamilyUpper T x c ≤ r ↔ (x : EReal) ≤ r ∧
      ∀ q ∈ ρ.expFamilyMeans T, x ≤ q → ρ.expFamilyRate T x q ≤ c → (q : EReal) ≤ r := by
  simp only [expFamilyUpper_def, sSup_le_iff, forall_mem_insert, forall_mem_image,
    mem_ofPred_eq, and_imp]

/-- **Characterization of the upper confidence level**: for a nondegenerate statistic and a mean
`q ≥ x`, `q ≤ U(x, c)` if and only if `dbar(x, q) ≤ c`. This uses that `dbar(x, ·)` is continuous
and nondecreasing on the means above `x`. -/
theorem le_expFamilyUpper_iff (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hq : q ∈ ρ.expFamilyMeans T)
    (hxq : x ≤ q) : (q : EReal) ≤ ρ.expFamilyUpper T x c ↔ ρ.expFamilyRate T x q ≤ c := by
  refine ⟨fun h ↦ ?_, le_expFamilyUpper_of_expFamilyRate_le hq hxq⟩
  by_contra! hlt
  -- By continuity, `dbar(x, ·)` exceeds `c` on an open interval `(l, u)` around `q`.
  have hev : ∀ᶠ q' in 𝓝 q, c < ρ.expFamilyRate T x q' :=
    ((continuousOn_expFamilyRate_right hT x).continuousAt (expFamilyMeans_mem_nhds hT hq))
      |>.eventually (lt_mem_nhds hlt)
  obtain ⟨l, u, ⟨hlq, hqu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hev
  have hxq' : x < q := hxq.lt_of_ne fun hxq ↦ by
    subst hxq
    rw [expFamilyRate_self hq] at hlt
    exact not_lt_zero hlt
  -- Every mean `q' ≥ x` with `dbar(x, q') ≤ c` is at most `max x l`, which is below `q`.
  have hU : ρ.expFamilyUpper T x c ≤ ((max x l : ℝ) : EReal) := by
    refine expFamilyUpper_le_iff.2 ⟨EReal.coe_le_coe_iff.2 (le_max_left x l),
      fun q' hq' hxq'' hq'c ↦ EReal.coe_le_coe_iff.2 (not_lt.1 fun hlt' ↦ ?_)⟩
    rcases le_or_gt q' q with hq'q | hqq'
    · exact (hlu ⟨(le_max_right x l).trans_lt hlt', hq'q.trans_lt hqu⟩).not_ge hq'c
    · exact (hlt.trans_le (monotoneOn_expFamilyRate_right x ⟨hq, hxq⟩ ⟨hq', hxq''⟩
        hqq'.le)).not_ge hq'c
  exact (max_lt hxq' hlq).not_ge (EReal.coe_le_coe_iff.1 (h.trans hU))

/-- **The budget is below the divergence to a mean above the upper confidence level**: for a
nondegenerate statistic, if `U(x, c) ≤ q` for a mean `q` of the family, then `c ≤ dbar(x, q)`.
This is a converse of `le_expFamilyUpper_of_expFamilyRate_le` at the means above `U(x, c)`. -/
theorem le_expFamilyRate_of_expFamilyUpper_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hq : q ∈ ρ.expFamilyMeans T) (h : ρ.expFamilyUpper T x c ≤ q) :
    c ≤ ρ.expFamilyRate T x q := by
  by_contra! hlt
  have hxq : x ≤ q := EReal.coe_le_coe_iff.1 ((le_expFamilyUpper ρ T x c).trans h)
  -- by continuity of `dbar(x, ·)` at `q`, a mean `q' > q` has `dbar(x, q') < c`, so it lies below
  -- `U(x, c) ≤ q`
  have hev : ∀ᶠ q' in 𝓝 q, q' ∈ ρ.expFamilyMeans T ∧ ρ.expFamilyRate T x q' < c :=
    Filter.Eventually.and (expFamilyMeans_mem_nhds hT hq)
      (((continuousOn_expFamilyRate_right hT x).continuousAt (expFamilyMeans_mem_nhds hT hq))
        |>.eventually (gt_mem_nhds hlt))
  obtain ⟨q', ⟨hq', hq'c⟩, hqq'⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi q))).exists
  exact (not_le.2 hqq') (EReal.coe_le_coe_iff.1
    ((le_expFamilyUpper_of_expFamilyRate_le hq' (hxq.trans (le_of_lt hqq')) hq'c.le).trans h))

/-- The upper confidence level is monotone in both arguments: a larger level and a larger budget
give a larger level `U(x, c)`. -/
theorem expFamilyUpper_mono (hx : x ≤ x') (hc : c ≤ c') :
    ρ.expFamilyUpper T x c ≤ ρ.expFamilyUpper T x' c' := by
  refine expFamilyUpper_le_iff.2
    ⟨(EReal.coe_le_coe_iff.2 hx).trans (le_expFamilyUpper ρ T x' c'), fun q hq hxq hqc ↦ ?_⟩
  rcases le_or_gt q x' with hqx | hqx
  · exact (EReal.coe_le_coe_iff.2 hqx).trans (le_expFamilyUpper ρ T x' c')
  · -- `dbar(·, q)` is nonincreasing below `q`, so `dbar(x', q) ≤ dbar(x, q) ≤ c ≤ c'`.
    exact le_expFamilyUpper_of_expFamilyRate_le hq hqx.le
      ((antitoneOn_expFamilyRate_left hq hxq hqx.le hx).trans (hqc.trans hc))

/-- The upper confidence level is monotone in the budget `c`. -/
theorem monotone_expFamilyUpper (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x : ℝ) :
    Monotone (ρ.expFamilyUpper T x) :=
  fun _ _ hc ↦ expFamilyUpper_mono le_rfl hc

/-- The upper confidence level is monotone in the level `x`. -/
theorem monotone_expFamilyUpper_left (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (c : ℝ≥0∞) :
    Monotone (ρ.expFamilyUpper T · c) :=
  fun _ _ hx ↦ expFamilyUpper_mono hx le_rfl

/-! ### Measurability -/

/-- The candidate means of the countable description of the upper confidence level: the
rationals, and the infimum of the means, which is the only mean not approximated from below by
rational means when it is the least mean. -/
private noncomputable def candidateMean (ρ : Measure 𝓧) (T : 𝓧 → ℝ) : Option ℚ → ℝ
  | none => sInf (ρ.expFamilyMeans T)
  | some r => r

open scoped Classical in
/-- The contribution of a candidate mean to the countable description of the upper confidence
level at `(x, c)`: the candidate itself if it is a mean `q ≥ x` with `dbar(x, q) ≤ c`, else `⊥`. -/
private noncomputable def candidateTerm (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (r : Option ℚ)
    (p : ℝ × ℝ≥0∞) : EReal :=
  if candidateMean ρ T r ∈ ρ.expFamilyMeans T ∧ p.1 ≤ candidateMean ρ T r ∧
    ρ.expFamilyRate T p.1 (candidateMean ρ T r) ≤ p.2
  then (candidateMean ρ T r : EReal) else ⊥

private lemma candidateTerm_of_mem (r : Option ℚ) (p : ℝ × ℝ≥0∞)
    (h : candidateMean ρ T r ∈ ρ.expFamilyMeans T ∧ p.1 ≤ candidateMean ρ T r ∧
      ρ.expFamilyRate T p.1 (candidateMean ρ T r) ≤ p.2) :
    candidateTerm ρ T r p = candidateMean ρ T r := by
  simp [candidateTerm, h]

private lemma measurable_candidateTerm (r : Option ℚ) : Measurable (candidateTerm ρ T r) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  simp only [ofPred_and]
  exact (MeasurableSet.const _).inter ((measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le ((lowerSemicontinuous_expFamilyRate_left _).measurable.comp measurable_fst)
      measurable_snd))

/-- The upper confidence level as a countable supremum over the candidate means. -/
private lemma expFamilyUpper_eq_max_iSup (p : ℝ × ℝ≥0∞) :
    ρ.expFamilyUpper T p.1 p.2 = max (p.1 : EReal) (⨆ r : Option ℚ, candidateTerm ρ T r p) := by
  obtain ⟨x, c⟩ := p
  refine le_antisymm (expFamilyUpper_le_iff.2 ⟨le_max_left _ _, fun q hq hxq hqc ↦ ?_⟩)
    (max_le (le_expFamilyUpper ρ T x c) (iSup_le fun r ↦ ?_))
  · rcases hxq.eq_or_lt with rfl | hxq'
    · exact le_max_left _ _
    refine le_max_of_le_right ?_
    by_cases hmin : ∃ m ∈ ρ.expFamilyMeans T, m < q
    · -- The rational means between `max x m` and `q` are candidates, and approximate `q`.
      obtain ⟨m, hm, hmq⟩ := hmin
      by_contra! hlt
      obtain ⟨r, hr, hrq⟩ := EReal.lt_iff_exists_rat_btwn.1
        (max_lt hlt (EReal.coe_lt_coe_iff.2 (max_lt hxq' hmq)))
      rw [max_lt_iff, EReal.coe_lt_coe_iff] at hr
      have hrq' : (r : ℝ) ≤ q := (EReal.coe_lt_coe_iff.1 hrq).le
      have hr_mem : (r : ℝ) ∈ ρ.expFamilyMeans T :=
        Icc_subset_expFamilyMeans hm hq ⟨(le_max_right x m).trans hr.2.le, hrq'⟩
      have hxr : x ≤ r := (le_max_left x m).trans hr.2.le
      refine hr.1.not_ge (le_iSup_of_le (some r) (candidateTerm_of_mem (some r) (x, c)
        ⟨hr_mem, hxr, (monotoneOn_expFamilyRate_right x ⟨hr_mem, hxr⟩ ⟨hq, hxq⟩ hrq').trans
          hqc⟩).ge)
    · -- Otherwise `q` is the least mean, that is, their infimum.
      simp only [not_exists, not_and, not_lt] at hmin
      have hinf : candidateMean ρ T none = q :=
        (show IsLeast (ρ.expFamilyMeans T) q from ⟨hq, hmin⟩).csInf_eq
      refine le_iSup_of_le none (le_of_eq ?_)
      rw [candidateTerm_of_mem none (x, c) (by rw [hinf]; exact ⟨hq, hxq, hqc⟩), hinf]
  · by_cases h : candidateMean ρ T r ∈ ρ.expFamilyMeans T ∧ x ≤ candidateMean ρ T r ∧
        ρ.expFamilyRate T x (candidateMean ρ T r) ≤ c
    · rw [candidateTerm_of_mem r (x, c) h]
      exact le_expFamilyUpper_of_expFamilyRate_le h.1 h.2.1 h.2.2
    · simp [candidateTerm, h]

/-- The upper confidence level is jointly measurable in the level and the budget. -/
theorem measurable_expFamilyUpper : Measurable (Function.uncurry (ρ.expFamilyUpper T)) := by
  have h : Function.uncurry (ρ.expFamilyUpper T) =
      fun p ↦ max (p.1 : EReal) (⨆ r : Option ℚ, candidateTerm ρ T r p) :=
    funext expFamilyUpper_eq_max_iSup
  rw [h]
  exact (measurable_coe_real_ereal.comp measurable_fst).max
    (Measurable.iSup measurable_candidateTerm)

@[fun_prop]
theorem _root_.Measurable.expFamilyUpper {α : Type*} {mα : MeasurableSpace α} {f : α → ℝ}
    {g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a ↦ ρ.expFamilyUpper T (f a) (g a) := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    measurable_expFamilyUpper.comp (hf.prodMk hg)

end MeasureTheory.Measure
