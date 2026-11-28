/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Semicontinuity
public import LMLExplore.MeasureTheory.Measure.TauEnvelope
import LMLExplore.MeasureTheory.Measure.SetwiseConvergence
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The bipolar rate through the envelopes of the smallest relative entropy

Let `Q` be a probability measure on `𝓧` (the alternative) and `S` a set of probability measures
on `𝓧` (the null), and write `d = bipolarRate Q S` and `a n = maxLogGrowth Q S n`. For `n ≥ 1`,
let `Φ_n R = klInf R (sampleNull S n)` be the smallest relative entropy from a law `R` of `n`
observations to the `n`-sample null, and `Φ R = klInf R S`. This file compares the bipolar rate
with the lower semicontinuous envelopes of these functions (`MeasureTheory.tauEnvelope`, the
neighbourhood envelope `Φ^τ` for the topology of the integrals of the bounded measurable
functions, and `MeasureTheory.seqTauEnvelope`, the sequential envelope `Φ^{τ,seq}` for setwise
convergence) [EVR26, Notes 15 and 19]. On any measurable space and for any null of probability
measures:

* `a n ≤ Φ_n^τ(Q ^ n) ≤ n d`, so that `d` is the supremum, and the limit, of `Φ_n^τ(Q ^ n) / n`:
  a variational formula for the rate;
* `a 1 ≤ Φ^τ(Q) ≤ d ≤ Φ^{τ,seq}(Q) ≤ klInf Q S`, so that `d = klInf Q S` forces the lower
  semicontinuity of `klInf · S` at `Q` in the sequential sense, and the lower semicontinuity in the
  neighbourhood sense, `klInf Q S ≤ Φ^τ(Q)`, gives `d = klInf Q S` [RR26, Theorem 4.1];
* when `klInf Q S < ∞`, `d = klInf Q S` exactly when for every `η > 0` some `n ≥ 1` and basic
  neighbourhood of `Q ^ n` contain only laws at relative entropy at least `n (klInf Q S - η)` from
  every `P ^ n`, `P ∈ S`.

The bound `Φ_n^τ(Q ^ n) ≤ n d` is the Sanov-type lower bound on the rate
(`ProbabilityTheory.le_bipolarRate_of_forall_le_klInf`) applied to blocks of `n` observations,
whose bipolar rate is `n d` (`ProbabilityTheory.bipolarRate_pi_sampleNull`). The bound `a 1 ≤ Φ^τ`
follows from the Donsker–Varadhan inequality for a bounded statistic, after truncation of the
logarithm of an e-variable. The bound `d ≤ Φ^{τ,seq}` uses the setwise convergence of the products
of setwise convergent probability measures (`MeasureTheory.tendsto_measure_pi_of_tendsto_measure`)
and `Φ_n(R ^ n) = n Φ(R)` (`ProbabilityTheory.klInf_pi_sampleNull`).

## Main statements

* `ProbabilityTheory.maxLogGrowth_le_tauEnvelope`,
  `ProbabilityTheory.tauEnvelope_le_mul_bipolarRate`: `a n ≤ Φ_n^τ(Q ^ n) ≤ n d`
  [EVR26, Note 15, Theorem (1)].
* `ProbabilityTheory.bipolarRate_eq_iSup_tauEnvelope_div`,
  `ProbabilityTheory.tendsto_tauEnvelope_div_bipolarRate`: the variational formula
  `d = sup_n Φ_n^τ(Q ^ n) / n = lim_n Φ_n^τ(Q ^ n) / n` [EVR26, Note 15, Theorem (2)].
* `ProbabilityTheory.maxEPower_le_tauEnvelope_klInf`,
  `ProbabilityTheory.tauEnvelope_klInf_le_bipolarRate`: `a 1 ≤ Φ^τ(Q) ≤ d`
  [EVR26, Note 15, Theorem (3)].
* `ProbabilityTheory.bipolarRate_le_seqTauEnvelope`: `d ≤ Φ^{τ,seq}(Q)` [EVR26, Note 19,
  Theorem (4)].
* `ProbabilityTheory.bipolarRate_eq_klInf_of_klInf_le_tauEnvelope`,
  `ProbabilityTheory.bipolarRate_eq_klInf_of_forall_exists_forall_le`: the rate is `klInf Q S`
  under lower semicontinuity of `klInf · S` at `Q` [RR26, Theorem 4.1].
* `ProbabilityTheory.bipolarRate_eq_klInf_iff_forall_exists`: the block criterion for
  `d = klInf Q S` when `klInf Q S < ∞` [EVR26, Note 15, Theorem (4)].

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/Envelopes.lean` in the paper
project `RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. The block criterion
assumes `klInf Q S < ∞`, as the revised Note 15 does: without it the criterion fails for the
geometric law `P {j} = 2^{-(j+1)}` and the law `Q {j} ∝ 1 / (j + 1)²` on `ℕ`, for which
`d = klInf Q S = ∞` while every basic neighbourhood of every `Q ^ n` contains a law at finite
relative entropy from `P ^ n` [EVR26, Note 15].

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and the Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and refereed
  by AI agents: Note 15, *When does the bipolar rate equal KL_inf? A variational formula*, and
  Note 19, *The bipolar rate is not determined by the single-letter τ-envelopes of KL_inf*.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### Lower bounds by the expected logarithms of e-variables -/

/-- **One observation: the largest e-power is at most the envelope** [EVR26, Note 15,
Theorem (3)]. The largest expected logarithm of an e-variable for a null of probability measures
is at most the neighbourhood envelope at `Q` of the smallest relative entropy to the null. -/
theorem maxEPower_le_tauEnvelope_klInf (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    maxEPower Q S ≤ tauEnvelope (fun R ↦ klInf R S) Q := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc not_top_lt
  | coe c =>
    obtain ⟨E, hE, hcE⟩ := lt_maxEPower_iff.1 hc
    obtain ⟨N, f, hfm, hfN, hfP, hcf⟩ := hE.exists_bounded_lt_integral_of_lt_eintegral_log Q
      (fun P hP ↦ (hS P hP).measure_univ.le) hcE
    -- the neighbourhood where the mean of `f` is above `(∫ f ∂Q + c) / 2`
    set ε := (∫ x, f x ∂Q - c) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    refine le_trans ?_ (tauNbhdInf_le_tauEnvelope (g := fun _ : Fin 1 ↦ f) (fun _ ↦ hfm)
      (fun _ ↦ ⟨N, hfN⟩) hε)
    refine le_tauNbhdInf_iff.2 fun R hR hRf ↦ le_klInf_iff.2 fun P hP ↦ ?_
    have := hS P hP
    have hint : Integrable f R :=
      .of_bound hfm.aestronglyMeasurable N (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact hfN x)
    have hexp : Integrable (fun x ↦ Real.exp (f x)) P :=
      .of_bound (by fun_prop) (Real.exp N) (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hfN x)))
    -- `∫ exp f ∂P ≤ 1`, so its logarithm is nonpositive
    have hZ1 : ∫ x, Real.exp (f x) ∂P ≤ 1 := by
      have h := hfP P hP
      rw [← ofReal_integral_eq_lintegral_ofReal hexp (.of_forall fun x ↦ (Real.exp_pos _).le)]
        at h
      exact ENNReal.ofReal_le_one.1 h
    have hlog : Real.log (∫ x, Real.exp (f x) ∂P) ≤ 0 :=
      Real.log_nonpos (integral_nonneg fun x ↦ (Real.exp_pos _).le) hZ1
    have hRf0 := abs_le.1 (hRf 0)
    -- the Donsker–Varadhan inequality for `f`
    have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv (μ := R) (ν := P) hint hexp
    rw [klIntegral_eq_klDiv (by simp)]
    calc (c : EReal)
    _ ≤ ((∫ x, f x ∂R - Real.log (∫ x, Real.exp (f x) ∂P) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith)
    _ ≤ ((ENNReal.ofReal (∫ x, f x ∂R - Real.log (∫ x, Real.exp (f x) ∂P)) : ℝ≥0∞) : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
    _ ≤ (klDiv R P : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hDV

/-- **The growth of `n` observations is at most the envelope** [EVR26, Note 15, Theorem (1)]. For
a null of probability measures, the largest expected logarithm `maxLogGrowth Q S n` of an
`n`-sample e-variable is at most the neighbourhood envelope, at `Q ^ n`, of the smallest relative
entropy to the `n`-sample null. -/
theorem maxLogGrowth_le_tauEnvelope (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) (n : ℕ) :
    maxLogGrowth Q S n ≤
      tauEnvelope (fun R ↦ klInf R (sampleNull S n)) (Measure.pi fun _ : Fin n ↦ Q) := by
  rw [maxLogGrowth_def]
  exact maxEPower_le_tauEnvelope_klInf _ _ (isProbabilityMeasure_of_mem_sampleNull hS n)

/-! ### Upper bounds by the bipolar rate -/

/-- **One observation: the envelope is at most the rate** [EVR26, Note 15, Theorem (3)]. For a
null of probability measures, the neighbourhood envelope at `Q` of the smallest relative entropy
to the null is at most the bipolar rate: on each basic neighbourhood of `Q`, the infimum of
`klInf · S` is a lower bound on the rate (`le_bipolarRate_of_forall_le_klInf`). -/
theorem tauEnvelope_klInf_le_bipolarRate (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    tauEnvelope (fun R ↦ klInf R S) Q ≤ bipolarRate Q S :=
  tauEnvelope_le_iff.2 fun _ _ hg hgb _ hε ↦
    le_bipolarRate_of_forall_le_klInf Q S hS hε hg hgb fun _ hR hRg ↦ tauNbhdInf_le hR hRg

/-- **The envelope of `n` observations is at most `n` times the rate** [EVR26, Note 15,
Theorem (1)]. For a null of probability measures and `n ≠ 0`, the neighbourhood envelope, at
`Q ^ n`, of the smallest relative entropy to the `n`-sample null is at most `n * bipolarRate Q S`.
-/
theorem tauEnvelope_le_mul_bipolarRate (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) {n : ℕ} (hn : n ≠ 0) :
    tauEnvelope (fun R ↦ klInf R (sampleNull S n)) (Measure.pi fun _ : Fin n ↦ Q) ≤
      n * bipolarRate Q S :=
  (tauEnvelope_klInf_le_bipolarRate _ _ (isProbabilityMeasure_of_mem_sampleNull hS n)).trans
    (bipolarRate_pi_sampleNull Q (fun P hP ↦ (hS P hP).measure_univ.le) hn).le

/-! ### The variational formula -/

/-- **The variational formula for the bipolar rate** [EVR26, Note 15, Theorem (2)]. For a null of
probability measures, the bipolar rate is the supremum over `n ≥ 1` of the neighbourhood envelope,
at `Q ^ n`, of the smallest relative entropy to the `n`-sample null, divided by `n`. -/
theorem bipolarRate_eq_iSup_tauEnvelope_div (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    bipolarRate Q S = ⨆ n : ℕ, tauEnvelope (fun R ↦ klInf R (sampleNull S (n + 1)))
      (Measure.pi fun _ : Fin (n + 1) ↦ Q) / ((n + 1 : ℕ) : EReal) := by
  refine le_antisymm ?_ (iSup_le fun n ↦ ?_)
  · rw [bipolarRate_def]
    exact iSup_mono fun n ↦ EReal.div_le_div_right_of_nonneg (by positivity)
      (maxLogGrowth_le_tauEnvelope Q S hS (n + 1))
  · exact (EReal.div_le_iff_le_mul (by exact_mod_cast Nat.succ_pos n)
      (EReal.natCast_ne_top _)).2 (tauEnvelope_le_mul_bipolarRate Q S hS n.succ_ne_zero)

/-- **The variational formula as a limit** [EVR26, Note 15, Theorem (2)]. For a null of
probability measures, the neighbourhood envelopes of the smallest relative entropy to the
`n`-sample null at `Q ^ n`, divided by `n`, tend to the bipolar rate. -/
theorem tendsto_tauEnvelope_div_bipolarRate (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    Tendsto (fun n : ℕ ↦ tauEnvelope (fun R ↦ klInf R (sampleNull S n))
      (Measure.pi fun _ : Fin n ↦ Q) / (n : EReal)) atTop (𝓝 (bipolarRate Q S)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_maxLogGrowth_div_bipolarRate Q fun P hP ↦ (hS P hP).measure_univ.le)
    tendsto_const_nhds ?_ ?_
  · exact .of_forall fun n ↦ EReal.div_le_div_right_of_nonneg (by positivity)
      (maxLogGrowth_le_tauEnvelope Q S hS n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (EReal.div_le_iff_le_mul (by exact_mod_cast hn) (EReal.natCast_ne_top _)).2
      (tauEnvelope_le_mul_bipolarRate Q S hS (by omega))

/-! ### The sequential envelope -/

/-- **The sequential envelope bounds the rate** [EVR26, Note 19, Theorem (4)]. For a null of
probability measures, the bipolar rate is at most the sequential envelope at `Q` of the smallest
relative entropy to the null. With `tauEnvelope_klInf_le_bipolarRate`,
`tauEnvelope_le_seqTauEnvelope` and `seqTauEnvelope_le`, this is the chain
`Φ^τ(Q) ≤ d ≤ Φ^{τ,seq}(Q) ≤ klInf Q S`: the equality `d = klInf Q S` forces the lower
semicontinuity of `klInf · S` at `Q` in the sequential sense. -/
theorem bipolarRate_le_seqTauEnvelope (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    bipolarRate Q S ≤ seqTauEnvelope (fun R ↦ klInf R S) Q := by
  refine le_seqTauEnvelope_iff.2 fun R hR hRQ ↦ ?_
  rw [bipolarRate_eq_iSup_tauEnvelope_div Q S hS]
  refine iSup_le fun n ↦ ?_
  have hm0 : (0 : EReal) < ((n + 1 : ℕ) : EReal) := by exact_mod_cast Nat.succ_pos n
  -- the `n + 1`-fold products of the `R k` converge to `Q ^ (n + 1)` on every measurable set
  have hseq := seqTauEnvelope_le_liminf (Φ := fun R' ↦ klInf R' (sampleNull S (n + 1)))
    (R := fun k ↦ Measure.pi fun _ : Fin (n + 1) ↦ R k) (fun _ ↦ inferInstance)
    fun A hA ↦ tendsto_measure_pi_of_tendsto_measure (fun _ ↦ hRQ) hA
  simp_rw [klInf_pi_sampleNull _ hS (n := n + 1) (by omega)] at hseq
  rw [EReal.liminf_const_mul_of_nonneg_of_ne_top hm0.le (EReal.natCast_ne_top _)] at hseq
  exact (EReal.div_le_iff_le_mul hm0 (EReal.natCast_ne_top _)).2
    ((tauEnvelope_le_seqTauEnvelope _ _).trans hseq)

/-! ### When the rate is the smallest relative entropy -/

/-- **Lower semicontinuity gives `d = klInf`.** For a null of probability measures, if the
smallest relative entropy to the null is at most its neighbourhood envelope at `Q`, that is, if
`klInf · S` is lower semicontinuous at `Q` for the topology of the integrals of bounded measurable
functions, then the bipolar rate is `klInf Q S`: the case `Φ^τ(Q) = klInf Q S` of
`tauEnvelope_klInf_le_bipolarRate` [RR26, Theorem 4.1]. -/
theorem bipolarRate_eq_klInf_of_klInf_le_tauEnvelope (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (h : klInf Q S ≤ tauEnvelope (fun R ↦ klInf R S) Q) :
    bipolarRate Q S = klInf Q S :=
  le_antisymm (bipolarRate_le_klInf Q hS) (h.trans (tauEnvelope_klInf_le_bipolarRate Q S hS))

/-- If the smallest relative entropy to `S` is lower semicontinuous at `Q` for the topology of
integrals of bounded measurable functions, in the sense of neighbourhoods, then the bipolar rate
of `Q` against `S` equals the smallest relative entropy from `Q` to `S` [RR26, Theorem 4.1]. The
test functions need only be bounded, by any constant, and measurable: no topology on `𝓧` is
used, and lower semicontinuity for weak convergence is a special case. -/
theorem bipolarRate_eq_klInf_of_forall_exists_forall_le (Q : Measure 𝓧)
    [IsProbabilityMeasure Q] (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (h : ∀ c : EReal, c < klInf Q S →
      ∃ (k : ℕ) (f : Fin k → 𝓧 → ℝ) (ε : ℝ), 0 < ε ∧ (∀ i, Measurable (f i)) ∧
        (∀ i, ∃ C, ∀ x, |f i x| ≤ C) ∧ ∀ R : Measure 𝓧, IsProbabilityMeasure R →
          (∀ i, |∫ x, f i x ∂R - ∫ x, f i x ∂Q| ≤ ε) → c ≤ klInf R S) :
    bipolarRate Q S = klInf Q S := by
  refine bipolarRate_eq_klInf_of_klInf_le_tauEnvelope Q S hS
    (le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_)
  obtain ⟨k, f, ε, hε, hfm, hfC, hU⟩ := h c hc
  exact (le_tauNbhdInf_iff.2 hU).trans (tauNbhdInf_le_tauEnvelope hfm hfC hε)

/-- **The block criterion for `d = klInf`** [EVR26, Note 15, Theorem (4)]. For a null of
probability measures with `klInf Q S < ∞`, the bipolar rate equals `klInf Q S` if and only if,
for every `η > 0`, there are `n ≥ 1`, finitely many bounded measurable statistics `g i` of `n`
observations and `ε > 0` such that every probability measure `R` on `n` observations whose
integrals of the `g i` are within `ε` of those of `Q ^ n` is at relative entropy at least
`n (klInf Q S - η)` from every `P ^ n`, `P ∈ S`. -/
theorem bipolarRate_eq_klInf_iff_forall_exists (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    (S : Set (Measure 𝓧)) (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hQS : klInf Q S ≠ ⊤) :
    bipolarRate Q S = klInf Q S ↔ ∀ η : ℝ, 0 < η →
      ∃ (n k : ℕ) (g : Fin k → (Fin n → 𝓧) → ℝ) (ε : ℝ), n ≠ 0 ∧ 0 < ε ∧
        (∀ i, Measurable (g i)) ∧ (∀ i, ∃ C, ∀ x, |g i x| ≤ C) ∧
        ∀ R : Measure (Fin n → 𝓧), IsProbabilityMeasure R →
          (∀ i, |∫ x, g i x ∂R - ∫ x, g i x ∂(Measure.pi fun _ : Fin n ↦ Q)| ≤ ε) →
          ∀ P ∈ S, (n : EReal) * (klInf Q S - η) ≤
            ((klDiv R (Measure.pi fun _ : Fin n ↦ P) : ℝ≥0∞) : EReal) := by
  have hK0 : 0 ≤ klInf Q S := klInf_nonneg fun P hP ↦ by simp [(hS P hP).measure_univ]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, (K : EReal) = klInf Q S :=
    ⟨(klInf Q S).toReal, EReal.coe_toReal hQS (ne_bot_of_le_ne_bot EReal.zero_ne_bot hK0)⟩
  rw [← hK]
  constructor
  · -- a block length `n + 1` and a neighbourhood whose envelope is above `(n + 1) (K - η)`
    intro hd η hη
    have hlt : ((K - η : ℝ) : EReal) < bipolarRate Q S := by
      rw [hd]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    rw [bipolarRate_eq_iSup_tauEnvelope_div Q S hS, lt_iSup_iff] at hlt
    obtain ⟨n, hn⟩ := hlt
    rw [EReal.lt_div_iff (by exact_mod_cast Nat.succ_pos n) (EReal.natCast_ne_top _),
      lt_tauEnvelope_iff] at hn
    obtain ⟨k, g, hg, hgb, ε, hε, hlt⟩ := hn
    refine ⟨n + 1, k, g, ε, n.succ_ne_zero, hε, hg, hgb, fun R hR hRg P hP ↦ ?_⟩
    have := hS P hP
    have h := (hlt.le.trans (tauNbhdInf_le hR hRg)).trans
      (klInf_le_klIntegral (pi_mem_sampleNull (n := n + 1) hP))
    rw [klIntegral_eq_klDiv (by simp)] at h
    rw [mul_comm, ← EReal.coe_sub]
    exact h
  · -- the envelope of blocks of length `n` is above `n c` for every `c < K`
    intro h
    refine le_antisymm (hK ▸ bipolarRate_le_klInf Q hS) ?_
    refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
    induction c using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hc not_top_lt
    | coe c =>
      have hη : 0 < K - c := by rw [EReal.coe_lt_coe_iff] at hc; linarith
      obtain ⟨n, k, g, ε, hn, hε, hg, hgb, hR⟩ := h (K - c) hη
      have hle : (n : EReal) * (c : EReal) ≤
          tauEnvelope (fun R ↦ klInf R (sampleNull S n)) (Measure.pi fun _ : Fin n ↦ Q) := by
        refine le_trans (le_tauNbhdInf_iff.2 fun R hR' hRg ↦ ?_)
          (tauNbhdInf_le_tauEnvelope hg hgb hε)
        refine le_klInf_iff.2 fun μ hμ ↦ ?_
        obtain ⟨P, hP, rfl⟩ := mem_sampleNull.1 hμ
        have := hS P hP
        rw [klIntegral_eq_klDiv (by simp)]
        have h' := hR R hR' hRg P hP
        rwa [← EReal.coe_sub, sub_sub_cancel] at h'
      have h1 := (EReal.div_le_iff_le_mul (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (EReal.natCast_ne_top _)).2 (hle.trans (tauEnvelope_le_mul_bipolarRate Q S hS hn))
      have hn0 : ((n : ℕ) : EReal) ≠ 0 := by exact_mod_cast hn
      rwa [mul_comm, ← EReal.mul_div_right, EReal.div_mul_cancel (EReal.natCast_ne_bot _)
        (EReal.natCast_ne_top _) hn0] at h1

end ProbabilityTheory
