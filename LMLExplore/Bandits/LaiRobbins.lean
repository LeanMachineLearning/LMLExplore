/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.MinimaxLowerBound

/-!
# The Lai–Robbins lower bound

An algorithm is consistent over a class `E` of bandits if its expected regret on every bandit of
`E` is `o(n ^ p)` for every `p > 0` [LS, Definition 16.1]. The Lai–Robbins lower bound
[LS, Theorem 16.2] states that a consistent algorithm cannot do much better than logarithmic regret
on any bandit of an unstructured class `E = ∏_a M_a`, where `M_a` is a set of laws on `ℝ`: for
`ν ∈ E`, with `μ*` the largest mean of `ν`,
`liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d_inf(ν_a, μ*, M_a)`, where
`d_inf(P, m, M) = inf {D(P, Q) : Q ∈ M, mean(Q) > m}`.

The proof compares `ν` with the bandit `ν'` in which the law of a suboptimal arm `a` is replaced by
a law `Q ∈ M_a` with mean above `μ*`, which makes `a` the unique optimal arm. The divergence
decomposition bounds the relative entropy between the laws of the histories of the first `n`
rounds by `E_ν[T_a(n)] D(ν_a, Q)`. The Bretagnolle–Huber inequality, through the two-bandit
inequality `le_integral_regret_add_integral_regret'`, bounds the sum of the regrets on `ν` and
`ν'` from below by `Δ n exp (-E_ν[T_a(n)] D(ν_a, Q)) / 2`, while consistency bounds it from above
by `o(n ^ p)` for every `p > 0`. Hence `E_ν[T_a(n)] D(ν_a, Q) ≥ (1 - p) log n` eventually.

Asymptotic statements are in eventual form: `liminf_n u_n / log n ≥ C` is
`∀ c < C, ∀ᶠ n in atTop, c log n ≤ u_n`. The constants are in `ℝ≥0∞`: `d_inf` is `∞` when no law
of `M_a` has a mean above `μ*`, and `Δ_a / d_inf` is `∞` when `d_inf` vanishes, in which case the
regret of a consistent algorithm eventually exceeds every multiple of `log n`.

Means are Bochner integrals `Q[id]`, as in LML's `gap` and `regret`; the statements need no
integrability assumption.

## Main definitions

* `LMLExplore.Bandits.IsConsistent alg E`: the algorithm `alg` is consistent over the class `E`.
* `LMLExplore.Bandits.dInf M P m`: `d_inf(P, m, M)`.

## Main statements

* `eventually_mul_log_le_integral_pullCount_of_klDiv`: the lower bound on the number of pulls of
  an arm given one alternative bandit `ν'` in the class.
* `eventually_mul_log_le_integral_pullCount_of_isConsistent`: [LS, Theorem 16.2] for the numbers
  of pulls, `liminf_n E[T_a(n)] / log n ≥ 1 / d_inf(ν_a, μ*, M_a)`.
* `eventually_mul_log_le_integral_regret_of_isConsistent`: [LS, Theorem 16.2],
  `liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d_inf(ν_a, μ*, M_a)`.
* `dInf_range_gaussianReal`: `d_inf` for Gaussian laws with known variance `σ²` is
  `(m - μ)² / (2 σ²)` [LS, Table 16.1].
* `eventually_mul_log_le_integral_regret_gaussianBandit`: the Lai–Robbins lower bound for Gaussian
  bandits with variance `σ²`, `liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 16.
* T. L. Lai and H. Robbins, *Asymptotically efficient adaptive allocation rules*, Advances in
  Applied Mathematics, 1985.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Finset Real Learning Bandits
open scoped ENNReal NNReal Topology

namespace LMLExplore.Bandits

variable {α : Type*} [MeasurableSpace α]

section Defs

/-- An algorithm `alg` is **consistent** over a class `E` of bandits if, for every Markov kernel
`ν ∈ E`, its expected regret on the stationary bandit `ν` is `o(n ^ p)` for every `p > 0`
[LS, Definition 16.1]. -/
def IsConsistent (alg : Algorithm Unit α ℝ) (E : Set (Kernel α ℝ)) : Prop :=
  ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ p : ℝ, 0 < p →
    Tendsto (fun n : ℕ ↦ (∫ ω, regret ν IT.action n ω ∂(trajMeasure alg (stationaryEnv ν))) /
      (n : ℝ) ^ p) atTop (𝓝 0)

lemma isConsistent_def (alg : Algorithm Unit α ℝ) (E : Set (Kernel α ℝ)) :
    IsConsistent alg E ↔ ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ p : ℝ, 0 < p →
      Tendsto (fun n : ℕ ↦ (∫ ω, regret ν IT.action n ω ∂(trajMeasure alg (stationaryEnv ν))) /
        (n : ℝ) ^ p) atTop (𝓝 0) :=
  Iff.rfl

/-- `d_inf(P, m, M)`: the infimum of the relative entropies `D(P, Q)` from `P` to the laws `Q ∈ M`
whose mean `Q[id]` exceeds `m` [LS, §16.1]. It is `∞` if no law of `M` has a mean above `m`. -/
noncomputable def dInf (M : Set (Measure ℝ)) (P : Measure ℝ) (m : ℝ) : ℝ≥0∞ :=
  ⨅ Q ∈ {Q ∈ M | m < Q[id]}, klDiv P Q

variable {M : Set (Measure ℝ)} {P Q : Measure ℝ} {m : ℝ} {x : ℝ≥0∞}

lemma dInf_def (M : Set (Measure ℝ)) (P : Measure ℝ) (m : ℝ) :
    dInf M P m = ⨅ Q ∈ {Q ∈ M | m < Q[id]}, klDiv P Q :=
  (rfl)

lemma dInf_le (hQ : Q ∈ M) (hm : m < Q[id]) : dInf M P m ≤ klDiv P Q := by
  rw [dInf_def]
  exact biInf_le _ ⟨hQ, hm⟩

lemma le_dInf_iff : x ≤ dInf M P m ↔ ∀ Q ∈ M, m < Q[id] → x ≤ klDiv P Q := by
  simp [dInf_def, and_imp]

lemma dInf_lt_iff : dInf M P m < x ↔ ∃ Q ∈ M, m < Q[id] ∧ klDiv P Q < x := by
  simp [dInf_def, iInf_lt_iff, and_assoc]

end Defs

variable [Finite α] [StandardBorelSpace α] {alg : Algorithm Unit α ℝ}
  {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Lower bound on the number of pulls from one alternative bandit**, the core of the
Lai–Robbins lower bound. Let `alg` be consistent over a class containing `ν` and `ν'`, where `ν'`
agrees with `ν` outside an arm `a` with positive gap in `ν`, and the mean of `ν' a` exceeds every
mean of `ν`. If `D(ν a, ν' a)` is finite, then `liminf_n E_ν[T_a(n)] / log n ≥ 1 / D(ν a, ν' a)`:
for every real `c` with `c D(ν a, ν' a) < 1`, eventually `c log n ≤ E_ν[T_a(n)]`. -/
theorem eventually_mul_log_le_integral_pullCount_of_klDiv [DecidableEq α] {E : Set (Kernel α ℝ)}
    (halg : IsConsistent alg E) {ν' : Kernel α ℝ} [IsMarkovKernel ν'] (hν : ν ∈ E)
    (hν' : ν' ∈ E) {a : α} (hνν' : ∀ b ≠ a, ν b = ν' b) (ha : 0 < gap ν a)
    (hmean : (⨆ b, (ν b)[id]) < (ν' a)[id]) (hD : klDiv (ν a) (ν' a) ≠ ∞) {c : ℝ}
    (hc : c * (klDiv (ν a) (ν' a)).toReal < 1) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, (pullCount IT.action a n ω : ℝ) ∂(trajMeasure alg (stationaryEnv ν)) := by
  set D := (klDiv (ν a) (ν' a)).toReal
  have hrun := IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)
  have hrun' := IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν')
  -- In `ν` the arm `a` has gap at least `Δ`, and in `ν'` every other arm has gap at least `Δ`.
  set Δ := min (gap ν a) ((ν' a)[id] - ⨆ b, (ν b)[id])
  have hΔ : 0 < Δ := lt_min ha (sub_pos.mpr hmean)
  have hgap' : ∀ b ≠ a, Δ ≤ gap ν' b := fun b hb ↦ by
    have h1 := sub_le_gap ν' b a
    have h2 : (ν b)[id] ≤ ⨆ b, (ν b)[id] :=
      le_ciSup (f := fun b ↦ (ν b)[id]) (Set.finite_range _).bddAbove b
    rw [← hνν' b hb] at h1
    exact (min_le_right _ _).trans (by linarith)
  -- By consistency, both regrets are eventually at most `Δ n ^ p / 8`, for `p = 1 - c D > 0`.
  set p := 1 - c * D
  have hp : 0 < p := sub_pos.mpr hc
  have hR := (tendsto_order.mp (halg ν hν p hp)).2 (Δ / 8) (by positivity)
  have hR' := (tendsto_order.mp (halg ν' hν' p hp)).2 (Δ / 8) (by positivity)
  filter_upwards [hR, hR', eventually_ge_atTop 1] with n hRn hR'n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) ^ p := rpow_pos_of_pos hn0 p
  rw [div_lt_iff₀ hnp] at hRn hR'n
  -- The relative entropy `K` between the laws of the histories is at most `E_ν[T_a(n)] D`.
  set T := ∫ ω, (pullCount IT.action a n ω : ℝ) ∂(trajMeasure alg (stationaryEnv ν))
  have hT : 0 ≤ T := integral_nonneg fun _ ↦ Nat.cast_nonneg _
  have hKL := hrun.klDiv_map_history_le_ofReal_integral_pullCount_mul hrun' hνν'
    (ENNReal.ofReal_toReal hD).ge n
  have htwo := le_integral_regret_add_integral_regret' hrun hrun' hΔ.le (min_le_left _ _) hgap'
    n (hKL.trans_lt ENNReal.ofReal_lt_top).ne
  generalize klDiv _ _ = K at hKL htwo
  have hK : K.toReal ≤ T * D := ENNReal.toReal_le_of_le_ofReal (by positivity) hKL
  -- The two-bandit inequality gives `n exp (-T D) < n ^ p / 2`, hence `c D log n + log 2 < T D`.
  have h1 : Δ * (n * exp (-(T * D))) < Δ * ((n : ℝ) ^ p / 2) := by
    have h2 : Δ * n * exp (-(T * D)) ≤ Δ * n * exp (-K.toReal) := by gcongr
    linarith
  have hlog := log_lt_log (by positivity) (lt_of_mul_lt_mul_left h1 hΔ.le)
  rw [log_mul hn0.ne' (exp_pos _).ne', log_exp, log_div hnp.ne' two_ne_zero,
    log_rpow hn0] at hlog
  have hTD : c * D * log n + log 2 < T * D := by linarith
  -- If `D = 0` this is impossible, and otherwise it gives `c log n < T`.
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ D from ENNReal.toReal_nonneg) with h0 | h0
  · simp only [← h0, mul_zero, zero_mul, zero_add] at hTD
    exact absurd hTD (not_lt.mpr (log_nonneg one_le_two))
  · have : c * log n * D < T * D := by linarith [log_pos one_lt_two]
    exact (lt_of_mul_lt_mul_right this h0.le).le

variable {M : α → Set (Measure ℝ)}

/-- **Lai–Robbins lower bound on the numbers of pulls** [LS, Theorem 16.2]. Let `M a` be a set of
probability laws on `ℝ` for every arm `a`, and let `alg` be consistent over the unstructured class
of the bandits `ν` with `ν a ∈ M a` for every arm `a`. For a bandit `ν` of that class and an arm
`a` with positive gap, `liminf_n E_ν[T_a(n)] / log n ≥ 1 / d_inf(ν a, μ*, M a)`, where `μ*` is the
largest mean of `ν`: for every real `c < 1 / d_inf(ν a, μ*, M a)`, eventually
`c log n ≤ E_ν[T_a(n)]`. -/
theorem eventually_mul_log_le_integral_pullCount_of_isConsistent [DecidableEq α]
    (hM : ∀ a, ∀ Q ∈ M a, IsProbabilityMeasure Q) (halg : IsConsistent alg {ν | ∀ a, ν a ∈ M a})
    (hν : ∀ a, ν a ∈ M a) {a : α} (ha : 0 < gap ν a) {c : ℝ}
    (hc : ENNReal.ofReal c < (dInf (M a) (ν a) (⨆ b, (ν b)[id]))⁻¹) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, (pullCount IT.action a n ω : ℝ) ∂(trajMeasure alg (stationaryEnv ν)) := by
  -- An alternative law `Q ∈ M a` with mean above `μ*` and `c D(ν a, Q) < 1`.
  obtain ⟨Q, hQM, hQmean, hQ⟩ := dInf_lt_iff.mp (ENNReal.lt_inv_iff_lt_inv.mp hc)
  have hD : klDiv (ν a) Q ≠ ∞ := ne_top_of_lt hQ
  have hcD : c * (klDiv (ν a) Q).toReal < 1 := by
    rcases le_or_gt c 0 with hc0 | hc0
    · nlinarith [ENNReal.toReal_nonneg (a := klDiv (ν a) Q)]
    · rw [← ENNReal.ofReal_toReal hD, ENNReal.ofReal_inv_of_pos hc0 |>.symm,
        ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hc0)] at hQ
      have := mul_lt_mul_of_pos_left hQ hc0
      rwa [mul_inv_cancel₀ hc0.ne'] at this
  -- The bandit `ν'` in which the law of the arm `a` is replaced by `Q`.
  have : IsProbabilityMeasure Q := hM a Q hQM
  have hupd : ∀ b, IsProbabilityMeasure (Function.update (fun b ↦ ν b) a Q b) := fun b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hb]
      infer_instance
  set ν' := Kernel.ofFunOfCountable (Function.update (fun b ↦ ν b) a Q)
  have hν'a : ν' a = Q := by simp [ν']
  have hν' : ∀ b ≠ a, ν b = ν' b := fun b hb ↦ by simp [ν', Function.update_of_ne hb]
  have hν'M : ν' ∈ {ν | ∀ a, ν a ∈ M a} := fun b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rwa [hν'a]
    · rw [← hν' b hb]
      exact hν b
  rw [← hν'a] at hQmean hD hcD
  exact eventually_mul_log_le_integral_pullCount_of_klDiv halg hν hν'M hν' ha hQmean hD hcD

/-- **Lai–Robbins lower bound** [LS, Theorem 16.2]. Let `M a` be a set of probability laws on `ℝ`
for every arm `a`, and let `alg` be consistent over the unstructured class of the bandits `ν` with
`ν a ∈ M a` for every arm `a`. For a bandit `ν` of that class, with largest mean `μ*`,
`liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d_inf(ν a, μ*, M a)`: for every real `c` below
that sum in `ℝ≥0∞`, eventually `c log n ≤ E[R_n]`. -/
theorem eventually_mul_log_le_integral_regret_of_isConsistent [Fintype α]
    (hM : ∀ a, ∀ Q ∈ M a, IsProbabilityMeasure Q) (halg : IsConsistent alg {ν | ∀ a, ν a ∈ M a})
    (hν : ∀ a, ν a ∈ M a) {c : ℝ}
    (hc : ENNReal.ofReal c < ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      ENNReal.ofReal (gap ν a) / dInf (M a) (ν a) (⨆ b, (ν b)[id])) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, regret ν IT.action n ω ∂(trajMeasure alg (stationaryEnv ν)) := by
  classical
  simp_rw [div_eq_mul_inv] at hc
  exact eventually_le_integral_regret_of_forall_eventually_le_integral_pullCount
    (IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)).measurable_action
    (.of_forall log_natCast_nonneg) _
    (fun a ha c hc ↦ eventually_mul_log_le_integral_pullCount_of_isConsistent hM halg hν ha hc) hc

/-- If `d_inf(ν a, μ*, M a) = 0` for an arm `a` with positive gap, then the regret of an algorithm
that is consistent over the unstructured class eventually exceeds every multiple of `log n`: the
Lai–Robbins constant is `∞`. -/
theorem eventually_mul_log_le_integral_regret_of_dInf_eq_zero
    (hM : ∀ a, ∀ Q ∈ M a, IsProbabilityMeasure Q) (halg : IsConsistent alg {ν | ∀ a, ν a ∈ M a})
    (hν : ∀ a, ν a ∈ M a) {a : α} (ha : 0 < gap ν a)
    (h0 : dInf (M a) (ν a) (⨆ b, (ν b)[id]) = 0) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, regret ν IT.action n ω ∂(trajMeasure alg (stationaryEnv ν)) := by
  have := Fintype.ofFinite α
  refine eventually_mul_log_le_integral_regret_of_isConsistent hM halg hν
    (ENNReal.ofReal_lt_top.trans_le ?_)
  calc ∞ = ENNReal.ofReal (gap ν a) / dInf (M a) (ν a) (⨆ b, (ν b)[id]) := by
        rw [h0, ENNReal.div_zero (ENNReal.ofReal_pos.mpr ha).ne']
    _ ≤ _ := single_le_sum (f := fun a ↦ ENNReal.ofReal (gap ν a) / dInf (M a) (ν a) _)
        (fun _ _ ↦ bot_le) (mem_filter.mpr ⟨mem_univ a, ha⟩)

section Gaussian

/-- **`d_inf` for Gaussian laws with known variance** [LS, Table 16.1]: among the Gaussian laws
with variance `σ² ≠ 0`, the infimum of the relative entropies from `𝒩(μ, σ²)` to the laws with a
mean above `m ≥ μ` is `(m - μ)² / (2 σ²)`. -/
lemma dInf_range_gaussianReal {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) {μ m : ℝ} (hμm : μ ≤ m) :
    dInf (Set.range fun x ↦ gaussianReal x σ2) (gaussianReal μ σ2) m =
      ENNReal.ofReal ((m - μ) ^ 2 / (2 * σ2)) := by
  have hkl (x : ℝ) : klDiv (gaussianReal μ σ2) (gaussianReal x σ2) =
      ENNReal.ofReal ((x - μ) ^ 2 / (2 * σ2)) := by
    rw [klDiv_gaussianReal_gaussianReal_same_var hσ2, sub_sq_comm]
  refine le_antisymm ?_ (le_dInf_iff.mpr ?_)
  · -- The relative entropies to `𝒩(x, σ²)` for `x > m` tend to `(m - μ)² / (2 σ²)` as `x → m`.
    have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal ((x - μ) ^ 2 / (2 * σ2))) (𝓝[>] m)
        (𝓝 (ENNReal.ofReal ((m - μ) ^ 2 / (2 * σ2)))) :=
      ((ENNReal.continuous_ofReal.comp (by fun_prop)).tendsto m).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto h_tendsto (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    rw [← hkl]
    exact dInf_le ⟨x, rfl⟩ (by simpa using hx)
  · rintro _ ⟨x, rfl⟩ hx
    have hx' : m < x := by simpa using hx
    dsimp only
    rw [hkl]
    gcongr

variable {σ2 : ℝ≥0} {μ : α → ℝ}

/-- **Lai–Robbins lower bound for Gaussian bandits** [LS, Theorem 16.2 and Table 16.1]: if `alg` is
consistent over the Gaussian bandits with variance `σ² ≠ 0`, then on each of them
`liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} 2 σ² / Δ_a`: for every `c` below that sum, eventually
`c log n ≤ E[R_n]`. -/
theorem eventually_mul_log_le_integral_regret_gaussianBandit [Fintype α] (hσ2 : σ2 ≠ 0)
    (halg : IsConsistent alg (Set.range fun μ : α → ℝ ↦ gaussianBandit μ σ2)) (μ : α → ℝ)
    {c : ℝ} (hc : c < ∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
      2 * σ2 / gap (gaussianBandit μ σ2) a) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤ ∫ ω, regret (gaussianBandit μ σ2) IT.action n ω
      ∂(trajMeasure alg (stationaryEnv (gaussianBandit μ σ2))) := by
  set ν := gaussianBandit μ σ2
  set S := univ.filter (fun a ↦ 0 < gap ν a)
  rcases le_or_gt c 0 with hc0 | hc0
  · exact .of_forall fun n ↦ (mul_nonpos_of_nonpos_of_nonneg hc0 (log_natCast_nonneg n)).trans
      (integral_nonneg fun _ ↦ regret_nonneg)
  -- The Gaussian bandits with variance `σ²` form the unstructured class of the Gaussian laws.
  set M : α → Set (Measure ℝ) := fun _ ↦ Set.range fun x ↦ gaussianReal x σ2
  have hE : {ν : Kernel α ℝ | ∀ a, ν a ∈ M a} = Set.range fun μ ↦ gaussianBandit μ σ2 := by
    ext κ
    refine ⟨fun h ↦ ?_, ?_⟩
    · choose μ' hμ' using h
      exact ⟨μ', Kernel.ext fun a ↦ by rw [gaussianBandit_apply]; exact hμ' a⟩
    · rintro ⟨μ', rfl⟩ a
      exact ⟨μ' a, (gaussianBandit_apply μ' σ2 a).symm⟩
  refine eventually_mul_log_le_integral_regret_of_isConsistent (M := M)
    (fun _ _ ⟨x, hx⟩ ↦ hx ▸ inferInstance) (hE ▸ halg)
    (fun a ↦ ⟨μ a, (gaussianBandit_apply μ σ2 a).symm⟩) ?_
  -- The Lai–Robbins constant is `∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
  have hterm : ∀ a ∈ S, ENNReal.ofReal (gap ν a) / dInf (M a) (ν a) (⨆ b, (ν b)[id]) =
      ENNReal.ofReal (2 * σ2 / gap ν a) := fun a ha ↦ by
    have hgap : 0 < gap ν a := (mem_filter.mp ha).2
    have hgap_eq : gap ν a = (⨆ b, (ν b)[id]) - μ a := by
      rw [gap, integral_id_gaussianBandit]
    have hσ : (0 : ℝ) < σ2 := by positivity
    rw [gaussianBandit_apply, dInf_range_gaussianReal hσ2 (by linarith), ← hgap_eq,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  rw [sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ div_nonneg (by positivity) gap_nonneg,
    ENNReal.ofReal_lt_ofReal_iff (hc0.trans hc)]
  exact hc

end Gaussian

end LMLExplore.Bandits
