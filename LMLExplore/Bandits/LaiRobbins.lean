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

* `isConsistent_of_eventually_le_mul_log`: an algorithm whose expected regret on every bandit of a
  class is `O(log n)` is consistent over that class.
* `eventually_mul_log_le_integral_pullCount_of_klDiv`: the lower bound on the number of pulls of
  an arm given one alternative bandit `ν'` in the class.
* `eventually_mul_log_le_integral_pullCount_of_isConsistent`: [LS, Theorem 16.2] for the numbers
  of pulls, `liminf_n E[T_a(n)] / log n ≥ 1 / d_inf(ν_a, μ*, M_a)`.
* `eventually_mul_log_le_integral_regret_of_isConsistent`: [LS, Theorem 16.2],
  `liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d_inf(ν_a, μ*, M_a)`.
* `setOf_forall_mem_range_eq_range`: the unstructured class built from a family of laws is the
  range of the corresponding parametrized bandits, such as `gaussianBandit` or `bernoulliBandit`.
* `dInf_range_gaussianReal`: `d_inf` for Gaussian laws with known variance `σ²` is
  `(m - μ)² / (2 σ²)` [LS, Table 16.1].
* `eventually_mul_log_le_integral_regret_gaussianBandit`: the Lai–Robbins lower bound for Gaussian
  bandits with variance `σ²`, `liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
* `dInf_range_bernoulliMeasure`: `d_inf` for Bernoulli laws is the binary relative entropy
  `d(p, m)` for `p ≤ m < 1` [LS, Table 16.1]; `dInf_range_bernoulliMeasure_of_one_le`: it is `∞`
  for `m ≥ 1`.
* `eventually_mul_log_le_integral_regret_bernoulliBandit`: the Lai–Robbins lower bound for
  Bernoulli bandits, `liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 16.
* T. L. Lai and H. Robbins, *Asymptotically efficient adaptive allocation rules*, Advances in
  Applied Mathematics, 1985.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Finset Real Learning Bandits
open scoped ENNReal NNReal Topology unitInterval

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

/-- Consistency over a class of bandits implies consistency over every subclass. -/
lemma IsConsistent.mono {alg : Algorithm Unit α ℝ} {E E' : Set (Kernel α ℝ)}
    (h : IsConsistent alg E) (hE : E' ⊆ E) : IsConsistent alg E' :=
  fun ν hν ↦ h ν (hE hν)

/-- An algorithm whose expected regret on every bandit of `E` is eventually at most a multiple of
`log n` is consistent over `E`. -/
lemma isConsistent_of_eventually_le_mul_log [Finite α] {alg : Algorithm Unit α ℝ}
    {E : Set (Kernel α ℝ)}
    (h : ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∃ c : ℝ, ∀ᶠ n : ℕ in atTop,
      ∫ ω, regret ν IT.action n ω ∂(trajMeasure alg (stationaryEnv ν)) ≤ c * log n) :
    IsConsistent alg E := by
  intro ν hν _ p hp
  obtain ⟨c, hc⟩ := h ν hν
  -- `c log n / n ^ p → 0`, and the regret is nonnegative.
  have hlog : Tendsto (fun n : ℕ ↦ c * (log n / (n : ℝ) ^ p)) atTop (𝓝 0) := by
    simpa using ((isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul c
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    (.of_forall fun n ↦ div_nonneg (integral_nonneg fun _ ↦ regret_nonneg) (by positivity)) ?_
  filter_upwards [hc] with n hn
  rw [mul_div_assoc']
  gcongr

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

/-- The unstructured class of the bandits whose arms all have laws in the range of a family `f` of
laws is the range of a parametrization `κ` of the bandits `a ↦ f (x a)`. -/
lemma setOf_forall_mem_range_eq_range {X : Type*} {f : X → Measure ℝ}
    {κ : (α → X) → Kernel α ℝ} (hκ : ∀ x a, κ x a = f (x a)) :
    {ν : Kernel α ℝ | ∀ a, ν a ∈ Set.range f} = Set.range κ := by
  ext ν
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose x hx using h
    exact ⟨x, Kernel.ext fun a ↦ (hκ x a).trans (hx a)⟩
  · rintro ⟨x, rfl⟩ a
    exact ⟨x a, (hκ x a).symm⟩

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
    · -- `D(ν a, Q) < (ofReal c)⁻¹` is `ofReal c * D(ν a, Q) < 1`, then take `toReal`.
      have h1 : ENNReal.ofReal c * klDiv (ν a) Q < 1 := by
        rwa [mul_comm, ← ENNReal.lt_div_iff_mul_lt (by simp [hc0]) (by simp), one_div]
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le] using
        ENNReal.toReal_lt_of_lt_ofReal (h1.trans_eq ENNReal.ofReal_one.symm)
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
  have hE : {ν : Kernel α ℝ | ∀ a, ν a ∈ M a} = Set.range fun μ ↦ gaussianBandit μ σ2 :=
    setOf_forall_mem_range_eq_range (gaussianBandit_apply · σ2)
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

section Bernoulli

variable {p : I} {m : ℝ}

/-- **`d_inf` for Bernoulli laws** [LS, Table 16.1]: among the Bernoulli laws on `{0, 1}`, the
infimum of the relative entropies from `Ber(p)` to the laws with a mean above `m ∈ [p, 1)` is the
binary relative entropy `d(p, m)`. -/
lemma dInf_range_bernoulliMeasure (hpm : (p : ℝ) ≤ m) (hm : m < 1) :
    dInf (Set.range fun q : I ↦ Ber((1 : ℝ), 0, q)) Ber((1 : ℝ), 0, p) m = klBer p m := by
  refine le_antisymm ?_ (le_dInf_iff.mpr ?_)
  · -- `d(p, q) → d(p, m)` as `q → m` from above, and `d_inf ≤ d(p, q)` for `q ∈ (m, 1)`.
    have h_tendsto : Tendsto (klBer p) (𝓝[>] m) (𝓝 (klBer p m)) := by
      rcases (p.2.1.trans hpm).eq_or_lt with hm0 | hm0
      · -- If `m = 0`, then `p = 0` and `d(0, q) ≤ q / (1 - q)` for `q ∈ (0, 1)`.
        have hp : (p : ℝ) = 0 := le_antisymm (hm0 ▸ hpm) p.2.1
        subst hm0
        rw [hp, klBer_self]
        have h_lim : Tendsto (fun q : ℝ ↦ ENNReal.ofReal (q / (1 - q))) (𝓝[>] 0) (𝓝 0) := by
          have : ContinuousAt (fun q : ℝ ↦ ENNReal.ofReal (q / (1 - q))) 0 :=
            ENNReal.continuous_ofReal.continuousAt.comp
              (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num))
          simpa using this.tendsto.mono_left nhdsWithin_le_nhds
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
          (.of_forall fun _ ↦ bot_le) ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with q hq
        have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
        calc klBer 0 q ≤ ENNReal.ofReal ((0 - q) ^ 2 / (q * (1 - q))) :=
              klBer_le_ofReal_sq_sub_div (by simp) hq
          _ = ENNReal.ofReal (q / (1 - q)) := by
            rw [zero_sub, neg_sq]
            congr 1
            field_simp [hq.1.ne']
      · -- If `m ∈ (0, 1)`, then `d(p, ·)` is continuous at `m`.
        have hcont : ContinuousOn (klBer p) (Set.Ioo 0 1) :=
          continuousOn_klBer.comp (continuous_const.prodMk continuous_id).continuousOn
            fun q hq ↦ ⟨p.2, hq⟩
        exact ((hcont.continuousAt (Ioo_mem_nhds hm0 hm)).tendsto).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [Ioo_mem_nhdsGT hm] with q hq
    have hqI : q ∈ Set.Icc (0 : ℝ) 1 := ⟨(p.2.1.trans hpm).trans hq.1.le, hq.2.le⟩
    calc dInf _ _ m ≤ klDiv Ber((1 : ℝ), 0, p) Ber((1 : ℝ), 0, ⟨q, hqI⟩) :=
          dInf_le (Set.mem_range_self (f := fun q : I ↦ Ber((1 : ℝ), 0, q)) ⟨q, hqI⟩)
            (by simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using hq.1)
      _ = klBer p q := klDiv_bernoulliMeasure p ⟨q, hqI⟩
  · -- `d(p, ·)` is monotone on `[p, 1]`.
    rintro _ ⟨q, rfl⟩ hq
    have hq' : m < q := by simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using hq
    rw [klDiv_bernoulliMeasure]
    exact monotoneOn_klBer p hpm (hpm.trans hq'.le) hq'.le

/-- **`d_inf` for Bernoulli laws** [LS, Table 16.1]: no Bernoulli law on `{0, 1}` has a mean above
`m ≥ 1`, so that `d_inf(P, m)` is `∞` for every law `P`. -/
lemma dInf_range_bernoulliMeasure_of_one_le (P : Measure ℝ) (hm : 1 ≤ m) :
    dInf (Set.range fun q : I ↦ Ber((1 : ℝ), 0, q)) P m = ∞ := by
  refine top_le_iff.mp (le_dInf_iff.mpr ?_)
  rintro _ ⟨q, rfl⟩ hq
  have hq' : m < q := by simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using hq
  exact absurd (hm.trans_lt hq') (not_lt.mpr q.2.2)

variable {p : α → I}

/-- **Lai–Robbins lower bound for Bernoulli bandits** [LS, Theorem 16.2 and Table 16.1]: if `alg`
is consistent over the Bernoulli bandits, then on each of them, with `μ* = max_b p_b`,
`liminf_n E[R_n] / log n ≥ ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`: for every `c` below that sum,
eventually `c log n ≤ E[R_n]`. The terms are computed from the real number `d(p_a, μ*).toReal`,
which is `0` when `d(p_a, μ*) = ∞`, that is, when `μ* = 1`: such terms are then `0`. -/
theorem eventually_mul_log_le_integral_regret_bernoulliBandit [Fintype α]
    (halg : IsConsistent alg (Set.range fun p : α → I ↦ bernoulliBandit p)) (p : α → I)
    {c : ℝ} (hc : c < ∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
      gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤ ∫ ω, regret (bernoulliBandit p) IT.action n ω
      ∂(trajMeasure alg (stationaryEnv (bernoulliBandit p))) := by
  set ν := bernoulliBandit p
  set S := univ.filter (fun a ↦ 0 < gap ν a)
  set μs := ⨆ b, (p b : ℝ)
  rcases le_or_gt c 0 with hc0 | hc0
  · exact .of_forall fun n ↦ (mul_nonpos_of_nonpos_of_nonneg hc0 (log_natCast_nonneg n)).trans
      (integral_nonneg fun _ ↦ regret_nonneg)
  -- The Bernoulli bandits form the unstructured class of the Bernoulli laws.
  set M : α → Set (Measure ℝ) := fun _ ↦ Set.range fun q : I ↦ Ber((1 : ℝ), 0, q)
  have hE : {ν : Kernel α ℝ | ∀ a, ν a ∈ M a} = Set.range fun p ↦ bernoulliBandit p :=
    setOf_forall_mem_range_eq_range bernoulliBandit_apply
  refine eventually_mul_log_le_integral_regret_of_isConsistent (M := M)
    (fun _ _ ⟨q, hq⟩ ↦ hq ▸ inferInstance) (hE ▸ halg)
    (fun a ↦ ⟨p a, (bernoulliBandit_apply p a).symm⟩) ?_
  -- The Lai–Robbins constant is `∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`.
  have hterm : ∀ a ∈ S, ENNReal.ofReal (gap ν a) / dInf (M a) (ν a) (⨆ b, (ν b)[id]) =
      ENNReal.ofReal (gap ν a / (klBer (p a) μs).toReal) := fun a ha ↦ by
    have : Nonempty α := ⟨a⟩
    have hgap : 0 < gap ν a := (mem_filter.mp ha).2
    have hμs : (⨆ b, (ν b)[id]) = μs := by simp_rw [ν, integral_id_bernoulliBandit, μs]
    have hgap_eq : gap ν a = μs - p a := by rw [gap, hμs, integral_id_bernoulliBandit]
    have hpa : (p a : ℝ) < μs := by linarith
    have hμs1 : μs ≤ 1 := ciSup_le fun b ↦ (p b).2.2
    rw [bernoulliBandit_apply, hμs]
    rcases hμs1.lt_or_eq with hlt | heq
    · -- If `μ* < 1`, then `d(p_a, μ*)` is finite and positive.
      have hμsI : μs ∈ Set.Ioo 0 1 := ⟨(p a).2.1.trans_lt hpa, hlt⟩
      have hne_top := klBer_ne_top (p := p a) hμsI
      have hpos : 0 < (klBer (p a) μs).toReal := ENNReal.toReal_pos
        (fun h ↦ hpa.ne ((klBer_eq_zero_iff (p a).2 (Set.Ioo_subset_Icc_self hμsI)).mp h))
        hne_top
      rw [dInf_range_bernoulliMeasure hpa.le hlt, ENNReal.ofReal_div_of_pos hpos,
        ENNReal.ofReal_toReal hne_top]
    · -- If `μ* = 1`, then `d_inf = d(p_a, 1) = ∞` and both sides vanish.
      have htop : klBer (p a) μs = ∞ :=
        (klBer_eq_top_iff (p a).2 (by simp [heq])).mpr (Or.inr ⟨heq, (heq ▸ hpa).ne⟩)
      rw [dInf_range_bernoulliMeasure_of_one_le _ heq.ge, htop, ENNReal.div_top,
        ENNReal.toReal_top, div_zero, ENNReal.ofReal_zero]
  rw [sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ div_nonneg gap_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_lt_ofReal_iff (hc0.trans hc)]
  exact hc

end Bernoulli

end LMLExplore.Bandits
