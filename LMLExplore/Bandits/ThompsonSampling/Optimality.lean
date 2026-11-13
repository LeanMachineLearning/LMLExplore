/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Bandits.Regret
public import LMLExplore.Bandits.ThompsonSampling.Jeffreys
public import LMLExplore.Probability.Distributions.ExponentialFamily.Posterior.Odds
import LMLExplore.Analysis.SpecialFunctions.Exp

/-!
# Asymptotic optimality of Thompson sampling with the Jeffreys prior

Let every arm `a` have a natural exponential family `ρ a` on `ℝ`, with log-partition function
`ψ_a`, natural parameters `Θ_a` and divergence `d_a(μ, μ')` in the mean parametrization, and let
Thompson sampling sample the natural parameter of each arm from its posterior for the Jeffreys
prior `π_a` [KKM13]. By [LS, Theorem 36.2], for arms `i ≠ j`, a level `c` and every horizon `n`,
`E[T_i(n)] ≤ 1 + E[∑_{s < n} (1 / G_{j s} - 1)] + ∑_{s < n} P(G_{i s} > 1 / n)`, where `G_{a s}`
is the probability that the sampled mean of arm `a` after its first `s` rewards exceeds `c`. For
a suboptimal arm `i` of mean `μ_i < c`, the last sum is at most `log n / β + O(1)` for every
`β < d_i(μ_i, c)` (`ExpFamilyTS.exists_lintegral_pullCount_le_add_log`, through the posterior
concentration theorem [KKM13, Theorem 4]).

This file bounds the first sum, for an optimal arm `j` of mean `μ_j > c`, uniformly in `n`:
`1 / G_{j s} - 1` is the posterior odds of the means at most `c`, whose expectation decays
exponentially in `s` (`MeasureTheory.Measure.expFamilyPosterior_inv_sub_one_le`,
`ProbabilityTheory.iIndepFun.lintegral_exp_sub_le`) as soon as the prior `π_j` gives finite mass
to the natural parameters of the means at most `c`. Letting `c → μ_j` and `β → d_i(μ_i, μ_j)`,
`limsup_n E[T_i(n)] / log n ≤ 1 / d_i(μ_i, μ_j)`, and the regret of Thompson sampling with the
Jeffreys prior satisfies `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_a(μ_a, μ*)`: the
upper bound of [KKM13, Theorem 1], which matches the Lai–Robbins lower bound.

The finiteness of the Jeffreys prior on the natural parameters of the means below `μ*` is a
hypothesis. It holds for Bernoulli arms, whose Jeffreys prior is finite, and for Poisson arms,
whose Jeffreys prior `√r e^{θ / 2} dθ` is finite on every half-line `(-∞, θ]`. It fails for
exponential arms, whose Jeffreys prior `dλ / λ` on the rate `λ` gives infinite mass to the large
rates, that is, to the small means: then, after one observation `S` of the optimal arm, the
posterior of the rate is the exponential law of rate `S`, `G_{j 1} = 1 - exp (-S / c)` is of order
`S` for small `S`, and `E[1 / G_{j 1}]` is infinite, so the bound of [LS, Theorem 36.2] gives
nothing. Gaussian arms, whose Jeffreys prior is a multiple of Lebesgue measure, are treated
separately by `gaussianTS_regret_eventually_le`, through the explicit Gaussian posteriors.

## Main statements

* `LMLExplore.Bandits.inv_expFamilyTSStackLaw_Ioi_sub_one_le`: whatever the number of pulls and
  the sum of rewards of an arm, `1 / G - 1` is at most the bound on the posterior odds of
  `MeasureTheory.Measure.expFamilyPosterior_inv_sub_one_le`.
* `ProbabilityTheory.iIndepFun.exists_sum_lintegral_inv_expFamilyTSStackLaw_Ioi_sub_one_le`: for
  independent observations dominated on `Set.Iic 0` by the member of mean `μ > c`, and a prior
  that gives finite mass to the natural parameters of the means at most `c` and positive mass to
  every interval of natural parameters, `∑_{s < n} E[1 / G_s - 1]` is bounded uniformly in `n`.
* `LMLExplore.Bandits.exists_sum_lintegral_streamMeasure_inv_expFamilyTSStackLaw_Ioi_sub_one_le`:
  the same bound in the reward-stack model of a stochastic bandit.
* `LMLExplore.Bandits.ExpFamilyTS.exists_lintegral_pullCount_le_log_div_add`: for Thompson
  sampling with the Jeffreys priors, `E[T_i(n)] ≤ log n / β + C` for every `β < d_i(μ_i, c)`.
* `LMLExplore.Bandits.ExpFamilyTS.integral_pullCount_eventually_le`: for every
  `c > 1 / d_a(μ_a, μ_b)`, eventually `E[T_a(n)] ≤ c log n`.
* `LMLExplore.Bandits.expFamilyTS_jeffreysPrior_regret_eventually_le`: [KKM13, Theorem 1], upper
  bound: for every `c > ∑_{a : Δ_a > 0} Δ_a / d_a(μ_a, μ*)`, eventually `E[R_n] ≤ c log n`.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013, Theorem 1.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 36.2.
-/

public section

open MeasureTheory ProbabilityTheory Set Learning Bandits Filter Topology LMLExplore
  LMLExplore.Bandits
open Real (exp log exp_pos exp_le_exp log_natCast_nonneg log_pos
  aemeasurable_of_aemeasurable_exp_mul eventually_lt_mul_log_of_tendsto_div_log
  tendsto_div_add_div_log)

open scoped ENNReal

namespace LMLExplore.Bandits

variable {ρ π : Measure ℝ} {a b c : ℝ}

/-- **Posterior odds in Thompson sampling.** Let `[a, b]` be an interval of natural parameters of
the natural exponential family of `ρ`, of positive mass for the prior `π`, whose means exceed the
level `c`. Whatever the number of pulls `s` and the sum of rewards `S` of an arm, the probability
`G` that its perturbation exceeds `c` satisfies
`1 / G - 1 ≤ π([a, b])⁻¹ ∫_{θ ∈ Θ, ψ'(θ) ≤ c} (exp (f(θ) - f(a)) + exp (f(θ) - f(b))) dπ(θ)`, with
`f(θ) = θ S - s ψ(θ)`: for a pulled arm with a proper posterior, `1 / G - 1` is the posterior odds
of the means at most `c`, and otherwise `G = 1`. -/
theorem inv_expFamilyTSStackLaw_Ioi_sub_one_le (hΘ : Icc a b ⊆ interior (integrableExpSet id ρ))
    (hc : c < deriv (cgf id ρ) a) (hπ : π (Icc a b) ≠ 0) (s : ℕ) (S : ℝ) :
    (expFamilyTSStackLaw ρ π s S (Ioi (c : EReal)))⁻¹ - 1 ≤
      (π (Icc a b))⁻¹ * ∫⁻ θ in interior (integrableExpSet id ρ) ∩ {θ | deriv (cgf id ρ) θ ≤ c},
        (ENNReal.ofReal (exp (θ * S - s * cgf id ρ θ - (a * S - s * cgf id ρ a))) +
          ENNReal.ofReal (exp (θ * S - s * cgf id ρ θ - (b * S - s * cgf id ρ b)))) ∂π := by
  by_cases h0 : s = 0 ∨ ρ.expFamilyPosterior id π s S = 0
  · have h1 : expFamilyTSStackLaw ρ π s S (Ioi (c : EReal)) = 1 := by
      rcases h0 with h0 | h0
      · rw [h0, expFamilyTSStackLaw_zero]
        simp
      · rw [expFamilyTSStackLaw_of_expFamilyPosterior_eq_zero h0]
        simp
    simp [h1]
  push Not at h0
  rw [expFamilyTSStackLaw_Ioi h0.1 h0.2]
  exact Measure.expFamilyPosterior_inv_sub_one_le hΘ hc hπ h0.2

end LMLExplore.Bandits

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}
  {ρ π : Measure ℝ} {μ c a b η k : ℝ}

/-- The expected posterior odds of the means at most `c` after `s` observations dominated on
`Set.Iic 0` by the member of natural parameter `η`, through an interval `[a, b] ⊆ (η(c), η]`
whose exponents `(η - e) (ψ'(e) - ψ'(η(c) + η - e))`, for `e ∈ {a, b}`, are at least `k`:
`E[1 / G_s - 1] ≤ π([a, b])⁻¹ π(ψ' ≤ c) 2 exp (-s k)`. -/
private lemma iIndepFun.lintegral_inv_expFamilyTSStackLaw_Ioi_sub_one_le [SFinite ρ] [SFinite π]
    (h_indep : iIndepFun X P)
    (hX : ∀ k, MGFDominatedOn (X k) P id (ρ.expFamily id η) (Iic 0))
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hc : c ∈ ρ.expFamilyMeans id)
    (hη : η ∈ interior (integrableExpSet id ρ)) (hIcc : Icc a b ⊆ interior (integrableExpSet id ρ))
    (hca : c < deriv (cgf id ρ) a) (hbη : b ≤ η) (hπ : π (Icc a b) ≠ 0)
    (hka : k ≤ (η - a) * (deriv (cgf id ρ) a - deriv (cgf id ρ) (ρ.natParam id c + η - a)))
    (hkb : k ≤ (η - b) * (deriv (cgf id ρ) b - deriv (cgf id ρ) (ρ.natParam id c + η - b)))
    (s : ℕ) :
    ∫⁻ ω, (expFamilyTSStackLaw ρ π s (∑ j ∈ Finset.range s, X j ω) (Ioi (c : EReal)))⁻¹ - 1 ∂P ≤
      (π (Icc a b))⁻¹ * π {θ | deriv (cgf id ρ) θ ≤ c} * (2 * ENNReal.ofReal (exp (-(s * k)))) := by
  have := h_indep.isProbabilityMeasure
  set Θ := interior (integrableExpSet (id : ℝ → ℝ) ρ)
  set ψ := cgf id ρ
  set θc := ρ.natParam id c
  have hθc : θc ∈ Θ := Measure.natParam_mem_interior_integrableExpSet hc
  have hΘ := (convex_integrableExpSet (X := (id : ℝ → ℝ)) (μ := ρ)).interior.ordConnected
  have hab : a ≤ b := nonempty_Icc.1 (nonempty_of_measure_ne_zero hπ)
  -- `η(c) < a`, since the mean at `a` exceeds `c`
  have hθca : θc < a := by
    by_contra! h
    have h' := monotoneOn_deriv_cgf (hIcc ⟨le_rfl, hab⟩) hθc h
    rw [Measure.deriv_cgf_natParam hc] at h'
    exact absurd hca (not_lt.2 h')
  have hmem (x : ℝ) (h1 : θc ≤ x) (h2 : x ≤ η) : x ∈ Θ := hΘ.out hθc hη ⟨h1, h2⟩
  -- the observations are almost everywhere measurable
  have hXm (j : ℕ) : AEMeasurable (X j) P := by
    have hY : Integrable (fun x ↦ exp ((θc - η) * id x)) (ρ.expFamily id η) := by
      change θc - η ∈ integrableExpSet id (ρ.expFamily id η)
      rw [Measure.integrableExpSet_expFamily (interior_subset hη), mem_preimage, add_sub_cancel]
      exact interior_subset hθc
    exact aemeasurable_of_aemeasurable_exp_mul (sub_ne_zero.2 (by linarith))
      ((hX j).integrable_exp_mul (sub_nonpos.2 (by linarith)) hY).aemeasurable
  have hS : AEMeasurable (fun ω ↦ ∑ j ∈ Finset.range s, X j ω) P :=
    Finset.aemeasurable_fun_sum _ fun j _ ↦ hXm j
  have hψm : Measurable ψ := measurable_cgf aemeasurable_id
  set Lset := Θ ∩ {θ | deriv ψ θ ≤ c}
  have hLm : MeasurableSet Lset :=
    isOpen_interior.measurableSet.inter (measurableSet_le (measurable_deriv _) measurable_const)
  obtain ⟨F, hF_def⟩ : ∃ F : ℝ → ℝ → ℝ≥0∞, F = fun x θ ↦
      ENNReal.ofReal (exp (θ * x - s * ψ θ - (a * x - s * ψ a))) +
        ENNReal.ofReal (exp (θ * x - s * ψ θ - (b * x - s * ψ b))) := ⟨_, rfl⟩
  have hF : Measurable (Function.uncurry F) := by
    rw [hF_def]
    fun_prop
  -- in expectation, for each natural parameter `θ` of a mean at most `c`, each of the two
  -- likelihood ratios is at most `exp (-s k)`
  have h_exp (θ : ℝ) (hθ : θ ∈ Lset) :
      ∫⁻ ω, F (∑ j ∈ Finset.range s, X j ω) θ ∂P ≤ 2 * ENNReal.ofReal (exp (-(s * k))) := by
    have hθc' : θ ≤ θc := Measure.natParam_deriv_cgf hT hθ.1 ▸
      Measure.monotoneOn_natParam (Measure.deriv_cgf_mem_expFamilyMeans hθ.1) hc hθ.2
    have h_one (e : ℝ) (he₁ : a ≤ e) (he₂ : e ≤ b)
        (hke : k ≤ (η - e) * (deriv ψ e - deriv ψ (θc + η - e))) :
        ∫⁻ ω, ENNReal.ofReal (exp (θ * ∑ j ∈ Finset.range s, X j ω - s * ψ θ -
          (e * ∑ j ∈ Finset.range s, X j ω - s * ψ e))) ∂P ≤ ENNReal.ofReal (exp (-(s * k))) := by
      have h := h_indep.lintegral_exp_sub_le (s := Finset.range s) (e := e) (fun j _ ↦ hX j)
        hθ.1 hη (by linarith) (by linarith)
      rw [Finset.card_range] at h
      refine h.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_))
      -- `ψ'(θ + η - e) ≤ ψ'(η(c) + η - e)` since `θ ≤ η(c)`
      have hd : deriv ψ (θ + η - e) ≤ deriv ψ (θc + η - e) :=
        monotoneOn_deriv_cgf (hΘ.out hθ.1 hη ⟨by linarith, by linarith⟩)
          (hmem _ (by linarith) (by linarith)) (by linarith)
      have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have hw : 0 ≤ η - e := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hd hw, mul_le_mul_of_nonneg_left hke hs]
    have hm : AEMeasurable (fun ω ↦ ENNReal.ofReal (exp (θ * ∑ j ∈ Finset.range s, X j ω -
        s * ψ θ - (a * ∑ j ∈ Finset.range s, X j ω - s * ψ a)))) P :=
      (by fun_prop : Measurable fun x : ℝ ↦
        ENNReal.ofReal (exp (θ * x - s * ψ θ - (a * x - s * ψ a)))).comp_aemeasurable hS
    rw [hF_def, lintegral_add_left' hm, two_mul]
    exact add_le_add (h_one a le_rfl hab hka) (h_one b hab le_rfl hkb)
  have hmeas : AEMeasurable (Function.uncurry fun ω θ ↦ F (∑ j ∈ Finset.range s, X j ω) θ)
      (P.prod (π.restrict Lset)) :=
    hF.comp_aemeasurable (hS.comp_fst.prodMk measurable_snd.aemeasurable)
  -- the pointwise bound on the posterior odds, then Tonelli
  calc ∫⁻ ω, (expFamilyTSStackLaw ρ π s (∑ j ∈ Finset.range s, X j ω) (Ioi (c : EReal)))⁻¹ - 1 ∂P
      ≤ ∫⁻ ω, (π (Icc a b))⁻¹ * ∫⁻ θ in Lset, F (∑ j ∈ Finset.range s, X j ω) θ ∂π ∂P :=
        lintegral_mono fun ω ↦ hF_def ▸ inv_expFamilyTSStackLaw_Ioi_sub_one_le hIcc hca hπ s _
    _ = (π (Icc a b))⁻¹ * ∫⁻ θ in Lset, ∫⁻ ω, F (∑ j ∈ Finset.range s, X j ω) θ ∂P ∂π := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hπ), lintegral_lintegral_swap hmeas]
    _ ≤ (π (Icc a b))⁻¹ * ∫⁻ _ in Lset, 2 * ENNReal.ofReal (exp (-(s * k))) ∂π :=
        mul_le_mul_right (setLIntegral_mono' hLm h_exp) _
    _ ≤ (π (Icc a b))⁻¹ * (2 * ENNReal.ofReal (exp (-(s * k))) * π {θ | deriv ψ θ ≤ c}) := by
        rw [setLIntegral_const]
        gcongr
        exact inter_subset_right
    _ = _ := by ring

/-- **The optimal arm is rarely underestimated by Thompson sampling.** Let `X₀, X₁, …` be
independent and dominated on `Set.Iic 0` by the member of mean `μ` of the natural exponential
family of `ρ`, let `c < μ` be a mean of the family, and let the prior `π` give finite mass to the
natural parameters of the means at most `c` and positive mass to every nondegenerate interval of
natural parameters. Write `G_s` for the probability that the perturbation of Thompson sampling
with the prior `π`, after the observations `X₀, …, X_{s-1}`, exceeds `c`. Then
`∑_{s < n} E[1 / G_s - 1]` is bounded uniformly in the horizon `n`. -/
theorem iIndepFun.exists_sum_lintegral_inv_expFamilyTSStackLaw_Ioi_sub_one_le [SFinite ρ]
    [SFinite π] (h_indep : iIndepFun X P)
    (hX : ∀ k, MGFDominatedOn (X k) P id (ρ.expFamily id (ρ.natParam id μ)) (Iic 0))
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans id)
    (hc : c ∈ ρ.expFamilyMeans id) (hcμ : c < μ) (hπc : π {θ | deriv (cgf id ρ) θ ≤ c} ≠ ∞)
    (hπ : ∀ a b, a < b → Icc a b ⊆ interior (integrableExpSet id ρ) → π (Icc a b) ≠ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ s ∈ Finset.range n, ∫⁻ ω,
        (expFamilyTSStackLaw ρ π s (∑ k ∈ Finset.range s, X k ω) (Ioi (c : EReal)))⁻¹ - 1 ∂P ≤
      ENNReal.ofReal C := by
  set ψ := cgf id ρ
  set θc := ρ.natParam id c
  set θμ := ρ.natParam id μ
  have hθc := Measure.natParam_mem_interior_integrableExpSet hc
  have hθμ := Measure.natParam_mem_interior_integrableExpSet hμ
  have hlt : θc < θμ := Measure.strictMonoOn_natParam hT hc hμ hcμ
  have hmem (x : ℝ) (h1 : θc ≤ x) (h2 : x ≤ θμ) : x ∈ interior (integrableExpSet id ρ) :=
    (convex_integrableExpSet (X := (id : ℝ → ℝ)) (μ := ρ)).interior.ordConnected.out hθc hθμ
      ⟨h1, h2⟩
  have hmono := strictMonoOn_deriv_cgf (X := (id : ℝ → ℝ)) hT
  -- the interval `[a, b]` of natural parameters, above the midpoint of `η(c)` and `η(μ)`, and the
  -- exponent `k > 0` of the decay of the expected posterior odds
  set a := θμ - (θμ - θc) / 4 with ha
  set b := θμ - (θμ - θc) / 8 with hb
  have hab : a < b := by linarith
  have hIcc : Icc a b ⊆ interior (integrableExpSet id ρ) := fun θ hθ ↦
    hmem θ (by linarith [hθ.1]) (by linarith [hθ.2])
  have hca : c < deriv ψ a := by
    have h := hmono hθc (hmem a (by linarith) (by linarith)) (by linarith)
    rwa [Measure.deriv_cgf_natParam hc] at h
  have hκ (e : ℝ) (he₁ : a ≤ e) (he₂ : e ≤ b) :
      0 < (θμ - e) * (deriv ψ e - deriv ψ (θc + θμ - e)) :=
    mul_pos (by linarith) (sub_pos.2 (hmono (hmem _ (by linarith) (by linarith))
      (hmem e (by linarith) (by linarith)) (by linarith)))
  set k := min ((θμ - a) * (deriv ψ a - deriv ψ (θc + θμ - a)))
    ((θμ - b) * (deriv ψ b - deriv ψ (θc + θμ - b)))
  have hk : 0 < k := lt_min (hκ a le_rfl hab.le) (hκ b hab.le le_rfl)
  have h_term := h_indep.lintegral_inv_expFamilyTSStackLaw_Ioi_sub_one_le (π := π) hX hT hc hθμ
    hIcc hca (by linarith) (hπ a b hab hIcc) (min_le_left _ _) (min_le_right _ _)
  -- summing the geometric series
  set K := (π (Icc a b))⁻¹ * π {θ | deriv ψ θ ≤ c}
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (hπ a b hab hIcc)) hπc
  have h_geom (n : ℕ) : ∑ s ∈ Finset.range n, exp (-(s * k)) ≤ 1 + k⁻¹ := by
    calc ∑ s ∈ Finset.range n, exp (-(s * k)) ≤ ∑ s ∈ Finset.range (n + 1), exp (-(s * k)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 n.le_succ)
            fun _ _ _ ↦ (exp_pos _).le
      _ = ∑ s ∈ Finset.range n, exp (-(k * (s + 1))) + 1 := by
          rw [Finset.sum_range_succ']
          simp [mul_comm]
      _ ≤ 1 + k⁻¹ := by linarith [Real.sum_range_exp_neg_mul_le hk n]
  refine ⟨K.toReal * (2 * (1 + k⁻¹)), fun n ↦ ?_⟩
  calc ∑ s ∈ Finset.range n, ∫⁻ ω,
        (expFamilyTSStackLaw ρ π s (∑ k ∈ Finset.range s, X k ω) (Ioi (c : EReal)))⁻¹ - 1 ∂P
      ≤ ∑ s ∈ Finset.range n, K * (2 * ENNReal.ofReal (exp (-(s * k)))) :=
        Finset.sum_le_sum fun s _ ↦ h_term s
    _ = K * (2 * ENNReal.ofReal (∑ s ∈ Finset.range n, exp (-(s * k)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ (exp_pos _).le, Finset.mul_sum, Finset.mul_sum]
    _ ≤ K * (2 * ENNReal.ofReal (1 + k⁻¹)) := by
        gcongr
        exact h_geom n
    _ = ENNReal.ofReal (K.toReal * (2 * (1 + k⁻¹))) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK,
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

end ProbabilityTheory

namespace LMLExplore.Bandits

/-- **The optimal arm is rarely underestimated by Thompson sampling, in the reward-stack model.**
Let the rewards of arm `j` be dominated on `Set.Iic 0` by the member of mean `μ` of the natural
exponential family of `ρ`, let `c < μ` be a mean of the family, and let the prior `π` give finite
mass to the natural parameters of the means at most `c` and positive mass to every nondegenerate
interval of natural parameters. In the reward-stack model `streamMeasure ν`, write `G_{j s}` for
the probability that the perturbation of `j` after its first `s` rewards exceeds `c`. Then
`∑_{s < n} E[1 / G_{j s} - 1]` is bounded uniformly in the horizon `n`. -/
theorem exists_sum_lintegral_streamMeasure_inv_expFamilyTSStackLaw_Ioi_sub_one_le {α : Type*}
    [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {j : α} {ρ π : Measure ℝ} [SFinite ρ]
    [SFinite π] {μ c : ℝ}
    (hν : MGFDominatedOn id (ν j) id (ρ.expFamily id (ρ.natParam id μ)) (Iic 0))
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans id)
    (hc : c ∈ ρ.expFamilyMeans id) (hcμ : c < μ) (hπc : π {θ | deriv (cgf id ρ) θ ≤ c} ≠ ∞)
    (hπ : ∀ a b, a < b → Icc a b ⊆ interior (integrableExpSet id ρ) → π (Icc a b) ≠ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ s ∈ Finset.range n, ∫⁻ x,
        (expFamilyTSStackLaw ρ π s (∑ k ∈ Finset.range s, x k j) (Ioi (c : EReal)))⁻¹ - 1
          ∂(streamMeasure ν) ≤ ENNReal.ofReal C :=
  iIndepFun.exists_sum_lintegral_inv_expFamilyTSStackLaw_Ioi_sub_one_le
    (iIndepFun_eval_streamMeasure'' ν j)
    (fun k ↦ (identDistrib_eval_eval_id_streamMeasure ν k j).mgfDominatedOn.trans hν)
    hT hμ hc hcμ hπc hπ

namespace ExpFamilyTS

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ρ : α → Measure ℝ} [∀ a, SFinite (ρ a)] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Number of pulls of Thompson sampling with the Jeffreys prior** [KKM13, proof of
Theorem 2]. In a run of Thompson sampling with the Jeffreys priors of the families `ρ a` against
the stochastic bandit `Environment.bandit ν`, let `i ≠ j` be arms and `c` a level with:
* the rewards of `i` dominated on `Set.univ` by the member of mean `μ < c` of `ρ i`, `c` a mean of
  `ρ i`, and the Jeffreys posterior of `ρ i` proper after some observations;
* the rewards of `j` dominated on `Set.Iic 0` by the member of mean `μ' > c` of `ρ j`, `c` a mean
  of `ρ j`, and the Jeffreys prior of `ρ j` finite on the natural parameters of the means at
  most `c`.
Then for every `0 < β < d_i(μ, c)` there is a constant `C` such that for every horizon `n`,
`E[T_i(n)] ≤ log n / β + C`. -/
theorem exists_lintegral_pullCount_le_log_div_add
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id)
      (Environment.bandit ν) P)
    {i j : α} (hij : i ≠ j) {μ μ' c β : ℝ}
    (hνi : MGFDominatedOn id (ν i) id ((ρ i).expFamily id ((ρ i).natParam id μ)) univ)
    (hTi : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ i] fun _ ↦ c) (hμ : μ ∈ (ρ i).expFamilyMeans id)
    (hci : c ∈ (ρ i).expFamilyMeans id) (hμc : μ < c)
    (hprop : ∃ s₀ S₀, (ρ i).expFamilyPosterior id ((ρ i).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hβ : 0 < β) (hβd : β < (ρ i).expFamilyDiv id μ c)
    (hνj : MGFDominatedOn id (ν j) id ((ρ j).expFamily id ((ρ j).natParam id μ')) (Iic 0))
    (hTj : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ j] fun _ ↦ c) (hμ' : μ' ∈ (ρ j).expFamilyMeans id)
    (hcj : c ∈ (ρ j).expFamilyMeans id) (hcμ' : c < μ')
    (hπ : (ρ j).jeffreysPrior id {θ | deriv (cgf id (ρ j)) θ ≤ c} ≠ ∞) :
    ∃ C : ℝ, ∀ n : ℕ, ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤ ENNReal.ofReal (log n / β + C) := by
  obtain ⟨C₁, hC₁⟩ := exists_lintegral_pullCount_le_add_log h hij hνi hTi hμ hci hμc hprop hβ hβd
  obtain ⟨C₂, hC₂⟩ := exists_sum_lintegral_streamMeasure_inv_expFamilyTSStackLaw_Ioi_sub_one_le
    hνj hTj hμ' hcj hcμ' hπ fun a b hab hΘ ↦ Measure.jeffreysPrior_Icc_ne_zero hTj hab hΘ
  refine ⟨1 + max C₂ 0 + max C₁ 0, fun n ↦ (hC₁ n).trans ?_⟩
  have hL : 0 ≤ log n / β := div_nonneg (log_natCast_nonneg n) hβ.le
  calc 1 + ∑ s ∈ Finset.range n, ∫⁻ x, (expFamilyTSStackLaw (ρ j) ((ρ j).jeffreysPrior id) s
          (∑ k ∈ Finset.range s, x k j) (Ioi (c : EReal)))⁻¹ - 1 ∂(streamMeasure ν) +
        ENNReal.ofReal (log n / β + C₁)
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal (max C₂ 0) + ENNReal.ofReal (log n / β + max C₁ 0) := by
        rw [ENNReal.ofReal_one]
        gcongr
        · exact (hC₂ n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        · exact le_max_left _ _
    _ = ENNReal.ofReal (log n / β + (1 + max C₂ 0 + max C₁ 0)) := by
        rw [← ENNReal.ofReal_add zero_le_one (le_max_right _ _),
          ← ENNReal.ofReal_add (by positivity) (add_nonneg hL (le_max_right _ _))]
        ring_nf

/-- **Asymptotic number of pulls of Thompson sampling with the Jeffreys prior** [KKM13, Theorem 2].
In a run of Thompson sampling with the Jeffreys priors of the families `ρ a` against the
stochastic bandit `Environment.bandit ν`, let `a` and `b` be arms with means `μ_a < μ_b`, both
means of `ρ a`, with `μ_b` a mean of `ρ b`. Let the law of `a` be dominated on `Set.univ` by the
member of mean `μ_a` of `ρ a`, whose Jeffreys posterior is proper after some observations, and
the law of `b` be dominated on `Set.Iic 0` by the member of mean `μ_b` of `ρ b`, whose statistic
is not almost everywhere constant and whose Jeffreys prior is finite on the natural parameters of
the means at most `m`, for every `m < μ_b`. Then for every `c > 1 / d_a(μ_a, μ_b)`, the expected
number of pulls of `a` during the first `n` rounds is eventually at most `c log n`; that is,
`limsup_n E[T_a(n)] / log n ≤ 1 / d_a(μ_a, μ_b)`. The arm `b` is typically an optimal arm. -/
theorem integral_pullCount_eventually_le
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id)
      (Environment.bandit ν) P)
    {a b : α} (ha : (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hνa : MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id])) univ)
    (hpropa : ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hb : (ν b)[id] ∈ (ρ b).expFamilyMeans id)
    (hνb : MGFDominatedOn id (ν b) id ((ρ b).expFamily id ((ρ b).natParam id (ν b)[id]))
      (Iic 0))
    (hρb : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ b] fun _ ↦ c)
    (hπb : ∀ m < (ν b)[id], (ρ b).jeffreysPrior id {θ | deriv (cgf id (ρ b)) θ ≤ m} ≠ ∞)
    (hab : (ν a)[id] < (ν b)[id]) (hba : (ν b)[id] ∈ (ρ a).expFamilyMeans id) {c : ℝ}
    (hc : ((ρ a).expFamilyDiv id (ν a)[id] (ν b)[id])⁻¹ < c) :
    ∀ᶠ n : ℕ in atTop, P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ c * log n := by
  set μa := (ν a)[id]
  set μb := (ν b)[id]
  have hρa := Measure.not_ae_eq_const_of_mem_expFamilyMeans ha hba hab.ne
  have hd0 : 0 < (ρ a).expFamilyDiv id μa μb := Measure.expFamilyDiv_pos ha hba hab.ne
  have hc0 : 0 < c := (inv_pos.2 hd0).trans hc
  -- choose a level `c' < μ_b`, close enough to `μ_b` that `1 / d_a(μ_a, c') < c`
  have h_div : Tendsto (fun x : ℝ ↦ ((ρ a).expFamilyDiv id μa x)⁻¹) (𝓝[<] μb)
      (𝓝 ((ρ a).expFamilyDiv id μa μb)⁻¹) := by
    have h_pair : Tendsto (fun x : ℝ ↦ (μa, x)) (𝓝[<] μb) (𝓝 (μa, μb)) :=
      ((Continuous.prodMk_right μa).tendsto μb).mono_left nhdsWithin_le_nhds
    have hM := Measure.isOpen_expFamilyMeans hρa
    exact (((Measure.continuousOn_expFamilyDiv hρa).continuousAt
      ((hM.prod hM).mem_nhds ⟨ha, hba⟩)).tendsto.comp h_pair).inv₀ hd0.ne'
  have h_mem : ∀ᶠ x in 𝓝[<] μb, x ∈ (ρ b).expFamilyMeans id :=
    mem_nhdsWithin_of_mem_nhds ((Measure.isOpen_expFamilyMeans hρb).mem_nhds hb)
  have h_Ioo : ∀ᶠ x in 𝓝[<] μb, x ∈ Ioo μa μb := Ioo_mem_nhdsLT hab
  obtain ⟨c', hc'b, ⟨hac', hc'b'⟩, hc'⟩ :=
    (h_mem.and (h_Ioo.and (h_div.eventually_lt_const hc))).exists
  have hc'a : c' ∈ (ρ a).expFamilyMeans id :=
    Measure.Icc_subset_expFamilyMeans ha hba ⟨hac'.le, hc'b'.le⟩
  have hdc : 0 < (ρ a).expFamilyDiv id μa c' := Measure.expFamilyDiv_pos ha hc'a hac'.ne
  -- a rate `β` with `1 / β < c` and `β < d_a(μ_a, c')`
  have hcd : c⁻¹ < (ρ a).expFamilyDiv id μa c' := inv_lt_of_inv_lt₀ hdc hc'
  set β := (c⁻¹ + (ρ a).expFamilyDiv id μa c') / 2 with hβ_def
  have hβ : 0 < β := by positivity
  have hβd : β < (ρ a).expFamilyDiv id μa c' := by linarith
  have hβc : β⁻¹ < c := inv_lt_of_inv_lt₀ hc0 (by linarith)
  have hne : a ≠ b := by
    rintro rfl
    exact lt_irrefl _ hab
  obtain ⟨C, hC⟩ := exists_lintegral_pullCount_le_log_div_add h hne hνa hρa ha hc'a hac' hpropa
    hβ hβd hνb hρb hb hc'b hc'b' (hπb c' hc'b')
  have hL : Tendsto (fun n : ℕ ↦ log n / log n) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact (div_self (log_pos (by exact_mod_cast hn)).ne').symm
  filter_upwards [eventually_lt_mul_log_of_tendsto_div_log (tendsto_div_add_div_log hL β C) hβc,
    eventually_ge_atTop 1] with n hn hn1
  have h_le := hC n
  rw [lintegral_pullCount_eq_ofReal_integral h.measurable_action] at h_le
  rcases (ENNReal.ofReal_le_ofReal_iff'.1 h_le) with h_le | h_le
  · exact h_le.trans hn.le
  · exact h_le.trans (mul_nonneg hc0.le (log_natCast_nonneg n))

end ExpFamilyTS

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ρ : α → Measure ℝ} [∀ a, SFinite (ρ a)] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Asymptotic regret of Thompson sampling with the Jeffreys prior** [KKM13, Theorem 1, upper
bound]. In a run of Thompson sampling with the Jeffreys priors of the families `ρ a` against the
stochastic bandit `Environment.bandit ν`, let the mean `μ_a` of every arm `a` with positive gap
lie in the interval of means of `ρ a`, together with the largest mean `μ*`, let its law be
dominated on `Set.univ` by the member of mean `μ_a` of `ρ a`, and let the Jeffreys posterior of
`ρ a` be proper after some observations. Let the optimal arm `a*` have its mean `μ*` in the
interval of means of `ρ a*`, its law dominated on `Set.Iic 0` by the member of mean `μ*`, a
statistic that is not almost everywhere constant, and a Jeffreys prior that is finite on the
natural parameters of the means at most `m`, for every `m < μ*`. Then for every
`c > ∑_{a : Δ_a > 0} Δ_a / d_a(μ_a, μ*)`, the expected regret at horizon `n` is eventually at most
`c log n`; that is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_a(μ_a, μ*)`. -/
theorem expFamilyTS_jeffreysPrior_regret_eventually_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id)
      (Environment.bandit ν) P)
    (hμ : ∀ a, 0 < gap ν a → (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ a, 0 < gap ν a →
      MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id])) univ)
    (hprop : ∀ a, 0 < gap ν a →
      ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hμs : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id)
    (hs : (ν (bestArm ν))[id] ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (hνs : MGFDominatedOn id (ν (bestArm ν)) id ((ρ (bestArm ν)).expFamily id
      ((ρ (bestArm ν)).natParam id (ν (bestArm ν))[id])) (Iic 0))
    (hρs : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ (bestArm ν)] fun _ ↦ c)
    (hπs : ∀ m < (ν (bestArm ν))[id], (ρ (bestArm ν)).jeffreysPrior id
      {θ | deriv (cgf id (ρ (bestArm ν))) θ ≤ m} ≠ ∞) {c : ℝ}
    (hc : ∑ a ∈ Finset.univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n :=
  integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
    h.measurable_action (.of_forall fun n ↦ log_natCast_nonneg n)
    (fun a ↦ ((ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id])⁻¹)
    (fun a ha _ hc ↦ ExpFamilyTS.integral_pullCount_eventually_le h (hμ a ha) (hν a ha)
      (hprop a ha) hs hνs hρs hπs (by linarith [gap_eq_bestArm_sub (ν := ν) (a := a)])
      (hμs a ha) hc)
    (by simpa only [div_eq_mul_inv] using hc)

end LMLExplore.Bandits
