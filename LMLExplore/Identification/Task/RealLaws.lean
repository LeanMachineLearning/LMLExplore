/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Regret
public import LMLExplore.EValues.SubGaussian.Null
public import LMLExplore.Identification.Task.ProductModel
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.Probability.Moments.SubGaussian.Bounded
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian

/-!
# The model of all bandits with real observations

A guarantee for every bandit of a class, such as the bandits whose arms are σ²-sub-Gaussian or have
laws on `[0, 1]`, and not only for the bandits of a parametric family, is a guarantee on a
restriction of a task of a single model, in which a model is the vector
`θ : α → ProbabilityMeasure ℝ` of the arm laws themselves: arm `a` of `θ` has law `θ a`
(`lawBandit θ`), and the mean functional is the vector of the means `lawMean θ a = ∫ x ∂(θ a)`.
Every Markov kernel `κ : Kernel α ℝ` is the bandit of a model, the model `a ↦ κ a`
(`exists_lawBandit_eq`), so that a statement for every model of a restricted task is a statement
for every bandit of the class. For instance, best arm identification with σ²-sub-Gaussian arms is
`(baiTask lawBandit lawMean).restrict (Set.univ.pi fun _ ↦ subgaussianLaws σ2)`.

This model is the product model (`LMLExplore.Identification.productBandit`) with arm parameters the
laws `ProbabilityMeasure ℝ` and per-arm admissible sets the laws of a class. Its transportation
costs `K⁻` and `K⁺` for the laws on `[0, 1]` are bounded below by the binary relative entropy of
the means: a law of mean `μ` on `[0, 1]` is at relative entropy at least `d(μ, u)` from every law
on `[0, 1]` of mean at least `u ≥ μ`, by the data processing inequality through the kernel
`x ↦ Ber(x)` (`LMLExplore.klBer_integral_le_klDiv`, the fundamental inequality of [GMS19]), with
equality at the Bernoulli laws [AJG20].

## Main definitions

* `LMLExplore.Identification.lawBandit θ`: the bandit whose arm `a` has law `θ a`, for a vector of
  laws `θ : α → ProbabilityMeasure ℝ`.
* `LMLExplore.Identification.lawMean θ a`: the mean `∫ x ∂(θ a)` of arm `a`, the mean functional of
  the model.
* `LMLExplore.Identification.subgaussianLaws σ2`: the laws `P` on `ℝ` that are σ²-sub-Gaussian
  around their mean, `P[exp (t (X - ∫ x ∂P))] ≤ exp (σ² t² / 2)`: their centred law is in the
  two-sided sub-Gaussian null `ProbabilityTheory.subgaussianNull σ2`.
* `LMLExplore.Identification.unitIntervalLaws`: the laws on `[0, 1]`.
* `LMLExplore.Identification.bernoulliModel p`: the Bernoulli model with success probabilities
  `p`, whose bandit is the Bernoulli bandit `Bandits.bernoulliBandit p`.

## Main statements

* `LMLExplore.Identification.exists_lawBandit_eq`: every Markov kernel `κ : Kernel α ℝ` is the
  bandit of a model, the model `a ↦ κ a`.
* `LMLExplore.Identification.unitIntervalLaws_subset_subgaussianLaws`: laws on `[0, 1]` are
  `1 / 4`-sub-Gaussian (Hoeffding's lemma).
* `LMLExplore.Identification.klBer_le_kInfUpper_of_subset_unitIntervalLaws`,
  `LMLExplore.Identification.klBer_le_kInfLower_of_subset_unitIntervalLaws`: for a law `P` on
  `[0, 1]` of mean `μ`, `d(μ, u) ≤ K⁺(P, u)` for `u ≥ μ` and `d(μ, u) ≤ K⁻(P, u)` for `u ≤ μ`, the
  infima being over any class of laws on `[0, 1]`.
* `LMLExplore.Identification.kInfUpper_unitIntervalLaws_bernoulliMeasure`,
  `LMLExplore.Identification.kInfLower_unitIntervalLaws_bernoulliMeasure`: over the class of all
  laws on `[0, 1]`, these bounds are equalities at the Bernoulli laws, for levels `u ∈ [0, 1]`.
* `LMLExplore.Identification.mem_M_bernoulliModel`,
  `LMLExplore.Identification.correct_bernoulliModel`,
  `LMLExplore.Identification.gap_lawBandit_bernoulliModel`: a Bernoulli model whose arm `a` has
  the largest success probability is a model of best arm identification with laws on `[0, 1]`,
  with correct answer `a` and gaps `p a - p b`.

## References

* [AJG20] S. Agrawal, S. Juneja and P. Glynn, *Optimal δ-correct best-arm selection for
  heavy-tailed distributions*, ALT 2020, for the transportation costs `K⁻`, `K⁺` of classes of
  laws.
* [GMS19] A. Garivier, P. Ménard and G. Stoltz, *Explore first, exploit next: the true shape of
  regret in bandit problems*, Math. Oper. Res. 44 (2019), for the fundamental inequality
  `d(∫ x ∂μ, ∫ x ∂ν) ≤ KL(μ ‖ ν)` behind the bounds on `K⁻` and `K⁺`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set

open scoped ENNReal NNReal unitInterval

namespace LMLExplore.Identification

variable {α : Type*} {mα : MeasurableSpace α}

/-! ### The model -/

section Model

variable [Countable α] [MeasurableSingletonClass α]

/-- The bandit of the model of all bandits with real observations: arm `a` of the model
`θ : α → ProbabilityMeasure ℝ` has law `θ a`. It is the product model whose arm parameters are the
arm laws. -/
noncomputable def lawBandit (θ : α → ProbabilityMeasure ℝ) : Kernel α ℝ :=
  productBandit (fun _ (P : ProbabilityMeasure ℝ) ↦ (P : Measure ℝ)) θ

lemma lawBandit_def :
    lawBandit = productBandit (α := α) fun _ (P : ProbabilityMeasure ℝ) ↦ (P : Measure ℝ) :=
  (rfl)

@[simp]
lemma lawBandit_apply (θ : α → ProbabilityMeasure ℝ) (a : α) :
    lawBandit θ a = (θ a : Measure ℝ) := by
  simp [lawBandit_def]

instance isMarkovKernel_lawBandit (θ : α → ProbabilityMeasure ℝ) :
    IsMarkovKernel (lawBandit θ) :=
  inferInstanceAs (IsMarkovKernel (productBandit (fun _ (P : ProbabilityMeasure ℝ) ↦
    (P : Measure ℝ)) θ))

/-- A model is determined by its bandit. -/
lemma lawBandit_injective : Function.Injective (lawBandit (α := α)) := fun θ θ' h ↦
  funext fun a ↦ ProbabilityMeasure.toMeasure_injective (by simpa using DFunLike.congr_fun h a)

@[simp]
lemma lawBandit_inj {θ θ' : α → ProbabilityMeasure ℝ} : lawBandit θ = lawBandit θ' ↔ θ = θ' :=
  lawBandit_injective.eq_iff

/-- A model has the bandit `κ` iff each of its arm laws is the law of the same arm under `κ`. -/
lemma lawBandit_eq_iff {θ : α → ProbabilityMeasure ℝ} {κ : Kernel α ℝ} :
    lawBandit θ = κ ↔ ∀ a, (θ a : Measure ℝ) = κ a := by
  simp [Kernel.ext_iff]

/-- Every Markov kernel is the bandit of a model: the model `θ` of its arm laws, `θ a = κ a`. -/
theorem exists_lawBandit_eq (κ : Kernel α ℝ) [IsMarkovKernel κ] : ∃ θ, lawBandit θ = κ :=
  ⟨fun a ↦ ⟨κ a, inferInstance⟩, lawBandit_eq_iff.2 fun _ ↦ ProbabilityMeasure.coe_mk _ _⟩

end Model

/-- The mean functional of the model of all bandits with real observations: the mean of arm `a`
of the model `θ` is the mean of its law `θ a`. -/
noncomputable def lawMean (θ : α → ProbabilityMeasure ℝ) (a : α) : ℝ := (θ a : Measure ℝ)[id]

lemma lawMean_def (θ : α → ProbabilityMeasure ℝ) (a : α) : lawMean θ a = (θ a : Measure ℝ)[id] :=
  (rfl)

lemma lawMean_eq_integral_lawBandit [Countable α] [MeasurableSingletonClass α]
    (θ : α → ProbabilityMeasure ℝ) (a : α) : lawMean θ a = (lawBandit θ a)[id] := by
  rw [lawBandit_apply, lawMean_def]

/-! ### Classes of laws -/

/-- The laws `P` on `ℝ` that are σ²-sub-Gaussian around their mean: the law of `x - ∫ y ∂P`
under `P` is in the two-sided σ²-sub-Gaussian null, that is,
`∫ exp (t (x - ∫ y ∂P)) ∂P(x) ≤ exp (σ² t² / 2)` for every `t` (`mem_subgaussianLaws_iff`). -/
def subgaussianLaws (σ2 : ℝ≥0) : Set (ProbabilityMeasure ℝ) :=
  {P | (P : Measure ℝ).map (fun x ↦ x - (P : Measure ℝ)[id]) ∈ subgaussianNull σ2}

/-- The laws on `[0, 1]`. -/
def unitIntervalLaws : Set (ProbabilityMeasure ℝ) :=
  {P | ∀ᵐ x ∂(P : Measure ℝ), x ∈ Icc 0 1}

variable {P : ProbabilityMeasure ℝ} {σ2 : ℝ≥0}

lemma subgaussianLaws_def (σ2 : ℝ≥0) :
    subgaussianLaws σ2 = {P : ProbabilityMeasure ℝ |
      (P : Measure ℝ).map (fun x ↦ x - (P : Measure ℝ)[id]) ∈ subgaussianNull σ2} :=
  (rfl)

@[simp]
lemma mem_subgaussianLaws_iff :
    P ∈ subgaussianLaws σ2 ↔ HasSubgaussianMGF (fun x ↦ x - (P : Measure ℝ)[id]) σ2 P := by
  rw [subgaussianLaws_def, mem_ofPred_eq, mem_subgaussianNull_iff_hasSubgaussianMGF,
    HasSubgaussianMGF.id_map_iff (by fun_prop)]
  exact and_iff_right inferInstance

@[simp]
lemma mem_unitIntervalLaws_iff : P ∈ unitIntervalLaws ↔ ∀ᵐ x ∂(P : Measure ℝ), x ∈ Icc 0 1 :=
  Iff.rfl

lemma subgaussianLaws_mono : Monotone subgaussianLaws := fun _ _ h _ hP ↦ by
  rw [subgaussianLaws_def, mem_ofPred_eq] at hP ⊢
  exact subgaussianNull_mono h hP

/-- **Hoeffding's lemma**: a law on `[0, 1]` is `1 / 4`-sub-Gaussian around its mean. -/
lemma unitIntervalLaws_subset_subgaussianLaws : unitIntervalLaws ⊆ subgaussianLaws (1 / 4) :=
  fun _ hP ↦ mem_subgaussianLaws_iff.2 (hasSubgaussianMGF_of_mem_Icc_zero_one aemeasurable_id hP)

/-- The Bernoulli laws `Ber(1, 0, p)` are laws on `[0, 1]`. -/
lemma bernoulliMeasure_mem_unitIntervalLaws (p : I) :
    (⟨Ber((1 : ℝ), 0, p), inferInstance⟩ : ProbabilityMeasure ℝ) ∈ unitIntervalLaws := by
  refine (ae_mem_uIcc_bernoulliMeasure (1 : ℝ) 0 p).mono fun x hx ↦ ?_
  rwa [uIcc_of_ge zero_le_one] at hx

/-- The models of the restricted task of σ²-sub-Gaussian arms are the models whose every arm is
σ²-sub-Gaussian around its mean. -/
lemma mem_pi_subgaussianLaws_iff [Countable α] [MeasurableSingletonClass α]
    {θ : α → ProbabilityMeasure ℝ} :
    θ ∈ univ.pi (fun _ ↦ subgaussianLaws σ2) ↔
      ∀ a, HasSubgaussianMGF (fun x ↦ x - lawMean θ a) σ2 (lawBandit θ a) := by
  simp [lawMean_def]

/-- The models of the restricted task of arms with laws on `[0, 1]` are the models whose every arm
takes values in `[0, 1]` almost surely. -/
lemma mem_pi_unitIntervalLaws_iff [Countable α] [MeasurableSingletonClass α]
    {θ : α → ProbabilityMeasure ℝ} :
    θ ∈ univ.pi (fun _ ↦ unitIntervalLaws) ↔ ∀ a, ∀ᵐ x ∂(lawBandit θ a), x ∈ Icc 0 1 := by
  simp

/-! ### Bernoulli models -/

section Bernoulli

/-- The Bernoulli model with success probabilities `p`: arm `a` has law `Ber(1, 0, p a)`. Its
bandit is the Bernoulli bandit `Bandits.bernoulliBandit p` (`lawBandit_bernoulliModel`). -/
noncomputable def bernoulliModel (p : α → I) : α → ProbabilityMeasure ℝ :=
  fun a ↦ ⟨Ber((1 : ℝ), 0, p a), inferInstance⟩

@[simp]
lemma bernoulliModel_apply (p : α → I) (a : α) :
    (bernoulliModel p a : Measure ℝ) = Ber((1 : ℝ), 0, p a) :=
  (rfl)

@[simp]
lemma lawMean_bernoulliModel (p : α → I) (b : α) : lawMean (bernoulliModel p) b = p b := by
  simp [lawMean_def]

/-- The Bernoulli models are models with laws on `[0, 1]`. -/
lemma bernoulliModel_mem_pi_unitIntervalLaws (p : α → I) :
    bernoulliModel p ∈ univ.pi fun _ ↦ unitIntervalLaws :=
  fun b _ ↦ bernoulliMeasure_mem_unitIntervalLaws (p b)

variable [Countable α] [MeasurableSingletonClass α] {p : α → I} {a : α}

@[simp]
lemma lawBandit_bernoulliModel (p : α → I) :
    lawBandit (bernoulliModel p) = Bandits.bernoulliBandit p :=
  lawBandit_eq_iff.2 fun b ↦ by simp

/-- The arm `b` of the Bernoulli model with success probabilities `p` has the law `Ber(p b)` in
best arm identification. -/
lemma ν_baiTask_bernoulliModel (p : α → I) (b : α) :
    (baiTask lawBandit lawMean).ν (bernoulliModel p) b = Ber((1 : ℝ), 0, p b) := by
  rw [ν_baiTask, lawBandit_bernoulliModel, Bandits.bernoulliBandit_apply]

/-- A Bernoulli model whose arm `a` has the largest success probability is a model of best arm
identification with laws on `[0, 1]`, with best arm `a`. -/
lemma mem_M_bernoulliModel (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    bernoulliModel p ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (univ.pi fun _ ↦ unitIntervalLaws)).M := by
  rw [IdentTask.M_restrict, M_baiTask]
  exact ⟨⟨a, fun b hb ↦ by simpa using ha b hb⟩, bernoulliModel_mem_pi_unitIntervalLaws p⟩

/-- The correct answer of best arm identification at a Bernoulli model whose arm `a` has the
largest success probability is `a`. -/
lemma correct_bernoulliModel (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    (baiTask (lawBandit (α := α)) lawMean).correct (bernoulliModel p) = {a} :=
  (correct_baiTask_eq_singleton_iff _ _).2 fun b hb ↦ by simpa using ha b hb

/-- The gap of the arm `b` of a Bernoulli model whose arm `a` has the largest success probability
is `p a - p b`. -/
lemma gap_lawBandit_bernoulliModel [Finite α] (ha : ∀ b ≠ a, (p b : ℝ) < p a) (b : α) :
    Bandits.gap (lawBandit (bernoulliModel p)) b = p a - p b := by
  rw [lawBandit_bernoulliModel, Bandits.gap_eq_sub_of_forall_lt (by simpa using ha),
    Bandits.integral_id_bernoulliBandit, Bandits.integral_id_bernoulliBandit]

variable [Fintype α]

/-- The complexity `∑_b Δ_b⁻²` of a Bernoulli model whose arm `a` has the largest success
probability. -/
lemma sum_inv_sq_gap_bernoulliModel (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    ∑ b, (Bandits.gap (lawBandit (bernoulliModel p)) b ^ 2)⁻¹ = ∑ b, (((p a : ℝ) - p b) ^ 2)⁻¹ := by
  simp_rw [gap_lawBandit_bernoulliModel ha]

/-- The complexity `∑_b Δ_b⁻²` of a Bernoulli model whose arm `a` has the largest success
probability is positive when there is another arm `b`. -/
lemma sum_inv_sq_gap_bernoulliModel_pos {b : α} (ha : ∀ b ≠ a, (p b : ℝ) < p a) (hb : b ≠ a) :
    0 < ∑ c, (Bandits.gap (lawBandit (bernoulliModel p)) c ^ 2)⁻¹ := by
  rw [sum_inv_sq_gap_bernoulliModel ha]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun c _ ↦ by positivity) (Finset.mem_univ b))
  have := sub_pos.2 (ha b hb)
  positivity

end Bernoulli

/-! ### The transportation costs of the laws on `[0, 1]` -/

section KInf

variable {S : Set (ProbabilityMeasure ℝ)} {u : ℝ}

/-- For a law `P` on `[0, 1]` of mean `μ`, a level `u ≥ μ` and a class `S` of laws on `[0, 1]`,
every law of `S` of mean at least `u` is at relative entropy at least `d(μ, u)` from `P`:
`d(μ, u) ≤ K⁺(P, u)`. -/
theorem klBer_le_kInfUpper_of_subset_unitIntervalLaws (hS : S ⊆ unitIntervalLaws)
    (hP : P ∈ unitIntervalLaws) (hu : (P : Measure ℝ)[id] ≤ u) :
    klBer (P : Measure ℝ)[id] u ≤
      kInfUpper ProbabilityMeasure.toMeasure S (fun Q ↦ (Q : Measure ℝ)[id]) P u :=
  le_kInfUpper_iff.2 fun _ hQ huQ ↦ (monotoneOn_klBer _ hu (hu.trans huQ) huQ).trans
    (klBer_integral_le_klDiv (mem_unitIntervalLaws_iff.1 hP)
      (mem_unitIntervalLaws_iff.1 (hS hQ)))

/-- For a law `P` on `[0, 1]` of mean `μ`, a level `u ≤ μ` and a class `S` of laws on `[0, 1]`,
every law of `S` of mean at most `u` is at relative entropy at least `d(μ, u)` from `P`:
`d(μ, u) ≤ K⁻(P, u)`. -/
theorem klBer_le_kInfLower_of_subset_unitIntervalLaws (hS : S ⊆ unitIntervalLaws)
    (hP : P ∈ unitIntervalLaws) (hu : u ≤ (P : Measure ℝ)[id]) :
    klBer (P : Measure ℝ)[id] u ≤
      kInfLower ProbabilityMeasure.toMeasure S (fun Q ↦ (Q : Measure ℝ)[id]) P u := by
  refine le_kInfLower_iff.2 fun Q hQ hQu ↦ ?_
  have hQ01 := integral_id_mem_Icc_of_ae_mem_Icc (hS hQ)
  exact ((strictAntiOn_klBer (integral_id_mem_Icc_of_ae_mem_Icc hP)).antitoneOn
    ⟨hQ01.1, hQu.trans hu⟩ ⟨hQ01.1.trans hQu, hu⟩ hQu).trans
    (klBer_integral_le_klDiv (mem_unitIntervalLaws_iff.1 hP)
      (mem_unitIntervalLaws_iff.1 (hS hQ)))

/-- At the Bernoulli law of mean `p` and a level `u ∈ [p, 1]`, the smallest relative entropy to a
law on `[0, 1]` of mean at least `u` is the binary relative entropy `d(p, u)`, attained at the
Bernoulli law of mean `u`. -/
theorem kInfUpper_unitIntervalLaws_bernoulliMeasure {p : I} (hpu : (p : ℝ) ≤ u) (hu : u ≤ 1) :
    kInfUpper ProbabilityMeasure.toMeasure unitIntervalLaws (fun Q ↦ (Q : Measure ℝ)[id])
      ⟨Ber((1 : ℝ), 0, p), inferInstance⟩ u = klBer p u := by
  refine le_antisymm ?_ ?_
  · simpa using kInfUpper_le (κ := ProbabilityMeasure.toMeasure) (m := fun Q ↦ (Q : Measure ℝ)[id])
      (x := ⟨Ber((1 : ℝ), 0, p), inferInstance⟩)
      (bernoulliMeasure_mem_unitIntervalLaws ⟨u, p.property.1.trans hpu, hu⟩)
      (by simp [TauCeti.Probability.integral_id_bernoulliMeasure])
  · simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using
      klBer_le_kInfUpper_of_subset_unitIntervalLaws subset_rfl
        (bernoulliMeasure_mem_unitIntervalLaws p)
        (by simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using hpu)

/-- At the Bernoulli law of mean `p` and a level `u ∈ [0, p]`, the smallest relative entropy to a
law on `[0, 1]` of mean at most `u` is the binary relative entropy `d(p, u)`, attained at the
Bernoulli law of mean `u`. -/
theorem kInfLower_unitIntervalLaws_bernoulliMeasure {p : I} (hu : 0 ≤ u) (hup : u ≤ p) :
    kInfLower ProbabilityMeasure.toMeasure unitIntervalLaws (fun Q ↦ (Q : Measure ℝ)[id])
      ⟨Ber((1 : ℝ), 0, p), inferInstance⟩ u = klBer p u := by
  refine le_antisymm ?_ ?_
  · simpa using kInfLower_le (κ := ProbabilityMeasure.toMeasure) (m := fun Q ↦ (Q : Measure ℝ)[id])
      (x := ⟨Ber((1 : ℝ), 0, p), inferInstance⟩)
      (bernoulliMeasure_mem_unitIntervalLaws ⟨u, hu, hup.trans p.property.2⟩)
      (by simp [TauCeti.Probability.integral_id_bernoulliMeasure])
  · simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using
      klBer_le_kInfLower_of_subset_unitIntervalLaws subset_rfl
        (bernoulliMeasure_mem_unitIntervalLaws p)
        (by simpa [TauCeti.Probability.integral_id_bernoulliMeasure] using hup)

end KInf

end LMLExplore.Identification
