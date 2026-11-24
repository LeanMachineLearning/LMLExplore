/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance
import LMLExplore.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration

/-!
# Restarting at a vector of counts in a table of observations

Finitely many sources `a : α` produce observations in `𝓧`, and a sequence of seeds in `𝓤` drives
the randomization of whoever reads them. A point is a pair `ω = (u, x)` of seeds `u : ℕ → 𝓤` and
of a table `x : ℕ → α → 𝓧`, where `x i a` is the observation number `i` of the source `a`. Under
`arrayLaw ρ ν` the seeds are independent with law `ρ`, the observations are independent, those of
the source `a` with law `ν a`, and the seeds are independent of the table. For the uniform law on
the unit interval and a kernel `ν`, this is the array model of LML,
`Bandits.ArrayModel.arrayMeasure`.

A *shape* `s : ℕ × (α → ℕ)` counts seeds and observations of each source: the entries below `s`
are the first `s.1` seeds and the first `s.2 a` observations of each source `a`. A random shape
`σ` determined by the entries below itself (`IsReadBy σ σ`) is a stopping point of the filtration
of the entries indexed by the shapes: it is what an algorithm reads when it chooses adaptively
which source to observe and stops. Such a shape is the vector of counts at which the table can
be restarted. Under `arrayLaw ρ ν`, what is determined by the entries below `σ` is independent of
the seeds and the table after `σ`, which have the law `arrayLaw ρ ν` again
(`ProbabilityTheory.lintegral_mul_comp_shiftArray_of_isReadBy`): this is the strong Markov
property of the table at a vector of counts.

Restarting a round that reads the entries below `σ` on the entries that the previous rounds have
not read gives independent rounds with the same law (`ProbabilityTheory.restartShape`,
`ProbabilityTheory.restartPoint`). When `σ` reads at most `K` observations of each source, the
numbers of observations read by `m` rounds concentrate around `m` times their mean, by
Chebyshev's inequality (`ProbabilityTheory.measureReal_not_restartShape_le`).

## Main definitions

* `ProbabilityTheory.arrayLaw ρ ν`: the law of the seeds and the table under the instance `ν`.
* `ProbabilityTheory.shiftArray s ω`: the seeds and the table after the shape `s`.
* `ProbabilityTheory.AgreeBelow s ω ω'`: `ω` and `ω'` have the same entries below the shape `s`.
* `ProbabilityTheory.IsReadBy σ f`: `f` is determined by the entries below the random shape `σ`.
* `ProbabilityTheory.restartShape σ j`, `ProbabilityTheory.restartPoint σ j`: the entries read by
  `j` rounds, each restarted on the entries that the previous rounds have not read, and the point
  at which the round of index `j` starts.
* `ProbabilityTheory.tableOfArray n x`: the first `n a` observations of each source, as a point of
  `(Σ a, Fin (n a)) → 𝓧`.

## Main statements

* `ProbabilityTheory.lintegral_mul_comp_shiftArray`: under `arrayLaw ρ ν`, a function of the
  entries below a shape `s` is independent of the entries after `s`, which have the law
  `arrayLaw ρ ν`.
* `ProbabilityTheory.lintegral_mul_comp_shiftArray_of_isReadBy`,
  `ProbabilityTheory.map_shiftArray_of_isReadBy`,
  `ProbabilityTheory.indepFun_comp_shiftArray_of_isReadBy`: the same at a random shape determined
  by the entries below itself.
* `ProbabilityTheory.lintegral_prod_restartPoint_le_one`: the product of the payoffs of restarted
  rounds of expectation at most `1` has expectation at most `1`.
* `ProbabilityTheory.measureReal_not_restartShape_le`: `m` rounds read more than `n a`
  observations of some source `a`, where `n a ≥ m (𝔼[(σ ω).2 a] + ε)`, with probability at most
  `|α| K² / (m ε²)`.

## Implementation notes

The definitions and proofs are adapted from the draft `notes/lean-wip/SeveralArmsRound.lean` of
the paper project `RemyDegenne/evalues_research`, which proves the Wald inequality with a design
of [EVR26, Note 41]. The one-stream analogue, a single i.i.d. sequence restarted at a stopping
time, is `LMLExplore.Probability.ProductMeasure.Restart`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`.
-/

public section

open MeasureTheory
open TauCeti.Probability (shift shift_iterate_apply)
open scoped ENNReal

namespace ProbabilityTheory

variable {α 𝓤 𝓧 : Type*} {m𝓤 : MeasurableSpace 𝓤} {m𝓧 : MeasurableSpace 𝓧}

/-! ### The table and its shifts -/

/-- The table after the first `n a` observations of each source `a`. -/
def shiftTable (n : α → ℕ) (x : ℕ → α → 𝓧) : ℕ → α → 𝓧 := fun i a ↦ x (i + n a) a

lemma shiftTable_apply (n : α → ℕ) (x : ℕ → α → 𝓧) (i : ℕ) (a : α) :
    shiftTable n x i a = x (i + n a) a := (rfl)

@[fun_prop]
lemma measurable_shiftTable (n : α → ℕ) : Measurable (shiftTable (𝓧 := 𝓧) n) :=
  measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun a ↦
    (measurable_pi_apply a).comp (measurable_pi_apply (i + n a))

/-- Shifting the table preserves its law. -/
lemma map_shiftTable (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] (n : α → ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν).map (shiftTable n) =
      Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν := by
  set C := MeasurableEquiv.curry ℕ α 𝓧
  have hφ : Function.Injective fun p : ℕ × α ↦ (p.1 + n p.2, p.2) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    simpa using h1
  have h_comp : shiftTable n ∘ C = C ∘ fun (y : ℕ × α → 𝓧) p ↦ y (p.1 + n p.2, p.2) := rfl
  rw [← Measure.infinitePi_map_curry (fun (_ : ℕ) (a : α) ↦ ν a),
    Measure.map_map (measurable_shiftTable n) C.measurable, h_comp,
    ← Measure.map_map C.measurable (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (P := fun p : ℕ × α ↦ ν p.2) hφ]

/-- Under the law of the table, a function of the first `n a` observations of each source `a` is
independent of the table after these observations, which has the same law: the expectation of the
product is the product of the expectations. -/
lemma lintegral_mul_comp_shiftTable (ν : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (ν a)] {n : α → ℕ} {f g : (ℕ → α → 𝓧) → ℝ≥0∞}
    (hf : Measurable f) (hfn : ∀ x x', (∀ a, ∀ i < n a, x i a = x' i a) → f x = f x')
    (hg : Measurable g) :
    ∫⁻ x, f x * g (shiftTable n x) ∂(Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν) =
      (∫⁻ x, f x ∂(Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν)) *
        ∫⁻ x, g x ∂(Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν) := by
  classical
  set P := Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν
  -- an empty space of tables carries only the zero measure
  rcases isEmpty_or_nonempty (ℕ → α → 𝓧) with hE | hne
  · simp [Measure.eq_zero_of_isEmpty P]
  obtain ⟨x₀⟩ := hne
  -- the entries below `n` and the entries after `n` are independent
  set S : Set (ℕ × α) := {p | p.1 < n p.2}
  set T : Set (ℕ × α) := {p | n p.2 ≤ p.1}
  have hST : Disjoint S T := Set.disjoint_left.2 fun p (hp : p.1 < n p.2) (hp' : n p.2 ≤ p.1) ↦
    (not_lt.2 hp') hp
  have h_indep := (iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) (fun (_ : ℕ) (a : α) ↦ ν a)
    (fun _ _ ↦ measurable_id)).indepFun_set S T hST
    (fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  simp only [id] at h_indep
  -- `f` is a function of the entries below `n`
  let ext : (S → 𝓧) → ℕ → α → 𝓧 := fun y i a ↦ if h : i < n a then y ⟨(i, a), h⟩ else x₀ i a
  have hext : Measurable ext := by
    refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun a ↦ ?_
    by_cases h : i < n a
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_const
  have hf_eq : f = (f ∘ ext) ∘ fun x (p : S) ↦ x p.val.1 p.val.2 := by
    ext x
    refine hfn _ _ fun a i hi ↦ ?_
    simp [ext, hi]
  -- the shifted table is a function of the entries after `n`
  let ψ : (T → 𝓧) → ℕ → α → 𝓧 := fun y i a ↦ y ⟨(i + n a, a), Nat.le_add_left _ _⟩
  have hψ : Measurable ψ :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun a ↦ measurable_pi_apply _
  have hg_eq : (fun x ↦ g (shiftTable n x)) = (g ∘ ψ) ∘ fun x (p : T) ↦ x p.val.1 p.val.2 := rfl
  have hmS : Measurable fun (x : ℕ → α → 𝓧) (p : S) ↦ x p.val.1 p.val.2 :=
    measurable_pi_iff.2 fun p ↦ (measurable_pi_apply p.val.2).comp (measurable_pi_apply p.val.1)
  have hmT : Measurable fun (x : ℕ → α → 𝓧) (p : T) ↦ x p.val.1 p.val.2 :=
    measurable_pi_iff.2 fun p ↦ (measurable_pi_apply p.val.2).comp (measurable_pi_apply p.val.1)
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    ((hf.comp hext).comp hmS) ((hg.comp hψ).comp hmT)
    (h_indep.comp (hf.comp hext) (hg.comp hψ))
  rw [← hf_eq, ← hg_eq] at h
  have h_shift : ∫⁻ x, g (shiftTable n x) ∂P = ∫⁻ x, g x ∂P := by
    rw [← lintegral_map hg (measurable_shiftTable n), map_shiftTable ν n]
  rw [← h_shift]
  exact h

/-! ### Seeds and table -/

/-- The law of the seeds and of the table of observations under the instance `ν`: the seeds are
independent with law `ρ`, the observations are independent, those of the source `a` with law `ν a`,
and the seeds are independent of the table. With `𝓤` the unit interval and `ρ` its uniform law,
this is `Bandits.ArrayModel.arrayMeasure` of LML. -/
noncomputable def arrayLaw (ρ : Measure 𝓤) (ν : α → Measure 𝓧) :
    Measure ((ℕ → 𝓤) × (ℕ → α → 𝓧)) :=
  (Measure.infinitePi fun _ : ℕ ↦ ρ).prod (Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν)

lemma arrayLaw_def (ρ : Measure 𝓤) (ν : α → Measure 𝓧) :
    arrayLaw ρ ν = (Measure.infinitePi fun _ : ℕ ↦ ρ).prod
      (Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν) := (rfl)

instance (ρ : Measure 𝓤) [IsProbabilityMeasure ρ] (ν : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (ν a)] : IsProbabilityMeasure (arrayLaw ρ ν) := by
  rw [arrayLaw_def]
  infer_instance

/-- The seeds and the table after a shape `s`: the seeds after the first `s.1` ones and, for each
source `a`, the observations after the first `s.2 a` ones. -/
def shiftArray (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : (ℕ → 𝓤) × (ℕ → α → 𝓧) :=
  (fun i ↦ ω.1 (i + s.1), shiftTable s.2 ω.2)

lemma shiftArray_def (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
    shiftArray s ω = (fun i ↦ ω.1 (i + s.1), shiftTable s.2 ω.2) := (rfl)

/-- The seeds after a shape are the iterated shift of the seeds. -/
lemma shiftArray_eq_shift_iterate (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
    shiftArray s ω = ((shift 𝓤)^[s.1] ω.1, shiftTable s.2 ω.2) :=
  Prod.ext (funext fun i ↦ (shift_iterate_apply s.1 i ω.1).symm) rfl

lemma shiftArray_fst_apply (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) (i : ℕ) :
    (shiftArray s ω).1 i = ω.1 (i + s.1) := (rfl)

lemma shiftArray_snd_apply (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) (i : ℕ) (a : α) :
    (shiftArray s ω).2 i a = ω.2 (i + s.2 a) a := (rfl)

@[fun_prop]
lemma measurable_shiftArray (s : ℕ × (α → ℕ)) :
    Measurable (shiftArray (𝓤 := 𝓤) (𝓧 := 𝓧) s) :=
  (measurable_pi_iff.2 fun i ↦ (measurable_pi_apply (i + s.1)).comp measurable_fst).prodMk
    ((measurable_shiftTable s.2).comp measurable_snd)

@[simp]
lemma shiftArray_zero (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : shiftArray 0 ω = ω := (rfl)

/-- Shifting by `r`, then by `s`, is shifting by `r + s`. -/
lemma shiftArray_shiftArray (r s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
    shiftArray s (shiftArray r ω) = shiftArray (r + s) ω := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ funext fun a ↦ ?_)
  · simp only [shiftArray_fst_apply, Prod.fst_add]
    rw [add_comm r.1, add_assoc]
  · simp only [shiftArray_snd_apply, Prod.snd_add, Pi.add_apply]
    rw [add_comm (r.2 a), add_assoc]

/-- A shape is at most its sum with another shape. -/
lemma shape_le_add (r s : ℕ × (α → ℕ)) : r ≤ r + s :=
  ⟨Nat.le_add_right _ _, fun _ ↦ Nat.le_add_right _ _⟩

/-- The points `ω` and `ω'` have the same entries below the shape `s`: the same first `s.1` seeds
and, for each source `a`, the same first `s.2 a` observations. -/
def AgreeBelow (s : ℕ × (α → ℕ)) (ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : Prop :=
  (∀ i < s.1, ω.1 i = ω'.1 i) ∧ ∀ a, ∀ i < s.2 a, ω.2 i a = ω'.2 i a

lemma agreeBelow_iff {s : ℕ × (α → ℕ)} {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)} :
    AgreeBelow s ω ω' ↔ (∀ i < s.1, ω.1 i = ω'.1 i) ∧ ∀ a, ∀ i < s.2 a, ω.2 i a = ω'.2 i a :=
  Iff.rfl

lemma AgreeBelow.refl (s : ℕ × (α → ℕ)) (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : AgreeBelow s ω ω :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

lemma AgreeBelow.symm {s : ℕ × (α → ℕ)} {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)}
    (h : AgreeBelow s ω ω') : AgreeBelow s ω' ω :=
  ⟨fun i hi ↦ (h.1 i hi).symm, fun a i hi ↦ (h.2 a i hi).symm⟩

/-- Points that agree below a shape agree below every smaller shape. -/
lemma AgreeBelow.mono {r s : ℕ × (α → ℕ)} {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)}
    (h : AgreeBelow s ω ω') (hrs : r ≤ s) : AgreeBelow r ω ω' :=
  ⟨fun i hi ↦ h.1 i (hi.trans_le hrs.1), fun a i hi ↦ h.2 a i (hi.trans_le (hrs.2 a))⟩

/-- If two points agree below `r + s`, their shifts by `r` agree below `s`. -/
lemma AgreeBelow.shiftArray {r s : ℕ × (α → ℕ)} {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)}
    (h : AgreeBelow (r + s) ω ω') : AgreeBelow s (shiftArray r ω) (shiftArray r ω') := by
  refine ⟨fun i hi ↦ ?_, fun a i hi ↦ ?_⟩
  · rw [shiftArray_fst_apply, shiftArray_fst_apply]
    exact h.1 _ (by simp only [Prod.fst_add]; omega)
  · rw [shiftArray_snd_apply, shiftArray_snd_apply]
    exact h.2 a _ (by simp only [Prod.snd_add, Pi.add_apply]; omega)

/-- **Restart at a fixed shape.** Under `arrayLaw ρ ν`, a function of the entries below a shape
`s` is independent of the seeds and the table after `s`, which have the law `arrayLaw ρ ν`: the
expectation of the product is the product of the expectations. -/
lemma lintegral_mul_comp_shiftArray (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] {s : ℕ × (α → ℕ)}
    {f g : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞} (hf : Measurable f)
    (hfs : ∀ ω ω', AgreeBelow s ω ω' → f ω = f ω') (hg : Measurable g) :
    ∫⁻ ω, f ω * g (shiftArray s ω) ∂arrayLaw ρ ν =
      (∫⁻ ω, f ω ∂arrayLaw ρ ν) * ∫⁻ ω, g ω ∂arrayLaw ρ ν := by
  rw [arrayLaw_def]
  set Pu := Measure.infinitePi fun _ : ℕ ↦ ρ
  set Pt := Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν
  -- integrate over the table first
  have h_inner (u : ℕ → 𝓤) :
      ∫⁻ x, f (u, x) * g ((shift 𝓤)^[s.1] u, shiftTable s.2 x) ∂Pt =
        (∫⁻ x, f (u, x) ∂Pt) * ∫⁻ x, g ((shift 𝓤)^[s.1] u, x) ∂Pt :=
    lintegral_mul_comp_shiftTable ν (g := fun x ↦ g ((shift 𝓤)^[s.1] u, x))
      (hf.comp (measurable_const.prodMk measurable_id))
      (fun x x' h ↦ hfs _ _ ⟨fun _ _ ↦ rfl, h⟩) (hg.comp (measurable_const.prodMk measurable_id))
  have hF : Measurable fun u ↦ ∫⁻ x, f (u, x) ∂Pt := hf.lintegral_prod_right'
  have hG : Measurable fun u ↦ ∫⁻ x, g (u, x) ∂Pt := hg.lintegral_prod_right'
  have hFs : DependsOn (fun u ↦ ∫⁻ x, f (u, x) ∂Pt) (Set.Iio s.1) := fun u u' h ↦
    lintegral_congr fun x ↦ hfs _ _ ⟨fun i hi ↦ h i hi, fun _ _ _ ↦ rfl⟩
  rw [lintegral_prod (fun ω ↦ f ω * g (shiftArray s ω))
      ((hf.mul (hg.comp (measurable_shiftArray s))).aemeasurable),
    lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable]
  simp only [shiftArray_eq_shift_iterate, h_inner]
  exact lintegral_mul_comp_shift_iterate ρ hF hFs hG


/-! ### Functions determined by the entries below a random shape -/

section IsReadBy

variable {β γ : Type*} {σ τ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)}
  {f : (ℕ → 𝓤) × (ℕ → α → 𝓧) → β}

/-- The function `f` is determined by the entries below the random shape `σ`: every point `ω'`
with the same entries as `ω` below the shape `σ ω` has `f ω' = f ω`. For `f = σ`, this says that
the shape `σ` is a stopping point of the filtration of the seeds and the tables indexed by the
shapes. A bandit algorithm that stops after reading the entries below `σ` and outputs `f` gives
such a pair. -/
def IsReadBy (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ))
    (f : (ℕ → 𝓤) × (ℕ → α → 𝓧) → β) : Prop :=
  ∀ ω ω', AgreeBelow (σ ω) ω ω' → f ω' = f ω

lemma isReadBy_iff : IsReadBy σ f ↔ ∀ ω ω', AgreeBelow (σ ω) ω ω' → f ω' = f ω := Iff.rfl

/-- A function determined by the entries below `σ` takes the same value at two points that agree
below the shape `σ ω`. -/
lemma IsReadBy.eq_of_agreeBelow (hf : IsReadBy σ f) {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)}
    (h : AgreeBelow (σ ω) ω ω') : f ω' = f ω :=
  hf ω ω' h

lemma isReadBy_const (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) (b : β) :
    IsReadBy σ fun _ ↦ b := fun _ _ _ ↦ rfl

/-- A function determined by the entries below a random shape is determined by the entries below
every larger random shape. -/
lemma IsReadBy.mono (hf : IsReadBy σ f) (hστ : ∀ ω, σ ω ≤ τ ω) : IsReadBy τ f :=
  fun ω ω' h ↦ hf ω ω' (h.mono (hστ ω))

lemma IsReadBy.comp (hf : IsReadBy σ f) (φ : β → γ) : IsReadBy σ fun ω ↦ φ (f ω) :=
  fun ω ω' h ↦ congrArg φ (hf ω ω' h)

lemma IsReadBy.prodMk {g : (ℕ → 𝓤) × (ℕ → α → 𝓧) → γ} (hf : IsReadBy σ f)
    (hg : IsReadBy σ g) : IsReadBy σ fun ω ↦ (f ω, g ω) :=
  fun ω ω' h ↦ Prod.ext (hf ω ω' h) (hg ω ω' h)

/-- If the random shape `τ` is determined by the entries below itself and `f` by the entries
below `σ`, then `f` read after `τ` is determined by the entries below `τ`, followed by `σ` read
after `τ`. -/
lemma IsReadBy.comp_shiftArray (hτ : IsReadBy τ τ) (hf : IsReadBy σ f) :
    IsReadBy (fun ω ↦ τ ω + σ (shiftArray (τ ω) ω)) fun ω ↦ f (shiftArray (τ ω) ω) := by
  intro ω ω' h
  have hτ' : τ ω' = τ ω := hτ ω ω' (h.mono (shape_le_add _ _))
  simp only [hτ']
  exact hf _ _ h.shiftArray

/-- Whether a random shape determined by the entries below itself takes the value `r`, and then
the value of a function determined by the entries below it, are determined by the entries below
`r`. -/
lemma IsReadBy.indicator_eq_of_agreeBelow [Zero β] (hσ : IsReadBy σ σ) (hf : IsReadBy σ f)
    {r : ℕ × (α → ℕ)} {ω ω' : (ℕ → 𝓤) × (ℕ → α → 𝓧)} (h : AgreeBelow r ω ω') :
    {ω | σ ω = r}.indicator f ω = {ω | σ ω = r}.indicator f ω' := by
  by_cases hω : σ ω = r
  · have hω' : σ ω' = r := (hσ ω ω' (hω ▸ h)).trans hω
    rw [Set.indicator_of_mem (s := {ω | σ ω = r}) hω,
      Set.indicator_of_mem (s := {ω | σ ω = r}) hω', hf ω ω' (hω ▸ h)]
  · have hω' : ¬ σ ω' = r := fun hω' ↦ hω ((hσ ω' ω (hω' ▸ h.symm)).trans hω')
    rw [Set.indicator_of_notMem (s := {ω | σ ω = r}) hω,
      Set.indicator_of_notMem (s := {ω | σ ω = r}) hω']

end IsReadBy

/-! ### Restart at a random shape -/

section Restart

variable [Finite α] {R : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)}

/-- The seeds and the table after a measurable random shape are measurable. -/
lemma measurable_shiftArray_apply (hRm : Measurable R) :
    Measurable fun ω ↦ shiftArray (R ω) ω :=
  (measurable_from_prod_countable_left (f := fun p : _ × (ℕ × (α → ℕ)) ↦ shiftArray p.2 p.1)
    fun r ↦ measurable_shiftArray r).comp (measurable_id.prodMk hRm)

/-- **Restart at a random shape.** Under `arrayLaw ρ ν`, let the random shape `R` be determined
by the entries below itself. A function of the entries below `R` is independent of the seeds and
the table after `R`, which have the law `arrayLaw ρ ν`: the expectation of the product is the
product of the expectations. -/
lemma lintegral_mul_comp_shiftArray_of_isReadBy (ρ : Measure 𝓤)
    [IsProbabilityMeasure ρ] (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)]
    (hRm : Measurable R) (hR : IsReadBy R R) {f g : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞}
    (hf : Measurable f) (hfR : IsReadBy R f) (hg : Measurable g) :
    ∫⁻ ω, f ω * g (shiftArray (R ω) ω) ∂arrayLaw ρ ν =
      (∫⁻ ω, f ω ∂arrayLaw ρ ν) * ∫⁻ ω, g ω ∂arrayLaw ρ ν := by
  have hRr (r : ℕ × (α → ℕ)) : MeasurableSet {ω | R ω = r} := hRm (measurableSet_singleton r)
  have hfr (r : ℕ × (α → ℕ)) : Measurable ({ω | R ω = r}.indicator f) := hf.indicator (hRr r)
  -- decompose along the value of the random shape
  have h_sum (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : ∑' r, {ω | R ω = r}.indicator f ω = f ω := by
    rw [tsum_eq_single (R ω) fun r hr ↦
        Set.indicator_of_notMem (s := {ω | R ω = r}) (fun h : R ω = r ↦ hr h.symm) _,
      Set.indicator_of_mem (s := {ω' | R ω' = R ω}) rfl]
  have h_sum' (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
      ∑' r, {ω | R ω = r}.indicator f ω * g (shiftArray r ω) = f ω * g (shiftArray (R ω) ω) := by
    rw [tsum_eq_single (R ω) fun r hr ↦ by
        rw [Set.indicator_of_notMem (s := {ω | R ω = r}) (fun h : R ω = r ↦ hr h.symm),
          zero_mul],
      Set.indicator_of_mem (s := {ω' | R ω' = R ω}) rfl]
  calc ∫⁻ ω, f ω * g (shiftArray (R ω) ω) ∂arrayLaw ρ ν
  _ = ∑' r, ∫⁻ ω, {ω | R ω = r}.indicator f ω * g (shiftArray r ω) ∂arrayLaw ρ ν := by
    rw [← lintegral_tsum (f := fun r ω ↦ {ω | R ω = r}.indicator f ω * g (shiftArray r ω))
      fun r ↦ ((hfr r).mul (hg.comp (measurable_shiftArray r))).aemeasurable]
    exact lintegral_congr fun ω ↦ (h_sum' ω).symm
  _ = ∑' r, (∫⁻ ω, {ω | R ω = r}.indicator f ω ∂arrayLaw ρ ν) * ∫⁻ ω, g ω ∂arrayLaw ρ ν :=
    tsum_congr fun r ↦ lintegral_mul_comp_shiftArray ρ ν (hfr r)
      (fun ω ω' h ↦ hR.indicator_eq_of_agreeBelow hfR h) hg
  _ = (∫⁻ ω, f ω ∂arrayLaw ρ ν) * ∫⁻ ω, g ω ∂arrayLaw ρ ν := by
    rw [ENNReal.tsum_mul_right, ← lintegral_tsum (f := fun r ω ↦ {ω | R ω = r}.indicator f ω)
      fun r ↦ (hfr r).aemeasurable]
    simp_rw [h_sum]

/-- The seeds and the table after a random shape determined by the entries below itself have the
law `arrayLaw ρ ν`. -/
lemma map_shiftArray_of_isReadBy (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] (hRm : Measurable R)
    (hR : IsReadBy R R) :
    (arrayLaw ρ ν).map (fun ω ↦ shiftArray (R ω) ω) = arrayLaw ρ ν := by
  ext B hB
  rw [Measure.map_apply (measurable_shiftArray_apply hRm) hB, ← lintegral_indicator_one hB,
    ← lintegral_indicator_one (measurable_shiftArray_apply hRm hB)]
  have h := lintegral_mul_comp_shiftArray_of_isReadBy ρ ν hRm hR (f := fun _ ↦ 1)
    measurable_const (isReadBy_const R 1) (measurable_one.indicator hB)
  simp only [one_mul, lintegral_const, measure_univ] at h
  rw [← h]
  exact lintegral_congr fun ω ↦ rfl

/-- Under `arrayLaw ρ ν`, a function of the entries below a random shape `R` determined by the
entries below itself is independent of every function of the seeds and the table after `R`. -/
lemma indepFun_comp_shiftArray_of_isReadBy {β γ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (ρ : Measure 𝓤) [IsProbabilityMeasure ρ] (ν : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (ν a)] (hRm : Measurable R) (hR : IsReadBy R R)
    {f : (ℕ → 𝓤) × (ℕ → α → 𝓧) → β} {g : (ℕ → 𝓤) × (ℕ → α → 𝓧) → γ} (hf : Measurable f)
    (hfR : IsReadBy R f) (hg : Measurable g) :
    IndepFun f (fun ω ↦ g (shiftArray (R ω) ω)) (arrayLaw ρ ν) := by
  classical
  refine indepFun_iff_measure_inter_preimage_eq_mul.2 fun A B hA hB ↦ ?_
  have hΘ := measurable_shiftArray_apply hRm
  have h := lintegral_mul_comp_shiftArray_of_isReadBy ρ ν hRm hR
    (f := (f ⁻¹' A).indicator 1) (g := (g ⁻¹' B).indicator 1)
    (measurable_one.indicator (hf hA))
    (fun ω ω' h ↦ by
      simp only [Set.indicator_apply, Set.mem_preimage, hfR ω ω' h, Pi.one_apply])
    (measurable_one.indicator (hg hB))
  rw [lintegral_indicator_one (hf hA), lintegral_indicator_one (hg hB)] at h
  have hB' : (fun ω ↦ g (shiftArray (R ω) ω)) ⁻¹' B =
      (fun ω ↦ shiftArray (R ω) ω) ⁻¹' (g ⁻¹' B) := rfl
  rw [hB', ← Measure.map_apply hΘ (hg hB) (μ := arrayLaw ρ ν),
    map_shiftArray_of_isReadBy ρ ν hRm hR, ← h,
    ← lintegral_indicator_one ((hf hA).inter (hΘ (hg hB)))]
  refine lintegral_congr fun ω ↦ ?_
  rw [Set.inter_indicator_one]
  rfl

end Restart



/-! ### The table of a fixed size -/

/-- The first `n a` observations of each source `a`, read in the table of all the observations,
as a point of `(Σ a, Fin (n a)) → 𝓧`. -/
def tableOfArray (n : α → ℕ) (x : ℕ → α → 𝓧) : (Σ a, Fin (n a)) → 𝓧 := fun p ↦ x p.2 p.1

lemma tableOfArray_apply (n : α → ℕ) (x : ℕ → α → 𝓧) (p : Σ a, Fin (n a)) :
    tableOfArray n x p = x p.2 p.1 :=
  (rfl)

@[fun_prop]
lemma measurable_tableOfArray (n : α → ℕ) : Measurable (tableOfArray (𝓧 := 𝓧) n) :=
  measurable_pi_iff.2 fun p ↦ (measurable_pi_apply p.1).comp (measurable_pi_apply (p.2 : ℕ))

/-- The first `n a` observations of each source `a` are independent, those of the source `a` with
law `ν a`. -/
lemma map_tableOfArray [Fintype α] (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)]
    (n : α → ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ Measure.infinitePi ν).map (tableOfArray n) =
      Measure.pi fun p : Σ a, Fin (n a) ↦ ν p.1 := by
  set C := MeasurableEquiv.curry ℕ α 𝓧
  have hφ : Function.Injective fun p : Σ a, Fin (n a) ↦ ((p.2 : ℕ), p.1) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    rw [Fin.ext h1]
  have h_comp : tableOfArray n ∘ C = fun (y : ℕ × α → 𝓧) p ↦ y ((p.2 : ℕ), p.1) := rfl
  rw [← Measure.infinitePi_map_curry (fun (_ : ℕ) (a : α) ↦ ν a),
    Measure.map_map (measurable_tableOfArray n) C.measurable, h_comp,
    Measure.map_infinitePi_infinitePi_of_inj (P := fun p : ℕ × α ↦ ν p.2) hφ,
    Measure.infinitePi_eq_pi]

/-! ### Restarting a round on the entries not yet read -/

section Rounds

variable {β : Type*} {σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)}
  {V : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℝ≥0∞}

/-- The entries read by the first `j` rounds, when a round that reads the entries below `σ ω` is
restarted, each time it ends, on the seeds and the observations that the previous rounds have not
read. -/
def restartShape (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) :
    ℕ → (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)
  | 0 => fun _ ↦ 0
  | j + 1 => fun ω ↦ restartShape σ j ω + σ (shiftArray (restartShape σ j ω) ω)

/-- The point at which the round of index `j` starts: the seeds and the table after the entries
read by the first `j` rounds. -/
def restartPoint (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) (j : ℕ)
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : (ℕ → 𝓤) × (ℕ → α → 𝓧) :=
  shiftArray (restartShape σ j ω) ω

@[simp]
lemma restartShape_zero (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ))
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : restartShape σ 0 ω = 0 := (rfl)

lemma restartShape_succ (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) (j : ℕ)
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
    restartShape σ (j + 1) ω = restartShape σ j ω + σ (restartPoint σ j ω) := (rfl)

lemma restartPoint_def (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) (j : ℕ)
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) :
    restartPoint σ j ω = shiftArray (restartShape σ j ω) ω := (rfl)

/-- The entries read by the first rounds increase with the number of rounds. -/
lemma monotone_restartShape (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ))
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) : Monotone fun j ↦ restartShape σ j ω :=
  monotone_nat_of_le_succ fun _ ↦ shape_le_add _ _

/-- The number of observations of a source read by `j + 1` rounds. -/
lemma restartShape_succ_snd (σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)) (j : ℕ)
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) (a : α) :
    (restartShape σ (j + 1) ω).2 a = (restartShape σ j ω).2 a + (σ (restartPoint σ j ω)).2 a :=
  (rfl)

/-- If a round reads at most `K` observations of each source, `j` rounds read at most `j * K`. -/
lemma restartShape_snd_le {K : ℕ} (hσK : ∀ ω a, (σ ω).2 a ≤ K) (j : ℕ)
    (ω : (ℕ → 𝓤) × (ℕ → α → 𝓧)) (a : α) : (restartShape σ j ω).2 a ≤ j * K := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [restartShape_succ_snd, Nat.succ_mul]
    exact Nat.add_le_add ih (hσK _ a)

/-- The entries read by the first `j` rounds are determined by these entries. -/
lemma isReadBy_restartShape (hσ : IsReadBy σ σ) (j : ℕ) :
    IsReadBy (restartShape σ j) (restartShape σ j) := by
  induction j with
  | zero => exact isReadBy_const _ _
  | succ j ih =>
    intro ω ω' h
    have h1 : restartShape σ j ω' = restartShape σ j ω :=
      ih ω ω' (h.mono (shape_le_add _ _))
    have h2 : σ (shiftArray (restartShape σ j ω') ω') = σ (shiftArray (restartShape σ j ω) ω) :=
      ih.comp_shiftArray hσ ω ω' h
    rw [restartShape_succ, restartShape_succ, restartPoint_def, restartPoint_def, h2, h1]

/-- A function of the round of index `i`, determined by the entries that this round reads, is
determined by the entries read by the first `j` rounds, for `i < j`. -/
lemma isReadBy_restartShape_comp_restartPoint (hσ : IsReadBy σ σ)
    {f : (ℕ → 𝓤) × (ℕ → α → 𝓧) → β} (hf : IsReadBy σ f) {i j : ℕ} (hij : i < j) :
    IsReadBy (restartShape σ j) fun ω ↦ f (restartPoint σ i ω) :=
  IsReadBy.mono (σ := restartShape σ (i + 1)) ((isReadBy_restartShape hσ i).comp_shiftArray hf)
    fun ω ↦ monotone_restartShape σ ω (Nat.succ_le_of_lt hij)

/-- The product of the payoffs of the first `j` rounds is determined by the entries that these
rounds read. -/
lemma isReadBy_prod_restartPoint (hσ : IsReadBy σ σ) (hV : IsReadBy σ V) (j : ℕ) :
    IsReadBy (restartShape σ j) fun ω ↦ ∏ i ∈ Finset.range j, V (restartPoint σ i ω) :=
  fun ω ω' h ↦
  Finset.prod_congr rfl fun _ hi ↦
    isReadBy_restartShape_comp_restartPoint hσ hV (Finset.mem_range.1 hi) ω ω' h

variable [Finite α]

@[fun_prop]
lemma measurable_restartShape (hσm : Measurable σ) (j : ℕ) : Measurable (restartShape σ j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have h := hσm.comp (measurable_shiftArray_apply ih)
    refine Measurable.prodMk (ih.fst.add h.fst) (measurable_pi_iff.2 fun a ↦ ?_)
    exact ((measurable_pi_apply a).comp ih.snd).add ((measurable_pi_apply a).comp h.snd)

@[fun_prop]
lemma measurable_restartPoint (hσm : Measurable σ) (j : ℕ) : Measurable (restartPoint σ j) :=
  measurable_shiftArray_apply (measurable_restartShape hσm j)

/-- The point at which each round starts has the law `arrayLaw ρ ν`. -/
lemma map_restartPoint (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] (hσm : Measurable σ)
    (hσ : IsReadBy σ σ) (j : ℕ) :
    (arrayLaw ρ ν).map (restartPoint σ j) = arrayLaw ρ ν :=
  map_shiftArray_of_isReadBy ρ ν (measurable_restartShape hσm j) (isReadBy_restartShape hσ j)

/-- If the payoff of a round has expectation at most `1`, so has the product of the payoffs of
the first `j` rounds. -/
lemma lintegral_prod_restartPoint_le_one (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (ν a)] (hσm : Measurable σ)
    (hσ : IsReadBy σ σ) (hVm : Measurable V) (hV : IsReadBy σ V)
    (h_null : ∫⁻ ω, V ω ∂arrayLaw ρ ν ≤ 1) (j : ℕ) :
    ∫⁻ ω, ∏ i ∈ Finset.range j, V (restartPoint σ i ω) ∂arrayLaw ρ ν ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp_rw [Finset.prod_range_succ, restartPoint_def σ j]
    rw [lintegral_mul_comp_shiftArray_of_isReadBy ρ ν (measurable_restartShape hσm j)
      (isReadBy_restartShape hσ j) (f := fun ω ↦ ∏ i ∈ Finset.range j, V (restartPoint σ i ω))
      (Finset.measurable_fun_prod _ fun i _ ↦ hVm.comp (measurable_restartPoint hσm i))
      (isReadBy_prod_restartPoint hσ hV j) hVm]
    exact mul_le_one' ih h_null

end Rounds


/-! ### The numbers of observations read by the restarted rounds -/

section Counts

variable {σ : (ℕ → 𝓤) × (ℕ → α → 𝓧) → ℕ × (α → ℕ)}

/-- The expected number of observations of a source read by `m` rounds is `m` times that of one
round. -/
lemma integral_restartShape_snd [Finite α] (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hσm : Measurable σ) (hσ : IsReadBy σ σ) {K : ℕ}
    (hσK : ∀ ω a, (σ ω).2 a ≤ K) (m : ℕ) (a : α) :
    ∫ ω, ((restartShape σ m ω).2 a : ℝ) ∂arrayLaw ρ μ =
      m * ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hN : Measurable fun ω ↦ ((σ ω).2 a : ℝ) :=
      measurable_from_top.comp ((measurable_pi_apply a).comp hσm.snd)
    have h1 : Integrable (fun ω ↦ ((restartShape σ m ω).2 a : ℝ)) (arrayLaw ρ μ) :=
      Integrable.of_bound (measurable_from_top.comp
        ((measurable_pi_apply a).comp (measurable_restartShape hσm m).snd)).aestronglyMeasurable
        (m * K)
        (ae_of_all _ fun ω ↦ by simpa using (by exact_mod_cast restartShape_snd_le hσK m ω a :
          ((restartShape σ m ω).2 a : ℝ) ≤ m * K))
    have h2 : Integrable (fun ω ↦ ((σ (restartPoint σ m ω)).2 a : ℝ)) (arrayLaw ρ μ) :=
      Integrable.of_bound (hN.comp (measurable_restartPoint hσm m)).aestronglyMeasurable K
        (ae_of_all _ fun ω ↦ by simpa using hσK _ a)
    have h3 : ∫ ω, ((σ (restartPoint σ m ω)).2 a : ℝ) ∂arrayLaw ρ μ =
        ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ := by
      conv_rhs => rw [← map_restartPoint ρ μ hσm hσ m]
      rw [integral_map (measurable_restartPoint hσm m).aemeasurable hN.aestronglyMeasurable]
    simp_rw [restartShape_succ_snd, Nat.cast_add]
    rw [integral_add h1 h2, ih, h3]
    push_cast
    ring

/-- The variance of the number of observations of a source read by `m` rounds is `m` times that of
one round: the rounds are independent with the same law. -/
lemma variance_restartShape_snd [Finite α] (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hσm : Measurable σ) (hσ : IsReadBy σ σ) {K : ℕ}
    (hσK : ∀ ω a, (σ ω).2 a ≤ K) (m : ℕ) (a : α) :
    Var[fun ω ↦ ((restartShape σ m ω).2 a : ℝ); arrayLaw ρ μ] =
      m * Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] := by
  induction m with
  | zero =>
    have h0 : (fun ω : (ℕ → 𝓤) × (ℕ → α → 𝓧) ↦ ((restartShape σ 0 ω).2 a : ℝ)) = 0 := by
      ext ω
      simp
    rw [h0, variance_zero]
    simp
  | succ m ih =>
    have hN : Measurable fun ω ↦ ((σ ω).2 a : ℝ) :=
      measurable_from_top.comp ((measurable_pi_apply a).comp hσm.snd)
    have hS : Measurable fun ω ↦ ((restartShape σ m ω).2 a : ℝ) :=
      measurable_from_top.comp ((measurable_pi_apply a).comp (measurable_restartShape hσm m).snd)
    have h1 : MemLp (fun ω ↦ ((restartShape σ m ω).2 a : ℝ)) 2 (arrayLaw ρ μ) :=
      MemLp.of_bound hS.aestronglyMeasurable (m * K)
        (ae_of_all _ fun ω ↦ by simpa using (by exact_mod_cast restartShape_snd_le hσK m ω a :
          ((restartShape σ m ω).2 a : ℝ) ≤ m * K))
    have h2 : MemLp (fun ω ↦ ((σ (restartPoint σ m ω)).2 a : ℝ)) 2 (arrayLaw ρ μ) :=
      MemLp.of_bound (hN.comp (measurable_restartPoint hσm m)).aestronglyMeasurable K
        (ae_of_all _ fun ω ↦ by simpa using hσK _ a)
    have h_indep : IndepFun (fun ω ↦ ((restartShape σ m ω).2 a : ℝ))
        (fun ω ↦ ((σ (restartPoint σ m ω)).2 a : ℝ)) (arrayLaw ρ μ) :=
      indepFun_comp_shiftArray_of_isReadBy ρ μ (measurable_restartShape hσm m)
        (isReadBy_restartShape hσ m) hS
        ((isReadBy_restartShape hσ m).comp fun r ↦ (r.2 a : ℝ)) hN
    have h3 : Var[fun ω ↦ ((σ (restartPoint σ m ω)).2 a : ℝ); arrayLaw ρ μ] =
        Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] := by
      conv_rhs => rw [← map_restartPoint ρ μ hσm hσ m]
      rw [variance_map hN.aemeasurable (measurable_restartPoint hσm m).aemeasurable]
      rfl
    have h_eq : (fun ω ↦ ((restartShape σ (m + 1) ω).2 a : ℝ)) =
        (fun ω ↦ ((restartShape σ m ω).2 a : ℝ)) +
          fun ω ↦ ((σ (restartPoint σ m ω)).2 a : ℝ) := by
      ext ω
      simp [restartShape_succ_snd]
    rw [h_eq, IndepFun.variance_add h1 h2 h_indep, ih, h3]
    push_cast
    ring

/-- **The restarted rounds fit in a table proportional to their mean.** Let a round read at most
`K` observations of each source, and `x a` of the source `a` in expectation. If the shape `n` has
`n a ≥ m (x a + ε)` for every source with `x a ≠ 0`, then `m` rounds read more than `n a`
observations of some source `a` with probability at most `|α| K² / (m ε²)`. -/
lemma measureReal_not_restartShape_le [Fintype α] (ρ : Measure 𝓤) [IsProbabilityMeasure ρ]
    (μ : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)] (hσm : Measurable σ)
    (hσ : IsReadBy σ σ) {K : ℕ} (hσK : ∀ ω a, (σ ω).2 a ≤ K) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) {n : α → ℕ}
    (hn : ∀ a, ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ ≠ 0 →
      m * (∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ + ε) ≤ n a) :
    (arrayLaw ρ μ).real {ω | ¬ (restartShape σ m ω).2 ≤ n} ≤
      Fintype.card α * (K : ℝ) ^ 2 / (m * ε ^ 2) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hN (a : α) : Measurable fun ω ↦ ((σ ω).2 a : ℝ) :=
    measurable_from_top.comp ((measurable_pi_apply a).comp hσm.snd)
  have hx0 (a : α) : 0 ≤ ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ :=
    integral_nonneg fun ω ↦ Nat.cast_nonneg _
  have hxK (a : α) : ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ ≤ K := by
    have h := integral_mono (μ := arrayLaw ρ μ)
      (Integrable.of_bound (hN a).aestronglyMeasurable K
        (ae_of_all _ fun ω ↦ by simpa using hσK ω a))
      (integrable_const (K : ℝ)) fun ω ↦ by exact_mod_cast hσK ω a
    simpa using h
  -- the bound for each source, by Chebyshev's inequality
  have h_source (a : α) : arrayLaw ρ μ {ω | n a < (restartShape σ m ω).2 a} ≤
      ENNReal.ofReal ((K : ℝ) ^ 2 / (m * ε ^ 2)) := by
    have hL2 : MemLp (fun ω ↦ ((restartShape σ m ω).2 a : ℝ)) 2 (arrayLaw ρ μ) :=
      MemLp.of_bound (measurable_from_top.comp
        ((measurable_pi_apply a).comp (measurable_restartShape hσm m).snd)).aestronglyMeasurable
        (m * K)
        (ae_of_all _ fun ω ↦ by simpa using (by exact_mod_cast restartShape_snd_le hσK m ω a :
          ((restartShape σ m ω).2 a : ℝ) ≤ m * K))
    have h_mean := integral_restartShape_snd ρ μ hσm hσ hσK m a
    have h_var := variance_restartShape_snd ρ μ hσm hσ hσK m a
    have h_var_le : Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] ≤
        K * ∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ := by
      simpa using variance_le_mul_integral_sub (c := 0) (d := K) (hN a).aemeasurable
        (ae_of_all _ fun ω ↦ ⟨Nat.cast_nonneg _, by exact_mod_cast hσK ω a⟩)
    rcases eq_or_ne (∫ ω, ((σ ω).2 a : ℝ) ∂arrayLaw ρ μ) 0 with hxa | hxa
    · -- the round never reads the source `a`
      have hv0 : Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] = 0 := by
        rw [hxa, mul_zero] at h_var_le
        exact le_antisymm h_var_le (variance_nonneg _ _)
      have h := meas_ge_le_variance_div_sq hL2 one_pos
      rw [h_var, hv0, mul_zero, zero_div, ENNReal.ofReal_zero, h_mean, hxa, mul_zero] at h
      refine (measure_mono fun ω hω ↦ ?_).trans (h.trans bot_le)
      have h1 : (1 : ℝ) ≤ ((restartShape σ m ω).2 a : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hω)
      rw [Set.mem_ofPred_eq, sub_zero]
      exact h1.trans (le_abs_self _)
    · have hc : 0 < m * ε := by positivity
      have h := meas_ge_le_variance_div_sq hL2 hc
      rw [h_var, h_mean] at h
      refine (measure_mono fun ω hω ↦ ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
      · have h1 : (n a : ℝ) < ((restartShape σ m ω).2 a : ℝ) := by exact_mod_cast hω
        have h2 := hn a hxa
        rw [Set.mem_ofPred_eq]
        refine le_trans ?_ (le_abs_self _)
        linarith
      · have h3 : Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] ≤ (K : ℝ) ^ 2 :=
          h_var_le.trans (by nlinarith [hxK a, hx0 a, Nat.cast_nonneg (α := ℝ) K])
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h4 : (0 : ℝ) ≤ (K : ℝ) ^ 2 - Var[fun ω ↦ ((σ ω).2 a : ℝ); arrayLaw ρ μ] := by
          linarith
        nlinarith [mul_nonneg (mul_nonneg hmr.le h4) (mul_nonneg hmr.le (sq_nonneg ε))]
  -- union bound
  have h_sub : {ω | ¬ (restartShape σ m ω).2 ≤ n} ⊆
      ⋃ a, {ω | n a < (restartShape σ m ω).2 a} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Pi.le_def, not_forall, not_le] at hω
    exact Set.mem_iUnion.2 hω
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc arrayLaw ρ μ {ω | ¬ (restartShape σ m ω).2 ≤ n}
  _ ≤ ∑ a, arrayLaw ρ μ {ω | n a < (restartShape σ m ω).2 a} :=
    (measure_mono h_sub).trans (measure_iUnion_fintype_le _ _)
  _ ≤ ∑ _a : α, ENNReal.ofReal ((K : ℝ) ^ 2 / (m * ε ^ 2)) := Finset.sum_le_sum fun a _ ↦ h_source a
  _ = ENNReal.ofReal (Fintype.card α * (K : ℝ) ^ 2 / (m * ε ^ 2)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]

end Counts

end ProbabilityTheory
