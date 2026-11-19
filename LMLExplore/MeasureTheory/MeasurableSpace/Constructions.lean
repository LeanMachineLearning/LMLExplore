/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Group.Arithmetic
public import TauCeti.MeasureTheory.MeasurableSpace.Eval

/-!
# Measurability of evaluations, initial segments of tuples, finite dependence and fibers

## Main definitions

* `MeasureTheory.initSeg n`: the first `n` terms of a sequence, as a function on `Fin n`.

## Main statements

* `MeasureTheory.measurable_div_apply`: for a finite type `α` with measurable singletons and
  `c : α → G`, the function `(p, b) ↦ c b / p b` on `(α → G) × α` is measurable.
* `MeasureTheory.measurable_eval_apply`: for a countable type `α` with measurable singletons,
  evaluating row `i` of a table `x : ι → α → β` at `a : α` is measurable in the pair `(x, a)`.
* `MeasureTheory.measurable_finInit`: the map `Fin.init` dropping the last entry of a tuple of
  length `n + 1` is measurable.
* `MeasureTheory.dependsOn_initSeg`, `MeasureTheory.dependsOn_comp_initSeg`: the initial segment
  `initSeg n`, and any function of it, only depend on the first `n` terms of a sequence.
* `MeasureTheory.exists_measurable_eq_comp_initSeg`: conversely, a measurable function of the first
  `n` terms of a sequence factors measurably through the initial segment `initSeg n`.
* `MeasurableSpace.measurableSet_comap_top_iff`: the measurable sets of the σ-algebra
  `MeasurableSpace.comap f ⊤` are the unions of fibers of `f`.
* `DependsOn.measurable_of_countable`: a function of a family of countable variables with
  measurable singletons that only depends on finitely many of them is measurable.
* `Measurable.comp_prodMk_of_le`: a function `r ω x` jointly measurable for a sub-σ-algebra of the
  ambient one and the space of `x`, evaluated at a measurable `X ω`, is measurable.
* `measurable_from_prod_of_dependsOn`: a function on a product whose first factor is a family of
  countable variables with measurable singletons is measurable if it only depends on finitely
  many of these variables and is measurable in the second factor.
-/

public section

namespace MeasureTheory

variable {α G : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α] [Div G]
  [MeasurableSpace G] [MeasurableDiv G]

/-- For a finite type `α` with measurable singletons and `c : α → G`, the function
`(p, b) ↦ c b / p b` on `(α → G) × α` is measurable. Evaluated at the weights and the action of a
round of a bandit algorithm, it is an inverse-weighted function of the action. -/
lemma measurable_div_apply (c : α → G) :
    Measurable fun z : (α → G) × α ↦ c z.2 / z.1 z.2 :=
  measurable_from_prod_countable_left fun b ↦
    (measurable_const_div (c b)).comp (measurable_pi_apply b)

omit [Finite α] in
/-- For a countable type `α` with measurable singletons, evaluating row `i` of a table
`x : ι → α → β` at `a : α` is a measurable function of the pair `(x, a)`. In the table model of a
stochastic bandit, it reads the reward of the action of round `i` from row `i` of the table. -/
lemma measurable_eval_apply [Countable α] {ι β : Type*} [MeasurableSpace β] (i : ι) :
    Measurable fun p : (ι → α → β) × α ↦ p.1 i p.2 :=
  measurable_from_prod_countable_left fun a ↦ (measurable_pi_apply a).comp (measurable_pi_apply i)

omit [Finite α] in
/-- For countable types `α`, `β` with measurable singletons on `α`, the supremum
`⨆ b, q x (o x, b)` of a measurable family `q x : α × β → γ` at a measurable first coordinate
`o x` is measurable in `x`. For random action values `q x` and a random state `o x`, it is the
largest action value at that state. -/
lemma _root_.Measurable.iSup_apply_prodMk [Countable α] {δ β γ : Type*} {mδ : MeasurableSpace δ}
    [Countable β] [MeasurableSpace γ] [TopologicalSpace γ] [ConditionallyCompleteLinearOrder γ]
    [OrderTopology γ] [SecondCountableTopology γ] [BorelSpace γ] {q : δ → α × β → γ} {o : δ → α}
    (hq : Measurable q) (ho : Measurable o) : Measurable fun x ↦ ⨆ b, q x (o x, b) :=
  (Measurable.of_eval fun a ↦ .iSup fun b ↦ (measurable_pi_apply (a, b)).comp hq).eval_index ho

/-- The map `Fin.init` dropping the last entry of a tuple of length `n + 1` is measurable. On the
histories of a sequential learning problem, it maps the history of the first `n + 1` rounds to
that of the first `n` rounds. -/
@[fun_prop]
lemma measurable_finInit {n : ℕ} {β : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (β i)] :
    Measurable (Fin.init : ((i : Fin (n + 1)) → β i) → (i : Fin n) → β i.castSucc) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- A function of a family of countable variables with measurable singletons that only depends on
finitely many of them is measurable: it factors through the restriction to these variables, whose
domain is countable. For example, a statistic of the first `N` rows of an array of samples with
finitely many keys and countably many values is a measurable function of the array. -/
lemma _root_.DependsOn.measurable_of_countable {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, Countable (X i)] [∀ i, MeasurableSingletonClass (X i)]
    {γ : Type*} [MeasurableSpace γ] {f : (Π i, X i) → γ} {s : Set ι} (hs : s.Finite)
    (hf : DependsOn f s) : Measurable f := by
  rcases isEmpty_or_nonempty (Π i, X i) with h | ⟨⟨x⟩⟩
  · exact Subsingleton.measurable
  have : Nonempty γ := ⟨f x⟩
  have : Finite s := hs.to_subtype
  obtain ⟨g, rfl⟩ := dependsOn_iff_exists_comp.1 hf
  exact (_root_.measurable_of_countable g).comp (Measurable.of_eval fun i ↦ measurable_pi_apply _)

/-- A function `f` on a product `(Π i, X i) × β`, where the `X i` are countable with measurable
singletons, is measurable if it only depends on finitely many coordinates of its first argument
and is measurable in its second argument. It factors through the restriction of the first argument
to these coordinates, whose domain is countable. This extends `measurable_from_prod_countable_right`
to such families: for example, a function of the first `N` rows of an array of samples with
finitely many keys and countably many values, and of an independent real parameter. -/
lemma _root_.measurable_from_prod_of_dependsOn {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, Countable (X i)] [∀ i, MeasurableSingletonClass (X i)]
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] {f : (Π i, X i) × β → γ} {s : Set ι}
    (hs : s.Finite) (hf : ∀ y, DependsOn (fun x ↦ f (x, y)) s)
    (hf' : ∀ x, Measurable fun y ↦ f (x, y)) : Measurable f := by
  classical
  rcases isEmpty_or_nonempty (Π i, X i) with h | ⟨⟨x₀⟩⟩
  · have : IsEmpty ((Π i, X i) × β) := Prod.isEmpty_left
    exact Subsingleton.measurable
  have : Finite s := hs.to_subtype
  -- `f` factors through the restriction of the first argument to `s`, whose domain is countable
  set e : (Π i : s, X i) → Π i, X i := fun u i ↦ if h : i ∈ s then u ⟨i, h⟩ else x₀ i
  have h : f = (fun z : (Π i : s, X i) × β ↦ f (e z.1, z.2)) ∘
      fun z ↦ (fun i : s ↦ z.1 i, z.2) := by
    ext z
    exact (hf z.2 fun i hi ↦ by simp [e, hi]).symm
  rw [h]
  exact (measurable_from_prod_countable_right (f := fun z : (Π i : s, X i) × β ↦ f (e z.1, z.2))
    fun u ↦ hf' (e u)).comp
    ((measurable_pi_iff.2 fun i ↦ (measurable_pi_apply _).comp measurable_fst).prodMk
      measurable_snd)

/-- The sets that are measurable for the σ-algebra `MeasurableSpace.comap f ⊤` pulled back by a
map `f` are the unions of fibers of `f`: the sets that contain, with each point, every point with
the same image. -/
lemma _root_.MeasurableSpace.measurableSet_comap_top_iff {α β : Type*} {f : α → β} {s : Set α} :
    MeasurableSet[MeasurableSpace.comap f ⊤] s ↔ ∀ a a', f a = f a' → (a ∈ s ↔ a' ∈ s) := by
  refine ⟨fun ⟨u, _, hu⟩ a a' h ↦ by simp [← hu, h], fun h ↦ ⟨f '' s, trivial, ?_⟩⟩
  ext a
  exact ⟨fun ⟨a', ha', he⟩ ↦ (h a' a he).1 ha', fun ha ↦ ⟨a, ha, rfl⟩⟩

/-- A function `r ω x` that is jointly measurable for a sub-σ-algebra `m ≤ mΩ` and `m𝓧`, evaluated
at a measurable `X ω`, is measurable: `ω ↦ r ω (X ω)` is the composite of `uncurry r` with the
measurable map `ω ↦ (ω, X ω)`. -/
lemma _root_.Measurable.comp_prodMk_of_le {Ω 𝓧 β : Type*} {m mΩ : MeasurableSpace Ω}
    {m𝓧 : MeasurableSpace 𝓧} [MeasurableSpace β] {r : Ω → 𝓧 → β} {X : Ω → 𝓧}
    (hr : Measurable[m.prod m𝓧] (Function.uncurry r)) (hm : m ≤ mΩ) (hX : Measurable X) :
    Measurable fun ω ↦ r ω (X ω) :=
  hr.comp ((measurable_id'' hm).prodMk hX)

/-! ### The first terms of a sequence -/

section InitSeg

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The first `n` terms of a sequence. -/
def initSeg (n : ℕ) (ω : ℕ → 𝓧) : Fin n → 𝓧 := fun i ↦ ω i

/-- The initial segment of length `n` restricts a sequence to its first `n` indices. -/
lemma initSeg_def (n : ℕ) : initSeg (𝓧 := 𝓧) n = fun ω i ↦ ω i := (rfl)

/-- The coordinates of the initial segment are the first coordinates of the sequence. -/
@[simp]
lemma initSeg_apply (n : ℕ) (ω : ℕ → 𝓧) (i : Fin n) : initSeg n ω i = ω i := (rfl)

/-- The initial segment is a measurable function of the sequence. -/
@[fun_prop]
lemma measurable_initSeg (n : ℕ) : Measurable (initSeg (𝓧 := 𝓧) n) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- The initial segment of length `n` only depends on the first `n` terms of the sequence. -/
lemma dependsOn_initSeg (n : ℕ) : DependsOn (initSeg (𝓧 := 𝓧) n) (Set.Iio n) :=
  fun _ _ h ↦ funext fun i ↦ h i i.isLt

/-- A function of the initial segment of length `n` only depends on the first `n` terms of the
sequence. -/
lemma dependsOn_comp_initSeg {β : Type*} {n : ℕ} (g : (Fin n → 𝓧) → β) :
    DependsOn (g ∘ initSeg n) (Set.Iio n) :=
  fun _ _ h ↦ congrArg g (dependsOn_initSeg n h)

/-- A measurable function of the first `n` terms of a sequence is a measurable function of the
initial segment of length `n`. -/
lemma exists_measurable_eq_comp_initSeg [Nonempty 𝓧] {β : Type*} [MeasurableSpace β]
    {f : (ℕ → 𝓧) → β} {n : ℕ} (hf : Measurable f) (hfn : DependsOn f (Set.Iio n)) :
    ∃ g : (Fin n → 𝓧) → β, Measurable g ∧ f = g ∘ initSeg n := by
  classical
  -- extend a finite sequence by a constant
  let x₀ : 𝓧 := Classical.arbitrary 𝓧
  let ext : (Fin n → 𝓧) → ℕ → 𝓧 := fun y i ↦ if h : i < n then y ⟨i, h⟩ else x₀
  have hext : Measurable ext := by
    refine Measurable.of_eval fun i ↦ ?_
    by_cases h : i < n
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_const
  refine ⟨f ∘ ext, hf.comp hext, funext fun ω ↦ hfn fun i hi ↦ ?_⟩
  simp only [Set.mem_Iio] at hi
  simp [ext, hi]

end InitSeg

end MeasureTheory
