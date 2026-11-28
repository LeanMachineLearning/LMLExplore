/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import Mathlib.Probability.Process.PartitionFiltration
import LMLExplore.EValues.BipolarRate.Finite
import Statlib.Divergence.FDiv.TrimApprox
import Statlib.Divergence.KullbackLeibler.Basic
import Statlib.ForMathlib.MeasureTheory.Measure.Trim

/-!
# Countable covers of a null by pieces of large bipolar rate

The bipolar rate `bipolarRate Q S` of a probability measure `Q` against the i.i.d. null of a set
`S` of probability measures can be smaller than the smallest relative entropy `klInf Q S`. This
file shows that the gap disappears once `S` may be cut into countably many pieces: on a countably
generated measurable space, for every `c < klInf Q S`, there is a countable cover `S = ⋃ k, C k`
with `c ≤ bipolarRate Q (C k)` for every `k` [EVR26, Note 47, Theorem 4′]. On any measurable space
the same holds for every `c` below the relative entropies `klDiv (Q.trim hm) (P.trim hm)` of the
restrictions to a countably generated sub-σ-algebra `m`.

So the rate `d_σ(Q, S)`, the supremum over the countable covers `S = ⋃ k, C k` of
`⨅ k, bipolarRate Q (C k)`, which is at most `klInf Q S`, is at least the smallest relative entropy
between the restrictions to any countably generated sub-σ-algebra, and equals `klInf Q S` on a
countably generated space. It is the constant of the lower bound on the pulls of the worse arm for
the bandit algorithms that are consistent at each model, on any observation space.

## Main statements

* `ProbabilityTheory.exists_iUnion_eq_forall_le_bipolarRate_of_lt_klDiv_trim`: for a countably
  generated sub-σ-algebra `m`, a level `c` below `klDiv (Q.trim hm) (P.trim hm)` for every
  `P ∈ S` is below the bipolar rates of the pieces of a countable cover of `S`.
* `ProbabilityTheory.exists_iUnion_eq_forall_le_bipolarRate_of_lt_klInf`: on a countably
  generated space, every level below `klInf Q S` is below the bipolar rates of the pieces of a
  countable cover of `S`.

## Implementation notes

The proof is the referee's proof of [EVR26, Note 47, Theorem 4′]. The countably generated
σ-algebra `m` is the union of the filtration `countableFiltration` of finite σ-algebras, and the
relative entropies of the restrictions to the `k`-th of them increase to the relative entropy of
the restrictions to `m` (Statlib's `tendsto_fDiv_trim_of_iSup_eq`, the theorem of Gel'fand,
Yaglom and Perez and of Dobrushin). The `k`-th piece is the set of the `P ∈ S` whose restriction
to the `k`-th σ-algebra is at relative entropy more than `c` from that of `Q`. A σ-algebra with
finitely many measurable sets is a finite alphabet, on which the bipolar rate is `klInf`
(`ProbabilityTheory.bipolarRate_eq_klInf_of_finite_measurableSet`), and restricting to a
sub-σ-algebra does not increase the bipolar rate (`ProbabilityTheory.bipolarRate_trim_le`).

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and the Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and refereed
  by AI agents: Note 47, *Regret constants for one-sided models*, Theorem 4′.
-/

public section

open MeasureTheory InformationTheory Filter MeasurableSpace
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*}

/-- **Countable covers along a countably generated sub-σ-algebra** [EVR26, Note 47, Theorem 4′].
Let `m` be a countably generated sub-σ-algebra. If `c < klDiv (Q.trim hm) (P.trim hm)` for every
`P ∈ S`, then `S` is the union of countably many pieces `C k` with `c ≤ bipolarRate Q (C k)`. -/
theorem exists_iUnion_eq_forall_le_bipolarRate_of_lt_klDiv_trim {m m𝓧 : MeasurableSpace 𝓧}
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] (S : Set (Measure 𝓧))
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) [hmc : @CountablyGenerated 𝓧 m] (hm : m ≤ m𝓧) {c : ℝ≥0∞}
    (hc : ∀ P ∈ S, c < klDiv (Q.trim hm) (P.trim hm)) :
    ∃ C : ℕ → Set (Measure 𝓧), ⋃ k, C k = S ∧ ∀ k, (c : EReal) ≤ bipolarRate Q (C k) := by
  let ℱ := @countableFiltration 𝓧 m hmc
  have hℱ (k : ℕ) : ℱ k ≤ m𝓧 := (ℱ.le k).trans hm
  refine ⟨fun k ↦ {P ∈ S | c < klDiv (Q.trim (hℱ k)) (P.trim (hℱ k))}, ?_, fun k ↦ ?_⟩
  · refine (Set.iUnion_subset fun k ↦ Set.sep_subset _ _).antisymm fun P hP ↦ ?_
    have := hS P hP
    -- the relative entropies along the countable filtration increase to the one on `m`
    have h := @tendsto_fDiv_trim_of_iSup_eq 𝓧 m (Q.trim hm) (P.trim hm) klDivFun _ _ ℱ
      (@iSup_countableFiltration 𝓧 m hmc)
    simp_rw [trim_trim, ← klDiv_eq_fDiv] at h
    obtain ⟨k, hk⟩ := (h.eventually (lt_mem_nhds (hc P hP))).exists
    exact Set.mem_iUnion.2 ⟨k, hP, hk⟩
  · -- on the finite `k`-th σ-algebra, the bipolar rate of the restrictions is their `klInf`
    set C := {P ∈ S | c < klDiv (Q.trim (hℱ k)) (P.trim (hℱ k))}
    have hC (P : Measure 𝓧) (hP : P ∈ C) : IsProbabilityMeasure P := hS P hP.1
    have hCk : ∀ R ∈ (fun P ↦ P.trim (hℱ k)) '' C, @IsProbabilityMeasure 𝓧 (ℱ k) R :=
      Set.forall_mem_image.2 fun P hP ↦ have := hC P hP; inferInstance
    refine le_trans ?_ (bipolarRate_trim_le Q (fun P hP ↦ have := hC P hP; inferInstance) (hℱ k))
    rw [@bipolarRate_eq_klInf_of_finite_measurableSet 𝓧 (ℱ k) _ _ _ hCk
      (@finite_setOf_measurableSet_countableFiltration 𝓧 m hmc k)]
    refine le_klInf_iff.2 (Set.forall_mem_image.2 fun P hP ↦ ?_)
    have := hC P hP
    rw [@klIntegral_eq_klDiv 𝓧 (ℱ k) _ _ _ _ (by simp)]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hP.2.le

/-- **Countable covers on a countably generated space** [EVR26, Note 47, Theorem 4′]. On a
countably generated measurable space, for every `c < klInf Q S`, the null `S` of probability
measures is the union of countably many pieces `C k` with `c ≤ bipolarRate Q (C k)`. -/
theorem exists_iUnion_eq_forall_le_bipolarRate_of_lt_klInf {m𝓧 : MeasurableSpace 𝓧}
    [CountablyGenerated 𝓧]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] (S : Set (Measure 𝓧))
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) {c : EReal} (hc : c < klInf Q S) :
    ∃ C : ℕ → Set (Measure 𝓧), ⋃ k, C k = S ∧ ∀ k, c ≤ bipolarRate Q (C k) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact ⟨fun _ ↦ S, Set.iUnion_const S, fun _ ↦
      hc0.trans (bipolarRate_nonneg Q fun P hP ↦ (hS P hP).measure_univ.le)⟩
  rw [← EReal.coe_toENNReal hc0.le]
  refine exists_iUnion_eq_forall_le_bipolarRate_of_lt_klDiv_trim Q S hS le_rfl fun P hP ↦ ?_
  have := hS P hP
  rw [trim_eq_self, trim_eq_self, ← EReal.coe_ennreal_lt_coe_ennreal_iff,
    EReal.coe_toENNReal hc0.le, ← klIntegral_eq_klDiv (by simp)]
  exact hc.trans_le (klInf_le_klIntegral hP)

end ProbabilityTheory
