/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Monotonicity of the product σ-algebra

## Main statements

* `MeasurableSpace.prod_mono`: the product σ-algebra `m₁.prod m₂` is monotone in both arguments.
* `MeasurableSpace.prod_mono_left`, `MeasurableSpace.prod_mono_right`: the one-sided versions.
-/

public section

namespace MeasurableSpace

variable {α β : Type*}

/-- The product σ-algebra `m₁.prod m₂` is monotone in both arguments. -/
@[gcongr]
lemma prod_mono {m₁ m₁' : MeasurableSpace α} {m₂ m₂' : MeasurableSpace β} (h₁ : m₁ ≤ m₁')
    (h₂ : m₂ ≤ m₂') : m₁.prod m₂ ≤ m₁'.prod m₂' :=
  -- By definition, `m₁.prod m₂ = m₁.comap Prod.fst ⊔ m₂.comap Prod.snd`.
  sup_le_sup (comap_mono h₁) (comap_mono h₂)

/-- The product σ-algebra `m₁.prod m₂` is monotone in `m₁`. -/
lemma prod_mono_left {m₁ m₁' : MeasurableSpace α} (h : m₁ ≤ m₁') (m₂ : MeasurableSpace β) :
    m₁.prod m₂ ≤ m₁'.prod m₂ :=
  prod_mono h le_rfl

/-- The product σ-algebra `m₁.prod m₂` is monotone in `m₂`. -/
lemma prod_mono_right (m₁ : MeasurableSpace α) {m₂ m₂' : MeasurableSpace β} (h : m₂ ≤ m₂') :
    m₁.prod m₂ ≤ m₁.prod m₂' :=
  prod_mono le_rfl h

end MeasurableSpace
