module

import Mathlib.Topology.Homotopy.Path

universe u

/- Notation 51.1: If `f` is a path, `⟦f⟧` denotes its path-homotopy
equivalence class relative to its endpoints. -/
#check fun {X : Type u} [TopologicalSpace X] {x₀ x₁ : X} (f : Path x₀ x₁) ↦
  (⟦f⟧ : Path.Homotopic.Quotient x₀ x₁)
