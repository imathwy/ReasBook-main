module

public import Mathlib.Topology.Order

public section

universe u

open scoped Topology

/- Exercise 18.3 (a): For two topologies `𝒯` and `𝒯'` on `X`, the identity map
from `(X, 𝒯')` to `(X, 𝒯)` is continuous if and only if `𝒯'` is finer than `𝒯`.
In Lean's reversed order on topologies, this refinement is written `𝒯' ≤ 𝒯`.
-/
#check continuous_id_iff_le

/-- Exercise 18.3 (b): For two topologies `𝒯` and `𝒯'` on `X`, the identity map
from `(X, 𝒯')` to `(X, 𝒯)` is a homeomorphism if and only if the topologies are equal. -/
theorem isHomeomorph_id_iff_eq {X : Type u} (𝒯₁ 𝒯₂ : TopologicalSpace X) :
    Continuous[𝒯₂, 𝒯₁] id ∧ Continuous[𝒯₁, 𝒯₂] id ↔ 𝒯₂ = 𝒯₁ := by
  simp only [continuous_id_iff_le]
  constructor
  · rintro ⟨h₂₁, h₁₂⟩
    exact le_antisymm h₂₁ h₁₂
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩
