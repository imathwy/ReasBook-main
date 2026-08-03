module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

public section

universe u v

/-- A `k`-fold covering is a surjective covering map whose fibers are all
equivalent to `Fin k`. -/
class IsKFoldCovering {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (k : outParam ℕ) (p : E → B) : Prop where
  isCoveringMap : IsCoveringMap p
  surjective : Function.Surjective p
  fiberEquiv (b : B) : Nonempty (p ⁻¹' {b} ≃ Fin k)

/-- A map is a `k`-fold covering exactly when it is a surjective covering map
and every fiber is equivalent to `Fin k`. -/
theorem isKFoldCovering_iff {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (k : ℕ) (p : E → B) :
    IsKFoldCovering k p ↔ IsCoveringMap p ∧ Function.Surjective p ∧
      ∀ b : B, Nonempty (p ⁻¹' {b} ≃ Fin k) := by
  constructor
  · intro h
    exact ⟨h.isCoveringMap, h.surjective, h.fiberEquiv⟩
  · rintro ⟨isCoveringMap, surjective, fiberEquiv⟩
    exact ⟨isCoveringMap, surjective, fiberEquiv⟩

namespace IsKFoldCovering

/-- Every fiber of a `k`-fold covering is finite. -/
instance finiteFiber {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {k : ℕ} {p : E → B} [h : IsKFoldCovering k p]
    (b : B) : Finite (p ⁻¹' {b}) := by
  let ⟨e⟩ := h.fiberEquiv b
  exact Finite.of_equiv (Fin k) e.symm

/-- Every fiber of a `k`-fold covering has cardinality `k`. -/
theorem fiberNatCard {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {k : ℕ} {p : E → B} [h : IsKFoldCovering k p]
    (b : B) : Nat.card (p ⁻¹' {b}) = k := by
  let ⟨e⟩ := h.fiberEquiv b
  exact Nat.card_eq_of_equiv_fin e

end IsKFoldCovering
