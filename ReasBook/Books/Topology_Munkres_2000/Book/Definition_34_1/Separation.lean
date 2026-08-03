module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open scoped Topology

universe u v

/-- An indexed family of continuous real-valued functions separates points from closed sets
when some coordinate is positive at each chosen point and vanishes outside each prescribed
neighborhood. -/
def SeparatesPointsFromClosedSets {X : Type u} {J : Type v} [TopologicalSpace X]
    (f : J → C(X, ℝ)) : Prop :=
  ∀ x U, U ∈ 𝓝 x → ∃ j, 0 < f j x ∧ ∀ y, y ∉ U → f j y = 0

namespace SeparatesPointsFromClosedSets

/-- A family separates points from closed sets exactly when every point outside a closed set
has a coordinate that is positive at the point and vanishes on the closed set. -/
theorem iff_closedSet {X : Type u} {J : Type v} [TopologicalSpace X]
    (f : J → C(X, ℝ)) :
    SeparatesPointsFromClosedSets f ↔
      ∀ x A, IsClosed A → x ∉ A → ∃ j, 0 < f j x ∧ ∀ y ∈ A, f j y = 0 := by
  constructor
  · intro h x A hA hx
    obtain ⟨j, hjx, hj⟩ := h x Aᶜ (hA.isOpen_compl.mem_nhds hx)
    exact ⟨j, hjx, fun y hy ↦ hj y (by simpa using hy)⟩
  · intro h x U hx
    have hxU : x ∈ interior U := mem_interior_iff_mem_nhds.2 hx
    obtain ⟨j, hjx, hj⟩ := h x (interior U)ᶜ isOpen_interior.isClosed_compl
      (by simpa using hxU)
    refine ⟨j, hjx, fun y hy ↦ hj y ?_⟩
    exact fun hyU ↦ hy (interior_subset hyU)

/-- A family separating points from closed sets supplies a coordinate that is positive at a
chosen point and vanishes on any closed set not containing that point. -/
theorem closedSet {X : Type u} {J : Type v} [TopologicalSpace X] {f : J → C(X, ℝ)}
    (h : SeparatesPointsFromClosedSets f) (x : X) (A : Set X) (hA : IsClosed A)
    (hx : x ∉ A) : ∃ j, 0 < f j x ∧ ∀ y ∈ A, f j y = 0 :=
  (iff_closedSet f).1 h x A hA hx

end SeparatesPointsFromClosedSets

end
