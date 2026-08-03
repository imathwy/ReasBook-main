module

public import Topology_Munkres_2000.Book.Theorem_72_1.Attachment
public import Mathlib.Topology.Homeomorph.Lemmas

public section

universe u v

/-- A topological space is a two-cell if it is homeomorphic to the closed unit disk in
`EuclideanSpace ℝ (Fin 2)`. -/
def IsTwoCell (B : Type u) [TopologicalSpace B] : Prop :=
  Nonempty (B² ≃ₜ B)

namespace IsTwoCell

/-- A chosen homeomorphism from the closed unit disk exhibits its target as a two-cell. -/
theorem ofHomeomorph {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) :
    IsTwoCell B :=
  ⟨e⟩

/-- The standard closed unit disk is a two-cell. -/
theorem standard : IsTwoCell B² :=
  ⟨Homeomorph.refl B²⟩

end IsTwoCell

namespace TwoCell

/-- The boundary presented by a chosen parametrization of a two-cell. -/
def boundary {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) : Set B :=
  e '' StandardSphere.boundary 1

/-- The interior presented by a chosen parametrization of a two-cell. -/
def interior {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) : Set B :=
  e '' ClosedUnitDisk.interior

/-- The restriction of a map from a presented two-cell to its boundary, with codomain
restricted to the subspace containing the boundary image. -/
@[expose]
def boundaryMap {B : Type u} {X : Type v} [TopologicalSpace B] [TopologicalSpace X]
    (e : B² ≃ₜ B) (A : Set X) (h : C(B, X))
    (h_boundary : Set.MapsTo h (boundary e) A) : C(boundary e, A) :=
  ⟨fun q ↦ ⟨h q, h_boundary q.property⟩,
    ((map_continuous h).comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem boundaryMap_coe {B : Type u} {X : Type v} [TopologicalSpace B] [TopologicalSpace X]
    (e : B² ≃ₜ B) (A : Set X) (h : C(B, X))
    (h_boundary : Set.MapsTo h (boundary e) A) (q : boundary e) :
    (boundaryMap e A h h_boundary q : X) = h q := by
  change h q = h q
  rfl

/-- Membership in the boundary presented by a chosen two-cell parametrization. -/
theorem mem_boundary {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) (x : B) :
    x ∈ boundary e ↔ ∃ q : StandardSphere.boundary 1, e q = x := sorry

/-- Membership in the interior presented by a chosen two-cell parametrization. -/
theorem mem_interior {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) (x : B) :
    x ∈ interior e ↔ ∃ q : ClosedUnitDisk.interior, e q = x := sorry

/-- The presented interior is the complement of the presented boundary. -/
theorem interior_eq_compl_boundary {B : Type u} [TopologicalSpace B]
    (e : B² ≃ₜ B) :
    interior e = (boundary e)ᶜ := sorry

/-- Postcomposing a two-cell parametrization transports its presented boundary by image. -/
theorem boundary_trans {B : Type u} {C : Type v} [TopologicalSpace B] [TopologicalSpace C]
    (e : B² ≃ₜ B) (f : B ≃ₜ C) :
    boundary (e.trans f) = f '' boundary e := sorry

/-- Postcomposing a two-cell parametrization transports its presented interior by image. -/
theorem interior_trans {B : Type u} {C : Type v} [TopologicalSpace B] [TopologicalSpace C]
    (e : B² ≃ₜ B) (f : B ≃ₜ C) :
    interior (e.trans f) = f '' interior e := sorry

end TwoCell

end
