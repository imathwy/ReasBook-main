module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Topology_Munkres_2000.Book.Definition_2_99_2.HomeomorphAction

public section

universe u

namespace QuotientGroup

/-- Every left-coset quotient of a topological group is homogeneous. -/
instance instIsPretransitive {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (H : Subgroup G) :
    MulAction.IsPretransitive ((G ⧸ H) ≃ₜ (G ⧸ H)) (G ⧸ H) where
  exists_smul_eq x y := by
    obtain ⟨g, rfl⟩ := mk_surjective x
    obtain ⟨k, rfl⟩ := mk_surjective y
    refine ⟨Homeomorph.smul (k * g⁻¹), ?_⟩
    simp

end QuotientGroup

/- Exercise 2.99.5 (1): Left translation induces a homeomorphism of the coset quotient,
carrying the coset represented by `x` to the coset represented by `α * x`. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) (α : G) ↦ (Homeomorph.smul α : (G ⧸ H) ≃ₜ (G ⧸ H))
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) (α x : G) ↦
      (MulAction.Quotient.smul_mk H α x :
        (Homeomorph.smul α : (G ⧸ H) ≃ₜ (G ⧸ H)) (x : G ⧸ H) = (α * x : G ⧸ H))

/- Exercise 2.99.5 (2): The left-coset quotient is a homogeneous space. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) ↦
      (inferInstance : MulAction.IsPretransitive ((G ⧸ H) ≃ₜ (G ⧸ H)) (G ⧸ H))

/- Exercise 2.99.5 (3): For a closed subgroup, singleton sets in the quotient are closed. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) [IsClosed (H : Set G)] ↦ (inferInstance : T1Space (G ⧸ H))

/- Exercise 2.99.5 (4): The quotient projection is an open map. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) ↦
      (QuotientGroup.isOpenMap_coe : IsOpenMap (QuotientGroup.mk : G → G ⧸ H))

/- Exercise 2.99.5 (5): A closed normal subgroup has a topological-group quotient. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) [IsClosed (H : Set G)] [H.Normal] ↦
      (inferInstance : T1Space (G ⧸ H))
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) [IsClosed (H : Set G)] [H.Normal] ↦
      (inferInstance : IsTopologicalGroup (G ⧸ H))
