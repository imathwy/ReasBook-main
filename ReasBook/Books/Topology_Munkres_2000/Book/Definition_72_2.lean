module

public import Topology_Munkres_2000.Book.Definition_72_2.TwoCell
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import Topology_Munkres_2000.Book.Theorem_72_1

public section

universe u v

/- Definition 72.2 (1): `IsTwoCell B` states that `B` is homeomorphic to the closed
unit disk in `EuclideanSpace ℝ (Fin 2)`. -/
#check IsTwoCell

/- Definition 72.2 (2): `TwoCell.boundary e` is the boundary of a two-cell presented
by the chosen homeomorphism `e`. -/
#check TwoCell.boundary

namespace TwoCell

/-- Definition 72.2 (3): Adjoining a two-cell presented by `e` to a closed
path-connected subspace makes the inclusion-induced map on fundamental groups surjective. -/
theorem adjoin_inclusion_surjective {B : Type u} {X : Type v}
    [TopologicalSpace B] [TopologicalSpace X] [T2Space X]
    (e : B² ≃ₜ B)
    (A : Set X) (hA_closed : IsClosed A) (hA_pathConnected : IsPathConnected A)
    (h : C(B, X)) (h_boundary : Set.MapsTo h (boundary e) A)
    (h_interior : Set.BijOn h (interior e) Aᶜ)
    (p : boundary e) :
    Function.Surjective
      (FundamentalGroup.mapOfSubtype A (boundaryMap e A h h_boundary p)) := sorry

/-- Definition 72.2 (4): For a two-cell presented by `e`, the kernel of the
inclusion-induced map is the normal closure of the attaching-loop image. -/
theorem adjoin_inclusion_ker {B : Type u} {X : Type v}
    [TopologicalSpace B] [TopologicalSpace X] [T2Space X]
    (e : B² ≃ₜ B)
    (A : Set X) (hA_closed : IsClosed A) (hA_pathConnected : IsPathConnected A)
    (h : C(B, X)) (h_boundary : Set.MapsTo h (boundary e) A)
    (h_interior : Set.BijOn h (interior e) Aᶜ)
    (p : boundary e) :
    (FundamentalGroup.mapOfSubtype A (boundaryMap e A h h_boundary p)).ker =
      Subgroup.normalClosure
        (Set.range (FundamentalGroup.map (boundaryMap e A h h_boundary) p)) := sorry

end TwoCell

end
