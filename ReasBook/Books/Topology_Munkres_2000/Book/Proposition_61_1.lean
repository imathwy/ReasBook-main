module

public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic

public section

open Set

/-- Proposition 61.1: The standard two-sphere with any one point removed is
homeomorphic to the Euclidean plane. -/
theorem puncturedTwoSphereHomeomorphicPlane (b : StandardSphere 2) :
    Nonempty (({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
  ⟨StandardSphere.puncturedHomeomorphPlane b⟩
