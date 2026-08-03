module

public import Topology_Munkres_2000.Book.Theorem_62_1.GraphHomology
public import Topology_Munkres_2000.Book.Theorem_62_1.OpenCoverComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

public section

namespace InvarianceOfDomainSupport

open Simplicial

-- Route correction: use relative open stars of every outside face, rather than
-- closed top-cell carriers that miss lower-dimensional complement points.

/-- Helper for Theorem 62.1: the realization of a standard simplicial boundary
with the realized range of a subcomplex removed. -/
abbrev boundaryRealizationComplement (n : ℕ)
    (K : (SSet.boundary (n + 1)).toSSet.Subcomplex) :=
  {x : |(SSet.boundary (n + 1)).toSSet| //
    x ∉ Set.range (SSet.toTop.map K.ι)}

/-- Helper for Theorem 62.1: an open-star cover of a realized boundary
complement, indexed by all nondegenerate simplices outside the subcomplex. -/
structure BoundaryComplementOpenStarModel (n : ℕ)
    (K : (SSet.boundary (n + 1)).toSSet.Subcomplex) where
  /-- The relative open star attached to an outside nondegenerate simplex. -/
  U : K.N → Set (boundaryRealizationComplement n K)
  /-- Every relative star is open in the realized complement. -/
  isOpen_U : ∀ s, IsOpen (U s)
  /-- Every relative star is path-connected. -/
  isPathConnected_U : ∀ s, IsPathConnected (U s)
  /-- The relative stars cover the entire realized complement. -/
  iUnion_U : ⋃ s, U s = Set.univ
  /-- Two relative stars intersect exactly when their indexing faces are comparable. -/
  inter_nonempty_iff (s t : K.N) :
    (U s ∩ U t).Nonempty ↔ s ≤ t ∨ t ≤ s

/-- Helper for Theorem 62.1: the graph joining comparable nondegenerate faces
outside a boundary subcomplex. -/
abbrev outsideFaceComparabilityGraph {n : ℕ}
    (K : (SSet.boundary (n + 1)).toSSet.Subcomplex) : SimpleGraph K.N :=
  SimpleGraph.fromRel fun s t : K.N ↦ s ≤ t ∨ t ≤ s

/-- Helper for Theorem 62.1: every standard simplicial boundary has finitely
many nondegenerate simplices. -/
lemma finiteBoundaryToSSet (n : ℕ) : (SSet.boundary n).toSSet.Finite := by
  -- Use the boundary dimension bound and finiteness of each standard-simplex degree.
  apply SSet.finite_of_hasDimensionLT _ n
  intro i _
  infer_instance

/-- Helper for Theorem 62.1: the nondegenerate faces outside any subcomplex of a
standard boundary form a finite type. -/
lemma finiteOutsideBoundarySubcomplexFaces {n : ℕ}
    (K : (SSet.boundary (n + 1)).toSSet.Subcomplex) : Finite K.N := by
  -- Forgetting the nonmembership proof injects outside faces into the finite ambient faces.
  letI : (SSet.boundary (n + 1)).toSSet.Finite := finiteBoundaryToSSet (n + 1)
  exact Finite.of_injective SSet.Subcomplex.N.toN
    (fun x y h ↦ (SSet.Subcomplex.N.ext_iff x y).mpr h)

/-- Helper for Theorem 62.1: reduced mod-two incidence homology of the finite
outside-face comparability graph, with its finite data chosen canonically. -/
noncomputable abbrev outsideFaceGraphReducedHomologyZeroModTwo {n : ℕ}
    (K : (SSet.boundary (n + 1)).toSSet.Subcomplex) :=
  letI : Finite K.N := finiteOutsideBoundarySubcomplexFaces K
  letI : Fintype K.N := Fintype.ofFinite K.N
  letI : DecidableEq K.N := Classical.decEq K.N
  letI : DecidableRel (outsideFaceComparabilityGraph K).Adj := Classical.decRel _
  graphReducedHomologyZeroModTwo (outsideFaceComparabilityGraph K)

/-- Helper for Theorem 62.1: any relative open-star model computes complement
path components by the comparability graph of outside faces. -/
lemma BoundaryComplementOpenStarModel.zerothHomotopyEquiv {n : ℕ}
    {K : (SSet.boundary (n + 1)).toSSet.Subcomplex}
    (M : BoundaryComplementOpenStarModel n K) :
    Nonempty
      (ZerothHomotopy (boundaryRealizationComplement n K) ≃
        (SimpleGraph.fromRel fun s t : K.N ↦ s ≤ t ∨ t ≤ s).ConnectedComponent) := by
  -- First compute components using the intersection graph of the open cover.
  obtain ⟨e⟩ := zerothHomotopyEquiv_intersectionGraph M.U M.isOpen_U
    M.isPathConnected_U M.iUnion_U
  -- The model's intersection formula identifies that graph with comparability.
  have hGraph :
      SimpleGraph.fromRel (fun s t : K.N ↦ (M.U s ∩ M.U t).Nonempty) =
        SimpleGraph.fromRel (fun s t : K.N ↦ s ≤ t ∨ t ≤ s) := by
    ext s t
    simp only [SimpleGraph.fromRel_adj, M.inter_nonempty_iff]
  rw [hGraph] at e
  exact ⟨e⟩

/-- Helper for Theorem 62.1: a finite relative open-star model identifies graph
reduced mod-two `H₀` with the augmentation kernel on complement path components. -/
lemma BoundaryComplementOpenStarModel.graphReducedHomologyZeroModTwoEquiv
    {n : ℕ} {K : (SSet.boundary (n + 1)).toSSet.Subcomplex}
    (M : BoundaryComplementOpenStarModel n K) :
    Nonempty
      (outsideFaceGraphReducedHomologyZeroModTwo K ≃ₗ[ZMod 2]
        LinearMap.ker
          (componentAugmentationModTwo
            (ZerothHomotopy (boundaryRealizationComplement n K)))) := by
  -- First normalize graph homology to graph components, then reindex those
  -- components along the open-star model's path-component equivalence.
  letI : Finite K.N := finiteOutsideBoundarySubcomplexFaces K
  letI : Fintype K.N := Fintype.ofFinite K.N
  letI : DecidableEq K.N := Classical.decEq K.N
  letI : DecidableRel (outsideFaceComparabilityGraph K).Adj := Classical.decRel _
  obtain ⟨eGraph⟩ :=
    graphReducedHomologyZeroModTwo_linearEquiv_componentKernel
      (outsideFaceComparabilityGraph K)
  obtain ⟨eComponents⟩ := M.zerothHomotopyEquiv
  refine ⟨?_⟩
  simpa only [outsideFaceGraphReducedHomologyZeroModTwo] using
    eGraph.trans (componentAugmentationKernelLinearEquiv eComponents.symm)

end InvarianceOfDomainSupport

end
