import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Path
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Construction_4_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_10

open scoped ContinuousMap
open scoped unitInterval

noncomputable section

universe u

private abbrev TopologicalPath {X : Type u} [TopologicalSpace X] (x y : X) : Type u :=
  Path x y

private noncomputable def topologicalPathRefl {X : Type u} [TopologicalSpace X] (x : X) :
    TopologicalPath x x :=
  Path.refl x

private noncomputable def topologicalPathTrans {X : Type u} [TopologicalSpace X] {x y z : X}
    (p : TopologicalPath x y) (q : TopologicalPath y z) : TopologicalPath x z :=
  Path.trans p q

namespace SimpleGraph
namespace MaximalTreeQuotientContext

variable {V : Type}

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- packaging a homotopy equivalence, but this item's source-facing content is the loop assembly
-- arising from the rooted tree paths of Construction 4.3.3.

/-- The loop in `X.graph` attached to a non-tree edge, using the rooted tree-path data from
Construction 4.3.3. -/
noncomputable def loopOfNonTreeEdge (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X)
    (e : X.nonTreeEdges) : X.graph.Walk A.root A.root :=
  let hSpanning : X.tree.IsSpanning := X.maximalTree.isSpanning X.connected
  let hAdj :
      X.graph.Adj (X.boundary e.1 0) (X.boundary e.1 1) :=
    (SimpleGraph.mem_edgeSet X.graph).mp (X.boundary_edge e.1 ▸ e.1.property)
  A.loopOfNonTreeAdj (hSpanning (X.boundary e.1 0)) (hSpanning (X.boundary e.1 1)) hAdj

/-- The realized maximal tree contains the chosen root vertex, so its collapse quotient has a
distinguished collapsed point. -/
theorem treeSubspace_nonempty (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    X.treeSubspace.Nonempty :=
  ⟨graphVertex X.boundary A.root, Or.inl ⟨A.root, rfl⟩⟩

/-- The collapsed point of `X / T`, using the chosen root of `A` only to witness nonemptiness of
`X.treeSubspace`. -/
noncomputable def quotientTreePoint (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    X.quotientTopCat :=
  collapseSubsetPoint X.treeSubspace (treeSubspace_nonempty X A)

/-- A single adjacent edge in `X.graph` determines the corresponding path in `X.realization`. -/
noncomputable def adjPath (X : MaximalTreeQuotientContext V) {u v : V} (h : X.graph.Adj u v) :
    TopologicalPath (graphVertex X.boundary u) (graphVertex X.boundary v) where
  toFun :=
    let e : X.graph.edgeSet := ⟨s(u, v), h⟩
    let _ : DecidableEq V := Classical.decEq V
    if hu : u = X.boundary e 0 then
      graphEdgePoint X.boundary e
    else
      fun t ↦ graphEdgePoint X.boundary e (σ t)
  continuous_toFun := by
    sorry
  source' := by
    sorry
  target' := by
    sorry

/-- A walk in `X.graph` gives a path in the realization by traversing each edge segment in order.
-/
noncomputable def walkPath (X : MaximalTreeQuotientContext V) {u v : V} :
    X.graph.Walk u v → TopologicalPath (graphVertex X.boundary u) (graphVertex X.boundary v)
  | Walk.nil => topologicalPathRefl _
  | Walk.cons h p => topologicalPathTrans (adjPath X h) (walkPath X p)

/-- The loop attached to a non-tree edge, now viewed as an actual loop in the realization
`X.realization`. -/
noncomputable def loopOfNonTreeEdgePath (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X)
    (e : X.nonTreeEdges) :
    TopologicalPath (graphVertex X.boundary A.root) (graphVertex X.boundary A.root) :=
  walkPath X (loopOfNonTreeEdge X A e)

/-- On realization representatives, collapse the tree to the chosen root and send each non-tree
edge parameter through the corresponding loop from Construction 4.3.3. -/
noncomputable def loopAssemblyRaw (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    V ⊕ (X.graph.edgeSet × I) → X.realization :=
  fun z ↦
    match z with
    | .inl _ => graphVertex X.boundary A.root
    | .inr (e, t) =>
        let _ : DecidablePred fun e' : X.graph.edgeSet ↦ e' ∈ X.treeEdges := Classical.decPred _
        if he : e ∈ X.treeEdges then
          graphVertex X.boundary A.root
        else
          loopOfNonTreeEdgePath X A ⟨e, he⟩ t

/-- The realization-level map that already collapses the realized maximal tree to the chosen root.
-/
noncomputable def loopAssemblyOnRealization (X : MaximalTreeQuotientContext V)
    (A : RootedTreePaths X) : C(X.realization, X.realization) where
  toFun :=
    Quotient.lift (loopAssemblyRaw X A) fun _ _ _ ↦ by
      sorry
  continuous_toFun := by
    sorry

/-- The realized maximal tree is sent to the chosen root vertex by
`loopAssemblyOnRealization X A`. -/
theorem loopAssemblyOnRealization_eq_root_of_mem_treeSubspace
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) {x : X.realization}
    (hx : x ∈ X.treeSubspace) :
    loopAssemblyOnRealization X A x = graphVertex X.boundary A.root := by
  sorry

/-- The concrete loop-assembly comparison map `X / T ⟶ X` determined by the rooted tree paths
`A`. It is obtained by quotient-lifting the realization-level map that collapses the tree to the
root and traverses each non-tree edge through the corresponding loop from Construction 4.3.3. -/
noncomputable def loopAssemblyMap (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    C(X.quotientTopCat, X.realization) where
  toFun :=
    Quotient.lift (loopAssemblyOnRealization X A) fun _ _ _ ↦ by
      sorry
  continuous_toFun := by
    sorry

/-- The loop-assembly map sends the collapsed tree point of `X / T` to the chosen root vertex. -/
theorem loopAssemblyMap_quotientTreePoint
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    loopAssemblyMap X A (quotientTreePoint X A) = graphVertex X.boundary A.root := by
  sorry

/-- The quotient-map composite with the explicit loop-assembly map is homotopic to the identity on
`X / T`. -/
theorem quotientMap_comp_loopAssemblyMap_homotopic_id
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    (X.quotientMap.comp (loopAssemblyMap X A)).Homotopic (ContinuousMap.id X.quotientTopCat) := by
  sorry

/-- The loop-assembly map composed with the quotient map is homotopic to the identity on the
realization `X.realization`. -/
theorem loopAssemblyMap_comp_quotientMap_homotopic_id
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    ((loopAssemblyMap X A).comp X.quotientMap).Homotopic (ContinuousMap.id X.realization) := by
  sorry

/-- Lemma 4.3.4. For rooted tree paths `A : RootedTreePaths X`, the loops from Construction 4.3.3
determine the concrete continuous map `loopAssemblyMap X A : X / T → X`, whose composition with
the quotient map `X.quotientMap : C(X.realization, X.quotientTopCat)` is homotopic to the
relevant identity map on both sides. -/
theorem loopAssemblyMap_homotopyInverse
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    (X.quotientMap.comp (loopAssemblyMap X A)).Homotopic (ContinuousMap.id X.quotientTopCat) ∧
      ((loopAssemblyMap X A).comp X.quotientMap).Homotopic
        (ContinuousMap.id X.realization) := by
  exact ⟨quotientMap_comp_loopAssemblyMap_homotopic_id X A,
    loopAssemblyMap_comp_quotientMap_homotopic_id X A⟩

/-- The explicit loop-assembly map packages with `X.quotientMap` into a homotopy equivalence. -/
noncomputable def loopAssemblyHomotopyEquiv
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    X.quotientTopCat ≃ₕ X.realization where
  toFun := loopAssemblyMap X A
  invFun := X.quotientMap
  left_inv := quotientMap_comp_loopAssemblyMap_homotopic_id X A
  right_inv := loopAssemblyMap_comp_quotientMap_homotopic_id X A

/-- The loop-assembly homotopy equivalence has inverse map `X.quotientMap`. -/
theorem loopAssemblyMap_exists_homotopyEquiv
    (X : MaximalTreeQuotientContext V) (A : RootedTreePaths X) :
    ∃ e : X.quotientTopCat ≃ₕ X.realization, e.invFun = X.quotientMap := by
  refine ⟨loopAssemblyHomotopyEquiv X A, ?_⟩
  simp [loopAssemblyHomotopyEquiv]

end MaximalTreeQuotientContext
end SimpleGraph
