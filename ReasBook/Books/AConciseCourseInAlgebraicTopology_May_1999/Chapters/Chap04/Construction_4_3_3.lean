import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_3_2.QuotientContext

namespace SimpleGraph
namespace MaximalTreeQuotientContext

-- Semantic recall via `lean_leansearch`: `SimpleGraph.Walk.reverse`,
-- `SimpleGraph.Walk.append`, and `SimpleGraph.Path.reverse` are the canonical mathlib owners for
-- path concatenation and inversion, so this construction is expressed as explicit walk data in the
-- ambient graph attached to a chosen maximal-tree context.

variable {V : Type}

/-- Paths in the chosen maximal subtree `X.tree` of a maximal-tree quotient context. -/
abbrev TreePath (X : MaximalTreeQuotientContext V) (u v : X.tree.verts) :=
  Path X.tree.coe u v

/-- A choice of base vertex in the maximal subtree `X.tree`; the unique tree path from any vertex
to that base vertex is then derived canonically from `X.maximalTree.isTree`. -/
structure RootedTreePaths (X : MaximalTreeQuotientContext V) where
  root : X.tree.verts

namespace RootedTreePaths

variable {X : MaximalTreeQuotientContext V}

/-- The unique path in the tree `X.tree` from `v` to the chosen root `A.root`. -/
noncomputable def pathToRoot (A : RootedTreePaths X) (v : X.tree.verts) : TreePath X v A.root :=
  let h := IsTree.existsUnique_path X.maximalTree.isTree v A.root
  ⟨Classical.choose h.exists, Classical.choose_spec h.exists⟩

/-- In a tree, every path from `v` to `A.root` coincides with the canonically derived one. -/
theorem pathToRoot_eq (A : RootedTreePaths X) (v : X.tree.verts) (p : TreePath X v A.root) :
    A.pathToRoot v = p := by
  apply Subtype.ext
  let h := IsTree.existsUnique_path X.maximalTree.isTree v A.root
  exact ExistsUnique.unique h (A.pathToRoot v).property p.property

/-- The chosen tree path from `v` to `A.root`, viewed as a walk in the ambient graph `X.graph`. -/
noncomputable def toRootWalk (A : RootedTreePaths X) (v : X.tree.verts) : X.graph.Walk v A.root :=
  ((A.pathToRoot v : Walk X.tree.coe v A.root).map X.tree.hom)

/-- Construction 4.3.3. Fix a vertex `A.root` of the maximal subtree `X.tree`; for each
vertex `v` of `X.tree`, let `A.pathToRoot v : TreePath X v A.root` be the unique tree path to
that root. Then any oriented edge `hvv' : X.graph.Adj v v'` whose endpoints lie in `X.tree`
determines the ambient loop based at `A.root` used later for the source's non-tree edges.

In Lean's left-to-right `Walk.append` order this loop is
`(A.toRootWalk ⟨v, hv⟩).reverse.append (Walk.cons hvv' (A.toRootWalk ⟨v', hv'⟩))`; this is the
textbook loop `b_j = a(v') · j · a(v)^{-1}` with the book's composition read right-to-left. -/
noncomputable def loopOfNonTreeAdj (A : RootedTreePaths X) {v v' : V} (hv : v ∈ X.tree.verts)
    (hv' : v' ∈ X.tree.verts) (hvv' : X.graph.Adj v v') : X.graph.Walk A.root A.root :=
  (A.toRootWalk ⟨v, hv⟩).reverse.append (Walk.cons hvv' (A.toRootWalk ⟨v', hv'⟩))

/-- The loop from Construction 4.3.3 traverses the chosen edge `s(v, v')`. -/
theorem mem_edges_loopOfNonTreeAdj (A : RootedTreePaths X) {v v' : V} (hv : v ∈ X.tree.verts)
    (hv' : v' ∈ X.tree.verts) (hvv' : X.graph.Adj v v') :
    s(v, v') ∈ (A.loopOfNonTreeAdj hv hv' hvv').edges := sorry

end RootedTreePaths
end MaximalTreeQuotientContext
end SimpleGraph
