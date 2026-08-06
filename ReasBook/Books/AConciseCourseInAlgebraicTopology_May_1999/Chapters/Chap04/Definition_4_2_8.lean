import Mathlib.Combinatorics.SimpleGraph.Acyclic

universe u

variable {V : Type u}

namespace SimpleGraph

-- Semantic recall via `lean_leansearch`: `SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree`
-- and `SimpleGraph.maximal_isAcyclic_iff_isTree` show that `Maximal` is the canonical order
-- surface for trees; together with `SimpleGraph.Subgraph` from Definition 4.1.6, this packages
-- the textbook phrase "maximal subtree of `X`" on the subgraph lattice of `X`.

/-- Definition 4.2.8. A subtree `T` of a graph `X` is maximal when `T` is a tree subgraph of `X`
and is contained in no strictly larger tree subgraph of `X`. -/
abbrev IsMaximalSubtree {X : SimpleGraph V} (T : X.Subgraph) : Prop :=
  Maximal (fun U : X.Subgraph ↦ U.coe.IsTree) T

namespace IsMaximalSubtree

/-- A maximal subtree is, in particular, a tree subgraph. -/
theorem isTree {X : SimpleGraph V} {T : X.Subgraph} (hT : IsMaximalSubtree T) :
    T.coe.IsTree :=
  hT.prop

/-- No strictly larger subgraph of a maximal subtree is again a tree. -/
theorem not_isTree_of_lt {X : SimpleGraph V} {T U : X.Subgraph} (hT : IsMaximalSubtree T)
    (hTU : T < U) :
    ¬ U.coe.IsTree :=
  hT.not_prop_of_gt hTU

/-- Any tree subgraph of `X` containing a maximal subtree `T` coincides with `T`. -/
theorem eq_of_le {X : SimpleGraph V} {T U : X.Subgraph} (hT : IsMaximalSubtree T) (hTU : T ≤ U)
    (hU : U.coe.IsTree) :
    T = U :=
  Maximal.eq_of_le hT hU hTU

end IsMaximalSubtree

/-- A maximal subtree is exactly a tree subgraph that is contained in no strictly larger tree
subgraph of the ambient graph. -/
theorem isMaximalSubtree_iff_forall_lt {X : SimpleGraph V} (T : X.Subgraph) :
    IsMaximalSubtree T ↔
      T.coe.IsTree ∧
        ∀ ⦃U : X.Subgraph⦄, T < U → ¬ U.coe.IsTree := by
  simpa [IsMaximalSubtree] using
    (show Maximal (fun U : X.Subgraph ↦ U.coe.IsTree) T ↔
        T.coe.IsTree ∧ ∀ ⦃U : X.Subgraph⦄, T < U → ¬ U.coe.IsTree from
      maximal_iff_forall_gt)

end SimpleGraph
