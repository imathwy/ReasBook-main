import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Corollary_4_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Principle_4_3_1

universe u

namespace SimpleGraph

open scoped SimpleGraph

-- Semantic recall via `lean_leansearch`: `FreeGroup.freeGroupCongr`,
-- `SimpleGraph.Connected.exists_isTree_le`, and `SimpleGraph.isTree_iff_connected_and_card`
-- are the nearby canonical combinatorial owners. Clause (1) below stays on a chosen realization
-- to name a basepointed fundamental group, while clause (3) uses the graph-level tree predicate
-- `G.IsTree`.

/-- Corollary 4.4.4 (1). If `G` is a finite connected graph, then `π₁(G)` is free on
`1 - χ(G)` generators. Using `χ(G) = Nat.card V - Nat.card G.edgeSet`, this rank is written here
as `Nat.card G.edgeSet + 1 - Nat.card V`. For a chosen realization `graphRealization boundary` of
`G` and a chosen vertex basepoint `graphVertex boundary v`, this is recorded as an isomorphism
with the free group on `Fin (Nat.card G.edgeSet + 1 - Nat.card V)`. The reusable canonical
free-group owner is the companion instance
`instIsFreeGroupFundamentalGroupGraphVertex_of_connected`. -/
theorem freeGroupFinEquivFundamentalGroup_of_connected
    {V : Type u} [Finite V] (G : SimpleGraph V) (boundary : G.edgeSet ↪ Fin 2 → V)
    (hboundary : ∀ e : G.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    (hG : G.Connected) (v : V) :
    Nonempty
      (FreeGroup (Fin (Nat.card G.edgeSet + 1 - Nat.card V)) ≃*
        FundamentalGroup (graphRealization boundary) (graphVertex boundary v)) := sorry

/-- Corollary 4.4.4 companion: the fundamental group of a connected graph realization is free.

This is the canonical reusable owner behind clause (1); the finite-rank statement remains the
source-facing corollary. -/
instance instIsFreeGroupFundamentalGroupGraphVertex_of_connected
    {V : Type} (G : SimpleGraph V) (boundary : G.edgeSet ↪ Fin 2 → V)
    (hboundary : ∀ e : G.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    (hG : G.Connected) (v : V) :
    IsFreeGroup (FundamentalGroup (graphRealization boundary) (graphVertex boundary v)) := by
  classical
  obtain ⟨T, _, hT⟩ := hG.exists_isMaximalSubtree
  let X : MaximalTreeQuotientContext V :=
    { graph := G
      boundary := boundary
      boundary_edge := hboundary
      connected := hG
      tree := T
      maximalTree := hT }
  simpa [X] using
    (MaximalTreeQuotientContext.instIsFreeGroupFundamentalGroupGraphVertex X v)

/-- Corollary 4.4.4 (2). If `G` is a finite connected graph, then `χ(G) ≤ 1`, written here as
`(Nat.card V : Int) - Nat.card G.edgeSet ≤ 1`. -/
theorem eulerCharacteristic_le_one_of_connected
    {V : Type u} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    χ(G) ≤ 1 := by
  rw [eulerCharacteristic_def]
  refine (sub_le_iff_le_add).2 ?_
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
    Int.ofNat_le.mpr hG.card_vert_le_card_edgeSet_add_one

/-- Corollary 4.4.4 (3). If `G` is a finite connected graph, then `χ(G) = 1` if and only if `G`
is a tree, written here as `(Nat.card V : Int) - Nat.card G.edgeSet = 1 ↔ G.IsTree`. -/
theorem eulerCharacteristic_eq_one_iff_isTree_of_connected
    {V : Type u} [Finite V] (G : SimpleGraph V)
    (hG : G.Connected) :
    χ(G) = 1 ↔ G.IsTree := by
  rw [eulerCharacteristic_def]
  constructor
  · intro hχ
    refine (G.isTree_iff_connected_and_card).2 ?_
    refine ⟨hG, Int.ofNat.inj ?_⟩
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (sub_eq_iff_eq_add.mp hχ).symm
  · intro hTree
    have hcard : Nat.card G.edgeSet + 1 = Nat.card V :=
      (G.isTree_iff_connected_and_card.mp hTree).2
    exact sub_eq_iff_eq_add.mpr <| by
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        congrArg (fun n : ℕ ↦ (n : ℤ)) hcard.symm

end SimpleGraph
