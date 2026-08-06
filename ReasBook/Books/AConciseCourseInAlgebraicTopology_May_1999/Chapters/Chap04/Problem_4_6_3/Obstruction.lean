import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_6

open scoped unitInterval

universe u u₁

namespace SimpleGraph

variable {V : Type u}

/-- The canonical boundary presentation of a graph, used to express the chapter's
source-faithful realization topology without choosing an auxiliary parametrization. -/
noncomputable def realizationBoundary (G : SimpleGraph V) : G.edgeSet ↪ Fin 2 → V where
  toFun e
    | 0 => e.1.out.1
    | 1 => e.1.out.2
  inj' := by
    intro e e' h
    apply Subtype.ext
    have h0 : e.1.out.1 = e'.1.out.1 := congr_fun h 0
    have h1 : e.1.out.2 = e'.1.out.2 := congr_fun h 1
    calc
      e.1 = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
      _ = s(e'.1.out.1, e'.1.out.2) := by rw [h0, h1]
      _ = e'.1 := e'.1.out_eq

namespace Subgraph

variable {G : SimpleGraph V}

/-- The canonical boundary presentation of a subgraph, used to state Kuratowski obstructions via
source-faithful realizations. -/
noncomputable def realizationBoundary (T : G.Subgraph) : T.edgeSet ↪ Fin 2 → T.verts where
  toFun e
    | 0 => ⟨e.1.out.1, T.mem_verts_of_mem_edge e.2 (Sym2.out_fst_mem e.1)⟩
    | 1 => ⟨e.1.out.2, T.mem_verts_of_mem_edge e.2 (Sym2.out_snd_mem e.1)⟩
  inj' := by
    intro e e' h
    apply Subtype.ext
    have h0 : e.1.out.1 = e'.1.out.1 := congrArg Subtype.val <| congr_fun h 0
    have h1 : e.1.out.2 = e'.1.out.2 := congrArg Subtype.val <| congr_fun h 1
    calc
      e.1 = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
      _ = s(e'.1.out.1, e'.1.out.2) := by rw [h0, h1]
      _ = e'.1 := e'.1.out_eq

end Subgraph

/-- A simple graph contains a Kuratowski obstruction when some canonical subgraph realization is
homeomorphic to the canonical realization of the obstruction graph, both taken with the chapter's
source-faithful realization topology. -/
noncomputable def containsSubgraphRealizationHomeomorphicTo
    (G : SimpleGraph V) {W : Type u₁} (obstruction : SimpleGraph W) : Prop :=
  let obstructionBoundary := realizationBoundary obstruction
  let _ : TopologicalSpace (graphRealization obstructionBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace obstructionBoundary
  ∃ T : G.Subgraph,
    let subgraphBoundary := Subgraph.realizationBoundary T
    let _ : TopologicalSpace (graphRealization subgraphBoundary) :=
      graphRealizationSourceFaithfulTopologicalSpace subgraphBoundary
    Nonempty (graphRealization subgraphBoundary ≃ₜ graphRealization obstructionBoundary)

end SimpleGraph
