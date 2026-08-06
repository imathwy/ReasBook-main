import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5

open Path.Homotopic.Quotient
open scoped ContinuousMap

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]

-- Semantic recall via `lean_leansearch`: `PathConnectedSpace.somePath` supplies a canonical chosen
-- path between any two points of a path-connected space. Combined with Theorem 7.6.5, this gives
-- existence of a homotopy equivalence between any two fibers.

/-- Corollary 7.6.6: if the base `B` is path connected, then any two fibers of a fibration
`p : C(E, B)` are homotopy equivalent. More precisely, the canonical path
`PathConnectedSpace.somePath b b'` yields a homotopy-equivalence class between the fibers over
`b` and `b'`. -/
theorem fiberHomotopyEquivOfPathConnected
    (p : C(E, B)) [IsFibration p] [PathConnectedSpace B] (b b' : B) :
    ∃ e : fiber p b ≃ₕ fiber p b',
      ⟦e.toFun⟧ = fiberTranslationClass p (mk (PathConnectedSpace.somePath b b')) :=
  exists_homotopyEquiv_fiberTranslationPath p (PathConnectedSpace.somePath b b')
