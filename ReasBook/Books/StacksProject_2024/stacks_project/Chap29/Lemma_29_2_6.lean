import StacksProject_2024.Chap26.Lemma_26_19_5
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

/-
Lemma 29.2.6: this chapter reuses the earlier source-facing theorem
`AlgebraicGeometry.closedImmersion_quasiCompact` from Chapter 26.
-/
recall AlgebraicGeometry.closedImmersion_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    QuasiCompact f

end AlgebraicGeometry
