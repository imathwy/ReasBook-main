import Mathlib.Tactic.Recall
import Mathlib.Topology.Homotopy.HomotopyGroup

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` identifies `LoopSpace` in
-- `Mathlib.Topology.Homotopy.HomotopyGroup`; mathlib's canonical owner is
-- `LoopSpace X x := Path x x`, with scoped notation `Ω X x`.

universe u

open scoped Topology.Homotopy

variable {X : Type u} [TopologicalSpace X] (x : X)

/- Definition 8.2.5: the loop space `Ω X x` is mathlib's `LoopSpace X x`; its points are loops
at the basepoint `x`, i.e. paths `Path x x`. -/
recall LoopSpace (X : Type u) [TopologicalSpace X] (x : X) : Type u

/- The notation `Ω X x` is definitionally the space of paths from `x` to itself. -/
theorem loopSpace_eq_path : Ω X x = Path x x := rfl

/- The constant path at `x` is a canonical point of the loop space `Ω X x`. -/
#check (Path.refl x : Ω X x)
