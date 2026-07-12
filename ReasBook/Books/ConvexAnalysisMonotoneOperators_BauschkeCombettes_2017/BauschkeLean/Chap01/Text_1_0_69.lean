import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.69: for an operator `T : X → X`, the textbook fixed point set `Fix T` is the
canonical mathlib set `Function.fixedPoints T`. -/
recall Function.fixedPoints {α : Type u} (T : α → α) : Set α

/- Companion recall: membership in `Function.fixedPoints T` is exactly the textbook condition
`T x = x`. -/
recall Function.mem_fixedPoints_iff {α : Type u} {T : α → α} {x : α} :
    x ∈ Function.fixedPoints T ↔ T x = x
