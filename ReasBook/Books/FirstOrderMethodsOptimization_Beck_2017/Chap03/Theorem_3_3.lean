import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
Theorem 3.3 is `source-facing` at the chapter owner `extendedRealSubdifferential : Set (Module.Dual ℝ E)`.
Its boundedness conclusion lives naturally on the normed continuous-dual view, so the file reuses
the existing bridge `strongDualSubdifferential` instead of introducing a second `StrongDual`-valued
owner. Domain sampling shows that the stronger chapter existence theorem is
`subdifferential_nonempty_at_relativeInterior_point`; part (1) below is only its finite-dimensional
interior specialization, while part (2) stays on the same owner/bridge surface.
-/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential
recall subdifferential_nonempty_at_relativeInterior_point

-- Proof sketch: this is the finite-dimensional interior specialization of the stronger owner
-- theorem `subdifferential_nonempty_at_relativeInterior_point`, using the canonical inclusion
-- `interior (effective_domain f) ⊆ intrinsicInterior ℝ (effective_domain f)`.
/-- Theorem 3.3 (1): for a convex extended-real-valued function, the extendedRealSubdifferential at an
interior point of the effective domain is nonempty. -/
theorem subdifferential_nonempty_at_interior_point
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    (extendedRealSubdifferential f x).Nonempty :=
  subdifferential_nonempty_at_relativeInterior_point f x hconvex
    (interior_subset_intrinsicInterior hx)

-- Proof sketch: use local Lipschitz continuity on a closed ball centered at `x` and contained in
-- `effective_domain f`. For any `g ∈ ∂ f(x)`, evaluate the subgradient inequality at a point of
-- the form `x + εu`, where `u` is a unit vector realizing the dual norm of `g`, to obtain a
-- uniform norm bound `‖g‖ ≤ L`; hence `∂ f(x)` is contained in a closed ball of the dual space.
/-- Theorem 3.3 (2): for a convex extended-real-valued function that never takes the value `⊥`,
the continuous-dual view of the extendedRealSubdifferential at an interior point of the effective domain is
bounded in the dual norm. -/
theorem subdifferential_bounded_at_interior_point
    (f : E → EReal) (x : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    IsBounded (strongDualSubdifferential f x) := sorry

end
