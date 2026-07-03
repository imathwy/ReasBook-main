import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_8 (from Chap04) -/
section

open Set
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local notation "E⋆" => StrongDual ℝ E
local notation:50 s " tangent " C => s tangent[E⋆,ℝ] C

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 18.8 says that a full-dimensional closed convex set is exactly the
  intersection of the closed half-spaces tangent to it.
- `core/canonical`: the ambient owner theorem is
  `closed_convex_eq_sInter_closedHalfSpacesContaining`; the source-facing owner predicate for the
  restricted family is `s tangent C` from Definition 18.7, together
  with the
  full-dimensionality condition `affineSpan ℝ C = ⊤`.
- `bridge/view`: this file is the source-facing bridge that narrows the Chapter 11 family of all
  containing closed half-spaces to the textbook family of tangent closed half-spaces, represented
  directly by `{s : Set E | s tangent C}`.

Domain-style sampling used here:
- `closed_convex_eq_sInter_closedHalfSpacesContaining`;
- `Set.IsSupportingHalfSpace`;
- `AffineSubspace.IsSupportingHyperplane`;
- `Set.IsTangentHalfSpace`;
- `affineSpan ℝ C = ⊤`.

Primitive data vs derived API:
- primitive inputs: the set `C` together with its closedness, convexity, and full-dimensionality;
- derived API: the recovery of `C` as the intersection of its tangent half-spaces.

Layer target: `source-facing`, stated directly with the existing tangent-half-space owner
predicate rather than via a surrogate package of support-function data.

Ambient refinement:
- the surrounding owner declarations `IsSupportingHalfSpace`,
  `Set.IsSupportingHalfSpace`,
  `AffineSubspace.IsSupportingHyperplane`, and `Set.IsTangentHalfSpace` are already
  coordinate-free;
- the Chapter 11 owner theorem for intersections of containing half-spaces is likewise
  coordinate-free on the dual/pairing owner layer `StrongDual ℝ E`.
- the theorem therefore belongs on arbitrary finite-dimensional real normed spaces rather than the
  concrete model `EuclideanSpace ℝ (Fin n)` or an unnecessary inner-product specialization.
-/

/-- Theorem 18.8: a full-dimensional closed convex set in a finite-dimensional real normed space,
formalized by `affineSpan ℝ C = ⊤`, is the intersection of all closed half-spaces tangent
to it. This is the source-facing tangent-half-space specialization of
`closed_convex_eq_sInter_closedHalfSpacesContaining`. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` formulation. -/
-- Proof sketch: every tangent half-space to `C` is supporting, hence contains `C`, giving the
-- inclusion from left to right. For the reverse inclusion, if `x ∉ C`, Theorem 13.1 supplies a
-- linear functional separating `x` from `C` via the support function of `C`. The cone argument of
-- Corollary 18.7.1 refines such a separator to one coming from an exposed ray of the epigraph of
-- the support function, which corresponds to a half-space tangent to `C`. That tangent half-space
-- contains `C` but excludes `x`, so `x` is not in the intersection of all tangent half-spaces.
theorem closed_convex_eq_sInter_tangentHalfSpaces
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_full : affineSpan ℝ C = ⊤) :
    C = ⋂₀ {s : Set E | s tangent C} := sorry

end
