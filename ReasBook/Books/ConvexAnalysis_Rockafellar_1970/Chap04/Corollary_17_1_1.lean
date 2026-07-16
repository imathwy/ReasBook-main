import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_2

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section

universe u v w

variable {ι : Type u} {R : Type v} {E : Type w}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E]

local instance : ConvexSpace R E := ConvexSpace.ofModule
local instance : IsModuleConvexSpace R E := IsModuleConvexSpace.ofModule

/-!
Source/core/bridge triage:

  sets can be written as a convex combination of at most
  `Module.finrank R (vectorSpan R (⋃ i, C i)) + 1` affinely independent points, with
  no two chosen points coming from the same member of the family.
- `core/canonical`: the owner abstractions are `convexHull R (⋃ i, C i)`, surfaced in Chapter 4 as
  `conv[R] (⋃ i, C i)`, together with `AffineIndependent R` and the chapter simplex owner
  `StdSimplex R s` on a finite support `s : Finset ι`, with represented point
  `(w.map z).convexCombination`.
- `bridge/view`: Theorem 3.3 gives the first source-facing reduction of a point of
  `conv[R] (⋃ i, C i)` to a finite simplex combination using one point from each selected
  convex set, while Theorem 17.0.3 supplies the finite-dimensional Carathéodory reduction to an
  affinely independent family of cardinality at most
  `Module.finrank R (vectorSpan R (⋃ i, C i)) + 1`.

Domain-style sampling used here:
- `Set.conv_iUnion_eq_iUnion_simplex_sum`;
- `exists_convex_combination_card_le_of_mem_conv`;
- `eq_pos_convex_span_of_mem_convexHull`;
- `AffineIndependent`.

Primitive data vs derived API:
- primitive inputs: the family `C`, its convexity hypothesis, and the point `x`;
- derived output data: the finite support `s` of selected family indices, the chosen point family
  `z`, its affine independence, and the simplex witness `w`, together with the cardinality bound
  `s.card ≤ Module.finrank R (vectorSpan R (⋃ i, C i)) + 1`.

Layer target: `source-facing`, stated directly for a family of convex sets rather than by
introducing a new package around the chosen points and weights.
-/

-- Proof sketch: apply Theorem 3.3 to write `x` as a simplex-weighted combination of one point
-- from each member of a finite subfamily of `C`. Regard those chosen points as a finite subset of
-- `⋃ i, C i` and apply Theorem 17.0.3 to the chapter hull `conv[R] (⋃ i, C i)` (equivalently,
-- mathlib's
-- `eq_pos_convex_span_of_mem_convexHull`) to reduce to an affinely independent family of
-- cardinality at most `Module.finrank R (vectorSpan R (⋃ i, C i)) + 1`. If two surviving points
-- lie in the same `C i`,
-- coalesce them using convexity of `C i`; iterating the textbook reduction yields an equivalent
-- representation in which the selected family indices are pairwise distinct, recorded canonically
-- by a finite support `s : Finset ι`.
/-- Corollary 17.1.1: if `x` lies in the convex hull of the union of a family of convex sets, then
`x` can be written as a convex combination of at most
`Module.finrank R (vectorSpan R (⋃ i, C i)) + 1` affinely
independent points, each chosen from a different member of the family. The selected family members
are recorded by a finite support `s : Finset ι`. Specializing to
`R = ℝ` and `E = Fin n → ℝ` recovers the textbook `R^n` formulation with `n + 1` or fewer
points. -/
theorem exists_affineIndependent_convexCombination_of_mem_convexHull_iUnion
    (C : ι → Set E) (hconv : ∀ i, Convex R (C i)) (x : E)
    [FiniteDimensional R (vectorSpan R (⋃ i, C i))]
    (hx : x ∈ conv[R] (⋃ i, C i)) :
    ∃ s : Finset ι, s.card ≤ Module.finrank R (vectorSpan R (⋃ i, C i)) + 1 ∧
      ∃ z : (i : s) → C i,
        AffineIndependent R (fun i ↦ (z i : E)) ∧
        ∃ w : StdSimplex R s,
          x = (w.map (fun i ↦ (z i : E))).convexCombination := sorry

end
