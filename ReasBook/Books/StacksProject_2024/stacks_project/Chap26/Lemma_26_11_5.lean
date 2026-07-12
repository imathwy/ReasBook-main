import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.11.5:
- `source-facing`: two affine open neighborhoods of a point in a scheme admit a common standard open
  neighborhood of that point inside their intersection;
- `core/canonical`: the exact owner `AlgebraicGeometry.exists_basicOpen_le_affine_inter`;
- `bridge/view`: none is needed here, because mathlib already exposes the Stacks lemma in the
  same source-facing shape. -/

-- Semantic recall: mathlib already provides the exact source-facing theorem
-- `AlgebraicGeometry.exists_basicOpen_le_affine_inter`, so the faithful refine is a pure recall
-- of that canonical owner rather than a duplicate local wrapper theorem.
/- Lemma 26.11.5: if `U` and `V` are affine open subsets of a scheme `X` and `x ∈ U ∩ V`, then
there are sections defining the same basic open neighborhood of `x` inside both `U` and `V`;
equivalently, there is an affine open neighborhood of `x` which is a standard open of both `U`
and `V`. In mathlib this is already exactly
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`, so this item is recorded as a direct
canonical use rather than a duplicate local wrapper. -/
recall exists_basicOpen_le_affine_inter

section

universe u

variable {X : Scheme.{u}} {U V : X.Opens}
variable (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V)

#check exists_basicOpen_le_affine_inter hU hV x hx

end
