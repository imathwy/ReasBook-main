import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry.Scheme

/- Source/core/bridge triage for Lemma 26.6.6:
- `source-facing`: for an affine scheme `Y`, the principal open `D(f) = Y.basicOpen f` is affine;
- `core/canonical`: `AlgebraicGeometry.IsAffineOpen.basicOpen`;
- `bridge/view`: specialize the affine-open owner to the top open via `isAffineOpen_top Y`. -/

/- Lemma 26.6.6: if `Y` is an affine scheme and `f ∈ Γ(Y, \mathcal O_Y)`, then the principal
open `D(f) = Y.basicOpen f` is affine. In mathlib this is the canonical theorem
`AlgebraicGeometry.IsAffineOpen.basicOpen`, applied to the affine open `⊤` of `Y` via
`isAffineOpen_top Y`; the source-facing Stacks lemma is therefore a thin specialization of that
canonical owner. -/
recall AlgebraicGeometry.IsAffineOpen.basicOpen

section

variable (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤))

/-- Lemma 26.6.6: for an affine scheme `Y`, the principal open `D(f)` cut out by a global
section `f` is affine. This is the top-open specialization of
`AlgebraicGeometry.IsAffineOpen.basicOpen`. -/
@[stacks 01I3]
theorem basicOpen_isAffineOpen : IsAffineOpen (Y.basicOpen f) :=
  (isAffineOpen_top Y).basicOpen f

end

end AlgebraicGeometry.Scheme
