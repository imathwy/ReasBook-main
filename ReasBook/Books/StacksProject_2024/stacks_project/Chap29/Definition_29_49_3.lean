import StacksProject_2024.stacks_project.Chap29.Definition_29_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/- Source/core/bridge triage:
- `source-facing`: Definition 29.49.3 recalls the notion of a rational function on a scheme `X`;
- `core/canonical`: mathlib already owns rational maps as `Scheme.RationalMap`, written `X ⤏ Y`;
- `bridge/view`: the source target is the affine line over `Spec ℤ`, identified directly with
  `Spec ℤ[t]`.

This item is therefore a pure canonical recall: a rational function on `X` is simply a rational
map from `X` to `Spec ℤ[t]`. No extra local owner or alias is needed.
-/

variable (X : Scheme)

/- Definition 29.49.3: a rational function on `X` is a rational map from `X` to the affine line
over `ℤ`, namely `Spec ℤ[t]`. -/
#check (X ⤏ Spec (CommRingCat.of (Polynomial ℤ)))

end AlgebraicGeometry.Scheme
