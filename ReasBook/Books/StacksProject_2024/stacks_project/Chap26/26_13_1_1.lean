import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

section

universe u

variable (X : Scheme.{u}) (x : X)

-- Semantic recall: `lean_leansearch` found the canonical mathlib owner
-- `Scheme.fromSpecStalk`. The canonical downstream surface is the object-prefix map
-- `X.fromSpecStalk x : Spec (X.presheaf.stalk x) ⟶ X`.

/- Source/core/bridge triage for 26.13.1.1:
- `source-facing`: the canonical local-spectrum morphism `Spec(𝒪_{X, x}) ⟶ X`;
- `core/canonical`: the existing mathlib owner `Scheme.fromSpecStalk`;
- `bridge/view`: this file is recall-only, so the faithful refine is to reuse that owner directly
  and expose its ordinary downstream call shape instead of introducing a duplicate wrapper. -/

/- 26.13.1.1: for a scheme `X` and a point `x : X`, the canonical morphism
`Spec(𝒪_{X, x}) ⟶ X` is the existing mathlib construction `X.fromSpecStalk x`,
so this item is a pure canonical recall. -/
recall Scheme.fromSpecStalk

#check X.fromSpecStalk x

end

end AlgebraicGeometry
