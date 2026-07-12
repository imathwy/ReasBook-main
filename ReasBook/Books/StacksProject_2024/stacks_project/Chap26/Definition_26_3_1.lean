import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Topology

universe u

namespace AlgebraicGeometry

/- Source/core/bridge triage:
- `source-facing`: the Stacks notion that a morphism of locally ringed spaces is an open
  immersion exactly when it is an open embedding on the underlying spaces and an isomorphism on
  every stalk.
- `core/canonical`: `LocallyRingedSpace.IsOpenImmersion`.
- `bridge/view`: the pointwise stalk criterion
  `LocallyRingedSpace.IsOpenImmersion.iff_isIso_stalkMap`. -/

-- Semantic recall: `lean_leansearch` points to the canonical owner
-- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` in
-- `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, with the stalk/open-embedding bridge API
-- `LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` and
-- `LocallyRingedSpace.IsOpenImmersion.stalk_iso`.

/- Definition 26.3.1: the Stacks definition of an open immersion of locally ringed spaces is the
canonical mathlib predicate `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` on a morphism
`f : X ⟶ Y`. -/
recall LocallyRingedSpace.IsOpenImmersion

/-- Definition 26.3.1, source-facing criterion: a morphism of locally ringed spaces is an open
immersion if it is an open embedding on the underlying spaces and induces an isomorphism on every
stalk. -/
@[stacks 01HE]
theorem LocallyRingedSpace.IsOpenImmersion.iff_isIso_stalkMap
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    LocallyRingedSpace.IsOpenImmersion f ↔
      IsOpenEmbedding f.base ∧
        ∀ x : X, IsIso (f.stalkMap x) := by
  constructor
  · intro hf
    letI : LocallyRingedSpace.IsOpenImmersion f := hf
    exact ⟨hf.base_open, fun x ↦ inferInstance⟩
  · rintro ⟨hf, hstalk⟩
    letI : ∀ x : X, IsIso (f.stalkMap x) := hstalk
    exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f hf

end AlgebraicGeometry
