import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]

-- Semantic recall:
-- * `lean_leansearch` surfaced the canonical finiteness owners
--   `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian` and
--   `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`;
-- * local project precedent in `Lemma_29_17_4` records irreducible-component images in schemes as
--   `Set.range i.base`, so the source statement is best exposed as a locally finite family on `X`
--   indexed by `irreducibleComponents Z`.

/-- Lemma 31.26.1: let `X` be a locally Noetherian scheme and let `i : Z ⟶ X` be a closed
immersion. Then the collection of irreducible components of `Z`, viewed as subsets of `X` via the
inclusion, is locally finite in `X`. -/
theorem locallyFinite_irreducibleComponents_of_isClosedImmersion :
    LocallyFinite fun W : irreducibleComponents Z ↦ i.base '' (W : Set Z) := sorry

end

end AlgebraicGeometry
