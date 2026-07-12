import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

-- Source/core/bridge triage for Lemma 29.23.4:
-- - `source-facing`: the field-base specialization asserting that the structure morphism of a
--   scheme over `k` is universally open;
-- - `core/canonical`: the owner `AlgebraicGeometry.UniversallyOpen`;
-- - `bridge/view`: the `Over (Spec (CommRingCat.of k))` presentation of a scheme over `k`.

/-- Lemma 29.23.4: if `X` is a scheme over a field `k`, then its structure morphism
`X ⟶ Spec(k)` is universally open. -/
@[stacks 0383]
theorem universallyOpen_structureMorphism_of_field
    (X : Over (Spec (CommRingCat.of k))) :
    UniversallyOpen X.hom := by
  let _ : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  let _ : Subsingleton (Spec (CommRingCat.of k)) := inferInstance
  infer_instance

end

end AlgebraicGeometry
