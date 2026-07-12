import Mathlib
import StacksProject_2024.Chap26.Example_26_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.IsClosedImmersion.Spec_iff` and
-- `AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`; nearby Chapter 26 files use
-- `LocallyRingedSpace.IsClosedImmersion` for the locally-ringed-space closed-subspace owner and
-- `Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` for the
-- quotient closed immersion of Example 26.8.1.

/-- Lemma 26.8.2: every closed immersion of locally ringed spaces into the affine scheme
`Spec(R)` is identified, over `Spec(R)`, with the quotient closed immersion
`Spec(R/I) -> Spec(R)` for a unique ideal `I ⊆ R`. -/
@[stacks 01IH]
theorem existsUniqueIdeal_isomorphicSpecQuotient_of_isClosedImmersion
    (R : Type u) [CommRing R]
    {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace)
    [_root_.AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion i] :
    ∃! I : Ideal R,
      Nonempty
        (Over.mk i ≅
          Over.mk
            (Scheme.Hom.toLRSHom
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) := sorry

end AlgebraicGeometry.LocallyRingedSpace
