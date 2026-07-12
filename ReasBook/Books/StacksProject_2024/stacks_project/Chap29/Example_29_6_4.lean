import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` returned `Scheme.Hom.image` for the
-- scheme-theoretic image, `Spec.map` for maps on affine schemes, and
-- `IsClosedImmersion.spec_of_quotient_mk` for the quotient closed immersion.
-- The Stacks tag evidence is consistent: item tag `056A` matches the source URL `/tag/056A`.

/-- Example 29.6.4: if `A ⟶ B` has kernel `I`, then the scheme-theoretic image
of `Spec B ⟶ Spec A` is the closed subscheme `Spec (A/I)` of `Spec A`. -/
@[stacks 056A]
theorem schemeTheoreticImage_specMap_iso_quotientOfKernel
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (I : Ideal A)
    (hI : RingHom.ker φ.hom = I) :
    ∃ e : Scheme.Hom.image (Spec.map φ) ≅ Spec (CommRingCat.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Scheme.Hom.imageι (Spec.map φ) := sorry

end

end AlgebraicGeometry
