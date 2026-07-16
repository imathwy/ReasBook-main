import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical image factorization
-- `Scheme.Hom.toImage`, the open-immersion result for quasi-compact immersions, and
-- `Scheme.Hom.opensRange`; local Chapter 29 inspection confirmed that
-- `schemeTheoreticallyDense` is the project owner for scheme-theoretically dense opens. The Stacks
-- tag evidence is consistent: item tag `01RG` matches the source URL `/tag/01RG`.

/-- Lemma 29.7.7 (1): if `h : Z ⟶ X` is an immersion and either `h` is quasi-compact or `Z` is
reduced, then the morphism from `Z` to the scheme-theoretic image of `h` is an open immersion. -/
@[stacks 01RG]
theorem isOpenImmersion_toImage_of_isImmersion_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) (hh : IsImmersion h)
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    IsOpenImmersion h.toImage := sorry

/-- Lemma 29.7.7 (2): under the same hypotheses, the open subscheme of the scheme-theoretic
image determined by `h.toImage` is scheme theoretically dense. -/
@[stacks 01RG]
theorem schemeTheoreticallyDense_opensRange_toImage_of_isImmersion_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) (hh : IsImmersion h)
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    schemeTheoreticallyDense (@opensRange _ _ h.toImage
      (isOpenImmersion_toImage_of_isImmersion_of_quasiCompact_or_isReduced h hh hqc_or_red)) := sorry

/-- Lemma 29.7.7 (3): under the same hypotheses, `Z` is topologically dense in its
scheme-theoretic image, equivalently the map to the image is dominant. -/
@[stacks 01RG]
theorem isDominant_toImage_of_isImmersion_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) (hh : IsImmersion h)
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    IsDominant h.toImage := sorry

end Scheme.Hom
end AlgebraicGeometry
