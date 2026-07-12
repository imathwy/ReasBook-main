import StacksProject_2024.Chap29.Lemma_29_6_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

noncomputable section

variable {X Y : Scheme} (f : X ⟶ Y)

-- Source-facing bridge on the canonical owners already fixed in nearby files:
-- `Scheme.Hom.image` and `Scheme.Hom.ker` from Lemma 29.6.3, together with the canonical
-- reduced-induced closed-subscheme owner `Scheme.IdealSheafData.vanishingIdeal` from Chapter 26.
-- The support of `f.ker` is the closed subset underlying the scheme-theoretic image, so the
-- reduced induced scheme structure on that support is the canonical source-facing replacement for
-- the raw radical-subscheme presentation. The Stacks tag evidence is consistent: item tag `056B`
-- matches the source URL `/tag/056B`.

/-- Lemma 29.6.7: if `X` is reduced, then the scheme theoretic image of `f` is the reduced induced
scheme structure on the closure of the set-theoretic image of `f`. -/
@[stacks 056B]
theorem schemeTheoreticImage_eq_reducedInducedSchemeStructure_of_isReduced
    [QuasiCompact f] [IsReduced X] :
    f.image = (Scheme.IdealSheafData.vanishingIdeal f.ker.support).subscheme := sorry

/-- If `X` is reduced, then the kernel ideal sheaf cutting out the scheme-theoretic image of `f`
is the reduced induced scheme structure on its support. -/
theorem schemeTheoreticImage_ker_eq_reducedInducedSchemeStructure_of_isReduced
    [QuasiCompact f] [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal f.ker.support := sorry

end

end AlgebraicGeometry
