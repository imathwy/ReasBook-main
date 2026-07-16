import StacksProject_2024.stacks_project.Chap34.Lemma_34_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` recalled `Presheaf.IsSheaf` and the canonical sheaf-condition owner. Local
Chapter 34 precedent represents the localized big site `(Sch/S)_τ` as a full subcategory
`C.FullSubcategory` of `Over S`, with topology obtained by comapping
`StandardTopology.overTopology`.
The source tag evidence is consistent with Stacks tag `0EUX`.
-/

/-- Lemma 34.13.4: for one of the five standard topologies, let `C` model the localized big site
`(Sch/S)_τ` as a full subcategory of `Sch/S`. If `F` is a `τ`-sheaf on this localized site and
satisfies property (b) of Lemma 34.13.1, then its Lemma 34.13.1 extension `F'` to all schemes over
`S` satisfies the sheaf condition for all `τ`-coverings. -/
@[stacks 0EUX]
theorem isSheaf_overTopology_of_tauSheaf_extension
    {S : Scheme.{u}} (τ : StandardTopology) (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
    (hC_open : overSubcategoryContainsAffineOpens C)
    (hC_fp : overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase C)
    (hF_tau :
      Presheaf.IsSheaf (((τ.overTopology S).toPrecoverage.comap C.ι).toGrothendieck) F)
    (hF_limits : preservesDirectedAffineLimitsOnSubcategory C F)
    (eF' : C.ι.op ⋙ F' ≅ F)
    (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
    (hF'_limits : preservesDirectedAffineLimitsOver S F')
    (hF'_unique :
      ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
        preservesDirectedAffineLimitsOver S G →
        ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF') :
    Presheaf.IsSheaf (τ.overTopology S) F' := sorry

end AlgebraicGeometry
