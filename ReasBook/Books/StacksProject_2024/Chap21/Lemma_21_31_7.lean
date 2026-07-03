import Mathlib
import StacksProject_2024.Chap21.Definition_21_31_2

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {X Y : LCCat.{u}}

/-- Sheaves of types on the small Zariski site of `X`. -/
abbrev SmallTypeSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf (Type u) X.obj

/-- Sheaves of types on the big Zariski site `LC_{Zar}/X`, represented here by a Grothendieck
topology `J` on `Over X`. -/
abbrev LCZarTypeSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  Sheaf J (Type u)

/-- Sheaves of abelian groups on the small Zariski site of `X`. -/
abbrev SmallAbSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj

/-- Sheaves of abelian groups on the big Zariski site `LC_{Zar}/X`, represented here by a
Grothendieck topology `J` on `Over X`. -/
abbrev LCZarAbSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  Sheaf J AddCommGrpCat.{u + 1}

/-- The inverse-image functor `π_X^{-1}` on sheaves of types, induced by the chosen continuous
functor from the small Zariski site of opens of `X` to the big Zariski site `LC_{Zar}/X`. -/
abbrev piInverseType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    SmallTypeSheaf X ⥤ LCZarTypeSheaf J :=
  π.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) J

/-- The direct-image functor `π_{X,*}` on sheaves of types attached to the same morphism of sites.
-/
abbrev piDirectImageType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J] :
    LCZarTypeSheaf J ⥤ SmallTypeSheaf X :=
  π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj) J

/-- The inverse-image functor `π_X^{-1}` on abelian sheaves, induced by the chosen continuous
functor from the small Zariski site of opens of `X` to the big Zariski site `LC_{Zar}/X`. -/
abbrev piInverseAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint] :
    SmallAbSheaf X ⥤ LCZarAbSheaf J :=
  π.sheafPullback AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) J

/-- The direct-image functor `π_{X,*}` on abelian sheaves attached to the same morphism of sites.
-/
abbrev piDirectImageAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J] :
    LCZarAbSheaf J ⥤ SmallAbSheaf X :=
  π.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) J

/-- The degree-`n` cohomology object obtained from a chosen derived global-sections functor. -/
abbrev derivedCohomologyObject
    {C : Type (u + 1)} [Category.{u} C]
    (RGamma : C ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (K : C) (n : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj (RGamma.obj K)

-- Proof sketch: the coverings of `X` in `LC_{Zar}` are the same open coverings used on the small
-- Zariski site, so the inverse-image sheaf `π_X^{-1}\mathcal F` has the same Čech and derived
-- cohomology as `\mathcal F` on `X`.
/-- Lemma 21.31.7 (1): for an abelian sheaf `\mathcal F` on the small Zariski site of `X`, the
cohomology of `π_X^{-1}\mathcal F` on `LC_{Zar}/X` is canonically isomorphic to the ordinary
Zariski cohomology of `\mathcal F` on `X`. -/
theorem lcZar_piInverse_cohomology_isomorphic
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint]
    [HasWeakSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt (LCZarAbSheaf J)]
    (ℱ : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor J n).obj ((piInverseAb J π).obj ℱ))
      ((Sheaf.cohomologyFunctor (Opens.grothendieckTopology X.obj) n).obj ℱ) := sorry

-- Proof sketch: `π_{X,*}` is the direct-image functor of a morphism of topoi, hence it is a
-- right adjoint. Exactness follows from the fact that this morphism identifies the localized big
-- Zariski site with the ordinary small Zariski site of `X`.
/-- Lemma 21.31.7 (2): the direct-image functor `π_{X,*}` from abelian sheaves on `LC_{Zar}/X` to
abelian sheaves on the small Zariski site of `X` is exact. -/
theorem lcZar_piDirectImage_exact
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] :
    exactFunctor (LCZarAbSheaf J) (SmallAbSheaf X) (piDirectImageAb J π) := sorry

-- Proof sketch: the functor `π_X^{-1}` is obtained from a site morphism whose composite with the
-- direct image is the identity on the small Zariski site; the unit of the adjunction therefore
-- identifies each small sheaf with its pull-push image.
/-- Lemma 21.31.7 (3): the adjunction unit
`id ⟶ π_{X,*} \circ π_X^{-1}` is an isomorphism on sheaves of types. -/
theorem lcZar_pi_adjunction_unit_isIso
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint]
    (adjπ : piInverseType J π ⊣ piDirectImageType J π)
    (ℱ : SmallTypeSheaf X) :
    IsIso (adjπ.unit.app ℱ) := sorry

-- Proof sketch: derive the adjunction `π_X^{-1} ⊣ π_{X,*}` on abelian sheaves. Since the
-- underived unit is an isomorphism and `π_{X,*}` is exact, the derived unit
-- `K ⟶ Rπ_{X,*} π_X^{-1} K` is an isomorphism for every derived object.
/-- Lemma 21.31.7 (4): for `K ∈ D(X)`, the canonical map
`K ⟶ Rπ_{X,*} π_X^{-1} K` is an isomorphism. -/
theorem lcZar_pi_derived_unit_isIso
    (DX : Type (u + 1)) [Category.{u} DX]
    (DLCZarX : Type (u + 1)) [Category.{u} DLCZarX]
    (piInverseDerived : DX ⥤ DLCZarX)
    (piDirectImageDerived : DLCZarX ⥤ DX)
    (adjDerived : piInverseDerived ⊣ piDirectImageDerived)
    (K : DX) :
    IsIso (adjDerived.unit.app K) := sorry

-- Proof sketch: the topological pullback on the small Zariski site and the base-change pullback on
-- the big Zariski site are induced by compatible continuous functors, so their associated inverse
-- image functors form a commuting square in the category of topoi.
/-- Lemma 21.31.7 (5): for a morphism `f : X ⟶ Y` in `LC`, the inverse-image functors on the
small and big Zariski sites are canonically isomorphic after composing around the two sides of the
topos square. -/
theorem lcZar_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JX : GrothendieckTopology (Over X))
    (JY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JY).IsRightAdjoint]
    [HasPullbacks LCCat.{u}]
    [(Over.pullback f).IsContinuous JY JX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JY JX).IsRightAdjoint] :
    IsIsomorphic
      ((TopCat.Sheaf.pullback (Type u) f.hom) ⋙ piInverseType JX πX)
      ((piInverseType JY πY) ⋙ ((Over.pullback f).sheafPullback (Type u) JY JX)) := sorry

-- Proof sketch: use the commutative square from part (5) to identify the pullback of
-- `π_Y^{-1}L` to `LC_{Zar}/X` with `π_X^{-1}(f^{-1}L)`. Part (1) then identifies the resulting
-- hypercohomology on `LC_{Zar}/X` with the ordinary hypercohomology of `f^{-1}L` on `X`.
/-- Lemma 21.31.7 (6): for `L ∈ D^+(Y)`, the hypercohomology of `π_Y^{-1}L` over `X` in the big
Zariski site is canonically isomorphic to the hypercohomology of `f^{-1}L` on the small Zariski
site of `X`, formalized here via chosen pullback and derived global-sections functors. -/
theorem lcZar_pullback_hypercohomology_isomorphic
    (DYplus : Type (u + 1)) [Category.{u} DYplus]
    (DXplus : Type (u + 1)) [Category.{u} DXplus]
    (DLCZarYplus : Type (u + 1)) [Category.{u} DLCZarYplus]
    (DLCZarXplus : Type (u + 1)) [Category.{u} DLCZarXplus]
    (piInverseDerivedPlusY : DYplus ⥤ DLCZarYplus)
    (smallPullbackDerivedPlus : DYplus ⥤ DXplus)
    (lcZarPullbackDerivedPlus : DLCZarYplus ⥤ DLCZarXplus)
    (RGammaSmallX : DXplus ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (RGammaZarX : DLCZarXplus ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (L : DYplus) (n : ℕ) :
    IsIsomorphic
      (derivedCohomologyObject RGammaZarX
        (lcZarPullbackDerivedPlus.obj (piInverseDerivedPlusY.obj L)) n)
      (derivedCohomologyObject RGammaSmallX
        (smallPullbackDerivedPlus.obj L) n) := sorry

-- Proof sketch: for a proper map `f`, proper base change identifies sections of `f_* \mathcal F`
-- after pulling back along any object of `LC_{Zar}/Y` with sections of the pullback object on the
-- corresponding fiber product over `X`. These objectwise identifications assemble into a natural
-- isomorphism of sheaf-valued functors.
/-- Lemma 21.31.7 (7): corresponding to the source's clause `(7a)`, if `f : X ⟶ Y` is proper,
then `π_Y^{-1} \circ f_*` is canonically isomorphic to `f_{Zar,*} \circ π_X^{-1}` as a functor
from sheaves on `X` to sheaves on `LC_{Zar}/Y`. -/
theorem proper_smallPushforward_piInverse_isomorphic_lcZarPushforward_piInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (JX : GrothendieckTopology (Over X))
    (JY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JY).IsRightAdjoint]
    [HasPullbacks LCCat.{u}]
    [(Over.pullback f).IsContinuous JY JX] :
    IsIsomorphic
      ((TopCat.Sheaf.pushforward (Type u) f.hom) ⋙ piInverseType JY πY)
      ((piInverseType JX πX) ⋙
        ((Over.pullback f).sheafPushforwardContinuous (Type u) JY JX)) := sorry

-- Proof sketch: apply the underived proper base-change comparison from part (7) objectwise to the
-- cohomology sheaves of a bounded-below complex and then use the sheafification description of
-- higher direct images to identify the two derived pushforwards.
/-- Lemma 21.31.7 (8): corresponding to the source's clause `(7b)`, if `f : X ⟶ Y` is proper,
then `π_Y^{-1} \circ Rf_*` is canonically isomorphic to `Rf_{Zar,*} \circ π_X^{-1}` as a functor
`D^+(X) ⥤ D^+(LC_{Zar}/Y)`. -/
theorem proper_smallDerivedPushforward_piInverse_isomorphic_lcZarDerivedPushforward_piInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (DXplus : Type (u + 1)) [Category.{u} DXplus]
    (DYplus : Type (u + 1)) [Category.{u} DYplus]
    (DLCZarXplus : Type (u + 1)) [Category.{u} DLCZarXplus]
    (DLCZarYplus : Type (u + 1)) [Category.{u} DLCZarYplus]
    (piInverseDerivedPlusX : DXplus ⥤ DLCZarXplus)
    (piInverseDerivedPlusY : DYplus ⥤ DLCZarYplus)
    (smallPushforwardDerivedPlus : DXplus ⥤ DYplus)
    (lcZarPushforwardDerivedPlus : DLCZarXplus ⥤ DLCZarYplus) :
    IsIsomorphic
      (smallPushforwardDerivedPlus ⋙ piInverseDerivedPlusY)
      (piInverseDerivedPlusX ⋙ lcZarPushforwardDerivedPlus) := sorry

end
