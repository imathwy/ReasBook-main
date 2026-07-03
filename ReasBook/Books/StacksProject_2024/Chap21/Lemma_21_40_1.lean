import Mathlib
import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap21.Example_21_39_2_Computing_homology
import StacksProject_2024.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}]
variable [∀ V : X, HasProjectiveResolutions ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The restriction of an abelian presheaf on the total category to the opposite of the fiber
over `V`. -/
private abbrev fiberRestrictionPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (V : X) :
    (P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  ((Functor.Fiber.fiberInclusion : P.p.Fiber V ⥤ P.S).op) ⋙ ℱ

/-- Precomposition along the chosen pullback functor between fibers over a morphism in the base
site. -/
private abbrev fiberPullbackPrecomp {U V : X} (f : V ⟶ U) :
    ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      ((P.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (Functor.whiskeringLeft (P.p.Fiber U)ᵒᵖ (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v}).obj
    (((canonicalPullbackChoice P.p).pullbackFunctor f).op)

/-- The colimit functor on abelian presheaves over the fiber above `V`. -/
private abbrev fiberColimitFunctor (V : X) :
    ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v} :=
  colim

variable [∀ ⦃U V : X⦄ (f : V ⟶ U), (fiberPullbackPrecomp X P f).PreservesProjectiveObjects]

/-- The restriction component on fiberwise abelian presheaves induced by a chosen strongly
cartesian lift over `f`. -/
private abbrev fiberRestrictionComparisonApp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) (x : (P.p.Fiber U)ᵒᵖ) :
    (fiberRestrictionPresheaf X P ℱ U).obj x ⟶
      (((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
        fiberRestrictionPresheaf X P ℱ V).obj x :=
  ℱ.map (op ((canonicalPullbackChoice P.p).map f x.unop))

-- Proof sketch: for a morphism in the fiber over `U`, naturality is the contravariant
-- functoriality of `ℱ` applied to the commutative square determined by the chosen pullback
-- functor on fibers.
/-- The chosen pullback maps define a natural transformation on fiber restrictions. -/
private theorem fiberRestrictionComparison_naturality
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    ∀ {x y : (P.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (fiberRestrictionPresheaf X P ℱ U).map g ≫
          fiberRestrictionComparisonApp X P ℱ f y =
        fiberRestrictionComparisonApp X P ℱ f x ≫
          (((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
            fiberRestrictionPresheaf X P ℱ V).map g := sorry

/-- The natural transformation on fiber restrictions induced by pullback along `f`. -/
private abbrev fiberRestrictionComparison
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) :
    fiberRestrictionPresheaf X P ℱ U ⟶
      (((canonicalPullbackChoice P.p).pullbackFunctor f).op ⋙
        fiberRestrictionPresheaf X P ℱ V) where
  app x := fiberRestrictionComparisonApp X P ℱ f x
  naturality := fun {_ _} g ↦ fiberRestrictionComparison_naturality X P ℱ f g

-- Proof sketch: this is the standard naturality identity `colimit.pre_map` for precomposition by
-- the pullback functor on fibers.
/-- The colimit comparison attached to pullback on fibers is natural in the abelian presheaf on
the target fiber. -/
private theorem fiberPullbackColimitComparison_naturality
    {U V : X} (f : V ⟶ U) :
    ∀ {ℱ 𝒢 : (P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} (τ : ℱ ⟶ 𝒢),
      (fiberColimitFunctor X P U).map
          ((fiberPullbackPrecomp X P f).map τ) ≫
        Limits.colimit.pre 𝒢 (((canonicalPullbackChoice P.p).pullbackFunctor f).op) =
          Limits.colimit.pre ℱ (((canonicalPullbackChoice P.p).pullbackFunctor f).op) ≫
            (fiberColimitFunctor X P V).map τ := sorry

/-- The canonical natural transformation from the colimit over the pulled-back fiber diagram to
the colimit over the original fiber diagram. -/
private abbrev fiberPullbackColimitComparison
    {U V : X} (f : V ⟶ U) :
    fiberPullbackPrecomp X P f ⋙ fiberColimitFunctor X P U ⟶
      fiberColimitFunctor X P V where
  app ℱ := Limits.colimit.pre ℱ (((canonicalPullbackChoice P.p).pullbackFunctor f).op)
  naturality := fun {_ _} τ ↦ fiberPullbackColimitComparison_naturality X P f τ

/-- The canonical comparison from the category homology of the pulled-back fiber presheaf to the
category homology of the original fiber presheaf. -/
private abbrev categoryHomologyPullbackComparison
    {U V : X} (f : V ⟶ U)
    (ℱ : (P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology ((fiberPullbackPrecomp X P f).obj ℱ) n ⟶
      categoryHomology ℱ n :=
  let Pℱ : ProjectiveResolution ℱ := projectiveResolution ℱ
  let Ppull : ProjectiveResolution ((fiberPullbackPrecomp X P f).obj ℱ) :=
    projectiveResolution ((fiberPullbackPrecomp X P f).obj ℱ)
  let Pmap : ProjectiveResolution ((fiberPullbackPrecomp X P f).obj ℱ) :=
    (fiberPullbackPrecomp X P f).mapProjectiveResolution Pℱ
  let chainMap :
      ((fiberColimitFunctor X P U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Ppull.complex ⟶
      ((fiberColimitFunctor X P V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Pℱ.complex :=
    ((fiberColimitFunctor X P U).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (𝟙 _) Ppull Pmap) ≫
      (NatTrans.mapHomologicalComplex (fiberPullbackColimitComparison X P f)
        (ComplexShape.down ℕ)).app Pℱ.complex
  let srcIso := Ppull.isoLeftDerivedObj
    (fiberColimitFunctor X P U) n
  let tgtIso := Pℱ.isoLeftDerivedObj
    (fiberColimitFunctor X P V) n
  srcIso.hom ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map chainMap ≫
      tgtIso.inv

/-- The restriction map on fiberwise category homology induced by a morphism in the base site. -/
private abbrev fiberCategoryHomologyRestriction
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : X} (f : V ⟶ U) (n : ℕ) :
    categoryHomology (fiberRestrictionPresheaf X P ℱ U) n ⟶
      categoryHomology (fiberRestrictionPresheaf X P ℱ V) n :=
  ((fiberColimitFunctor X P U).leftDerived n).map (fiberRestrictionComparison X P ℱ f) ≫
    categoryHomologyPullbackComparison X P f (fiberRestrictionPresheaf X P ℱ V) n

-- Proof sketch: for the identity arrow, the chosen pullback functor on the fiber is naturally
-- isomorphic to the identity, so both the map on left-derived colimits and the colimit
-- comparison reduce to identities.
/-- The fiberwise category-homology restriction is the identity on identity arrows. -/
private theorem fiberCategoryHomologyRestriction_id
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (U : X) :
    fiberCategoryHomologyRestriction X P ℱ (𝟙 U) n =
      𝟙 (categoryHomology (fiberRestrictionPresheaf X P ℱ U) n) := sorry

-- Proof sketch: compose the pullback functors on fibers and compare the resulting projective
-- resolution models for homology. The functoriality of left-derived colimits and the cocycle
-- identity for `colimit.pre` give the stated composition law.
/-- Fiberwise category-homology restrictions respect composition in the base site. -/
private theorem fiberCategoryHomologyRestriction_comp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    fiberCategoryHomologyRestriction X P ℱ (g ≫ f) n =
      fiberCategoryHomologyRestriction X P ℱ f n ≫
        fiberCategoryHomologyRestriction X P ℱ g n := sorry

-- Proof sketch: after unop-ing arrows in `Xᵒᵖ`, this is exactly the composition formula for the
-- underlying restriction maps on fiberwise category homology.
/-- The morphism part of `fiberCategoryHomologyPresheaf` respects composition. -/
private theorem fiberCategoryHomologyPresheaf_map_comp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    {U V W : Xᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberCategoryHomologyRestriction X P ℱ (f ≫ g).unop n =
      fiberCategoryHomologyRestriction X P ℱ f.unop n ≫
        fiberCategoryHomologyRestriction X P ℱ g.unop n := sorry

/-- The presheaf on the base site sending `V` to the category homology
`H_n(\mathcal C_V, \mathcal F|_{\mathcal C_V})`. -/
abbrev fiberCategoryHomologyPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj V := categoryHomology (fiberRestrictionPresheaf X P ℱ (unop V)) n
  map f := fiberCategoryHomologyRestriction X P ℱ f.unop n
  map_id V := fiberCategoryHomologyRestriction_id X P ℱ n (unop V)
  map_comp f g := fiberCategoryHomologyPresheaf_map_comp X P ℱ n f g

/-- The sheaf associated to the fiberwise category-homology presheaf. -/
abbrev fiberCategoryHomologySheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  (presheafToSheaf X.siteTopology AddCommGrpCat.{max u v}).obj
    (fiberCategoryHomologyPresheaf X P ℱ n)

/-- The underlying abelian presheaf of the associated abelian sheaf `\mathcal F^\#`. -/
abbrev associatedAbelianSheafPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (sheafToPresheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}).obj
    ((presheafToSheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}).obj ℱ)

-- Proof sketch: the canonical map `ℱ ⟶ ℱ^\#` induces a morphism between the fiberwise homology
-- presheaves. Using the explicit projective-resolution model for fiber homology, one proves this
-- morphism is locally bijective on the base site, hence its sheafification is an isomorphism.
/-- Lemma 21.40.1: for an abelian presheaf `\mathcal F` on the total category of a fibred
category over `X`, the sheaf associated to the presheaf
`V ↦ H_n(\mathcal C_V, \mathcal F|_{\mathcal C_V})` is canonically isomorphic to the same sheaf
constructed from the associated sheaf `\mathcal F^\#`. -/
theorem fiberCategoryHomologySheaf_isomorphic_of_associatedAbelianSheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIsomorphic
      (fiberCategoryHomologySheaf X P ℱ n)
      (fiberCategoryHomologySheaf X P (associatedAbelianSheafPresheaf X P ℱ) n) := sorry

end

end FibredCategoryOver
end CategoryTheory
