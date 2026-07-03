import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_40_1 (from Chap21) -/
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

/-! ### Lemma_21_40_2 (from Chap21) -/
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
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}]
variable [∀ V : X, HasProjectiveResolutions ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]
variable [(projectionAbelianInverseImage X P).IsRightAdjoint]
variable [(projectionAbelianLowerShriek X P).Additive]
variable [HasProjectiveResolutions
  (Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})]

/-- The pullback precomposition functor on fiberwise abelian presheaves, written explicitly so
this file can state the projective-preservation assumption needed by
`fiberCategoryHomologySheaf`. -/
private abbrev fiberPullbackPrecomp
    {U V : X} (f : V ⟶ U) :
    ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      ((P.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (Functor.whiskeringLeft (P.p.Fiber U)ᵒᵖ (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v}).obj
    (((canonicalPullbackChoice P.p).pullbackFunctor f).op)

variable [∀ ⦃U V : X⦄ (f : V ⟶ U), (fiberPullbackPrecomp X P f).PreservesProjectiveObjects]

-- Proof sketch: for `n = 0`, this is Lemma `21.38.8`, which identifies `π_! ℱ` with the
-- sheafification of the fiberwise colimit presheaf, i.e. with `L_0(ℱ)`. Lemma `21.40.1` and the
-- vanishing argument from the Stacks proof show that `n ↦ fiberCategoryHomologySheaf X P ℱ.1 n`
-- forms the universal delta functor extending degree zero, so uniqueness of universal delta
-- functors identifies it with the left derived functors of `π_!`.
/-- Lemma 21.40.2: under the assumptions of Situation `21.38.1`, for an abelian sheaf `ℱ` on the
total site of `P` and `n ≥ 0`, the `n`-th left derived functor `L_n\pi_!(\mathcal F)` of the
abelian lower shriek is canonically isomorphic to the sheaf `L_n(\mathcal F)` constructed in
Lemma `21.40.1`, namely `fiberCategoryHomologySheaf X P ℱ.1 n`. -/
theorem projectionAbelianLowerShriek_leftDerived_isomorphic_fiberCategoryHomologySheaf
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIsomorphic
      (((projectionAbelianLowerShriek X P).leftDerived n).obj ℱ)
      (fiberCategoryHomologySheaf X P ℱ.1 n) := sorry

end

end FibredCategoryOver
end CategoryTheory

/-! ### Lemma_21_40_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D)

/-- The target object `U` viewed in the fiber category over its image in the base site. -/
abbrev comparisonIndexTargetFiberObj (U : S.C.S) :
    Functor.Fiber S.C.p ((S.C.p).obj U) :=
  mk rfl

/-- The comparison functor on the fibers over `p(U)`, obtained by restricting the morphism of
fibred categories `u : \mathcal C' \to \mathcal C`. -/
abbrev comparisonFiberUnderlyingFunctor (U : S.C.S) :
    Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C.S :=
  (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ S.u.G

/-- The restricted comparison functor lands in the fiber over `p(U)`, so its composite with the
projection to the base is the constant functor at `p(U)`. -/
private theorem comparisonFiberUnderlyingFunctor_comp_eq_const (U : S.C.S) :
    comparisonFiberUnderlyingFunctor S U ⋙ S.C.p =
      (Functor.const (Functor.Fiber S.C'.p ((S.C.p).obj U))).obj ((S.C.p).obj U) := by
  calc
    comparisonFiberUnderlyingFunctor S U ⋙ S.C.p =
        (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ S.C'.p := by
          simpa [comparisonFiberUnderlyingFunctor] using congrArg
            (fun F ↦
              (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ F)
            S.u.w
    _ = (Functor.const (Functor.Fiber S.C'.p ((S.C.p).obj U))).obj ((S.C.p).obj U) :=
      fiberInclusion_comp_eq_const

/-- The comparison functor on the fibers over `p(U)`, obtained by restricting the morphism of
fibred categories `u : \mathcal C' \to \mathcal C`. -/
noncomputable abbrev comparisonFiberFunctor (U : S.C.S) :
    Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ Functor.Fiber S.C.p ((S.C.p).obj U) :=
  Functor.Fiber.inducedFunctor (comparisonFiberUnderlyingFunctor_comp_eq_const S U)

/-- The indexing category `\mathcal I_U` of pairs `(U', \varphi)` with
`\varphi : U \to u(U')` in the fiber over `p(U)`. -/
abbrev comparisonIndexCategory (U : S.C.S) :=
  StructuredArrow (comparisonIndexTargetFiberObj S U) (comparisonFiberFunctor S U)

/-- The presheaf `\mathcal F'_U` on `\mathcal I_U`, obtained by restricting `\mathcal F'` to the
source fiber and then projecting from `\mathcal I_U`. -/
noncomputable abbrev comparisonIndexRestrictionPresheaf
    (ℱ' : sourceAbelianSheafCat S) (U : S.C.S) :
    (comparisonIndexCategory S U)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (StructuredArrow.proj (comparisonIndexTargetFiberObj S U) (comparisonFiberFunctor S U)).op ⋙
    ((fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S).op) ⋙ ℱ'.1

variable [∀ U : S.C.S,
  HasProjectiveResolutions ((comparisonIndexCategory S U)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The objectwise homology group `H_n(\mathcal I_U, \mathcal F'_U)` attached to `U`. -/
def comparisonIndexHomologyObject
    (ℱ' : sourceAbelianSheafCat S) (n : ℕ) (U : S.C.S) :
    AddCommGrpCat.{max u v} :=
  categoryHomology (comparisonIndexRestrictionPresheaf S ℱ' U) n

variable [HasWeakSheafify (targetTopology S) AddCommGrpCat.{max u v}]
variable [(abelianInverseImage S).IsRightAdjoint]
variable [(abelianLowerShriek S).Additive]
variable [HasProjectiveResolutions (sourceAbelianSheafCat S)]

-- Proof sketch: factor the comparison functor `u` through the fibred category `\mathcal C''`
-- of Categories, Lemma `4.33.14`, where the first stage has exact lower shriek and the second
-- stage is covered by Lemma `21.40.2`. The construction of `\mathcal C''` identifies each fiber
-- `\mathcal C''_U` with `\mathcal I_U`, and the restricted sheaf with `\mathcal F'_U`. The
-- proof also supplies the restriction maps on the objectwise rule `U ↦ H_n(\mathcal I_U,
-- \mathcal F'_U)`, producing the presheaf whose sheafification computes `L_n g_!(\mathcal F')`.
/-- Lemma 21.40.3: in Situation `21.38.3`, for an abelian sheaf `\mathcal F'` on `\mathcal C'`
and `n \ge 0`, the `n`-th left derived lower shriek `L_n g_!(\mathcal F')` is canonically
isomorphic to the sheaf associated to the presheaf sending an object `U` of `\mathcal C` to the
homology group `H_n(\mathcal I_U, \mathcal F'_U)`, where `\mathcal I_U` is the fiberwise
comparison indexing category defined above and `\mathcal F'_U` is the induced presheaf on
`\mathcal I_U`. -/
theorem abelian_lower_shriek_left_derived_isomorphic_comparison_index_homology_sheaf
    (ℱ' : sourceAbelianSheafCat S) (n : ℕ) :
    ∃ P : S.C.Sᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (∀ U : S.C.S, P.obj (op U) = comparisonIndexHomologyObject S ℱ' n U) ∧
        IsIsomorphic
          (((abelianLowerShriek S).leftDerived n).obj ℱ')
          ((presheafToSheaf (targetTopology S) AddCommGrpCat.{max u v}).obj P) := sorry

end

end FibredCategoryOver
end CategoryTheory
