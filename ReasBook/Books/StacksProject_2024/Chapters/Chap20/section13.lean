import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_13_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u u₁ u₂ u₃

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The underlying morphism of presheafed spaces attached to a morphism of ringed spaces. -/
abbrev toPresheafedSpaceHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    X.toPresheafedSpace ⟶ Y.toPresheafedSpace :=
  f.hom

/-- The underlying continuous map of a morphism of ringed spaces. -/
abbrev baseMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  (toPresheafedSpaceHom f).base

/-- The morphism of structure sheaves attached to a morphism of ringed spaces. -/
abbrev structureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :=
  (toPresheafedSpaceHom f).c

/-- The open subset `f^{-1}(V)` of `X` attached to an open subset `V ⊆ Y`. -/
abbrev preimageOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Opens X.carrier :=
  Opens.comap (baseMap f).hom V

/-- The ring of sections `Γ(U, \mathcal O_X)` on an open subset `U ⊆ X`. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- Modules over the section ring of an open subset carry the standard derived category. -/
instance sectionsRingOnOpen_hasDerivedCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  HasDerivedCategory.standard _

/-- The sections functor `\Gamma(U, -)` on `\mathcal O_X`-modules. -/
abbrev moduleSectionsFunctorAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    SheafOfModules ((RingedSpace.ringCatSheaf X)) ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation ((RingedSpace.ringCatSheaf X)) (op U)

/-- The induced functor `K^+(X) ⥤ D^+(\Gamma(U, \mathcal O_X)\text{-Mod})` on bounded-below
homotopy and derived categories of section modules. -/
abbrev moduleSectionsHomotopyToDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ObjectProperty.FullSubcategory
        (CategoryTheory.boundedBelowHomotopyProperty
          (SheafOfModules ((RingedSpace.ringCatSheaf X)))) ⥤
      boundedBelowDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (moduleSectionsFunctorAtOpen X U)

/-- The sections functor on an open subset is additive. -/
instance moduleSectionsFunctorAtOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsFunctorAtOpen X U).Additive := sorry

/-- Direct image on `\mathcal O`-modules is additive. -/
instance ringedSpaceModulePushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Hom.pushforward f).Additive := sorry

/-- The map on section rings over `V` induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  (structureSheafHom f).app (op V)

/-- Restriction of scalars along the map on sections `Γ(V, \mathcal O_Y) → Γ(f^{-1}(V),
\mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

/-- Restriction of scalars on section modules is additive. -/
instance moduleSectionsRestrictionFunctor_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (moduleSectionsRestrictionFunctor f V).Additive := by
  infer_instance

-- Proof sketch: both composites evaluate an `\mathcal O_X`-module on `f^{-1}(V)` and then
-- regard the resulting module as a `\Gamma(V, \mathcal O_Y)`-module via the map `f^\sharp(V)`.
/-- The underived identity `restriction ∘ \Gamma(f^{-1}(V), -) = \Gamma(V, -) ∘ f_*`. -/
theorem moduleSectionsFunctorAtPreimage_comp_restriction_eq_pushforward_comp_sections
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    moduleSectionsFunctorAtOpen X (preimageOpen f V) ⋙ moduleSectionsRestrictionFunctor f V =
      RingedSpace.Hom.pushforward f ⋙ moduleSectionsFunctorAtOpen Y V := sorry

/-- The composite `\Gamma(V, -) ∘ f_*` admits a bounded-below right derived functor. -/
instance modulePushforward_sectionsAtOpen_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
          (moduleSectionsFunctorAtOpen Y V))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := sorry

/-- The composite `f_*` followed by the localization functor on `D^+(Y)` admits the required
bounded-below right derived functor. -/
instance modulePushforward_identity_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
          (𝟭 (SheafOfModules ((RingedSpace.ringCatSheaf Y)))))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := sorry

local instance modulePushforward_Q_composite_hasRightDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
        (CategoryTheory.boundedBelowHomotopyQuasiIso
          (SheafOfModules ((RingedSpace.ringCatSheaf Y)))).Q)
      (CategoryTheory.boundedBelowHomotopyQuasiIso
        (SheafOfModules ((RingedSpace.ringCatSheaf X)))) := by
  sorry

/-- The functor `\Gamma(V, -)` admits a bounded-below right derived functor. -/
instance moduleSectionsFunctorAtOpen_hasRightDerivedFunctor
    (Y : RingedSpace.{u}) (V : Opens Y.carrier) :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
        (moduleSectionsFunctorAtOpen Y V))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf Y)))) := sorry

-- Proof sketch: use the previous underived identity to rewrite the source composite as
-- `restriction ∘ Γ(f^{-1}(V), -)`. Since restriction of scalars is exact, the Grothendieck
-- comparison criterion applies, and Lemma `20.11.10` supplies the required acyclicity of
-- `Γ(V, -)` on pushforwards of injective `\mathcal O_X`-modules.
/-- Lemma 20.13.1: for an open subset `V ⊆ Y` and `U = f^{-1}(V)`, the canonical bounded-below
Grothendieck comparison morphism for the composite `\Gamma(V, -) \circ f_*`, equivalently for
`restriction \circ \Gamma(U, -)`, is an isomorphism. This is the commutativity of the diagram
with `R\Gamma(U, -)`, `Rf_*`, `R\Gamma(V, -)`, and restriction on `D^+`. -/
theorem modulePushforward_sectionsAtOpen_boundedBelowRightDerivedCompComparison_isIso
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso
      (CategoryTheory.Functor.rightDerivedCompComparison
        (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))
        (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))
        (CategoryTheory.mapBoundedBelowHomotopyCategory
          (RingedSpace.Hom.pushforward f))
        (moduleSectionsHomotopyToDerived Y V)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_13_2 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: unfold the definition of module pushforward on sections and then forget the module
-- structures to additive groups. Evaluating `f_* ℱ` on the terminal open subset of `Y` is by
-- definition evaluation of `ℱ` on the inverse image of that open, and `f^{-1}(Y) = X`; applying
-- this termwise to an injective resolution gives the additive-complex identity
-- `Γ(X, \mathcal I^\bullet) = Γ(Y, f_* \mathcal I^\bullet)` used in the remark.
/-- Remark 20.13.2: for a morphism of ringed spaces `f : X ⟶ Y`, the global sections of the
pushforward `f_* \mathcal F`, after forgetting the module structures, agree with the global
sections of `\mathcal F`. Applied termwise to an injective resolution `\mathcal I^\bullet`, this
is the identity
`\Gamma(X, \mathcal I^\bullet) = \Gamma(Y, f_* \mathcal I^\bullet)` used in the explanation of
Lemma `20.13.1`. -/
lemma modulePushforward_underlyingGlobalSections_eq_underlyingGlobalSections
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (ℱ : (RingedSpace.Modules X)) :
    (forget₂ (ModuleCat (globalSectionsRing Y)) AddCommGrpCat).obj
        (((RingedSpace.Hom.pushforward f).obj ℱ).1.obj (op (⊤ : Opens Y.carrier))) =
      (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat).obj
        (ℱ.1.obj (op (⊤ : Opens X.carrier))) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_13_3 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

section OpenCohomology

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

-- Proof sketch: compute `H^i(U, \mathcal F)` as the `i`-th right derived functor of the sections
-- functor `\Gamma(U, -)` on `\mathcal O_X`-modules, then forget the `\Gamma(U, \mathcal O_X)`-
-- module structure. The same injective resolution, viewed through `SheafOfModules.toSheaf`,
-- computes the abelian-sheaf cohomology group on `U`.
/-- Lemma 20.13.3 (1): for an open subset `U ⊆ X`, the degree-`i` cohomology of an
`\mathcal O_X`-module `\mathcal F` computed in the category of `\mathcal O_X`-modules agrees,
after forgetting the module structure, with the degree-`i` cohomology of the underlying abelian
sheaf of `\mathcal F` on `U`. -/
theorem moduleCohomologyAtOpen_underlying_isomorphic_underlyingSheafCohomology
    (ℱ : (RingedSpace.Modules X)) (U : Opens X.carrier) (i : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} (X.presheaf.obj (op U))) AddCommGrpCat.{u}).obj
        (moduleCohomologyAtOpen U ℱ i))
      (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' i U) := sorry

end OpenCohomology

section HigherDirectImage

variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable [HasInjectiveResolutions
  (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

-- Proof sketch: forget an injective resolution of `\mathcal F` in `(RingedSpace.Modules X)` to an
-- injective resolution of the underlying abelian sheaf, use Remark `20.13.2` to identify the
-- section complexes termwise, and then apply Lemma `20.7.3` to identify the resulting right
-- derived direct images.
/-- Lemma 20.13.3 (2): for a morphism of ringed spaces `f : X ⟶ Y`, the degree-`i` higher direct
image of an `\mathcal O_X`-module `\mathcal F`, viewed as an abelian sheaf on `Y`, agrees with
the degree-`i` higher direct image of the underlying abelian sheaf of `\mathcal F`. -/
theorem higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf
    (f : X ⟶ Y)
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).Additive]
    (ℱ : (RingedSpace.Modules X)) (i : ℕ) :
    IsIsomorphic
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj
        (((RingedSpace.Hom.pushforward f).rightDerived i).obj ℱ))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).rightDerived i).obj
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ)) := sorry

end HigherDirectImage

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_13_4_Leray_spectral_sequence (from Chap20) -/
open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local instance (X : RingedSpace.{u}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Modules X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (RingedSpace.Modules X)

/-- The underlying additive sheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The degree-`p` global sheaf cohomology of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleGlobalCohomology {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).H' p (⊤ : Opens X.carrier)

/-- The bounded-below derived category `D^+(\mathcal O_X)` of `\mathcal O_X`-modules on a
ringed space. -/
abbrev ModuleDerivedPlus (X : RingedSpace.{u}) :=
  CategoryTheory.boundedBelowDerivedCategory (RingedSpace.Modules X)

/-- A bounded-below complex of `\mathcal O_X`-modules defines an object of `D^+(\mathcal O_X)`.
-/
abbrev moduleComplexToDerivedPlus (X : RingedSpace.{u})
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))] :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤ ModuleDerivedPlus X :=
  CategoryTheory.boundedBelowCochainComplexToDerivedBelow (𝟭 (RingedSpace.Modules X))

/-- The bounded-below right derived direct-image functor on `\mathcal O_X`-modules. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (modulePushforward f))
    (mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Modules X))
    (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    (RingedSpace.Modules Y) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Y)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The `E_2^{p,q}` term in the Leray spectral sequence of a bounded-below complex, written as the
global degree-`p` cohomology of the `q`-th cohomology sheaf of `Rf_* K`. -/
abbrev leraySpectralSequencePageTwoTerm
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (p q : ℕ) :
    AddCommGrpCat.{u} :=
  moduleGlobalCohomology
    (modulePushforwardDerivedPlusCohomology f ((moduleComplexToDerivedPlus X).obj K) q) p

/-- A packaged Leray spectral sequence for a bounded-below complex of `\mathcal O_X`-modules on a
morphism of ringed spaces `f : X ⟶ Y`. -/
structure LeraySpectralSequenceBoundedBelow
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) where
  /-- The chosen cohomological spectral sequence, starting on the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u}
  /-- The `E₂`-page identifies with `H^p(Y, R^q f_* K)`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        leraySpectralSequencePageTwoTerm f K p q
  /-- The chosen abutment additive groups of the spectral sequence. -/
  abutment : ℕ → AddCommGrpCat.{u}
  /-- The abutment identifies with the hypercohomology of `K` on `X`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleDerivedGlobalSectionsCohomology X K (Int.ofNat n)

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite of
-- `modulePushforward f` with the additive global-sections functor on `Y`. The comparison from
-- Lemma `20.13.1`, together with the global-sections identification of Remark `20.13.2`, rewrites
-- the abutment as the hypercohomology of `K` on `X`, and the `E₂`-page becomes
-- `H^p(Y, R^q f_* K)`.
/-- Lemma 20.13.4 (Leray spectral sequence): for a morphism of ringed spaces `f : X ⟶ Y` and a
bounded-below complex `K` of `\mathcal O_X`-modules, there is a cohomological spectral sequence
with `E_2^{p,q} = H^p(Y, R^q f_* K)` converging to the hypercohomology `H^{p + q}(X, K)`. -/
theorem exists_leraySpectralSequence_boundedBelow
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    Nonempty (LeraySpectralSequenceBoundedBelow f K) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_13_5 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The category of additive commutative groups has its standard derived category. -/
local instance addCommGrpCat_hasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

-- Proof sketch: replace `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` by the morphism of ringed
-- spaces `f' : (X, \mathcal O_X) ⟶ (Y, f_* \mathcal O_X)`. By Lemma `20.13.3`, the Leray
-- spectral sequence for `f'` has the same underlying additive `E_r^{p,q}` terms as the usual
-- Leray spectral sequence for `f` for every `r ≥ 2`. Since
-- `Γ(Y, f_* \mathcal O_X) = Γ(X, \mathcal O_X)`, these terms inherit a
-- `Γ(X, \mathcal O_X)`-module structure.
/-- Remark 20.13.5: in the bounded-below-complex form of the Leray spectral sequence for
`f : X ⟶ Y`, every page entry `E_r^{p,q}` with `r ≥ 2` can be viewed as a
`\Gamma(X, \mathcal O_X)`-module. Concretely, there exists an object of
`ModuleCat (globalSectionsRing X)` whose underlying additive group is the given
`E_r^{p,q}`-term. -/
theorem leraySpectralSequence_page_has_globalSectionsModule_lift
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(RingedSpace.Hom.pushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (RingedSpace.Hom.pushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X))
    (S : LeraySpectralSequenceBoundedBelow f K)
    {r : ℕ} (hr : 2 ≤ r) (p q : ℕ) :
    ∃ M : ModuleCat (globalSectionsRing X),
      IsIsomorphic
        ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat).obj M)
        ((S.spectralSequence.page r).X (p, q)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_13_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(modulePushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules ((RingedSpace.ringCatSheaf X)))]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every higher direct image
-- `R^q f_* ℱ` with `q > 0` vanishes, the `E₂`-page is concentrated on the `q = 0` row, so the
-- abutment identifies with the `p`-th cohomology of `f_* ℱ` on `Y`.
/-- Lemma 20.13.6 (1): if the higher direct images `R^q f_* \mathcal F` vanish for `q > 0`,
then the global degree-`p` cohomology of `\mathcal F` on `X` is canonically isomorphic to the
global degree-`p` cohomology of `f_* \mathcal F` on `Y`. -/
theorem globalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (hRq : ∀ q : ℕ, 0 < q → IsZero (((modulePushforward f).rightDerived q).obj ℱ))
    (p : ℕ) :
    IsIsomorphic (moduleGlobalCohomology ℱ p)
      (moduleGlobalCohomology ((modulePushforward f).obj ℱ) p) := sorry

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every positive-degree
-- cohomology group of every higher direct image `R^q f_* ℱ` vanishes on `Y`, the `E₂`-page is
-- concentrated in the `p = 0` column, so the abutment in total degree `q` identifies with the
-- edge term `H^0(Y, R^q f_* ℱ)`.
/-- Lemma 20.13.6 (2): if `H^p(Y, R^q f_* \mathcal F) = 0` for all `q` and all `p > 0`, then
the global degree-`q` cohomology of `\mathcal F` on `X` is canonically isomorphic to the degree-`0`
cohomology of the higher direct image `R^q f_* \mathcal F` on `Y`. -/
theorem globalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (moduleGlobalCohomology (((modulePushforward f).rightDerived q).obj ℱ) p))
    (q : ℕ) :
    IsIsomorphic (moduleGlobalCohomology ℱ q)
      (moduleGlobalCohomology (((modulePushforward f).rightDerived q).obj ℱ) 0) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_13_7 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [(mapBoundedBelowHomotopyToDerivedBelow (𝟭 (RingedSpace.Modules Y))).IsLocalization
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
    mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward g))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
    mapBoundedBelowHomotopyToDerivedBelow (𝟭 (RingedSpace.Modules Y)))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward g))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (RingedSpace.Hom.pushforward g))
  (HomotopyCategory.quasiIso (RingedSpace.Modules Y) (ComplexShape.up ℤ))]

-- Proof sketch: the ordinary pushforwards compose, so the canonical comparison morphism from
-- `R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*`. Apply Lemma `13.22.1`; by Lemma `20.11.10`, `f_*` sends injectives
-- to sheaves whose higher cohomology on opens vanishes for `g`, and Lemma `20.7.3` identifies
-- the higher direct images of `g_*` with those cohomology sheaves, giving the required
-- right-acyclicity.
/-- Lemma 20.13.7: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical comparison morphism from the right derived direct image of the composite to the
composite of the right derived direct images is an isomorphism; this formalizes
`R(g \circ f)_* = Rg_* \circ Rf_*` on `D^{+}`. -/
lemma modulePushforward_rightDerivedCompComparison_isIso :
    IsIso (rightDerivedCompComparison
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))
      (RingedSpace.Hom.pushforward f) (RingedSpace.Hom.pushforward g)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_13_8_Relative_Leray_spectral_sequence (from Chap20) -/
open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}}

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on a ringed
space. -/
abbrev ModuleDerivedPlus (X : RingedSpace.{u}) :=
  AlgebraicGeometry.boundedBelowDerivedCategory (RingedSpace.Modules X)

/-- The bounded-below right derived direct-image functor on module sheaves over ringed
spaces. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  Functor.totalRightDerived
    (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
    (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
    (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    (RingedSpace.Modules Y) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Y)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The degree-`n` cohomology sheaf of the bounded-below derived direct image
`R(g \circ f)_* K`. -/
abbrev moduleCompositePushforwardDerivedPlusCohomology
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) (n : ℕ) :
    (RingedSpace.Modules Z) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Z)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Z) n).obj
    ((modulePushforwardDerivedPlus (f ≫ g)).obj K))

/-- A functorial package for the relative Leray spectral sequence attached to composable
morphisms of ringed spaces. -/
structure RelativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially in
  the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    (RingedSpace.Modules X) ⥤ E₂CohomologicalSpectralSequenceNat (RingedSpace.Modules Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (R^q f_* \mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        ((modulePushforward g).rightDerived p).obj
          (((modulePushforward f).rightDerived q).obj ℱ)
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : (RingedSpace.Modules X) → ℕ → (RingedSpace.Modules Z)
  /-- The abutment identifies with the higher direct images of the composite morphism
  `(g \circ f)_*`. -/
  targetIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (n : ℕ),
      abutment ℱ n ≅ ((modulePushforward (f ≫ g)).rightDerived n).obj ℱ

/-- A bounded-below-complex version of the relative Leray spectral sequence for composable
morphisms of ringed spaces. -/
structure RelativeLeraySpectralSequenceBoundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) where
  /-- The cohomological spectral sequence attached to the bounded-below complex `K`, starting on
  the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat (RingedSpace.Modules Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (H^q(Rf_* K))`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        ((modulePushforward g).rightDerived p).obj
          (modulePushforwardDerivedPlusCohomology f K q)
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℕ → (RingedSpace.Modules Z)
  /-- The abutment identifies with the cohomology sheaves of `R(g \circ f)_* K`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleCompositePushforwardDerivedPlusCohomology f g K n

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite
-- of the two direct-image functors on sheaves of modules. Lemma `20.13.7` identifies the right
-- derived direct image of the composite with the composite of the right derived direct images, so
-- the `E₂`-page becomes `R^p g_* (R^q f_* \mathcal F)`. Naturality of the Grothendieck
-- construction yields functoriality in `\mathcal F`.
/-- Lemma 20.13.8 (Relative Leray spectral sequence): for composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z`, there is a cohomological spectral sequence functorial in an
`\mathcal O_X`-module `\mathcal F` whose `E_2^{p,q}`-term is
`R^p g_* (R^q f_* \mathcal F)` and whose abutment is `R^{p + q} (g \circ f)_* \mathcal F`. -/
theorem exists_relativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive] :
    Nonempty (RelativeLeraySpectralSequence f g) := sorry

-- Proof sketch: apply the bounded-below Grothendieck spectral sequence to the composable
-- direct-image functors `f_*` and `g_*` on sheaves of modules. The same comparison from Lemma
-- `20.13.7` identifies the abutment with the cohomology sheaves of `R(g \circ f)_* K`, and the
-- `E₂`-page is obtained by taking higher direct images of the cohomology sheaves of `Rf_* K`.
/-- A bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed spaces. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) :
    Nonempty (RelativeLeraySpectralSequenceBoundedBelow f g K) := sorry

end AlgebraicGeometry.RingedSpace
