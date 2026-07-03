import Mathlib
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_23_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Ab}(\mathcal C)` of sheaves of abelian groups on the site
`(\mathcal C, J)`. -/
abbrev SiteAbelianSheaf :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The category of sequential inverse systems of abelian sheaves on the site `(\mathcal C, J)`.
-/
abbrev SiteAbelianSheafInverseSystem :=
  ℕᵒᵖ ⥤ SiteAbelianSheaf J

/-- The ordinary inverse-limit functor on sequential inverse systems of abelian sheaves on the
site `(\mathcal C, J)`. -/
abbrev siteAbelianSheafInverseLimitFunctor :
    SiteAbelianSheafInverseSystem J ⥤ SiteAbelianSheaf J :=
  lim

-- Proof sketch: limits in the sheaf category are computed objectwise from the ambient
-- presheaf category, so the inverse-limit functor preserves zero morphisms and addition
-- componentwise.
/-- The inverse-limit functor on sequential inverse systems of abelian sheaves is additive. -/
local instance siteAbelianSheafInverseLimitFunctor_additive :
    (siteAbelianSheafInverseLimitFunctor J).Additive := sorry

/-- The cochain-level inverse-limit functor from inverse systems of abelian sheaves on the site
to the derived category of abelian sheaves on the site. -/
abbrev siteAbelianSheafInverseLimitFunctorToDerived :
    CochainComplex (SiteAbelianSheafInverseSystem J) ℤ ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafInverseLimitFunctor J).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

-- Proof sketch: choose K-injective representatives in the abelian category of inverse systems
-- of abelian sheaves and apply inverse limit termwise; this computes the total right derived
-- functor of the cochain-level inverse-limit functor.
/-- The cochain-level inverse-limit functor on sequential inverse systems of abelian sheaves
admits a chosen right derived functor. -/
local instance siteAbelianSheafInverseLimitFunctorToDerived_hasRightDerivedFunctor :
    (siteAbelianSheafInverseLimitFunctorToDerived J).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ)) := sorry

/-- The chosen derived inverse-limit functor
`R lim : D(\mathcal C \times \mathbf N) ⥤ D(\mathcal C)`, modeled here by inverse systems of
abelian sheaves on the site. -/
abbrev siteAbelianSheafDerivedInverseLimitFunctor :
    DerivedCategory (SiteAbelianSheafInverseSystem J) ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafInverseLimitFunctorToDerived J).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ))

/-- The exact evaluation functor at the `n`th stage of a sequential inverse system of abelian
sheaves on the site. This is the site-theoretic restriction functor `i_n^{-1}` from the textbook
notation. -/
abbrev siteAbelianSheafEvaluation (n : ℕ) :
    SiteAbelianSheafInverseSystem J ⥤ SiteAbelianSheaf J :=
  (evaluation ℕᵒᵖ (SiteAbelianSheaf J)).obj (op n)

/-- The `n`th stage functor on derived categories obtained by applying the restriction
`i_n^{-1}` stagewise. -/
abbrev siteAbelianSheafDerivedEvaluation (n : ℕ) :
    DerivedCategory (SiteAbelianSheafInverseSystem J) ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafEvaluation J n).mapDerivedCategory

/-- Stagewise evaluation on derived categories is the right derived functor of stagewise
evaluation on cochain complexes. -/
local instance siteAbelianSheafDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (siteAbelianSheafDerivedEvaluation J n).IsRightDerivedFunctor
      ((siteAbelianSheafEvaluation J n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ)) := sorry

/-- The transition natural transformation from stage `n + 1` to stage `n` on sequential inverse
systems of abelian sheaves on the site. -/
abbrev siteAbelianSheafEvaluationStep (n : ℕ) :
    siteAbelianSheafEvaluation J (n + 1) ⟶ siteAbelianSheafEvaluation J n :=
  (evaluation ℕᵒᵖ (SiteAbelianSheaf J)).map ((homOfLE (Nat.le_succ n)).op)

/-- The induced transition natural transformation between the stagewise restriction functors on
derived categories. -/
abbrev siteAbelianSheafDerivedEvaluationStep (n : ℕ) :
    siteAbelianSheafDerivedEvaluation J (n + 1) ⟶
      siteAbelianSheafDerivedEvaluation J n :=
  Functor.rightDerivedNatTrans
    (siteAbelianSheafDerivedEvaluation J (n + 1))
    (siteAbelianSheafDerivedEvaluation J n)
    ((siteAbelianSheafEvaluation J (n + 1)).mapDerivedCategoryFactors.inv)
    ((siteAbelianSheafEvaluation J n).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (siteAbelianSheafEvaluationStep J n)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The tower `(K_n)_n` in `D(\mathcal C)` attached to
`K ∈ D(\mathcal C \times \mathbf N)`, modeled here by stagewise restriction of an inverse-system
object in `D(ℕᵒᵖ ⥤ \mathrm{Ab}(\mathcal C))`. -/
abbrev siteAbelianSheafDerivedInverseLimitTower
    (K : DerivedCategory (SiteAbelianSheafInverseSystem J)) :
    ℕᵒᵖ ⥤ DerivedCategory (SiteAbelianSheaf J) :=
  @Functor.ofOpSequence (DerivedCategory (SiteAbelianSheaf J)) _
    (fun n ↦ (siteAbelianSheafDerivedEvaluation J n).obj K)
    (fun n ↦ (siteAbelianSheafDerivedEvaluationStep J n).app K)

-- Proof sketch: choose a representing inverse system of cochain complexes of abelian sheaves for
-- `K`, restrict it stagewise along the embeddings `i_n`, and compare the chosen derived
-- inverse-limit functor with the Milnor distinguished triangle defining `R lim_n K_n`.
/-- Lemma 21.23.1: let `(\mathcal C, J)` be a site and let `K` be an object of
`D(\mathcal C \times \mathbf N)`, modeled here as an object of
`D(ℕᵒᵖ ⥤ \mathrm{Ab}(\mathcal C))`. If `K_n = i_n^{-1}K` denotes the stagewise restriction to
`\mathcal C`, then the chosen object `R lim(K)` is a derived limit of the tower `(K_n)_n`.
Equivalently, `R lim(K) ≅ R lim_n K_n` in `D(\mathcal C)`. -/
theorem siteAbelianSheafDerivedInverseLimit_isDerivedLimit_of_stagewiseRestriction
    (K : DerivedCategory (SiteAbelianSheafInverseSystem J)) :
    CategoryTheory.IsDerivedLimit (siteAbelianSheafDerivedInverseLimitTower J K)
      ((siteAbelianSheafDerivedInverseLimitFunctor J).obj K) := sorry

end

end CategoryTheory

/-! ### Lemma_21_23_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.2:
- primary domain: derived global/objectwise sections on a ringed site and the Milnor short exact
  sequence for sequential derived limits in `D(\operatorname{Ab})`;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.moduleGlobalSectionsDerived`,
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction: the ambient module category and derived category are already owned by
  `RingedSite.Hom.ModuleCat` and `RingedSite.Hom.ModuleDerived`; the relevant derived functors are
  already owned by `moduleGlobalSectionsDerived` and `moduleSectionsAsAbelianDerived`; the Milnor
  short exact sequence is already owned by `derivedLimit_cohomology_shortExact`, whose left term
  is the canonical `firstDerivedLimit`, not a raw cokernel wrapper;
- primitive data: a ringed site `X`, optionally an object `U : X`, a sequential inverse system
  `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`, a chosen derived limit `K`, and a cohomological degree `m`;
- derived API: preservation of derived limits by the canonical derived sections functors, and the
  resulting Milnor short exact sequences on cohomology.

Source/core/bridge triage:
- `source-facing`: the four ringed-site statements below about `RΓ(\mathcal C,-)` and
  `RΓ(U,-)`;
- `core/canonical`: `ModuleCat`, `ModuleDerived`, `moduleGlobalSectionsDerived`,
  `moduleSectionsAsAbelianDerived`, and `derivedLimit_cohomology_shortExact`;
- `bridge/view`: this file, which specializes the canonical Chapter 15 and Chapter 19 owners to
  the ringed-site functors without introducing a parallel local wrapper API.
-/

section GlobalSections

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]

-- Proof sketch: specialize Lemma `19.13.6` to the canonical derived global-sections functor
-- `moduleGlobalSectionsDerived X`.
/-- Lemma 21.23.2 (1): for a ringed site `X`, the canonical derived global-sections functor
`R\Gamma(\mathcal C,-)` carries a derived limit of a sequential inverse system in
`D(\mathcal O_X)` to the derived limit of the stagewise derived global sections. -/
theorem ringedSiteDerivedGlobalSections_preservesDerivedLimit
    {Ksys : ℕᵒᵖ ⥤ ModuleDerived X} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ moduleGlobalSectionsDerived X)
      ((moduleGlobalSectionsDerived X).obj K) := sorry

-- Proof sketch: apply the Milnor short exact sequence of Lemma `15.87.10` to the inverse system
-- `Ksys ⋙ moduleGlobalSectionsDerived X` in `D(\operatorname{Ab})`.
/-- Lemma 21.23.2 (4): for a ringed site `X`, a sequential inverse system `(K_n)` in
`D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the global cohomology of
`K` fits into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(\mathcal C, K_n) \to H^m(\mathcal C, K) \to
\varprojlim H^m(\mathcal C, K_n) \to 0`. -/
theorem ringedSiteDerivedGlobalSections_cohomology_shortExact
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ moduleGlobalSectionsDerived X) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleGlobalSectionsDerived X).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleGlobalSectionsDerived X).obj K) ⟶
          limit
            ((Ksys ⋙ moduleGlobalSectionsDerived X) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end GlobalSections

section SectionsOverObject

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

-- Proof sketch: specialize Lemma `19.13.6` to the canonical derived sections functor
-- `moduleSectionsAsAbelianDerived X U`.
/-- Lemma 21.23.2 (2): for a ringed site `X` and an object `U : X`, the canonical derived sections
functor `R\Gamma(U,-)` carries a derived limit of a sequential inverse system in `D(\mathcal O_X)`
to the derived limit of the stagewise derived sections over `U`. -/
theorem ringedSiteDerivedSectionsOverObject_preservesDerivedLimit
    (U : X)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    {Ksys : ℕᵒᵖ ⥤ ModuleDerived X} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ moduleSectionsAsAbelianDerived X U)
      ((moduleSectionsAsAbelianDerived X U).obj K) := sorry

-- Proof sketch: apply the Milnor short exact sequence of Lemma `15.87.10` to the inverse system
-- `Ksys ⋙ moduleSectionsAsAbelianDerived X U` in `D(\operatorname{Ab})`.
/-- Lemma 21.23.2 (3): for a ringed site `X`, an object `U : X`, a sequential inverse system
`(K_n)` in `D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the
cohomology groups over `U` fit into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim H^m(U, K_n) \to 0`. -/
theorem ringedSiteDerivedSectionsOverObject_cohomology_shortExact
    (U : X)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleSectionsAsAbelianDerived X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((moduleSectionsAsAbelianDerived X U).obj K) ⟶
          limit
            ((Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end SectionsOverObject

/-! ### Lemma_21_23_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/-- The category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on the ringed site `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves on `X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {A B : Type u} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor induced by pushforward on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived Y :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The unbounded derived direct-image functor `Rf_*` on module sheaves. -/
abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The family of stages underlying a sequential inverse system in `D(\mathcal O_X)`. -/
abbrev inverseSystemFamily {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X) :
    ℕ → ModuleDerived X :=
  fun n ↦ Ksys.obj (op n)

/-- The Milnor difference endomorphism of `\prod_n K_n` attached to a sequential inverse system in
`D(\mathcal O_X)`. -/
def derivedLimitDifferenceMap {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n -
      Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map ((homOfLE (Nat.le_succ n)).op)

/-- A chosen sequential derived limit of a tower `(K_n)` in `D(\mathcal O_X)` is an object `K`
that fits into the standard Milnor distinguished triangle
`K ⟶ \prod_n K_n ⟶ \prod_n K_n ⟶ K[1]`. -/
def IsSequentialDerivedLimit {X : RingedSite.{u, v}} (Ksys : ℕᵒᵖ ⥤ ModuleDerived X)
    (K : ModuleDerived X) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang (ModuleDerived X)

-- Proof sketch: represent the inverse system by an object of the derived category of sequential
-- inverse systems, apply the site-theoretic description of `R lim` from Lemma `21.23.1`, and use
-- the commutative square relating `f_*` and the projection from `X × ℕ` to `X`. Equivalently, one
-- can apply `Rf_*` to the Milnor distinguished triangle defining the derived limit and use that
-- `Rf_*` is a right adjoint, hence preserves products.
/-- Lemma 21.23.3: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f : X ⟶ Y`, the derived direct image functor `Rf_*` commutes with derived limits of sequential
inverse systems. Concretely, if `K` is a chosen derived limit of a tower `(K_n)` in
`D(\mathcal O_X)`, then `Rf_* K` is a chosen derived limit of the pushed-forward tower
`(Rf_* K_n)` in `D(\mathcal O_Y)`. -/
theorem modulePushforwardDerived_isSequentialDerivedLimit_of_isSequentialDerivedLimit
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived X) {K : ModuleDerived X}
    (hK : IsSequentialDerivedLimit Ksys K) :
    IsSequentialDerivedLimit (Ksys ⋙ modulePushforwardDerived f)
      ((modulePushforwardDerived f).obj K) := sorry

end RingedSite.Hom

/-! ### Remark_21_23_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite `\Gamma(U,-)` is additive.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (SheafOfModules X.structureSheaf)] :
    @Functor.Additive
      (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)] :
    DerivedCategory (SheafOfModules X.structureSheaf) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

-- Proof sketch: apply the derived-functor preservation of homotopy limits from
-- `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit` to the sections
-- functor `\Gamma(U,-)`, and then apply the Milnor short exact sequence for the resulting inverse
-- system in `D(\operatorname{Ab})`.
/-- Remark 21.23.4: for a ringed site `X`, an object `U : X`, a sequential inverse system
`(K_n)` in `D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the
objectwise cohomology groups `H^m(U, K)` fit into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim_n H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim_n H^m(U, K_n) \to 0`.
This is the formal content of the displayed exact sequence `21.23.4.1` in the remark; the
surrounding discussion about sheafification versus inverse limit is recorded here only in the
docstring. -/
theorem ringedSiteDerivedLimit_objectwiseCohomologyShortExact
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules X.structureSheaf))
    (K : DerivedCategory (SheafOfModules X.structureSheaf))
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        cokernel
            (CategoryTheory.derivedLimitDifferenceMap
              ((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1))) ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K) ⟶
          limit
            ((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-! ### Lemma_21_23_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ hAb _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` objectwise cohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module
`K`. -/
abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- A sheaf of `\mathcal O_X`-modules viewed as a derived object concentrated in degree `0`. -/
abbrev ringedSiteSingleFunctorZero
    [Abelian (RingedSiteModuleCat X)] :
    RingedSiteModuleCat X ⥤ DerivedCategory (RingedSiteModuleCat X) :=
  DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the derived-category embedding in degree `0`. -/
abbrev ringedSiteModuleObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((ringedSiteSingleFunctorZero X).obj ℱ)

/-- The sequential inverse system in `D(\mathcal O_X)` obtained from a tower of sheaves by
placing every stage in degree `0`. -/
abbrev ringedSiteModuleTowerInDerived
    [Abelian (RingedSiteModuleCat X)]
    (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X) :
    ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X) :=
  Fsys ⋙ ringedSiteSingleFunctorZero X

/-- The canonical model for the `R^1 \!\varprojlim` term of the tower of section groups
`n ↦ \mathcal F_n(U)`. -/
abbrev ringedSiteSectionsR1LimitTerm
    (U : X)
    (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  cokernel (derivedLimitDifferenceMap (Fsys ⋙ ringedSiteSectionsOverObjectFunctor X U))

end

section

variable (X : RingedSite.{u, v})

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

variable (B : Set X)
variable (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X)
variable (K : DerivedCategory (RingedSiteModuleCat X))

-- Proof sketch: use Remark `21.23.4` objectwise on each `U ∈ B`. Since every stage `\mathcal F_n`
-- is concentrated in degree `0` and has no higher cohomology on `U`, the Milnor exact sequence
-- shows the higher objectwise cohomology of the chosen derived limit `K` vanishes on `B`. Then
-- Lemma `21.20.3` identifies the cohomology sheaf with the sheafification of this basiswise-zero
-- presheaf, so the higher cohomology sheaves of `K` vanish.
/-- Lemma 21.23.5 (1): if a subset `B` covers the ringed site `X`, if every stage `\mathcal F_n`
has vanishing higher cohomology on objects of `B`, and if the section towers
`n ↦ \mathcal F_n(U)` have vanishing `R^1 \!\varprojlim` for `U ∈ B`, then every nonzero
cohomology sheaf of a chosen derived limit `K = R\!\varprojlim_n \mathcal F_n` vanishes. This
is the higher-degree part of the statement `R\!\varprojlim_n \mathcal F_n = \varprojlim_n
\mathcal F_n`. -/
theorem derivedLimit_higherCohomologySheaf_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj K) := sorry

-- Proof sketch: apply the same objectwise Milnor exact sequence on each `U ∈ B`. The positive
-- degree terms vanish by hypothesis, and the `R^1 \!\varprojlim` term on sections vanishes by
-- assumption, so the degree-zero objectwise cohomology of `K` identifies with
-- `\varprojlim_n \mathcal F_n(U)` on the basis. Sheafifying with Lemma `21.20.3` identifies the
-- degree-zero cohomology sheaf of `K` with the ordinary inverse limit sheaf.
/-- Lemma 21.23.5 (2): under the same hypotheses, the degree-zero cohomology sheaf of a chosen
derived limit `K = R\!\varprojlim_n \mathcal F_n` is isomorphic to the ordinary inverse limit
sheaf `\varprojlim_n \mathcal F_n`. This is the degree-zero part of the statement
`R\!\varprojlim_n \mathcal F_n = \varprojlim_n \mathcal F_n`. -/
theorem derivedLimit_zeroCohomologySheaf_isomorphic_limit_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj K)
      (limit Fsys) := sorry

-- Proof sketch: combine the degree-zero identification from part `(2)` with the vanishing of the
-- higher cohomology sheaves from part `(1)`. Evaluating over a basis object `U ∈ B` recovers the
-- higher cohomology of the ordinary inverse limit sheaf and shows it vanishes.
/-- Lemma 21.23.5 (3): under the same hypotheses, the ordinary inverse limit sheaf
`\varprojlim_n \mathcal F_n` has vanishing higher cohomology on every basis object `U ∈ B`. -/
theorem limit_objectwiseCohomology_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    (U : X) (hU : U ∈ B) (p : ℤ) (hp : 0 < p) :
    IsZero (ringedSiteModuleObjectwiseCohomology X U p (limit Fsys)) := sorry

end

/-! ### Lemma_21_23_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ hAb _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`m` objectwise cohomology group `H^m(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The inverse system `n ↦ H^m(U, K_n)` attached to a sequential inverse system in
`D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedObjectwiseCohomologySystem
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m

/-- The canonical model for `R^1 \!\varprojlim_n H^m(U, K_n)` used by the Milnor short exact
sequence. -/
private abbrev ringedSiteDerivedObjectwiseR1LimitTerm
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    AddCommGrpCat.{max u v} :=
  cokernel
    (CategoryTheory.derivedLimitDifferenceMap
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m))

/-- The transition morphism `H^m(U, K_j) ⟶ H^m(U, K_i)` attached to an inequality `i ≤ j`. -/
private abbrev ringedSiteDerivedObjectwiseCohomologyTransition
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ)
    {i j : ℕ} (hij : i ≤ j) :
    (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op j) ⟶
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op i) :=
  (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).map ((homOfLE hij).op)

/-- The projection from `\varprojlim_n H^m(U, K_n)` to the `n`th stage. -/
private abbrev ringedSiteDerivedObjectwiseCohomologyLimitProjection
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) (n : ℕ) :
    limit (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m) ⟶
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op n) :=
  limit.π (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m) (op n)

/-- A Milnor comparison map over `U` for the tower `(K_n)` in degree `m`. This packages the
derived-limit hypothesis together with the short exact sequence used in the proof of the lemma. -/
private abbrev IsMilnorComparisonOver
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X))
    (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ)
    (π :
      ringedSiteDerivedObjectwiseCohomology X U m K ⟶
        limit (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m)) : Prop :=
  IsDerivedLimit Ksys K ∧
    ∃ (ι :
        ringedSiteDerivedObjectwiseR1LimitTerm X U Ksys (m - 1) ⟶
          ringedSiteDerivedObjectwiseCohomology X U m K)
      (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact

-- Proof sketch: use the sheafification description of objectwise cohomology from Lemma `21.20.3`
-- to refine to a covering in the chosen cofinal family on which the image of a section vanishes at
-- stage `nV`. For each member of that cover, the Milnor short exact sequence and the vanishing of
-- the `R^1 lim` term identify `H^m(-, K)` with the inverse limit `lim_n H^m(-, K_n)`, and the
-- eventual injectivity hypothesis forces the local section itself to vanish. Since the
-- corresponding cohomology sheaf is obtained by sheafification, the original section must vanish.
/-- Lemma 21.23.6: let `X` be a ringed site, let `(K_n)` be a sequential inverse system in
`D(\mathcal O_X)`, let `V : X`, and let `m : ℤ`. Assume there is an integer `nV` and a cofinal
family `CovV` of coverings of `V` such that for every cover `T ∈ CovV` and every member
`I : T.Arrow`, the Milnor term `R^1 \!\varprojlim_n H^{m-1}(I.Y, K_n)` vanishes and the
transition maps `H^m(I.Y, K_n) → H^m(I.Y, K_{nV})` are injective for all `n ≥ nV`. Then every
Milnor comparison map `H^m(V, K) → \varprojlim_n H^m(V, K_n)` associated to the derived limit
`K = R \!\varprojlim_n K_n` becomes injective after projection to stage `nV`; this composite
formalizes the map `H^m(R \!\varprojlim_n K_n)(V) → H^m(K_{nV})(V)`. -/
theorem milnorComparisonToEventualStage_mono_of_cofinal_coverSystem
    (X : RingedSite.{u, v}) (V : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X))
    (K : DerivedCategory (RingedSiteModuleCat X))
    (m : ℤ) (nV : ℕ)
    (CovV : X.siteTopology.Cover V → Prop)
    (hcofinal :
      ∀ S : X.siteTopology.Cover V,
        ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S))
    (hR1vanish :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow,
        IsZero (ringedSiteDerivedObjectwiseR1LimitTerm X I.Y Ksys (m - 1)))
    (hinj :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ n : ℕ, ∀ hn : nV ≤ n,
        Mono
          (ringedSiteDerivedObjectwiseCohomologyTransition X I.Y Ksys m hn))
    {π :
      ringedSiteDerivedObjectwiseCohomology X V m K ⟶
        limit (ringedSiteDerivedObjectwiseCohomologySystem X V Ksys m)}
    (hπ : IsMilnorComparisonOver X V Ksys K m π) :
    Mono
      (π ≫ ringedSiteDerivedObjectwiseCohomologyLimitProjection X V Ksys m nV) := sorry

/-! ### Lemma_21_23_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in derived
abelian groups. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a module sheaf on a ringed site,
computed by applying derived sections over `U` to `\mathcal F[0]`. -/
private abbrev ringedSiteModuleCohomologyOverObject
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj
      ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ))

/-- Witness data for the eventual local vanishing hypothesis on the cohomology sheaves of a
derived object over a fixed basis object `V`. -/
private structure BasiswiseEventualCohomologySheafVanishingData
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E : DerivedCategory (RingedSiteModuleCat X))
    (V : X) where
  /-- A degree bound for the local vanishing condition over `V`. -/
  pBound : ℤ → ℤ
  /-- A cofinal family of coverings of `V`. -/
  CovV : X.siteTopology.Cover V → Prop
  /-- The chosen family of coverings is cofinal in all coverings of `V`. -/
  cofinal :
    ∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)
  /-- On each covering in the cofinal family, sufficiently high cohomology of the cohomology
  sheaves of `E` vanishes on every member. -/
  vanishing :
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p m : ℤ,
      pBound m < p →
        IsZero
          (ringedSiteModuleCohomologyOverObject X I.Y p
            ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) (m - p)).obj E))

-- Proof sketch: for each `V ∈ B`, apply the stated vanishing bounds on the cover system `CovV`
-- to the cohomology sheaves `H^{m-p}(E)`, use the truncation triangles from Remark `13.12.4` to
-- obtain eventual isomorphisms on the towers `H^{m-1}(V_i, \tau_{\ge -n} E)` and
-- `H^m(V_i, \tau_{\ge -n} E)`, deduce eventual injectivity from Lemma `21.23.6`, and then apply
-- the comparison-independence criterion of Remark `13.34.5`.
/-- Lemma 21.23.7: let `(\mathcal C, \mathcal O)` be a ringed site, let
`E ∈ D(\mathcal O)`, and let `B` be a subset of objects of `\mathcal C`. Assume every object of
`\mathcal C` has a covering by members of `B`, and for each `V ∈ B` there are a bound
`pBound(V,-) : \mathbf Z \to \mathbf Z` and a cofinal system `Cov_V` of coverings of `V` such
that `H^p(V_i, H^{m-p}(E)) = 0` for every member `V_i` of every covering in `Cov_V` whenever
`p > pBound(V,m)`. Then any compatible map from `E` to a chosen derived limit of the truncation
tower `(\tau_{\ge -n} E)_n`, formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_basiswise_eventual_cohomologySheaf_vanishing
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E K : DerivedCategory (RingedSiteModuleCat X))
    (c : E ⟶ K)
    (hc : CategoryTheory.IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseEventualCohomologySheafVanishingData X E V) :
    IsIso c := sorry

/-! ### Lemma_21_23_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (Opposite.op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in derived
abelian groups. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a module sheaf on a ringed site,
computed by applying derived sections over `U` to `\mathcal F[0]`. -/
private abbrev ringedSiteModuleObjectwiseCohomology
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj
      ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ))

/-- Witness data for the negative-cohomology local vanishing hypothesis over a fixed basis object
`V`. -/
private structure BasiswiseNegativeCohomologySheafVanishingData
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E : DerivedCategory (RingedSiteModuleCat X))
    (V : X) where
  /-- A nonnegative cohomological bound for the local vanishing condition over `V`. -/
  dV : ℤ
  /-- The chosen bound is nonnegative. -/
  nonneg : 0 ≤ dV
  /-- A cofinal family of coverings of `V`. -/
  CovV : X.siteTopology.Cover V → Prop
  /-- The chosen family of coverings is cofinal in all coverings of `V`. -/
  cofinal :
    ∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)
  /-- On each covering in the cofinal family, the negative cohomology sheaves of `E` have no
  cohomology above the bound `dV` on any member of the covering. -/
  vanishing :
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p q : ℤ,
      dV < p → q < 0 →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X I.Y p
            ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj E))

-- Proof sketch: apply Lemma `21.23.7` with the bound function
-- `pBound(V, m) = d_V + max 0 m`. If `p > d_V + max 0 m`, then either `m < 0`, in which case
-- `m - p < 0`, or `m ≥ 0`, in which case `d_V < p`, hence the given vanishing hypothesis for the
-- negative cohomology sheaves of `E` yields the basiswise eventual vanishing required there.
/-- Lemma 21.23.8: let `(\mathcal C,\mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`, and
let `\mathcal B` be a subset of objects of `\mathcal C`. Assume every object has a covering by
members of `\mathcal B`, and for each `V ∈ \mathcal B` there exist an integer `d_V ≥ 0` and a
cofinal system `\mathrm{Cov}_V` of coverings of `V` such that
`H^p(V_i, H^q(E)) = 0` for every member `V_i` of every covering in `\mathrm{Cov}_V` whenever
`p > d_V` and `q < 0`. Then every compatible comparison map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E K : DerivedCategory (RingedSiteModuleCat X))
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseNegativeCohomologySheafVanishingData X E V) :
    IsIso c := sorry

/-! ### Lemma_21_23_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ hAb _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` objectwise cohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module
`K`. -/
abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- A sheaf of `\mathcal O_X`-modules viewed as a derived object concentrated in degree `0`. -/
abbrev ringedSiteSingleFunctorZero
    [Abelian (RingedSiteModuleCat X)] :
    RingedSiteModuleCat X ⥤ DerivedCategory (RingedSiteModuleCat X) :=
  DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the derived-category embedding in degree `0`. -/
abbrev ringedSiteModuleObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((ringedSiteSingleFunctorZero X).obj ℱ)

-- Proof sketch: this is the uniform-basis specialization of Lemma `21.23.7`. For each basis
-- object `V ∈ B`, use the constant bound family `pBound(V, m) := pBound m` and let `Cov_V` be
-- the coverings of `V` whose members all lie in `B`; the covering hypothesis makes this family
-- cofinal, so Lemma `21.23.7` applies to the cohomology sheaves `H^{m-p}(E)` and yields that any
-- compatible truncation-derived-limit comparison `c : E ⟶ K` is an isomorphism.
/-- Lemma 21.23.9: let `(\mathcal C, \mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`,
and assume there are a function `pBound : \mathbf Z \to \mathbf Z` and a subset `B` of objects of
`\mathcal C` such that every object admits a covering by members of `B` and
`H^p(V, H^{m-p}(E)) = 0` for every `V ∈ B` whenever `p > pBound(m)`. Then any compatible map
from `E` to a chosen derived limit of the truncation tower `(\tau_{\ge -n} E)_n`, i.e. any
formalization of the canonical map `E \to R\!\varprojlim_n \tau_{\ge -n} E` from
Remark `13.34.5`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing
    (E K : DerivedCategory ModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (pBound : ℤ → ℤ)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X V p
            ((DerivedCategory.homologyFunctor ModX (m - p)).obj E))) :
    IsIso c := sorry

end

/-! ### Lemma_21_23_10 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in derived
abelian groups. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a module sheaf on a ringed site,
computed by applying derived sections over `U` to `\mathcal F[0]`. -/
private abbrev ringedSiteModuleObjectwiseCohomology
    (U : X)
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj
      ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ))

-- Proof sketch: apply Lemma `21.23.8` with the constant bound `d_V = d` for every basis object
-- `V ∈ B`, and let `Cov_V` be the coverings of `V` all of whose members lie in `B`. The covering
-- hypothesis makes each `Cov_V` cofinal, and the stated vanishing assumption is exactly the
-- required hypothesis on the negative cohomology sheaves `H^q(E)`.
/-- Lemma 21.23.10: let `(\mathcal C, \mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`,
and assume there exist an integer `d ≥ 0` and a subset `B` of objects of `\mathcal C` such that
every object admits a covering by members of `B` and
`H^p(V, H^q(E)) = 0` for `p > d`, `q < 0`, and `V ∈ B`. Then any compatible comparison map
from `E` to a chosen derived limit of the truncation tower `(\tau_{\ge -n} E)_n`, i.e. any
formalization of the canonical map `E \to R\!\varprojlim_n \tau_{\ge -n} E` from
Remark `13.34.5`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (E K : DerivedCategory (SheafOfModules X.structureSheaf))
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (d : ℤ) (hd : 0 ≤ d)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p q : ℤ, d < p → q < 0 →
        IsZero
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X V).obj
              ((DerivedCategory.singleFunctor (SheafOfModules X.structureSheaf) (0 : ℤ)).obj
                ((DerivedCategory.homologyFunctor (SheafOfModules X.structureSheaf) q).obj
                  E))))) :
    IsIso c := sorry

end

/-! ### Lemma_21_23_11 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in derived
abelian groups. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X) :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`q` objectwise cohomology group `H^q(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X) (q : ℤ) (K : DerivedCategory ModX) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} q).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the embedding into `D(\mathcal O_X)` concentrated in degree `0`. -/
private abbrev ringedSiteModuleObjectwiseCohomology
    (U : X) (p : ℤ) (ℱ : ModX) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((DerivedCategory.singleFunctor ModX (0 : ℤ)).obj ℱ)

-- Proof sketch: apply the spectral sequence of Lemma `13.21.3` to the sections functor
-- `\Gamma(U,-)` and to the bounded-below truncations `\tau_{\ge -n} K`. The basiswise
-- higher-cohomology vanishing hypothesis forces the spectral sequence to degenerate on every
-- `U ∈ B`, so for each truncation one gets
-- `H^q(U, \tau_{\ge -n}K) ≅ H^0(U, H^q(\tau_{\ge -n}K))`. For `n` large relative to `q`, the
-- right-hand side stabilizes to `H^0(U, H^q(K))`. Combine this stabilization with the Milnor
-- short exact sequence for `R\Gamma(U,-)` and the truncation-limit comparison from Lemma
-- `21.23.10` to identify `H^q(U, K)` with `H^0(U, H^q(K))`.
/-- Lemma 21.23.11: let `(\mathcal C, \mathcal O)` be a ringed site, let `K` be an object of
`D(\mathcal O)`, and let `\mathcal B` be a subset of objects such that every object admits a
covering by members of `\mathcal B`. If for every `U ∈ \mathcal B` and all `p > 0`, `q ∈ \mathbf
Z` one has `H^p(U, H^q(K)) = 0`, then for every `U ∈ \mathcal B` and `q ∈ \mathbf Z` the
derived cohomology group `H^q(U, K)` is naturally identified with the degree-zero sections
`H^0(U, H^q(K))` of the `q`-th cohomology sheaf. -/
theorem ringedSiteDerivedObjectwiseCohomology_iso_zeroDegree_of_basiswise_cohomologySheafAcyclic
    (K : DerivedCategory ModX)
    (B : Set X)
    (hcover :
      ∀ W : X, ∃ S : X.siteTopology.Cover W, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ ⦃U : X⦄, U ∈ B → ∀ p q : ℤ, 0 < p →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X U p
            ((DerivedCategory.homologyFunctor ModX q).obj K)))
    ⦃U : X⦄ (hU : U ∈ B) (q : ℤ) :
    IsIsomorphic
      (ringedSiteDerivedObjectwiseCohomology X U q K)
      (ringedSiteModuleObjectwiseCohomology X U 0
        ((DerivedCategory.homologyFunctor ModX q).obj K)) := sorry

end
