import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_35_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  RingedSite.Hom.ModuleCat X

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- The standard chosen derived category `D(\mathcal O_X)` attached to `X`. -/
private abbrev StandardRingedSiteDerivedCat (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)] :=
  @DerivedCategory (RingedSiteModuleCat X) _ _
    (HasDerivedCategory.standard (RingedSiteModuleCat X))

/-- The standard chosen localized derived category `D(\mathcal O_U)` attached to `X` and `U`. -/
private abbrev StandardLocalizedRingedSiteDerivedCat (X : RingedSite.{u, v}) (U : X)
    [Abelian (LocalizedRingedSiteModuleCat X U)] :=
  @DerivedCategory (LocalizedRingedSiteModuleCat X U) _ _
    (HasDerivedCategory.standard (LocalizedRingedSiteModuleCat X U))

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (CategoryTheory.evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X) [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`m` objectwise cohomology group `H^m(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The underived global-sections functor `\Gamma(\mathcal C, -)` on `\mathcal O_X`-modules. -/
private abbrev ringedSiteGlobalSectionsFunctor :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

-- Proof sketch: the forgetful functor to abelian sheaves and the global-sections functor on
-- sheaves of abelian groups are additive, so their composite is additive.
/-- The global-sections functor on a ringed site is additive. -/
private theorem ringedSiteGlobalSectionsFunctor_isAdditive
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteGlobalSectionsFunctor X) := sorry

/-- The right derived global-sections functor `R\Gamma(\mathcal C, -)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedGlobalSectionsFunctor
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ AddCommGrpCat.instAbelian
    (ringedSiteGlobalSectionsFunctor X)
    (ringedSiteGlobalSectionsFunctor_isAdditive X) inferInstance

/-- The degree-`m` global cohomology group `H^m(\mathcal C, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedGlobalCohomology
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedGlobalSectionsFunctor X).obj K)

-- Proof sketch: choose a K-flat complex representing `L` and a K-injective complex representing
-- `M`. Lemma `21.34.8` shows that the internal-Hom complex representing
-- `R\mathcal H\!\mathit{om}(L, M)` is again K-injective, so `H^0(U, -)` is computed by ordinary
-- sections of that complex. Lemma `21.34.6` then identifies the resulting degree-zero cohomology
-- with morphisms in the localized derived category `D(\mathcal O_U)`.
/-- Lemma 21.35.1 (1): for every object `U` of a ringed site `(\mathcal C, \mathcal O)`, the
degree-zero cohomology of the derived internal Hom over `U` is identified with the morphism group
in the localized derived category. Formalized here, after choosing a derived restriction functor
to the localized site, a chosen comparison map
`H^0(U, R\mathcal H\!\mathit{om}(L, M)) →
  \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`
is bijective. -/
theorem derivedInternalHom_objectwiseH0_comparison_bijective
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [MonoidalCategory (DerivedCategory (RingedSiteModuleCat X))]
    [MonoidalClosed (DerivedCategory (RingedSiteModuleCat X))]
    (U : X)
    [Abelian (LocalizedRingedSiteModuleCat X U)]
    (restrictU :
      DerivedCategory (RingedSiteModuleCat X) ⥤
        DerivedCategory (LocalizedRingedSiteModuleCat X U))
    (L M : DerivedCategory (RingedSiteModuleCat X))
    (comparison :
      ringedSiteDerivedObjectwiseCohomology X U (0 : ℤ) ((ihom L).obj M) →
        ((restrictU.obj L) ⟶ (restrictU.obj M))) :
    Function.Bijective comparison := sorry

-- Proof sketch: choose a K-flat complex representing `L` and a K-injective complex representing
-- `M`. By Lemma `21.34.8`, their internal-Hom complex is K-injective and represents
-- `R\mathcal H\!\mathit{om}(L, M)`. Applying global sections and then Lemma `21.34.6` identifies
-- the degree-zero cohomology of that complex with the morphism group
-- `\operatorname{Hom}_{D(\mathcal O)}(L, M)`.
/-- Lemma 21.35.1 (2): the degree-zero global cohomology of the derived internal Hom on a ringed
site `(\mathcal C, \mathcal O)` is identified with the morphism group in `D(\mathcal O)`.
Formalized here, a chosen comparison map
`H^0(\mathcal C, R\mathcal H\!\mathit{om}(L, M)) →
  \operatorname{Hom}_{D(\mathcal O)}(L, M)`
is bijective. -/
theorem derivedInternalHom_globalH0_comparison_bijective
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [MonoidalCategory (DerivedCategory (RingedSiteModuleCat X))]
    [MonoidalClosed (DerivedCategory (RingedSiteModuleCat X))]
    (L M : DerivedCategory (RingedSiteModuleCat X))
    (comparison :
      ringedSiteDerivedGlobalCohomology X (0 : ℤ) ((ihom L).obj M) →
        (L ⟶ M)) :
    Function.Bijective comparison := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Tensoring on the left by `K ⊗ L` is naturally isomorphic to first tensoring on the left by
`K` and then by `L`, after reordering the tensor factors into the Stacks Project convention. -/
noncomputable abbrev ringedSiteDerivedTensorLeftTensorIso
    (K L : RingedSiteDerived J 𝒪) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((MonoidalCategory.tensoringLeft (RingedSiteDerived J 𝒪)).mapIso (β_ K L)) ≪≫
    MonoidalCategory.tensorLeftTensor L K

/-- The functorial currying isomorphism identifying iterated derived internal Hom with derived
internal Hom out of the derived tensor product on a ringed site. -/
noncomputable def ringedSiteDerivedInternalHomTensorNatIso
    (K L : RingedSiteDerived J 𝒪) :
    ihom L ⋙ ihom K ≅ ihom (K ⊗ L) :=
  (Adjunction.rightAdjointUniq
      (ihom.adjunction (K ⊗ L))
      (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
        (ringedSiteDerivedTensorLeftTensorIso K L).symm)).symm

/-- Lemma 21.35.2: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical isomorphism
`R\mathcal H\!\mathit{om}(K, R\mathcal H\!\mathit{om}(L, M)) \cong
R\mathcal H\!\mathit{om}(K \otimes_\mathcal O^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. Taking `H^0(\mathcal C, -)` recovers `21.35.0.1`. -/
noncomputable def ringedSiteDerivedInternalHomTensorIso
    (K L M : RingedSiteDerived J 𝒪) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  (ringedSiteDerivedInternalHomTensorNatIso K L).app M

-- Proof sketch: both sides are definitionally the component at `M` of the functorial natural
-- isomorphism `ringedSiteDerivedInternalHomTensorNatIso K L`.
/-- The textbook isomorphism is the component at `M` of the functorial currying isomorphism. -/
theorem ringedSiteDerivedInternalHomTensorIso_eq_app
    (K L M : RingedSiteDerived J 𝒪) :
    ringedSiteDerivedInternalHomTensorIso K L M =
      (ringedSiteDerivedInternalHomTensorNatIso K L).app M := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
private abbrev RingedSiteDerivedCat (X : RingedSite.{u, v}) :=
  DerivedCategory (RingedSiteModuleCat X)

/-- The localized derived category `D(\mathcal O_U)` of module sheaves on `X.localization U`. -/
private abbrev LocalizedRingedSiteDerivedCat (X : RingedSite.{u, v}) (U : X) :=
  DerivedCategory (LocalizedRingedSiteModuleCat X U)

-- Proof sketch: choose the standard derived internal-Hom constructions on `D(\mathcal O_X)` and
-- `D(\mathcal O_U)` by resolving the target with a K-injective complex. Lemma `21.20.1` says
-- restriction preserves K-injective complexes, so applying the same construction after
-- restriction produces the localized derived internal Hom. This yields the comparison
-- isomorphism.
/-- Lemma 21.35.3: for a ringed site `(\mathcal C, \mathcal O)` and an object
`U : \mathcal C`, for objects `K, L` of `D(\mathcal O)` and chosen derived internal-Hom
constructions on the ambient
and localized derived categories, the derived internal Hom of the restrictions `K|_U` and `L|_U`
is canonically isomorphic to the restriction of the derived internal Hom of `K` and `L`. -/
theorem localizedRestriction_derivedInternalHomConstruction_isomorphic
    (X : RingedSite.{u, v}) (U : X)
    [HasDerivedCategory (RingedSiteModuleCat X)]
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(RingedSite.Hom.localizedRestriction X U).Additive]
    [PreservesFiniteLimits (RingedSite.Hom.localizedRestriction X U)]
    [PreservesFiniteColimits (RingedSite.Hom.localizedRestriction X U)]
    (ambientDerivedInternalHom :
      (RingedSiteDerivedCat X)ᵒᵖ ⥤
        RingedSiteDerivedCat X ⥤
          RingedSiteDerivedCat X)
    (localizedDerivedInternalHom :
      (LocalizedRingedSiteDerivedCat X U)ᵒᵖ ⥤
        LocalizedRingedSiteDerivedCat X U ⥤
          LocalizedRingedSiteDerivedCat X U)
    (K L : RingedSiteDerivedCat X) :
    IsIsomorphic
      ((localizedDerivedInternalHom.obj (op ((RingedSite.Hom.localizedRestrictionDerived X U).obj K))).obj
        ((RingedSite.Hom.localizedRestrictionDerived X U).obj L))
      ((RingedSite.Hom.localizedRestrictionDerived X U).obj
        ((ambientDerivedInternalHom.obj (op K)).obj L)) := sorry

/-! ### Lemma_21_35_4 (from Chap21) -/
open CategoryTheory

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.35.4:
- primary domain: triangulated functors on derived categories, especially exactness transported
  across adjunctions and opposite categories;
- sampled owner declarations:
  `Adjunction.isTriangulated_rightAdjoint`,
  `Functor.isTriangulated_of_op`,
  `Functor.op_isTriangulated_iff`,
  `SheafOfModules.RingedSite.derivedTensorProduct_isTriangulated`;
- best owner abstraction: the mathematical owners here are the generic triangulated-functor
  theorems `Adjunction.isTriangulated_rightAdjoint` and `Functor.isTriangulated_of_op`; the
  ringed-site input only supplies the ambient derived category and the source-facing realization of
  `- ⊗^L K` as the exact left adjoint from Definition `21.17.13`;
- primitive vs derived: the primitive data are a shift-compatible adjunction and, respectively, an
  opposite functor known to be triangulated; the exactness of the right adjoint and of the
  contravariant original functor are derived API, so they should not be restated as parallel local
  owner theorems.

Source/core/bridge triage:
- `source-facing`: Lemma 21.35.4 asserts exactness of derived internal Hom in each variable on the
  derived category of sheaves of modules over a ringed site;
- `core/canonical`: `Adjunction.isTriangulated_rightAdjoint` and `Functor.isTriangulated_of_op`;
- `bridge/view`: the ringed-site reading in which `- ⊗^L K` is the exact left adjoint and
  `R\mathcal H\!\mathit{om}(K,-)` or `R\mathcal H\!\mathit{om}(-,L)` are its source-facing
  second- and first-variable specializations.
-/

/- Lemma 21.35.4 (1): in the ringed-site setting, exactness of a chosen
`R\mathcal H\!\mathit{om}(K,-)` follows from the canonical theorem that a shift-compatible right
adjoint of a triangulated functor is triangulated. -/
recall Adjunction.isTriangulated_rightAdjoint

end

end SheafOfModules.RingedSite

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]
variable [Limits.HasZeroObject D]
variable [Preadditive D]
variable [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated D]

/- Lemma 21.35.4 (2): exactness in the contravariant first variable is the opposite-category form
of exactness for a covariant triangulated functor, so the owner theorem is the canonical recall
`Functor.isTriangulated_of_op`. -/
recall Functor.isTriangulated_of_op

end

end CategoryTheory

/-! ### Lemma_21_35_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.5: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_\mathcal O^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)`. In the monoidal closed derived
category formalization used here, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the
canonical morphism is the currying of the composite obtained by first evaluating
`R\mathcal H\!\mathit{om}(K, L)` on `K` and then evaluating `R\mathcal H\!\mathit{om}(L, M)` on
the resulting object `L`. -/
noncomputable def ringedSiteDerivedTensorInternalHomToIteratedInternalHom
    (K L M : RingedSiteDerived J 𝒪) :
    ((ihom L).obj M ⊗ K) ⟶
      (ihom ((ihom K).obj L)).obj M :=
  let A := (ihom L).obj M
  let B := (ihom K).obj L
  MonoidalClosed.curry
    ((α_ B A K).inv ≫
      ((β_ B A).hom ⊗ₘ 𝟙 K) ≫
      (α_ A B K).hom ≫
      (𝟙 A ⊗ₘ (β_ B K).hom) ≫
      (𝟙 A ⊗ₘ (ihom.ev K).app L) ≫
      (β_ A L).hom ≫
      (ihom.ev L).app M)

-- Proof sketch: this is the defining `curry`/`uncurry` adjunction in the closed monoidal
-- category `D(\mathcal O)`. Uncurrying the displayed morphism returns the composite of the
-- braiding and the two evaluation maps that was curried in the definition.
/-- Uncurrying the canonical derived tensor-to-iterated-internal-Hom morphism recovers the
evaluation composite used to define it. -/
theorem ringedSiteDerivedTensorInternalHomToIteratedInternalHom_uncurry
    (K L M : RingedSiteDerived J 𝒪) :
    MonoidalClosed.uncurry
      (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
      (α_ ((ihom K).obj L) ((ihom L).obj M) K).inv ≫
        ((β_ ((ihom K).obj L) ((ihom L).obj M)).hom ⊗ₘ 𝟙 K) ≫
        (α_ ((ihom L).obj M) ((ihom K).obj L) K).hom ≫
        (𝟙 ((ihom L).obj M) ⊗ₘ (β_ ((ihom K).obj L) K).hom) ≫
        (𝟙 ((ihom L).obj M) ⊗ₘ (ihom.ev K).app L) ≫
        (β_ ((ihom L).obj M) L).hom ≫
        (ihom.ev L).app M := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the given ringed site. -/
private abbrev RingedSiteModules (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
private abbrev RingedSiteDerived (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.6: for objects `K`, `L`, and `M` of `D(\mathcal O)` on a ringed site, there is a
canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_\mathcal O^{\mathbf L}
  R\mathcal H\!\mathit{om}(K, L) \to R\mathcal H\!\mathit{om}(K, M)`.
In Lean, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the map is obtained by
braiding the two internal-Hom factors into the order required by the closed-monoidal composition
map. -/
noncomputable def ringedSiteDerivedInternalHomComposition
    (K L M : RingedSiteDerived J 𝒪) :
    ((ihom L).obj M ⊗ (ihom K).obj L) ⟶ (ihom K).obj M :=
  (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫
    MonoidalClosed.comp K L M

-- Proof sketch: unfold the definition; the morphism is exactly the braiding
-- `R\mathcal H\!\mathit{om}(L,M) ⊗ R\mathcal H\!\mathit{om}(K,L)
--   ⟶ R\mathcal H\!\mathit{om}(K,L) ⊗ R\mathcal H\!\mathit{om}(L,M)`
-- followed by the canonical closed-monoidal composition map
-- `[K,L] ⊗ [L,M] ⟶ [K,M]`.
/-- The canonical derived internal-Hom composition morphism is the braiding followed by the
closed-monoidal composition map. -/
theorem ringedSiteDerivedInternalHomComposition_def
    (K L M : RingedSiteDerived J 𝒪) :
    ringedSiteDerivedInternalHomComposition K L M =
      (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫
        MonoidalClosed.comp K L M := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the given ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.7: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical morphism
`K \otimes_\mathcal O^{\mathbf L} R\mathcal H\!\mathit{om}(M, L) \to
R\mathcal H\!\mathit{om}(M, K \otimes_\mathcal O^{\mathbf L} L)`.
In the closed monoidal formalization of `D(\mathcal O)`, `R\mathcal H\!\mathit{om}(A, B)` is
`(ihom A).obj B`, and this morphism is the adjoint transpose of the map obtained by braiding `M`
past `K` and then evaluating `R\mathcal H\!\mathit{om}(M, L)`. -/
noncomputable def ringedSiteDerivedTensorInternalHomComparison
    (K L M : RingedSiteDerived J 𝒪) :
    (K ⊗ (ihom M).obj L) ⟶ (ihom M).obj (K ⊗ L) :=
  MonoidalClosed.curry
    ((α_ M K ((ihom M).obj L)).inv ≫
      ((β_ M K).hom ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
      (α_ K M ((ihom M).obj L)).hom ≫
      (𝟙 K ⊗ₘ (ihom.ev M).app L))

-- Proof sketch: this is immediate from the definition and the `curry`/`uncurry` adjunction in
-- the closed monoidal category `D(\mathcal O)`.
/-- Uncurrying the tensor-internal-Hom comparison recovers the braiding-evaluation composite used
to define it. -/
theorem ringedSiteDerivedTensorInternalHomComparison_uncurry
    (K L M : RingedSiteDerived J 𝒪) :
    MonoidalClosed.uncurry (ringedSiteDerivedTensorInternalHomComparison K L M) =
      (α_ M K ((ihom M).obj L)).inv ≫
        ((β_ M K).hom ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
        (α_ K M ((ihom M).obj L)).hom ≫
        (𝟙 K ⊗ₘ (ihom.ev M).app L) := sorry

-- Proof sketch: apply naturality of the braiding, associator, `MonoidalClosed.pre`, and
-- `ihom.map` to the defining uncurried composite, then use the injectivity of `curry`.
/-- The tensor-internal-Hom comparison is functorial in `K` and `L`, and contravariantly
functorial in `M`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : RingedSiteDerived J 𝒪}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    (fK ⊗ₘ ((MonoidalClosed.pre fM).app L₁ ≫ (ihom M₁).map fL)) ≫
        ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁ =
      ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
        (MonoidalClosed.pre fM).app (K₁ ⊗ L₁) ≫
        (ihom M₁).map (fK ⊗ₘ fL) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.8: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L` of
`D(\mathcal O)`, the canonical coevaluation morphism
`K \to R\mathcal H\!\mathit{om}(L, K \otimes_\mathcal O^{\mathbf L} L)`. In the closed monoidal
formalization of `D(\mathcal O)`, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the
canonical morphism is the adjoint transpose of the braiding
`L \otimes K \to K \otimes L`. -/
noncomputable def ringedSiteDerivedTensorInternalHomUnit
    (K L : RingedSiteDerived J 𝒪) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  MonoidalClosed.curry ((β_ L K).hom)

-- Proof sketch: uncurry both sides. Naturality in `K` reduces to naturality of the braiding in
-- the second variable, followed by the naturality of `curry` with respect to postcomposition on
-- the target of `R\mathcal H\!\mathit{om}(L, -)`.
/-- The canonical derived tensor-Hom unit is functorial in the left variable `K`. -/
theorem ringedSiteDerivedTensorInternalHomUnit_naturalLeft
    {K₁ K₂ L : RingedSiteDerived J 𝒪} (α : K₁ ⟶ K₂) :
    α ≫ ringedSiteDerivedTensorInternalHomUnit K₂ L =
      ringedSiteDerivedTensorInternalHomUnit K₁ L ≫
        (ihom L).map (α ⊗ₘ 𝟙 L) := sorry

-- Proof sketch: uncurry both sides. Naturality in `L` is the compatibility of the braiding with
-- a morphism `β : L₁ ⟶ L₂`, rewritten through the contravariant action `MonoidalClosed.pre β`
-- on the first internal-Hom argument and the induced map on the tensor target.
/-- The canonical derived tensor-Hom unit is functorial in the right variable `L`. -/
theorem ringedSiteDerivedTensorInternalHomUnit_naturalRight
    (K : RingedSiteDerived J 𝒪) {L₁ L₂ : RingedSiteDerived J 𝒪} (β : L₁ ⟶ L₂) :
    ringedSiteDerivedTensorInternalHomUnit K L₂ ≫
        (MonoidalClosed.pre β).app (K ⊗ L₂) =
      ringedSiteDerivedTensorInternalHomUnit K L₁ ≫
        (ihom L₁).map (𝟙 K ⊗ₘ β) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_35_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

-- Proof sketch: both postcomposition with `ringedSiteDerivedEvaluationHom L M` and the
-- closed-monoidal uncurrying map are additive on morphisms, and precomposition with the fixed
-- right-unitor inverse `(ρ_ L).inv` preserves addition.
/- The map induced on degree-zero global sections by the evaluation morphism is additive. -/
private theorem ringedSiteDerivedEvaluationH0ToHom_add
    (L M : D) (s t : 𝟙_ D ⟶ M ⊗ L^∨) :
    (ρ_ L).inv ≫
        uncurry
          ((s + t) ≫ ringedSiteDerivedEvaluationHom L M) =
      ((ρ_ L).inv ≫
          uncurry
            (s ≫ ringedSiteDerivedEvaluationHom L M)) +
        ((ρ_ L).inv ≫
          uncurry
            (t ≫ ringedSiteDerivedEvaluationHom L M)) := sorry

/-- Lemma 21.35.9: the canonical morphism
`M \otimes_\mathcal O^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)`
induces a canonical map
`H^0(\mathcal C, M \otimes_\mathcal O^{\mathbf L} L^\vee) \to
\operatorname{Hom}_{D(\mathcal O)}(L, M)`,
formalized here as the additive map from morphisms
`\mathcal O \to M \otimes_\mathcal O^{\mathbf L} L^\vee` out of the monoidal unit of
`D(\mathcal O)` to morphisms `L ⟶ M`. -/
noncomputable def ringedSiteDerivedEvaluationH0ToHom
    (L M : D) :
    AddMonoidHom (𝟙_ D ⟶ M ⊗ L^∨) (L ⟶ M) :=
  AddMonoidHom.mk'
    (fun s ↦
      (ρ_ L).inv ≫
        uncurry
          (s ≫ ringedSiteDerivedEvaluationHom L M))
    (ringedSiteDerivedEvaluationH0ToHom_add L M)

-- Proof sketch: on the source, functoriality in `M` is postcomposition with
-- `f ⊗ 𝟙_{L^\vee}`. Expand the definition and use functoriality of
-- `MonoidalClosed.uncurry` and the right unitor.
/-- The induced map on degree-zero global sections is functorial in the variable `M`. -/
theorem ringedSiteDerivedEvaluationH0ToHom_natural
    {L M₁ M₂ : D} (f : M₁ ⟶ M₂)
    (s : 𝟙_ D ⟶ M₁ ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M₂
        (s ≫ (f ⊗ₘ 𝟙 (L^∨))) =
      ringedSiteDerivedEvaluationH0ToHom L M₁ s ≫ f := sorry

end

end SheafOfModules.RingedSite

/-! ### Remark_21_35_10 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
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

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory (ModuleCat X))
    (ModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ DerivedCategory (ModuleCat Y))
    (ModuleQis Y)

/-- The morphism adjoint to the relative cup-product map, obtained from the pullback-tensor
comparison together with the counit `Lf^* Rf_* ⟶ \mathrm{id}` on each tensor factor. -/
noncomputable def relativeCupProductAdjointMap
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] [f.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (pullbackTensorComparison :
      ∀ (K L : ModuleDerived Y),
        ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
          ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
            ((modulePullbackDerived f).obj K)))
    (K L : ModuleDerived X) :
    ((modulePullbackDerived f).obj
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      ((tensorSource.obj L).obj K) :=
  (pullbackTensorComparison
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)).hom ≫
    ((tensorSource.map (adj.counit.app L)).app
      ((modulePullbackDerived f).obj ((modulePushforwardDerived f).obj K))) ≫
    ((tensorSource.obj L).map (adj.counit.app K))

/-- The relative cup-product morphism
`Rf_* K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* L ⟶ Rf_*(K \otimes_{\mathcal O_X}^{\mathbf L} L)`.
-/
noncomputable def relativeCupProductMap
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] [f.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (pullbackTensorComparison :
      ∀ (K L : ModuleDerived Y),
        ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
          ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
            ((modulePullbackDerived f).obj K)))
    (K L : ModuleDerived X) :
    ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
      ((modulePushforwardDerived f).obj K)) ⟶
      (modulePushforwardDerived f).obj ((tensorSource.obj L).obj K) :=
  (adj.homEquiv
      ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
        ((modulePushforwardDerived f).obj K))
      ((tensorSource.obj L).obj K))
    (relativeCupProductAdjointMap
      f tensorSource tensorTarget adj pullbackTensorComparison K L)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [BraidedCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (A B : ModuleDerived Y),
      ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj B).obj A)) ≅
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj B)).obj
          ((modulePullbackDerived f).obj A)))

/-- The canonical evaluation morphism
`R\mathcal H\!\mathit{om}(L, K) \otimes_\mathcal O^{\mathbf L} L \to K` in the derived category
of module sheaves on `X`, expressed via the internal-Hom adjunction. -/
private noncomputable abbrev moduleDerivedInternalHomEvaluationMap
    (L K : ModuleDerived X) :
    ((ihom L).obj K ⊗ L) ⟶ K :=
  ((((ihom.adjunction L).homEquiv ((ihom L).obj K) K).symm.trans
      ((β_ ((ihom L).obj K) L).symm.homCongr (Iso.refl K))) :
    (((ihom L).obj K ⟶ (ihom L).obj K) ≃ ((ihom L).obj K ⊗ L ⟶ K)))
    (𝟙 ((ihom L).obj K))

/-- Remark 21.35.10: for a morphism of ringed topoi formalized by the ringed-site morphism `f`
and objects `L`, `K` of `D(\mathcal O_\mathcal C)`, there is a canonical morphism
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to
  R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)`. It is the adjoint transpose of the composite
obtained by first applying the relative cup product to
`Rf_* R\mathcal H\!\mathit{om}(L, K) \otimes_{\mathcal O_\mathcal D}^{\mathbf L} Rf_* L` and
then applying `Rf_*` to the source-side evaluation map
`R\mathcal H\!\mathit{om}(L, K) \otimes_{\mathcal O_\mathcal C}^{\mathbf L} L \to K`. -/
noncomputable def derivedPushforwardInternalHomComparison
    (L K : ModuleDerived X) :
    (modulePushforwardDerived f).obj ((ihom L).obj K) ⟶
      (ihom ((modulePushforwardDerived f).obj L)).obj ((modulePushforwardDerived f).obj K) :=
  (((((ihom.adjunction ((modulePushforwardDerived f).obj L)).homEquiv
        ((modulePushforwardDerived f).obj ((ihom L).obj K))
        ((modulePushforwardDerived f).obj K)).symm.trans
          ((β_ ((modulePushforwardDerived f).obj ((ihom L).obj K))
              ((modulePushforwardDerived f).obj L)).symm.homCongr
            (Iso.refl ((modulePushforwardDerived f).obj K))))).symm)
    (relativeCupProductMap
        f (curriedTensor (ModuleDerived X)) (curriedTensor (ModuleDerived Y))
        adj pullbackTensorComparison L ((ihom L).obj K) ≫
      (modulePushforwardDerived f).map (moduleDerivedInternalHomEvaluationMap L K))

-- Proof sketch: apply the target-side internal-Hom adjunction `21.35.0.1`. By construction,
-- `derivedPushforwardInternalHomComparison` is defined as the inverse adjoint transpose of the
-- composite consisting of the relative cup product of Remark `21.19.7` followed by `Rf_*`
-- applied to the source-side evaluation map.
/-- The canonical map
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)` is adjoint to
the composite
`Rf_* R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} Rf_* L \to
  Rf_*(R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} L) \to Rf_* K`
described in Remark `21.35.10`. -/
theorem derivedPushforwardInternalHomComparison_spec
    (L K : ModuleDerived X) :
    ((((ihom.adjunction ((modulePushforwardDerived f).obj L)).homEquiv
          ((modulePushforwardDerived f).obj ((ihom L).obj K))
          ((modulePushforwardDerived f).obj K)).symm.trans
        ((β_ ((modulePushforwardDerived f).obj ((ihom L).obj K))
            ((modulePushforwardDerived f).obj L)).symm.homCongr
          (Iso.refl ((modulePushforwardDerived f).obj K))))
      (derivedPushforwardInternalHomComparison f adj pullbackTensorComparison L K)) =
      relativeCupProductMap
          f (curriedTensor (ModuleDerived X)) (curriedTensor (ModuleDerived Y))
          adj pullbackTensorComparison L ((ihom L).obj K) ≫
        (modulePushforwardDerived f).map (moduleDerivedInternalHomEvaluationMap L K) :=
  sorry

end

end RingedSite.Hom

/-! ### Remark_21_35_11 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes_\mathcal O^{\mathbf L} K \to L`
in `D(\mathcal O)`. -/
private abbrev ringedSiteDerivedInternalHomEvaluation
    (K L : RingedSiteDerived J 𝒪) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ((((ihom.adjunction K).homEquiv ((ihom K).obj L) L).symm.trans
      ((β_ ((ihom K).obj L) K).symm.homCongr (Iso.refl L))) :
    (((ihom K).obj L ⟶ (ihom K).obj L) ≃ ((ihom K).obj L ⊗ K ⟶ L)))
    (𝟙 ((ihom K).obj L))

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
variable [J'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪' : Sheaf J' CommRingCat.{max u v}}
variable [Abelian (RingedSiteModules J' 𝒪')]
variable (leftDerivedPullback : RingedSiteDerived J' 𝒪' ⥤ RingedSiteDerived J 𝒪)
variable [MonoidalCategory (RingedSiteDerived J' 𝒪')]
variable [BraidedCategory (RingedSiteDerived J' 𝒪')]
variable [MonoidalClosed (RingedSiteDerived J' 𝒪')]

/-- Remark 21.35.11: for a morphism of ringed topoi, represented here by a chosen derived
pullback functor `Lh^* : D(\mathcal O') ⥤ D(\mathcal O)`, the pullback-tensor comparison of
Lemma `21.18.4` and the tensor-internal-Hom adjunction `21.35.0.1` induce the canonical morphism
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)` in `D(\mathcal O)`. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : RingedSiteDerived J' 𝒪'),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : RingedSiteDerived J' 𝒪') :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (((((ihom.adjunction (leftDerivedPullback.obj K)).homEquiv
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj L)).symm.trans
          ((β_ (leftDerivedPullback.obj ((ihom K).obj L))
              (leftDerivedPullback.obj K)).symm.homCongr
            (Iso.refl (leftDerivedPullback.obj L))))).symm)
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSiteDerivedInternalHomEvaluation K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison
-- `Lh^*(R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K) ≅
--   Lh^*R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} Lh^*K`.
/-- Applying the target-side tensor-internal-Hom adjunction to
`pullbackDerivedInternalHomComparison` recovers the pulled-back evaluation morphism after
transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : RingedSiteDerived J' 𝒪'),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : RingedSiteDerived J' 𝒪') :
    ((((ihom.adjunction (leftDerivedPullback.obj K)).homEquiv
          (leftDerivedPullback.obj ((ihom K).obj L))
          (leftDerivedPullback.obj L)).symm.trans
        ((β_ (leftDerivedPullback.obj ((ihom K).obj L))
            (leftDerivedPullback.obj K)).symm.homCongr
          (Iso.refl (leftDerivedPullback.obj L))))
      (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L)) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSiteDerivedInternalHomEvaluation K L) := sorry

end

end SheafOfModules.RingedSite

/-! ### Remark_21_35_12 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable (DC : Type u) [Category.{v} DC]
variable (DC' : Type u) [Category.{v} DC']
variable (DD : Type u) [Category.{v} DD]
variable (DD' : Type u) [Category.{v} DD']

variable [MonoidalCategory DC]
variable [BraidedCategory DC]
variable [MonoidalClosed DC]
variable [MonoidalCategory DC']
variable [BraidedCategory DC']
variable [MonoidalClosed DC']

variable (leftDerivedPullback_h : DC ⥤ DC')
variable (leftDerivedPullback_g : DD ⥤ DD')
variable (leftDerivedPullback_f : DD ⥤ DC)
variable (leftDerivedPullback_f' : DD' ⥤ DC')
variable (rightDerivedPushforward_f : DC ⥤ DD)
variable (rightDerivedPushforward_f' : DC' ⥤ DD')

/-- Remark 21.35.12: for a commutative square of ringed topoi, encoded here by the four derived
categories `D(\mathcal O_\mathcal C)`, `D(\mathcal O_{\mathcal C'})`, `D(\mathcal O_\mathcal D)`,
`D(\mathcal O_{\mathcal D'})`, chosen derived pullbacks `Lh^*`, `Lg^*`, `Lf^*`, `L(f')^*`,
chosen derived pushforwards `Rf_*`, `R(f')_*`, the pullback comparison
`Lh^* R\mathcal H\!\mathit{om}(K,L) \to R\mathcal H\!\mathit{om}(Lh^*K,Lh^*L)` from
Remark `21.35.11`, and a commutativity isomorphism `L(f')^* ∘ Lg^* ≅ Lh^* ∘ Lf^*`, there is a
canonical base-change morphism
`Lg^* Rf_* R\mathcal H\!\mathit{om}(K, L) ⟶
R(f')_* R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def derivedPushforwardInternalHomBaseChangeMap
    (internalHomPullbackComparison_h :
      ∀ (K L : DC),
        leftDerivedPullback_h.obj ((ihom K).obj L) ⟶
          (ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)) ⟶
      rightDerivedPushforward_f'.obj
        ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L)) :=
  (adj_f'.homEquiv
      (leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)))
      ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L)))
    ((hpull.app (rightDerivedPushforward_f.obj ((ihom K).obj L))).hom ≫
      leftDerivedPullback_h.map (adj_f.counit.app ((ihom K).obj L)) ≫
      internalHomPullbackComparison_h K L)

-- Proof sketch: by definition, transpose across the adjunction `L(f')^* ⊣ R(f')_*` the
-- composite obtained from the pullback commutativity isomorphism
-- `L(f')^* Lg^* ≅ Lh^* Lf^*`, then the counit `Lf^* Rf_* → id`, and finally the internal-Hom
-- pullback comparison from Remark `21.35.11`.
/-- Applying the adjunction `L(f')^* ⊣ R(f')_*` to
`derivedPushforwardInternalHomBaseChangeMap` recovers the composite used to define it. -/
theorem derivedPushforwardInternalHomBaseChangeMap_spec
    (internalHomPullbackComparison_h :
      ∀ (K L : DC),
        leftDerivedPullback_h.obj ((ihom K).obj L) ⟶
          (ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    (adj_f'.homEquiv
        (leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)))
        ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
        ).symm
        (derivedPushforwardInternalHomBaseChangeMap
          DC DC' DD DD'
          leftDerivedPullback_h leftDerivedPullback_g
          leftDerivedPullback_f leftDerivedPullback_f'
          rightDerivedPushforward_f rightDerivedPushforward_f'
          internalHomPullbackComparison_h hpull adj_f adj_f' K L) =
      (hpull.app (rightDerivedPushforward_f.obj ((ihom K).obj L))).hom ≫
        leftDerivedPullback_h.map (adj_f.counit.app ((ihom K).obj L)) ≫
        internalHomPullbackComparison_h K L := sorry

end

end SheafOfModules.RingedSite
