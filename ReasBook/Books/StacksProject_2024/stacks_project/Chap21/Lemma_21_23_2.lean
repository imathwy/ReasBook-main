import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_5_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_7_core
import StacksProject_2024.stacks_project.Chap21.DerivedCategoryExact
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_6
import StacksProject_2024.stacks_project.Chap15.Remark_15_87_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom
open scoped RingedSiteCohomology
open scoped RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable (X : RingedSite.{u, v})
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

/-- Helper for Lemma 21.23.2: evaluate an additive presheaf on `X` at the fixed object `U`. This
keeps the later derived-owner comparisons in one spelling world. -/
private abbrev abelianPresheafEvaluation (U : X) :
    (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v} :=
  (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- Helper for Lemma 21.23.2: composing two exact additive functors on abelian categories and then
deriving is canonically the same as deriving each functor and composing the derived functors. -/
private noncomputable def mapDerivedCategoryCompIso
    {A : Type*} {B : Type*} {D : Type*}
    [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    (F : A ⥤ B) (G : B ⥤ D)
    [Functor.Additive F] [Functor.Additive G]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let QD : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let eFactors :
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory) ≅
        (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD := by
    -- Normalize the composite to the owner-side `mapDerivedCategoryFactors` comparison.
    simpa using
      (Functor.associator
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        QB
        G.mapDerivedCategory) ≪≫
      Functor.isoWhiskerLeft
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (show QB ⋙ G.mapDerivedCategory ≅
            G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD from
          G.mapDerivedCategoryFactors)
  letI :
      Localization.Lifting
        QA
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory)
        (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    Localization.Lifting.compRight
      QA
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB)
      F.mapDerivedCategory
      G.mapDerivedCategory
  exact
    Localization.liftNatIso
      QA
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory)
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
      ((F ⋙ G).mapDerivedCategory)
      eFactors

/-- Helper for Lemma 21.23.2: the public owner
`underlyingAbelianPresheafDerived X ⋙ abelianPresheafEvaluation X U` agrees with the internal
derived-sections owner `moduleSectionsAsAbelianDerived X U`. -/
private noncomputable def
    underlyingAbelianPresheafDerivedEvaluation_iso_moduleSectionsAsAbelianDerived
    (U : X) :
    (underlyingAbelianPresheafDerived X ⋙
      (abelianPresheafEvaluation X U).mapDerivedCategory) ≅
      moduleSectionsAsAbelianDerived X U := by
  let F := underlyingAbelianPresheafFunctor X
  let G := abelianPresheafEvaluation X U
  letI : F.Additive :=
    exactFunctor_le_additiveFunctor
      (ModuleCat X)
      (Xᵒᵖ ⥤ AddCommGrpCat.{max u v})
      F
      (underlyingAbelianPresheafFunctor_exact X)
  letI : PreservesFiniteLimits F :=
    (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact X) |>.1
  letI : PreservesFiniteColimits F :=
    (exactFunctor_iff F).mp (underlyingAbelianPresheafFunctor_exact X) |>.2
  let eExact :
      (underlyingAbelianPresheafDerived X ⋙ G.mapDerivedCategory) ≅
        (F ⋙ G).mapDerivedCategory := by
    -- First rewrite the public owner to the exact composite owner `F ⋙ G`.
    simpa [underlyingAbelianPresheafDerived, F, G] using
      (mapDerivedCategoryCompIso F G)
  let exactModel : ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
    (F ⋙ G).mapDerivedCategory
  letI :
      exactModel.IsRightDerivedFunctor
        (show
          moduleSectionsAsAbelianToDerived X U ⟶
            (DerivedCategory.Qh :
              HomotopyCategory (ModuleCat X) (ComplexShape.up ℤ) ⥤ ModuleDerived X) ⋙ exactModel
         from
          (F ⋙ G).mapDerivedCategoryFactorsh.inv)
        (HomotopyCategory.quasiIso (ModuleCat X) (ComplexShape.up ℤ)) := by
    -- Route correction: instead of forcing a final `simpa` on `H^m(U, K)`, make the exact model
    -- explicit and let right-derived uniqueness compare it to the chosen owner.
    simpa [exactModel, moduleSectionsAsAbelianToDerived, moduleSectionsAsAbelianFunctor,
      underlyingAbelianPresheafFunctor, underlyingAbelianSheafFunctor, F, G] using
      (Functor.isRightDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat X) (ComplexShape.up ℤ))
        exactModel
        (F ⋙ G).mapDerivedCategoryFactorsh)
  let eDerived :
      moduleSectionsAsAbelianDerived X U ≅ exactModel :=
    (moduleSectionsAsAbelianDerived X U).rightDerivedUnique
      exactModel
      (Functor.totalRightDerivedUnit
        (moduleSectionsAsAbelianToDerived X U)
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat X) (ComplexShape.up ℤ) ⥤ ModuleDerived X)
        (HomotopyCategory.quasiIso (ModuleCat X) (ComplexShape.up ℤ)))
      (show
        moduleSectionsAsAbelianToDerived X U ⟶
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat X) (ComplexShape.up ℤ) ⥤ ModuleDerived X) ⋙ exactModel
       from
        (F ⋙ G).mapDerivedCategoryFactorsh.inv)
      (HomotopyCategory.quasiIso (ModuleCat X) (ComplexShape.up ℤ))
  -- Compose the exact-model comparison with the uniqueness comparison to reach the chosen owner.
  exact eExact ≪≫ eDerived.symm

/-- Helper for Lemma 21.23.2: `H^q(U, K)` is the degree-`q` homology of the canonical additive
derived-sections owner `moduleSectionsAsAbelianDerived X U`. -/
private noncomputable def cohomologyOverObject_iso_moduleSectionsAsAbelianDerivedHomology
    (U : X) (K : ModuleDerived X) (q : ℤ) :
    H^q(U, K) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} q).obj
        ((moduleSectionsAsAbelianDerived X U).obj K) := by
  let G := abelianPresheafEvaluation X U
  let eEval :
      H^q(U, K) ≅
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} q).obj
          ((G.mapDerivedCategory).obj ((underlyingAbelianPresheafDerived X).obj K)) := by
    -- Move homology through the exact evaluation functor on abelian presheaves.
    simpa [RingedSite.Hom.cohomologyOverObject, RingedSite.Hom.objectwiseCohomologyPresheaf, G] using
      (CategoryTheory.exactFunctor_homology_iso_mapDerivedCategory
        G
        ((underlyingAbelianPresheafDerived X).obj K)
        q)
  let eOwner :
      ((G.mapDerivedCategory).obj ((underlyingAbelianPresheafDerived X).obj K)) ≅
        ((moduleSectionsAsAbelianDerived X U).obj K) :=
    (underlyingAbelianPresheafDerivedEvaluation_iso_moduleSectionsAsAbelianDerived
      (X := X) U).app K
  -- Then transport the target along the owner comparison built above.
  exact eEval ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} q).mapIso eOwner

/-- Helper for Lemma 21.23.2: the underived sections functor over `U`, viewed in abelian groups,
is canonically the composite of module-valued evaluation with the forgetful functor to
`AddCommGrpCat`. -/
private noncomputable def moduleSectionsAsAbelianFunctorIsoEvaluationForget
    (U : X) :
    moduleSectionsAsAbelianFunctor X U ≅
      SheafOfModules.evaluation X.structureSheaf (op U) ⋙
        forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v} := by
  -- Reuse the canonical comparison between sheaf-valued and presheaf-valued evaluation.
  simpa [moduleSectionsAsAbelianFunctor, underlyingAbelianSheafFunctor] using
    (Functor.isoWhiskerRight
      (SheafOfModules.toSheafCompSheafToPresheafIso X.structureSheaf)
      ((evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))

/-- Helper for Lemma 21.23.2: the abelian-group valued sections functor over `U` preserves
countable products because it is naturally isomorphic to evaluation followed by the forgetful
functor from modules to abelian groups. -/
private noncomputable instance moduleSectionsAsAbelianFunctor_preservesDiscreteLimits
    (U : X) :
    PreservesLimitsOfShape (Discrete ℕ) (moduleSectionsAsAbelianFunctor X U) :=
  Limits.preservesLimitsOfShape_of_natIso
    (moduleSectionsAsAbelianFunctorIsoEvaluationForget (X := X) U).symm

/-- The objectwise degree-`q` cohomology tower `n ↦ H^q(U, K_n)` obtained from a sequential
inverse system in `ModuleDerived X` by derived sections over `U`, viewed in `Ab`. -/
abbrev objectwiseCohomologyInverseSystem
    (U : X) (Ksys : SequentialInverseSystem (ModuleDerived X)) (q : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  Ksys ⋙ moduleSectionsAsAbelianDerived X U ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat q

end

end RingedSite.Hom

/- Domain-style sampling for Lemma 21.23.2:
- primary domain: derived sections over a fixed object of a ringed site and the Milnor short exact
  sequence for sequential derived limits, surfaced through the objectwise cohomology groups
  `H^m(U, K)`;
- sampled owner declarations:
  `RingedSite.Hom.moduleSectionsDerived`,
  `RingedSite.Hom.cohomologyOverObject`,
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction: the source-facing objectwise derived sections owner is the module-valued
  functor `RΓ[X](U)`, and the source-facing cohomology owner is `H^m(U, K)` from
  `cohomologyOverObject`; the additive derived sections functor
  `moduleSectionsAsAbelianDerived X U` is only the underlying-abelian bridge from Lemma
  `21.20.7`; the Milnor short exact sequence itself is already owned by
  `derivedLimit_cohomology_shortExact`, whose left term is the canonical `firstDerivedLimit`, not
  a raw cokernel wrapper;
- primitive data: a ringed site `X`, an object `U : X`, a sequential inverse system
  `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`, a chosen derived limit `K`, and a cohomological degree `m`;
- derived API: preservation of derived limits by the canonical objectwise derived sections owner
  `RΓ[X](U)`, and the resulting Milnor short exact sequences on the groups `H^m(U, K)`.

Source/core/bridge triage:
- `source-facing`: the three objectwise derived-sections statements below about `RΓ[X](U)`;
- `core/canonical`: `ModuleCat`, `ModuleDerived`, `RΓ[X](U)`, `cohomologyOverObject`,
  `moduleSectionsAsAbelianDerived`, and `derivedLimit_cohomology_shortExact`;
- `bridge/view`: passage from the module-valued owner `RΓ[X](U)` to the additive derived-sections
  bridge `moduleSectionsAsAbelianDerived X U`, and the resulting objectwise cohomology tower used
  to apply the ambient Milnor exact sequence in `D(AddCommGrpCat)`.
-/

section SectionsOverObject

variable (X : RingedSite.{u, v})
local notation "DModX" => ModuleDerived X
local notation "RΓMod[" U "]" => RΓ[X](U)
local notation "RΓAb[" U "]" => moduleSectionsAsAbelianDerived X U

variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

-- Proof sketch: specialize Lemma `19.13.6` to the canonical module-valued derived sections
-- functor `RΓ[X](U)`.
/-- Derived-limit preservation companion for Lemma 21.23.2: for a ringed site `X` and an object
`U : X`, the canonical derived sections
functor `RΓ[X](U)` sends a derived limit of a sequential inverse system in `ModuleDerived X`
to the derived limit of the stagewise derived sections over `U`. -/
@[stacks 0D6K]
theorem ringedSiteDerivedSectionsOverObject_preservesDerivedLimit
    (U : X)
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ RΓMod[U]) ((RΓMod[U]).obj K) := by
  -- Specialize the canonical derived-limit preservation theorem to objectwise sections over `U`.
  simpa
      [CategoryTheory.additiveFunctorTotalRightDerived, RingedSite.Hom.moduleSectionsDerived,
        RingedSite.Hom.moduleSectionsToDerived] using
    (CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit
      (SheafOfModules.evaluation X.structureSheaf (op U)) hK)

-- Proof sketch: transport
-- `ringedSiteDerivedSectionsOverObject_preservesDerivedLimit` across the canonical comparison from
-- Lemma `21.20.7 (2)` between `RΓ[X](U)` followed by derived forgetful functor and the owner
-- `moduleSectionsAsAbelianDerived X U`.
/-- Bridge companion to Lemma 21.23.2 (2): after forgetting the
`Γ(U, 𝒪_X)`-module structure, the canonical derived sections functor `RΓ[X](U)` still sends a
derived limit of a sequential inverse system in `ModuleDerived X` to the derived limit of the
stagewise derived sections over `U`, now viewed in `D(AddCommGrpCat)`. -/
theorem ringedSiteDerivedSectionsOverObject_underlyingAbelian_preservesDerivedLimit
    (U : X)
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ RΓAb[U]) ((RΓAb[U]).obj K) := by
  -- The same preservation statement holds after passing to the underlying abelian-group valued
  -- derived sections owner.
  simpa
      [CategoryTheory.additiveFunctorTotalRightDerived,
        RingedSite.Hom.moduleSectionsAsAbelianDerived,
        RingedSite.Hom.moduleSectionsAsAbelianToDerived] using
    (CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit
      (moduleSectionsAsAbelianFunctor X U) hK)

-- Proof sketch: apply the Milnor short exact sequence of Lemma `15.87.10` to the inverse system
-- obtained from `RΓ[X](U)` after forgetting the `Γ(U, 𝒪_X)`-module structure; the public middle
-- term is then surfaced through the Chapter 21 owner `H^m(U, K)`.
/-- Lemma 21.23.2 (3): for a ringed site `X`, an object `U : X`, a sequential inverse system
`Ksys` in `ModuleDerived X`, and a chosen derived limit `K` of `Ksys`, the cohomology groups over
`U` fit into the usual Milnor short exact sequence relating `H^m(U, K)` to the inverse system of
stagewise groups `H^m(U, K_n)`, formalized by
`objectwiseCohomologyInverseSystem X U Ksys m`. -/
@[stacks 0D6K]
theorem ringedSiteDerivedSectionsOverObject_cohomology_shortExact
    (U : X)
    (Ksys : SequentialInverseSystem DModX)
    (K : DModX)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        (objectwiseCohomologyInverseSystem X U Ksys (m - 1)).firstDerivedLimit ⟶
          H^m(U, K))
      (π :
        H^m(U, K) ⟶
          limit (objectwiseCohomologyInverseSystem X U Ksys m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let e :
      H^m(U, K) ≅
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
          ((RΓAb[U]).obj K) :=
    cohomologyOverObject_iso_moduleSectionsAsAbelianDerivedHomology
      (X := X) U K m
  rcases CategoryTheory.derivedLimit_cohomology_shortExact
      (Ksys ⋙ RΓAb[U])
      ((RΓAb[U]).obj K)
      (ringedSiteDerivedSectionsOverObject_underlyingAbelian_preservesDerivedLimit
        (X := X) U hK)
      m with
    ⟨ι₀, π₀, h₀, hShort₀⟩
  let hTransport : (ι₀ ≫ e.inv) ≫ (e.hom ≫ π₀) = 0 := by
    -- Transport the zero composite across the middle isomorphism only.
    simpa [Category.assoc] using h₀
  refine ⟨ι₀ ≫ e.inv, e.hom ≫ π₀, hTransport, ?_⟩
  let i :
      ShortComplex.mk ι₀ π₀ h₀ ≅
        ShortComplex.mk (ι₀ ≫ e.inv) (e.hom ≫ π₀) hTransport :=
    ShortComplex.isoMk
      (Iso.refl _)
      e.symm
      (Iso.refl _)
      (by simp)
      (by simp)
  -- The Milnor short exact sequence is already proved for the additive derived-sections owner, so
  -- it suffices to transport it through the middle-term isomorphism `e`.
  simpa [i] using ShortComplex.shortExact_of_iso i hShort₀

end SectionsOverObject
