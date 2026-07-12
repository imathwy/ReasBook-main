import StacksProject_2024.Chap13.Definition_13_6_7
import StacksProject_2024.Chap21.Lemma_21_20_1
import StacksProject_2024.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex.HomComplex.CohomologyClass
open CategoryTheory.DerivedCategory
open DerivedCategory HomotopyCategory
open RingedSite.Hom
open scoped RingedSiteDerived

noncomputable section

universe u

namespace SheafOfModules.RingedSite

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X

local instance : HasDerivedCategory ModX := HasDerivedCategory.standard ModX
local instance (U : C) :
    HasDerivedCategory (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :=
  HasDerivedCategory.standard (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))
local instance : Category DModX := inferInstance
local instance : Preadditive DModX := inferInstance
local instance (A B : DModX) : Add (A ⟶ B) := inferInstance

/- Domain-style sampling for Lemma 21.34.6:
- primary domain: degree-zero cohomology of internal-Hom complexes of module sheaves on a ringed
  site and on its localizations, together with the corresponding morphism groups in derived
  categories;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringedSiteLocalizedRestriction_isKInjective`,
  `RingedSite.Hom.localizedRestriction`,
  `RingedSite.Hom.localizedRestrictionComplex`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `DerivedCategory.quotientCompQhIso`,
  `Functor.mapDerivedCategoryFactors`;
- best owner abstraction: the core owner is the generic K-injective comparison
  `H^0(Hom^⋅(L, I)) ≃ Hom_D(L, I)` in the ambient module category; localization is the
  source-facing specialization obtained by applying the Chapter 21 owners
  `ringedSiteLocalizedRestriction_isKInjective` and
  `RingedSite.Hom.localizedRestrictionDerived X U`, exposed propositionally because the localized
  K-injectivity input is still proof debt;
- primitive data: the commutative ringed site data `(C, J, 𝒪)`, the bundled owner
  `X := RingedSite.ofCommRingSheaf J 𝒪`, the object `U : X`, and the complexes `L` and `I`;
- derived API: the canonical additive equivalences from degree-zero Hom-complex cohomology to
  morphisms in `D(𝒪)`, together with the theorem-level `IsIsomorphic` comparison for the
  localized statement, the K-injective hom-bijection
  and the bridge `mapDerivedCategoryFactors` from restricted representatives to the owner
  `localizedRestrictionDerived X U`.

Source/core/bridge triage:
- `source-facing`: the localized and global comparisons
  `H^0(Γ(U, ℋom^⋅(𝓛, 𝓘))) ≅ Hom_{D(𝒪_U)}(L|_U, I|_U)` and
  `H^0(Γ(𝒞, ℋom^⋅(𝓛, 𝓘))) ≃ Hom_{D(𝒪)}(L, I)`;
- `core/canonical`: `ringedSiteModuleCategory`, `ringedSiteLocalizedRestriction_isKInjective`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `CochainComplex.HomComplex.homologyAddEquiv`, `homAddEquiv`,
  `CochainComplex.IsKInjective.Qh_map_bijective`, `DerivedCategory.quotientCompQhIso`, and
  `Functor.mapDerivedCategoryFactors`;
- `bridge/view`: the private generic K-injective comparison below and the internal bridge from
  `DerivedCategory.Q.obj (((localizedRestriction X U).mapHomologicalComplex (up ℤ)).obj K)` to
  `(localizedRestrictionDerived X U).obj (DerivedCategory.Q.obj K)`.
-/

private lemma iso_homCongr_map_add
    {C : Type*} [Category C] [Preadditive C] {A B A' B' : C} (α : A ≅ A') (β : B ≅ B')
    (f g : A ⟶ B) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {A B A' B' : C} (α : A ≅ A') (β : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := α.homCongr β
  map_add' := iso_homCongr_map_add α β

private noncomputable def kInjectiveHomComplex_homology_zero_addEquiv_derivedHom
    {A : Type*} [Category A] [Abelian A] [CategoryWithHomology A]
    (L I : CochainComplex A ℤ) [I.IsKInjective] :
    (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
      ((DerivedCategory.Q.obj L : DerivedCategory A) ⟶
        (DerivedCategory.Q.obj I : DerivedCategory A)) :=
  let KQ := HomotopyCategory.quotient A (up ℤ)
  let KL := KQ.obj L
  let I0Iso : KQ.obj (I⟦(0 : ℤ)⟧) ≅ KQ.obj I :=
    KQ.mapIso ((shiftFunctorZero (CochainComplex A ℤ) ℤ).app I)
  let e₀ :
      (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
        (KL ⟶ KQ.obj (I⟦(0 : ℤ)⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv L I (0 : ℤ)).trans homAddEquiv
  let e₁ : (KL ⟶ KQ.obj (I⟦(0 : ℤ)⟧)) ≃+ (KL ⟶ KQ.obj I) :=
    isoHomCongrAddEquiv (Iso.refl KL) I0Iso
  let e₂ : (KL ⟶ KQ.obj I) ≃+
      (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj I)) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        (KL ⟶ KQ.obj I) →+ (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj I)))
      (CochainComplex.IsKInjective.Qh_map_bijective KL I)
  let e₃ : (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj I)) ≃+
      ((DerivedCategory.Q.obj L : DerivedCategory A) ⟶
        (DerivedCategory.Q.obj I : DerivedCategory A)) :=
    isoHomCongrAddEquiv
      ((quotientCompQhIso A).app L)
      ((quotientCompQhIso A).app I)
  e₀.trans (e₁.trans (e₂.trans e₃))

private noncomputable def homComplex_homology_zero_addEquiv_mapDerivedCategoryHom
    {A B : Type*} [Category A] [Abelian A] [CategoryWithHomology A]
    [Category B] [Abelian B] [CategoryWithHomology B]
    (F : A ⥤ B)
    [F.Additive]
    [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    (L I : CochainComplex A ℤ)
    [CochainComplex.IsKInjective (((F.mapHomologicalComplex (up ℤ)).obj I))] :
    let Res := F.mapHomologicalComplex (up ℤ)
    (CochainComplex.HomComplex (Res.obj L) (Res.obj I)).homology (0 : ℤ) ≃+
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L) ⟶
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) := by
  let Res : CochainComplex A ℤ ⥤ CochainComplex B ℤ := F.mapHomologicalComplex (up ℤ)
  let e₀ :
      (CochainComplex.HomComplex
          (Res.obj L)
          (Res.obj I)).homology (0 : ℤ) ≃+
        ((DerivedCategory.Q.obj (Res.obj L) : DerivedCategory B) ⟶
          (DerivedCategory.Q.obj (Res.obj I) : DerivedCategory B)) :=
    kInjectiveHomComplex_homology_zero_addEquiv_derivedHom
      (Res.obj L)
      (Res.obj I)
  let e₁ :
      ((DerivedCategory.Q.obj (Res.obj L) : DerivedCategory B) ⟶
          (DerivedCategory.Q.obj (Res.obj I) : DerivedCategory B)) ≃+
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L) ⟶
          F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
    isoHomCongrAddEquiv
      ((F.mapDerivedCategoryFactors.app L).symm)
      ((F.mapDerivedCategoryFactors.app I).symm)
  exact e₀.trans e₁

-- Proof sketch: the clean owner comparison only needs the restricted target complex to be
-- K-injective already. Lemma `21.20.1` then recovers the source-facing localized statement as a
-- theorem-level `IsIsomorphic` comparison, while the concrete localized `≃+` remains private so
-- that proof debt in localized K-injectivity does not become public data.
section

variable [HasBinaryProducts C]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance (U : C) :
    (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).PreservesZeroMorphisms := by
  dsimp [RingedSite.Hom.localizedRestriction]
  refine ⟨fun _ _ ↦ rfl⟩

local instance (U : C) :
    Category (ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :=
  inferInstance
local instance (U : C) :
    Quiver (ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :=
  inferInstance
local instance (U : C) :
    Preadditive (ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :=
  inferInstance
local instance (U : C) (A B :
    ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :
    Add (A ⟶ B) := inferInstance
local instance (U : C) (A B :
    ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :
    AddCommGroup (A ⟶ B) := inferInstance

/-- Internal bridge for Lemma 21.34.6 (1): once the restricted target complex `I|_U` is known to
be K-injective, the localized degree-zero internal-Hom cohomology identifies with the localized
derived-category morphism group. -/
private noncomputable def localizedHomComplex_homology_zero_addEquiv_localizedDerivedHom_of_isKInjective
    (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
    [PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    [PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective]
    [CochainComplex.IsKInjective
      ((localizedRestrictionComplex (RingedSite.ofCommRingSheaf J 𝒪) U).obj I)] :
    let Res := localizedRestrictionComplex (RingedSite.ofCommRingSheaf J 𝒪) U;
      (CochainComplex.HomComplex (Res.obj L) (Res.obj I)).homology (0 : ℤ) ≃+
      (((localizedRestrictionDerived (RingedSite.ofCommRingSheaf J 𝒪) U).obj
          (DerivedCategory.Q.obj L)) ⟶
        ((localizedRestrictionDerived (RingedSite.ofCommRingSheaf J 𝒪) U).obj
          (DerivedCategory.Q.obj I))) := by
  letI : CochainComplex.IsKInjective (((localizedRestriction X U).mapHomologicalComplex (up ℤ)).obj I) := by
    simpa [RingedSite.Hom.localizedRestrictionComplex, RingedSite.Hom.localizedRestriction] using
      (inferInstance :
        CochainComplex.IsKInjective ((localizedRestrictionComplex X U).obj I))
  simpa using
    homComplex_homology_zero_addEquiv_mapDerivedCategoryHom
      (localizedRestriction X U) L I

/-- Lemma 21.34.6 (1): for a ringed site `(𝒞, 𝒪)`, an object `U : 𝒞`, and a K-injective complex
`𝓘` of `𝒪`-modules, the degree-zero cohomology of the localized internal-Hom complex is
canonically isomorphic, in `AddCommGrpCat`, to the morphism group in the localized derived
category. -/
@[stacks 0A94]
theorem localizedHomComplex_homology_zero_isomorphic_localizedDerivedHom
    (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
    [PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    [PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
              ((localizedRestrictionComplex X U).obj L)
              ((localizedRestrictionComplex X U).obj I)).homology
            (0 : ℤ))))
      (AddCommGrpCat.of
        (((j[U]⁻¹).obj (DerivedCategory.Q.obj L)) ⟶
          ((j[U]⁻¹).obj (DerivedCategory.Q.obj I)))) := by
  letI : CochainComplex.IsKInjective ((localizedRestrictionComplex X U).obj I) := by
    simpa using localizedRestrictionComplex_isKInjective J 𝒪 U I
  exact ⟨by
    simpa using
      (AddEquiv.ulift.trans
        (localizedHomComplex_homology_zero_addEquiv_localizedDerivedHom_of_isKInjective
          J 𝒪 U L I)).toAddCommGrpIso⟩

end

-- Proof sketch: this is the ambient, non-localized instance of the same generic K-injective
-- comparison, applied directly in the module category `ModX`.
/-- Lemma 21.34.6 (2): for a ringed site `(𝒞, 𝒪)` and a K-injective complex `𝓘` of
`𝒪`-modules, the degree-zero cohomology of the global internal-Hom complex is canonically
additively equivalent to the morphism group in the ambient derived category:
`H^0(Γ(𝒞, ℋom^⋅(𝓛, 𝓘))) ≃ Hom_{D(𝒪)}(L, I)`. -/
@[stacks 0A94]
noncomputable def homComplex_homology_zero_addEquiv_derivedHom
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
      ((DerivedCategory.Q.obj L : DModX) ⟶
        (DerivedCategory.Q.obj I : DModX)) := by
  simpa using kInjectiveHomComplex_homology_zero_addEquiv_derivedHom L I

end

end SheafOfModules.RingedSite
