import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.Chap20.Open_subspace_module_owners

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.DerivedCategory
open CochainComplex.HomComplex.CohomologyClass
open ComplexShape
open DerivedCategory HomotopyCategory
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.41.6:
- primary domain: restriction of complexes of `𝒪_X`-modules to an open subspace and the
  identification of degree-zero Hom-complex cohomology with derived-category morphisms into a
  K-injective complex;
- sampled owner declarations:
  `openSubspaceModuleCategory`,
  `moduleRestrictionToOpen`,
  `moduleRestrictionToOpenDerived`,
  `moduleRestrictionToOpen_isKInjective`,
  `CochainComplex.HomComplex.homologyAddEquiv`;
- best owner abstraction: the Chapter 20 owner file `Open_subspace_module_owners` for
  `openSubspaceModuleCategory X U`, `moduleRestrictionToOpen X U`, and
  `moduleRestrictionToOpen_isKInjective`, together with the canonical Hom-complex/homotopy
  equivalence and the K-injective hom-bijection
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- primitive data: the ringed space `X`, the open subset `U`, the complexes `Lc`, `Ic`, and the
  hypothesis that `Ic` is K-injective;
- derived API: restriction on complexes, localization to `D(𝒪_U)`, and the equivalence
  below.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.6 itself, identifying the restricted internal-Hom cohomology with
  morphisms in `D(𝒪_U)`;
- `core/canonical`: `openSubspaceModuleCategory`, `moduleRestrictionToOpen`,
  `moduleRestrictionToOpenDerived`, `moduleRestrictionToOpen_isKInjective`,
  `CochainComplex.HomComplex.homologyAddEquiv`, `homAddEquiv`, and
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: this file should compose those canonical owners directly, not rebuild parallel
  local ambient/open-subspace module-category abbreviations.
-/

section

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

local notation "ModX" => RingedSpace.Modules X

/-- Transport along source and target isomorphisms is additive on Hom groups in a preadditive
category. -/
private theorem isoHomCongr_map_add
    {C : Type*} [Category C] [Preadditive C] {A B A₁ B₁ : C}
    (eA : A ≅ A₁) (eB : B ≅ B₁) (f g : A ⟶ B) :
    eA.homCongr eB (f + g) = eA.homCongr eB f + eA.homCongr eB g := by
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Isomorphisms on source and target induce an additive equivalence on Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {A B A₁ B₁ : C}
    (eA : A ≅ A₁) (eB : B ≅ B₁) :
    (A ⟶ B) ≃+ (A₁ ⟶ B₁) where
  toEquiv := eA.homCongr eB
  map_add' := isoHomCongr_map_add eA eB

/-- Helper for Lemma 20.41.6: restricting a K-injective complex to `U` preserves
K-injectivity. -/
private theorem restrictedComplexOnOpen_isKInjective
    (Ic : CochainComplex ModX ℤ) [Ic.IsKInjective] :
    (restrictedComplexOnOpen X U Ic).IsKInjective := by
  simpa [restrictedComplexOnOpen] using moduleRestrictionToOpen_isKInjective U Ic

/-- Helper for Lemma 20.41.6: for a K-injective restricted target complex, degree-zero
Hom-complex cohomology on `U` identifies with morphisms in `D(𝒪_U)`. -/
private noncomputable def restrictedHomComplex_homology_zero_addEquiv_restrictedDerivedHom
    (Lc Ic : CochainComplex ModX ℤ)
    [(restrictedComplexOnOpen X U Ic).IsKInjective] :
    ((CochainComplex.HomComplex
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ)) ≃+
      ((DerivedCategory.Q.obj (restrictedComplexOnOpen X U Lc) :
          DerivedCategory (openSubspaceModuleCategory X U)) ⟶
        (DerivedCategory.Q.obj (restrictedComplexOnOpen X U Ic) :
          DerivedCategory (openSubspaceModuleCategory X U))) :=
  let KQ := HomotopyCategory.quotient (openSubspaceModuleCategory X U) (up ℤ)
  let KL := KQ.obj (restrictedComplexOnOpen X U Lc)
  let I0Iso :
      KQ.obj ((restrictedComplexOnOpen X U Ic)⟦(0 : ℤ)⟧) ≅
        KQ.obj (restrictedComplexOnOpen X U Ic) :=
    KQ.mapIso ((shiftFunctorZero (CochainComplex (openSubspaceModuleCategory X U) ℤ) ℤ).app
      (restrictedComplexOnOpen X U Ic))
  let e₀ :
      ((CochainComplex.HomComplex
          (restrictedComplexOnOpen X U Lc)
          (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ)) ≃+
        (KL ⟶ KQ.obj ((restrictedComplexOnOpen X U Ic)⟦(0 : ℤ)⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)
        (0 : ℤ)).trans homAddEquiv
  let e₁ :
      (KL ⟶ KQ.obj ((restrictedComplexOnOpen X U Ic)⟦(0 : ℤ)⟧)) ≃+
        (KL ⟶ KQ.obj (restrictedComplexOnOpen X U Ic)) :=
    isoHomCongrAddEquiv (Iso.refl KL) I0Iso
  let e₂ :
      (KL ⟶ KQ.obj (restrictedComplexOnOpen X U Ic)) ≃+
        (DerivedCategory.Qh.obj KL ⟶
          DerivedCategory.Qh.obj (KQ.obj (restrictedComplexOnOpen X U Ic))) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        (KL ⟶ KQ.obj (restrictedComplexOnOpen X U Ic)) →+
          (DerivedCategory.Qh.obj KL ⟶
            DerivedCategory.Qh.obj (KQ.obj (restrictedComplexOnOpen X U Ic))))
      (CochainComplex.IsKInjective.Qh_map_bijective KL (restrictedComplexOnOpen X U Ic))
  let e₃ :
      (DerivedCategory.Qh.obj KL ⟶
          DerivedCategory.Qh.obj (KQ.obj (restrictedComplexOnOpen X U Ic))) ≃+
        ((DerivedCategory.Q.obj (restrictedComplexOnOpen X U Lc) :
            DerivedCategory (openSubspaceModuleCategory X U)) ⟶
          (DerivedCategory.Q.obj (restrictedComplexOnOpen X U Ic) :
            DerivedCategory (openSubspaceModuleCategory X U))) :=
    isoHomCongrAddEquiv
      ((DerivedCategory.quotientCompQhIso (openSubspaceModuleCategory X U)).app
        (restrictedComplexOnOpen X U Lc))
      ((DerivedCategory.quotientCompQhIso (openSubspaceModuleCategory X U)).app
        (restrictedComplexOnOpen X U Ic))
  e₀.trans (e₁.trans (e₂.trans e₃))

/-- Helper for Lemma 20.41.6: the derived restriction functor agrees with the intrinsic
restricted derived objects on Hom groups. -/
private noncomputable def restrictedDerivedHom_addEquiv_moduleRestrictionToOpenDerivedHom
    (Lc Ic : CochainComplex ModX ℤ) :
    ((DerivedCategory.Q.obj (restrictedComplexOnOpen X U Lc) :
        DerivedCategory (openSubspaceModuleCategory X U)) ⟶
      (DerivedCategory.Q.obj (restrictedComplexOnOpen X U Ic) :
        DerivedCategory (openSubspaceModuleCategory X U))) ≃+
      (((moduleRestrictionToOpenDerived X U).obj (Q.obj Lc)) ⟶
        ((moduleRestrictionToOpenDerived X U).obj (Q.obj Ic))) :=
  isoHomCongrAddEquiv
    (moduleRestrictionToOpenDerivedFactors X U Lc).symm
    (moduleRestrictionToOpenDerivedFactors X U Ic).symm

/-- Helper for Lemma 20.41.6: the functorial restricted derived object agrees with the intrinsic
restriction `K↾[U]`. -/
private theorem moduleRestrictionToOpenDerivedObjIsomorphicRestrictedModuleDerivedOnOpen
    (K : DerivedCategory ModX) :
    IsIsomorphic ((moduleRestrictionToOpenDerived X U).obj K) (K↾[U]) := by
  refine
    ⟨(moduleRestrictionToOpenDerived X U).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ ?_⟩
  simpa [restrictedModuleDerivedOnOpen] using
    moduleRestrictionToOpenDerivedFactors X U (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 20.41.6: once the functorial restricted derived objects are identified with
the intrinsic restricted objects, the corresponding Hom groups are canonically isomorphic. -/
private theorem moduleRestrictionToOpenDerivedHomObj_isomorphic_restrictedModuleDerivedOnOpenHom
    (Lc Ic : CochainComplex ModX ℤ) :
    IsIsomorphic
      (AddCommGrpCat.of
        (((moduleRestrictionToOpenDerived X U).obj (Q.obj Lc)) ⟶
          ((moduleRestrictionToOpenDerived X U).obj (Q.obj Ic))))
      (AddCommGrpCat.of ((Q.obj Lc)↾[U] ⟶ (Q.obj Ic)↾[U])) := by
  rcases
      moduleRestrictionToOpenDerivedObjIsomorphicRestrictedModuleDerivedOnOpen
        (X := X) (U := U) (Q.obj Lc) with
    ⟨eLc⟩
  rcases
      moduleRestrictionToOpenDerivedObjIsomorphicRestrictedModuleDerivedOnOpen
        (X := X) (U := U) (Q.obj Ic) with
    ⟨eIc⟩
  exact ⟨(isoHomCongrAddEquiv eLc eIc).toAddCommGrpIso⟩

-- Proof sketch: apply the canonical `20.41.0.1` additive equivalence with `n = 0` to the
-- restricted complexes `𝓛^•|_U` and `𝓘^•|_U`, giving morphisms in the homotopy category
-- `K(𝒪_U)`. By Lemma `20.32.1`, the restriction of the K-injective complex `𝓘^•` is again
-- K-injective, so the localization functor identifies these homotopy classes with morphisms in
-- `D(𝒪_U)`. This is the restricted-representative form of the textbook identification
-- `H^0(Γ(U, Hom^•(𝓛^•, 𝓘^•))) = Hom_{D(𝒪_U)}(L|_U, M|_U)`.
/-- The degree-zero cohomology of the restricted internal-Hom complex is canonically isomorphic,
as an object of `AddCommGrpCat`, to morphisms between the functorial derived restrictions of
`Q.obj Lc` and `Q.obj Ic` to `U`. -/
theorem openSubspaceHomComplex_homology_zero_isomorphic_moduleRestrictionToOpenDerivedHom
    (Lc Ic : CochainComplex ModX ℤ) [Ic.IsKInjective] :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
            (restrictedComplexOnOpen X U Lc)
            (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ))))
      (AddCommGrpCat.of
        (((moduleRestrictionToOpenDerived X U).obj (Q.obj Lc)) ⟶
          ((moduleRestrictionToOpenDerived X U).obj (Q.obj Ic)))) := by
  let _ : (restrictedComplexOnOpen X U Ic).IsKInjective :=
    restrictedComplexOnOpen_isKInjective (X := X) (U := U) Ic
  let e₀ :=
    restrictedHomComplex_homology_zero_addEquiv_restrictedDerivedHom
      (X := X) (U := U) Lc Ic
  let e₁ :=
    restrictedDerivedHom_addEquiv_moduleRestrictionToOpenDerivedHom
      (X := X) (U := U) Lc Ic
  exact ⟨(AddEquiv.ulift.trans (e₀.trans e₁)).toAddCommGrpIso⟩

/-- Lemma 20.41.6: if `Lc` and `Ic` are complexes of `𝒪_X`-modules and `Ic` is
K-injective, then the degree-zero cohomology of the sections of the restricted internal-Hom
complex on an open subset `U` has a canonical universe lift that is isomorphic, as an object of
`AddCommGrpCat`, to the local derived morphism group
`AddCommGrpCat.of ((Q.obj Lc)↾[U] ⟶ (Q.obj Ic)↾[U])`; the companion
`openSubspaceHomComplex_homology_zero_isomorphic_moduleRestrictionToOpenDerivedHom` exposes the same
comparison first on the functorial derived restrictions, and Lemma `20.32.2` transports it to the
intrinsic restriction objects. -/
@[stacks 0A8R]
theorem openSubspaceHomComplex_homology_zero_isomorphic_restrictedDerivedHom
    (Lc Ic : CochainComplex ModX ℤ)
    [Ic.IsKInjective] :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
            (restrictedComplexOnOpen X U Lc)
            (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ))))
      (AddCommGrpCat.of ((Q.obj Lc)↾[U] ⟶ (Q.obj Ic)↾[U])) :=
by
  rcases openSubspaceHomComplex_homology_zero_isomorphic_moduleRestrictionToOpenDerivedHom
      Lc Ic with ⟨e⟩
  rcases moduleRestrictionToOpenDerivedHomObj_isomorphic_restrictedModuleDerivedOnOpenHom
      Lc Ic with ⟨e'⟩
  exact ⟨e ≪≫ e'⟩

end

end AlgebraicGeometry.RingedSpace
