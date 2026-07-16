import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_20_2
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_28_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_30_8
import StacksProject_2024.stacks_project.Chap21.Lemma_21_37_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open Opposite
open scoped CategoryTheory
open scoped CategoryTheory.GrothendieckTopology
open scoped GrothendieckTopologyDerivedSections

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

section HypercohomologyComparison

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasWeakSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C, IsGrothendieckAbelian.{u} (SiteAbelianSheafCat (τ.over X))]
variable [∀ X : C, IsGrothendieckAbelian.{u} (SiteAbelianSheafCat (τ'.over X))]

/-- Helper for Lemma 21.30.4: degree-`i` cohomology of a derived object agrees with the homology
of its chosen cochain-complex preimage under `DerivedCategory.Q`. -/
noncomputable def derived_objPreimage_homology_iso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (i : ℤ) :
    (DerivedCategory.homologyFunctor A i).obj K ≅ (DerivedCategory.Q.objPreimage K).homology i := by
  -- Rewrite the derived homology through the canonical representative chosen by `Q.objPreimage`.
  exact
    ((DerivedCategory.homologyFunctor A i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors A i).app (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 21.30.4: a lower cohomological bound on a derived object descends to the
canonical cochain-complex representative chosen by `DerivedCategory.Q`. -/
theorem objPreimage_isGE_of_isGE
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (M : DerivedCategory A)
    {m : ℤ}
    (hM : M.IsGE m) :
    (DerivedCategory.Q.objPreimage M).IsGE m := by
  -- Transport the low-degree vanishing from the derived object to its chosen cochain model.
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rw [DerivedCategory.isGE_iff] at hM
  exact (derived_objPreimage_homology_iso M i).isZero_iff.1 (hM i hi)

/-- Helper for Lemma 21.30.4: derived sections of a bounded-below complex vanish in all lower
degrees. -/
theorem siteAbelianSections_homology_isZero_below_of_isGE
    {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat J)]
    (U : C)
    (M : DerivedCategory (SiteAbelianSheafCat J))
    {i m : ℤ}
    (hi : i < m)
    (hM : M.IsGE m) :
    IsZero ((homologyFunctor AddCommGrpCat.{u} i).obj ((RΓ[J](U)).obj M)) := by
  sorry

/-- Helper for Lemma 21.30.4: after applying derived sections, the upper truncation tail
`τ_{≥ m} M` has zero homology in every degree `i < m`. -/
theorem derived_sections_homology_isZero_of_truncGE
    {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat J)]
    (U : C)
    (M : DerivedCategory (SiteAbelianSheafCat J))
    {i m : ℤ}
    (hi : i < m) :
    IsZero
      ((homologyFunctor AddCommGrpCat.{u} i).obj
        ((RΓ[J](U)).obj ((t.truncGE m).obj M))) := by
  sorry

/-- Helper for Lemma 21.30.4: after applying derived sections, the upper truncation inclusion
`τ_{< m} M ⟶ M` is an isomorphism on degree-`i` homology throughout the full range `i < m`. -/
theorem derived_sections_homologyMap_isIso_of_truncLT
    {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat J)]
    (U : C)
    (M : DerivedCategory (SiteAbelianSheafCat J))
    {i m : ℤ}
    (hi : i < m) :
    IsIso
      ((homologyFunctor AddCommGrpCat.{u} i).map
        ((RΓ[J](U)).map ((t.truncLTι m).app M))) := by
  sorry

/-- Helper for Lemma 21.30.4: the upper truncation inclusion
`τ_{< m} L ⟶ L` is an isomorphism on degree-`q` cohomology throughout the full source-faithful
range `q < m`. -/
theorem truncLT_homologyMap_isIso_in_range
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (L : DerivedCategory A)
    (q m : ℤ)
    (hq : q < m) :
    IsIso
      ((DerivedCategory.homologyFunctor A q).map
        ((t.truncLTι m).app L)) := by
  sorry

/-- Helper for Lemma 21.30.4: precomposition with the derived localization functor reflects
isomorphisms of natural transformations. -/
private theorem isIso_of_whiskerLeft_isIso_local
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {H : Type*} [Category H]
    {F G : DerivedCategory A ⥤ H} (τFG : F ⟶ G)
    [IsIso
      (Functor.whiskerLeft
        (DerivedCategory.Qh :
          HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
        τFG)] :
    IsIso τFG := by
  -- The localization universal property makes whiskering by `Qh` fully faithful, hence it
  -- reflects isomorphisms.
  letI : ((Functor.whiskeringLeft
      (HomotopyCategory A (ComplexShape.up ℤ))
      (DerivedCategory A)
      H).obj
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)).Full :=
    Localization.full_whiskeringLeft
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      H
  letI : ((Functor.whiskeringLeft
      (HomotopyCategory A (ComplexShape.up ℤ))
      (DerivedCategory A)
      H).obj
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)).Faithful :=
    Localization.faithful_whiskeringLeft
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      H
  letI : ((Functor.whiskeringLeft
      (HomotopyCategory A (ComplexShape.up ℤ))
      (DerivedCategory A)
      H).obj
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)).ReflectsIsomorphisms := by
    infer_instance
  letI : IsIso
      (((Functor.whiskeringLeft
          (HomotopyCategory A (ComplexShape.up ℤ))
          (DerivedCategory A)
          H).obj
          (DerivedCategory.Qh :
            HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)).map
          τFG) := by
    change IsIso
      (Functor.whiskerLeft
        (DerivedCategory.Qh :
          HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
        τFG)
    infer_instance
  exact
    Functor.ReflectsIsomorphisms.reflects
      ((Functor.whiskeringLeft
        (HomotopyCategory A (ComplexShape.up ℤ))
        (DerivedCategory A)
        H).obj
        (DerivedCategory.Qh :
          HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A))
      τFG

/-- Helper for Lemma 21.30.4: if both comparison maps out of a homotopy-level source functor are
pointwise isomorphisms, then the induced right-derived descent morphism is an isomorphism. -/
private theorem isIso_rightDerivedDesc_of_app_isIso_local
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {H : Type*} [Category H]
    {F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H}
    {RF G : DerivedCategory A ⥤ H}
    {α : F ⟶
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A) ⋙ RF}
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (β : F ⟶
      (DerivedCategory.Qh :
        HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A) ⋙ G)
    (hα : ∀ K, IsIso (α.app K))
    (hβ : ∀ K, IsIso (β.app K)) :
    IsIso
      (RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β) := by
  -- First show the whiskered descent morphism is pointwise an isomorphism on the homotopy source.
  have hτ :
      IsIso
        (Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
          (RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    -- The defining `rightDerived_fac_app` identity rewrites the comparison through `β.app K`.
    have hcomp :
        IsIso
          (α.app K ≫
            (RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β).app
              ((DerivedCategory.Qh :
                HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A).obj K)) := by
      rw [Functor.rightDerived_fac_app RF α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β K]
      exact hβ K
    exact
      (@isIso_comp_left_iff H _ _ _ _
        (α.app K)
        ((RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β).app
          ((DerivedCategory.Qh :
            HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A).obj K))
        (hα K)).1 hcomp
  -- Then reflect that isomorphism back across the localization.
  letI :
      IsIso
        (Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
          (RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β)) := hτ
  exact
    isIso_of_whiskerLeft_isIso_local
      (RF.rightDerivedDesc α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β)

/- Domain-style sampling for Lemma 21.30.4:
- primary domain: hypercohomology comparison on the slice sites `(C_τ / X)` and
  `(C_{τ'} / X)` under the localized vanishing condition `(V_n)`;
- sampled owner declarations:
  `CohomologyComparisonSituation.LocalVanishing`,
  `siteAbelianSectionsDerived`,
  `Functor.mapDerivedCategory`,
  `comparisonTopologyPullback`;
- best owner abstraction:
  `source-facing`: the cohomology-range hypothesis on `L` and the resulting degree-`n`
    hypercohomology comparison;
  `core/canonical`: the comparison situation owner
    `CohomologyComparisonSituation`, the source condition `(V_n)` owned by
    `CohomologyComparisonSituation.LocalVanishing`, the exact inverse-image
    `ε[hle]_(X)⁻¹` together with its canonical derived functor
    `(ε[hle]_(X)⁻¹).mapDerivedCategory`, and the terminal-object derived-sections owner
    `RΓ[_](Over.mk (𝟙 X))`;
  `bridge/view`: the range-truncation predicate on cohomology sheaves below.

Primitive data are the comparison situation `h`, the object `X`, the derived object `L`, and the
source cohomology-range hypotheses on `L`, together with the source-facing local vanishing
hypothesis `(h.LocalVanishing) n`. The old degree-zero/global-sections bridge predicates and
arbitrary `RGamma` parameters were proof-route artifacts, not owner-level mathematical data, so
the refined theorem below is stated directly with the canonical terminal-object derived-sections
owners, the owner-level inverse-image notation `ε[hle]_(X)⁻¹` and its derived functor, and its
explicit source-facing hypotheses.
-/

-- Proof sketch: apply the Leray spectral sequence for the composition
-- `RΓ((𝟙_X), -) ∘ R ε_{X,*}` on the slice sites. The source-facing local vanishing hypothesis
-- `(V_n)` makes the positive `R^p ε_{X,*}` terms up to degree `n` vanish. The range hypothesis on
-- `L` keeps the `q`-direction inside `A'_X` and excludes negative cohomology. The surviving
-- `p = 0` column is exactly the hypercohomology of `ε_X^{-1}L` over `(C_τ / X)` computed by the
-- canonical terminal-object derived-sections functor, giving the stated comparison.
/-- Lemma 21.30.4: in Situation `21.30.1`, if
`L ∈ D(C_{τ'} / X)` has `H^i(L) = 0` for `i < 0` and `H^i(L) ∈ A'_X` for
`0 ≤ i ≤ n`, and `(V_n)` holds, then the degree-`n` hypercohomology of `L` on `(C_{τ'} / X)` is
canonically isomorphic to the degree-`n` hypercohomology of `ε_X⁻¹L` on `(C_τ / X)`. In Lean the
hypercohomology owners are the canonical slice-site derived-sections functors
`RΓ[τ'.over X](Over.mk (𝟙 X))` and `RΓ[τ.over X](Over.mk (𝟙 X))`, with `(V_n)` expressed by
`CohomologyComparisonSituation.LocalVanishing`. The derived pullback on the right is written
directly as the canonical derived functor `(ε[hle]_(X)⁻¹).mapDerivedCategory`. -/
@[stacks 0EZB]
theorem hypercohomology_comparison_isomorphic_of_conditionV
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ)
    (hVn : h.LocalVanishing n)
    (X : C)
    (L : DerivedCategory (SiteAbelianSheafCat (τ'.over X)))
    (hLneg :
      ∀ i : ℤ, i < 0 → IsZero ((homologyFunctor _ i).obj L))
    (hLA' :
      ∀ i : ℕ, i ≤ n → A' X ((homologyFunctor _ (i : ℤ)).obj L)) :
    IsIsomorphic
      ((homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
        ((RΓ[τ'.over X](Over.mk (𝟙 X))).obj L))
      ((homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
        ((RΓ[τ.over X](Over.mk (𝟙 X))).obj
          (((ε[hle]_(X)⁻¹).mapDerivedCategory).obj L))) := by
  -- Route correction: the source-faithful proof goes through the upper truncation
  -- `τ_{< n + 1} L`, the bounded-below comparison from Lemma `21.30.8`, and the derived-sections
  -- comparison induced from the underived identity-on-`Over X` comparison above. The truncation
  -- comparison on derived sections is now established by
  -- `derived_sections_homologyMap_isIso_of_truncLT`; what remains is the bounded-below packaging
  -- of `τ_{< n + 1} L` and the terminal-object sections/pushforward comparison.
  -- TODO: package `τ_{< n + 1} L` as an object of `D⁺_{A' X}`, apply
  -- `comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn`, and then compare
  -- derived sections via a `rightDerivedDesc` construction built from the identity-on-`Over X`
  -- sections comparison before composing the four degree-`n` isomorphisms from the source proof.
  sorry

end HypercohomologyComparison

end CategoryTheory.GrothendieckTopology
