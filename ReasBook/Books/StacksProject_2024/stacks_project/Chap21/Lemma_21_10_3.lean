import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Definition_13_16_2
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap13.Lemma_13_20_2
import StacksProject_2024.Chap20.«20_2_0_3»
import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap21.Lemma_21_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [EnoughInjectives (Sheaf J AddCommGrpCat)]
variable [IsGrothendieckAbelian (Sheaf J AddCommGrpCat)]

/- Domain-style sampling for Lemma 21.10.3:
- primary domain: the canonical Čech-to-site cohomology comparison for abelian sheaves on a site,
  with the bounded-below derived Čech complex used only as bridge data;
- sampled owner declarations:
  `cechCohomologyDegree`,
  `siteAbelianSectionsFunctor`,
  `siteAbelianSectionsBoundedBelowDerived`,
  `boundedBelowRightDerivedDeltaFunctor`,
  `Functor.boundedBelowRightDerived`,
  `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_enoughInjectives`,
  `DerivedCategory.homologyFunctorFactors`,
  `Sheaf.H'`,
  `Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- best owner abstraction: the source-facing owner is the canonical family of comparison maps
  `Čech H^p(𝒰, F) ⟶ H^p(U, F)` determined by the degree-zero isomorphism
  `Γ(U, F) ≅ Čech H^0(𝒰, F)` and the universal bounded-below right-derived `δ`-functor of
  `Γ(U, -)`;
- primitive data: the covering family `family : ι → Over U`, the canonical degree-`p` Čech
  cohomology functor on abelian sheaves, the bounded-below derived sections owner, and the
  objectwise cohomology owner `ℱ.H' p U`;
- derived API: the degree-zero comparison with sections and the resulting positive-degree Čech-to-
  site cohomology maps; the derived-complex comparison is internal bridge data only.

Source/core/bridge triage:
- `source-facing`: the canonical comparison maps `Čech H^p(𝒰, F) ⟶ H^p(U, F)`;
- `core/canonical`: `cechCohomologyDegree`, `siteAbelianSectionsFunctor`,
  `siteAbelianSectionsBoundedBelowDerived`, `boundedBelowRightDerivedDeltaFunctor`, and `Sheaf.H'`;
- `bridge/view`: Lemma `21.10.2` for the degree-zero identification with sections, the bounded-
  below derived Čech-complex functor, the transport from `ℕ`-indexed Čech complexes to their
  bounded-below `ℤ`-indexed extensions, and the injective-resolution comparison computing
  `ℱ.H' p U`.
-/

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

section

variable (J)
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type u} (family : ι → Over U)

/-- The positive-degree Čech cohomology functor on abelian sheaves is canonically isomorphic to
the higher right derived functor of degree-zero Čech cohomology. This is the sheaf-level
companion to the bounded-below/right-derived owner comparison, with the presheaf-side comparison
used only internally as bridge data. -/
theorem higherCechCohomologyOnSheaves_isomorphic_rightDerived (q : ℕ) :
    IsIsomorphic (cechCohomologyOnSheaves J family (q + 1))
      ((cechCohomologyOnSheaves J family 0).rightDerived (q + 1)) := by
  -- Intended owner-level route: first identify the bounded-below derived sections package with the
  -- canonical right-derived `δ`-functor on sheaves, then read off the positive-degree terms.
  sorry

private abbrev cechComplexOnSheavesExtended
    (U : C) [Limits.HasFiniteProducts (Over U)] {ι : Type u} (family : ι → Over U) :
    Sheaf J AddCommGrpCat.{u} ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (sheafToPresheaf J AddCommGrpCat.{u} ⋙ cechComplexOnPresheaves U family) ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{u}

omit [HasWeakSheafify J AddCommGrpCat] [HasSheafify J AddCommGrpCat]
  [EnoughInjectives (Sheaf J AddCommGrpCat)]
  [IsGrothendieckAbelian (Sheaf J AddCommGrpCat)] in
private theorem cechComplexDerived_obj_mem
    (U : C) [Limits.HasFiniteProducts (Over U)] {ι : Type u} (family : ι → Over U)
    (F : Sheaf J AddCommGrpCat.{u}) :
    (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
      ((cechComplexOnSheavesExtended J U family ⋙ DerivedCategory.Q).obj F) := by
  let K := (cechComplexOnSheavesExtended J U family).obj F
  letI : CochainComplex.IsStrictlyGE K 0 := by
    change
      CochainComplex.IsStrictlyGE
        (HomologicalComplex.extend
          ((sheafToPresheaf J AddCommGrpCat.{u} ⋙ cechComplexOnPresheaves U family).obj F)
          ComplexShape.embeddingUpNat)
        0
    infer_instance
  letI : K.IsGE 0 := inferInstance
  refine ⟨0, ?_⟩
  change (DerivedCategory.Q.obj K).IsGE 0
  exact
    (DerivedCategory.isGE_Q_obj_iff K 0).2 inferInstance

/-- Bridge owner for Lemma 21.10.3: the bounded-below derived Čech complex functor
`Čech C^•(𝒰, -)` on abelian sheaves. Its role is to mediate between
the source-facing Čech cohomology owner and the canonical bounded-below derived sections functor;
the comparison maps to site cohomology are obtained by applying homology to a normalized natural
transformation out of this bridge. -/
noncomputable def cechComplexDerivedFunctor
    (U : C) [Limits.HasFiniteProducts (Over U)] {ι : Type u} (family : ι → Over U) :
    Sheaf J AddCommGrpCat.{u} ⥤ D⁺(AddCommGrpCat.{u}) :=
  ObjectProperty.lift
    (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
    (cechComplexOnSheavesExtended J U family ⋙ DerivedCategory.Q)
    (cechComplexDerived_obj_mem J U family)

private noncomputable def cechComplexHomologyIso
    (U : C) [Limits.HasFiniteProducts (Over U)] {ι : Type u} (family : ι → Over U)
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    ((cechCohomologyOnSheaves J family p).obj F) ≅
      ((cechComplexOnSheavesExtended J U family).obj F).homology ((p : ℕ) : ℤ) := by
  let K := (sheafToPresheaf J AddCommGrpCat.{u} ⋙ cechComplexOnPresheaves U family).obj F
  change K.homology p ≅ (K.extend ComplexShape.embeddingUpNat).homology ((p : ℕ) : ℤ)
  exact (K.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).symm

private noncomputable def cechComplexDerivedHomologyIso
    (U : C) [Limits.HasFiniteProducts (Over U)] {ι : Type u} (family : ι → Over U)
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    ((cechComplexOnSheavesExtended J U family).obj F).homology ((p : ℕ) : ℤ) ≅
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((p : ℕ) : ℤ)).obj
        ((cechComplexDerivedFunctor J U family).obj F).obj) := by
  let K := (cechComplexOnSheavesExtended J U family).obj F
  let e :
      (ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat))).obj
          ((cechComplexDerivedFunctor J U family).obj F) ≅
        DerivedCategory.Q.obj K :=
    (ObjectProperty.liftCompιIso
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat))
      (cechComplexOnSheavesExtended J U family ⋙ DerivedCategory.Q)
      (cechComplexDerived_obj_mem J U family)).app F
  exact
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} ((p : ℕ) : ℤ)).app K).symm ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((p : ℕ) : ℤ)).mapIso e.symm

/-- The bounded-below derived sections package computes the canonical site-cohomology owner
`F ↦ F.H' p U` in degree `p`. -/
private theorem boundedBelowDerivedSections_boundedBelowRightDerived_eq_cohomologyAtObjectFunctor
    (p : ℕ) :
    (siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived p =
      (Sheaf.cohomologyPresheafFunctor J p ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) := by
  /- Proof sketch: both sides are the degree-`p` right derived functor of the same sections
  owner `Γ(U, -)`, with the left side computed through the bounded-below total right derived
  functor and the right side through the canonical local cohomology owner `F ↦ F.H' p U`. -/
  sorry

private theorem boundedBelowDerivedSections_boundedBelowRightDerived_obj_eq_H'
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived p).obj F) =
      F.H' p U := by
  simpa [Sheaf.H'] using congrArg (fun G ↦ G.obj F)
    (boundedBelowDerivedSections_boundedBelowRightDerived_eq_cohomologyAtObjectFunctor
      J U p)

/-- Bridge helper: the degree-`p` comparison from Čech cohomology to the bounded-below derived
sections owner, induced by a comparison natural transformation of bounded-below derived complex
models. -/
noncomputable def cechCohomologyToBoundedBelowDerivedSections
    (τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U)
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    ((cechCohomologyOnSheaves J family p).obj F) ⟶
      (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived p).obj F) :=
  (cechComplexHomologyIso J U family p F).hom ≫
  (cechComplexDerivedHomologyIso J U family p F).hom ≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((p : ℕ) : ℤ)).map
      ((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat))).map
        (τ.app F)))

/-- A normalized comparison from the bounded-below derived Čech complex model to the
bounded-below derived sections functor. The normalization requires the induced degree-zero map to
agree with the canonical identification `Čech H^0(𝒰, F) ⟶ H^0(U, F)`. -/
def IsCechComplexToDerivedSectionsComparison
    (τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U) : Prop :=
  (∀ ℐ : Sheaf J AddCommGrpCat, Injective ℐ → IsIso (τ.app ℐ)) ∧
    ∀ F : Sheaf J AddCommGrpCat,
      ∃ h :
        (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived 0).obj F) =
          F.H' 0 U,
        ∃ comparisonIso :
          F.H' 0 U ≅
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) 0).obj
              ((((siteAbelianSectionsFunctor J U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                (injectiveResolution F).cocomplex))),
          ∃ cechZeroIso :
            ((cechCohomologyOnSheaves J family 0).obj F) ≅
              (siteAbelianSectionsFunctor J U).obj F,
            cechCohomologyToBoundedBelowDerivedSections J U family τ 0 F ≫ eqToHom h =
              cechZeroIso.hom ≫
                ((Functor.rightDerivedZeroIsoSelf (siteAbelianSectionsFunctor J U)).app F).inv ≫
                  (((injectiveResolution F).isoRightDerivedObj
                    (siteAbelianSectionsFunctor J U) 0 ≪≫ comparisonIso.symm).hom)

/-- A degree-zero Čech-to-site comparison map on `F`, described via a normalized bounded-below
derived comparison. -/
def IsCechCohomologyZeroToSiteCohomology
    (F : Sheaf J AddCommGrpCat.{u})
    (f : ((cechCohomologyOnSheaves J family 0).obj F) ⟶ F.H' 0 U) : Prop :=
  ∃ τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U,
    IsCechComplexToDerivedSectionsComparison J U family τ ∧
      ∃ h :
        (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived 0).obj F) =
          F.H' 0 U,
        f = cechCohomologyToBoundedBelowDerivedSections J U family τ 0 F ≫ eqToHom h

/-- A degree-`q + 1` Čech-to-site comparison map on `F`, described via a normalized bounded-below
derived comparison. -/
def IsCechCohomologyToSiteCohomologySucc
    (q : ℕ) (F : Sheaf J AddCommGrpCat.{u})
    (f : ((cechCohomologyOnSheaves J family (q + 1)).obj F) ⟶ F.H' (q + 1) U) : Prop :=
  ∃ τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U,
    IsCechComplexToDerivedSectionsComparison J U family τ ∧
      ∃ h :
        (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived (q + 1)).obj F) =
          F.H' (q + 1) U,
        f = cechCohomologyToBoundedBelowDerivedSections J U family τ (q + 1) F ≫ eqToHom h

-- Proof sketch: compare the bounded-below derived Čech complex model with the canonical bounded-
-- below derived sections functor by a right-derived comparison normalized to induce the canonical
-- degree-zero map `Čech H^0(𝒰, F) ⟶ H^0(U, F)`. Uniqueness of this normalization is
-- the key point ensuring that the public positive-degree comparison does not depend on arbitrary
-- hidden choice.
/-- For a covering family, there is a unique normalized bounded-below comparison from the Čech
complex model to the canonical derived sections functor. -/
theorem cechComplexToDerivedSectionsComparison_existsUnique
    (hfamily : (J.over U).CoversTop family) :
    ∃! τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U,
      IsCechComplexToDerivedSectionsComparison J U family τ := by
  sorry

/-- On injective abelian sheaves, a normalized bounded-below Čech-to-derived-sections comparison
is an isomorphism. -/
instance cechComplexToDerivedSectionsComparison_app_isIso_of_injective
    {τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U}
    (hτ : IsCechComplexToDerivedSectionsComparison J U family τ)
    (ℐ : Sheaf J AddCommGrpCat.{u}) [Injective ℐ] :
    IsIso (τ.app ℐ) :=
  hτ.1 ℐ inferInstance

/-- Any normalized bounded-below comparison induces a degree-zero Čech-to-site comparison. -/
theorem IsCechComplexToDerivedSectionsComparison.isCechCohomologyZeroToSiteCohomology
    {τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U}
    (hτ : IsCechComplexToDerivedSectionsComparison J U family τ)
    (F : Sheaf J AddCommGrpCat.{u})
    (h :
      (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived 0).obj F) =
        F.H' 0 U) :
    IsCechCohomologyZeroToSiteCohomology J U family F
      (cechCohomologyToBoundedBelowDerivedSections J U family τ 0 F ≫ eqToHom h) :=
  ⟨τ, hτ, h, rfl⟩

/-- Any normalized bounded-below comparison induces a positive-degree Čech-to-site comparison. -/
theorem IsCechComplexToDerivedSectionsComparison.isCechCohomologyToSiteCohomologySucc
    {τ :
      cechComplexDerivedFunctor J U family ⟶
        sheafToBoundedBelowDerivedSectionsFunctor J U}
    (hτ : IsCechComplexToDerivedSectionsComparison J U family τ)
    (q : ℕ) (F : Sheaf J AddCommGrpCat.{u})
    (h :
      (((siteAbelianSectionsBoundedBelowDerived J U).boundedBelowRightDerived (q + 1)).obj F) =
        F.H' (q + 1) U) :
    IsCechCohomologyToSiteCohomologySucc J U family q F
      (cechCohomologyToBoundedBelowDerivedSections J U family τ (q + 1) F ≫ eqToHom h) :=
  ⟨τ, hτ, h, rfl⟩

/-- Companion specification for a degree-zero Čech-to-site comparison map. -/
theorem IsCechCohomologyZeroToSiteCohomology.spec
    {F : Sheaf J AddCommGrpCat.{u}}
    {f : ((cechCohomologyOnSheaves J family 0).obj F) ⟶ F.H' 0 U}
    (hf : IsCechCohomologyZeroToSiteCohomology J U family F f) :
    ∃ comparisonIso :
      F.H' 0 U ≅
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) 0).obj
          ((((siteAbelianSectionsFunctor J U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex))),
      ∃ cechZeroIso :
        ((cechCohomologyOnSheaves J family 0).obj F) ≅
          (siteAbelianSectionsFunctor J U).obj F,
        f = cechZeroIso.hom ≫
          ((Functor.rightDerivedZeroIsoSelf (siteAbelianSectionsFunctor J U)).app F).inv ≫
            (((injectiveResolution F).isoRightDerivedObj
              (siteAbelianSectionsFunctor J U) 0 ≪≫ comparisonIso.symm).hom) := by
  sorry

/-- Lemma 21.10.3: for a covering family, there is a unique degree-zero comparison
`Čech H^0(𝒰, F) ⟶ H^0(U, F)` for abelian sheaves on `(C, J)`. -/
@[stacks 03AX]
theorem cechCohomologyZeroToSiteCohomology_existsUnique
    (hfamily : (J.over U).CoversTop family)
    (F : Sheaf J AddCommGrpCat.{u}) :
    ∃! f : ((cechCohomologyOnSheaves J family 0).obj F) ⟶ F.H' 0 U,
      IsCechCohomologyZeroToSiteCohomology J U family F f := by
  sorry

/-- Lemma 21.10.3: for a covering family, there is a unique degree-`q + 1` comparison
`Čech H^(q + 1)(𝒰, F) ⟶ H^(q + 1)(U, F)` for abelian sheaves on `(C, J)`. -/
@[stacks 03AX]
theorem cechCohomologyToSiteCohomologySucc_existsUnique
    (hfamily : (J.over U).CoversTop family)
    (q : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    ∃! f : ((cechCohomologyOnSheaves J family (q + 1)).obj F) ⟶ F.H' (q + 1) U,
      IsCechCohomologyToSiteCohomologySucc J U family q F f := by
  sorry

end
end CategoryTheory
end
