import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory
namespace Sheaf

/- Domain-style sampling for Lemma 21.7.2:
- primary domain: inverse image on abelian sheaves over sites and the induced comparison on local
  and global sheaf cohomology;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `siteAbelianSectionsFunctor`,
  `InjectiveResolution.isoRightDerivedObj`,
  `Sheaf.cohomologyPresheaf`,
  `Sheaf.H'`,
  `Sheaf.cohomologyFunctor`,
  `NatTrans.rightDerived`;
- best owner abstraction: the local comparison is canonically owned by the underived sections
  isomorphism
  `u.sheafPushforwardContinuous AddCommGrpCat J K ⋙ siteAbelianSectionsFunctor J U ≅
    siteAbelianSectionsFunctor K (u.obj U)`,
  while the source-facing `H^p(U,-)` comparison is obtained by composing this derived-sections
  isomorphism with the canonical `sheafSections`-to-`H'` bridge;
- primitive data: the site functor `u : C ⥤ D`, the object `U : C`, and the abelian sheaf `F`;
- derived API: the canonical comparison morphism on `H^p(U, -)` and its `IsIso`/isomorphic
  companions.

Source/core/bridge triage:
- `source-facing`: the comparison
  `H^p(U, g^{-1}\mathcal F) ⟶ H^p(g(U), \mathcal F)` and its global-cohomology analogue;
- `core/canonical`: `u.sheafPushforwardContinuous`, `sheafSections`,
  `InjectiveResolution.isoRightDerivedObj`, `Sheaf.cohomologyPresheaf`, `Sheaf.H'`,
  `Sheaf.cohomologyFunctor`, and `NatTrans.rightDerived`;
- `bridge/view`: evaluation at `U` via `sheafSections`, together with the injective-resolution
  computation of `H'`.
-/

private instance abelianPresheafLimit_additive
    {C : Type u} [Category.{u} C] :
    (lim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π G j = (limMap f + limMap g) ≫ limit.π G j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

@[stacks 03YU]
noncomputable def sheafPushforwardContinuous_sectionsOverObjectIso
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] (U : C) :
    u.sheafPushforwardContinuous AddCommGrpCat.{u} J K ⋙ siteAbelianSectionsFunctor J U ≅
      siteAbelianSectionsFunctor K (u.obj U) := by
  simpa [siteAbelianSectionsFunctor] using
    (Functor.isoWhiskerRight
      (u.sheafPushforwardContinuousCompSheafToPresheafIso AddCommGrpCat.{u} J K)
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))

/-- Helper: inverse image on abelian sheaves is additive because it is induced by precomposition on
underlying abelian presheaves. -/
private instance sheafPushforwardContinuous_additive
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] :
    (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).Additive := by
  simpa [Functor.sheafPushforwardContinuous] using
    (inferInstance :
      (ObjectProperty.lift _
        (sheafToPresheaf K AddCommGrpCat.{u} ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj u.op)
        (u.op_comp_isSheaf J K)).Additive)

section Local

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]

private instance sheafPushforwardContinuous_sectionsOverObject_additive (U : C) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K ⋙
      siteAbelianSectionsFunctor J U).Additive := by
  exact Functor.additive_of_iso
    (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).symm

-- Semantic recall: the project-level proxy for the source's "hypotheses of Sites, Lemma 7.21.8"
-- follows the Chapter 34 bigger-site owner pattern combining the continuous and cocontinuous
-- morphisms of topoi.
variable [u.Full] [u.Faithful] [u.IsCocontinuous J K]
variable [HasWeakSheafify K (Type u)]
variable [∀ P : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]
variable [HasSheafify J (Type u)]
variable [∀ P : Cᵒᵖ ⥤ Type u, u.op.HasPointwiseRightKanExtension P]

omit [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf K AddCommGrpCat.{u})] in
/-- Owner-level companion for Lemma 21.7.2 (1): deriving the explicit underived sections
comparison over `U` yields a canonical isomorphism between the degree-`p` right derived functors
of the two sections functors. -/
@[stacks 03YU]
noncomputable def sheafPushforwardContinuous_sectionsOverObjectDerivedIso
    (p : ℕ) (U : C) :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K ⋙
        siteAbelianSectionsFunctor J U).rightDerived p) ≅
      ((siteAbelianSectionsFunctor K (u.obj U)).rightDerived p) :=
  { hom :=
      NatTrans.rightDerived
        (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).hom p
    inv :=
      NatTrans.rightDerived
        (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).inv p
    hom_inv_id := by
      simpa using
        (NatTrans.rightDerived_comp
          (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).hom
          (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).inv
          p).symm
    inv_hom_id := by
      simpa using
        (NatTrans.rightDerived_comp
          (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).inv
          (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).hom
          p).symm }

@[stacks 03YU]
theorem sheafPushforwardContinuous_sectionsOverObjectDerivedIso_hom
    (p : ℕ) (U : C) :
    (sheafPushforwardContinuous_sectionsOverObjectDerivedIso u p U).hom =
      NatTrans.rightDerived
        (sheafPushforwardContinuous_sectionsOverObjectIso J K u U).hom p := sorry

/-- Lemma 21.7.2 (2): for any abelian sheaf `F` on `D`, inverse image identifies the degree-`p`
cohomology over `U` with the degree-`p` cohomology over `u(U)`, functorially in `F`. -/
@[stacks 03YU]
theorem sheafPushforwardContinuous_cohomologyAtObject_isomorphic
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    IsIsomorphic
      (((u.sheafPushforwardContinuous AddCommGrpCat J K).obj F).H' p U)
      (F.H' p (u.obj U)) := sorry

/-- A chosen objectwise cohomology isomorphism attached to
`sheafPushforwardContinuous_cohomologyAtObject_isomorphic`. -/
@[stacks 03YU]
noncomputable abbrev sheafPushforwardContinuous_cohomologyAtObjectIso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    (((u.sheafPushforwardContinuous AddCommGrpCat J K).obj F).H' p U) ≅
      (F.H' p (u.obj U)) :=
  Classical.choice
    (sheafPushforwardContinuous_cohomologyAtObject_isomorphic u F p U)

/-- The chosen objectwise comparison morphism induced by
`sheafPushforwardContinuous_cohomologyAtObjectIso`. -/
@[stacks 03YU]
noncomputable abbrev sheafPushforwardContinuous_cohomologyAtObjectComparison
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    (((u.sheafPushforwardContinuous AddCommGrpCat J K).obj F).H' p U) ⟶
      (F.H' p (u.obj U)) :=
  (sheafPushforwardContinuous_cohomologyAtObjectIso u F p U).hom

@[stacks 03YU]
theorem sheafPushforwardContinuous_cohomologyAtObjectIso_eq_choice
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    (sheafPushforwardContinuous_cohomologyAtObjectIso u F p U :
      (((u.sheafPushforwardContinuous AddCommGrpCat J K).obj F).H' p U) ≅
        (F.H' p (u.obj U))) =
      Classical.choice
        (sheafPushforwardContinuous_cohomologyAtObject_isomorphic u F p U) := sorry

@[stacks 03YU]
theorem sheafPushforwardContinuous_cohomologyAtObjectComparison_isIso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    IsIso
      (sheafPushforwardContinuous_cohomologyAtObjectComparison u F p U :
        (((u.sheafPushforwardContinuous AddCommGrpCat J K).obj F).H' p U) ⟶
          (F.H' p (u.obj U))) := sorry

end Local

section Global

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [u.IsContinuous J K]
variable [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]

/-- Internal bridge identifying global sections with sections over chosen terminal objects. -/
private noncomputable def sheafPushforwardContinuous_comp_globalSectionsIso
    (eC : C) (hC : IsTerminal eC) (huC : IsTerminal (u.obj eC)) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K ⋙ Sheaf.Γ J AddCommGrpCat.{u}) ≅
      Sheaf.Γ K AddCommGrpCat.{u} := by
  letI : ∀ X : C, Unique (X ⟶ eC) := fun X ↦
    { default := hC.from X
      uniq := fun f ↦ hC.hom_ext f (hC.from X) }
  letI : HasTerminal C := Limits.hasTerminal_of_unique eC
  letI : ∀ Y : D, Unique (Y ⟶ u.obj eC) := fun Y ↦
    { default := huC.from Y
      uniq := fun f ↦ huC.hom_ext f (huC.from Y) }
  letI : HasTerminal D := Limits.hasTerminal_of_unique (u.obj eC)
  exact
    Functor.isoWhiskerLeft
        (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K)
        (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{u} hC) ≪≫
      sheafPushforwardContinuous_sectionsOverObjectIso J K u eC ≪≫
      (Sheaf.ΓNatIsoSheafSections K AddCommGrpCat.{u} huC).symm

variable [u.Full] [u.Faithful] [u.IsCocontinuous J K]
variable [HasWeakSheafify K (Type u)]
variable [∀ P : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]
variable [HasSheafify J (Type u)]
variable [∀ P : Cᵒᵖ ⥤ Type u, u.op.HasPointwiseRightKanExtension P]

section DerivedGlobal

variable [HasGlobalSectionsFunctor J AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor K AddCommGrpCat.{u}]

private instance gammaJ_additive :
    (Sheaf.Γ J AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_iso (Sheaf.ΓNatIsoLim J AddCommGrpCat.{u}).symm

private instance gammaK_additive :
    (Sheaf.Γ K AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_iso (Sheaf.ΓNatIsoLim K AddCommGrpCat.{u}).symm

/-- Lemma 21.7.2 (3): for any abelian sheaf `F` on `D`, inverse image identifies
`RΓ(C, g⁻¹F)` with `RΓ(D, F)`, functorially in `F`. -/
@[stacks 03YU]
theorem sheafPushforwardContinuous_globalSectionsDerived_isomorphic
    (p : ℕ) :
    IsIsomorphic
      (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K) ⋙
          Sheaf.Γ J AddCommGrpCat.{u}).rightDerived p)
      ((Sheaf.Γ K AddCommGrpCat.{u}).rightDerived p) := sorry

end DerivedGlobal

/-- Functor-level companion: inverse image identifies the degree-`p` global cohomology functor on
`Sh(D)` with the degree-`p` global cohomology functor on `Sh(C)`. -/
@[stacks 03YU]
theorem sheafPushforwardContinuous_globalCohomology_isomorphic
    (p : ℕ) :
    IsIsomorphic
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K) ⋙ Sheaf.cohomologyFunctor J p)
      (Sheaf.cohomologyFunctor K p) := sorry

/-- Lemma 21.7.2 (4): for any abelian sheaf `F` on `D`, inverse image identifies the degree-`p`
global cohomology of `F` on `D` with the degree-`p` global cohomology of `g⁻¹F` on `C`. -/
@[stacks 03YU]
theorem sheafPushforwardContinuous_globalCohomology_obj_isomorphic
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor J p).obj
        ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F))
      ((Sheaf.cohomologyFunctor K p).obj F) := sorry

end Global

end Sheaf
end CategoryTheory
