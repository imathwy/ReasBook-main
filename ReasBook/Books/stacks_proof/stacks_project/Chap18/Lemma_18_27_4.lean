import Mathlib
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v u₁ v₁

namespace CategoryTheory

namespace ParametrizedAdjunction

open Opposite

/-- Helper for Lemma 18.27.4: a parametrized right adjoint preserves the limit of an opposite
diagram once the corresponding left-variable tensor functors preserve the dual colimit. -/
private theorem preservesLimit_flip_obj
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj₂ : F ⊣₂ G)
    {J : Type*} [Category* J] (P : J ⥤ C₁ᵒᵖ)
    [∀ X₂ : C₂, PreservesColimit P.leftOp (F.flip.obj X₂)] (X₃ : C₃) :
    PreservesLimit P (G.flip.obj X₃) where
  preserves {c} hc := by
    -- Follow the source proof: convert a cone over the right-adjoint diagram into a cocone over
    -- the left-adjoint diagram, use colimit preservation there, and transpose the universal map
    -- back through the parametrized Hom-equivalence.
    let cocone (s : Cone (P ⋙ G.flip.obj X₃)) :
        Cocone (P.leftOp ⋙ F.flip.obj s.pt) :=
      { pt := X₃
        ι.app j := adj₂.homEquiv.symm (s.π.app (unop j))
        ι.naturality j j' f := by
          simpa [← s.w f.unop] using
            (adj₂.homEquiv_symm_naturality_one
              (f₁ := (P.map f.unop).unop) (g := s.π.app (unop j'))).symm }
    let hc' (s : Cone (P ⋙ G.flip.obj X₃)) :=
      isColimitOfPreserves (F.flip.obj s.pt) (isColimitCoconeLeftOpOfCone _ hc)
    -- The desired lift is the transpose of the colimit-descending morphism from the induced
    -- cocone, and the factorization/uniqueness are checked after undoing that transpose.
    exact ⟨{
      lift s := adj₂.homEquiv ((hc' s).desc (cocone s))
      fac s j := by
        have hfac :
            (F.map (c.π.app j).unop).app s.pt ≫ (hc' s).desc (cocone s) =
              adj₂.homEquiv.symm (s.π.app j) := by
          simpa [cocone, coconeLeftOpOfCone_ι_app] using
            (hc' s).fac (cocone s) (op j)
        have h₁ :
            adj₂.homEquiv ((hc' s).desc (cocone s)) ≫ ((G.flip.obj X₃).mapCone c).π.app j =
              adj₂.homEquiv
                ((F.map (c.π.app j).unop).app s.pt ≫ (hc' s).desc (cocone s)) := by
          simpa using
            (adj₂.homEquiv_naturality_one (f₁ := (c.π.app j).unop)
              (g := (hc' s).desc (cocone s))).symm
        have h₂ :
            adj₂.homEquiv
                ((F.map (c.π.app j).unop).app s.pt ≫ (hc' s).desc (cocone s)) =
              adj₂.homEquiv (adj₂.homEquiv.symm (s.π.app j)) :=
          congrArg adj₂.homEquiv hfac
        exact h₁.trans (h₂.trans (adj₂.homEquiv.apply_symm_apply (s.π.app j)))
      uniq s m hm := adj₂.homEquiv.symm.injective (by
        simp only [op_unop, Equiv.symm_apply_apply]
        refine (hc' s).uniq (cocone s) _ (fun j ↦ ?_)
        simpa [cocone, ← hm] using
          (adj₂.homEquiv_symm_naturality_one
            (f₁ := (c.π.app j.unop).unop) (g := m)).symm) }⟩

/-- Helper for Lemma 18.27.4: the previous pointwise limit-preservation result upgrades to all
limits of a fixed shape. -/
private theorem preservesLimitsOfShape_flip_obj
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj₂ : F ⊣₂ G)
    {J : Type*} [Category* J]
    [∀ X₂ : C₂, PreservesColimitsOfShape Jᵒᵖ (F.flip.obj X₂)] (X₃ : C₃) :
    PreservesLimitsOfShape J (G.flip.obj X₃) where
  -- Once each shape-`Jᵒᵖ` colimit is preserved on the left side, the pointwise argument applies to
  -- every `J`-shaped limit cone on the right side.
  preservesLimit {K} := preservesLimit_flip_obj (adj₂ := adj₂) (P := K) X₃

end ParametrizedAdjunction

/- Domain-style sampling for Lemma 18.27.4:
- primary domain: internal Hom in monoidal closed categories of presheaves and sheaves of modules
  over commutative ring objects;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`;
- best owner abstraction:
  `ihom` for the target-variable internal Hom, and
  `((MonoidalClosed.internalHom).flip.obj 𝒢)` for the source-variable contravariant internal Hom;
- primitive data:
  a monoidal closed module category together with a fixed module object;
- derived API:
  preservation of limits by `ihom ℱ`, and preservation of limits by the contravariant
  source-variable owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the four Stacks clauses asserting that internal Hom preserves limits in the
  target variable and sends colimits in the source variable to limits;
- `core/canonical`: `ihom`, `ihom.adjunction`, `MonoidalClosed.internalHom`, and
  `MonoidalClosed.internalHomAdjunction₂`;
- `bridge/view`: the braided transport from the parametrized owner
  `MonoidalClosed.internalHomAdjunction₂` to the source-variable contravariant owner
  `((MonoidalClosed.internalHom).flip.obj 𝒢)`.

The target-variable clauses are exact uses of the owner theorem
`Adjunction.rightAdjoint_preservesLimits`, so they should appear only as direct canonical use. In
the active mathlib version for this workspace, the source-variable clauses still need a thin
braided bridge from `MonoidalClosed.internalHomAdjunction₂` to the actual contravariant
internal-Hom owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`, so this file exposes that
owner-level limit-preservation theorem once and then specializes it to the presheaf and ringed-site
module categories below.
-/

namespace MonoidalClosed

/-- Helper for Lemma 18.27.4: in a braided monoidal closed category, tensoring on the right by a
fixed object preserves colimits because braiding identifies it with the left adjoint
`tensorLeft`. -/
private theorem tensorRight_preservesColimitsOfShape
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalClosed A] {I : Type u₁} [Category.{v₁} I] (X : A) :
    PreservesColimitsOfShape I (MonoidalCategory.tensorRight X : A ⥤ A) := by
  -- The source proof uses restriction functors that are both left and right adjoints; here the
  -- braided analogue is that `tensorRight X` is isomorphic to the left adjoint `tensorLeft X`.
  letI : (MonoidalCategory.tensorRight X : A ⥤ A).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)
  infer_instance

/-- In a braided monoidal closed category, fixing the target of internal Hom yields a
contravariant functor `Cᵒᵖ ⥤ C` that preserves limits. Equivalently, the source-variable internal
Hom functor sends colimits to limits. -/
theorem preservesLimitsOfShape_internalHom_flip_obj
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalClosed A] {I : Type u₁} [Category.{v₁} I] (G : A) :
    PreservesLimitsOfShape I ((MonoidalClosed.internalHom).flip.obj G : Aᵒᵖ ⥤ A) := by
  -- Route correction: the owner theorem already exists at braided strength in mathlib, matching
  -- the source proof's use of the closed-category owner rather than a symmetry-specific bridge.
  -- We therefore invoke the canonical parametrized-adjunction limit-preservation theorem
  -- directly instead of rebuilding the braiding transport in this file.
  letI (X : A) :
      PreservesColimitsOfShape Iᵒᵖ ((MonoidalCategory.curriedTensor A).flip.obj X) := by
    simpa using (tensorRight_preservesColimitsOfShape (A := A) (I := Iᵒᵖ) X)
  simpa using
    (CategoryTheory.ParametrizedAdjunction.preservesLimitsOfShape_flip_obj
      (adj₂ := MonoidalClosed.internalHomAdjunction₂ (C := A)) (J := I) G)

end MonoidalClosed

section PresheafModulesTarget

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

local notation "PMod" => PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)

/- Lemma 18.27.4 (1): for a presheaf of commutative rings `𝒪` and a fixed presheaf module `ℱ`,
the target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
exactly the canonical right-adjoint preservation instance for `ihom ℱ`. -/
theorem presheafOfModules_preservesLimitsOfShape_ihom :
    PreservesLimitsOfShape I (ihom ℱ : PMod ⥤ PMod) := by
  letI := (ihom.adjunction ℱ).rightAdjoint_preservesLimits
  infer_instance

end PresheafModulesTarget

section PresheafModulesSource

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [BraidedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

local notation "PMod" => PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)
/- Lemma 18.27.4 (2): for a fixed presheaf module `𝒢`, the source-variable contravariant
internal-Hom functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner
`((MonoidalClosed.internalHom).flip.obj 𝒢)`, and it preserves limits. Equivalently, it sends
colimits in presheaf modules to limits. -/
theorem presheafOfModules_preservesLimitsOfShape_internalHom_flip_obj :
    PreservesLimitsOfShape I ((MonoidalClosed.internalHom).flip.obj 𝒢 : PModᵒᵖ ⥤ PMod) := by
  -- The source-facing presheaf statement is now exactly the braided owner theorem specialized to
  -- the presheaf-module monoidal closed category.
  simpa using
    (MonoidalClosed.preservesLimitsOfShape_internalHom_flip_obj
      (A := PMod) (I := I) 𝒢)

end PresheafModulesSource

section RingedSiteTarget

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable (ℱ : ringedSiteModuleCategory J 𝒪)

local notation "ModOJ" => ringedSiteModuleCategory J 𝒪

/- Lemma 18.27.4 (3): on a ringed site `(C, J, 𝒪)`, for a fixed sheaf module `ℱ`, the
target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
again the canonical right-adjoint preservation instance for `ihom ℱ`. -/
theorem ringedSiteModuleCategory_preservesLimitsOfShape_ihom :
    PreservesLimitsOfShape I (ihom ℱ : ModOJ ⥤ ModOJ) := by
  letI := (ihom.adjunction ℱ).rightAdjoint_preservesLimits
  infer_instance

end RingedSiteTarget

section RingedSiteSource

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable (𝒢 : ringedSiteModuleCategory J 𝒪)

local notation "ModOJ" => ringedSiteModuleCategory J 𝒪
/- Lemma 18.27.4 (4): for a fixed sheaf module `𝒢`, the source-variable contravariant internal-Hom
functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`, and
it preserves limits. Equivalently, it sends colimits in sheaves of modules to limits. -/
theorem ringedSiteModuleCategory_preservesLimitsOfShape_internalHom_flip_obj :
    PreservesLimitsOfShape I ((MonoidalClosed.internalHom).flip.obj 𝒢 : ModOJᵒᵖ ⥤ ModOJ) :=
  by
    -- The ringed-site source-variable clause is the same braided owner theorem, specialized to the
    -- sheaf-module monoidal closed category.
    simpa using
      (MonoidalClosed.preservesLimitsOfShape_internalHom_flip_obj
        (A := ModOJ) (I := I) 𝒢)

end RingedSiteSource

/-- Lemma 18.27.4: internal Hom commutes with arbitrary limits in the target variable and sends
arbitrary colimits in the source variable to limits, both for presheaves of modules over a
presheaf of rings and for sheaves of modules on a ringed site. The source-variable clauses are
expressed through the contravariant owner `internalHom.flip.obj`, so they appear as
limit-preservation statements on opposite-indexed diagrams. -/
@[stacks 03EN]
theorem internalHom_preserves_limits_and_source_colimits
    {C : Type u} [Category.{v} C]
    {I : Type u₁} [Category.{v₁} I]
    (𝒪P : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [MonoidalCategory (PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat))]
    [BraidedCategory (PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat))]
    [MonoidalClosed (PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat))]
    (ℱP 𝒢P : PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat))
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪S : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪S)]
    [BraidedCategory (ringedSiteModuleCategory J 𝒪S)]
    [MonoidalClosed (ringedSiteModuleCategory J 𝒪S)]
    (ℱS 𝒢S : ringedSiteModuleCategory J 𝒪S) :
    PreservesLimitsOfShape I
        (ihom ℱP :
          PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat) ⥤
            PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat)) ∧
      PreservesLimitsOfShape I
        ((MonoidalClosed.internalHom).flip.obj 𝒢P :
          (PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat))ᵒᵖ ⥤
            PresheafOfModules (𝒪P ⋙ forget₂ CommRingCat RingCat)) ∧
      PreservesLimitsOfShape I
        (ihom ℱS : ringedSiteModuleCategory J 𝒪S ⥤ ringedSiteModuleCategory J 𝒪S) ∧
      PreservesLimitsOfShape I
        ((MonoidalClosed.internalHom).flip.obj 𝒢S :
          (ringedSiteModuleCategory J 𝒪S)ᵒᵖ ⥤ ringedSiteModuleCategory J 𝒪S) := by
  constructor
  · exact presheafOfModules_preservesLimitsOfShape_ihom (I := I) 𝒪P ℱP
  · constructor
    · exact presheafOfModules_preservesLimitsOfShape_internalHom_flip_obj (I := I) 𝒪P 𝒢P
    · constructor
      · exact ringedSiteModuleCategory_preservesLimitsOfShape_ihom (I := I) J 𝒪S ℱS
      · exact
          ringedSiteModuleCategory_preservesLimitsOfShape_internalHom_flip_obj
            (I := I) J 𝒪S 𝒢S

end CategoryTheory
