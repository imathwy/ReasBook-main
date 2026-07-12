import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Shift.Quotient
import Mathlib.CategoryTheory.Triangulated.Functor
import StacksProject_2024.Chap21.Definition_21_17_13_Core

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory
universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Domain-style sampling for Definition 21.17.13:
- primary domain: fixed-right-factor tensoring on the homotopy category of sheaves of modules on a
  ringed site and its total left derived functor on `D(𝒪)`;
- sampled owner declarations:
  `derivedTensorProduct`,
  `derivedTensorSourceFunctorOfComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.CommShift`,
  `NatTrans.CommShift`,
  `Functor.totalLeftDerived`,
  `Functor.IsTriangulated`;
- best owner abstraction: the primitive tensor owner data already live in
  `Definition_21_17_13_Core`; this file is the thin derived-API layer whose public surface keeps
  the canonical `CommShift`, counit `NatTrans.CommShift`, and triangulated-exactness companions on
  the owner `derivedTensorProduct`, while the source-functor shift scaffolding stays internal;
- primitive vs derived: the primitive data are the fixed-right-factor source functor, its chosen
  representative, and the owner `derivedTensorProduct`; the derived API here is the owner-level
  shift and exactness companion surface on `derivedTensorProduct`, with private source-level
  shift-compatibility scaffolding used only to support those statements.

Source/core/bridge triage:
- `source-facing`: exactness of `- ⊗^L F` on `D(𝒪)`;
- `core/canonical`: `derivedTensorProduct`, `Functor.totalLeftDerived`,
  `Functor.mapHomotopyCategory`, `Functor.CommShift`, `NatTrans.CommShift`, and
  `Functor.IsTriangulated`;
- `bridge/view`: the only local work should be thin `simpa` bridges from the canonical
  `mapHomotopyCategory` and `totalLeftDerived` exactness owners to the Chapter 21 tensor owners,
  while keeping the shift-comparison constructions internal. -/

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod
local notation "Complexes" => CochainComplex Mod ℤ
local notation "KMod" => HomotopyCategory Mod (up ℤ)
local notation "Q" => (HomotopyCategory.quotient Mod (up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso Mod (up ℤ)

private noncomputable instance derivedTensorSourceFunctorOfComplex_commShift
    (K : Complexes) :
    (derivedTensorSourceFunctorOfComplex K).CommShift ℤ := by
  let F : Complexes ⥤ KMod :=
    (((curriedTensor Mod).map₂CochainComplex).flip.obj K) ⋙ Q
  let _ : F.CommShift ℤ := by
    infer_instance
  change
    ((CategoryTheory.Quotient.lift
      (homotopic Mod (up ℤ))
      F
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 K)
            (curriedTensor Mod)
            (up ℤ)))) ⋙ Qh).CommShift ℤ
  infer_instance

/-- The homotopy-category source functor underlying `derivedTensorProduct F` commutes with the
triangulated shift. -/
private noncomputable instance derivedTensorSourceFunctor_commShift
    (F : DMod) :
    (derivedTensorSourceFunctor F).CommShift ℤ := by
  simpa [derivedTensorSourceFunctor] using
    (derivedTensorSourceFunctorOfComplex_commShift
      ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage F))

/-- The derived tensor product endofunctor `- ⊗^L F` commutes with shifts. -/
@[stacks 06YU] noncomputable instance derivedTensorProduct_commShift
    (F : DMod) :
    (derivedTensorProduct F).CommShift ℤ := by
  -- Route correction: the total left derived owner already knows how shift compatibility
  -- propagates from the source functor, so no custom shifted-counit data are needed here.
  change ((derivedTensorSourceFunctor F).totalLeftDerived Qh Qis).CommShift ℤ
  -- The generic `totalLeftDerived` instance supplies the derived shift compatibility.
  infer_instance

/-- The canonical counit `Qh ⋙ derivedTensorProduct F ⟶ derivedTensorSourceFunctor F` commutes
with shifts. -/
@[stacks 06YU] noncomputable instance derivedTensorProductCounit_commShift
    (F : DMod) :
    NatTrans.CommShift (derivedTensorProductCounit F) ℤ := by
  -- Route correction: recall the canonical total-left-derived counit instead of proving
  -- shift compatibility for a chapter-local counit wrapper by hand.
  change NatTrans.CommShift
    ((derivedTensorSourceFunctor F).totalLeftDerivedCounit Qh Qis) ℤ
  -- This compatibility is part of the standard `totalLeftDerivedCounit` API.
  infer_instance

/-- Definition 21.17.13: for a fixed right factor `F` in `D(𝒪)`, the derived tensor product
functor `- ⊗^L F` is exact in the triangulated sense. -/
@[stacks 06YU, instance] theorem derivedTensorProduct_isTriangulated (F : DMod) :
    (derivedTensorProduct F).IsTriangulated := by
  -- Route correction: exactness is inherited from the canonical total left derived functor,
  -- so the proof should normalize to that owner rather than redoing `map_distinguished`.
  change ((derivedTensorSourceFunctor F).totalLeftDerived Qh Qis).IsTriangulated
  -- Once normalized, the triangulated structure is provided by the generic derived-functor API.
  infer_instance

end

end SheafOfModules.RingedSite
