import Mathlib
import StacksProject_2024.Chap15.Definition_15_32_1
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap20.IdealSheafStalkIdeal
import StacksProject_2024.Chap18.IdealSectionIdeal
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open RingTheory
open RingTheory.Sequence
open SheafOfModules.RingedSite (idealSectionIdeal)
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

-- The sectionwise ideal owner `idealSectionIdeal` is canonical in
-- `SheafOfModules.RingedSite`, and Chapter 20 already exports the stalk ideal owner
-- `idealSheafStalkIdeal`. This file reuses those owners and adds the support companion and the
-- source-facing local-generation predicate used throughout Section 31.20.

/-- Helper predicate: the support of `\mathcal O_X / \mathcal I`, expressed stalkwise as the set
of points where the stalk ideal `\mathcal I_x` is proper. -/
def idealQuotientSupport (I : Subobject 𝒪X) : Set X :=
  moduleSupport (cokernel (I.arrow : (I : ModX) ⟶ 𝒪X))

/-- `idealQuotientSupport I` is the canonical module support of the quotient `\mathcal O_X /
\mathcal I`. -/
theorem idealQuotientSupport_eq_moduleSupport_cokernel
    (I : Subobject 𝒪X) :
    idealQuotientSupport I = moduleSupport (cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)) :=
  rfl

/-- Membership in `idealQuotientSupport I` means exactly that the stalk ideal `\mathcal I_x` is
proper. -/
theorem mem_idealQuotientSupport
    (I : Subobject 𝒪X) (x : X) :
    x ∈ idealQuotientSupport I ↔ idealSheafStalkIdeal I x ≠ ⊤ :=
  sorry

/-- A local section of the ideal sheaf determines a local section of the ambient structure sheaf.
-/
def idealSectionToRingSection
    (I : Subobject 𝒪X) (U : Opens X)
    (s : (I : ModX).val.obj (op U)) :
    X.presheaf.obj (op U) :=
  let iArrow := I.arrow.val
  SheafOfModules.unitSectionToRingSection U ((iArrow.app (op U)) s)

/-- Companion expansion for `idealSectionToRingSection`. -/
theorem idealSectionToRingSection_def
    (I : Subobject 𝒪X) (U : Opens X)
    (s : (I : ModX).val.obj (op U)) :
    idealSectionToRingSection I U s =
      let iArrow := I.arrow.val
      SheafOfModules.unitSectionToRingSection U ((iArrow.app (op U)) s) :=
  rfl

/-- Passing from ideal-sheaf sections to ambient ring sections commutes with restriction. -/
theorem idealSectionToRingSection_restrict
    (I : Subobject 𝒪X) {U V : Opens X} (i : V ⟶ U)
    (s : (I : ModX).val.obj (op U)) :
    X.presheaf.map i.op (idealSectionToRingSection I U s) =
      idealSectionToRingSection I V (((I : ModX).val.map i.op).hom s) := by
  sorry

/-- Helper predicate: `I` is generated on `U` by the finite family `f` of ideal-sheaf sections
when, on every smaller open `V ⟶ U`, the section ideal cut out by `I` equals the ideal generated
by the restricted ideal-sheaf sections induced by `f`, viewed in the ambient ring. -/
def IsGeneratedByIdealSectionFamilyOn
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U)) : Prop :=
  ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
    idealSectionIdeal I (op V) =
      Ideal.span (Set.range fun j : Fin r ↦
        idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)))

/-- Companion expansion for `IsGeneratedByIdealSectionFamilyOn`. -/
theorem isGeneratedByIdealSectionFamilyOn_iff
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U)) :
    IsGeneratedByIdealSectionFamilyOn I U f ↔
      ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
        idealSectionIdeal I (op V) =
          Ideal.span (Set.range fun j : Fin r ↦
            idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j))) :=
  Iff.rfl

/-- A finite family of local ideal-sheaf sections generates `I` on `U` exactly when the
corresponding restricted ambient ring sections induce generators on every smaller open. -/
theorem isGeneratedByIdealSectionFamilyOn_idealSectionToRingSection_iff
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U)) :
    IsGeneratedByIdealSectionFamilyOn I U f ↔
      ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
        idealSectionIdeal I (op V) =
          Ideal.span (Set.range fun j : Fin r ↦
            X.presheaf.map i.op (idealSectionToRingSection I U (f j))) := by
  constructor <;> intro h <;> intro V i
  · simpa [idealSectionToRingSection_restrict] using h i
  · simpa [idealSectionToRingSection_restrict] using h i

/-- Helper predicate: `I` is locally generated near the support of `\mathcal O_X / \mathcal I`
by finite families satisfying the sequence condition `P`. -/
private def LocallyGeneratedBySequencePredicate
    (I : Subobject 𝒪X)
    (P : ∀ {U : Opens X} {r : ℕ}, (Fin r → X.presheaf.obj (op U)) → Prop) : Prop :=
  ∀ x ∈ idealQuotientSupport I,
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
      P (fun j ↦ idealSectionToRingSection I U (f j)) ∧
        IsGeneratedByIdealSectionFamilyOn I U f

/-- Definition 31.20.2 (1): an ideal sheaf `\mathcal I ⊆ \mathcal O_X` on a ringed space is
regular if near every point of `\operatorname{Supp}(\mathcal O_X / \mathcal I)` it is generated by
a finite regular sequence of local sections. -/
@[stacks 063D]
def IsRegularIdealSheaf (I : Subobject 𝒪X) : Prop :=
  LocallyGeneratedBySequencePredicate I
    (fun {U _} f ↦ IsRegular (X.presheaf.obj (op U)) (List.ofFn f))

/-- The predicate `IsRegularIdealSheaf I` is exactly the local generation criterion by finite
regular sequences on neighborhoods of the support of `\mathcal O_X / \mathcal I`. -/
theorem isRegularIdealSheaf_iff (I : Subobject 𝒪X) :
    IsRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          IsRegular (X.presheaf.obj (op U))
            (List.ofFn fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  Iff.rfl

/-- Definition 31.20.2 (2): an ideal sheaf `\mathcal I ⊆ \mathcal O_X` on a ringed space is
Koszul-regular if near every point of `\operatorname{Supp}(\mathcal O_X / \mathcal I)` it is
generated by a finite Koszul-regular sequence of local sections. -/
@[stacks 063D]
def IsKoszulRegularIdealSheaf (I : Subobject 𝒪X) : Prop :=
  LocallyGeneratedBySequencePredicate I
    (fun {_ _} f ↦ IsKoszulRegularSequence f)

/-- The predicate `IsKoszulRegularIdealSheaf I` is exactly the local generation criterion by
finite Koszul-regular sequences on neighborhoods of the support of `\mathcal O_X / \mathcal I`.
-/
theorem isKoszulRegularIdealSheaf_iff (I : Subobject 𝒪X) :
    IsKoszulRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          IsKoszulRegularSequence (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  Iff.rfl

/-- Definition 31.20.2 (3): an ideal sheaf `\mathcal I ⊆ \mathcal O_X` on a ringed space is
`H_1`-regular if near every point of `\operatorname{Supp}(\mathcal O_X / \mathcal I)` it is
generated by a finite `H_1`-regular sequence of local sections. -/
@[stacks 063D]
def IsH1RegularIdealSheaf (I : Subobject 𝒪X) : Prop :=
  LocallyGeneratedBySequencePredicate I
    (fun {_ _} f ↦ IsH1RegularSequence f)

/-- The predicate `IsH1RegularIdealSheaf I` is exactly the local generation criterion by finite
`H_1`-regular sequences on neighborhoods of the support of `\mathcal O_X / \mathcal I`. -/
theorem isH1RegularIdealSheaf_iff (I : Subobject 𝒪X) :
    IsH1RegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          IsH1RegularSequence (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  Iff.rfl

/-- Definition 31.20.2 (4): an ideal sheaf `\mathcal I ⊆ \mathcal O_X` on a ringed space is
quasi-regular if near every point of `\operatorname{Supp}(\mathcal O_X / \mathcal I)` it is
generated by a finite quasi-regular sequence of local sections. -/
@[stacks 063D]
def IsQuasiRegularIdealSheaf (I : Subobject 𝒪X) : Prop :=
  LocallyGeneratedBySequencePredicate I
    (fun {U _} f ↦ IsQuasiRegular (X.presheaf.obj (op U)) (List.ofFn f))

/-- The predicate `IsQuasiRegularIdealSheaf I` is exactly the local generation criterion by finite
quasi-regular sequences on neighborhoods of the support of `\mathcal O_X / \mathcal I`. -/
theorem isQuasiRegularIdealSheaf_iff (I : Subobject 𝒪X) :
    IsQuasiRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          IsQuasiRegular (X.presheaf.obj (op U))
            (List.ofFn fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace
