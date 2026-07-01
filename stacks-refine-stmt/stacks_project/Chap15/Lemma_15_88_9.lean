import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import stacks_project.Chap15.Lemma_15_58_1
import stacks_project.Chap15.Lemma_15_88_1_Core

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open BraidedCategory
open HomologicalComplex
open HomotopyCategory

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)
local notation "KModSeq" => HomotopyCategory (SeqRingMod A ρ) (up ℤ)
local notation "Qh" => (DerivedCategory.Qh : KModSeq ⥤ DModSeq)
local notation "Qis" => HomotopyCategory.quasiIso (SeqRingMod A ρ) (up ℤ)
local notation "CpxSeq" => CochainComplex (SeqRingMod A ρ) ℤ

attribute [local instance] seqRingMod_abelian seqRingMod_categoryWithHomology

variable [HasBinaryBiproducts (SeqRingMod A ρ)]
variable [HasZeroObject (SeqRingMod A ρ)]
variable [MonoidalCategory (SeqRingMod A ρ)] [SymmetricCategory (SeqRingMod A ρ)]
variable [(curriedTensor (SeqRingMod A ρ)).Additive]
variable [∀ X : SeqRingMod A ρ, ((curriedTensor (SeqRingMod A ρ)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (SeqRingMod A ρ), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : SeqRingMod A ρ,
  PreservesColimit (Functor.empty.{0} (SeqRingMod A ρ)) ((curriedTensor (SeqRingMod A ρ)).obj X)]
variable [∀ X : SeqRingMod A ρ,
  PreservesColimit (Functor.empty.{0} (SeqRingMod A ρ)) ((curriedTensor (SeqRingMod A ρ)).flip.obj X)]

/-
Domain-style sampling for Lemma 15.88.9:
- primary domain: the canonical derived tensor product on
  `D(SeqRingMod A ρ) = D(\mathrm{Mod}(\mathbf N, (A_n)))`;
- sampled owner declarations:
  `cochainComplexSymmetricCategory`,
  `LocalizedMonoidal`,
  `CategoryTheory.LocalizedMonoidal`,
  `BraidedCategory.braiding`,
  `MonoidalCategory.tensorLeft`,
  `MonoidalCategory.tensorRight`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owner is the tensor object `K ⊗ L` on
  `D(Mod(\mathbf N, (A_n)))`, coming from the localized symmetric monoidal structure on the
  derived category itself, and its owner is the symmetric monoidal tensor on `SeqRingMod A ρ`
  together with the canonical Chapter 15 symmetric monoidal structure on cochain complexes and
  the localization to homotopy and derived categories; the exactness statements belong to the
  canonical owners `tensorLeft L` and `tensorRight L`;
- primitive data: the symmetric monoidal tensor on `SeqRingMod A ρ` and the standard Chapter 15
  tensor closure on `CochainComplex (SeqRingMod A ρ) ℤ`;
- derived API: the induced symmetric monoidal structures on `K(Mod(\mathbf N, (A_n)))` and
  `D(Mod(\mathbf N, (A_n)))`, symmetry via the braiding `β_ K L`, and the owner-level
  `CommShift` / `IsTriangulated` structures on left and right tensoring.

Source/core/bridge triage:
- `source-facing`: the canonical derived tensor product on `D(Mod(\mathbf N, (A_n)))`, its
  symmetry, and its exactness in each variable;
- `core/canonical`: the symmetric monoidal tensor on `SeqRingMod A ρ`, the Chapter 15 symmetric
  monoidal structure on `CochainComplex (SeqRingMod A ρ) ℤ`, and the localized symmetric
  monoidal structures on `HomotopyCategory (SeqRingMod A ρ) (up ℤ)` and
  `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: none in this file.
-/

namespace SequentialRingedModules

local instance : Abelian (SeqRingMod A ρ) := seqRingMod_abelian A ρ

local instance : Preadditive (SeqRingMod A ρ) := inferInstance

local instance : CategoryWithHomology (SeqRingMod A ρ) := inferInstance

private abbrev homotopyQuotient :
    CpxSeq ⥤ KModSeq :=
  HomotopyCategory.quotient (SeqRingMod A ρ) (up ℤ)

private abbrev homotopyEquivalences :
    MorphismProperty CpxSeq :=
  HomologicalComplex.homotopyEquivalences (SeqRingMod A ρ) (up ℤ)

private abbrev homotopyQuasiIso :
    MorphismProperty KModSeq :=
  Qis

private noncomputable abbrev homotopyQuotientUnitIso :
    (homotopyQuotient : CpxSeq ⥤ KModSeq).obj (MonoidalCategoryStruct.tensorUnit CpxSeq) ≅
      (homotopyQuotient : CpxSeq ⥤ KModSeq).obj (MonoidalCategoryStruct.tensorUnit CpxSeq) :=
  Iso.refl _

local instance :
    Functor.IsLocalization
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq) :=
  (ComplexShape.up ℤ).quotient_isLocalization (fun n ↦ ⟨n - 1, by simp⟩) (SeqRingMod A ρ)

/-- Homotopy equivalences of cochain complexes of sequential ringed modules are stable under the
totalized tensor product. -/
private theorem homotopyEquivalences_isMonoidal :
    (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal := by
  sorry

/-- The homotopy category `K(\mathrm{Mod}(\mathbf N, (A_n)))` inherits its monoidal structure by
localizing the totalized tensor product on cochain complexes of sequential ringed modules along
homotopy equivalences. -/
noncomputable instance : MonoidalCategory KModSeq := by
  let _ : SymmetricCategory CpxSeq := inferInstance
  let _ : (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal :=
    homotopyEquivalences_isMonoidal
  change MonoidalCategory
    (LocalizedMonoidal
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq)
      homotopyQuotientUnitIso)
  infer_instance

/-- The homotopy category `K(\mathrm{Mod}(\mathbf N, (A_n)))` inherits the symmetric monoidal
structure induced from cochain complexes of sequential ringed modules. -/
noncomputable instance : SymmetricCategory KModSeq := by
  let _ : SymmetricCategory CpxSeq := inferInstance
  let _ : (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal :=
    homotopyEquivalences_isMonoidal
  change SymmetricCategory
    (LocalizedMonoidal
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq)
      homotopyQuotientUnitIso)
  infer_instance

/-- Quasi-isomorphisms in the homotopy category of sequential ringed modules are stable under the
tensor product coming from the sequential-module tensor on `SeqRingMod A ρ`. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal := by
  sorry

/-- The monoidal structure on `D(\mathrm{Mod}(\mathbf N, (A_n)))` obtained by localizing the
tensor product on the homotopy category of complexes of sequential ringed modules. -/
noncomputable instance : MonoidalCategory DModSeq := by
  let _ : (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : MonoidalCategory
      (LocalizedMonoidal
      Qh
      (homotopyQuasiIso : MorphismProperty KModSeq)
      (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KModSeq)))))

/-- The derived category `D(\mathrm{Mod}(\mathbf N, (A_n)))` inherits the symmetric monoidal
structure obtained by localizing the symmetric tensor product on the homotopy category. -/
noncomputable instance : SymmetricCategory DModSeq := by
  let _ : (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : SymmetricCategory
      (LocalizedMonoidal
      Qh
      (homotopyQuasiIso : MorphismProperty KModSeq)
      (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KModSeq)))))

/- Lemma 15.88.9: the canonical derived tensor product on
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is symmetric, via the owner braiding `β_`. -/
#check (β_ : ∀ K L : DModSeq, K ⊗ L ≅ L ⊗ K)

/- Lemma 15.88.9: tensoring on the left by a fixed object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is exact in the triangulated sense, through the owner
structures on `tensorLeft L`. -/
noncomputable instance (L : DModSeq) :
    (tensorLeft L : DModSeq ⥤ DModSeq).CommShift ℤ := by
  sorry

instance (L : DModSeq) :
    (tensorLeft L : DModSeq ⥤ DModSeq).IsTriangulated := by
  sorry

/- Lemma 15.88.9: tensoring on the right by a fixed object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is exact in the triangulated sense, through the owner
structures on `tensorRight L`. -/
noncomputable instance (L : DModSeq) :
    (tensorRight L : DModSeq ⥤ DModSeq).CommShift ℤ := by
  sorry

instance (L : DModSeq) :
    (tensorRight L : DModSeq ⥤ DModSeq).IsTriangulated := by
  sorry

end SequentialRingedModules

end
