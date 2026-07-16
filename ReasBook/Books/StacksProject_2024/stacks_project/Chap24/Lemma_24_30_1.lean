import StacksProject_2024.stacks_project.Chap13.Lemma_13_7_2
import StacksProject_2024.stacks_project.Chap24.Definition_24_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA uB vA vB

-- Semantic search note: the `lean_leansearch` tool was unavailable in this runner, so the
-- owner/API choice was checked against local derived-functor precedents `Lemma_24_28_4`,
-- `Definition_24_29_2`, and the adjunction equivalence criterion `Lemma_13_7_2`. The Chapter 24
-- DG-algebra owner files currently fail to compile in this workspace, so this item is formalized
-- through the underlying cochain map on module sheaves over the ringed site.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA]
variable [Abelian DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB]
variable [Abelian DGModB]
local notation "DA" => DerivedCategory DGModA
local notation "DB" => DerivedCategory DGModB
variable (tensorWithBimodule : DGModA ⥤ DGModB)
variable (restriction : DB ⥤ DA)
variable [tensorWithBimodule.Additive]
variable [Functor.HasLeftDerivedFunctor
  (pullbackTensorToDerived (𝟭 DGModA) tensorWithBimodule)
  (HomotopyCategory.quasiIso DGModA (up ℤ))]
local notation "LT" => derivedTensorProduct tensorWithBimodule

/-- For the chosen derived extension/restriction adjunction of Lemma `24.30.1`, if the unit is an
isomorphism on every source object and the derived restriction functor has zero kernel, then the
source-facing derived tensor functor is essentially surjective. This is the canonical
adjunction-owner bridge used by the final equivalence statement. -/
theorem derivedTensorProduct_essSurj_of_unit_isIso_of_kernel_le_isZero
    (adj : LT ⊣ restriction)
    (hunit : ∀ M : DA, IsIso (adj.unit.app M))
    (hkernel : restriction.kernel ≤ IsZero) :
    Functor.EssSurj LT := by
  letI : LT.CommShift ℤ := adj.leftAdjointCommShift ℤ
  letI (M : DA) : IsIso (adj.unit.app M) := hunit M
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  letI : LT.FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  exact Adjunction.essSurj_of_kernel_le_isZero adj hkernel

/-- Lemma 24.30.1: for a chosen derived extension/restriction adjunction between differential
graded module categories, if the unit is an isomorphism on every object and the chosen derived
restriction functor has zero kernel, then the source-facing Chapter 24 derived tensor functor is
an equivalence of categories. This keeps `derivedTensorProduct` as the source-facing owner while
delegating the fully-faithful and zero-kernel hypotheses to the canonical adjunction-owner
equivalence criterion of `Chap13.Lemma_13_7_2`; the previous theorem records the intermediate
owner-level `EssSurj` bridge. -/
@[stacks 0FTZ]
theorem derivedTensorProduct_isEquivalence_of_unit_isIso_of_kernel_le_isZero
    (adj : LT ⊣ restriction)
    (hunit : ∀ M : DA, IsIso (adj.unit.app M))
    (hkernel : restriction.kernel ≤ IsZero) :
    Functor.IsEquivalence LT := by
  letI : LT.CommShift ℤ := adj.leftAdjointCommShift ℤ
  letI (M : DA) : IsIso (adj.unit.app M) := hunit M
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  letI : LT.FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  exact Adjunction.isEquivalence_of_fullyFaithful_of_kernel_le_isZero adj hkernel

end

end DifferentialGradedModule
