import stacks_proof.stacks_project.Chap13.Proposition_13_38_2
import stacks_proof.stacks_project.Chap19.Lemma_19_15_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.IsGrothendieckAbelian

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{max u₁ v₁} A]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]
variable [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
variable [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
variable [Pretriangulated 𝒟] [IsTriangulated 𝒟]

attribute [local instance] HasDerivedCategory.standard

/-- A Grothendieck abelian category has arbitrary direct sums in its derived category. -/
local instance derivedCategory_hasCoproductsForProposition_19_15_2 :
    HasCoproducts.{max u₁ v₁} (DerivedCategory A) :=
  fun _ ↦ derivedCategory_hasCoproductsOfShape

/-
Domain-style sampling:
- primary domain: Brown representability and adjunctions of exact functors between triangulated
  categories;
- sampled owner declarations:
  `exactFunctor_isLeftAdjoint_of_isCompactlyGenerated`,
  `exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated`,
  `derivedCategory_isCompactlyGenerated`,
  `Adjunction.ofIsLeftAdjoint`;
- best owner abstraction: `F.IsLeftAdjoint` for
  `F : DerivedCategory A ⥤ 𝒟`, with the exactness of the chosen right adjoint expressed by the
  canonical owner `F.rightAdjoint.IsTriangulated`;
- primitive data: the functor `F` together with its exactness and preservation of arbitrary direct
  sums;
- derived API: the chosen adjunction `Adjunction.ofIsLeftAdjoint F`, its induced right-adjoint
  shift compatibility, and the theorem that `F.rightAdjoint` is exact.

Source/core/bridge triage:
- `source-facing`: the two theorems below specialized to `DerivedCategory A`;
- `core/canonical`: the Chapter 13 owner theorems
  `exactFunctor_isLeftAdjoint_of_isCompactlyGenerated` and
  `exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated`;
- `bridge/view`: `derivedCategory_isCompactlyGenerated`, which supplies the compact-generation
  hypothesis for the standard derived-category model of a Grothendieck abelian category.
-/

/-- An exact functor from the derived category of a Grothendieck abelian category to a
triangulated category that preserves arbitrary direct sums is a left adjoint. -/
theorem derivedCategory_exactFunctor_isLeftAdjoint
    (F : DerivedCategory A ⥤ 𝒟) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint := by
  exact CategoryTheory.exactFunctor_isLeftAdjoint_of_isCompactlyGenerated F

-- Proof sketch: apply the compact-generation owner theorem from Proposition `13.38.2` to the
-- derived category of `A` using Lemma `19.15.1`, then read exactness of the chosen right adjoint
-- through the canonical owner `F.rightAdjoint.IsTriangulated`.
/-- Proposition 19.15.2: an exact functor from the derived category of a Grothendieck abelian
category to a triangulated category that preserves arbitrary direct sums admits a right adjoint
which is again exact. -/
@[stacks 0F5Y]
theorem derivedCategory_exactFunctor_hasExactRightAdjoint
    (F : DerivedCategory A ⥤ 𝒟) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F] :
    letI := derivedCategory_exactFunctor_isLeftAdjoint F
    let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
    letI := adj.rightAdjointCommShift ℤ
    F.rightAdjoint.IsTriangulated := by
  simpa using
    (CategoryTheory.exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated F)

end CategoryTheory.IsGrothendieckAbelian
