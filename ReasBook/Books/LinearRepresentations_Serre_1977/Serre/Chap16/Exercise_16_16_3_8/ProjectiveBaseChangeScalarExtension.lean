import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1.PositiveConeBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ReductionProjectiveClassBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ProjectivePositiveReflection
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.PositiveGeneration

noncomputable section

universe u v

open CategoryTheory
open scoped Representation ZeroObject

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-- Helper for Exercise 16-16.3-8: scalar extension of an actual projective base-change class
from `K` to `K'` agrees with direct base change from `A` to `K'`. -/
theorem finiteRepScalarExtension_projectiveClass_eq_direct_e16338
    {K' : Type u} [Field K'] [Algebra A K'] [Algebra K K']
    [IsScalarTower A K K']
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    finiteRepGrothendieckScalarExtensionHom K K' G [P.scalarExtension K]₀ =
      [P.scalarExtension K']₀ := by
  -- Reassociate the iterated tensor product and collapse the redundant middle `K`-factor.
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk
    ((TensorProduct.AlgebraTensorModule.assoc A K K' K' K P.V).symm.trans
      (TensorProduct.AlgebraTensorModule.congr
        (TensorProduct.AlgebraTensorModule.rid K K' K')
        (LinearEquiv.refl A P.V))) ?_
  intro g
  ext x
  rfl

/-- Helper for Exercise 16-16.3-8: finite scalar extension after projective base change is the
same additive homomorphism as direct projective base change to the larger field. -/
theorem finiteRepScalarExtension_comp_projectiveBaseChangeHom_eq_direct
    {K' : Type u} [Field K'] [Algebra A K'] [Algebra K K']
    [IsScalarTower A K K'] :
    (finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) =
        projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' := by
  -- Compare on projective generators and descend through the projective Grothendieck quotient.
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp [projectiveGrothendieckBaseChangeHom]
  · intro P
    simp [projectiveGrothendieckBaseChangeHom,
      finiteRepScalarExtension_projectiveClass_eq_direct_e16338
        (K := K) (K' := K') (G := G) P]
  · intro y' hy'
    simpa using congrArg Neg.neg hy'
  · intro y₁ y₂ hy₁ hy₂
    simp [map_add, hy₁, hy₂]

end

end Representation
