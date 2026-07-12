import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1.PositiveConeBridge
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.ReductionProjectiveClassBridge
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.ProjectivePositiveReflection
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.PositiveGeneration

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

omit [HenselianLocalRing A] in
/-- Helper for Exercise 16-16.3-8: positive decomposition surjectivity over a finite witness
field supplies positive columns over that witness for any family of residue-field classes. -/
theorem conditionRPositiveColumnsForResidueFamily
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    (hdecomp :
      decompositionHom A' K' G '' R⁺[K'](G) =
        R⁺[IsLocalRing.ResidueField A'](G))
    {ι : Type*} (π : ι → FDRep k G) :
    ∃ z : ι → R₀[K'](G),
      (∀ i, z i ∈ R⁺[K'](G)) ∧
        ∀ i,
          decompositionHom A' K' G (z i) =
            finiteRepGrothendieckScalarExtensionHom
              k (IsLocalRing.ResidueField A') G [π i]₀ := by
  classical
  -- Each scalar-extended residue class is positive, hence has a positive preimage by `hdecomp`.
  have hcolumns :
      ∀ i, ∃ z : R₀[K'](G),
        z ∈ R⁺[K'](G) ∧
          decompositionHom A' K' G z =
            finiteRepGrothendieckScalarExtensionHom
              k (IsLocalRing.ResidueField A') G [π i]₀ := by
    intro i
    have hpositive :
        finiteRepGrothendieckScalarExtensionHom
            k (IsLocalRing.ResidueField A') G [π i]₀ ∈
          R⁺[IsLocalRing.ResidueField A'](G) := by
      refine (mem_finiteRepPositiveSubset_iff
        (K := IsLocalRing.ResidueField A') (G := G)).2 ?_
      let V' : FDRep (IsLocalRing.ResidueField A') G :=
        @FDRep.scalarExtension (IsLocalRing.ResidueField A') inferInstance
          k inferInstance inferInstance G inferInstance (π i)
      refine ⟨V', ?_⟩
      exact (finiteRepGrothendieckScalarExtensionHom_class_eq
        k (IsLocalRing.ResidueField A') G (π i)).symm
    have himage :
        finiteRepGrothendieckScalarExtensionHom
            k (IsLocalRing.ResidueField A') G [π i]₀ ∈
          decompositionHom A' K' G '' R⁺[K'](G) := by
      rw [hdecomp]
      exact hpositive
    rcases himage with ⟨z, hzpositive, hzdecomp⟩
    exact ⟨z, hzpositive, hzdecomp⟩
  choose z hzpositive hzdecomp using hcolumns
  -- Package the pointwise witnesses as the column family used by the coordinate argument.
  exact ⟨z, hzpositive, hzdecomp⟩

end

end Representation
