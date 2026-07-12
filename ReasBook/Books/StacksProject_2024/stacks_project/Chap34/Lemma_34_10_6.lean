import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksProject_2024.Chap34.Definition_34_10_1

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- Lemma 34.10.6 (1): a finite affine family over an affine scheme is a standard V covering if
and only if it admits a refinement by a standard V covering. -/
theorem isStandardVCover_iff_exists_refinement (𝒰 : AffineFamilyOver T) :
    IsStandardVCover 𝒰 ↔
      ∃ (𝒱 : AffineFamilyOver T) (r : Refinement 𝒱 𝒰), IsStandardVCover 𝒱 := sorry

/-- Lemma 34.10.6 (2): a finite affine family over an affine scheme is a standard `V` covering if
and only if the single coproduct morphism `∐ Uⱼ ⟶ T` is valuatively standard. -/
theorem isStandardVCover_iff_coproductMap (𝒰 : AffineFamilyOver T) :
    IsStandardVCover 𝒰 ↔
      ValuativeCriterion.Existence (Sigma.desc 𝒰.map) := sorry

end AffineFamilyOver

end AlgebraicGeometry
