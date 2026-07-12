import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import StacksProject_2024.Chap23.Remark_23_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open DividedPowers

universe uA uJ uB

section

variable (A : Type uA) [CommRing A] (J : Type uJ)

-- Semantic search hit `DividedPowers.dpow_eq_from_gens`; local precedent is the indexed
-- divided-power polynomial API from `Remark_23_5_2`, with `ExteriorAlgebra` for exterior
-- generators.

/-- Remark 23.6.4 (1): in the exterior-generator case, adjoining a set `J` of generators in a
fixed positive degree is represented by the exterior algebra on the free `A`-module with basis
`J`; its maps out are uniquely determined by the square-zero image of that generator module. -/
@[stacks 0F4I]
theorem existsUnique_indexedExteriorGeneratorLift
    {B : Type uB} [Semiring B] [Algebra A B]
    (F : (J →₀ A) →ₗ[A] B) (_hF : ∀ m : J →₀ A, F m * F m = 0)
    {d : ℕ} (_hd : 0 < d) :
    ∃! φ : ExteriorAlgebra A (J →₀ A) →ₐ[A] B,
      φ.toLinearMap.comp (ExteriorAlgebra.ι A) = F := sorry

/-- Remark 23.6.4 (2): in the divided-power-generator case, for `(A, I, γ)` and a set `J`, the
algebra `A⟨T_j : j ∈ J⟩` obtained as the directed colimit over finite subsets of `J` has a unique
divided power structure compatible with the given structure on `A` and with each generator
`T_j`. The positive degree hypothesis records that all generators are adjoined in one fixed
degree `d > 0`. -/
@[stacks 0F4I]
theorem existsUnique_indexedTateGeneratorDividedPowers
    (I : Ideal A) (γ : DividedPowers I) {d : ℕ} (_hd : 0 < d) :
    ∃! δ : DividedPowers (indexedDividedPowerPolynomialIdeal A J I),
      (∀ n : ℕ, ∀ j : J,
        δ.dpow n (indexedDividedPowerPolynomialVariable A J j) =
          DividedPowerAlgebra.dp A n (Finsupp.single j (1 : A))) ∧
      IsDPMorphism γ δ (algebraMap A (indexedDividedPowerPolynomial A J)) := sorry

end
