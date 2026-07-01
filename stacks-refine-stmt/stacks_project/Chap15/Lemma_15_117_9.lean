import Mathlib
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap15.Definition_15_116_1
import stacks_project.Chap15.Lemma_15_117_6
import stacks_project.Chap15.Proposition_15_117_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

-- Proof sketch: if `A` is Nagata, then `B` is Nagata because an essentially finite type algebra
-- over a Nagata ring is again Nagata after passing through a finite type model and localizing.
-- With `B` Nagata in hand, Proposition `15.117.8` gives a solution for `A → B`, and then
-- Lemma `15.117.6` upgrades that solution to a separable solution because `L / K` is separable.
/-- Lemma 15.117.9: let `A → B` be an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`. Assume either `A` or `B` is a Nagata ring, and assume `L / K`
is separable. Then there exists a separable solution for `A → B` in the sense of Definition
`15.116.1`. -/
lemma exists_separableSolution_of_essentiallyFiniteType_of_nagataRing_or
    (hNagata : NagataRing A ∨ NagataRing B)
    (hsepKL : Algebra.IsSeparable K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry

end
