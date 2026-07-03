import Mathlib
import StacksProject_2024.Chap15.Definition_15_116_1

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

-- Proof sketch: follow the textbook argument by first applying Epp's theorem to obtain a finite
-- weak solution after passing to a DVR with perfect residue field, use Lemma `15.112.5` to
-- identify weak solutions with solutions over the perfect-residue-field base, and then descend
-- the resulting formally smooth local branches to a finite stage using Lemma `15.117.7` and the
-- finite-type hypothesis on `B`.
/-- Proposition 15.117.8: if `A ⊂ B` is an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`, then there exists a finite extension `K₁ / K` which is a
solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_finite_extension_solution_of_essentiallyFiniteType :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSolutionFor A B K L K1 := sorry

end
