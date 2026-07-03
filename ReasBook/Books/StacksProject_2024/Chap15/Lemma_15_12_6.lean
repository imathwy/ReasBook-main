import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.Lemma_15_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum

universe u

noncomputable section

section

variable {A : Type u} [CommRing A]
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

-- Proof sketch: Lemma `15.11.7` shows that `V(I) = V(J)` makes `(A, I)` henselian exactly when
-- `(A, J)` is henselian. Applying the universal property of the left adjoint from Lemma `15.12.1`
-- to the two henselization pairs gives unique `A`-algebra maps in both directions, and the same
-- uniqueness forces the composites to be identities.
/-- Lemma 15.12.6: if two ideals of `A` have the same zero locus in `Spec A`, then the chosen
pair-henselization functor yields canonically isomorphic `A`-algebras for the pairs `(A, I)` and
`(A, J)`. -/
theorem henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A))) :
    ∃! e : henselizationRing (pairOfIdeal I) ≃ₐ[A] henselizationRing (pairOfIdeal J),
      e.toRingHom.comp
        (toHenselization (pairOfIdeal I)) =
      toHenselization (pairOfIdeal J) := sorry

end
