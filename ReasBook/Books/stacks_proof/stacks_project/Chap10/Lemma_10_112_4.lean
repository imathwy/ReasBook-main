import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_112_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

-- Proof sketch: combine the upper bound `ringKrullDim S ≤ ringKrullDim R` from Lemma `10.112.3`
-- with the lower bound `ringKrullDim R ≤ ringKrullDim S` obtained from the surjectivity of
-- `Spec(S) → Spec(R)` for an integral map with injective `algebraMap`, using the canonical owner
-- theorem `RingHom.IsIntegral.comap_surjective` and the specializing-map comparison of
-- Lemma `10.112.1`.
/-- Lemma 10.112.4: if `R` is identified with a subring of `S` and `S` is integral over `R`, then
the Krull dimensions of `R` and `S` are equal. -/
@[stacks 00OK]
theorem ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  have hInt : (algebraMap R S).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  apply le_antisymm
  · exact ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
      (algebraMap R S)
      (RingHom.IsIntegral.comap_surjective hInt hinj)
      (.inl <| (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S) hInt).specializingMap)
  · exact ringKrullDim_le_of_isIntegral

end
