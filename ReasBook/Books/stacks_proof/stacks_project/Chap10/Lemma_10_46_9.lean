import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_46_8

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum Topology
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]

/- The closed-map input is the canonical mathlib owner theorem
`PrimeSpectrum.isClosedMap_comap_of_isIntegral`. -/
recall PrimeSpectrum.isClosedMap_comap_of_isIntegral

/- Integrality is preserved by the canonical base-change owner theorem
`RingHom.isIntegral_isStableUnderBaseChange`. -/
recall RingHom.isIntegral_isStableUnderBaseChange

/- The injective-spectrum and purely inseparable residue-field part is already the chapter-local
owner theorem from Lemma `10.46.8`. -/
recall baseChange_injective_comap_and_hasPurelyInseparableResidueFieldExtensions

/-- Lemma 10.46.9: if `R → S` is integral, induces an injective map `Spec(S) → Spec(R)`, and
induces purely inseparable extensions on residue fields, then `Spec(S) → Spec(R)` is a
homeomorphism onto a closed subset, and after any base change `R → R'` the map
`R' → R' ⊗[R] S` still satisfies these three properties. -/
@[stacks 0BRC]
theorem integral_isClosedEmbedding_primeSpectrum_comap_and_baseChange
    (hInt : (algebraMap R S).IsIntegral)
    (hinj : Function.Injective (comap (algebraMap R S)))
    (hres : (algebraMap R S).HasPurelyInseparableResidueFieldExtensions) :
    IsClosedEmbedding (comap (algebraMap R S)) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        f'.IsIntegral ∧
          Function.Injective (comap f') ∧
          f'.HasPurelyInseparableResidueFieldExtensions := by
  refine ⟨?_, ?_⟩
  · exact .of_continuous_injective_isClosedMap (continuous_comap _) hinj
      (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hInt)
  · intro R' _ _
    letI : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hInt
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    have hInt' : f'.IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
    have hbase :
        Function.Injective (comap f') ∧ f'.HasPurelyInseparableResidueFieldExtensions := by
      simpa [f'] using
        baseChange_injective_comap_and_hasPurelyInseparableResidueFieldExtensions
          R' hinj hres
    exact ⟨hInt', hbase.1, hbase.2⟩

end
