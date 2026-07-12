import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.2: if `φ : R[X] →+* S` and `t : S` is integral over `R[X]`, and if there is a
monic polynomial `p : R[X]` such that `t * φ p` lies in the image of `φ`, then there exists
`q : R[X]` such that `t - φ q` is integral over `R` with respect to the composite map
`R → R[X] → S`. -/
-- Proof sketch: equip `S` with the `R`-algebra structure induced by `φ.comp C`, convert `φ` into
-- the corresponding `R`-algebra morphism from `R[X]`, apply the canonical mathlib theorem
-- `exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range`, and then translate the conclusion
-- back to `RingHom.IsIntegralElem` for the composite map `φ.comp C`.
theorem exists_isIntegralElem_sub_of_isIntegralElem_of_mul_mem_range
    {φ : R[X] →+* S} {t : S} {p : R[X]}
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : t * φ p ∈ Set.range φ) :
    ∃ q : R[X], (φ.comp C).IsIntegralElem (t - φ q) := by
  letI : Algebra R S := (φ.comp C).toAlgebra
  let φ' : R[X] →ₐ[R] S :=
    { toRingHom := φ
      commutes' := by
        intro r
        simp [RingHom.algebraMap_toAlgebra] }
  have hp' : φ' p * t ∈ φ'.range := by
    rcases hp with ⟨q, hq⟩
    exact ⟨q, by simpa [φ', mul_comm] using hq⟩
  obtain ⟨q, hq⟩ :=
    exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range φ' t p ht hpm hp'
  refine ⟨q, ?_⟩
  simpa [IsIntegral, RingHom.IsIntegralElem, RingHom.algebraMap_toAlgebra, φ'] using hq

end RingHom

end
