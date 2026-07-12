import StacksProject_2024.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Ideal PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

private theorem exists_ideal_ge_of_comap_eq_of_le_of_specializingMap
    {p p' : Ideal R} [p'.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Ideal.comap (algebraMap R S) Q = p) (hpq : p ≤ p') :
    ∃ Q' : Ideal S, Q ≤ Q' ∧ Q'.IsPrime ∧ Ideal.comap (algebraMap R S) Q' = p' := by
  let hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) :=
    (isClosedMap_comap_of_isIntegral (algebraMap R S)
      (algebraMap_isIntegral_iff.mpr inferInstance)).specializingMap
  by_cases h : p = p'
  · subst h
    exact ⟨Q, le_rfl, inferInstance, hQ⟩
  · have hspec :
        PrimeSpectrum.comap (algebraMap R S) ⟨Q, inferInstance⟩ ⤳
          (⟨p', inferInstance⟩ : PrimeSpectrum R) := by
      rw [← PrimeSpectrum.le_iff_specializes]
      change Ideal.comap (algebraMap R S) Q ≤ p'
      simpa [hQ] using hpq
    obtain ⟨Q', hQQ', hQ'p⟩ := hgu hspec
    exact ⟨Q'.asIdeal, by simpa using (PrimeSpectrum.le_iff_specializes _ _).mpr hQQ', Q'.2,
      by simpa using congrArg PrimeSpectrum.asIdeal hQ'p⟩

private theorem exists_ideal_gt_of_comap_eq_of_lt_of_specializingMap
    {p p' : Ideal R} [p'.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Ideal.comap (algebraMap R S) Q = p) (hpq : p < p') :
    ∃ Q' : Ideal S, Q < Q' ∧ Q'.IsPrime ∧ Ideal.comap (algebraMap R S) Q' = p' := by
  obtain ⟨Q', hQQ', hQ'prime, hQ'p'⟩ :=
    exists_ideal_ge_of_comap_eq_of_le_of_specializingMap Q hQ hpq.le
  refine ⟨Q', lt_of_le_of_ne hQQ' ?_, hQ'prime, hQ'p'⟩
  intro hQQ'eq
  exact hpq.ne <| hQ.symm.trans <| hQQ'eq ▸ hQ'p'

/- Lemma 10.36.22: in an integral extension, a prime of `S` lying over `p` extends to a prime of
`S` lying over any larger prime `p'` of `R`. This is the integral specialization of the owner
abstraction from Definition 10.41.1 (1), using the canonical closed-map theorem
`PrimeSpectrum.isClosedMap_comap_of_isIntegral`. -/
#check exists_ideal_ge_of_comap_eq_of_le_of_specializingMap

/- If `p < p'`, the same specialization of the owner theorem
from Definition 10.41.1 (1) yields a strictly larger prime over `p'`. -/
#check exists_ideal_gt_of_comap_eq_of_lt_of_specializingMap

end
