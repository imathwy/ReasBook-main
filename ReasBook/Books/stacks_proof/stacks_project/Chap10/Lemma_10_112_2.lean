import Mathlib
import StacksProject_2024.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: view the maximal ideal `q` as a closed point of `Spec(S)`. A specializing map
-- sends the closure of a singleton to a closed set; since `q` is already closed, its image in
-- `Spec(R)` is a closed point. Translating closed points back to maximal ideals gives the result.
/-- Lemma 10.112.2: for a ring map `R → S` with the going-up property, the inverse image in `R` of
a maximal ideal of `S` is again a maximal ideal. -/
@[stacks 00OI]
theorem isMaximal_comap_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (q : Ideal S) [q.IsMaximal] :
    (q.comap (algebraMap R S)).IsMaximal := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  have hx : IsClosed ({x} : Set (PrimeSpectrum S)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2 inferInstance
  have hclosed :
      IsClosed (PrimeSpectrum.comap (algebraMap R S) '' closure ({x} : Set (PrimeSpectrum S))) :=
    (specializingMap_iff_isClosed_image_closure_singleton
      (PrimeSpectrum.continuous_comap (algebraMap R S))).1 hgu x
  have hclosed' : IsClosed ({PrimeSpectrum.comap (algebraMap R S) x} : Set (PrimeSpectrum R)) := by
    simpa [hx.closure_eq] using hclosed
  simpa [x, PrimeSpectrum.comap_asIdeal] using
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap (algebraMap R S) x)).1
      hclosed'

end
