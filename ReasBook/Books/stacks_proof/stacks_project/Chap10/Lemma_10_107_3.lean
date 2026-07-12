import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u

section

variable {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Lemma 10.107.3: base change of an epimorphism of commutative rings along any map `R → R'`
remains an epimorphism. Equivalently, if `R → S` is epic, then the canonical map
`R' → R' ⊗[R] S` is again epic. -/
@[stacks 04VQ]
theorem algebra_isEpi_tensorProduct_of_isEpi [Algebra.IsEpi R S] :
    Algebra.IsEpi R' (R' ⊗[R] S) := by
  letI : Epi (CommRingCat.ofHom (algebraMap R S)) := (CommRingCat.epi_iff_epi).2 inferInstance
  exact (CommRingCat.epi_iff_epi).1 <| by
    simpa using (CommRingCat.isPushout_tensorProduct R R' S).epi_inl_of_epi

end
