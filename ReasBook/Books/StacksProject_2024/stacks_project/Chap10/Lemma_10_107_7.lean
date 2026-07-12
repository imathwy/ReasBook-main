import StacksProject_2024.Chap10.Lemma_10_107_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: use the canonical faithfully-flat codescent theorem for bijectivity, reducing to
-- the base-changed map `algebraMap S (S ⊗[R] S)`. Under the epimorphism hypothesis, Lemma
-- `10.107.1` identifies this map with the canonical tensor-factor map and proves it bijective.
/-- Lemma 10.107.7: a faithfully flat epimorphism of commutative rings is bijective, hence an
isomorphism. -/
theorem faithfullyFlat_epi_bijective [Algebra.IsEpi R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Function.Bijective (algebraMap R S) := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI : Module.FaithfullyFlat R S := hff
  have hbase : Function.Bijective (algebraMap S (S ⊗[R] S)) := by
    simpa using
      (algebra_isEpi_iff_bijective_includeLeft.mp (inferInstance : Algebra.IsEpi R S))
  exact Module.FaithfullyFlat.bijective_of_tensorProduct hbase

end
