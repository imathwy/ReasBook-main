import Mathlib
import StacksProject_2024.Chap10.Lemma_10_47_5
import StacksProject_2024.Chap10.Lemma_10_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

section

variable {k R S : Type u}
variable [Field k] [IsSepClosed k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

private theorem irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime
    (h : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    IrreducibleSpace (PrimeSpectrum R) := by
  rcases h with ⟨p, hp, hp_unique⟩
  have hminimal : minimalPrimes R = {p} := by
    ext q
    constructor
    · intro hq
      simpa using hp_unique q hq
    · rintro rfl
      exact hp
  have hsInf : sInf (minimalPrimes R) = nilradical R := by
    rw [minimalPrimes, nilradical]
    exact Ideal.sInf_minimalPrimes
  have hnil : nilradical R = p := by
    rw [← hsInf, hminimal]
    simp
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  simpa [hnil] using Ideal.minimalPrimes_isPrime hp

private theorem existsUnique_minimalPrime_of_irreducibleSpace_primeSpectrum
    (h : IrreducibleSpace (PrimeSpectrum R)) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at h
  letI : (nilradical R).IsPrime := h
  have hminimal : minimalPrimes R = {nilradical R} := by
    simpa [minimalPrimes, nilradical] using
      (show (nilradical R).minimalPrimes = {nilradical R} from
        Ideal.minimalPrimes_eq_subsingleton_self)
  refine ⟨nilradical R, ?_, ?_⟩
  · rw [hminimal]
    simp
  · intro q hq
    rw [hminimal] at hq
    simpa using hq

-- Proof sketch: over a separably closed field, Lemma `10.47.5` identifies irreducibility of
-- `Spec S` with geometric irreducibility over `k`. Lemma `10.47.7` then upgrades geometric
-- irreducibility of `S` to geometric irreducibility of the tensor-product projection
-- `Spec (R ⊗[k] S) ⟶ Spec R`. Since this projection is open over a field, the owner theorem
-- `GeometricallyIrreducible.irreducibleSpace` yields irreducibility of `Spec (R ⊗[k] S)` from
-- irreducibility of `Spec R`.
/-- Canonical prime-spectrum form of Lemma 10.47.2: over a separably closed field, the tensor
product of two `k`-algebras with irreducible prime spectrum again has irreducible prime spectrum. -/
theorem irreducibleSpace_primeSpectrum_tensorProduct
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  let f : Spec (of (R ⊗[k] S)) ⟶ Spec (of R) :=
    Spec.map (ofHom (algebraMap R (R ⊗[k] S)))
  letI : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) :=
    (Lemma_10_47_5).2 <| by
      simpa using hS
  letI : GeometricallyIrreducible f := by
    simpa [f] using
      (inferInstance :
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))))
  letI : IrreducibleSpace (Spec (of R)) := by
    simpa using hR
  simpa using
    (GeometricallyIrreducible.irreducibleSpace f
      (by
        simpa using
          (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
            IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))))))

/-- Lemma 10.47.2 (Tag 00I7): if `k` is separably closed and the `k`-algebras `R` and `S` each
have a unique minimal prime ideal, then `R ⊗[k] S` also has a unique minimal prime ideal. This is
the textbook formulation of `irreducibleSpace_primeSpectrum_tensorProduct`. -/
@[stacks 00I7]
theorem existsUnique_minimalPrime_tensorProduct
    (hR : ∃! p : Ideal R, p ∈ minimalPrimes R)
    (hS : ∃! p : Ideal S, p ∈ minimalPrimes S) :
    ∃! p : Ideal (R ⊗[k] S), p ∈ minimalPrimes (R ⊗[k] S) := by
  exact existsUnique_minimalPrime_of_irreducibleSpace_primeSpectrum <|
    irreducibleSpace_primeSpectrum_tensorProduct
      (irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime hR)
      (irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime hS)

end
