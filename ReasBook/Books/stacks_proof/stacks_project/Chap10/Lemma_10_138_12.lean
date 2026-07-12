import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) [Module.Flat R S]

-- Proof sketch: apply the canonical quotient-descent theorem
-- `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` to the quotient maps
-- `R → R ⧸ I` and `S → S ⧸ IS`. For quotient maps, surjectivity is automatic, the kernel of
-- `S → S ⧸ IS` is exactly `IS`, and the square-zero hypothesis is precisely `(ker q_R)^2 = ⊥`.
/-- Lemma 10.138.12: if `I` is a square-zero ideal of `R`, `S` is flat over `R`, and the
quotient map `R ⧸ I → S ⧸ IS` is formally smooth, then `R → S` is formally smooth. -/
@[stacks 031L]
theorem formallySmooth_of_square_zero_ideal_of_flat_of_quotient_formallySmooth
    (hSq : I ^ 2 = ⊥)
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    Algebra.FormallySmooth R S := by
  have hsurjR : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  have hsurjS : Function.Surjective (algebraMap S (S ⧸ Ideal.map (algebraMap R S) I)) := by
    simpa using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)))
  simpa using
    (Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
      hsurjR hsurjS
      (by simp)
      (by simpa using hSq)
      hSmooth)

end
