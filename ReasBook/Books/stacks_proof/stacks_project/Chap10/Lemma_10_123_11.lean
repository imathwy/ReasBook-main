import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.123.11: if `S` is a quotient of `R[X]`, `q` is a prime ideal of `S`, and `R → S` is
quasi-finite at `q`, then there exists an element of the integral closure of `R` in `S` outside
`q` such that localizing the integral closure and `S` away from that element gives the same ring. -/
-- Proof sketch: a surjective `R`-algebra map `R[X] → S` makes `S` finite type over `R`. Apply the
-- algebraic Zariski main theorem at `q` to conclude `Algebra.ZariskisMainProperty R q`, which is
-- exactly the existence of such an element in `integralClosure R S` with bijective away map.
@[stacks 00Q8]
theorem zariskisMainProperty_of_surjective_polynomial
    (φ : Polynomial R →ₐ[R] S) (hφ : Function.Surjective φ) (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] : Algebra.ZariskisMainProperty R q := by
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective φ hφ
  exact Algebra.ZariskisMainProperty.of_finiteType q

end
