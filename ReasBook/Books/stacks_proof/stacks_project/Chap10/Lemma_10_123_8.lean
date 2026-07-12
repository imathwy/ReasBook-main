import Mathlib.RingTheory.Algebraic.StronglyTranscendental
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsReduced S]

-- Proof sketch: first apply
-- `isStronglyTranscendental_mk_of_mem_minimalPrimes` to pass from `S` to `S ⧸ q` while keeping the
-- base ring `R`. Then descend the base ring along the surjection `R → R ⧸ q.under R` using
-- `IsStronglyTranscendental.of_surjective_left`.
/-- Lemma 10.123.8: if `q` is a minimal prime of `S`, then the image of a strongly transcendental
element `x` in `S ⧸ q` is strongly transcendental over the quotient subring `R ⧸ q.under R`. -/
@[stacks 00Q0]
theorem isStronglyTranscendental_quotient_over_under_of_mem_minimalPrimes
    {x : S} (hx : IsStronglyTranscendental R x) (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental (R ⧸ q.under R) (Ideal.Quotient.mk q x) :=
  (isStronglyTranscendental_mk_of_mem_minimalPrimes hx q hq).of_surjective_left
    Ideal.Quotient.mk_surjective

end
