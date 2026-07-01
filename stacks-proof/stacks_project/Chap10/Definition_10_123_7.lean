import Mathlib.RingTheory.Algebraic.StronglyTranscendental
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.123.7: the source-facing notion is the canonical mathlib owner predicate
`IsStronglyTranscendental R x`. The theorem below is only a bridge/view to the coefficientwise
wording from the source text. -/
recall IsStronglyTranscendental

open Polynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {x : S}

/-- Bridge/view: strong transcendence is equivalent to saying that any annihilated polynomial
relation forces the multiplier to annihilate every coefficient. -/
theorem isStronglyTranscendental_iff_forall_mul_coeff_eq_zero :
    IsStronglyTranscendental R x ↔
      ∀ u : S, ∀ p : R[X], u * p.aeval x = 0 → ∀ n : ℕ, u * algebraMap R S (p.coeff n) = 0 := by
  constructor
  · intro hx u p hp n
    have hcoeff := congrArg (fun q : S[X] ↦ q.coeff n) <|
      hx u p (by simpa [mul_comm] using hp)
    simpa [coeff_mul_C, coeff_map, mul_comm] using hcoeff
  · intro hx u p hp
    ext n
    simpa [coeff_mul_C, coeff_map, mul_comm] using
      hx u p (by simpa [mul_comm] using hp) n

end
