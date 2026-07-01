import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

/- Domain-style sampling:
- primary domain: irreducible polynomials over a field, their separability, and the
  positive-characteristic `expand`/contraction interface;
- sampled owner declarations:
  `Polynomial.separable_iff_derivative_ne_zero`,
  `Polynomial.separable_def`,
  `Polynomial.HasSeparableContraction.isSeparableContraction`,
  `Irreducible.hasSeparableContraction`;
- best owner abstractions:
  `Polynomial.separable_iff_derivative_ne_zero` for the derivative criterion and
  `Polynomial.HasSeparableContraction` for the positive-characteristic factorization;
- primitive data: an irreducible polynomial `P : F[X]`;
- derived API: the source-facing `or` and existence reformulations below, together with their
  coprimeness companions.

Layer triage:
- `source-facing`: the four bridge theorems in this file;
- `core/canonical`: the two recalled owner declarations above;
- `bridge/view`: the coprimeness restatements obtained from `Polynomial.separable_def`.
-/

/- Lemma 9.12.1: the irreducible-case derivative criterion is the canonical theorem
`Polynomial.separable_iff_derivative_ne_zero`; the source-facing `or` reformulation below is only
its textbook bridge. -/
recall Polynomial.separable_iff_derivative_ne_zero

/- Lemma 9.12.1: the positive-characteristic factorization is organized by the owner abstraction
`Polynomial.HasSeparableContraction`, produced canonically for irreducibles by
`Irreducible.hasSeparableContraction`. The source-facing existence theorem below unpacks this owner
and adds the irreducibility of the contracted factor. -/
recall Irreducible.hasSeparableContraction

variable {F : Type u} [Field F] {P : F[X]}

/-- Source-facing bridge for Lemma 9.12.1: an irreducible polynomial is separable unless its
derivative vanishes. -/
theorem irreducible_separable_or_derivative_eq_zero (hP : Irreducible P) :
    P.Separable ∨ P.derivative = 0 := by
  by_cases hderiv : P.derivative = 0
  · exact Or.inr hderiv
  · exact Or.inl <| (separable_iff_derivative_ne_zero hP).2 hderiv

/-- Companion bridge for Lemma 9.12.1: via `Polynomial.separable_def`, the textbook wording is
that an irreducible polynomial is coprime to its derivative unless the derivative vanishes. -/
theorem irreducible_isCoprime_derivative_or_derivative_eq_zero (hP : Irreducible P) :
    IsCoprime P P.derivative ∨ P.derivative = 0 := by
  simpa [separable_def] using irreducible_separable_or_derivative_eq_zero hP

/-- Source-facing bridge for Lemma 9.12.1: if an irreducible polynomial over a field has zero
derivative, then the field has positive characteristic and the polynomial is an iterated `expand`
of an irreducible separable polynomial. -/
theorem exists_irreducible_separable_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ Q.Separable := by
  have hchar_ne_zero : ringChar F ≠ 0 := by
    intro hchar
    letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 hchar
    exact (separable_iff_derivative_ne_zero hP).1 hP.separable hderiv
  have hchar : 0 < ringChar F := Nat.pos_of_ne_zero hchar_ne_zero
  letI : NeZero (ringChar F) := ⟨hchar_ne_zero⟩
  letI : Fact (ringChar F).Prime := CharP.char_is_prime_of_pos F (ringChar F)
  have hcontraction := hP.hasSeparableContraction (ringChar F)
  obtain ⟨hQsep, n, hQP⟩ := hcontraction.isSeparableContraction
  have hQirr : Irreducible hcontraction.contraction :=
    of_irreducible_expand_pow (Nat.ne_of_gt hchar) (hQP ▸ hP)
  exact ⟨hchar, n, hcontraction.contraction, hQP.symm, hQirr, hQsep⟩

/-- Companion bridge for Lemma 9.12.1: rewriting separability as coprimeness with the derivative
recovers the textbook formulation of the positive-characteristic case. -/
theorem exists_irreducible_isCoprime_derivative_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ IsCoprime Q Q.derivative := by
  simpa [separable_def] using
    exists_irreducible_separable_expand_of_derivative_eq_zero hP hderiv
