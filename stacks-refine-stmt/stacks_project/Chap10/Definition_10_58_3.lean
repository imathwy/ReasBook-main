import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped BigOperators

section

variable {A : Type u} [AddCommGroup A]

/-- Definition 10.58.3: a function on the integers is a numerical polynomial if, for all
sufficiently large integers `n`, it agrees with a finite sum `∑_{i=0}^r \binom{n}{i} a_i` with
coefficients in the abelian group `A`. In Lean, the source's partial-function wording is modeled
canonically by eventual equality at `atTop` for a total function `ℤ → A`. -/
def IsNumericalPolynomial (f : ℤ → A) : Prop :=
  ∃ (r : ℕ) (a : Fin (r + 1) → A),
    f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

end
