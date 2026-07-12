import Mathlib
import StacksProject_2024.Chap10.Definition_10_58_3
import StacksProject_2024.Chap10.Definition_10_59_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Ideal

-- Proof sketch: form the associated graded ring `⊕_{d ≥ 0} I^d / I^(d + 1)` and the associated
-- graded module via the owner abstractions `idealAssociatedGradedRing I` and
-- `RingTheory.Sequence.idealAssociatedGradedModule I M`; Proposition 10.58.7 shows that the
-- resulting graded-piece Grothendieck-class function is numerical polynomial, and Lemma 10.55.1
-- identifies its length with the Hilbert-Samuel `φ`-function.
variable (I : Ideal R)

-- Source/core/bridge triage:
-- * source-facing: the Hilbert-Samuel `φ`- and `χ`-functions attached to an ideal of definition;
-- * core/canonical: the chapter owner predicate `IsNumericalPolynomial`;
-- * bridge/view: the source functions are reindexed along `Int.toNat`, which is the input shape
--   used later to pass from eventual numerical-polynomiality on `ℤ` to eventual rational
--   polynomial representatives on `ℕ`.

/-- Proposition 10.59.5 (1): if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`I` is an ideal of definition, then the Hilbert-Samuel `φ`-function of `M` with respect to `I`,
viewed as a function on the integers via `Int.toNat`, is a numerical polynomial. -/
theorem hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := sorry

-- Proof sketch: use the first part together with Lemma 10.58.5, which upgrades eventual
-- numerical polynomiality of the first difference to numerical polynomiality of the original
-- function via `IsNumericalPolynomial.of_sub_pred`, after identifying the first difference of
-- `χ_{I,M}` with `φ_{I,M}` for large `n`.
/-- Proposition 10.59.5 (2): if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`I` is an ideal of definition, then the Hilbert-Samuel `χ`-function of `M` with respect to `I`,
viewed as a function on the integers via `Int.toNat`, is a numerical polynomial. -/
theorem hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial fun n : ℤ ↦ ((χ_ I M n.toNat).toNat : ℚ) := sorry

end Ideal

end
