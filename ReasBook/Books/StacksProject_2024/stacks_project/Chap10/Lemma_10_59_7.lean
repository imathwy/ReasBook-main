import StacksProject_2024.Chap10.Lemma_10_59_4
import StacksProject_2024.Chap10.Proposition_10_59_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Ideal

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
variable {I I' : Ideal R} {P P' : Polynomial ℚ}

-- Source/core/bridge triage:
-- * source-facing: the Hilbert-Samuel `χ`- and `φ`-functions attached to an ideal of definition;
-- * core/canonical: Definition 10.59.8's owner invariant `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the current lemmas identify the degree of any eventual polynomial representative,
--   so the later owner invariant does not depend on the chosen ideal of definition.

-- Proof sketch: apply Lemma 10.59.4 to compare the two adic quotient-length functions after
-- linear reindexing in both directions. Once both `χ`-functions are known to be eventually given
-- by polynomials, these eventual inequalities force any two polynomial representatives to have the
-- same degree.
/-- Lemma 10.59.7 (2): for a finite module over a Noetherian local ring, the degree of any
eventual polynomial representative of the Hilbert-Samuel `χ`-function is independent of the chosen
ideal of definition. -/
lemma hilbertSamuelChi_degree_eq_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = ((χ_ I' M n).toNat : ℚ)) :
    P.degree = P'.degree := sorry

-- Proof sketch: first apply the `χ`-degree statement above to the two eventual `χ`-polynomials,
-- obtained from Proposition 10.59.5. Then use the eventual relation
-- `φ_{I,M}(n) = χ_{I,M}(n) - χ_{I,M}(n - 1)` and the finite-difference formula for polynomial
-- degree to transport the same degree equality to the `φ`-functions.
/-- Lemma 10.59.7 (1): for a finite module over a Noetherian local ring, the degree of any
eventual polynomial representative of the Hilbert-Samuel `φ`-function is independent of the chosen
ideal of definition. -/
lemma hilbertSamuelPhi_degree_eq_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((φ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = ((φ_ I' M n).toNat : ℚ)) :
    P.degree = P'.degree := sorry

end Ideal

end
