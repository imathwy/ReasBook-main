import StacksProject_2024.Chap10.Lemma_10_59_3
import StacksProject_2024.Chap10.Definition_10_59_8
import StacksProject_2024.Chap10.Lemma_10_59_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Filter Ideal
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]

-- Source/core/bridge triage:
-- * source-facing: the first two theorems compare eventual Hilbert-Samuel `χ`-polynomials for the
--   three terms of a short exact sequence with respect to a fixed ideal of definition;
-- * core/canonical: the owner invariant is `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the final theorem passes from the source-facing polynomial comparison to that
--   canonical degree invariant.

variable (I : Ideal R)
variable (P₁ P₂ P₃ : Polynomial ℚ)

-- Proof sketch: use Lemma 10.59.3 to replace `S.X₁` by a finite-colength submodule
-- `N ⊆ S.X₁` and a shift `c` so that `χ_{I,S.X₂} - χ_{I,S.X₃}` is eventually `χ_{I,N}(n - c)` up
-- to a constant. Lemma 10.59.9 compares the Hilbert-Samuel polynomials of `S.X₁` and `N`, and the
-- finite-difference term coming from the shift lowers the degree by one.
/-- Lemma 10.59.10 (1): for a short exact sequence `S` of finite modules, if `P₁`, `P₂`, and `P₃`
are eventual Hilbert-Samuel `χ`-polynomials for `S.X₁`, `S.X₂`, and `S.X₃`, then
`P₂ - P₃ - P₁` is eventually the corresponding difference of `χ`-functions; if `S.X₁` has
infinite length, this difference has degree strictly smaller than `P₁`. -/
theorem hilbertSamuelChi_difference_degree_lt_of_shortExact
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : ∀ᶠ n : ℕ in atTop, P₁.eval (n : ℚ) = ((χ_ I S.X₁ n).toNat : ℚ))
    (hP₂ : ∀ᶠ n : ℕ in atTop, P₂.eval (n : ℚ) = ((χ_ I S.X₂ n).toNat : ℚ))
    (hP₃ : ∀ᶠ n : ℕ in atTop, P₃.eval (n : ℚ) = ((χ_ I S.X₃ n).toNat : ℚ))
    (hX₁ : ¬ IsFiniteLength R S.X₁) :
    (∀ᶠ n : ℕ in atTop,
        (P₂ - P₃ - P₁).eval (n : ℚ) =
          ((χ_ I S.X₂ n).toNat : ℚ) -
            ((χ_ I S.X₃ n).toNat : ℚ) -
              ((χ_ I S.X₁ n).toNat : ℚ)) ∧
      (P₂ - P₃ - P₁).degree < P₁.degree := sorry

-- Proof sketch: when `S.X₁` has infinite length, combine the lower-degree error-term statement
-- above with nonnegativity of leading coefficients of Hilbert-Samuel polynomials. When `S.X₁` has
-- finite length, Artin-Rees shows that `χ_{I,S.X₂} - χ_{I,S.X₃}` is eventually constant.
/-- Lemma 10.59.10 (2): for a short exact sequence `S` of finite modules, the degree of any
eventual Hilbert-Samuel `χ`-polynomial for `S.X₂` is the maximum of the corresponding degrees for
`S.X₁` and `S.X₃`. -/
theorem hilbertSamuelChi_degree_eq_max_of_shortExact
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : ∀ᶠ n : ℕ in atTop, P₁.eval (n : ℚ) = ((χ_ I S.X₁ n).toNat : ℚ))
    (hP₂ : ∀ᶠ n : ℕ in atTop, P₂.eval (n : ℚ) = ((χ_ I S.X₂ n).toNat : ℚ))
    (hP₃ : ∀ᶠ n : ℕ in atTop, P₃.eval (n : ℚ) = ((χ_ I S.X₃ n).toNat : ℚ)) :
    P₂.degree = max P₁.degree P₃.degree := sorry

-- Proof sketch: apply the preceding degree formula to eventual Hilbert-Samuel polynomial
-- representatives, then use Definition 10.59.8's canonical bridge from any eventual polynomial
-- representative of `χ_{I,-}` to the corresponding `d(-)` invariant.
/-- Lemma 10.59.10 (3): if `S : ShortComplex (ModuleCat R)` is short exact with finite terms over a
Noetherian local ring, then the invariant `d(-)` from Definition 10.59.8 satisfies
`d(S.X₂) = max (d(S.X₁), d(S.X₃))`. -/
theorem hilbertSamuelPolynomialDegree_eq_max_of_shortExact
    (hS : S.ShortExact) :
    hilbertSamuelPolynomialDegree R S.X₂ =
      max (hilbertSamuelPolynomialDegree R S.X₁) (hilbertSamuelPolynomialDegree R S.X₃) := sorry

end
