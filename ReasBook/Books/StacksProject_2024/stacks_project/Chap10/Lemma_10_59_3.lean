import Mathlib
import StacksProject_2024.Chap10.Lemma_10_59_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}

open CategoryTheory
open scoped Ideal

variable [IsLocalRing R] [IsNoetherianRing R]

variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₂]

namespace Ideal

-- Proof sketch: apply Artin-Rees to the submodule `LinearMap.range S.f.hom ⊆ S.X₂` to obtain a
-- shift `c` with `S.X₁ ∩ I^n S.X₂ = I^(n - c) (S.X₁ ∩ I^c S.X₂)` for `n ≥ c`, set
-- `N = S.X₁ ∩ I^c S.X₂`, and use additivity of `Module.length` on the short exact sequence
-- `0 → S.X₁ / (S.X₁ ∩ I^n S.X₂) → S.X₂ / I^n S.X₂ → S.X₃ / I^n S.X₃ → 0`.
/-- Lemma 10.59.3: if `I` is an ideal of definition of the Noetherian local ring `R` and
`S : ShortComplex (ModuleCat R)` is a short exact sequence of finite `R`-modules, then there
exist a submodule `N ⊆ S.X₁` of finite colength and an integer shift `c` carrying the shifted
Hilbert-Samuel decomposition for the `χ`-function. This is the primitive source-facing content;
the `φ`-decomposition is its standard finite-difference companion. -/
theorem exists_hilbertSamuelChi_decomposition_of_shortExact
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          χ_ I S.X₂ n =
            χ_ I S.X₃ n +
              χ_ I N (n - c) +
                Module.length R (S.X₁ ⧸ N) := sorry

/-- Companion to Lemma 10.59.3: under the same hypotheses, one may choose a finite-colength
submodule of `S.X₁` and a shift giving the corresponding shifted Hilbert-Samuel decomposition for
the `φ`-function. -/
theorem exists_hilbertSamuelPhi_decomposition_of_shortExact
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          φ_ I S.X₂ n =
            φ_ I S.X₃ n +
              φ_ I N (n - c) := sorry

end Ideal

end
