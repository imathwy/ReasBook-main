import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_59_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Ideal

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

-- Domain-style sampling for this file:
-- * primary domain: Hilbert-Samuel functions in local commutative algebra, compared along a
--   finite-colength submodule;
-- * relevant owner APIs in the surrounding ecosystem: `Ideal.hilbertSamuelChi`,
--   `Ideal.exists_pos_pow_inf_eq_pow_smul`, `Module.length_eq_add_of_exact`, and
--   `IsFiniteLength`;
-- * best owner abstraction: the source-facing owner is already `Ideal.hilbertSamuelChi`, so this
--   file should provide only comparison lemmas for that owner rather than a parallel wrapper;
-- * primitive data: the ideal of definition `I`, the submodule `N`, and the finite-length
--   quotient `M ⧸ N`;
-- * derived API: an eventual `atTop` reformulation of the cutoff inequality for later polynomial
--   arguments.

-- Proof sketch: because `I` is an ideal of definition and `M ⧸ N` has finite length, some power
-- of `I` annihilates `M ⧸ N`, equivalently `I ^ c₂ • ⊤ ≤ N`. Then use the short exact sequence
-- `0 → N / (I^(n + 1) M ∩ N) → M / I^(n + 1) M → (M ⧸ N) → 0` and additivity of module length for
-- the upper bound, while the containment `I^(n + 1) M ≤ I^(n + 1 - c₂) N` for `n ≥ c₂` gives the
-- lower bound.
/-- Lemma 10.59.2: if `N ⊆ M` has finite-length quotient, then the Hilbert-Samuel `χ`-functions
of `N` and `M` with respect to an ideal of definition `I` differ only by an additive constant and
an eventual shift in the index. This is the source-facing cutoff formulation. -/
theorem exists_hilbertSamuelChi_bounds_of_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, ∀ n ≥ c,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤
          χ_ I M n ∧
        χ_ I M n ≤
          Module.length R (M ⧸ N) + χ_ I N n := sorry

/-- Canonical eventual reformulation of Lemma 10.59.2: for a finite-colength submodule
`N ⊆ M`, the Hilbert-Samuel `χ`-function of `M` is eventually squeezed between a translate of the
Hilbert-Samuel `χ`-function of `N` and the same function shifted only by the quotient length. -/
theorem exists_eventually_hilbertSamuelChi_bounds_of_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤
          χ_ I M n ∧
        χ_ I M n ≤
          Module.length R (M ⧸ N) + χ_ I N n := by
  rcases exists_hilbertSamuelChi_bounds_of_isFiniteLength_quotient I hI N hquot with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop c] with n hn
  exact hc n hn

end Ideal

end
