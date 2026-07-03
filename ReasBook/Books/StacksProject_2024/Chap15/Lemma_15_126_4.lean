import Mathlib
import StacksProject_2024.Chap15.Lemma_15_126_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain-style sampling:
-- * primary domain: systems of parameters and parameter ideals in two-dimensional Noetherian
--   local rings;
-- * sampled owner declarations: `IsSystemOfParameters`, `parameterIdeal`,
--   `isSystemOfParameters_iff_of_ringKrullDim_eq`,
--   `exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes`;
-- * best owner abstraction: the chosen parameter family should be expressed in the chapter's
--   canonical `Fin.cons` form, here specialized to a singleton tail;
-- * primitive-vs-derived: the primitive data are the chosen second parameter `g` and the resulting
--   family `Fin.cons f ![g]`, while perturbation stability and quotient-length equality are
--   derived properties of that owner family.

-- Source/core/bridge triage:
-- * source-facing: the lemma fixes the first parameter `f` and chooses one further parameter in
--   dimension `2`;
-- * core/canonical: the parameter family is owned by `IsSystemOfParameters (Fin.cons f ![g])`
--   and its ideal `parameterIdeal (Fin.cons f ![g])`;
-- * bridge/view: the older pair notation `![f, g]` is only a coordinate presentation of the same
--   owner family, so it should not remain the primary public surface.

-- Proof sketch: use Lemma `15.126.3` with tail length `d = 1` and `k = 1` to choose
-- `g ∈ maximalIdeal R` such that `Fin.cons f ![g]` is a system of parameters. Since the
-- corresponding parameter ideal is an ideal of definition, Lemma `10.32.5` gives `n` with
-- `(maximalIdeal R) ^ n ≤ parameterIdeal (Fin.cons f ![g])`. For any
-- `h ∈ (maximalIdeal R) ^ (n + 1)`, write `h = af + bg` with `a, b ∈ maximalIdeal R`; then
-- `Fin.cons (f + h) ![g]` generates the same ideal as `Fin.cons f ![g]` because `1 + a` is a
-- unit, so the perturbed family is again a system of parameters and the quotient lengths agree.
/-- Lemma 15.126.4: in a two-dimensional Noetherian local ring, if `f ∈ maximalIdeal R` avoids
all minimal primes, then there exist `g ∈ maximalIdeal R` and an exponent `n` (equivalently
`N = n + 1`) such that `Fin.cons f ![g]` is a system of parameters, and every perturbation of the
head entry by an element of `(maximalIdeal R)^(n + 1)` preserves the system of parameters and the
quotient length. -/
theorem exists_systemOfParameters_cons_singleton_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
    (hdim : ringKrullDim R = 2) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ g : maximalIdeal R, ∃ n : ℕ,
      IsSystemOfParameters (Fin.cons f ![g]) ∧
        ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
          IsSystemOfParameters (Fin.cons (f + h) ![g]) ∧
            Module.length R (R ⧸ parameterIdeal (Fin.cons f ![g])) =
              Module.length R (R ⧸ parameterIdeal (Fin.cons (f + h) ![g])) := sorry

end
