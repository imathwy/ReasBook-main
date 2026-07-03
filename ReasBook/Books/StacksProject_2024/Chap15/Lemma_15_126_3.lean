import stacks_project.Chap10.Definition_10_60_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain-style sampling:
-- * primary domain: systems of parameters in Noetherian local rings, with minimal-prime
--   avoidance and one-step dimension reduction;
-- * sampled owner declarations: `IsSystemOfParameters`, `parameterIdeal`,
--   `generatedIdeal_clause_iff_exists_systemOfParameters`,
--   `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`.
--
-- Source/core/bridge triage:
-- * source-facing: the lemma asserts that an element `f` outside all minimal primes can be
--   extended, in first-position order, to a system of parameters whose tail lies in a prescribed
--   power of the maximal ideal;
-- * core/canonical: `IsSystemOfParameters` is the owner abstraction for the chosen parameter
--   family, so the primitive data should be the ordered tail `y : Fin d → maximalIdeal R`, with
--   the full family derived as `Fin.cons f y`;
-- * bridge/view: minimal-prime avoidance should use the chapter's canonical membership-style
--   owner surface `∀ p ∈ minimalPrimes R, (f : R) ∉ p`, and
--   the existence step in the quotient should be read through the owner theorem
--   `generatedIdeal_clause_iff_exists_systemOfParameters` rather than through a lower-level
--   generated-ideal witness package.
-- Proof sketch: if `d = 0`, use the one-term parameter family `Fin.cons f` and the tail condition
-- is vacuous. Otherwise, Lemma `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`
-- lowers the quotient dimension to `d`, and the owner-level existence clause from Proposition
-- `10.60.9`, packaged by `generatedIdeal_clause_iff_exists_systemOfParameters`, supplies a
-- length-`d` system of parameters in `R / (f)`. Lift those parameters to `R`, then replace each
-- lift by its `k`-th power so that the tail lands in `(maximalIdeal R)^k` without changing the
-- generated radical.
/-- Lemma 15.126.3: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters in `(maximalIdeal R)^k` whose ordered extension
`Fin.cons f y` is a system of parameters. This is the source-facing ordered `Fin.cons` form of
adjoining further parameters in `(maximalIdeal R)^k` to the specified element `f`. -/
theorem exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes
    {d k : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ j, (y j : R) ∈ maximalIdeal R ^ k := sorry

end
