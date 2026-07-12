import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable [IsNoetherianRing (R ⧸ I)]

-- Domain-style sampling:
-- * primary domain: adic completions of commutative rings, with Noetherianity and adic
--   completeness for the extended ideal on the completion.
-- * layer: `source-facing`; the theorem keeps the textbook criterion while reusing the canonical
--   owner ring `AdicCompletion I R` and the owner predicate `IsAdicComplete`.
-- * sampled declarations:
--   `AdicCompletion.isAdicComplete`,
--   `IsAdicComplete.map_algebraMap_iff`,
--   `AdicCompletion.evalOneₐ`,
--   `isNoetherianRing_iff_ideal_fg`.
-- * owner abstraction: `AdicCompletion I R`; the extended ideal
--   `I.map (algebraMap R (AdicCompletion I R))` is derived from that owner, not extra primitive
--   data.
-- * primitive data: the ideal `I`, the quotient hypothesis `[IsNoetherianRing (R ⧸ I)]`, and the
--   finite-generation input `hI`.
-- * derived API: Noetherianity of the completion ring and completeness for the extended ideal.
--
-- Proof sketch: use finite generation of `I` to obtain `I`-adic completeness of
-- `AdicCompletion I R`, then transport it to the extended ideal via
-- `IsAdicComplete.map_algebraMap_iff`. For noetherianity, combine the quotient identification
-- `(AdicCompletion I R) ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I`
-- with finite generation of the extended ideal and the standard criterion that a ring is
-- noetherian when a finitely generated ideal has noetherian quotient.
/-- Lemma 10.97.5: if `R ⧸ I` is Noetherian and `I` is finitely generated, then the `I`-adic
completion `AdicCompletion I R` is a Noetherian ring and is complete for the adic topology defined
by the extended ideal `I.map (algebraMap R (AdicCompletion I R))`. -/
lemma adicCompletion_isNoetherian_and_isAdicComplete
    (hI : I.FG) :
    IsNoetherianRing (AdicCompletion I R) ∧
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  constructor
  · sorry
  ·
    have hmap :
        IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) ↔
          IsAdicComplete I (AdicCompletion I R) :=
      IsAdicComplete.map_algebraMap_iff I (AdicCompletion I R)
    exact hmap.2 (AdicCompletion.isAdicComplete hI)

end
