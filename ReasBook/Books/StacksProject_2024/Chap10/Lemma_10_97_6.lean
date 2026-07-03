import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

-- Domain-style sampling:
-- * primary domain: adic completions of commutative Noetherian rings.
-- * layer: `bridge/view`; this item is the textbook specialization of the owner theorem from
--   `Lemma_10_97_5`.
-- * sampled declarations:
--   `adicCompletion_isNoetherian_and_isAdicComplete`,
--   `I.fg_of_isNoetherianRing`,
--   the quotient instance `[IsNoetherianRing (R ⧸ I)]`.
-- * owner abstraction: the completion ring `AdicCompletion I R`; completeness for the extended
--   ideal is derived API and is discarded here because the source item asks only for
--   Noetherianity.
-- * primitive data: the ring `R`, the ideal `I`, and the ambient Noetherian hypothesis on `R`.
--
-- Proof sketch: since `R` is Noetherian, the ideal `I` is finitely generated and the quotient
-- `R ⧸ I` is Noetherian. Apply the standard noetherianity criterion for `AdicCompletion I R`
-- from the previous lemma to conclude that the completion is Noetherian.
/-- Lemma 10.97.6: if `R` is a Noetherian ring, then its `I`-adic completion
`AdicCompletion I R` is Noetherian. -/
lemma adicCompletion_isNoetherianRing :
    IsNoetherianRing (AdicCompletion I R) :=
  (adicCompletion_isNoetherian_and_isAdicComplete I I.fg_of_isNoetherianRing).1

end
