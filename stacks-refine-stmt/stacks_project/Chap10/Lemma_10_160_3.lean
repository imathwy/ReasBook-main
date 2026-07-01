import Mathlib
import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap10.Lemma_10_97_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

-- Domain-style sampling:
-- * primary domain: complete local rings and maximal-ideal adic completion.
-- * layer: `bridge/view`; the source statement is the Noetherianity consequence of the chapter
--   owner `IsCompleteLocalRing`, obtained by comparing `R` with its canonical completion.
-- * sampled declarations:
--   `IsCompleteLocalRing`,
--   `AdicCompletion.ofAlgEquiv`,
--   `adicCompletion_isNoetherian_and_isAdicComplete`,
--   `isNoetherianRing_of_ringEquiv`.
-- * owner abstraction: `IsCompleteLocalRing R`; the raw hypothesis
--   `IsAdicComplete (maximalIdeal R) R` is derived from this owner and should not remain the main
--   public interface here.
-- * primitive data: the ring `R`, the complete-local owner structure, and the finite-generation
--   hypothesis on `maximalIdeal R`.
-- * derived API: Noetherianity of the maximal-ideal adic completion and the canonical completion
--   equivalence back to `R`.

-- Proof sketch: apply Lemma `10.97.5` to the ideal `maximalIdeal R`. The quotient
-- `R ⧸ maximalIdeal R` is the residue field of the local ring `R`, hence Noetherian. Since `R`
-- is complete for the `maximalIdeal R`-adic topology by hypothesis, the canonical map
-- `R → AdicCompletion (maximalIdeal R) R` is bijective, so the Noetherianity of the completion
-- transfers back to `R`.
/-- Lemma 10.160.3: a complete local ring whose maximal ideal is finitely generated is
Noetherian. -/
theorem isNoetherianRing_of_isCompleteLocalRing_of_maximalIdeal_fg
    (hfg : (maximalIdeal R).FG) : IsNoetherianRing R := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let _ : IsNoetherianRing (R ⧸ maximalIdeal R) := by infer_instance
  let _ : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal R) hfg).1
  exact isNoetherianRing_of_ringEquiv (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingEquiv

end
