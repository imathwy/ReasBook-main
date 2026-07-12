import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open IsLocalRing

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

-- Proof sketch: `IsCompleteLocalRing R` is the chapter owner for a complete local ring, so it
-- supplies the maximal-ideal adic completeness needed for the canonical mathlib instance
-- `IsAdicComplete.henselianRing`. Specializing that instance to `maximalIdeal R` gives the
-- required Hensel lifting statement for a local ring directly.
/-- Lemma 10.153.9: a local ring that is complete for the `maximalIdeal`-adic topology, i.e. a
complete local ring in the sense of Definition 10.160.1, is henselian. -/
@[stacks 04GM]
instance localRing_henselian_of_isCompleteLocalRing : HenselianLocalRing R where
  is_henselian f hf a₀ ha₀ hderiv := by
    let _ : HenselianRing R (maximalIdeal R) := inferInstance
    exact HenselianRing.is_henselian f hf a₀ ha₀ (IsUnit.map (Ideal.Quotient.mk _) hderiv)

end
