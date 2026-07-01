import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: flatness of adic completions of free modules over a Noetherian ring;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `AdicCompletion.flat_of_isNoetherian`,
  `adicCompletionDirectSumToPi_universallyInjective`,
  `adicCompletion_isNoetherian_and_flat_of_flat_mod_ideal_and_tor_one_vanishing`;
- primitive data: the ideal `I`, the index type `A`, and the free `R`-module `⨁ a : A, R`;
- derived API: the universally injective comparison with the product module from
  Lemma `15.27.1`, and the more general completion-flatness criterion later packaged in
  Lemma `15.27.5`.

Source/core/bridge triage:
- `source-facing`: the flatness statement for the completed direct sum from the Stacks lemma;
- `core/canonical`: the owner predicate `Module.Flat`;
- `bridge/view`: the canonical comparison map from the completed direct sum to the product module.
-/

-- Proof sketch: combine the universally injective comparison map from Lemma `15.27.1` with the
-- flatness of the product module over a Noetherian ring and the flat completion map
-- `R → AdicCompletion I R`. The public statement should remain on the canonical owner
-- `Module.Flat R (AdicCompletion I (⨁ a, R))`; the comparison map and any quotient/tensor bridges
-- belong to the proof route rather than the theorem surface.
/-- Lemma 15.27.2: for a Noetherian ring `R`, ideal `I`, and set `A`, the `I`-adic completion of
the direct sum `⨁ a : A, R` is a flat `R`-module. -/
theorem adicCompletion_directSum_flat (I : Ideal R) (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := sorry

end
