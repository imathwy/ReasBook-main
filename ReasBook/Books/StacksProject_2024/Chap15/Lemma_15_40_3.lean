import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/- Domain-style sampling for Lemma 15.40.3:
- primary domain: adic formal smoothness of local homomorphisms of Noetherian local rings and the
  resulting flatness criterion.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_tfae_completion_invariance`
  * `adicCompletion_algebraMap_flat`
  * `exists_powerSeries_presentation_of_localHom_completeLocal`
- best owner abstraction: the primitive datum is the local ring map `f : A →+* B` itself, so the
  public statement should live on the owner `RingHom` and conclude with the canonical flatness
  predicate `f.Flat`, not with an auxiliary wrapper around the source and target rings.
- primitive data: the ring map `f`, the local/Noetherian hypotheses on `A` and `B`, and the
  maximal-ideal-adic formal smoothness hypothesis on `f`.
- derived API: flatness of `f`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project implication from maximal-ideal-adic formal smoothness to
  flatness for a local homomorphism of Noetherian local rings;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `RingHom.Flat`;
- `bridge/view`: completion invariance, flatness of Noetherian adic completions, and the complete
  local power-series presentation from Lemma `15.39.3`.
-/

-- Proof sketch: pass to the completions of `A` and `B` using the completion-invariance of adic
-- formal smoothness and the flatness criterion for Noetherian completions. After reducing to the
-- complete local case, choose a flat power-series presentation as in Lemma `15.39.3`. Formal
-- smoothness provides a section of the quotient map from the base change `S / I S → B`, so `B` is
-- a retract of a flat `A`-module and hence flat.
/-- Lemma 15.40.3: a local homomorphism of Noetherian local rings which is formally smooth for the
`maximalIdeal B`-adic topology is flat. -/
theorem flat_of_formallySmooth_for_maximalIdeal_adic
    (f : A →+* B) [IsLocalHom f]
    (hfs : f.formally_smooth_for_adic (maximalIdeal B)) :
    f.Flat := sorry

end

end RingHom
