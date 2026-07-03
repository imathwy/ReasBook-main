import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Domain-style sampling:
- primary domain: Noetherian complete local domains, the chapter owner `IsJ0Ring`, and the
  finite regular complete-local subring / fraction-field descent machinery used to prove openness
  of the regular locus;
- sampled owner and bridge declarations of the same kind:
  `IsJ0Ring`,
  `PrimeSpectrum.regularLocus`,
  `exists_finite_regular_completeLocalSubring`,
  `Algebra.isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension`;
- best owner abstraction: the public statement should stay on the chapter owner `IsJ0Ring`,
  with the finite complete-local subring and the separable/purely inseparable fraction-field
  analysis kept internal to the proof route;
- source/core/bridge triage:
  * source-facing: the conclusion that a Noetherian complete local domain is `J-0`;
  * core/canonical: the chapter owner `IsJ0Ring`;
  * bridge/view: the finite regular complete local subring from Cohen structure, the separability
    bridge on fraction fields, and the purely inseparable derivation/adjoin-root regularity step;
- primitive vs. derived: the primitive public data are exactly the ambient assumptions
  `[IsNoetherianRing A]`, `[IsCompleteLocalRing A]`, and `[IsDomain A]`. The finite regular
  complete local subring, the separable versus purely inseparable case split on the fraction
  field extension, and the derivation witness used in the purely inseparable branch are all
  derived implementation data supplied by the chapter bridge lemmas, so this file should keep
  the public surface on `IsJ0Ring A` rather than introducing a parallel wrapper API.
-/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsDomain A]

-- Proof sketch: choose a finite regular complete local subring `A₀ ⊆ A` using
-- Lemma `10.160.11`.
-- If the induced fraction-field extension is separable, apply Lemma `15.47.5` to descend `J-0`
-- from the regular ring `A₀`. Otherwise, pass to a minimal purely inseparable subextension,
-- produce a derivation on the intermediate ring by Lemma `15.48.5`, and apply Lemma `15.48.4` to
-- obtain regularity on a nonempty open subset of `Spec A`; since the intermediate ring is already
-- `J-0`, this yields `IsJ0Ring A`.
/-- Lemma 15.48.6: a Noetherian complete local domain is `J-0`. -/
theorem isJ0Ring_of_noetherian_completeLocalDomain : IsJ0Ring A := sorry

end
