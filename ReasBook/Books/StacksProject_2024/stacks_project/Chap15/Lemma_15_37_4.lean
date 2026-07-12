import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.37.4:
- primary domain: adic completion and adic formal smoothness of commutative ring maps.
- inspected owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.adicCompletionMap`
  * `RingHom.adicCompletionMap_comp`
  * `AdicCompletion.liftRingHom`
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the source-facing owner for the
  formal-smoothness statements, while `RingHom.adicCompletionMap` is the owner-level bridge from a
  continuous adic ring map to the induced map on completions; the lower-level completion lift API
  `AdicCompletion.liftRingHom` is core/canonical implementation.
- primitive data: the ideals `I`, `J`, the ring map `f`, finite generation of `I` and `J`, and
  the continuity witness from the `I`-adic topology to the `J`-adic topology.
- derived API: the canonical completion map `R^∧ → S^∧`, its extension property, and the `TFAE`
  completion-invariance statement.
- source/core/bridge triage:
  * `source-facing`: the completion-invariance `TFAE` below.
  * `core/canonical`: `AdicCompletion.liftRingHom`.
  * `bridge/view`: `RingHom.adicCompletionMap` and
    `RingHom.formally_smooth_for_adic_tfae_completion_invariance`. -/

/- Lemma 15.37.4 now lives with the owner-level bridge API on `RingHom`, so this file is a direct
canonical check of that theorem. -/
#check RingHom.formally_smooth_for_adic_tfae_completion_invariance
