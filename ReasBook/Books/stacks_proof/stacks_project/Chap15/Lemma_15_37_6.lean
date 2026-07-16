import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.37.6:
- primary domain: adic topologies and topological formal smoothness of commutative ring maps.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmoothTopologically.of_le`
  * `RingHom.formally_smooth_for_adic`
  * `Ideal.adicTopology_mono`
- best owner abstraction: the owner for the present bridge is
  `RingHom.formally_smooth_for_adic`; the monotonicity theorem belongs next to that owner and is
  derived from the core theorem `RingHom.FormallySmoothTopologically.of_le`.
- primitive data: the ring map `f`, the two ideals `𝔫 ≤ 𝔫'`, and formal smoothness for the finer
  `𝔫`-adic topology.
- derived API: monotonicity for `RingHom.formally_smooth_for_adic`.
- source/core/bridge triage:
  * `source-facing`: formal smoothness for the `𝔫'`-adic topology.
  * `core/canonical`: `RingHom.FormallySmoothTopologically.of_le`.
  * `bridge/view`: `RingHom.formally_smooth_for_adic` and its monotonicity theorem.
-/

/- Lemma 15.37.6: if `R → S` is formally smooth for the `𝔫`-adic topology and `𝔫 ≤ 𝔫'`, then it
is formally smooth for the `𝔫'`-adic topology. This source-facing bridge is now used directly from
the owner file of `RingHom.formally_smooth_for_adic`. -/
recall RingHom.formally_smooth_for_adic_of_le
