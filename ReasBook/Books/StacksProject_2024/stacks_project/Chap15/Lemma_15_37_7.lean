import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.37.7:
- primary domain: topological formal smoothness of continuous homomorphisms of commutative
  topological rings.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmoothTopologically.comp`
  * `RingHom.FormallySmoothTopologically.id`
  * `RingHom.formally_smooth_for_adic`
- best owner abstraction: the source-facing and canonical owner for this file is
  `RingHom.FormallySmoothTopologically`; this lemma is the owner-level derived API
  `RingHom.FormallySmoothTopologically.comp`.
- primitive data: formal smoothness of the two factors.
- derived API: formal smoothness of the composite map, together with the instance form in the
  owner file.

Source/core/bridge triage:
- `source-facing`: the topological lifting property `RingHom.FormallySmoothTopologically`.
- `core/canonical`: the owner-level composition theorem
  `RingHom.FormallySmoothTopologically.comp`.
- `bridge/view`: adic reformulations such as `RingHom.formally_smooth_for_adic`. -/

/- Lemma 15.37.7: a composition of formally smooth continuous homomorphisms of commutative
topological rings is formally smooth. This is exactly the owner-level theorem
`RingHom.FormallySmoothTopologically.comp`. -/
recall RingHom.FormallySmoothTopologically.comp
