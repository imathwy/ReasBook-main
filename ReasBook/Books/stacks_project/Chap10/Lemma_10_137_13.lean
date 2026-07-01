import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: smooth commutative ring homomorphisms and their stability properties;
- sampled owner declarations:
  `RingHom.Smooth`,
  `RingHom.Smooth.comp`,
  `Algebra.Smooth`,
  `Algebra.Smooth.comp`;
- best owner abstraction: `RingHom.Smooth` for ring-hom statements, with `Algebra.Smooth` as the
  algebra-side owner bridged by mathlib;
- primitive data: smoothness of the two ring maps being composed;
- derived API: smoothness of the composite map;

Source/core/bridge triage:
- `source-facing`: the composition statement below;
- `core/canonical`: `Algebra.Smooth.comp`;
- `bridge/view`: `RingHom.Smooth.comp`, which is exactly the right owner-level surface for this
  ring-hom formulation.
-/

/- Lemma 10.137.13: a composition of smooth ring maps is smooth. This is exactly the canonical
mathlib theorem `RingHom.Smooth.comp`. -/
recall RingHom.Smooth.comp
