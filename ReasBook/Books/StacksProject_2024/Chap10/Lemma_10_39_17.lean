import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 10.39.17: a flat local ring homomorphism between local rings is faithfully flat.

Layering for this item:
* source-facing: a flat local ring homomorphism of local rings is faithfully flat;
* core/canonical owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
* bridge/view: the ring-hom statement is the canonical algebraized view for `algebraMap`.
-/
recall Module.FaithfullyFlat.of_flat_of_isLocalHom
