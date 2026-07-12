import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap23.Proposition_23_8_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall / owner check:
- `lean_leansearch` surfaced only the surrounding flat-local infrastructure.
- Local search verified that
  `isCompleteIntersectionLocalRing_iff_source_and_closedFiber_of_flat_localHom` from
  `Proposition_23_8_4` already has exactly the local-ring formulation needed here.
- This item is therefore recall-only: a new local theorem would duplicate the existing owner
  theorem without adding API.
-/

/- Lemma 23.8.9: let `A → B` be a flat local homomorphism of Noetherian local rings. Then the
following are equivalent: `B` is a complete intersection local ring, and `A` together with the
closed fiber `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)` are complete intersection local
rings. This is exactly the canonical theorem
`isCompleteIntersectionLocalRing_iff_source_and_closedFiber_of_flat_localHom`. -/
recall isCompleteIntersectionLocalRing_iff_source_and_closedFiber_of_flat_localHom
