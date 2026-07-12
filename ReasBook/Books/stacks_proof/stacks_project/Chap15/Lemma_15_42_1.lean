import Mathlib
import StacksProject_2024.Chap10.Lemma_10_163_6
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsReduced R]

/- Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of reducedness along flat
  maps with reduced fibers;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `isReduced_of_flat_of_fiber`,
  `RingHom.IsRegularRingMap.isReduced_fiber`,
  `IsReduced`;
- best owner abstraction: the source-facing hypothesis is the actual map owner
  `f.IsRegularRingMap`, with canonical ascent owner `isReduced_of_flat_of_fiber`; reducedness of
  the fibers is derived from the canonical owner theorem
  `RingHom.IsRegularRingMap.isReduced_fiber`.

Source/core/bridge triage:
- `source-facing`: `isReduced_of_regularRingMap`;
- `core/canonical`: `isReduced_of_flat_of_fiber`;
- `bridge/view`: the fiberwise implication chain packaged by
  `RingHom.IsRegularRingMap.isReduced_fiber`.
-/
-- Proof sketch: a regular ring map is flat, and every fiber ring is geometrically regular over the
-- corresponding residue field, hence reduced through the owner-level fiber theorem
-- `RingHom.IsRegularRingMap.isReduced_fiber`.
-- Apply Lemma `10.163.6` to the flat map `R → S`, using the chapter owner lemma
-- `RingHom.IsRegularRingMap.isReduced_fiber` directly to avoid rederiving fiber reducedness
-- locally.
/-- Lemma 15.42.1: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is Noetherian and
reduced, then `S` is reduced. -/
@[stacks 07QK]
theorem isReduced_of_regularRingMap (f : R →+* S) [f.IsRegularRingMap] : IsReduced S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  exact isReduced_of_flat_of_fiber fun p ↦ hRS.isReduced_fiber p

end

end Algebra
