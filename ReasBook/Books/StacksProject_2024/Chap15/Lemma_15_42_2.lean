import Mathlib
import stacks_project.Chap10.Lemma_10_157_5
import stacks_project.Chap10.Lemma_10_163_8
import stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsNormalRing R]

/-
Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of normality along flat maps
  with normal fibers;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `isNormalRing_of_flat_of_fiber`,
  `RingHom.IsRegularRingMap.isRegularRing_fiber`,
  `isNormalRing_of_isRegularRing`,
  `IsNormalRing`;
- best owner abstraction: the source-facing hypothesis is a regular ring map
  `f : R →+* S`, while the
  canonical owner theorem for the conclusion is `isNormalRing_of_flat_of_fiber`;
- primitive data: the regular-map owner assumption on `f` and the normal/Noetherian hypotheses on
  `R` and `S`;
- derived API: fiberwise regularity from `RingHom.IsRegularRingMap.isRegularRing_fiber`, then
  fiberwise normality from `isNormalRing_of_isRegularRing`.

Layering:
- `source-facing`: `isNormalRing_of_regularRingMap`;
- `core/canonical`: `isNormalRing_of_flat_of_fiber`;
- `bridge/view`: the canonical implication chain
  `IsGeometricallyRegular → IsRegularRing → IsNormalRing` on each fiber.
-/

-- Proof sketch: a regular ring map `f : R →+* S` is flat, and each fiber ring is geometrically
-- regular over the
-- corresponding residue field, hence regular and therefore normal in the Noetherian case. Apply
-- `isNormalRing_of_flat_of_fiber` to the flat map `f`, using the algebra-side fiber
-- regularity theorem induced by `IsRegularRingMap`.
/-- Lemma 15.42.2: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is Noetherian and
normal, then `S` is normal. -/
theorem isNormalRing_of_regularRingMap
    (f : R →+* S) [f.IsRegularRingMap] : IsNormalRing S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  refine isNormalRing_of_flat_of_fiber fun p ↦ by
    let _ : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
    exact show IsNormalRing (p.asIdeal.Fiber S) from isNormalRing_of_isRegularRing

end

end Algebra
