import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_166_2
import stacks_proof.stacks_project.Chap10.Lemma_10_157_5
import stacks_proof.stacks_project.Chap10.Lemma_10_163_8

-- Declarations for this item will be appended below by the statement pipeline.

namespace RingHom

universe u v

/-- Helper for Lemma 15.42.2: a ring map is regular if it is flat and all of its fibers are
geometrically regular over the corresponding residue fields. This theorem-local owner restores the
minimal canonical API needed by the target statement without importing the broken chapter file. -/
class IsRegularRingMap {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Prop extends f.Flat where
  /-- Each fiber of a regular ring map is geometrically regular over the corresponding residue
  field. -/
  isGeometricallyRegular_fiber (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S)

namespace IsRegularRingMap

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}

/-- Helper for Lemma 15.42.2: every fiber of a regular ring map is a regular ring. -/
theorem isRegularRing_fiber (h : f.IsRegularRingMap) (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsRegularRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  -- The defining geometric-regularity hypothesis on the fiber is the only input needed here.
  let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    h.isGeometricallyRegular_fiber p
  -- Geometric regularity over the residue field implies ordinary regularity of the fiber ring.
  exact Algebra.isRegularRing_of_isGeometricallyRegular
    p.asIdeal.ResidueField (p.asIdeal.Fiber S)

end

end IsRegularRingMap

end RingHom

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
omit [IsNoetherianRing R] [IsNoetherianRing S] [IsNormalRing R] in
/-- Helper for Lemma 15.42.2: every fiber of a regular ring map is a normal ring. -/
lemma regularRingMap_fiber_normal
    (f : R →+* S) [f.IsRegularRingMap] (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsNormalRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  -- The regular-map API first gives regularity of the fiber ring.
  letI : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
  -- A regular Noetherian ring is normal.
  exact isNormalRing_of_isRegularRing

/-- Lemma 15.42.2: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is Noetherian and
normal, then `S` is normal. -/
@[stacks 0BFK]
theorem isNormalRing_of_regularRingMap
    (f : R →+* S) [f.IsRegularRingMap] : IsNormalRing S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  -- The ascent theorem reduces normality of `S` to normality of all fibers of `f`.
  exact isNormalRing_of_flat_of_fiber fun p ↦ regularRingMap_fiber_normal (f := f) p

end

end Algebra
