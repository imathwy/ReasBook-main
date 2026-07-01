import Mathlib
import stacks_project.Chap10.Definition_10_166_2
import stacks_project.Chap10.Lemma_10_157_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace RingHom

universe u v

/- Domain-style sampling:
* primary domain: commutative algebra of regular ring maps and fiberwise geometric regularity;
* sampled owner declarations:
  `RingHom.Flat`,
  `IsGeometricallyRegular`,
  `Ideal.Fiber`,
  `Module.Flat`,
  `IsRegularRing`;
* best owner abstraction: this file is the `source-facing` owner for regular ring maps, so the
  owner must be the actual ring hom `f : R →+* S`, not only the pair of rings with an implicit
  algebra structure. The field-level fiber condition already has the canonical owner
  `IsGeometricallyRegular`, so the map-level owner here should keep only flatness of `f` and
  fiberwise geometric regularity as primitive data.

Source/core/bridge triage:
* `source-facing`: `IsRegularRingMap f`;
* `core/canonical`: `RingHom.Flat f`, `Module.Flat R S` for structure maps, and
  `IsGeometricallyRegular` on each fiber;
* `bridge/view`: for `f = algebraMap R S`, the canonical fiber ring
  `p.asIdeal.Fiber S = κ(p) ⊗[R] S`, together with the field-source bridge from
  `IsGeometricallyRegular k A` to `(algebraMap k A).IsRegularRingMap`.
-/

/-- Definition 15.41.1: a ring map `R → S` is regular if it is flat and for every prime
`p ⊂ R` the fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S` is geometrically regular over the
residue field `κ(p)`. In this project, `IsGeometricallyRegular` already packages the
Noetherianity required in the textbook definition of the fibers. -/
@[mk_iff isRegularRingMap_iff_flat_and_geometricallyRegular_fiber]
class IsRegularRingMap {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Prop extends f.Flat where
  /-- Every fiber ring of a regular ring map is geometrically regular over the corresponding
  residue field. -/
  isGeometricallyRegular_fiber (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S)

attribute [instance] IsRegularRingMap.isGeometricallyRegular_fiber

section

variable (R : Type u) [CommRing R]

-- Proof sketch: the identity map is flat, and for each prime `p` the fiber of `R → R` over `p`
-- identifies with the residue field `κ(p)`, which is geometrically regular over itself by the
-- canonical Chapter 10 field instance `IsGeometricallyRegular k k`.
/-- The identity map of a commutative ring is a regular ring map. -/
instance : (RingHom.id R).IsRegularRingMap where
  toFlat := RingHom.Flat.id R
  isGeometricallyRegular_fiber _ := by
    sorry

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}

namespace IsRegularRingMap

/-- Every fiber ring of a regular ring map is a regular ring. -/
instance (p : PrimeSpectrum R) [h : f.IsRegularRingMap] :
    let _ : Algebra R S := f.toAlgebra
    IsRegularRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  have hgeom :
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    h.isGeometricallyRegular_fiber p
  letI : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hgeom
  exact
    (Algebra.isRegularRing_of_isGeometricallyRegular
      p.asIdeal.ResidueField (p.asIdeal.Fiber S) :
        IsRegularRing (p.asIdeal.Fiber S))

/-- The fibers of a regular ring map are regular rings. -/
theorem isRegularRing_fiber (h : f.IsRegularRingMap) (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsRegularRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  letI : f.IsRegularRingMap := h
  infer_instance

/-- The fibers of a regular ring map are reduced rings. -/
theorem isReduced_fiber (h : f.IsRegularRingMap) (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsReduced (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  letI : IsRegularRing (p.asIdeal.Fiber S) := h.isRegularRing_fiber p
  letI : IsNormalRing (p.asIdeal.Fiber S) := isNormalRing_of_isRegularRing
  infer_instance

end IsRegularRingMap

end

end RingHom

namespace Algebra

section GeometricallyRegular

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

-- Proof sketch: every `k`-algebra is flat over the field `k`, and the unique fiber of
-- `k → A` over `(0)` is `A` itself, which is regular by
-- `isRegularRing_of_isGeometricallyRegular`.
/-- A geometrically regular algebra over a field gives a regular ring map from that field. -/
instance [IsGeometricallyRegular k A] : (algebraMap k A).IsRegularRingMap where
  toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
  isGeometricallyRegular_fiber _ := by
    sorry

end GeometricallyRegular

end Algebra
