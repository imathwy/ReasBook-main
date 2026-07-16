import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_166_2
import stacks_proof.stacks_project.Chap10.Lemma_10_164_4
import stacks_proof.stacks_project.Chap10.Lemma_10_157_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

section GeometricallyRegularTransport

universe u v

variable {k : Type u} {A : Type v} {B : Type v}
variable [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- Helper for Definition 15.41.1: geometric regularity is preserved under `k`-algebra
equivalence. -/
theorem isGeometricallyRegular_of_algEquiv (e : A ≃ₐ[k] B) [IsGeometricallyRegular k B] :
    IsGeometricallyRegular k A := by
  refine
    { isRegularRing_baseChange := by
        intro K
        intro _ _ _ _
        let T₁ := TensorProduct k K A
        let T₂ := TensorProduct k K B
        let eK : T₁ ≃ₐ[k] T₂ :=
          Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e
        have hregB : IsRegularRing T₂ := by
          infer_instance
        let _ : IsRegularRing T₂ := hregB
        -- Route correction: use the bijective tensor-product equivalence as a faithfully flat map
        -- and descend regularity from the transported base change.
        exact isRegularRing_of_faithfullyFlat eK.toRingHom
          (RingHom.FaithfullyFlat.of_bijective eK.bijective) }

end GeometricallyRegularTransport

end Algebra

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
@[stacks 07BZ, mk_iff isRegularRingMap_iff_flat_and_geometricallyRegular_fiber]
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

/-- Helper for Definition 15.41.1: the fiber of the identity map is canonically the residue
field. -/
noncomputable def fiber_id_algEquiv_residueField (p : PrimeSpectrum R) :
    p.asIdeal.Fiber R ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField := by
  -- The identity fiber is the tensor product `κ(p) ⊗[R] R`, so the right-unit tensor equivalence
  -- collapses it to `κ(p)`.
  simpa using
    (Algebra.TensorProduct.rid R p.asIdeal.ResidueField p.asIdeal.ResidueField)

/-- Helper for Definition 15.41.1: the fiber of the identity map over a prime is geometrically
regular over the residue field because `κ(p) ⊗[R] R` is canonically `κ(p)`. -/
lemma fiber_id_isGeometricallyRegular (p : PrimeSpectrum R) :
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber R) := by
  -- Transport the canonical field regularity instance across the fiber identification.
  exact Algebra.isGeometricallyRegular_of_algEquiv
    (fiber_id_algEquiv_residueField (R := R) p)

-- Proof sketch: the identity map is flat, and for each prime `p` the fiber of `R → R` over `p`
-- identifies with the residue field `κ(p)`, which is geometrically regular over itself by the
-- canonical Chapter 10 field instance `IsGeometricallyRegular k k`.
/-- The identity map of a commutative ring is a regular ring map. -/
instance : (RingHom.id R).IsRegularRingMap where
  toFlat := RingHom.Flat.id R
  isGeometricallyRegular_fiber p := by
    -- The identity fiber is the residue field, so the helper closes the fiber clause directly.
    simpa using fiber_id_isGeometricallyRegular (R := R) p

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
