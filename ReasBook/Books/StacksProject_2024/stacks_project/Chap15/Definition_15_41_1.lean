import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_166_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_164_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_166_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_157_5

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

namespace Algebra

section GeometricallyRegular

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Definition 15.41.1: the canonical map from a field to the residue field at any of
its prime ideals is bijective. -/
lemma residueField_to_self_bijective_of_field_prime (p : PrimeSpectrum k) :
    Function.Bijective (IsScalarTower.toAlgHom k k p.asIdeal.ResidueField) := by
  constructor
  · exact RingHom.injective _
  · have hp : p = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
    subst hp
    simpa using Ideal.algebraMap_residueField_surjective (⊥ : Ideal k)

/-- Helper for Definition 15.41.1: over a field, the residue field at any prime is canonically the
field itself. -/
noncomputable def residueField_algEquiv_self_of_field_prime (p : PrimeSpectrum k) :
    p.asIdeal.ResidueField ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (IsScalarTower.toAlgHom k k p.asIdeal.ResidueField)
    (residueField_to_self_bijective_of_field_prime (k := k) p)).symm

/-- Helper for Definition 15.41.1: after identifying the residue field of a prime of a field with
the field itself, geometric regularity over `k` may be read as geometric regularity over that
residue field. -/
lemma field_geometricallyRegular_over_residueField [IsGeometricallyRegular k A]
    (p : PrimeSpectrum k) :
    let _ : Algebra p.asIdeal.ResidueField k :=
      (residueField_algEquiv_self_of_field_prime (k := k) p).toRingHom.toAlgebra
    let _ : Algebra p.asIdeal.ResidueField A :=
      ((algebraMap k A).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
    let _ : IsScalarTower p.asIdeal.ResidueField k A := IsScalarTower.of_algebraMap_eq' rfl
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField A := by
  let eκ := residueField_algEquiv_self_of_field_prime (k := k) p
  let _ : Algebra p.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField A :=
    ((algebraMap k A).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
  let _ : IsScalarTower p.asIdeal.ResidueField k A := IsScalarTower.of_algebraMap_eq' rfl
  let φ : p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] k :=
    IsScalarTower.toAlgHom p.asIdeal.ResidueField p.asIdeal.ResidueField k
  let eκ' : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] k :=
    AlgEquiv.ofBijective φ <| by
      simpa [φ, RingHom.algebraMap_toAlgebra] using eκ.bijective
  let _ : Algebra.IsSeparable p.asIdeal.ResidueField k :=
    AlgEquiv.Algebra.isSeparable eκ'
  -- Apply the separable base-field invariance theorem with the transported residue-field action.
  simpa using
    ((Algebra.isGeometricallyRegular_iff_of_isSeparable : _ ↔ _).2
      (inferInstance : Algebra.IsGeometricallyRegular k A))

/-- Helper for Definition 15.41.1: over a field, the raw fiber `κ(p) ⊗[k] A` is canonically the
same algebra as `A` after transporting scalars along the residue-field equivalence. -/
noncomputable def field_fiber_algEquiv (p : PrimeSpectrum k) :
    let _ : Algebra p.asIdeal.ResidueField k :=
      (residueField_algEquiv_self_of_field_prime (k := k) p).toRingHom.toAlgebra
    let _ : Algebra p.asIdeal.ResidueField A :=
      ((algebraMap k A).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
    let _ : IsScalarTower p.asIdeal.ResidueField k A := IsScalarTower.of_algebraMap_eq' rfl
    p.asIdeal.Fiber A ≃ₐ[p.asIdeal.ResidueField] A := by
  let eκ := residueField_algEquiv_self_of_field_prime (k := k) p
  let _ : Algebra p.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField A :=
    ((algebraMap k A).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
  let _ : IsScalarTower p.asIdeal.ResidueField k A := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower k p.asIdeal.ResidueField A := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap k A x =
      algebraMap p.asIdeal.ResidueField A (algebraMap k p.asIdeal.ResidueField x)
    change algebraMap k A x =
      algebraMap k A (algebraMap p.asIdeal.ResidueField k (algebraMap k p.asIdeal.ResidueField x))
    rw [show algebraMap p.asIdeal.ResidueField k (algebraMap k p.asIdeal.ResidueField x) = x by
      simpa [RingHom.algebraMap_toAlgebra] using eκ.commutes x]
  let _ : IsScalarTower k p.asIdeal.ResidueField p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap k p.asIdeal.ResidueField x =
        algebraMap p.asIdeal.ResidueField p.asIdeal.ResidueField
          (algebraMap k p.asIdeal.ResidueField x)
      simp
  let _ : IsScalarTower p.asIdeal.ResidueField k p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      apply eκ.injective
      simp [RingHom.algebraMap_toAlgebra]
  -- Once `A` carries the transported `κ(p)`-algebra structure, the fiber is the left tensor unit.
  simpa using Algebra.TensorProduct.lidOfCompatibleSMul k p.asIdeal.ResidueField A

/-- Helper for Definition 15.41.1: if `A` is geometrically regular over a field `k`, then the
fiber over any prime of `k` is geometrically regular over the corresponding residue field. -/
lemma field_fiber_isGeometricallyRegular [IsGeometricallyRegular k A] (p : PrimeSpectrum k) :
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
  let eκ := residueField_algEquiv_self_of_field_prime (k := k) p
  let _ : Algebra p.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField A :=
    ((algebraMap k A).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
  let _ : IsScalarTower p.asIdeal.ResidueField k A := IsScalarTower.of_algebraMap_eq' rfl
  have hA :
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField A :=
    field_geometricallyRegular_over_residueField (k := k) (A := A) p
  have e : p.asIdeal.Fiber A ≃ₐ[p.asIdeal.ResidueField] A :=
    field_fiber_algEquiv (k := k) (A := A) p
  -- Route correction: keep the theorem surface on the ambient `k`-algebra and move the
  -- transported residue-field structure entirely inside the proof.
  refine
    { isRegularRing_baseChange := by
        intro K
        intro _ _ _ _
        let T₁ := TensorProduct p.asIdeal.ResidueField K (p.asIdeal.Fiber A)
        let T₂ := TensorProduct p.asIdeal.ResidueField K A
        let eK : T₁ ≃ₐ[p.asIdeal.ResidueField] T₂ :=
          Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[p.asIdeal.ResidueField] K) e
        have hregA : IsRegularRing T₂ := by
          let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField A := hA
          infer_instance
        let _ : IsRegularRing T₂ := hregA
        exact isRegularRing_of_faithfullyFlat eK.toRingHom
          (RingHom.FaithfullyFlat.of_bijective eK.bijective) }

/-- Helper for Definition 15.41.1: the algebra structure induced by `algebraMap k A` agrees with
the ambient `k`-algebra structure on `A`. -/
lemma algebraMap_toAlgebra_eq_inferInstance :
    (algebraMap k A).toAlgebra = (inferInstance : Algebra k A) := by
  -- Both algebra structures have the same structure map, so extensionality identifies them.
  apply Algebra.algebra_ext
  intro x
  rfl

/-- Helper for Definition 15.41.1: geometric regularity transports to the explicit algebra
structure coming from `(algebraMap k A).toAlgebra`. -/
lemma isGeometricallyRegular_toAlgebra [IsGeometricallyRegular k A] :
    @Algebra.IsGeometricallyRegular k A _ _ ((algebraMap k A).toAlgebra) := by
  -- Route correction: rewrite the class parameter to the ambient algebra structure before
  -- asking typeclass search for the existing geometric-regularity instance.
  let hGeom : Algebra.IsGeometricallyRegular k A := inferInstance
  let hAlg : (algebraMap k A).toAlgebra = (inferInstance : Algebra k A) :=
    algebraMap_toAlgebra_eq_inferInstance (k := k) (A := A)
  exact hAlg ▸ hGeom

/-- Helper for Definition 15.41.1: the fiber clause for `algebraMap k A` is exactly the field
fiber geometric-regularity statement after installing the explicit algebra structure. -/
lemma algebraMap_fiber_isGeometricallyRegular [IsGeometricallyRegular k A]
    (p : PrimeSpectrum k) :
    let _ : Algebra k A := (algebraMap k A).toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
  -- Install the explicit `k`-algebra structure and transport geometric regularity to it once.
  let hGeom :
      @Algebra.IsGeometricallyRegular k A _ _ ((algebraMap k A).toAlgebra) :=
    isGeometricallyRegular_toAlgebra (k := k) (A := A)
  letI : Algebra k A := (algebraMap k A).toAlgebra
  letI : Algebra.IsGeometricallyRegular k A := hGeom
  exact field_fiber_isGeometricallyRegular (k := k) (A := A) p

-- Proof sketch: every `k`-algebra is flat over the field `k`, and the unique fiber of
-- `k → A` over `(0)` is `A` itself, which is regular by
-- `isRegularRing_of_isGeometricallyRegular`.
/-- A geometrically regular algebra over a field gives a regular ring map from that field. -/
instance [IsGeometricallyRegular k A] : (algebraMap k A).IsRegularRingMap := by
  -- Route correction: keep the source-faithful field-fiber proof and isolate the only transport
  -- issue in concrete rewrite helpers for `(algebraMap k A).toAlgebra`.
  refine
    { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
      isGeometricallyRegular_fiber := fun p ↦ ?_ }
  -- The exact fiber clause is now a direct call to the adapter lemma.
  exact algebraMap_fiber_isGeometricallyRegular (k := k) (A := A) p

end GeometricallyRegular

end Algebra
