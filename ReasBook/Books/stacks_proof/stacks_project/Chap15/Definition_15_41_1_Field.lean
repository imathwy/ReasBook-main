import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_41_1
import stacks_proof.stacks_project.Chap10.Lemma_10_166_6

-- Declarations for the field-algebra support around Definition 15.41.1.

namespace Algebra

section GeometricallyRegular

universe u v

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
