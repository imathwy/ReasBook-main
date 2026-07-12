import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap10.Lemma_10_39_7
import StacksProject_2024.Chap10.Lemma_10_166_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

namespace RingHom.IsRegularRingMap

universe u v w x

section

variable {R : Type u} {R' : Type v} {Λ : Type w}
variable [CommRing R] [CommRing R'] [CommRing Λ]
variable [Algebra R Λ] [Algebra R R']
variable [Algebra.EssFiniteType R R']

/- Domain triage:
- primary domain: regular ring maps and tensor-product base change in commutative algebra;
- sampled owner declarations of the same kind:
  `RingHom.IsRegularRingMap`,
  `Algebra.IsGeometricallyRegular`,
  `Algebra.EssFiniteType`;
- best owner abstraction: the regularity datum already lives on the ring hom
  `algebraMap R Λ : R →+* Λ`, so the source-facing tensor-product statement should be exposed as a
  theorem in the owner namespace `RingHom.IsRegularRingMap` rather than through a parallel
  algebra-only wrapper namespace;
- primitive data: the algebra structures `R → Λ` and `R → R'`, together with
  `[Algebra.EssFiniteType R R']` and a proof `h : (algebraMap R Λ).IsRegularRingMap`;
- derived API: the regularity of the canonical base-change map
  `(algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap`, exposed by the exact owner theorem below with
  its essentially-finite-type hypothesis kept visible on the theorem surface.

Layering:
- `baseChange_of_essFiniteType` is `source-facing`;
- the core/canonical owner is `RingHom.IsRegularRingMap`;
- there is no additional bridge/view layer beyond the canonical tensor-product base change.
 -/

/-- Helper for Lemma 15.41.3 (Regular maps and base change): for a prime of an essentially finite
type `R`-algebra `R'`, the induced residue-field extension over the contracted prime is again
essentially finite type. -/
lemma residueField_extension_essFiniteType (p' : PrimeSpectrum R') :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    Algebra.EssFiniteType p.asIdeal.ResidueField p'.asIdeal.ResidueField := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  -- First pass to the residue field as an essentially finite type `R'`-algebra.
  let _ : Algebra.EssFiniteType R' p'.asIdeal.ResidueField := inferInstance
  let _ : Algebra.EssFiniteType R p'.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp R R' p'.asIdeal.ResidueField
  -- Then descend along the contracted residue-field map.
  exact
    Algebra.EssFiniteType.of_comp R p.asIdeal.ResidueField p'.asIdeal.ResidueField

/-- Helper for Lemma 15.41.3 (Regular maps and base change): an equality of `R`-algebra
structures on `Λ` transports geometric regularity of the source fiber. -/
lemma source_fiber_isGeometricallyRegular_of_algebra_eq (p : PrimeSpectrum R)
    {A₁ A₂ : Algebra R Λ} (hA : A₁ = A₂) :
    (let _ : Algebra R Λ := A₁;
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)) →
    (let _ : Algebra R Λ := A₂;
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)) := by
  subst hA
  intro hGeom
  exact hGeom

/-- Helper for Lemma 15.41.3 (Regular maps and base change): shrinking the universe of an
essentially finite type field extension is legitimate because the field is small after presenting
it as a localization of a finite type subalgebra. -/
lemma essFiniteType_field_small
    {κ : Type u} [Field κ] (K : Type x) [Field K] [Algebra κ K]
    [Algebra.EssFiniteType κ K] :
    Small.{max u w} K := by
  classical
  have hsmallκ : Small.{max u w} κ := by
    let _ : Small.{u} κ := small_self κ
    exact small_lift.{u, w, u} κ
  let _ : Small.{max u w} κ := hsmallκ
  obtain ⟨K₀, M, hK₀, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra (R := κ) (S := K)).mp inferInstance
  let _ : Algebra.FiniteType κ K₀ := hK₀
  let _ : IsLocalization M K := hloc
  let _ : Small.{max u w} K₀ := Algebra.FiniteType.small (R := κ) (S := K₀)
  have hsmallLoc : Small.{max u w} (Localization M) :=
    small_of_surjective Localization.mkHom_surjective
  let eLoc : Localization M ≃+* K := (IsLocalization.algEquiv M (Localization M) K).toRingEquiv
  exact small_of_surjective eLoc.surjective

/-- Helper for Lemma 15.41.3 (Regular maps and base change): shrinking the universe of an
essentially finite type field extension preserves essential finite type over the same base
field. -/
lemma shrunk_test_field_essFiniteType
    {κ : Type u} [Field κ] (K : Type x) [Field K] [Algebra κ K]
    [Algebra.EssFiniteType κ K] [Small.{max u w} K] :
    Algebra.EssFiniteType κ (Shrink.{max u w} K) := by
  let eK : Shrink.{max u w} K ≃ₐ[κ] K := Shrink.algEquiv κ K
  -- Transport the finite-type structure across the canonical shrink equivalence once.
  exact (Algebra.EssFiniteType.iff_of_algEquiv eK).2 inferInstance

/-- Helper for Lemma 15.41.3 (Regular maps and base change): shrinking the left field factor only
induces the expected ring equivalence on the source-fiber tensor product. -/
noncomputable abbrev shrink_source_fiber_tensor_ringEquiv
    {κ : Type u} [Field κ] {A : Type w} [CommRing A] [Algebra κ A]
    (K : Type x) [Field K] [Algebra κ K] [Small.{max u w} K] :
    (Shrink.{max u w} K) ⊗[κ] A ≃+* K ⊗[κ] A :=
  (Algebra.TensorProduct.congr
      (Shrink.algEquiv κ K)
      (AlgEquiv.refl : A ≃ₐ[κ] A)).toRingEquiv

/-- Helper for Lemma 15.41.3 (Regular maps and base change): after shrinking the target test field
to the source universe once, the common tensor model `K ⊗[R] Λ` is regular. -/
lemma common_tensor_regular_of_source_regular
    (h : (algebraMap R Λ).IsRegularRingMap) (p' : PrimeSpectrum R')
    (K : Type (max v w)) [Field K] [Algebra p'.asIdeal.ResidueField K]
    [Algebra R' K] [Algebra R K] [IsScalarTower R' p'.asIdeal.ResidueField K]
    [IsScalarTower R R' K] [Algebra.EssFiniteType p'.asIdeal.ResidueField K] :
    IsRegularRing (K ⊗[R] Λ) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let φ : p.asIdeal.ResidueField →+* p'.asIdeal.ResidueField :=
    algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
  let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField := inferInstance
  let _ : Algebra p.asIdeal.ResidueField K :=
    RingHom.toAlgebra ((algebraMap p'.asIdeal.ResidueField K).comp φ)
  let _ : IsScalarTower p.asIdeal.ResidueField p'.asIdeal.ResidueField K :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField p'.asIdeal.ResidueField := by
    simpa [p] using residueField_extension_essFiniteType (R := R) (R' := R') p'
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField K :=
    Algebra.EssFiniteType.comp p.asIdeal.ResidueField p'.asIdeal.ResidueField K
  let _ : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun x ↦ by
      have hmap :
          algebraMap R' p'.asIdeal.ResidueField (algebraMap R R' x) =
            algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
              (algebraMap R p.asIdeal.ResidueField x) := by
        simpa [p] using
          (Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal (algebraMap R R') rfl x).symm
      calc
        (algebraMap R K) x = (algebraMap R' K) (algebraMap R R' x) := by
          simpa using DFunLike.congr_fun (IsScalarTower.algebraMap_eq R R' K) x
        _ =
            (algebraMap p'.asIdeal.ResidueField K)
              (algebraMap R' p'.asIdeal.ResidueField (algebraMap R R' x)) := by
          simpa using
            DFunLike.congr_fun (IsScalarTower.algebraMap_eq R' p'.asIdeal.ResidueField K)
              (algebraMap R R' x)
        _ =
            (algebraMap p'.asIdeal.ResidueField K)
              (algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
                (algebraMap R p.asIdeal.ResidueField x)) := by
          exact congrArg (algebraMap p'.asIdeal.ResidueField K) hmap
        _ = (algebraMap p.asIdeal.ResidueField K) (algebraMap R p.asIdeal.ResidueField x) := by
          simpa using
            (DFunLike.congr_fun
              (IsScalarTower.algebraMap_eq
                p.asIdeal.ResidueField p'.asIdeal.ResidueField K)
              (algebraMap R p.asIdeal.ResidueField x)).symm
  let hsourceExplicit :
      let _ : Algebra R Λ := (algebraMap R Λ).toAlgebra;
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ) :=
    h.isGeometricallyRegular_fiber p
  let hAlgSource : (algebraMap R Λ).toAlgebra = (inferInstance : Algebra R Λ) := by
    -- Normalize the source algebra structure once before invoking the geometric-regularity
    -- criterion on the source fiber.
    apply Algebra.algebra_ext
    intro x
    rfl
  have hsource :
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ) :=
    source_fiber_isGeometricallyRegular_of_algebra_eq
      (R := R) (Λ := Λ) (p := p) hAlgSource hsourceExplicit
  let _ : Small.{max u w} K :=
    essFiniteType_field_small (κ := p.asIdeal.ResidueField) K
  let Ks := Shrink.{max u w} K
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField Ks :=
    shrunk_test_field_essFiniteType
      (κ := p.asIdeal.ResidueField) K
  have hsourceRegShrink :
      IsRegularRing (Ks ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) :=
    -- Apply geometric regularity exactly on the source fiber, after shrinking only the test field.
    (Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing.mp
      hsource) Ks
  let eShrink :
      Ks ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ ≃+*
        K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ :=
    shrink_source_fiber_tensor_ringEquiv
      (κ := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber Λ) K
  let _ : IsRegularRing (Ks ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) := hsourceRegShrink
  have hsourceReg :
      IsRegularRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) := by
    let fShrink :
        K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ →+*
          Ks ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ :=
      eShrink.symm.toRingHom
    have hfShrink : fShrink.FaithfullyFlat := by
      exact RingHom.FaithfullyFlat.of_bijective eShrink.symm.bijective
    -- Descend regularity across the shrink-induced tensor equivalence to recover the original
    -- test field `K`.
    exact isRegularRing_of_faithfullyFlat fShrink hfShrink
  let eSource :
      K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ ≃+* K ⊗[R] Λ := by
    -- This is the standard cancellation equivalence from the source fiber tensor model to the
    -- common ambient tensor product used in the main theorem.
    simpa using
      (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField
        p.asIdeal.ResidueField K Λ).toRingEquiv
  let _ : IsRegularRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) := hsourceReg
  let fSource : K ⊗[R] Λ →+* K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ :=
    eSource.symm.toRingHom
  have hfSource : fSource.FaithfullyFlat := by
    exact RingHom.FaithfullyFlat.of_bijective eSource.symm.bijective
  -- Descend regularity from the source-fiber tensor model to the ambient tensor product
  -- `K ⊗[R] Λ`.
  exact isRegularRing_of_faithfullyFlat fSource hfSource

/-- Helper for Lemma 15.41.3 (Regular maps and base change): the target fiber test ring over `p'`
identifies with the same ambient base change `K ⊗[R] Λ`. -/
noncomputable abbrev fiber_baseChange_ringEquiv (p' : PrimeSpectrum R')
    (K : Type (max v w)) [Field K] [Algebra p'.asIdeal.ResidueField K] :
    let _ : Algebra R' K :=
      RingHom.toAlgebra
        ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
    let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
    let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
    K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) ≃+* K ⊗[R] Λ :=
  let _ : Algebra R' K :=
    RingHom.toAlgebra
      ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
  let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
  let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
  -- First cancel the `p'`-fiber, then cancel the remaining tensor base change along `R → R'`.
  ((Algebra.TensorProduct.cancelBaseChange R' p'.asIdeal.ResidueField
      p'.asIdeal.ResidueField K (R' ⊗[R] Λ)).toRingEquiv).trans
    ((Algebra.TensorProduct.cancelBaseChange R R' K K Λ).toRingEquiv)

/-- Helper for Lemma 15.41.3 (Regular maps and base change): an equality of `R'`-algebra
structures on `R' ⊗[R] Λ` transports regularity of the target test ring. -/
lemma target_tensor_isRegular_of_algebra_eq (p' : PrimeSpectrum R')
    (K : Type (max v w)) [Field K] [Algebra p'.asIdeal.ResidueField K]
    {A₁ A₂ : Algebra R' (R' ⊗[R] Λ)} (hA : A₁ = A₂) :
    (let _ : Algebra R' (R' ⊗[R] Λ) := A₁;
      IsRegularRing
        (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ))) →
    (let _ : Algebra R' (R' ⊗[R] Λ) := A₂;
      IsRegularRing
        (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ))) := by
  subst hA
  intro hReg
  exact hReg

-- Proof sketch: flatness is preserved by tensor base change along `R → R'`. For each prime
-- `p' : Spec R'`, compare the fiber of `R' → R' ⊗[R] Λ` over `p'` with the base change of the
-- fiber of `R → Λ` over the image prime in `R`, then use geometric regularity of fibers together
-- with the essentially-finite-type hypothesis on `R → R'`.
/-- Lemma 15.41.3 (Regular maps and base change): the base change of a regular ring map along an
essentially finite type ring map is again a regular ring map. -/
@[stacks 07C1]
theorem baseChange_of_essFiniteType (h : (algebraMap R Λ).IsRegularRingMap) :
    (algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap := by
  refine
    (RingHom.isRegularRingMap_iff_flat_and_geometricallyRegular_fiber
      (f := algebraMap R' (R' ⊗[R] Λ))).mpr ?_
  constructor
  · -- Base change preserves flatness, so the tensor-product structure map stays flat.
    let _ : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp <| by
      simpa using h.toFlat
    let _ : Module.Flat R' (R' ⊗[R] Λ) := Module.Flat.baseChange R R' Λ
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · intro p'
    let A₁ : Algebra R' (R' ⊗[R] Λ) := (algebraMap R' (R' ⊗[R] Λ)).toAlgebra
    let A₂ : Algebra R' (R' ⊗[R] Λ) := Algebra.TensorProduct.leftAlgebra
    have hAlgTensor : A₁ = A₂ := by
      -- Compare the ambient tensor algebra with the explicit algebraMap algebra structure once.
      apply Algebra.algebra_ext
      intro x
      rfl
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    let φ : p.asIdeal.ResidueField →+* p'.asIdeal.ResidueField :=
      algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
    -- Route correction: follow the textbook proof literally and compare both source and target
    -- test rings with the common ambient tensor product `K ⊗[R] Λ`.
    rw [Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing]
    intro K
    intro _ _ _
    let _ : Algebra p.asIdeal.ResidueField K :=
      RingHom.toAlgebra ((algebraMap p'.asIdeal.ResidueField K).comp φ)
    let _ : Algebra R' K :=
      RingHom.toAlgebra
        ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
    let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
    let _ : IsScalarTower p.asIdeal.ResidueField p'.asIdeal.ResidueField K :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun x ↦ by
        have hmap :
            algebraMap R' p'.asIdeal.ResidueField (algebraMap R R' x) =
              algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
                (algebraMap R p.asIdeal.ResidueField x) := by
          simpa [p] using
            (Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal (algebraMap R R') rfl x).symm
        exact congrArg (algebraMap p'.asIdeal.ResidueField K) hmap
    have hKR : IsRegularRing (K ⊗[R] Λ) :=
      common_tensor_regular_of_source_regular
        (R := R) (R' := R') (Λ := Λ) h p' K
    let _ : IsRegularRing (K ⊗[R] Λ) := hKR
    have htargetA₂ :
        let _ : Algebra R' (R' ⊗[R] Λ) := A₂
        IsRegularRing
          (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := by
      let _ : Algebra R' (R' ⊗[R] Λ) := A₂
      let eTarget :
          K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) ≃+* K ⊗[R] Λ := by
        -- Cancel the target fiber and the remaining tensor base change to reach `K ⊗[R] Λ`.
        simpa [Ideal.Fiber] using
          fiber_baseChange_ringEquiv (R := R) (R' := R') (Λ := Λ) p' (K := K)
      let fTarget :
          K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) →+* K ⊗[R] Λ :=
        eTarget.toRingHom
      have hfTarget : fTarget.FaithfullyFlat := by
        exact RingHom.FaithfullyFlat.of_bijective eTarget.bijective
      -- Descend regularity from the common tensor model to the target fiber test ring.
      exact isRegularRing_of_faithfullyFlat fTarget hfTarget
    exact
      target_tensor_isRegular_of_algebra_eq
        (R := R) (R' := R') (Λ := Λ) (p' := p') (K := K)
        (A₁ := A₂) (A₂ := A₁) hAlgTensor.symm htargetA₂

end

end RingHom.IsRegularRingMap
