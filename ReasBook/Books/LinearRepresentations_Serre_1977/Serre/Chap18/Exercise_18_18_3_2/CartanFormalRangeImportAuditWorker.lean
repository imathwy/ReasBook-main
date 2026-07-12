import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateSpanProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanRingEquivTransport

/-!
Import-cycle audit for the support theorem at `CartanFormalRange.lean:43`.

Target audited:

```
∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
  (cartanHom k G).range.map e.toAddMonoidHom =
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
```

Checked acyclic candidates requested by the parallel job:

* `ProjectiveCharacterDivisibility` proves Serre 18.5(a) as the projective-character
  regular-restriction divisibility theorem.
* `ProjectiveCartanIntegerDescent` supplies the integer-to-regular-value lattice cast.
* `CartanCokernelSaturation` supplies the exact adapter from fixed-coordinate Cartan range or
  mixed-characteristic span equality to the audited target.
* `CartanCoordinateRangeGenerators` supplies the fixed-coordinate range equality from coordinate
  divisibility plus scaled-indicator generators.
* `ProjectiveCartanSpanStability` identifies the remaining span target with Brauer-coordinate
  stability of Serre's divisibility lattice.
* `ProjectiveCartanCoordinateSpanProducer` packages the full mixed-model fixed-coordinate
  hypotheses that are strong enough for the span target.
* `CartanRingEquivTransport` transports the audited target across residue-field isomorphisms.

None of these files imports `CartanFormalRange.lean`; their direct imports also avoid the
`CartanFormalRange` endpoint chain used by the downstream product/readback files.

Strength gap:

The prioritized source files do not currently contain an unconditional proof of the audited target.
They prove that the target follows from one of the following source-side inputs:

* fixed-coordinate Cartan range equality;
* mixed-characteristic Cartan-coordinate span equality;
* the source hypotheses in
  `fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement`.

The projective-character divisibility theorem gives Serre 18.5(a), but it does not by itself prove
that the chosen Brauer-coordinate map preserves the original divisibility lattice.  The precise
compiled blocker is
`projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_iff_cartanCoordinate_span_eq`.
Using the final cokernel/product endpoint would close the existential target, but that is the
forbidden downstream route for this audit.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeImportAuditWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeImportAuditWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeImportAuditWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Audit adapter: the fixed regular-class coordinate range equality is exactly strong enough to
prove the existential target from `CartanFormalRange.lean:47`, without importing
`CartanFormalRange.lean`. -/
theorem cartanFormalRange_line47_of_fixedCoordinateRange_audit
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
    (p := p) (k := k) (G := G) hrange

/-- Audit adapter: a mixed-characteristic span equality proves the audited target over that
model's residue field. -/
theorem cartanFormalRange_line47_of_span_eq_residueField_audit
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq
    (p := p) (A := A) (K := K) (G := G) hspan

omit [IsAlgClosed k] [CharP k p] in
/-- Audit adapter: combine the mixed-characteristic span bridge with coefficient-field transport
to obtain exactly the target field `k`.  This records the non-circular route and the required
residue-field model input explicitly. -/
theorem cartanFormalRange_line47_of_span_eq_transport_audit
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (e0 : IsLocalRing.ResidueField A ≃+* k)
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
    (p := p) (G := G) e0
    (cartanFormalRange_line47_of_span_eq_residueField_audit
      (p := p) (G := G) (A := A) (K := K) hspan)

omit [IsAlgClosed k] [CharP k p] in
/-- Audit adapter from the strongest fixed-coordinate full mixed-model source package available in
the prioritized imports.  It avoids the final cokernel/product endpoint: the proof goes through
coordinate divisibility and scaled-generator membership, then the saturation bridge. -/
theorem cartanFormalRange_line47_of_coordinateDivisibilityAndGenerators_audit
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (e0 : IsLocalRing.ResidueField A ≃+* k)
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rcases hsource (A := A) (K := K) e0 with ⟨π, hπ_coord, hdiv, hgen⟩
  have hfull :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (π := π) hπ_coord hdiv hgen
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
      (p := p) (G := G) e0
      (existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hfull)

/-- Full audit adapter: the fixed-coordinate full mixed-model source package is sufficient to prove
exactly the `CartanFormalRange.lean:47` target.  The model is supplied by
`existsFullMixedCharacteristicModel_with_all_roots`; the range proof itself uses only the
coordinate divisibility/generator route and transport, not a final cokernel/product endpoint. -/
theorem cartanFormalRange_line47_of_coordinateDivisibilityAndGenerators_fullMixed_audit
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoeth,
      instComplete, K, instField, instAlg, instFrac, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlg
  letI : IsFractionRing A K := instFrac
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom
      (R := k) (A := IsLocalRing.ResidueField A) (f := e0.symm.toRingHom)
      e0.symm.injective p
  rcases hsource (A := A) (K := K) e0 with ⟨π, hπ_coord, hdiv, hgen⟩
  have hfull :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (π := π) hπ_coord hdiv hgen
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
      (p := p) (G := G) e0
      (existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hfull)

end CartanFormalRangeImportAuditWorker

end Representation
