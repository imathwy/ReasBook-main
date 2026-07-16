import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanRingEquivTransport
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Final transport adapter for the formal Cartan range statement.

This is the closed transport wiring behind
`existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_support`:
choose a full mixed-characteristic model whose residue field is ring-equivalent to `k`, prove the
range statement over that residue field by any endpoint, and transport it back across the residue
field equivalence.  The remaining endpoint input is kept as an explicit parameter. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModel_residueEndpoint
    (hresidue :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+
              (PRegularConjClass G p → ℤ),
            (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
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
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
      (p := p) (G := G) e0 (hresidue (A := A) (K := K) e0)

include p in
/-- Final transport adapter specialized to the source-span residue-field endpoint.

The only remaining mathematical input is the `hspan` hypothesis for the full mixed-characteristic
model selected by `existsFullMixedCharacteristicModel_with_all_roots`; no use is made of the
placeholder support theorem in `CartanFormalRange.lean`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_span_eq
    (hspan :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) =
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModel_residueEndpoint
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq
      (p := p) (A := A) (K := K) (G := G)
      (hspan (A := A) (K := K) e0)

end CartanFormalRangeTransport

end Representation
