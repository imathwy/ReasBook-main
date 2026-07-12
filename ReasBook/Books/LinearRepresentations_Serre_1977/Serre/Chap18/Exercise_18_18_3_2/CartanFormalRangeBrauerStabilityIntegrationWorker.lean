import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanProviderFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanRingEquivTransport

/-!
Brauer-stability integration adapter for the support theorem in `CartanFormalRange.lean`.

This file records the shortest forward route from the fixed-coordinate Brauer stability input to
the formal Cartan range target.  It does not import `CartanFormalRange.lean`, and it does not use a
Cartan cokernel/product/Smith/determinant endpoint to manufacture the source input.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeBrauerStabilityIntegrationWorkerLocal

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanFormalRangeBrauerStabilityIntegrationWorkerLocalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeBrauerStabilityIntegrationWorkerLocalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local Brauer-stability adapter.

For one mixed-characteristic model whose residue field is identified with `k`, stability of
Serre's regular-value divisibility lattice under the chosen Brauer-coordinate map gives exactly
the formal Cartan range target over `k`.
-/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_local_brauerRepr_stable
    (e0 : IsLocalRing.ResidueField A ≃+* k)
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
    (p := p) (G := G) e0
    (existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerRepr_stable_final
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable)

end CartanFormalRangeBrauerStabilityIntegrationWorkerLocal

section CartanFormalRangeBrauerStabilityIntegrationWorkerFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeBrauerStabilityIntegrationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeBrauerStabilityIntegrationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Full mixed-model Brauer-stability adapter for `CartanFormalRange.lean:47`.

If another worker supplies
`fullMixedModelBrauerReprRegularValueDivisibilityStableStatement`, this theorem proves the exact
existential coordinate-equivalence target of the support theorem in `CartanFormalRange.lean`.
-/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReprRegularValueDivisibilityStable
    (hstable :
      fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoetherian,
      instComplete, K, instField, instAlgebra, instFraction, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoetherian
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlgebra
  letI : IsFractionRing A K := instFraction
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom
      (R := k) (A := IsLocalRing.ResidueField A) (f := e0.symm.toRingHom)
      e0.symm.injective p
  rcases hstable (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hstable_model⟩
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_local_brauerRepr_stable
      (p := p) (k := k) (A := A) (K := K) (G := G)
      e0 π hπ_simple hπ_coord hstable_model

end CartanFormalRangeBrauerStabilityIntegrationWorkerFullMixed

end Representation
