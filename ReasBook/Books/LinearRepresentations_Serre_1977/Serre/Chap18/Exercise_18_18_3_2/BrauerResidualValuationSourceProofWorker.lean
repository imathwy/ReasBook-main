import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.DVRValuationRegularValueSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.VisibleReadbackSourceLemmaCompletionWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualValuationSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance brauerResidualValuationSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualValuationSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_sourceProof
    (hsource :
      coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
        (p := p) (A := A) (G := G))
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (hsource π hπ_simple hπ_coord)

theorem exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_sourceProof
    (hsource :
      coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord c d _hd
  have hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_sourceProof
      (p := p) (A := A) (G := G) hsource π hπ_simple hπ_coord
  have hvisible :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual
  exact hvisible c d

end BrauerResidualValuationSourceProofWorker

end Representation
