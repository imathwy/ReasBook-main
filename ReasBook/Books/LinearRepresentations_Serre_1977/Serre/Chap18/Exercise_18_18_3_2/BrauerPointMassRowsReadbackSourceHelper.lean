import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PairingResidualDirectWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof

/-!
Source-side helpers from direct point-mass row divisibility to the fixed-coordinate Brauer
readback input.  The route stays within the Brauer readback/pairing API: point-mass rows give
the pairing residual, and the pairing residual gives fixed-coordinate readback.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerPointMassRowsReadbackSourceHelper

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerPointMassRowsReadbackSourceHelperFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassRowsReadbackSourceHelperDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Direct point-mass regular-value row divisibility closes fixed-coordinate Brauer readback
for the same coordinate-normalized family.

This is the non-circular fixed-family source bridge: it uses the direct pairing residual worker
and the A-linear residual-to-readback step, not a Cartan range/cokernel/product endpoint. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows)

/-- Projective-character lattice row representatives close fixed-coordinate Brauer readback for
any already chosen coordinate-normalized family.

This is just the previous theorem after specializing the lattice congruence to the point-mass
rows of the family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveCharacter_lattice_rows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_pointMassRowsInRegularValueSubmodule
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) π hπ_coord hlattice)

/-- A fixed coordinate-normalized family with direct point-mass row divisibility supplies the
local Brauer-basis readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) :=
  ⟨π, hπ_simple, hπ_coord,
    brauerBasisFixedCoordinateReadbackDivisibility_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows⟩

end LocalBrauerPointMassRowsReadbackSourceHelper

section FullMixedBrauerPointMassRowsReadbackSourceHelper

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerPointMassRowsReadbackSourceHelperFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerPointMassRowsReadbackSourceHelperDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic source input using direct point-mass row divisibility. -/
def fullMixedModelPointMassRowsInRegularValueSubmoduleInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ _hπ_simple : ∀ c, Simple (π c),
          ∃ _hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
              (p := p) (A := A) (K := K) (G := G) π

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed direct point-mass row input closes the full mixed Brauer readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pointMassRowsInRegularValueSubmodule
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hrows (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hrow⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrow

end FullMixedBrauerPointMassRowsReadbackSourceHelper

end Representation
