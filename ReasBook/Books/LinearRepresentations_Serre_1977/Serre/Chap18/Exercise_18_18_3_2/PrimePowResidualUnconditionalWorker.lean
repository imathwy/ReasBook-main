import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualValuationInfraWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualValuationSourceProofWorker

/-!
Prime-power residual source boundary.

The requested local source theorem is already equivalent, family by family, to the expanded
nontrivial-column prime-power residual input.  This file packages that equivalence at source
theorem level and records the exact valuation/divisibility input that remains.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PrimePowResidualUnconditionalWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance primePowResidualUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance primePowResidualUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-level expanded prime-power residual input, restricted to the columns whose
centralizer `p`-part is nontrivial.  The trivial columns are formal in
`coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_nontrivialPointwisePrimePowInput`.
-/
def coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Source-level expanded DVR valuation input, again only in nontrivial centralizer columns. -/
def coordinateNormalizedBrauerBasisNontrivialPointwiseAddValSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The requested source theorem is exactly the nontrivial-column expanded prime-power
divisibility input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_iff_nontrivialPointwisePrimePowSourceLemma :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_nontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hsource π hπ_simple hπ_coord)
  · intro hpoint π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_nontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hpoint π hπ_simple hπ_coord)

/-- The valuation form is equivalent to the same requested source theorem. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_iff_nontrivialPointwiseAddValSourceLemma :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualAddValInput_iff_nontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        ((coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_addValInput
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
          (hsource π hπ_simple hπ_coord))
  · intro hpoint π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_addValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        ((coordinateNormalizedBrauerBasisPairingResidualAddValInput_iff_nontrivialPointwiseAddValInput
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
          (hpoint π hπ_simple hπ_coord))

/-- Closure direction from the exact nontrivial-column divisibility input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_of_nontrivialPointwisePrimePowSourceLemma
    (hpoint :
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowSourceLemma
        (p := p) (A := A) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_iff_nontrivialPointwisePrimePowSourceLemma
    (p := p) (A := A) (G := G)).2 hpoint

/-- Closure direction from the exact nontrivial-column valuation input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_of_nontrivialPointwiseAddValSourceLemma
    (hval :
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValSourceLemma
        (p := p) (A := A) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_iff_nontrivialPointwiseAddValSourceLemma
    (p := p) (A := A) (G := G)).2 hval

/-- This is the route needed by
`exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_sourceProof`. -/
theorem exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_of_nontrivialPointwisePrimePowSourceLemma
    (hpoint :
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
      (p := p) (A := A) (G := G) :=
  exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_sourceProof
    (p := p) (A := A) (G := G)
    (coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_of_nontrivialPointwisePrimePowSourceLemma
      (p := p) (A := A) (G := G) hpoint)

end PrimePowResidualUnconditionalWorker

end Representation
