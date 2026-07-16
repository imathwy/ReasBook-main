import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCastRegularValueProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ForwardDiagonalWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance forwardDiagonalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance forwardDiagonalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local cast/readback preservation for the projective-envelope Cartan rows.

This is the source-side row statement needed by the forward diagonal route: after reading a
projective-envelope row back to fixed Cartan coordinates, the integer cast of that row remains in
Serre's regular-value divisibility lattice. -/
def forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c : PRegularConjClass G p,
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model form of the minimal cast/readback-preservation input for this worker.

It is stated with the same projective-envelope family data needed to extend the row statement to
all projective Cartan coordinates. -/
def fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement :
    Prop :=
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
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            ∃ _ : PairwiseNonisomorphic π,
              ∃ _ : IsCompleteIrreducibleFamily π,
                ∃ P : PRegularConjClass G p →
                    FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
                  ∃ _ :
                    ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
                      asModule (π c).ρ, f.IsProjectiveEnvelope,
                    forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
                      (p := p) (A := A) (K := K) (G := G) P

omit [IsAlgClosed k] [CharP k p] in
/-- The worker's explicit cast/readback-preservation statement is exactly the existing
endpoint-facing cast regular-value provider. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_forwardDiagonalWorkerCastReadback
    (hcast :
      fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hcast (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hrows⟩
  exact ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hrows⟩

omit [IsAlgClosed k] [CharP k p] in
/-- Conditional provider for the fixed-coordinate Cartan-coordinate divisibility target. -/
theorem
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_forwardDiagonalWorkerCastReadback
    (hcast :
      fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  exact
    @fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
      p k inferInstance G inferInstance inferInstance inferInstance
      (fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_forwardDiagonalWorkerCastReadback
          (p := p) (k := k) (G := G) hcast)

omit [IsAlgClosed k] [CharP k p] in
/-- Conditional provider for the maximum-split forward diagonal input. -/
theorem
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_forwardDiagonalWorkerCastReadback
    (hcast :
      fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
      (p := p) (k := k) (G := G) := by
  exact
    @fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_projectiveEnvelope_castRegularValue
      p k inferInstance G inferInstance inferInstance inferInstance
      (fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_forwardDiagonalWorkerCastReadback
          (p := p) (k := k) (G := G) hcast)

end ForwardDiagonalWorker

end Representation
