import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanProviderFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardScaledProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprStabilityProviderWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance brauerReprStabilityProviderWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprStabilityProviderWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model Brauer-coordinate stability from the two forward source inputs.

The proof is the non-circular local stability route: regular-value source congruence gives the
inverse-side containment for the Brauer-coordinate equivalence, while the forward diagonal
congruence gives the forward containment on Serre's divisibility lattice. -/
theorem fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_forwardDiagonal
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hforward (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hdiag⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_regularIntegerDiagonal_congruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (by
        simpa [regularValueCongruenceSourceFaithfulStatement] using
          hregular (A := A) (K := K) e0)
      hdiag

omit [IsAlgClosed k] [CharP k p] in
/-- Scaled-indicator form of the same provider.

The scaled basis-vector congruences are first promoted to the whole diagonal-lattice forward
congruence by `ProjectiveCartanForwardDiagonalBasis`. -/
theorem fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_forwardScaled
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hscaled :
      fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_forwardDiagonal
    (p := p) (k := k) (G := G)
    hregular
    (fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_scaledIndicators
      (p := p) (k := k) (G := G) hscaled)

omit [IsAlgClosed k] [CharP k p] in
/-- Fixed-coordinate range-inclusion form of the provider.

This packages the preferred forward-coordinate API: a proof that the fixed Cartan-coordinate range
lands in Serre's regular integer diagonal lattice supplies the forward diagonal congruence, and
regular-value source congruence supplies the inverse-side containment. -/
theorem
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_cartanCoordinateRangeLe
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hrange_le :
      fullMixedModelCartanCoordinateRangeLeStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_forwardDiagonal
    (p := p) (k := k) (G := G) hregular <| by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      rcases
          exists_coordinate_normalized_complete_family_with_projective_envelopes
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
        ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
      refine ⟨π, hπ_simple, hπ_coord, ?_⟩
      exact
        projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_range_le
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord
          (hrange_le (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Fixed-coordinate coordinatewise-divisibility form of the provider.

This is the smallest forward diagonal source input exposed by
`ProjectiveCartanForwardDiagonalProducer`: coordinatewise centralizer-`p`-part divisibility for
Cartan-coordinate rows. -/
theorem
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_cartanCoordinateDivisibility
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValue_and_forwardDiagonal
    (p := p) (k := k) (G := G) hregular <| by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      rcases
          exists_coordinate_normalized_complete_family_with_projective_envelopes
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
        ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
      refine ⟨π, hπ_simple, hπ_coord, ?_⟩
      exact
        projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord
          (hdiv (A := A) (K := K) e0)

end BrauerReprStabilityProviderWorker

end Representation
