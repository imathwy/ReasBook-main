import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanProviderFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardSpanClosureWorker

/-!
Source-side closure of the Brauer-coordinate stability obstruction.

The key point is deliberately local: Serre 18.5(a), in the source-faithful regular-value
congruence form, supplies both the inverse-side containment used by
`ProjectiveCharacterDivisibilityEndpoint` and the forward inclusion
`span(cartanCoordinateCast.range) <= regularValueDivisibilitySubmodule`.  Since the existing
Brauer-coordinate image theorem identifies `T(D)` with that span, these two inputs close the
remaining stability equality `T(D) = D` without using the final Cartan range/product endpoints.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprStabilitySourceClosureWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerReprStabilitySourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprStabilitySourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Per-model source closure of the remaining Brauer-coordinate stability equality.

Here `T` is `projectiveCartanASpanBrauerRepr` and `D` is
`regularValueDivisibilitySubmodule`.  The proof uses only the source-faithful regular-value
congruence and the existing source image theorem `T(D) = span(cartanCoordinateCast.range)`.
-/
theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValueCongruence_sourceClosure
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_ ?_
  · simpa [regularValueCongruenceSourceFaithfulStatement] using hregular
  · have hspan_le :
        Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) ≤
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
      projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G) hregular
    have himage :
        Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) :=
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    simpa [himage] using hspan_le

end BrauerReprStabilitySourceClosureWorker

section FullMixedBrauerReprStabilitySourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReprStabilitySourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReprStabilitySourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model Brauer-coordinate stability from the regular-value source congruence.

This closes `fullMixedModelBrauerReprRegularValueDivisibilityStableStatement` from the same
source-faithful regular-value API used elsewhere for Serre 18.5(a), without appealing to the
final Cartan formal range, cokernel product, or determinant endpoints.
-/
theorem fullMixedModelBrauerReprRegularValueDivisibilityStableStatement_of_regularValueSource_sourceClosure
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValueCongruence_sourceClosure
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (hregular (A := A) (K := K) e0)

end FullMixedBrauerReprStabilitySourceClosureWorker

end Representation
