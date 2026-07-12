import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PPrimarySaturationProviderFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateSpanProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeProviderFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PPrimarySaturationRouteWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance pPrimarySaturationRouteWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pPrimarySaturationRouteWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

theorem
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (hregular :
      regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G))
    (hdiv :
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  have hdiag :
      ∀ f : PRegularConjClass G p → ℤ,
        f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
          projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hdiv
  exact
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_regularValue_congruence_and_brauerRepr_forward_regularIntegerDiagonal_congruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hregular hdiag

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice source input supplies the regular-value source statement
used by the non-circular span route. -/
theorem fullMixedModelRegularValueSourceStatement_of_lattice_pPrimaryRoute
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Regular-value source congruence plus fixed-coordinate divisibility gives the stronger
mixed-characteristic Cartan-coordinate span equality, without using any cokernel/product
endpoint. -/
theorem
    fullMixedModelProjectiveCartanCoordinateSpanStatement_of_regularValue_and_divisible_pPrimaryRoute
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- P-primary saturation route to the fixed-coordinate range equality.

The span equality is produced from source-side regular-value congruence and coordinate
divisibility; the final step is
`cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq`,
which uses the prime-to-`p` denominator-clearing saturation of the fixed Cartan coordinate range. -/
theorem
    fullMixedModelFixedCartanCoordinateRangeStatement_of_regularValue_and_divisible_pPrimaryRoute
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelFixedCartanCoordinateRangeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hspanFull :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)
      (hdiv (A := A) (K := K) e0)
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G)
      hspanFull

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice plus fixed-coordinate divisibility closes the fixed-coordinate
range equality through the p-primary saturation route. -/
theorem
    fullMixedModelFixedCartanCoordinateRangeStatement_of_lattice_and_divisible_pPrimaryRoute
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelFixedCartanCoordinateRangeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)
  have hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A) (K := K) (G := G)
      hregular
      (hdiv (A := A) (K := K) e0)
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan

end PPrimarySaturationRouteWorker

end Representation
