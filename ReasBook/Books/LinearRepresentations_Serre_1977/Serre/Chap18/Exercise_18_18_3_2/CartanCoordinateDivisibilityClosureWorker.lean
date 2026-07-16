import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanPPrimarySaturationSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanReadbackCoordinateProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCoordinateDivisibilityClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCoordinateDivisibilityClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCoordinateDivisibilityClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Local fixed-coordinate divisibility closure from the source-faithful regular-value
congruence.

The proof uses only the source congruence for projective-envelope rows and integer descent from
Serre's regular-value divisibility lattice. -/
theorem cartanCoordinateAddHom_coordinate_divisible_of_regularValueCongruence
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
          (ConjClasses.centralizerPPart p c.1 : ℤ) * a := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  have hcast :
      ∀ c : PRegularConjClass G p,
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_sourceFaithfulRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hregular
  have hbasis_div :
      ∀ c d : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
            (ConjClasses.centralizerPPart p d.1 : ℤ) * a :=
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
      (p := p) (A := A) (K := K) (G := G) P hcast
  exact
    cartanCoordinateAddHom_coordinate_divisible_of_projectiveEnvelope_basis_vectors
      (p := p) (A := A) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hbasis_div

omit [IsAlgClosed k] [CharP k p] in
/-- Local p-primary span closure using the divisibility just derived from the regular-value
source congruence. -/
theorem projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
    (p := p) (A := A) (K := K) (G := G)
    hregular
    (cartanCoordinateAddHom_coordinate_divisible_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G) hregular)

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful regular-value congruence closes the fixed Cartan-coordinate divisibility
input.

This is the non-circular closure of the `p`-primary/Smith fixed-coordinate divisibility
hypothesis: the regular-value congruence gives the projective-envelope Cartan-coordinate cast
membership, and the existing integer descent turns that membership into coordinatewise
centralizer-`p`-part divisibility. -/
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCoordinateAddHom_coordinate_divisible_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The regular-value source statement used by the p-primary route already supplies the
fixed-coordinate divisibility input. -/
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hfaithful :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
    intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR'
      _instNoetherian' _instComplete' K' _instField' _instAlgebra' _instFraction'
      _instCharZero' _instRoots' _instAlgClosed' _instCharP' e0'
    exact hregular (A := A') (K := K') e0'
  exact
    fullMixedModelCartanCoordinateDivisibilityStatement_of_regularValueCongruence
      (p := p) (k := k) (G := G) hfaithful
      (A := A) (K := K) e0

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice representative congruence, together with Serre `18.5(a)`,
closes the fixed Cartan-coordinate divisibility input. -/
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    fullMixedModelCartanCoordinateDivisibilityStatement_of_regularValueSource
      (p := p) (k := k) (G := G)
      (fullMixedModelRegularValueSourceStatement_of_lattice_pPrimaryRoute
        (p := p) (k := k) (G := G) hlattice)
      (A := A) (K := K) e0

omit [IsAlgClosed k] [CharP k p] in
/-- P-primary saturation route to the fixed-coordinate range equality using only the regular-value
source congruence. -/
theorem fullMixedModelFixedCartanCoordinateRangeStatement_of_regularValue_pPrimaryRoute
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedCartanCoordinateRangeStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice source input closes the fixed-coordinate range equality through
the p-primary saturation route, with no separate divisibility hypothesis. -/
theorem fullMixedModelFixedCartanCoordinateRangeStatement_of_lattice_pPrimaryRoute
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedCartanCoordinateRangeStatement
      (p := p) (k := k) (G := G) := by
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
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G) hregular
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan

omit [IsAlgClosed k] [CharP k p] in
/-- The Cartan p-primary saturation source span theorem with the divisibility hypothesis
discharged from the same regular-value source input. -/
theorem
    fullMixedModelProjectiveCartanCoordinateSpanStatement_of_regularValue_pPrimarySaturationSource
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The determinant-product p-primary saturation source theorem with the divisibility hypothesis
discharged from the same regular-value source input. -/
theorem
    fullMixedModelCartanDetNatAbsProductStatement_of_regularValue_pPrimarySaturationSource
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_projectiveCartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G)
      hspan π hπ_pairwise hπ_complete P hP_envelope

omit [IsAlgClosed k] [CharP k p] in
/-- The Smith-coefficient product p-primary saturation source theorem with the divisibility
hypothesis discharged from the same regular-value source input. -/
theorem
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_regularValue_pPrimarySaturationSource
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR'
    _instNoetherian' _instComplete' K' _instField' _instAlgebra' _instFraction'
    _instCharZero' _instRoots' _instAlgClosed' _instCharP' e0'
  exact
    fullMixedModelCartanDetNatAbsProductStatement_of_regularValue_pPrimarySaturationSource
      (p := p) (k := k) (G := G) hregular
      (A := A') (K := K') e0'

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice source input closes the p-primary saturation source span theorem,
with no separate fixed-coordinate divisibility hypothesis. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_lattice_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)
  exact
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G) hregular

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice source input closes the determinant-product source theorem,
with no separate fixed-coordinate divisibility hypothesis. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_lattice_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement
      (p := p) (k := k) (G := G) := by
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
    projectiveCartanCoordinate_span_eq_of_regularValueCongruence_closure
      (p := p) (A := A) (K := K) (G := G) hregular
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_projectiveCartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G)
      hspan π hπ_pairwise hπ_complete P hP_envelope

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice source input closes the Smith-product source theorem, with no
separate fixed-coordinate divisibility hypothesis. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_lattice_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR'
    _instNoetherian' _instComplete' K' _instField' _instAlgebra' _instFraction'
    _instCharZero' _instRoots' _instAlgClosed' _instCharP' e0'
  exact
    fullMixedModelCartanDetNatAbsProductStatement_of_lattice_pPrimarySaturationSource
      (p := p) (k := k) (G := G) hlattice
      (A := A') (K := K') e0'

end CartanCoordinateDivisibilityClosureWorker

end Representation
