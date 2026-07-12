import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PPrimarySaturationRouteWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanPPrimarySaturationSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanPPrimarySaturationSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanPPrimarySaturationSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The p-primary saturation route supplies the B2 source-span input from the strictly
source-side regular-value congruence and fixed-coordinate divisibility inputs. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_regularValue_and_divisible_pPrimarySaturationSource
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
/-- B-side determinant/product provider obtained from p-primary saturation, without using the
final Cartan range or cokernel/product endpoint as a source readback. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_regularValue_and_divisible_pPrimarySaturationSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR' _instNoetherian'
    _instComplete' K' _instField' _instAlgebra' _instFraction' _instCharZero' _instRoots'
    _instAlgClosed' _instCharP' e0'
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A') (K := K') (G := G)
      (hregular (A := A') (K := K') e0')
      (hdiv (A := A') (K := K') e0')

omit [IsAlgClosed k] [CharP k p] in
/-- Non-cyclic Smith-product provider obtained from the p-primary saturation route.  This is the
B-side product input accepted by `CartanFormalRangeParallelSplit`. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_regularValue_and_divisible_pPrimarySaturationSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR' _instNoetherian'
    _instComplete' K' _instField' _instAlgebra' _instFraction' _instCharZero' _instRoots'
    _instAlgClosed' _instCharP' e0'
  refine
    fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      (p := p) (k := k) (G := G) ?_ (A := A') (K := K') e0'
  intro A'' _instComm'' _instLocal'' _instHenselian'' _instDomain'' _instDVR''
    _instNoetherian'' _instComplete'' K'' _instField'' _instAlgebra'' _instFraction''
    _instCharZero'' _instRoots'' _instAlgClosed'' _instCharP'' e0''
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A'') (K := K'') (G := G)
      (hregular (A := A'') (K := K'') e0'')
      (hdiv (A := A'') (K := K'') e0'')

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice plus fixed-coordinate divisibility is a concrete source package
for the p-primary saturation B2 span route. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_lattice_and_divisible_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
        (hlattice (A := A) (K := K) e0))
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice plus fixed-coordinate divisibility gives the determinant-product
form of the B-side input. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_lattice_and_divisible_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR' _instNoetherian'
    _instComplete' K' _instField' _instAlgebra' _instFraction' _instCharZero' _instRoots'
    _instAlgClosed' _instCharP' e0'
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A') (K := K') (G := G)
      (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
        (p := p) (A := A') (K := K') (G := G)
        (hlattice (A := A') (K := K') e0'))
      (hdiv (A := A') (K := K') e0')

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice plus fixed-coordinate divisibility gives the non-cyclic
Smith-product form of the B-side input. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_lattice_and_divisible_pPrimarySaturationSource
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G))
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      (p := p) (k := k) (G := G) ?_ (A := A) (K := K) e0
  intro A' _instComm' _instLocal' _instHenselian' _instDomain' _instDVR' _instNoetherian'
    _instComplete' K' _instField' _instAlgebra' _instFraction' _instCharZero' _instRoots'
    _instAlgClosed' _instCharP' e0'
  refine
    fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      (p := p) (k := k) (G := G) ?_ (A := A') (K := K') e0'
  intro A'' _instComm'' _instLocal'' _instHenselian'' _instDomain'' _instDVR''
    _instNoetherian'' _instComplete'' K'' _instField'' _instAlgebra'' _instFraction''
    _instCharZero'' _instRoots'' _instAlgClosed'' _instCharP'' e0''
  exact
    projectiveCartanCoordinate_span_eq_of_regularValue_and_divisible_pPrimaryRoute
      (p := p) (A := A'') (K := K'') (G := G)
      (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
        (p := p) (A := A'') (K := K'') (G := G)
        (hlattice (A := A'') (K := K'') e0''))
      (hdiv (A := A'') (K := K'') e0'')

end CartanPPrimarySaturationSourceWorker

end Representation
