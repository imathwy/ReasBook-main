import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SourceProductRepresentativesFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalRegularValueCongruenceClosureFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance regularValueCongruenceClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueCongruenceClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local minimal source-side input left for the non-circular closure.

This is the Exercise `18.4` plus orthogonality pointwise residual, restricted to the
nontrivial centralizer-`p`-part columns; the existing readback API fills the
`centralizerPPart = 1` columns. -/
abbrev regularValueCongruenceClosureLocalPointwiseResidualInput : Prop :=
  regularValueCongruenceSourceFaithfulPointwiseResidualProof
    (p := p) (A := A) (G := G)

/-- The pointwise Exercise `18.4`/orthogonality residual closes the local
source-faithful regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_pointwiseResidualInput
    (hresidual :
      regularValueCongruenceClosureLocalPointwiseResidualInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
      (p := p) (A := A) (G := G) hresidual)

/-- The same local residual input closes the projective-character lattice representative
congruence by Serre `18.5(a)`. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointwiseResidualInput
    (hresidual :
      regularValueCongruenceClosureLocalPointwiseResidualInput
        (p := p) (A := A) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)).2
    (regularValueCongruenceSourceFaithfulStatement_of_pointwiseResidualInput
      (p := p) (A := A) (K := K) (G := G) hresidual)

end LocalRegularValueCongruenceClosureFinal

section FullMixedRegularValueCongruenceClosureFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedRegularValueCongruenceClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedRegularValueCongruenceClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the remaining source-side pointwise residual input. -/
abbrev regularValueCongruenceClosureFullMixedPointwiseResidualInput : Prop :=
  fullMixedModelBrauerBasisPointwiseResidualBlocker
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed pointwise residual input closes
`fullMixedModelRegularValueCongruenceSourceFaithfulStatement`. -/
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_pointwiseResidualInput
    (hresidual :
      regularValueCongruenceClosureFullMixedPointwiseResidualInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
        (p := p) (A := A) (G := G) (hresidual (A := A) (K := K) e0))

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed pointwise residual input also closes the projective-character lattice
integer representative congruence. -/
theorem
    fullMixedModelProjectiveCharacterLatticeCongruence_of_pointwiseResidualInput
    (hresidual :
      regularValueCongruenceClosureFullMixedPointwiseResidualInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointwiseResidualInput
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed regular-value statement is exactly the source-product blocker introduced in
`SourceProductRepresentativesFinal`. -/
theorem fullMixedModelSourceProductRegularValueCongruenceBlocker_of_regularValue
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelSourceProductRegularValueCongruenceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact hregular (A := A) (K := K) e0

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the source-product blocker is the same full mixed regular-value statement. -/
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_sourceProductBlocker
    (hregular :
      fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact hregular (A := A) (K := K) e0

omit [IsAlgClosed k] [CharP k p] in
/-- The exact equivalence between the final source-product blocker and the full mixed
regular-value congruence. -/
theorem fullMixedModelSourceProductRegularValueCongruenceBlocker_iff_regularValue :
    fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_sourceProductBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelSourceProductRegularValueCongruenceBlocker_of_regularValue
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed pointwise residual input closes the source-product regular-value blocker. -/
theorem fullMixedModelSourceProductRegularValueCongruenceBlocker_of_pointwiseResidualInput
    (hresidual :
      regularValueCongruenceClosureFullMixedPointwiseResidualInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelSourceProductRegularValueCongruenceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
        (p := p) (A := A) (G := G) (hresidual (A := A) (K := K) e0))

end FullMixedRegularValueCongruenceClosureFinal

end Representation
