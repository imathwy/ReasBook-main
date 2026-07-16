import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Source-side closure for the inverse-Brauer point-mass input.

The local content is the fixed-family equivalence between the inverse-Brauer point-mass
congruence and the direct point-mass row divisibility supplied by the Serre `18.5(a)` source
lattice.  The remaining statements package this equivalence for the existing residual and
orthogonality source inputs, and then lift it to the full mixed-characteristic statement.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerInversePointMassSourceClosureWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance brauerInversePointMassSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerInversePointMassSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Direct point-mass row divisibility gives the inverse-Brauer point-mass congruence for the
same coordinate-normalized Brauer family.

This is the source-side form of the basis-vector inverse-Brauer congruence: the existing
`projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence` identifies
the row congruence for `[π c]₀` with the inverse-Brauer congruence for the standard point mass. -/
theorem regularValueCongruenceSourceFaithfulBrauerInversePointMassInput_of_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  have hsource :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[kA](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
      virtualModularCharacterOnPRegularConjClass_class] using hrows c
  exact
    (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).1 hsource

/-- Conversely, inverse-Brauer point-mass congruences recover the direct point-mass row
divisibility for the same family. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_brauerInversePointMassInput
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hinv :
      regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  have hsource :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[kA](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2
      (hinv c)
  simpa [coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule,
    virtualModularCharacterOnPRegularConjClass_class] using hsource

/-- Fixed-family exact source equivalence: inverse-Brauer point masses are the same datum as
direct point-mass regular-value rows. -/
theorem regularValueCongruenceSourceFaithfulBrauerInversePointMassInput_iff_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    regularValueCongruenceSourceFaithfulBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_brauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      regularValueCongruenceSourceFaithfulBrauerInversePointMassInput_of_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Existential point-mass row source gives the existential inverse-Brauer point-mass input. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_sourceRows
    (hrows :
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerInversePointMassInput_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows

/-- The existential inverse-Brauer point-mass input recovers the existential point-mass row
source. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_brauerInversePointMassInput
    (hinv :
      regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hinv with ⟨π, hπ_simple, hπ_coord, hinv⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_brauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hinv

/-- Existential source equivalence: the inverse-Brauer point-mass input is exactly the direct
point-mass row input. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_sourceRows :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_brauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_sourceRows
        (p := p) (A := A) (K := K) (G := G)

/-- Projective-character lattice representatives supply the inverse-Brauer point-mass input by
specializing Serre `18.5(a)` to the coordinate-normalized point-mass rows. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_sourceRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

/-- The existential pairing residual is enough for the inverse-Brauer point-mass input. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_existsPairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_sourceRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G) hresidual)

/-- The inverse-Brauer point-mass input and the existential pairing residual are equivalent. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_existsPairingResidualProof :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_sourceRows
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_sourceRows
      (p := p) (A := A) (K := K) (G := G)).symm

/-- The explicit Serre `18.4`/orthogonality source input closes the inverse-Brauer point-mass
input. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_orthogonalityInput
    (horth :
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_existsPairingResidualProof
    (p := p) (A := A) (K := K) (G := G)).2
    (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
      (p := p) (A := A) (K := K) (G := G) horth)

/-- The inverse-Brauer point-mass input is equivalent to the explicit Serre `18.4`/orthogonality
source input. -/
theorem regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_orthogonalityInput :
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_iff_existsPairingResidualProof
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_orthogonalityInput
      (p := p) (A := A) (K := K) (G := G))

/-- Local lift from the existential inverse-Brauer point-mass input to the regular-value source
statement. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_existsBrauerInversePointMassInput
    (hinv :
      regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerInversePointMassInput
    (p := p) (A := A) (K := K) (G := G)).2 hinv

end LocalBrauerInversePointMassSourceClosureWorker

section FullMixedBrauerInversePointMassSourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerInversePointMassSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerInversePointMassSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic form of the existential inverse-Brauer point-mass source input. -/
def fullMixedModelBrauerInversePointMassSourceInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed direct point-mass rows give the full mixed inverse-Brauer point-mass source
input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_of_pointMassRowsInRegularValueSubmoduleInput
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerInversePointMassSourceInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_sourceRows
      (p := p) (A := A) (K := K) (G := G)
      (by
        simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
          hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed inverse-Brauer point-mass source input recovers the full mixed direct
point-mass row input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_brauerInversePointMassSourceInput
    (hinv :
      fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_brauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G)
      (hinv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed equivalence with the direct point-mass row source input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_iff_pointMassRowsInRegularValueSubmoduleInput :
    fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_brauerInversePointMassSourceInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerInversePointMassSourceInput_of_pointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed projective-character lattice input supplies the inverse-Brauer point-mass source
input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerInversePointMassSourceInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed existential pairing residuals give the inverse-Brauer point-mass source input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerInversePointMassSourceInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_existsPairingResidualProof
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed equivalence with the existential pairing residual blocker. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_iff_existsPairingResidualBlocker :
    fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerInversePointMassSourceInput_iff_pointMassRowsInRegularValueSubmoduleInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_existsPairingResidualBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed explicit Serre `18.4`/orthogonality input gives the inverse-Brauer point-mass
source input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerInversePointMassSourceInput
      (p := p) (k := k) (G := G) :=
  fullMixedModelBrauerInversePointMassSourceInput_of_pointMassRowsInRegularValueSubmoduleInput
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_orthogonalityInput
      (p := p) (k := k) (G := G) horth)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed inverse-Brauer source input is equivalent to the explicit Serre `18.4`/
orthogonality source input. -/
theorem fullMixedModelBrauerInversePointMassSourceInput_iff_orthogonalityInput :
    fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerInversePointMassSourceInput_iff_pointMassRowsInRegularValueSubmoduleInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed lift from inverse-Brauer point-mass source input to the regular-value source
statement. -/
theorem fullMixedModelRegularValueSourceStatement_of_brauerInversePointMassSourceInput
    (hinv :
      fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_existsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G)
      (hinv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact equivalence between the target regular-value source statement and the
inverse-Brauer point-mass source input. -/
theorem fullMixedModelRegularValueSourceStatement_iff_brauerInversePointMassSourceInput :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerInversePointMassSourceInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)).1
        (hregular (A := A) (K := K) e0)
  · exact
      fullMixedModelRegularValueSourceStatement_of_brauerInversePointMassSourceInput
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed lift from explicit Serre `18.4`/orthogonality source input to the regular-value
source statement. -/
theorem fullMixedModelRegularValueSourceStatement_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceStatement_of_brauerInversePointMassSourceInput
    (p := p) (k := k) (G := G)
    (fullMixedModelBrauerInversePointMassSourceInput_of_orthogonalityInput
      (p := p) (k := k) (G := G) horth)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed lift from the existential pairing residual blocker to the regular-value source
statement. -/
theorem fullMixedModelRegularValueSourceStatement_of_existsPairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_existsBrauerInversePointMassInput
      (p := p) (A := A) (K := K) (G := G)
      (regularValueCongruenceSourceFaithfulExistsBrauerInversePointMassInput_of_existsPairingResidualProof
        (p := p) (A := A) (K := K) (G := G)
        (hresidual (A := A) (K := K) e0))

end FullMixedBrauerInversePointMassSourceClosureWorker

end Representation
