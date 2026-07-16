import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceClosureWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassResidualFullRepresentativeWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker

/-!
Source-text boundary for the projective-character lattice congruence.

This worker keeps Serre Exercise `18.5(a)` in its literal support/value form.  The remaining
local input is the construction of full class-function representatives for the
coordinate-normalized residual rows:

* zero on the `p`-singular locus;
* divisible by the centralizer `p`-part on the `p`-regular locus;
* regular restriction equal to the row
  `modularCharacter(π c) - Pi.single c 1`.

The theorems below show that this source-text package is exactly the same non-Cartan obligation
as `projectiveCharacterLatticeIntegerRepresentativeCongruence` and its full mixed form.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterLatticeSourceTextProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterLatticeSourceTextProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeSourceTextProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The precise local source-text API left by Serre `18.5(a)`.

This is the existing support/value row package, renamed at the projective-character lattice
frontier.  Unfolding it gives:
there is a coordinate-normalized Brauer family `π` such that each residual row has a full
representative `Φ : A ⊗R[K](G)` satisfying the two right-hand-side conditions of Serre `18.5(a)`.
-/
def projectiveCharacterLatticeSourceTextLocalSupportValueAPI : Prop :=
  regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
    (p := p) (A := A) (K := K) (G := G)

/-- Serre `18.5(a)` turns the support/value row package into projective-character row
representatives.  This is the direct use of the source text criterion, not a Cartan endpoint
argument. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases hrows c with ⟨Φ, hzero, hvalue, hres⟩
  refine ⟨Φ, ?_, ?_⟩
  · exact
      mem_projectiveCharacterSubmodule_of_serre18_5a_rhs_of_enoughRoots
        (p := p) (A := A) (K := K) (G := G) hzero hvalue
  · simpa [coordinateNormalizedPointMassExplicitResidualRow,
      virtualModularCharacterOnPRegularConjClass_class] using hres

/-- Local provider: the source-text support/value package closes the
projective-character lattice congruence. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitness_source
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hsource)

/-- Conversely, the projective-character lattice congruence supplies the source-text
support/value row package, by rewriting it as the regular-value congruence and choosing the
standard coordinate-normalized family. -/
theorem projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_projectiveCharacterLattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) := by
  have hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) :=
    (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)).1 hlattice
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) hregular

/-- Exact local boundary: the projective-character lattice congruence is equivalent to the
literal Serre `18.5(a)` support/value source package for the point-mass residual rows. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_sourceTextSupportValueAPI :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ↔
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_projectiveCharacterLattice
        (p := p) (A := A) (K := K) (G := G)
  · exact
      projectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)

end LocalProjectiveCharacterLatticeSourceTextProofWorker

section FullMixedProjectiveCharacterLatticeSourceTextProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeSourceTextProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeSourceTextProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed version of the source-text support/value API. -/
def fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI : Prop :=
  fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed support/value rows give the point-mass projective-restriction witnesses by
Serre `18.5(a)` in each mixed-characteristic model. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed provider: the source-text support/value API closes
`fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence`. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitnessBlocker_source
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_sourceTextSupportValueAPI
      (p := p) (k := k) (G := G) hsource)

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the full mixed projective-character lattice congruence supplies the same
source-text support/value package in every mixed-characteristic model. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_projectiveCharacterLattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_projectiveCharacterLattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary: the projective-character lattice source theorem is equivalent to
the literal Serre `18.5(a)` support/value source package. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_sourceTextSupportValueAPI :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_of_projectiveCharacterLattice
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
        (p := p) (k := k) (G := G)

end FullMixedProjectiveCharacterLatticeSourceTextProofWorker

end Representation
