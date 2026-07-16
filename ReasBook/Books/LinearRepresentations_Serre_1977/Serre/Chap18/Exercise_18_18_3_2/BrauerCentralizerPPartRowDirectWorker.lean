import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerNontrivialFieldRowSourceAPIWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceTextProofWorker

/-!
Direct source-side centralizer `p`-part row divisibility.

This worker keeps the proof on Serre's `18.5(a)` source side.  The global regular-value
divisibility statement is specialized to the coordinate-normalized Brauer row `[π c]₀`, then
unpacked pointwise.  No Cartan cokernel/product/Smith endpoint is used.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerCentralizerPPartRowDirectWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerCentralizerPPartRowDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerCentralizerPPartRowDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Serre `18.5(a)` in regular-value form gives the literal K/A-valued Brauer-row congruence:
for each coordinate-normalized Brauer row, the readback row differs from the point mass by a
multiple of the target centralizer `p`-part. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
      (p := p) (A := A) (K := K) (G := G) := by
  intro π _hπ_simple hπ_coord c d _hd
  have hrow :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [hπ_coord c] using hregular ([π c]₀ : R₀[k](G))
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))).1 hrow d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [coordinateNormalizedBrauerCharacterNontrivialFieldRowSource,
    virtualModularCharacterOnPRegularConjClass_class] using ha

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A-valued readback form of the same direct row congruence.  The K-valued source row is
descended by the existing fraction-field readback bridge; the centralizer `p`-part divisor is
unchanged. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_iff_fieldRowSourceAPI
    (p := p) (A := A) (K := K) (G := G)).2
    (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G) hregular)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The direct regular-value congruence also closes the equivalent Exercise `18.4` point-mass
row source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem
    (p := p) (A := A) (K := K) (G := G)).1
    (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G) hregular)

/-- Projective-character lattice representative congruence gives the nontrivial centralizer
`p`-part Brauer-row congruence by Serre's regular-value divisibility identification. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
      (p := p) (A := A) (K := K) (G := G) :=
  coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)
    ((projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)).1 hlattice)

/-- Literal source-text support/value row representatives close the nontrivial centralizer
`p`-part Brauer-row congruence.  This is the Serre `18.5(a)` route: support/value representatives
give projective-character row representatives, hence regular-value divisibility, hence the row
readback congruence. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
      (p := p) (A := A) (K := K) (G := G) :=
  coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hsource)

/-- Source-text support/value representatives give the requested A-valued nontrivial readback
row congruence. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_iff_fieldRowSourceAPI
    (p := p) (A := A) (K := K) (G := G)).2
    (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hsource)

/-- Source-text support/value representatives close the equivalent Exercise `18.4` point-mass
row congruence source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
    (hsource :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem
    (p := p) (A := A) (K := K) (G := G)).1
    (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hsource)

end BrauerCentralizerPPartRowDirectWorker

section FullMixedBrauerCentralizerPPartRowDirectWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerCentralizerPPartRowDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerCentralizerPPartRowDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed version of the direct source-side row bridge from Serre `18.5(a)` support/value
representatives to the nontrivial centralizer `p`-part Brauer-row congruence. -/
theorem fullMixedModelBrauerCharacterNontrivialFieldRowSourceAPI_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
          (p := p) (A := A) (K := K) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed A-valued readback version of the direct source-side row bridge. -/
theorem fullMixedModelBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
          (p := p) (A := A) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed Exercise `18.4` point-mass row source version of the direct source-side bridge. -/
theorem fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        exercise18_4PointMassRowCongruenceSourceTheorem
          (p := p) (A := A) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

end FullMixedBrauerCentralizerPPartRowDirectWorker

end Representation
