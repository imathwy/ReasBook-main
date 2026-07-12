import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.SourceProductSmithCompletion
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreBasisForwardABasis
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreBasisReverseABasis
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section SourceProductRepresentativesFinalLocal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance sourceProductRepresentativesFinalLocalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceProductRepresentativesFinalLocalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local bridge from the source-faithful regular-value congruence to the exact Serre-basis
integer representative package needed by the source-product route. -/
theorem canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  have hfamily :
      ∃ π : PRegularConjClass G p → FDRep k G,
        (∀ c, Simple (π c)) ∧
          (∀ c,
            regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
          PairwiseNonisomorphic π ∧
          IsCompleteIrreducibleFamily π ∧
          ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
            ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope :=
    exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (G := G)
  rcases hfamily with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, _P, _hP_envelope⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, ?_⟩
  exact
    ⟨canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete hregular,
      canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete hregular⟩

/-- The same local bridge in projective-character witness form. -/
theorem canonicalSourceProductSerreBasisProjectiveWitnessPack_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisProjectiveWitnessPack
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G) hregular with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, hreps⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  refine ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, ?_⟩
  exact
    (serreBasisProjectiveWitness_iff_integerRepresentativesModuloD
      (p := p) (A := A) (K := K) (G := G) π).2 hreps

/-- Local bridge from the regular-value congruence to the split projective-character lattice
and reverse source representative statement. -/
theorem projectiveCharacterLatticeReverseSource_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ∧
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[k](G),
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
              canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)).2 hregular
  · intro g
    let coord : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ) :=
      regularClassCoordinateAddEquiv (p := p) (G := G)
    let x : R₀[k](G) :=
      coord.symm g
    refine ⟨x, ?_⟩
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    have hx :
        regularClassCoordinateAddEquiv (p := p) (G := G) x = g := by
      simp [x, coord]
    have hmem :
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈ D := by
      simpa [D, hx] using hregular x
    have hneg :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈ D := by
      simpa [D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using D.neg_mem hmem
    simpa [D,
      canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hneg

end SourceProductRepresentativesFinalLocal

section SourceProductRepresentativesFinalFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance sourceProductRepresentativesFinalFullMixedFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceProductRepresentativesFinalFullMixedDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side blocker for the final representatives: in every full mixed model, virtual
modular characters are congruent to their fixed integer regular-class coordinates modulo
Serre's regular-value divisibility lattice. -/
def fullMixedModelSourceProductRegularValueCongruenceBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-side regular-value blocker gives the full mixed Serre-basis integer
representatives modulo Serre's divisibility lattice. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-side regular-value blocker gives the full mixed projective-character witness
form of the Serre-basis representatives. -/
theorem fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalSourceProductSerreBasisProjectiveWitnessPack_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-side regular-value blocker gives the full mixed split projective-character
lattice plus reverse source representative statement. -/
theorem fullMixedModelProjectiveCharacterLatticeReverseSourceStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeReverseSourceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeReverseSource_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Combined final bridge: the remaining source-side regular-value blocker supplies all three
full mixed source representative inputs requested by the source-product route. -/
theorem fullMixedModelSourceProductRepresentatives_of_regularValueCongruence
    (hregular :
      fullMixedModelSourceProductRegularValueCongruenceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G) ∧
      fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
        (p := p) (k := k) (G := G) ∧
      fullMixedModelProjectiveCharacterLatticeReverseSourceStatement
        (p := p) (k := k) (G := G) := by
  exact
    ⟨fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_regularValueCongruence
        (p := p) (k := k) (G := G) hregular,
      fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_regularValueCongruence
        (p := p) (k := k) (G := G) hregular,
      fullMixedModelProjectiveCharacterLatticeReverseSourceStatement_of_regularValueCongruence
        (p := p) (k := k) (G := G) hregular⟩

end SourceProductRepresentativesFinalFullMixed

end Representation
