import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SourceProductRepresentativesFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionWitnessCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SupportValueResidualRowsDirectWorker

/-!
Source-side canonical source-product closure.

The local bridge below uses the coordinate-normalized Serre `18.4` Brauer family.  A
point-mass projective-restriction witness for the rows `χ(π c) - δ_c` gives the forward
Serre-basis projective witnesses directly and gives the reverse point witnesses by negating the
same projective character.  The full mixed statements then feed the existing source-product
Serre-basis package, without deriving source input from later Cartan endpoints.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalSourceProductUnconditionalWorkerLocal

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

local instance canonicalSourceProductUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A coordinate-normalized point-mass projective-restriction witness is exactly enough to build
the Serre-basis projective-witness package used by the canonical source-product route. -/
theorem canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisProjectiveWitnessPack
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance, π,
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord,
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord, ?_⟩
  constructor
  · intro c
    rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
    refine ⟨Pi.single c (1 : ℤ), Φ, hΦ, ?_⟩
    simpa [virtualModularCharacterOnPRegularConjClass_class] using hΦres
  · intro c
    rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
    refine ⟨Pi.single c (1 : ℤ), -Φ, ?_, ?_⟩
    · exact (projectiveCharacterSubmodule (A := A) (K := K) (G := G)).neg_mem hΦ
    · let χ : R₀[kA](G) →+ (PRegularConjClass G p → K) :=
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      have hsum :
          (∑ i : PRegularConjClass G p,
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) i) •
                χ ([π i]₀ : R₀[kA](G))) =
            χ ([π c]₀ : R₀[kA](G)) := by
        ext d
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single_of_mem (a := c) (by simp)
          (fun b _hb hbc => by simp [Pi.single_eq_of_ne hbc])]
        simp
      calc
        regularRestriction (p := p) (A := A) (K := K) (G := G) (-Φ) =
            -regularRestriction (p := p) (A := A) (K := K) (G := G) Φ := by
              change
                regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) (-Φ) =
                  -regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) Φ
              simp
        _ =
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
              χ ([π c]₀ : R₀[kA](G)) := by
              rw [hΦres]
              ext d
              simp [χ, sub_eq_add_neg, add_comm]
        _ =
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
              ∑ i : PRegularConjClass G p,
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) i) •
                  virtualModularCharacterOnPRegularConjClass
                    (p := p) (A := K) (G := G)
                    (PrimeToPRoot.toFieldLift
                      (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
                    ([π i]₀ : R₀[kA](G)) := by
              rw [hsum]

end CanonicalSourceProductUnconditionalWorkerLocal

section CanonicalSourceProductUnconditionalWorkerFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedCanonicalSourceProductUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedCanonicalSourceProductUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed point-mass projective-restriction witnesses give the Serre-basis projective
witness statement for the canonical source-product route. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_pointMassProjectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed point-mass projective-restriction witnesses give the integer representatives
modulo Serre's regular-value divisibility lattice. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_pointMassProjectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_projectiveWitness
    (p := p) (k := k) (G := G)
    (fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_pointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

omit [IsAlgClosed k] [CharP k p] in
/-- Source-product closure from the point-mass projective-restriction witness blocker. -/
theorem fullMixedModelCanonicalSourceProductImageStatement_of_pointMassProjectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisProjectiveWitnessPack
      (p := p) (A := A) (K := K) (G := G)
      (canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)
        (hwitness (A := A) (K := K) e0))

omit [IsAlgClosed k] [CharP k p] in
/-- The current Serre `18.5(a)` source-text theorem supplies the Serre-basis projective-witness
statement for the canonical source-product route. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_serre18_5ASourceTextTheorem
    (hsource :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)
  exact
    canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) hwitness

omit [IsAlgClosed k] [CharP k p] in
/-- Source-product closure from the current Serre `18.5(a)` source-text theorem. -/
theorem fullMixedModelCanonicalSourceProductImageStatement_of_serre18_5ASourceTextTheorem
    (hsource :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisProjectiveWitnessPack
      (p := p) (A := A) (K := K) (G := G)
      (canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) hwitness)

omit [IsAlgClosed k] [CharP k p] in
/-- The Exercise `18.4` point-mass row theorem, combined with the literal Serre `18.5(a)`
support/value criterion, supplies the Serre-basis projective-witness statement. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hapi :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) :=
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)
  have hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hapi
  exact
    canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) hwitness

omit [IsAlgClosed k] [CharP k p] in
/-- Source-product closure from the Exercise `18.4` point-mass row theorem and literal Serre
`18.5(a)` support/value route. -/
theorem fullMixedModelCanonicalSourceProductImageStatement_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hapi :
      projectiveCharacterLatticeSourceTextLocalSupportValueAPI
        (p := p) (A := A) (K := K) (G := G) :=
    projectiveCharacterLatticeSourceTextLocalSupportValueAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)
  have hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_sourceTextSupportValueAPI
      (p := p) (A := A) (K := K) (G := G) hapi
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisProjectiveWitnessPack
      (p := p) (A := A) (K := K) (G := G)
      (canonicalSourceProductSerreBasisProjectiveWitnessPack_of_pointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) hwitness)

end CanonicalSourceProductUnconditionalWorkerFullMixed

end Representation
