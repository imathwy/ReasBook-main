import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreIntegralRepresentatives
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductSerreBasisForwardABasis

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance canonicalSourceProductSerreBasisForwardABasisFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductSerreBasisForwardABasisDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

set_option linter.style.longLine false in
omit [Fintype ι] [DecidableEq ι] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Coordinate form of the forward integer-representative condition.

For each Brauer row and each regular class, the class of the Brauer value modulo Serre's
`p^{z(s)}` lattice must lie in the image of the ordinary integers. This is the exact local
obstruction to the unconditional forward representative theorem. -/
theorem canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives_iff_coordinate_integer_lifts
    (π : ι → FDRep k G) :
    canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π ↔
      ∀ i : ι, ∀ c : PRegularConjClass G p,
        ∃ n : ℤ, ∃ a : A,
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π i]₀ : R₀[k](G)) c =
            (n : K) +
              algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := by
  constructor
  · intro h i c
    rcases h i with ⟨g, hg⟩
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G) _).1 hg c with
      ⟨a, ha⟩
    refine ⟨g c, a, ?_⟩
    simp only [Pi.sub_apply, regularIntegerFunctionCast] at ha
    rw [sub_eq_iff_eq_add] at ha
    simpa [add_comm] using ha
  · intro h i
    choose g hg using h i
    choose a ha using hg
    refine ⟨g, ?_⟩
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) _).2 ?_
    intro c
    refine ⟨a c, ?_⟩
    have hchar :
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π i)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) c =
          (g c : K) +
            algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a c) := by
      simpa [virtualModularCharacterOnPRegularConjClass_class] using ha c
    calc
      (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g) c
          =
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π i)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) c -
          (g c : K) := by
            simp [regularIntegerFunctionCast, virtualModularCharacterOnPRegularConjClass_class]
      _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a c) := by
            simp [hchar]

set_option linter.style.longLine false in
omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The global source-faithful regular-value congruence supplies the forward integer
representatives for any complete Brauer basis.

The proof uses the canonical integer coordinate function as the representative. Thus an
unconditional proof of the suggested theorem is reduced to the existing global congruence
blocker, not to basis bookkeeping. -/
theorem canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives_of_regularValueCongruenceSourceFaithfulStatement
    (π : ι → FDRep k G)
    (_hπ_pairwise : PairwiseNonisomorphic π)
    (_hπ_complete : IsCompleteIrreducibleFamily π)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π := by
  intro i
  let coord : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ) :=
    regularClassCoordinateAddEquiv (p := p) (G := G)
  refine ⟨coord ([π i]₀ : R₀[k](G)), ?_⟩
  simpa [regularValueCongruenceSourceFaithfulStatement] using
    hregular ([π i]₀ : R₀[k](G))

end CanonicalSourceProductSerreBasisForwardABasis

end Representation
