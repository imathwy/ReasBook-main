import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromSerreBasis

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductReverseWitness

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

local instance canonicalSourceProductReverseWitnessFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductReverseWitnessDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [DecidableEq ι] in
/-- Serre 18.5(a), used in the reverse point direction: a regular-value divisibility
congruence for each point mass can be lifted to an actual projective-character regular
restriction witness. -/
theorem canonicalSourceProductSerreBasisReversePointProjectiveWitness_of_regularValueDivisibility
    (π : ι → FDRep k G)
    (hD :
      ∀ c : PRegularConjClass G p,
        ∃ m : ι → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
            ∑ i : ι,
              m i •
                virtualModularCharacterOnPRegularConjClass
                  (p := p) (A := K) (G := G)
                  (PrimeToPRoot.toFieldLift
                    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
                  ([π i]₀ : R₀[k](G)) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisReversePointProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases hD c with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  let f : PRegularConjClass G p → K :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
      ∑ i : ι,
        m i •
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G))
  have hfD :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [f] using hm
  have hfmap :
      f ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hfD
  rcases Submodule.mem_map.1 hfmap with ⟨Φ, hΦ, hΦres⟩
  refine ⟨Φ, hΦ, ?_⟩
  simpa [f, regularRestrictionLinearMap] using hΦres

end CanonicalSourceProductReverseWitness

end Representation
