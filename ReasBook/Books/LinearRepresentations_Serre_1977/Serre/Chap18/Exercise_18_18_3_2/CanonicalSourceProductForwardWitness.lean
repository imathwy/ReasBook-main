import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromSerreBasis

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductForwardWitness

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

/-- Serre 18.5(a), read backwards: a regular-class function satisfying the coordinatewise
`p^{z(s)}` divisibility condition is the regular restriction of a projective character. -/
theorem canonicalSourceProductSerreBasisForwardProjectiveWitness_of_regularValueDivisibility
    (π : ι → FDRep k G)
    (hD : ∀ i : ι,
      ∃ g : PRegularConjClass G p → ℤ,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisForwardProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π := by
  intro i
  rcases hD i with ⟨g, hg⟩
  let f : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π i]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G) g
  have hfD :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [f] using hg
  have hfmap :
      f ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hfD
  rcases Submodule.mem_map.mp hfmap with ⟨Φ, hΦ, hΦres⟩
  refine ⟨g, Φ, hΦ, ?_⟩
  simpa [f, regularRestrictionLinearMap] using hΦres

end CanonicalSourceProductForwardWitness

end Representation
