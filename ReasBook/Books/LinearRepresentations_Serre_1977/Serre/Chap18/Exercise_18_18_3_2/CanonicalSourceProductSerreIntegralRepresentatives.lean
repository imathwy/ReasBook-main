import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromSerreBasis

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductSerreIntegralRepresentatives

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

local instance canonicalSourceProductSerreIntegralRepresentativesFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductSerreIntegralRepresentativesDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Forward integer representatives modulo Serre's regular divisibility lattice.

This is the non-fixed-witness form: the representative `g` is arbitrary and is not required to be
the coordinate point mass attached to the simple row. -/
def canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
    (π : ι → FDRep k G) : Prop :=
  ∀ i : ι,
    ∃ g : PRegularConjClass G p → ℤ,
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- Reverse point representatives modulo Serre's regular divisibility lattice.

Each integer point mass may use an arbitrary integral linear combination of the Serre 18.4
simple Brauer rows. -/
def canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
    (π : ι → FDRep k G) : Prop :=
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
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The exact remaining Serre-basis input needed by the source-product route: integer
representatives modulo the diagonal divisibility lattice in both directions. -/
def canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
    (π : ι → FDRep k G) : Prop :=
  canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π ∧
    canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π

omit [Fintype ι] [DecidableEq ι] in
/-- The canonical-span forward input is the same as the regular-divisibility representative
input, by Serre 18.5(a) as formalized in
`canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule`. -/
theorem canonicalSourceProductSerreBasisForwardInput_iff_forwardDivisibilityRepresentatives
    (π : ι → FDRep k G) :
    canonicalSourceProductSerreBasisForwardInput
        (p := p) (A := A) (K := K) (G := G) π ↔
      canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · intro h i
    rcases h i with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hg
  · intro h i
    rcases h i with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hg

omit [DecidableEq ι] in
/-- The canonical-span reverse point input is the same as the regular-divisibility reverse point
representative input. -/
theorem canonicalSourceProductSerreBasisReversePointInput_iff_reversePointDivisibilityRepresentatives
    (π : ι → FDRep k G) :
    canonicalSourceProductSerreBasisReversePointInput
        (p := p) (A := A) (K := K) (G := G) π ↔
      canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · intro h c
    rcases h c with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hm
  · intro h c
    rcases h c with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hm

omit [Fintype ι] [DecidableEq ι] in
/-- Serre 18.5(a), forward direction: a projective-character restriction witness gives an
integer representative modulo the regular divisibility lattice. -/
theorem forwardDivisibilityRepresentatives_of_forwardProjectiveWitness
    (π : ι → FDRep k G)
    (hwitness :
      canonicalSourceProductSerreBasisForwardProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π := by
  intro i
  rcases hwitness i with ⟨g, Φ, hΦ, hΦres⟩
  refine ⟨g, ?_⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    ⟨Φ, hΦ, rfl⟩
  have hD :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [hΦres] using hD

omit [Fintype ι] [DecidableEq ι] in
/-- Serre 18.5(a), converse forward direction: membership in the regular divisibility lattice
is exactly the existence of a projective-character restriction witness. -/
theorem forwardProjectiveWitness_of_forwardDivisibilityRepresentatives
    (π : ι → FDRep k G)
    (hD :
      canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisForwardProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π := by
  intro i
  rcases hD i with ⟨g, hg⟩
  have hmap :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hg
  rcases Submodule.mem_map.1 hmap with ⟨Φ, hΦ, hΦres⟩
  refine ⟨g, Φ, hΦ, ?_⟩
  simpa [regularRestrictionLinearMap] using hΦres

omit [Fintype ι] [DecidableEq ι] in
/-- Forward projective-character witnesses are equivalent to forward integer representatives
modulo `D`. The latter is the actual missing integrality statement. -/
theorem forwardProjectiveWitness_iff_forwardDivisibilityRepresentatives
    (π : ι → FDRep k G) :
    canonicalSourceProductSerreBasisForwardProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π ↔
      canonicalSourceProductSerreBasisForwardDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact forwardDivisibilityRepresentatives_of_forwardProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π
  · exact forwardProjectiveWitness_of_forwardDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π

omit [DecidableEq ι] in
/-- Serre 18.5(a), reverse point direction: a projective-character restriction witness gives
reverse integer point representatives modulo the regular divisibility lattice. -/
theorem reversePointDivisibilityRepresentatives_of_reversePointProjectiveWitness
    (π : ι → FDRep k G)
    (hwitness :
      canonicalSourceProductSerreBasisReversePointProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases hwitness c with ⟨m, Φ, hΦ, hΦres⟩
  refine ⟨m, ?_⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    ⟨Φ, hΦ, rfl⟩
  have hD :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [hΦres] using hD

omit [DecidableEq ι] in
/-- Serre 18.5(a), converse reverse point direction: a reverse congruence modulo `D` is exactly
a projective-character restriction witness for that difference. -/
theorem reversePointProjectiveWitness_of_reversePointDivisibilityRepresentatives
    (π : ι → FDRep k G)
    (hD :
      canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisReversePointProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases hD c with ⟨m, hm⟩
  have hmap :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        ∑ i : ι,
          m i •
            virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π i]₀ : R₀[k](G)) ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hm
  rcases Submodule.mem_map.1 hmap with ⟨Φ, hΦ, hΦres⟩
  refine ⟨m, Φ, hΦ, ?_⟩
  simpa [regularRestrictionLinearMap] using hΦres

omit [DecidableEq ι] in
/-- Reverse point projective-character witnesses are equivalent to reverse integer point
representatives modulo `D`. -/
theorem reversePointProjectiveWitness_iff_reversePointDivisibilityRepresentatives
    (π : ι → FDRep k G) :
    canonicalSourceProductSerreBasisReversePointProjectiveWitness
        (p := p) (A := A) (K := K) (G := G) π ↔
      canonicalSourceProductSerreBasisReversePointDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact reversePointDivisibilityRepresentatives_of_reversePointProjectiveWitness
      (p := p) (A := A) (K := K) (G := G) π
  · exact reversePointProjectiveWitness_of_reversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π

omit [DecidableEq ι] in
/-- Combined equivalence: the source route needs exactly integer representatives modulo Serre's
divisibility lattice, not fixed point-mass congruences. -/
theorem serreBasisProjectiveWitness_iff_integerRepresentativesModuloD
    (π : ι → FDRep k G) :
    (canonicalSourceProductSerreBasisForwardProjectiveWitness
          (p := p) (A := A) (K := K) (G := G) π ∧
        canonicalSourceProductSerreBasisReversePointProjectiveWitness
          (p := p) (A := A) (K := K) (G := G) π) ↔
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · rintro ⟨hforward, hreverse⟩
    exact
      ⟨forwardDivisibilityRepresentatives_of_forwardProjectiveWitness
          (p := p) (A := A) (K := K) (G := G) π hforward,
        reversePointDivisibilityRepresentatives_of_reversePointProjectiveWitness
          (p := p) (A := A) (K := K) (G := G) π hreverse⟩
  · rintro ⟨hforward, hreverse⟩
    exact
      ⟨forwardProjectiveWitness_of_forwardDivisibilityRepresentatives
          (p := p) (A := A) (K := K) (G := G) π hforward,
        reversePointProjectiveWitness_of_reversePointDivisibilityRepresentatives
          (p := p) (A := A) (K := K) (G := G) π hreverse⟩

omit [DecidableEq ι] in
/-- Conditional endpoint from the exact Serre-basis integer representative input.

The hypotheses `hforward` and `hreverse` are precisely the two representative congruences stated
above, with arbitrary integer witnesses. No fixed simple-row/point-mass equality is required. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_integerRepresentativesModuloD
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hreps :
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
      ((canonicalSourceProductSerreBasisForwardInput_iff_forwardDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π).2 hreps.1)
      ((canonicalSourceProductSerreBasisReversePointInput_iff_reversePointDivisibilityRepresentatives
        (p := p) (A := A) (K := K) (G := G) π).2 hreps.2)

end CanonicalSourceProductSerreIntegralRepresentatives

end Representation
