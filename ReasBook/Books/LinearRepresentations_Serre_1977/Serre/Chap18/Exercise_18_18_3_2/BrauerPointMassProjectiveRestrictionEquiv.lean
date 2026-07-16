import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassDivisibilityProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulBlocker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassProjectiveRestrictionEquiv

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassProjectiveRestrictionEquivFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassProjectiveRestrictionEquivDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre 18.5(a) in point-mass form: once the fixed row difference satisfies the
coordinatewise divisibility condition, the projective-character restriction witness exists. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcoord :
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  let f : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  have hfD : f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) f).2 ?_
    intro d
    rcases hcoord c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [f, virtualModularCharacterOnPRegularConjClass_class] using ha
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

/-- The projective-restriction and coordinate-divisibility versions of the fixed point-mass
blocker are equivalent. -/
theorem brauerPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      brauerPointMassCoordinateDivisibility_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      brauerPointMassProjectiveRestrictionWitness_of_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

end BrauerPointMassProjectiveRestrictionEquiv

section BrauerPointMassProjectiveRestrictionBlocker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassProjectiveRestrictionBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassProjectiveRestrictionBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Existence of one coordinate-normalized Brauer family satisfying the projective-restriction
witness form of the fixed point-mass congruence. -/
def regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness : Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)
              ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        brauerPointMassProjectiveRestrictionWitness
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The projective-restriction and coordinatewise-divisibility existential blockers are
equivalent by Serre 18.5(a). -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, hwitness⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hwitness
  · rintro ⟨π, hπ_simple, hπ_coord, hcoord⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcoord

end BrauerPointMassProjectiveRestrictionBlocker

section FullMixedModelBrauerPointMassProjectiveRestrictionBlocker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassProjectiveRestrictionBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassProjectiveRestrictionBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model version of the projective-restriction point-mass blocker. -/
def fullMixedModelPointMassProjectiveRestrictionWitnessBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed-model projective-restriction and coordinate-divisibility blockers are
equivalent. -/
theorem
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_coordinateDivisibilityBlocker :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).1
        (hblock (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

end FullMixedModelBrauerPointMassProjectiveRestrictionBlocker

end Representation
