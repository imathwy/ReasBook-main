import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker

/-!
Direct source-representative blocker for the Serre `18.5(a)` projective-character lattice route.

The point is to keep the integer representatives flexible.  Serre `18.4` and `18.5(a)` do not
force the fixed coordinate-normalized Brauer rows to be congruent to visible point masses; asking
for that would be the over-strong fixed-row congruence.  The remaining faithful source input is an
additive choice of integer regular-class representatives, compatible with the fixed coordinate map
only modulo Serre's diagonal lattice.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterLatticeDirectWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterLatticeDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal faithful source-representative blocker for the projective-character lattice target.

It asks for an additive integer representative `ρ` of every virtual modular character such that
the Serre `18.5(a)` residual `χ_x - ρ x` is coordinatewise divisible by the target centralizer
`p`-part, and such that `ρ` agrees with the fixed `regularClassCoordinateAddEquiv` coordinates
only modulo the integer diagonal lattice.  No fixed Brauer row or visible point-mass congruence is
part of this statement. -/
def projectiveCharacterLatticeDirectSourceRepresentativeBlocker : Prop :=
  ∃ ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ),
    (∀ x : R₀[IsLocalRing.ResidueField A](G),
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ∧
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ρ x -
            regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)

/-- The direct source-representative blocker closes the local projective-character lattice
congruence by Serre `18.5(a)`.

This is a one-way provider, not another equivalence boundary. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_directSourceRepresentativeBlocker
    (hblock :
      projectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hblock with ⟨ρ, hρD, hρcoord⟩
  refine
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_additiveRepresentativeModuloDiagonal
      (p := p) (A := A) (K := K) (G := G) ρ ?_ hρcoord
  intro x
  simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)] using hρD x

/-- Explicit arbitrary-representative form of the local projective-character lattice
congruence.  The extra compatibility is displayed directly: the chosen integer representative
must differ from the fixed regular-class coordinate representative by Serre's diagonal lattice. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_arbitraryRepresentativeModuloDiagonal
    (ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ))
    (hρD :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hρcoord :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ρ x -
            regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_directSourceRepresentativeBlocker
    (p := p) (A := A) (K := K) (G := G)
    ⟨ρ, hρD, hρcoord⟩

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Explicit arbitrary-representative form of the local regular-value source statement.

This is the same additive decomposition as the projective-character lattice provider, but it
lands directly in the regular-value source statement.  No point-mass rows are used. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_arbitraryRepresentativeModuloDiagonal
    (ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ))
    (hρD :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hρcoord :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ρ x -
            regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) := by
  intro x
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x
  let coord : PRegularConjClass G p → ℤ :=
    regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  have hdiag :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x - coord) ∈ D :=
    regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G)
      (by simpa [coord] using hρcoord x)
  have hdecomp :
      χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord =
        (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x)) +
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x - coord) := by
    ext c
    simp [regularIntegerFunctionCast]
  rw [show
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) =
        χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord by rfl]
  rw [hdecomp]
  exact D.add_mem (by simpa [D, χ] using hρD x) hdiag

end LocalProjectiveCharacterLatticeDirectWorker

section FullMixedProjectiveCharacterLatticeDirectWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic version of the direct source-representative blocker. -/
def fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      projectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed provider from the direct source-representative blocker to the projective-character
lattice congruence. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_directSourceRepresentativeBlocker
    (hblock :
      fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_directSourceRepresentativeBlocker
      (p := p) (A := A) (K := K) (G := G)
      (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed explicit arbitrary-representative provider for the projective-character lattice
congruence.  The hypothesis is the exact remaining compatibility datum: in each mixed model,
choose an additive integer representative modulo Serre's diagonal lattice whose residual lies in
the regular-value divisibility lattice. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_arbitraryRepresentativeModuloDiagonal
    (hrep :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∃ ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ),
            (∀ x : R₀[IsLocalRing.ResidueField A](G),
              virtualModularCharacterOnPRegularConjClass
                  (p := p) (A := K) (G := G)
                  (PrimeToPRoot.toFieldLift
                    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
                  regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ∧
              ∀ x : R₀[IsLocalRing.ResidueField A](G),
                ρ x -
                    regularClassCoordinateAddEquiv
                      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
                  regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hrep (A := A) (K := K) e0 with ⟨ρ, hρD, hρcoord⟩
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_arbitraryRepresentativeModuloDiagonal
      (p := p) (A := A) (K := K) (G := G) ρ hρD hρcoord

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed explicit arbitrary-representative provider for the regular-value source
statement.  This is the direct target-facing version of the same hypothesis, with no
point-mass-row interpretation. -/
theorem fullMixedModelRegularValueSourceStatement_of_arbitraryRepresentativeModuloDiagonal
    (hrep :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∃ ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ),
            (∀ x : R₀[IsLocalRing.ResidueField A](G),
              virtualModularCharacterOnPRegularConjClass
                  (p := p) (A := K) (G := G)
                  (PrimeToPRoot.toFieldLift
                    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
                  regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ∧
              ∀ x : R₀[IsLocalRing.ResidueField A](G),
                ρ x -
                    regularClassCoordinateAddEquiv
                      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
                  regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hrep (A := A) (K := K) e0 with ⟨ρ, hρD, hρcoord⟩
  exact
    regularValueCongruenceSourceFaithfulStatement_of_arbitraryRepresentativeModuloDiagonal
      (p := p) (A := A) (K := K) (G := G) ρ hρD hρcoord

omit [IsAlgClosed k] [CharP k p] in
/-- The same direct blocker also closes the regular-value source statement through the existing
projective-character lattice adapter. -/
theorem fullMixedModelRegularValueSourceStatement_of_directSourceRepresentativeBlocker
    (hblock :
      fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceStatement_sourceProof_of_projectiveCharacter_lattice
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_directSourceRepresentativeBlocker
      (p := p) (k := k) (G := G) hblock)

end FullMixedProjectiveCharacterLatticeDirectWorker

end Representation
