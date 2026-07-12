import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeDirectWorker

/-!
Direct representative boundary for the Serre `18.5(a)` source statement.

The direct representative blocker is not weaker than the usual regular-value source
congruence: because its representative is required to agree with the fixed regular-class
coordinate map modulo the integer diagonal lattice, it is exactly the same source obligation.
This file records both directions without using Cartan final/cokernel/product/Smith/determinant
endpoints to manufacture source-side input.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalDirectRepresentativeUnconditionalWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance directRepresentativeUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance directRepresentativeUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The regular-value source statement constructs the direct additive representative by taking
`ρ` to be the fixed regular-class coordinate map. -/
theorem projectiveCharacterLatticeDirectSourceRepresentativeBlocker_of_regularValueCongruenceSourceFaithfulStatement
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeDirectSourceRepresentativeBlocker
      (p := p) (A := A) (K := K) (G := G) := by
  let ρ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → ℤ) :=
    (regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).toAddMonoidHom
  refine ⟨ρ, ?_, ?_⟩
  · intro x
    simpa [ρ] using hregular x
  · intro x
    simp [ρ]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, any direct representative satisfying the diagonal compatibility gives the usual
regular-value source congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacterLatticeDirectSourceRepresentativeBlocker
    (hblock :
      projectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hblock with ⟨ρ, hρD, hρcoord⟩
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

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The direct representative blocker is exactly the existing regular-value source statement. -/
theorem projectiveCharacterLatticeDirectSourceRepresentativeBlocker_iff_regularValueCongruenceSourceFaithfulStatement :
    projectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (A := A) (K := K) (G := G)
  · exact
      projectiveCharacterLatticeDirectSourceRepresentativeBlocker_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)

end LocalDirectRepresentativeUnconditionalWorker

section FullMixedDirectRepresentativeUnconditionalWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedDirectRepresentativeUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedDirectRepresentativeUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed version: the regular-value source statement constructs the direct additive
representative in every mixed-characteristic model. -/
theorem fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker_of_regularValueSourceStatement
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeDirectSourceRepresentativeBlocker_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed reverse direction: the direct representative blocker gives the regular-value
source statement in every mixed-characteristic model. -/
theorem fullMixedModelRegularValueSourceStatement_of_directSourceRepresentativeBlocker_boundary
    (hblock :
      fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacterLatticeDirectSourceRepresentativeBlocker
      (p := p) (A := A) (K := K) (G := G)
      (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed direct representative blocker is exactly the existing full mixed regular-value
source statement. -/
theorem fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker_iff_regularValueSourceStatement :
    fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelRegularValueSourceStatement_of_directSourceRepresentativeBlocker_boundary
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelProjectiveCharacterLatticeDirectSourceRepresentativeBlocker_of_regularValueSourceStatement
        (p := p) (k := k) (G := G)

end FullMixedDirectRepresentativeUnconditionalWorker

end Representation
