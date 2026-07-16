import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueSourceCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalRegularValueRowSourceFinal

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

local instance regularValueRowSourceFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueRowSourceFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The existing projective-restriction witness is the exact source-side form needed by
`regularValueSourceCompletionPointMassProjectiveRowInput`: it gives an explicit projective
character whose regular restriction is each point-mass row difference. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
  refine Submodule.mem_map.2 ?_
  refine ⟨Φ, hΦ, ?_⟩
  simpa [regularRestrictionLinearMap] using hΦres

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, the row-source input can be unpacked into the more explicit projective
restriction witness by choosing a preimage in the mapped projective-character lattice. -/
theorem projectiveRestrictionWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases Submodule.mem_map.1 (hrows c) with ⟨Φ, hΦ, hΦres⟩
  refine ⟨Φ, hΦ, ?_⟩
  simpa [regularRestrictionLinearMap] using hΦres

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The target local row input is equivalent to the explicit projective-restriction source
blocker.  Thus an unconditional proof of the right-hand side is exactly enough to obtain
`regularValueSourceCompletionPointMassProjectiveRowInput_proof`. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitness :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      projectiveRestrictionWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)

/-- Serre `18.5(a)` row-divisibility witnesses directly provide the requested point-mass
projective-row input.

This is the non-circular provider for the lattice/row route: the only substantive source input is
that each coordinate-normalized row difference already lies in Serre's regular-value divisibility
lattice.  The formalized `18.5(a)` equality then produces the projective-restriction witness. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_regularValueWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    (existsPointMassProjectiveRestrictionWitness_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) hwitness)

/-- Named local blocker left by this file: construct the projective-restriction witness for one
coordinate-normalized complete simple family. -/
def regularValueRowSourceFinalProjectiveRestrictionBlocker : Prop :=
  regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The named blocker immediately gives the requested local row source input. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_rowSourceFinalBlocker
    (hblock :
      regularValueRowSourceFinalProjectiveRestrictionBlocker
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G) hblock

end LocalRegularValueRowSourceFinal

section FullMixedRegularValueRowSourceFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedRegularValueRowSourceFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedRegularValueRowSourceFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model bridge from the explicit projective-restriction blocker to the requested
point-mass projective row input. -/
theorem
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitnessBlocker
    (hblock :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G)
      (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed row input unpacks back to the explicit projective-restriction blocker. -/
theorem
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueSourceCompletionPointMassProjectiveRowInput
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveRestrictionWitness_of_regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model exact equivalence.  An unconditional proof of the right-hand side is the
remaining source theorem needed for
`fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_proof`. -/
theorem
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitnessBlocker :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model provider from the row-divisibility form of Serre `18.5(a)` to the requested
point-mass projective-row input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_regularValueWitnessBlocker
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitnessBlocker
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

/-- Named full mixed blocker left by this file. -/
def fullMixedModelRegularValueRowSourceFinalProjectiveRestrictionBlocker : Prop :=
  fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
    (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The named full mixed blocker immediately gives the requested full mixed row source input. -/
theorem
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_rowSourceFinalBlocker
    (hblock :
      fullMixedModelRegularValueRowSourceFinalProjectiveRestrictionBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitnessBlocker
    (p := p) (k := k) (G := G) hblock

end FullMixedRegularValueRowSourceFinal

end Representation
