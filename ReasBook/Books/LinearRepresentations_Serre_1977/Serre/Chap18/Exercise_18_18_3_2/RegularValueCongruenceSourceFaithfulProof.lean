import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulBlocker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularValueCongruenceSourceFaithfulProof

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

local instance regularValueCongruenceSourceFaithfulProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueCongruenceSourceFaithfulProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact remaining local readback input needed to turn the existing Serre `18.5(a)`
projective-character divisibility theorem into the fixed-coordinate source-faithful congruence.

This is intentionally stated for the coordinate-normalized simple family used by
`regularClassCoordinateAddEquiv`.  It asks for the canonical `A`-valued Brauer-basis rows from
Exercise `18.4` to agree with those fixed integer coordinate rows modulo the centralizer
`p`-parts. -/
def regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single π hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            π hπ_simple hπ_coord)

/-- A closed adapter: the canonical Brauer-basis fixed-coordinate readback input is sufficient
for the requested local source-faithful regular-value congruence. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
    (hread : regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      π hπ_simple hπ_coord
  have hrow :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv ([π c]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [hπ_pairwise, hπ_complete] using
      ((fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete).2 hread)
  refine
    regularValueCongruence_of_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  intro c
  simpa [brauerPointMassSourceCongruence, hπ_coord c] using hrow c

end RegularValueCongruenceSourceFaithfulProof

section FullMixedModelRegularValueCongruenceSourceFaithfulProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelRegularValueCongruenceSourceFaithfulProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelRegularValueCongruenceSourceFaithfulProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model form of the remaining Brauer-basis fixed-coordinate readback input. -/
def fullMixedModelBrauerBasisReadbackInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)

/- A closed adapter from the full mixed-model readback input to the requested full mixed-model
regular-value congruence. -/
omit [IsAlgClosed k] [CharP k p] in
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

/-!
Minimal missing lemma for the exact local target:

```
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_proof :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G)
```

Equivalently, for one coordinate-normalized complete family `π`, prove
`brauerBasisFixedCoordinateReadbackDivisibility` for the canonical DVR Brauer basis from
Exercise `18.4`.  Expanded pointwise, the missing assertion is:

```
∀ c d : PRegularConjClass G p,
  ∃ a : A,
    canonicalDVRBrauerBasis π hπ_pairwise hπ_complete c d -
      ((regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a
```

This is the fixed-coordinate row readback congruence.  The existing files already prove Serre
`18.5(a)` as the projective-character divisibility lattice and already reduce the global
source-faithful statement to this readback input; the missing step is not the formal
projective-character lattice equality but this fixed-coordinate identification of the chosen
Brauer rows.
-/

end FullMixedModelRegularValueCongruenceSourceFaithfulProof

end Representation
