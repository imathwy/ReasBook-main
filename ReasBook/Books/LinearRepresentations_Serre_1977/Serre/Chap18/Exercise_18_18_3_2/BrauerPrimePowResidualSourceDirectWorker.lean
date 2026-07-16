import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.DVRValuationRegularValueSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Direct source-side adapters for the high-order prime-power pairing residual.

This file does not use Cartan range, cokernel, product, Smith, determinant, or endpoint
arguments.  It records the exact non-Cartan source datum still needed for an unconditional
proof of `coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem`: for every
coordinate-normalized Brauer family, the point-mass row difference must lie in Serre's
regular-value divisibility lattice.  Once that source-row datum is available, the existing
Exercise `18.4` / projective-envelope orthogonality bridge and the DVR high-order API give the
full `p ^ n` residual statement.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerPrimePowResidualSourceDirectWorker

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

local instance brauerPrimePowResidualSourceDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPrimePowResidualSourceDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family direct source adapter: Serre's point-mass regular-value row input gives the
high-order prime-power pairing residual for the same coordinate-normalized Brauer family. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_divisibility
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows)

/-- The same fixed-family adapter in exact DVR valuation form. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_pointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_primePowInput
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows)

/-- Local source theorem from the universal point-mass row source datum.  This is the exact
non-Cartan source lemma that would close the unconditional high-order residual target. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_of_pointMassRowsInRegularValueSubmoduleSource
    (hrows :
      ∀ (π : PRegularConjClass G p → FDRep kA G)
        (_hπ_simple : ∀ c, Simple (π c))
        (_hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
          (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord (hrows π hπ_simple hπ_coord)

/-- Existing projective-character lattice input supplies the local high-order source theorem.
This is an adapter only; the lattice input remains the substantive source obligation. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowSourceTheorem
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice
      π hπ_simple hπ_coord

end LocalBrauerPrimePowResidualSourceDirectWorker

section FullMixedBrauerPrimePowResidualSourceDirectWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerPrimePowResidualSourceDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerPrimePowResidualSourceDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Universal full mixed point-mass row source datum for every coordinate-normalized family.

This is stronger than the existing existential `fullMixedModelPointMassRowsInRegularValueSubmoduleInput`
and is exactly the direct row-level source obligation equivalent to the universal prime-power
residual blocker. -/
def fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker :
    Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
        (_hπ_simple : ∀ c, Simple (π c))
        (_hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G)
                ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
          (p := p) (A := A) (K := K) (G := G) π

omit [IsAlgClosed k] [CharP k p] in
/-- Universal point-mass row source data gives the full mixed high-order prime-power blocker. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_of_pointMassRowsInRegularValueSubmoduleBlocker
    (hrows :
      fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_pointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (hrows (A := A) (K := K) e0 π hπ_simple hπ_coord)

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the full mixed high-order prime-power blocker recovers the universal
point-mass row source datum by adding back the projective-envelope row. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker_of_pairingResidualPrimePowBlocker
    (hpow :
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (hpow (A := A) (K := K) e0 π hπ_simple hπ_coord))

omit [IsAlgClosed k] [CharP k p] in
/-- Exact source-side boundary for the universal direct row datum and the high-order
prime-power residual blocker. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_iff_pointMassRowsInRegularValueSubmoduleBlocker :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker_of_pairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_of_pointMassRowsInRegularValueSubmoduleBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The existing projective-character lattice source input supplies the universal direct row
datum.  This does not remove the source obligation; it only names its row-level form. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelCoordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmoduleBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π _hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_coord (hlattice (A := A) (K := K) e0)

end FullMixedBrauerPrimePowResidualSourceDirectWorker

end Representation
