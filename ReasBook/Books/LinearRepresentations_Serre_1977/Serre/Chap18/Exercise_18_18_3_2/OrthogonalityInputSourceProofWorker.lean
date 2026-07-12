import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker

/-!
Source-side boundary for the full mixed orthogonality input.

The explicit Serre `18.4` / projective-envelope orthogonality input is equivalent to the pure
point-mass source congruence

```
  bA c d - delta_cd = centralizerPPart(d) * a.
```

Thus an unconditional proof of the requested full mixed orthogonality input is exactly the
remaining local `18.5(a)` point-mass row congruence for a coordinate-normalized Brauer family.
This file does not use the Cartan range, cokernel, product, or determinant endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalOrthogonalityInputSourceProofWorker

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

local instance orthogonalityInputSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityInputSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal local source blocker for the orthogonality input.

After the two visible Serre pairings are evaluated by Exercise `18.4` and
`<Phi_E, phi_E'> = delta_EE'`, the requested orthogonality residual is precisely this
point-mass row congruence. -/
def regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
          ∃ _hP_envelope :
            ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope,
            let hπ_pairwise :=
              pairwiseNonisomorphic_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_coord
            let hπ_complete :=
              complete_irreducible_family_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_simple hπ_coord
            orthogonalityPairingSumPointMassSourceCongruence
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete

/-- Local exact reduction: the named orthogonality input is equivalent to the pure point-mass
source congruence. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) := by
  constructor
  · intro horth
    rcases horth with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, horth⟩
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    exact
      (orthogonalityPairingSumResidualCongruence_iff_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)
        P hP_envelope).1 horth
  · intro hblock
    rcases hblock with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hsource⟩
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    exact
      (orthogonalityPairingSumResidualCongruence_iff_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)
        P hP_envelope).2 hsource

/-- Adapter form: the local point-mass source congruence closes the local orthogonality input. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_sourceProof_of_pointMassSourceBlocker
    (hblock :
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
      (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
    (p := p) (A := A) (K := K) (G := G)).2 hblock

end LocalOrthogonalityInputSourceProofWorker

section FullMixedOrthogonalityInputSourceProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedOrthogonalityInputSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedOrthogonalityInputSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed package of the minimal local point-mass source congruence. -/
def fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact reduction: the requested orthogonality input is equivalent to the
point-mass source congruence blocker. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro horth A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).1
        (horth (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Adapter form: the full mixed point-mass source blocker closes the requested full mixed
orthogonality input. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_of_pointMassSourceBlocker
    (hblock :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
      (p := p) (A := A) (K := K) (G := G)).2
      (hblock (A := A) (K := K) e0)

end FullMixedOrthogonalityInputSourceProofWorker

end Representation
