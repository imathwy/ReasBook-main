import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerOrthogonalityCongruenceWorker

/-!
Source-side closure boundary for the explicit orthogonality residual input.

The Exercise `18.4` pairing API already proves the two visible replacements

* `<Phi_c, phi_d> = delta_cd`, and
* `<Phi_c, 1_{d^{-1}}> = bA.repr (1_{d^{-1}}) c`.

After those replacements, the remaining source-side statement is exactly the pure `A`-valued
residual

```
bA c d - delta_cd - z(d) * (bA.repr (1_{d^{-1}}) c) = z(d) * a.
```

This file records the non-circular bridge from that smaller residual input to the requested
orthogonality input, without using the Cartan range/cokernel/product endpoint.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalOrthogonalityResidualSourceClosureWorker

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

local instance orthogonalityResidualSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityResidualSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family explicit source residual, with the pointwise shape left visible.

This is strictly smaller than `orthogonalityPairingSumResidualCongruence`: it contains no
projective-envelope family and no `K`-valued pairing sums. -/
def coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The explicit source residual is definitionally the pure `A`-side pairing residual isolated
by the earlier pairing worker. -/
theorem coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  rfl

/-- Fixed-family bridge: once the pure `A`-side residual is supplied, Exercise `18.4` and
`<Phi_E, phi_E'> = delta_EE'` convert it to the explicit orthogonality pairing-sum input. -/
theorem orthogonalityPairingSumResidualCongruence_of_explicitOrthogonalityResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual :
      coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  exact
    orthogonalityPairingSumResidualCongruence_of_coordinateNormalizedPairingResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      ((coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual)

/-- Existential bridge from the pure source residual to the named local orthogonality input. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsResidual
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    orthogonalityPairingSumResidualCongruence_of_explicitOrthogonalityResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      ((coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hresidual)

/-- Local equivalence: the requested orthogonality input is precisely the pure `A`-side
existential residual, after the two Exercise `18.4` pairing replacements. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_existsResidual :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof_of_orthogonalityInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsResidual
        (p := p) (A := A) (K := K) (G := G)

end LocalOrthogonalityResidualSourceClosureWorker

section FullMixedOrthogonalityResidualSourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedOrthogonalityResidualSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedOrthogonalityResidualSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic bridge from the smaller existential `A`-side residual blocker to
the requested full orthogonality input. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_of_existsResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_existsResidual
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic equivalence at the source boundary.  The forward direction is the
previous worker's descent from orthogonality sums; the reverse direction is the explicit residual
bridge in this file. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_iff_existsResidualBlocker :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_orthogonalityInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_of_existsResidualBlocker
        (p := p) (k := k) (G := G)

end FullMixedOrthogonalityResidualSourceClosureWorker

end Representation
