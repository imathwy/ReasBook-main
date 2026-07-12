import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRowsProviderFinal

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

local instance pointMassProjectiveRowsProviderFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRowsProviderFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family projective-envelope residuals are already enough to provide the requested
point-mass projective rows.

This is the source-facing Serre `18.5(a)` route: the residual is converted to a projective
restriction by the regular-value divisibility criterion, then the visible projective-envelope row
is added back.  No Cartan range, cokernel, or product endpoint is used. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_fixedFamilyProjectiveEnvelopeResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)
    ⟨π, hπ_simple, hπ_coord,
      brauerPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hresidual⟩

/-- Existential projective-envelope residual input closes the local point-mass projective-row
provider. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidual
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, P, _hP_envelope, hresidual⟩
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_fixedFamilyProjectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hresidual

/-!
Smallest missing local source lemma for an unconditional provider:

```
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_proof :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
```

Equivalently, for one coordinate-normalized complete family `π` and projective envelopes `P`,
prove for all regular classes `c d` that

```
(modular row of π c at d - δ_c d)
  - regularRestriction (projective character of P c) d
```

is an `algebraMap A K` image of a `centralizerPPart p d.1` multiple.  This is exactly the
projective-envelope residual left after Exercise `18.4` orthogonality supplies the visible
projective-envelope row; it is not obtained here from any downstream Cartan/cokernel/product
endpoint.
-/

end LocalPointMassProjectiveRowsProviderFinal

section FullMixedPointMassProjectiveRowsProviderFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRowsProviderFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRowsProviderFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic point-mass projective-row provider from the projective-envelope
residual blocker. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidualBlocker
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

/-!
Smallest missing full mixed source lemma for an unconditional provider:

```
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_proof :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G)
```

The theorem above is the non-Cartan adapter from that residual input to
`fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput`.
-/

end FullMixedPointMassProjectiveRowsProviderFinal

end Representation
