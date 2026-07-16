import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityResidualSourceClosureWorker

/-!
Source-side adapters for the projective-envelope residual input.

The target `fullMixedModelProjectiveEnvelopeResidualSourceInput` is definitionally the same
existential `A`-valued Brauer pairing residual package used by the orthogonality workers.  This
file records that identity and compresses the remaining full mixed source obligation to the
explicit Exercise `18.4` / projective-envelope orthogonality input.  No Cartan cokernel, product,
or range endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveEnvelopeResidualSourceProofWorker

variable {p : Nat}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveEnvelopeResidualSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeResidualSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local identity adapter: the projective-envelope residual source input is exactly the
existential `A`-side Brauer pairing residual package. -/
theorem regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualProof :
    regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) := by
  rfl

/-- Local compression to the explicit Exercise `18.4` / projective-envelope orthogonality input.
This is only a source-side formula adapter. -/
theorem regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_orthogonalityInput :
    regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualProof
    (p := p) (A := A) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_existsResidual
      (p := p) (A := A) (K := K) (G := G)).symm

/-- One-way local source closure from the explicit orthogonality residual input. -/
theorem regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_of_orthogonalityInput
    (horth :
      regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_orthogonalityInput
    (p := p) (A := A) (K := K) (G := G)).2 horth

end LocalProjectiveEnvelopeResidualSourceProofWorker

section FullMixedProjectiveEnvelopeResidualSourceProofWorker

variable {p : Nat}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveEnvelopeResidualSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveEnvelopeResidualSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed identity adapter: the requested projective-envelope residual input is exactly the
full mixed existential `A`-side Brauer pairing residual blocker. -/
theorem fullMixedModelProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualBlocker :
    fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hsource A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualProof
        (p := p) (A := A) (G := G)).1
        (hsource (A := A) (K := K) e0)
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualProof
        (p := p) (A := A) (G := G)).2
        (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed compression to the explicit Exercise `18.4` / projective-envelope orthogonality
source input. -/
theorem fullMixedModelProjectiveEnvelopeResidualSourceInput_iff_orthogonalityInput_sourceProof :
    fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveEnvelopeResidualSourceInput_iff_existsPairingResidualBlocker
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_iff_existsResidualBlocker
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- One-way full mixed source closure from the explicit orthogonality residual input. -/
theorem fullMixedModelProjectiveEnvelopeResidualSourceInput_sourceProof_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveEnvelopeResidualSourceInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR
    _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
    _instRoots _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_of_orthogonalityInput
      (p := p) (A := A) (K := K) (G := G)
      (horth (A := A) (K := K) e0)

/-!
Remaining unconditional source lemma:

```
theorem fullMixedModelProjectiveEnvelopeResidualSourceInput_sourceProof :
    fullMixedModelProjectiveEnvelopeResidualSourceInput (p := p) (k := k) (G := G)
```

By the equivalence above, the missing API is exactly
`fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput`: locally, for one
coordinate-normalized complete family and projective envelopes, prove the
`orthogonalityPairingSumResidualCongruence` residual left after the two Serre `18.4` /
projective-envelope pairing replacements.  This file only records the identity/compression
adapter, not that source theorem.
-/

end FullMixedProjectiveEnvelopeResidualSourceProofWorker

end Representation
