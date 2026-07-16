import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.VisibleReadbackDiagonalSourceCompletionWorker

/-!
Diagonal source-side proof worker for visible point-mass readback.

The `centralizerPPart = 1` branch and the projective-envelope delta readout are already
available in `VisibleReadbackDiagonalSourceCompletionWorker`.  The nontrivial branch still
requires the local diagonal divisibility statement

```
∀ π hπ_simple hπ_coord c,
  ConjClasses.centralizerPPart p c.1 ≠ 1 →
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a
```

Equivalently, in the fraction-field/projective-envelope route isolated upstream, the missing
input is the diagonal readout hypothesis expected by
`exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma_of_diagonalPairingReadout`:

```
∃ P, hP_envelope ∧
  ∀ c, ConjClasses.centralizerPPart p c.1 ≠ 1 →
    ∃ a : A,
      algebraMap A K (bA c c) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) (bA c) =
      algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a)
```

No unconditional theorem is added here: the current local API only proves the trivial
centralizer branch and conditional adapters for the nontrivial branch.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation ZeroObject

universe u

namespace Representation

section VisibleReadbackDiagonalSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance visibleReadbackDiagonalSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackDiagonalSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

end VisibleReadbackDiagonalSourceProofWorker

end Representation
