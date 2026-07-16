import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.VisibleReadbackOffDiagonalSourceCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerNontrivialCentralizerRowCompletionWorker

/-!
Off-diagonal direct Brauer-character worker.

The off-diagonal target follows immediately from the nontrivial-column pointwise
Brauer-character congruence: away from the diagonal, the coordinate point mass is zero.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section OffDiagonalBrauerCharacterUnconditionalWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance offDiagonalBrauerCharacterUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance offDiagonalBrauerCharacterUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The nontrivial-column pointwise Brauer-character congruence closes the requested
off-diagonal direct Brauer-character source statement. -/
theorem exercise18_4PointMassRowVisibleReadbackOffDiagonalBrauerCharacterSourceLemma_of_nontrivialPointwiseReadbackCongruenceAPI
    (hpoint :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackOffDiagonalBrauerCharacterSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c d hcd hd
  rcases hpoint π hπ_simple hπ_coord c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdc : d ≠ c := fun h => hcd h.symm
  have hsingle :
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) = 0 := by
    simp [hdc]
  simpa [hsingle] using ha

end OffDiagonalBrauerCharacterUnconditionalWorker

end Representation
