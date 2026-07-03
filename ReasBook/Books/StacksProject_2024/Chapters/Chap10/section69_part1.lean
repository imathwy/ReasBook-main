import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_69_1 (from Chap10) -/
universe u v

open RingTheory
open Function
open scoped TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Definition 10.69.1: a sequence `rs` is `M`-quasi-regular when the canonical associated-graded
map of `10.69.0.1` is an isomorphism of `(R / Ideal.ofList rs)[X₁, ..., X_c]`-modules. -/
def IsQuasiRegular (M : Type v) [AddCommGroup M] [Module R M] (rs : List R) : Prop :=
  Bijective (quasiRegularSequenceAssociatedGradedMap M rs)

/-- Helper for Definition 10.69.1: injectivity of the canonical associated-graded map upgrades to
quasi-regularity once the surjectivity half of `10.69.0.1` is available in the imported API. -/
theorem isQuasiRegular_of_injective (rs : List R) :
    Injective (quasiRegularSequenceAssociatedGradedMap M rs) → IsQuasiRegular M rs :=
  -- TODO: apply `fun h ↦ ⟨h, quasiRegularSequenceAssociatedGradedMap_surjective M rs⟩` after
  -- `10.69.0.1` exports the surjectivity owner theorem under a stable name.
  sorry

/-- Since Equation `10.69.0.1` is always surjective, quasi-regularity is equivalently injectivity
of the canonical associated-graded map. -/
theorem isQuasiRegular_iff_injective (rs : List R) :
    IsQuasiRegular M rs ↔ Injective (quasiRegularSequenceAssociatedGradedMap M rs) := by
  constructor
  · -- Bijectivity already contains the injective half.
    exact Bijective.injective
  · -- The converse is the isolated prerequisite bridge above.
    exact isQuasiRegular_of_injective (M := M) rs

namespace IsQuasiRegular

/-- The canonical linear equivalence attached to a quasi-regular sequence. -/
noncomputable def linearEquiv {rs : List R} (hqr : IsQuasiRegular M rs) :
    ((M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      idealAssociatedGradedModule (Ideal.ofList rs) M :=
  LinearEquiv.ofBijective (quasiRegularSequenceAssociatedGradedMap M rs) hqr

end IsQuasiRegular

/-- A finite sequence in a commutative ring is quasi-regular when it is quasi-regular on the
regular module `R`. -/
abbrev IsQuasiRegularSequence (rs : List R) : Prop :=
  IsQuasiRegular R rs

end RingTheory.Sequence
