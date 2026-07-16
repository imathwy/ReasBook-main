import Mathlib
import stacks_proof.stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory
open Function
open scoped TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Definition 10 69 1: a sequence `rs` is `M`-quasi-regular when the canonical
associated-graded map of `10.69.0.1` is an isomorphism of
`(R / Ideal.ofList rs)[X₁, ..., X_c]`-modules. -/
@[stacks 061P]
def IsQuasiRegular (M : Type v) [AddCommGroup M] [Module R M] (rs : List R) : Prop :=
  Bijective (quasiRegularSequenceAssociatedGradedMap M rs)

/-- Chap10 Definition 10 69 1: injectivity of the canonical associated-graded map
upgrades to quasi-regularity once the surjectivity half of `10.69.0.1` is available in the
imported API. -/
theorem isQuasiRegular_of_injective (rs : List R) :
    Injective (quasiRegularSequenceAssociatedGradedMap M rs) → IsQuasiRegular M rs := by
  -- Quasi-regularity is bijectivity of the comparison map, so the hypothesis gives one half.
  intro h
  -- The imported construction theorem supplies the surjective half for the same map.
  exact ⟨h, quasiRegularSequenceAssociatedGradedMap_surjective M rs⟩

/-- Helper for Chap10 Definition 10 69 1: quasi-regularity is equivalently injectivity of the
canonical associated-graded map, since Equation `10.69.0.1` is always surjective. -/
theorem isQuasiRegular_iff_injective (rs : List R) :
    IsQuasiRegular M rs ↔ Injective (quasiRegularSequenceAssociatedGradedMap M rs) := by
  constructor
  · -- Bijectivity already contains the injective half.
    exact Bijective.injective
  · -- The converse is the isolated prerequisite bridge above.
    exact isQuasiRegular_of_injective (M := M) rs

namespace IsQuasiRegular

/-- Helper for Chap10 Definition 10 69 1: the canonical linear equivalence attached to a
quasi-regular sequence. -/
noncomputable def linearEquiv {rs : List R} (hqr : IsQuasiRegular M rs) :
    ((M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      idealAssociatedGradedModule (Ideal.ofList rs) M :=
  LinearEquiv.ofBijective (quasiRegularSequenceAssociatedGradedMap M rs) hqr

end IsQuasiRegular

/-- Helper for Chap10 Definition 10 69 1: a finite sequence in a commutative ring is
quasi-regular when it is quasi-regular on the regular module `R`. -/
abbrev IsQuasiRegularSequence (rs : List R) : Prop :=
  IsQuasiRegular R rs

end RingTheory.Sequence
