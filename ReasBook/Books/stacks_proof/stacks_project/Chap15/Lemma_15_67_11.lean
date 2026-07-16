import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Lemma_15_67_6
import stacks_proof.stacks_project.Chap15.Lemma_15_67_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/-- Lemma 15.67.11: if `K^•` has tor-amplitude in `[a, b]` over `B` and `B` is flat over `A`,
then `K^•`, viewed as a complex of `A`-modules by restriction of scalars, has tor-amplitude in
`[a, b]`. -/
@[stacks 066J]
theorem hasTorAmplitudeIn_restrictScalars_of_flat
    (K : DModB) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) a b := by
  -- Proof comment: this is exactly Lemma `15.67.12` specialized to tor dimension `0`, and
  -- flatness is equivalent to tor dimension at most `0` by Lemma `15.67.6`.
  simpa using
    hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE
      (A := A) (B := B) (a := a) (b := b) (d := 0) K
      ((ModuleCat.hasTorDimensionLE_zero_iff_flat (R := A) (M := ModuleCat.of A B)).2
        inferInstance)
      hK

end

end CategoryTheory
