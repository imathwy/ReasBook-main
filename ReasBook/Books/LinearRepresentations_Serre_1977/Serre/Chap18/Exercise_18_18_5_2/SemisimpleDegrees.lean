import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4

/-!
# Characteristic-uniform degrees of the augmentation constituents (support for Exercise 18.5.2)

This file records the *degree* (dimension) of the permutation-augmentation constituent
`permutationAugmentationSubrepresentation F G X` as a **natural number**, valid over an
*arbitrary* field `F` (no characteristic restriction and no invertibility of `|G|` or `|X|`).

The existing degree computations in `OrdinaryExplicitModels.lean` are stated over `ℂ` and route
through the character value at the identity (`χ(1) = dim`); transferring that argument to a field
of positive characteristic is delicate because `(χ(1) : F) = (n : F)` only determines `n` modulo
the characteristic.  Here we instead use the **structural** description of the augmentation
submodule as the kernel of the augmentation (sum) map and rank–nullity, which gives the degree as
a genuine natural-number identity `dim = |X| - 1` in every characteristic.
-/

noncomputable section

open Representation

namespace Representation

section

variable {F : Type*} [Field F] {G : Type*} [Monoid G] {X : Type*} [MulAction G X]

/-- The augmentation (sum) map `(X →₀ F) → F` is surjective whenever `X` is nonempty: it sends the
basis vector `Finsupp.single x 1` to `1`. -/
lemma permutationAugmentationLinearMap_surjective [Nonempty X] :
    Function.Surjective (permutationAugmentationLinearMap F X) := by
  intro c
  refine ⟨Finsupp.single (Classical.arbitrary X) c, ?_⟩
  simp [permutationAugmentationLinearMap]

/-- The range of the augmentation map is all of `F`, hence one-dimensional. -/
lemma permutationAugmentationLinearMap_finrank_range [Nonempty X] :
    Module.finrank F (LinearMap.range (permutationAugmentationLinearMap F X)) = 1 := by
  rw [LinearMap.range_eq_top.mpr (permutationAugmentationLinearMap_surjective (F := F) (X := X))]
  simp

/-- **Characteristic-uniform degree of the augmentation constituent.**  Over any field `F`, the
augmentation subrepresentation of a finite nonempty `G`-set `X` has dimension `|X| - 1`.  The
proof is rank–nullity applied to the surjective augmentation (sum) map, so it needs no assumption
on the characteristic of `F` nor on the invertibility of `|G|` or `|X|`. -/
theorem permutationAugmentationSubrepresentation_finrank [Finite X] [Nonempty X] :
    Module.finrank F (permutationAugmentationSubrepresentation F G X).toSubmodule
      = Nat.card X - 1 := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  -- The augmentation submodule is the kernel of the augmentation (sum) linear map.
  have hker :
      (permutationAugmentationSubrepresentation F G X).toSubmodule
        = LinearMap.ker (permutationAugmentationLinearMap F X) := rfl
  -- Rank–nullity for the augmentation map: `dim range + dim ker = dim (X →₀ F)`.
  have hrn :
      Module.finrank F (LinearMap.range (permutationAugmentationLinearMap F X))
        + Module.finrank F (LinearMap.ker (permutationAugmentationLinearMap F X))
        = Module.finrank F (X →₀ F) :=
    LinearMap.finrank_range_add_finrank_ker (permutationAugmentationLinearMap F X)
  have hrange : Module.finrank F (LinearMap.range (permutationAugmentationLinearMap F X)) = 1 :=
    permutationAugmentationLinearMap_finrank_range (F := F) (X := X)
  have hdom : Module.finrank F (X →₀ F) = Nat.card X := by
    rw [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]
  rw [hrange, hdom] at hrn
  rw [hker]
  omega

end

end Representation
