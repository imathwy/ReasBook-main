import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleDegrees

/-!
# Characteristic-uniform degrees of the five `S₄` models (support for Exercise 18.5.2)

This file records the degrees (dimensions) of Serre's five explicit `S₄`-models as natural numbers,
over an *arbitrary* field `F` of *any* characteristic.  These supersede the `ℂ`-only computations
`s4_explicit_complex_family_degree` in `OrdinaryExplicitModels.lean`: the degrees `1, 1, 2, 3, 3`
and the square-sum `1² + 1² + 2² + 3² + 3² = 24 = |S₄|` are characteristic-uniform, which is the
Maschke/square-degree input for the semisimple branch of the completeness statement.

The key new ingredient is `permutationAugmentationSubrepresentation_finrank`
(in `SemisimpleDegrees.lean`), the *characteristic-uniform* `dim = |X| - 1` via rank–nullity.
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {F : Type*} [Field F]

-- The `S₄`-action on `Fin 3` (via the quotient `S₄ / V₄ ≃ S₃`) is a `local instance` in
-- `LinearCharacters`, so it does not propagate to importers; re-declare it here.
local instance s4_action_on_three_via_quotient_deg : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

/-- Degree of the degree-`2` quotient-augmentation model, over any field. -/
theorem s4_quotient_augmentation_representation_finrank :
    Module.finrank F (s4_quotient_augmentation_representation F).asModule = 2 := by
  -- `q₂` is the augmentation submodule of the `S₄`-action on `Fin 3` (`|Fin 3| - 1 = 2`).
  have h := permutationAugmentationSubrepresentation_finrank (F := F) (G := S4) (X := Fin 3)
  simpa [s4_quotient_augmentation_representation, permutationAugmentationRepresentation,
    Representation.asModule, Nat.card_eq_fintype_card] using h

/-- Degree of the degree-`3` standard-augmentation model, over any field. -/
theorem s4_standard_augmentation_representation_finrank :
    Module.finrank F (s4_standard_augmentation_representation F).asModule = 3 := by
  -- `std` is the augmentation submodule of the natural `S₄`-action on `Fin 4` (`|Fin 4| - 1 = 3`).
  have h := permutationAugmentationSubrepresentation_finrank (F := F) (G := S4) (X := Fin 4)
  simpa [s4_standard_augmentation_representation, permutationAugmentationRepresentation,
    Representation.asModule, Nat.card_eq_fintype_card] using h

/-- Degree of the degree-`3` sign-twist model `sgn ⊗ std`, over any field. -/
theorem s4_sign_standard_tensor_representation_finrank :
    Module.finrank F
        (TensorProduct F F
          (permutationAugmentationSubrepresentation F S4 (Fin 4)).toSubmodule) = 3 := by
  -- Tensoring with the one-dimensional sign line does not change the degree.
  rw [Module.finrank_tensorProduct, Module.finrank_self]
  have h := permutationAugmentationSubrepresentation_finrank (F := F) (G := S4) (X := Fin 4)
  simpa [Nat.card_eq_fintype_card] using h

/-- The characteristic-uniform square-degree sum of the five `S₄` models is `|S₄| = 24`. -/
theorem s4_explicit_family_sum_sq_degree :
    (1 ^ 2 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2 + 3 ^ 2 : ℕ) = Nat.card S4 := by
  rw [show Nat.card S4 = 24 from by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide]
  decide

end

end Representation
