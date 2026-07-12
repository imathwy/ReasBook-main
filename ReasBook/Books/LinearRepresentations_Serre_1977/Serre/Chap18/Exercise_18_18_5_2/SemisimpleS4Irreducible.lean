import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.GeneralFieldAugmentation

/-!
# Characteristic-uniform irreducibility of the augmentation `S₄`-models (support for Exercise 18.5.2)

Using the field-general augmentation criterion
`permutationAugmentationRepresentation_isIrreducible_of_two_pretransitive_overField`
(from `GeneralFieldAugmentation.lean`), the two augmentation `S₄`-models are irreducible over an
arbitrary field `k` in which the relevant orders are invertible:

* the degree-`3` **standard** model `std` (natural `S₄`-action on `Fin 4`), and
* the degree-`2` **quotient** model `q₂` (the `S₄`-action on `Fin 3` through `S₄ ↠ S₃`).

In the semisimple branch `ringChar k ∉ {2, 3}` of Exercise 18.5.2, `NeZero (Nat.card S₄ : k)` gives
all the required invertibility, so both models are irreducible there.  These supersede the `ℂ`-only
`OrdinaryExplicitModels.s4_standard_augmentation_representation_isIrreducible` and
`s4_quotient_augmentation_representation_isIrreducible`.
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation

namespace Representation

section

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type*} [Field k]

-- The `S₄`-action on `Fin 3` (via the quotient `S₄ / V₄ ≃ S₃`), re-declared locally (cf. siblings).
local instance s4_action_on_three_via_quotient_irr : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

/-- The standard degree-`3` `S₄`-model is irreducible over any field in which `|S₄|` and `|Fin 4|`
are invertible (in particular in the semisimple branch `ringChar k ∉ {2,3}`). -/
theorem s4_standard_augmentation_representation_isIrreducible_overField
    [Invertible (Nat.card S4 : k)] [Invertible (Nat.card (Fin 4) : k)] :
    (s4_standard_augmentation_representation k).IsIrreducible := by
  -- The natural `S₄`-action on four letters is doubly transitive.
  have h2 : MulAction.IsMultiplyPretransitive S4 (Fin 4) 2 :=
    Equiv.Perm.isMultiplyPretransitive (α := Fin 4) 2
  exact permutationAugmentationRepresentation_isIrreducible_of_two_pretransitive_overField h2

/-- The `S₃`-augmentation model on three letters is irreducible over any field in which `|S₃|` and
`|Fin 3|` are invertible. -/
theorem s3_augmentation_representation_isIrreducible_overField
    [Invertible (Nat.card S3 : k)] [Invertible (Nat.card (Fin 3) : k)] :
    (permutationAugmentationRepresentation k S3 (Fin 3)).IsIrreducible := by
  have h2 : MulAction.IsMultiplyPretransitive S3 (Fin 3) 2 :=
    Equiv.Perm.isMultiplyPretransitive (α := Fin 3) 2
  exact permutationAugmentationRepresentation_isIrreducible_of_two_pretransitive_overField h2

end

end Representation
