import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : C)

/- Domain-style sampling for Lemma 12.3.4:
- primary domain: binary products, coproducts, and biproducts in a preadditive category;
- sampled canonical declarations:
  `HasBinaryBiproduct.of_hasBinaryProduct`,
  `HasBinaryBiproduct.of_hasBinaryCoproduct`,
  `HasBinaryBiproduct.hasLimit_pair`,
  `HasBinaryBiproduct.hasColimit_pair`;
- owner abstraction: `HasBinaryBiproduct X Y`;
- primitive data: a chosen binary product or binary coproduct structure on `X` and `Y`;
- derived API: the opposite finite-limit/finite-colimit structure obtained from the owner
  biproduct instance.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence between existence of the binary product and binary
  coproduct of `X` and `Y`;
- `core/canonical`: the owner instance `HasBinaryBiproduct X Y`;
- `bridge/view`: the equivalence theorem below, obtained by passing through that owner. -/

/- Core/canonical owner declaration used in Lemma 12.3.4: in a preadditive category, a binary
product canonically yields a binary biproduct. -/
recall HasBinaryBiproduct.of_hasBinaryProduct (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y

/- Core/canonical owner declaration used in Lemma 12.3.4: dually, a binary coproduct canonically
yields a binary biproduct. -/
recall HasBinaryBiproduct.of_hasBinaryCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y

/-- Lemma 12.3.4: in a preadditive category, a binary product of `x` and `y` exists if and only
if a binary coproduct of `x` and `y` exists. -/
@[stacks 0101]
theorem hasBinaryProduct_iff_hasBinaryCoproduct
    : HasBinaryProduct X Y ↔ HasBinaryCoproduct X Y := by
  constructor
  · intro _
    let _ : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
    infer_instance
  · intro _
    let _ : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryCoproduct X Y
    infer_instance

end

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (X Y : C) [HasBinaryBiproduct X Y]

/- The final sentence of Lemma 12.3.4 is the existing mathlib comparison isomorphism `biprodIso`
in the chosen binary biproduct context. -/
recall biprodIso

end

end CategoryTheory
