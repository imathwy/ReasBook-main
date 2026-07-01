import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable (F : A ⥤ B) [F.Additive]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/- Source/core/bridge triage for Lemma 12.3.7:
- source-facing: an additive functor preserves binary direct sums and zero objects
- core/canonical owner: `Functor.Additive`
- bridge/view: `PreservesBinaryBiproducts F` and `Functor.map_isZero` are derived from the owner,
  so they should remain recall-level consequences rather than new local wrapper declarations -/

/- Lemma 12.3.7 (1): this is a source-facing use of the canonical owner abstraction
`Functor.Additive`. In mathlib, additivity gives `PreservesFiniteBiproducts F`, and binary direct
sums are then recovered through the canonical derived instance `PreservesBinaryBiproducts F`. -/
#synth PreservesBinaryBiproducts F

/- Lemma 12.3.7 (2): preservation of zero objects is derived API, not extra primitive data. Once
`F` is additive, the canonical owner theorem is `Functor.map_isZero`. -/
recall Functor.map_isZero

end

end CategoryTheory
