import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Limits

universe v u

attribute [local instance] HasBinaryBiproduct.of_hasBinaryProduct

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (x y : C) [HasBinaryProduct x y]

/- Source/core/bridge triage for Definition 12.3.5:
- source-facing: the direct sum `x ⊕ y` is the binary product `x ⨯ y` together with the two
  projections and the two canonical inclusions
- primitive data: `prod x y`, `prod.fst`, and `prod.snd`
- derived API: the canonical inclusions `prod.inl` and `prod.inr`, obtained from the product
  structure together with the zero morphisms already supplied by `Preadditive C`
- core/canonical companion: Lemma 12.3.4 upgrades the same product-based data to the canonical
  binary biproduct view via `HasBinaryBiproduct.of_hasBinaryProduct`
- bridge/view: the chosen biproduct object `x ⊞ y`, compared to the source-facing product by
  `biprod.isoProd` -/
/- Definition 12.3.5: in a preadditive category, the textbook direct sum `x ⊕ y` is the binary
product `x × y`, i.e. the product object `x ⨯ y`. -/
recall prod

/- Companion recall: the source-facing direct sum comes with the usual projection maps
`prod.fst : x ⨯ y ⟶ x` and `prod.snd : x ⨯ y ⟶ y`. -/
recall prod.fst
recall prod.snd

/- Companion recall: in a preadditive category, the direct-sum inclusions into the source-facing
product object are the canonical morphisms `prod.inl : x ⟶ x ⨯ y` and
`prod.inr : y ⟶ x ⨯ y`. -/
recall prod.inl
recall prod.inr

/- Companion recall: Lemma 12.3.4 supplies the canonical binary biproduct view of the same
product-based direct sum. -/
recall HasBinaryBiproduct.of_hasBinaryProduct (x y : C) [HasBinaryProduct x y] :
    HasBinaryBiproduct x y

/- Companion recall: the chosen binary biproduct object `x ⊞ y` is canonically isomorphic to the
source-facing product object `x ⨯ y`. -/
recall biprod.isoProd

end

end CategoryTheory
