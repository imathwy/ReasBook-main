import Mathlib.CategoryTheory.Preadditive.Injective.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u u'

section

variable {C : Type u} [Category.{v} C]
variable {Ω : Type u'} (I : Ω → C) [HasProduct I] [∀ ω, Injective (I ω)]

/- Domain-style sampling for Lemma 12.27.3:
- primary domain: injective objects in a category, together with their stability under products;
- sampled owner API:
  `Injective`,
  `Injective.factors`,
  `Injective.factorThru`,
  the product instance `Injective (∏ᶜ I)` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`;
- best owner abstraction: `Injective (∏ᶜ I)`;
- primitive data: only the family `I`, the product existence hypothesis `[HasProduct I]`, and the
  objectwise injective instances `[∀ ω, Injective (I ω)]`;
- derived API: the injective structure on the product itself, obtained canonically by instance
  synthesis.

This item is a `core/canonical` recall: the textbook statement is exactly the upstream owner
instance that products of injective objects are injective, so no local wrapper theorem is needed.
-/

/- Lemma 12.27.3: if `I : Ω → C` is a family of injective objects and the product `∏ᶜ I`
exists, then `∏ᶜ I` is injective. This is exactly the canonical product instance for
`Injective`. -/
#synth Injective (∏ᶜ I)

end
