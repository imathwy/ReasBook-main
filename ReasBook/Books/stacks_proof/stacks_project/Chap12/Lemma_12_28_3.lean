import Mathlib.CategoryTheory.Preadditive.Projective.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

section

variable {Ω : Type v}
variable {C : Type u} [Category.{v} C]
variable (P : Ω → C)
variable [HasCoproduct P] [∀ ω, Projective (P ω)]

/- Domain-style sampling in the projective-object owner API:
- primitive owner predicate: `Projective`
- canonical lift across epis: `Projective.factorThru`
- owner stability under isomorphism: `Projective.of_iso`
- owner coproduct closure: the instance `Projective (∐ P)` in
  `Mathlib.CategoryTheory.Preadditive.Projective.Basic`
- best owner abstraction: `Projective (∐ P)`
- primitive data: a family `P : Ω → C` with a coproduct and objectwise projectivity
- derived API: the canonical instance exhibiting the coproduct itself as projective
- source/core/bridge triage:
  `source-facing`: the textbook lemma that a coproduct of projective objects is projective
  `core/canonical`: the upstream instance `Projective (∐ P)`
  `bridge/view`: none needed here

Lemma 12.28.3 is a `core/canonical` recall item: the source statement is exactly the upstream owner
instance asserting that a coproduct of projective objects is projective. The ambient abelian
hypothesis from the textbook is redundant for this canonical construction, so the refined Lean
interface keeps only the categorical data actually used by the owner abstraction.
-/
#check (inferInstance : Projective (∐ P))

end

end CategoryTheory
