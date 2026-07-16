import Mathlib
import StacksProject_2024.stacks_project.Chap08.Lemma_8_8_1
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [HasFiniteNonemptyLimits C]

/- Domain-style sampling for Definition 8.12.9:
- primary domain: stackifications of fibred categories over a site, specialized here to the
  canonical pushforward fibred category attached to `X` along `u`.
- inspected owner-level declarations:
  `StackOver`,
  `FibredCategoryMor.IsStackification`,
  `Functor.pushforwardProjection`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`.
- best owner abstraction: the source-facing inverse-image datum should use the chapter owner
  obtained by bundling the canonical projection `u.pushforwardProjection X.p` as a fibred
  category, together with a comparison morphism to `Y` and the morphism-owned predicate
  `FibredCategoryMor.IsStackification i`.
- primitive data: a target stack over `(D, K)`, a canonical comparison morphism from the bundled
  pushforward source to `Y`, and a proof that this morphism is a stackification.
- derived API: downstream universal-property equivalences recovered from the owner statement
  `Functor.IsEquivalence (stackification_precompose_functor _ i)` and its canonical
  `.asEquivalence`.

Source/core/bridge triage:
- `source-facing`: an inverse-image stack of `X` along `u`.
- `core/canonical`: `StackOver`, `Functor.pushforwardProjection`,
  `FibredCategoryMor.IsStackification`.
- `bridge/view`: the comparison morphism from the bundled pushforward source to `Y`. -/

variable (u : C ⥤ D) [PreservesFiniteNonemptyLimits u]
variable (X : StackOver J)
variable (Y : StackOver K)
variable [(u.pushforwardProjection X.p).IsFibered]
variable (i : FibredCategoryOver.ofFunctor (u.pushforwardProjection X.p) ⟶ Y)

/- Definition 8.12.9: an inverse-image stack of `X` along the morphism of sites represented by
`u` is a stack `Y` over `(D, K)` together with a morphism from the canonical pushforward fibred
category `u ₚ X` to `Y` that is a stackification. -/
#check (FibredCategoryMor.IsStackification i)

end

end CategoryTheory
