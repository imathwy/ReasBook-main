import Mathlib
import StacksProject_2024.Chap04.Lemma_4_18_3
import StacksProject_2024.Chap08.Lemma_8_8_1
import StacksProject_2024.Chap08.Lemma_8_12_5

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
variable [(u.pushforwardProjection X.p).IsFibered]

/-- Helper for Definition 8.12.4: the source fibred category underlying an inverse-image stack
along `u` is the canonical bundled pushforward projection `u.pushforwardProjection X.p`. -/
noncomputable abbrev pushforward_source_over : FibredCategoryOver D :=
  FibredCategoryOver.ofFunctor (u.pushforwardProjection X.p)

-- Route correction: the metadata text points to Definition `8.12.4`, but the concrete file and
-- downstream Chapter 8 owner context require the inverse-image-stack packaging of Definition
-- `8.12.9`.
/-- Definition 8.12.9: an inverse-image stack of `X` along the morphism of sites represented by
`u` is a stack `Y` over `(D, K)` together with a morphism from the canonical pushforward fibred
category attached to `X` along `u` to `Y`, and a proof that this morphism is a stackification. -/
@[stacks 04WJ]
structure InverseImageStackAlong where
  /-- The chosen target stack over `(D, K)`. -/
  Y : StackOver K
  /-- The canonical comparison from the bundled pushforward source to the chosen target stack. -/
  i : pushforward_source_over u X ⟶ Y
  /-- The comparison morphism exhibits the target as a stackification of the pushforward source. -/
  hi : FibredCategoryMor.IsStackification i

end

end CategoryTheory
