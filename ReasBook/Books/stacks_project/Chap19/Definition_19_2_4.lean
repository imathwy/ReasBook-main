import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for 19.2.4:
- primary domain: transfinite smallness conditions expressed by preservation of colimits of
  `α`-indexed diagrams under the represented functor `Hom(A, -) = coyoneda.obj (op A)`;
- sampled owner declarations:
  `PreservesColimit`,
  `colimit.post`,
  `preservesColimit_of_isIso_post`,
  `MorphismProperty.IsCardinalForSmallObjectArgument.preservesColimit`;
- best owner abstraction: for a fixed system `B`, the canonical owner is
  `PreservesColimit B (coyoneda.obj (op A))`; the extra restriction that every transition map of
  `B` lie in `I` is source-facing data of Definition 19.2.4, not a separate owner already present
  in mathlib/project;
- primitive data: an object `A`, a morphism property `I`, an ordinal `α`, an `α`-indexed diagram
  `B`, and the hypothesis that each structure map of `B` lies in `I`;
- derived API: the equivalent comparison-map formulation via
  `colimit.post B (coyoneda.obj (op A))`.

Source/core/bridge triage:
- `source-facing`: `is_alpha_small_wrt A I α`;
- `core/canonical`: `PreservesColimit B (coyoneda.obj (op A))` for each admissible system `B`;
- `bridge/view`: the comparison morphism `colimit.post B (coyoneda.obj (op A))`.

The deleted helper predicate and elimination theorem were only local packaging around this
canonical preservation condition.
-/

/-- Definition 19.2.4: an object `A` is `α`-small with respect to `I` if for every system
`B : α.ToType ⥤ C` whose transition maps lie in `I`, the functor `Hom(A, -)` preserves the
colimit of `B`; equivalently, the comparison map of `19.2.0.1` is an isomorphism for every such
system. -/
def is_alpha_small_wrt (A : C) (I : MorphismProperty C) (α : Ordinal) : Prop :=
  ∀ (B : α.ToType ⥤ C)
    (_ : ∀ ⦃j j' : α.ToType⦄ (f : j ⟶ j'), I (B.map f)),
      PreservesColimit B (coyoneda.obj (op A))

end

end CategoryTheory
