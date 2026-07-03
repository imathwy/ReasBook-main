import Mathlib
import stacks_project.Chap08.Lemma_8_8_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver C} {S' X : StackOver J}

/- Domain-style sampling for Lemma 8.8.2:
- primary domain: the universal property of stackification for morphisms from a fibred category
  into a stack.
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`,
  `Functor.asEquivalence`,
  `Functor.objPreimage`.
- best owner abstraction: the canonical owner is the precomposition functor
  `stackification_precompose_functor X G`, together with the owner predicate
  `Functor.IsEquivalence`.
- primitive data: a stackification morphism `G : S ⟶ S'` and a target stack morphism
  `F : S ⟶ X`.
- derived API: the chosen lift object in `(S' ⟶ X)` coming from
  `(stackification_precompose_functor X G).asEquivalence.inverse`, together with the counit
  isomorphism expressing `G ≫ H ≅ F`.

Source/core/bridge triage:
- `source-facing`: the existence of a factorization of `F` through the stackification morphism
  `G`, up to `2`-isomorphism.
- `core/canonical`: the owner predicate `Functor.IsEquivalence` on
  `stackification_precompose_functor X G`.
- `bridge/view`: the specific lifted morphism
  `H := (stackification_precompose_functor X G).asEquivalence.inverse.obj F` and the counit
  isomorphism of that canonical equivalence at `F`. -/

-- Proof sketch: use local essential surjectivity in `hG` to cover each object of `S'` by objects
-- coming from `S`, apply `F` on those local models, and then descend the resulting local objects
-- and morphisms along the stack condition on `X`. The descended objects define the lift `H`, and
-- the local identifications glue to a compatible `2`-isomorphism from the composite of `G` and
-- `H` to `F`.
/-- Lemma 8.8.2: if `G : S ⟶ S'` exhibits `S'` as a stackification of the fibred category `S`
over `(C, J)`, then every morphism `F : S ⟶ X` to a stack `X` factors through `S'` by a morphism
`H : S' ⟶ X` together with a `2`-isomorphism from the composite `G ≫ H` to `F`. -/
theorem isStackification_exists_lift_to_stack
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∃ H : S' ⟶ X, Nonempty (G ≫ H ≅ F) := by
  let _ :
      Functor.IsEquivalence
        (stackification_precompose_functor X G : (S' ⟶ X) ⥤ (S ⟶ X)) :=
    stackification_precompose_functor_isEquivalence X G hG
  let e := (stackification_precompose_functor X G).asEquivalence
  refine ⟨e.inverse.obj F, ?_⟩
  change Nonempty (e.functor.obj (e.inverse.obj F) ≅ F)
  exact ⟨e.counitIso.app F⟩

end

end CategoryTheory
