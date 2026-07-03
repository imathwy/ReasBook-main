import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_6_1 (from Chap04) -/
namespace CategoryTheory

/- Domain-style sampling for Definition 4.6.1:
- primary domain: pullback squares and fibre-product universal properties in `CategoryTheory`;
- inspected canonical declarations: `IsPullback`, `IsPullback.exists_lift`, `IsPullback.hom_ext`,
  and `IsPullback.of_isLimit`;
- best owner abstraction: `IsPullback`;
- primitive-vs-derived split:
  primitive data: the four edges of the square together with the commutativity and limiting
    pullback witness already bundled by `IsPullback`;
  derived API: the existence clause `IsPullback.exists_lift`, the uniqueness clause
    `IsPullback.hom_ext`, and the converse constructor `IsPullback.of_isLimit`. -/

/- Source/core/bridge triage for Definition 4.6.1:
- source-facing: the Stacks condition that `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as the fibre
  product of `f : X ⟶ S` and `g : Y ⟶ S`;
- core/canonical: `IsPullback`;
- bridge/view: the universal-property projections `IsPullback.exists_lift` and
  `IsPullback.hom_ext`, and the limiting-cone constructor `IsPullback.of_isLimit`. -/

/- Definition 4.6.1: saying that morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as the fibre
product of `f : X ⟶ S` and `g : Y ⟶ S` is exactly the canonical pullback-square predicate
`IsPullback p q f g`. -/
#check IsPullback

/- Companion recall: the existence clause in the textbook universal property is the canonical
theorem `IsPullback.exists_lift`. -/
#check IsPullback.exists_lift

/- Companion recall: the uniqueness clause in the textbook universal property is the canonical
theorem `IsPullback.hom_ext`. -/
#check IsPullback.hom_ext

/- Companion recall: the converse direction from a limiting pullback cone is the canonical
constructor `IsPullback.of_isLimit`. -/
#check IsPullback.of_isLimit

end CategoryTheory

/-! ### Definition_4_6_2 (from Chap04) -/
namespace CategoryTheory

/- Domain-style sampling for Definition 4.6.2:
- primary domain: pullback squares in `CategoryTheory`.
- inspected declarations: `CommSq`, `IsPullback`, `Square.IsPullback`, and `IsPullback.toCommSq`.
- best owner abstraction: `IsPullback`.
- primitive-vs-derived split:
  primitive data: the four edges of the square together with commutativity and the limiting
    pullback-cone witness packaged by `IsPullback`;
  derived API: the projection `IsPullback.toCommSq` and the bundled-square view
    `Square.IsPullback`. -/

/- Source/core/bridge triage for Definition 4.6.2:
- source-facing: the textbook adjective that a commutative square is cartesian.
- core/canonical: `IsPullback`.
- bridge/view: `IsPullback.toCommSq` and `Square.IsPullback`. -/

/-
Definition 4.6.2: a commutative square
`w ⟶ z`
`↓   ↓`
`x ⟶ y`
in a category is cartesian if `w` together with the morphisms `w ⟶ x` and `w ⟶ z` forms a fibre
product of `x ⟶ y` and `z ⟶ y`. This is the canonical mathlib notion `IsPullback`; the bundled
square view `Square.IsPullback` is only a later bridge/view on top of it. -/
#check IsPullback

/- The canonical cartesian-square notion already packages the underlying commutative square via
`IsPullback.toCommSq`. -/
#check IsPullback.toCommSq

end CategoryTheory

/-! ### Definition_4_6_3 (from Chap04) -/
universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 4.6.3:
- primary domain: categorical pullbacks and existence-of-limits-of-cospans.
- inspected canonical declarations: `HasPullbacks`, `HasPullback`, `HasPullbacksAlong`,
  `pullback.fst`.
- core/canonical owner: `CategoryTheory.Limits.HasPullbacks`.
- primitive data: none beyond the owner predicate itself; this is already the canonical global
  existence predicate.
- derived API: the pointwise specializations `HasPullback f g`, the chosen object `pullback f g`,
  and its universal-property API such as `pullback.fst`, `pullback.snd`, and `pullback.lift`.

Source/core/bridge triage:
- `source-facing`: the Stacks notion that a category has fibre products.
- `core/canonical`: `CategoryTheory.Limits.HasPullbacks`.
- `bridge/view`: the per-morphism existence predicate `HasPullback`, and later chapter uses such as
  `HasPullbacksAlong`, which specialize the global owner to a fixed morphism. -/

/- Definition 4.6.3: a category has fibre products exactly when it has the canonical mathlib
typeclass `HasPullbacks`, meaning that for every pair of morphisms `f : x ⟶ y` and
`g : z ⟶ y` a pullback of `f` and `g` exists. -/
recall HasPullbacks

end CategoryTheory.Limits

/-! ### Definition_4_6_4 (from Chap04) -/
universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.6.4:
- primary domain: morphism properties and pullbacks in `CategoryTheory`.
- inspected owner declarations:
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isPullback`,
  `(𝟭 C).relativelyRepresentable`,
  `Limits.HasPullbacksAlong`.
- best owner abstraction: the identity-functor specialization `(𝟭 C).relativelyRepresentable`.
- primitive-vs-derived split:
  primitive data: only the morphism `f`.
  derived API: the pullback-existence package `HasPullbacksAlong f`, and the chosen pullback
    square extracted from relative representability via `hf.isPullback g`. -/

/- Source/core/bridge triage for Definition 4.6.4:
- source-facing: the Stacks-project equivalence between representable morphisms and existence of
  pullbacks along the morphism.
- core/canonical: `(𝟭 C).relativelyRepresentable`.
- bridge/view: `HasPullbacksAlong`.

This item keeps the canonical owner specialization as the main entry and the textbook pullback
formulation only as a companion bridge theorem. -/

/- Definition 4.6.4: a morphism `f : x ⟶ y` is representable precisely when it belongs to the
canonical morphism property `(𝟭 C).relativelyRepresentable`. -/
#check (𝟭 C).relativelyRepresentable

/- Companion owner: pullbacks existing along a fixed morphism are recorded by
`Limits.HasPullbacksAlong`. -/
recall Limits.HasPullbacksAlong

/-- Bridge/view companion to Definition 4.6.4: a morphism is representable in the canonical
identity-functor sense exactly when pullbacks along it exist. -/
-- Proof sketch: specialize `Functor.relativelyRepresentable` to the identity functor `𝟭 C`. For
-- a morphism `g : z ⟶ y`, the representing square is precisely a pullback square for `g` along `f`.
theorem relativelyRepresentable_iff_hasPullbacksAlong {x y : C} (f : x ⟶ y) :
    (𝟭 C).relativelyRepresentable f ↔ HasPullbacksAlong f := by
  constructor
  · intro hf z g
    -- The representing square for `g` already gives the required pullback of `g` along `f`.
    simpa using (hf.isPullback g).flip.hasPullback
  · intro hg z g
    -- Repackage the canonical pullback of `g` and `f` as the identity-functor witness.
    letI : HasPullback g f := hg g
    refine ⟨pullback g f, pullback.fst g f, pullback.snd g f, ?_⟩
    simpa using (IsPullback.of_hasPullback g f).flip

end CategoryTheory

/-! ### Lemma_4_6_5 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.6.5:
- primary domain: morphism properties in `CategoryTheory`, specialized to representable morphisms.
- inspected owner declarations:
  `MorphismProperty.comp_mem`,
  `MorphismProperty.IsStableUnderComposition`,
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isMultiplicative`.
- best owner abstraction: the morphism property `(𝟭 C).relativelyRepresentable`, whose
  composition stability is inherited from the generic owner theorem `MorphismProperty.comp_mem`.
- primitive-vs-derived split:
  primitive data: only the morphisms `f`, `g` and their representability hypotheses.
  derived API: closure under composition, supplied canonically by the `IsMultiplicative` instance
    on `Functor.relativelyRepresentable`. -/

/- Source/core/bridge triage for Lemma 4.6.5:
- `source-facing`: the composite of two representable morphisms is representable.
- `core/canonical`: `MorphismProperty.comp_mem` for the morphism property
  `(𝟭 C).relativelyRepresentable`.
- `bridge/view`: the specialization from relative representability with respect to a general
  functor to the identity functor on `C`.
-/

/- Core owner recall: the multiplicative structure on relatively representable morphisms is the
upstream instance `Functor.relativelyRepresentable.isMultiplicative`. -/
recall Functor.relativelyRepresentable.isMultiplicative

/- Lemma 4.6.5: the composite of representable morphisms in a category is exactly the canonical
composition theorem for the morphism property `(𝟭 C).relativelyRepresentable`, derived from that
owner instance through `MorphismProperty.comp_mem`. -/
#check ((𝟭 C).relativelyRepresentable).comp_mem

end CategoryTheory

/-! ### Lemma_4_6_6 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Source/core/bridge triage for Lemma 4.6.6:
- `source-facing`: representable morphisms are stable under arbitrary base change squares.
- `core/canonical`: the direct base-change theorem
  `((𝟭 C).relativelyRepresentable).of_isPullback`.
- `bridge/view`: the generic owner instance
  `Functor.relativelyRepresentable.isStableUnderBaseChange`, specialized to the identity functor.
- inspected domain declarations:
  `(𝟭 C).relativelyRepresentable`,
  `((𝟭 C).relativelyRepresentable).of_isPullback`,
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isStableUnderBaseChange`,
  `Limits.IsPullback`.
- primitive data: a cartesian square and a representability witness on one side of it.
- derived API: representability of the base-changed morphism, supplied directly by the owner
  theorem `((𝟭 C).relativelyRepresentable).of_isPullback`.
-/

/- Lemma 4.6.6: stability under base change for ordinary representable morphisms in `C` is already
the direct theorem on the canonical owner `(𝟭 C).relativelyRepresentable`. -/
#check ((𝟭 C).relativelyRepresentable).of_isPullback

end CategoryTheory
