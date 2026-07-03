import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_13_1 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {f : X ⟶ Y} {g h : Z ⟶ X} {g' h' : Y ⟶ Z}

/- Domain-style sampling for Definition 4.13.1:
- primary domain: categorical monomorphisms and epimorphisms of a morphism.
- inspected owner declarations:
  `Mono`,
  `Epi`,
  `cancel_mono`,
  `cancel_epi`.
- sampled project owner reuse: `StacksProject_2024/Items/Chap12/Definition_12_5_3.lean`
  recalls `Mono` and `Epi` directly.
- owner abstraction: the mathlib classes `Mono f` and `Epi f`.
- primitive data: the owner-class fields `Mono.right_cancellation` and `Epi.left_cancellation`.
- derived API: the textbook cancellation clauses `cancel_mono f` and `cancel_epi f`.

Source/core/bridge triage:
- `source-facing`: the textbook notions of monomorphism and epimorphism together with their
  cancellation properties;
- `core/canonical`: the mathlib owner classes `Mono` and `Epi`;
- `bridge/view`: the cancellation theorems `cancel_mono` and `cancel_epi`.

This numbered item is recall-only at the `core/canonical` layer, so no local wrapper definition
or characterization theorem should be introduced here. -/

/- Definition 4.13.1 (1), owner recall: for a morphism `f : X ⟶ Y`, the textbook notion that `f`
is a monomorphism is exactly the canonical mathlib owner predicate `Mono f`. -/
recall Mono

/- Companion recall: the textbook right-cancellation clause for a monomorphism is the canonical
theorem `cancel_mono`. -/
section

variable [Mono f]

#check (cancel_mono f : g ≫ f = h ≫ f ↔ g = h)

end

/- Definition 4.13.1 (2), owner recall: for a morphism `f : X ⟶ Y`, the textbook notion that `f`
is an epimorphism is exactly the canonical mathlib owner predicate `Epi f`. -/
recall Epi

/- Companion recall: the textbook left-cancellation clause for an epimorphism is the canonical
theorem `cancel_epi`. -/
section

variable [Epi f]

#check (cancel_epi f : f ≫ g' = f ≫ h' ↔ g' = h')

end

end CategoryTheory

/-! ### Example_4_13_2 (from Chap04) -/
namespace CategoryTheory

/- Domain-style sampling for Example 4.13.2:
- primary domain: monomorphisms and epimorphisms in the category of sets.
- inspected owner declarations:
  `CategoryTheory.Mono`,
  `CategoryTheory.Epi`,
  `CategoryTheory.mono_iff_injective`,
  `CategoryTheory.epi_iff_surjective`.
- owner abstraction: the categorical classes `Mono` and `Epi`, with the canonical `Type`
  characterizations supplied by `mono_iff_injective` and `epi_iff_surjective`.
- primitive data: the monomorphism/epimorphism structures themselves.
- derived API: the injectivity/surjectivity reformulations specific to `Type`.
- triage: this example is a `bridge/view` recall of the canonical `Type`-level characterizations,
  so the right public surface is direct recall of the upstream theorems rather than any local
  restatement or wrapper. -/

/- Example 4.13.2 (monomorphism clause): in the category of sets, a morphism is a monomorphism
exactly when its underlying function is injective. This is the canonical theorem
`CategoryTheory.mono_iff_injective`. -/
recall mono_iff_injective

/- Example 4.13.2 (epimorphism clause): in the category of sets, a morphism is an epimorphism
exactly when its underlying function is surjective. This is the canonical theorem
`CategoryTheory.epi_iff_surjective`. -/
recall epi_iff_surjective

end CategoryTheory

/-! ### Lemma_4_13_3 (from Chap04) -/
universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/-
Domain-style sampling for Lemma 4.13.3:
- primary domain: characterizations of monomorphisms and epimorphisms by canonical pullback and
  pushout squares in `CategoryTheory`;
- inspected owner declarations:
  `Mono`,
  `Epi`,
  `mono_iff_isPullback`,
  `epi_iff_isPushout`;
- best owner abstraction: the canonical owner theorems `mono_iff_isPullback` and
  `epi_iff_isPushout`;
- primitive-vs-derived split:
  primitive data: only the morphism `f : X ⟶ Y` together with the standard owner predicates
    `Mono f` and `Epi f`;
  derived API: the corresponding cartesian and cocartesian square formulations
    `IsPullback (𝟙 X) (𝟙 X) f f` and `IsPushout f f (𝟙 Y) (𝟙 Y)`. -/

/- Source/core/bridge triage for Lemma 4.13.3:
- source-facing: the textbook equivalences expressing mono and epi morphisms through the obvious
  pullback and pushout squares;
- core/canonical: the mathlib owner theorems `mono_iff_isPullback` and `epi_iff_isPushout`;
- bridge/view: the earlier source-facing square notions `IsPullback` and `IsPushout` recalled in
  Definitions 4.6.2 and 4.9.2. -/

/- Lemma 4.13.3 (1): a morphism `f : X ⟶ Y` is a monomorphism if and only if the canonical square
with both horizontal arrows `𝟙 X` and both vertical arrows `f` is a pullback. This is exactly the
canonical mathlib theorem `CategoryTheory.mono_iff_isPullback`. -/
recall mono_iff_isPullback (f : X ⟶ Y) :
  Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f

/- Lemma 4.13.3 (2): a morphism `f : X ⟶ Y` is an epimorphism if and only if the canonical square
with both horizontal arrows `f` and both vertical arrows `𝟙 Y` is a pushout. This is exactly the
canonical mathlib theorem `CategoryTheory.epi_iff_isPushout`. -/
recall epi_iff_isPushout (f : X ⟶ Y) :
  Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y)

end CategoryTheory
