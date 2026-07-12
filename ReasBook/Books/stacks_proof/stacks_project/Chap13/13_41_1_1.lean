import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows

universe v u

variable {C : Type u} [Category.{v} C] {n : ℕ}
variable (X X' : ComposableArrows C n)

/-
Domain-style sampling:
- primary domain: finite rows of composable arrows, organized canonically by mathlib as the
  functor category `ComposableArrows C n = Fin (n + 1) ⥤ C`;
- inspected owner declarations:
  `ComposableArrows`,
  `ComposableArrows.homMk`,
  `ComposableArrows.app'`,
  `ComposableArrows.naturality'`;
- best owner abstraction: the functor-category morphism type `X ⟶ X'`;
- primitive data: only the two finite rows `X` and `X'`;
- derived API: component maps `φ.app i` / `ComposableArrows.app' φ i`, square commutativity via
  `ComposableArrows.naturality'`, and ladder construction from components via
  `ComposableArrows.homMk`.

This item is recall-only, so the refined file should stay a direct canonical check rather than
introducing any parallel ladder structure or restatement wrapper.

Source/core/bridge triage:
- source-facing: the textbook commutative ladder between two finite rows of composable arrows;
- core/canonical: the morphism type `X ⟶ X'` in `ComposableArrows C n`;
- bridge/view: the component maps `app'` and the square commutativity lemma `naturality'`,
  assembled from components by `homMk`.
-/

/- 13.41.1.1: the displayed commutative ladder between two length-`n` rows of composable arrows
is formalized by a morphism `X ⟶ X'` in `ComposableArrows C n`; its components are the vertical
maps, and naturality expresses commutativity of each square. -/
#check (X ⟶ X')

/- Companion recall: the canonical constructor and naturality API recover the vertical maps and
commutative squares of such a ladder directly, without any local wrapper definition. -/
recall homMk
recall app'
recall naturality'
