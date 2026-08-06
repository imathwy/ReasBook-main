import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Tactic.Recall

open CategoryTheory
open TopCat
open scoped ContinuousMap

-- Semantic recall: `CategoryTheory.Over`, `Over.mk`, `Over.w`, and `Over.homMk` in
-- `Mathlib.CategoryTheory.Comma.Over.Basic` give the canonical API for spaces over a fixed base.
-- Chapter 7 also works repeatedly with unbundled spaces `B : Type u` and maps `p : C(E, B)`, so
-- this file exposes the thin bridge `SpaceOver B := Over (TopCat.of B)`.

universe u v

/-- The category of spaces over a space `B` is `Over B`, whose
objects are maps `E ⟶ B` and whose morphisms are commutative triangles over `B`. -/
abbrev SpacesOver (B : TopCat.{u}) := Over B

/-
Definition 7.5.1. For a space `B : TopCat`, the category of spaces over `B` is `Over B`.
An object of `Over B` is a map `E ⟶ B`, implemented by `Over.mk`. A morphism in `Over B`
is induced from a map of total spaces by `Over.homMk`, and the commuting triangle is recorded by
`Over.w`.
-/
variable (B : TopCat.{u})

#check Over B

section OverApi

variable {T : Type u} [Category.{v} T] {X Y : T}

/- An object of an over-category is given by a morphism with codomain `X`. -/
recall Over.mk (f : Y ⟶ X) : Over X

/- Equivalently, a morphism in an over-category is built from a commutative triangle. -/
recall Over.homMk {U V : Over X} (g : U.left ⟶ V.left)
    (hg : g ≫ V.hom = U.hom) : U ⟶ V

/- Every morphism in the over-category satisfies the defining commutative-triangle relation. -/
recall Over.w {U V : Over X} (g : U ⟶ V) : g.left ≫ V.hom = U.hom

end OverApi

/-- The category of spaces over an unbundled topological space `B`. This is the source-facing
bridge from continuous maps to the canonical owner `Over (TopCat.of B)`. -/
abbrev SpaceOver (B : Type u) [TopologicalSpace B] := Over (TopCat.of B)

namespace SpaceOver

variable {E E' B : Type u}
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]

/-- A space over `B` given by a continuous map `p : C(E, B)`. -/
abbrev mk (p : C(E, B)) : SpaceOver B :=
  Over.mk (TopCat.ofHom p)

/-- A commuting triangle of continuous maps gives the square required by `Over.homMk`. -/
theorem homMkCondition {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) :
    TopCat.ofHom f ≫ (mk q).hom = (mk p).hom := by
  -- Convert the source-facing equality of continuous maps into the categorical square.
  simpa using congrArg TopCat.ofHom hf

/-- Definition 7.5.1: a map over `B` is a commuting triangle of continuous maps, packaged as
the induced morphism in `SpaceOver B`. -/
def homMk {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) :
    mk p ⟶ mk q :=
  -- Package the chosen total-space map using the canonical `Over.homMk` constructor.
  Over.homMk (TopCat.ofHom f) (homMkCondition f hf)

/-- The underlying continuous map of `SpaceOver.homMk f hf` is `f`. -/
@[simp] theorem homMk_left_hom {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) :
    (homMk f hf).left.hom = f :=
  -- The left component of `Over.homMk` is definitionally the map we supplied.
  rfl

/-- Every morphism of spaces over `B` satisfies the defining commutative-triangle relation. -/
theorem w {p : C(E, B)} {q : C(E', B)} (f : mk p ⟶ mk q) : q.comp f.left.hom = p := by
  -- Transport the canonical `Over.w` identity back to continuous maps.
  simpa using congrArg TopCat.Hom.hom (Over.w f)

end SpaceOver
