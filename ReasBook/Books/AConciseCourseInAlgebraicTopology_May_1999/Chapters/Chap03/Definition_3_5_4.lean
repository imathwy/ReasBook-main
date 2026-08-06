import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `CategoryTheory.Over`, `Over.mk`, `Over.homMk`, and `Over.w` in
-- `Mathlib.CategoryTheory.Comma.Over.Basic` give the canonical API for coverings over a fixed
-- base groupoid.

open CategoryTheory

universe u v

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
  (p : E ⥤ B) (p' : E' ⥤ B)

/- Definition 3.5.4: a map of coverings of `B`, from `p : E ⥤ B` to `p' : E' ⥤ B`, is a
morphism in the over-category `Over (Cat.of B)`. Equivalently, it is a functor `g : E ⥤ E'`
such that `g ⋙ p' = p`. -/
#check (Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)

section OverApi

variable {T : Type u} [Category.{v} T]
variable {X Y : T}

/- An object of an over-category is given by a morphism with codomain `X`. -/
recall Over.mk (f : Y ⟶ X) : Over X

/- Equivalently, a morphism in an over-category is built from a commutative triangle. -/
recall Over.homMk {U V : Over X} (g : U.left ⟶ V.left)
    (hg : g ≫ V.hom = U.hom) : U ⟶ V

/- Every morphism in an over-category satisfies the defining commutative-triangle relation. -/
recall Over.w {U V : Over X} (g : U ⟶ V) : g.left ≫ V.hom = U.hom

end OverApi
