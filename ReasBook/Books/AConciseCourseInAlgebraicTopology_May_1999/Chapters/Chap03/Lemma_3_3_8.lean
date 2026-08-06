import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/- Lemma 3.3.8: the fiber translation assignment `T(p)` of Definition 3.3.7 is the canonical
functor sending each object of the base groupoid to its fiber and each morphism to the induced
translation map between fibers. -/
recall fiberTranslationFunctor (hp : Functor.IsCovering p) : B ⥤ Type u₁

/- On objects, `fiberTranslationFunctor hp` is the fiber of `p` over the chosen base object. -/
recall fiberTranslationFunctor_obj (hp : Functor.IsCovering p) (b : B) :
    (fiberTranslationFunctor hp).obj b = p.Fiber b

/- On morphisms, `fiberTranslationFunctor hp` acts by the induced translation map on fibers. -/
recall fiberTranslationFunctor_map (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    (fiberTranslationFunctor hp).map f = fiberTranslationMap hp f

/- Evaluating the transported morphism at a point of the source fiber is the fiber translation
itself. -/
recall fiberTranslationFunctor_map_apply (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) :
    (fiberTranslationFunctor hp).map f x = fiberTranslationMap hp f x

end CategoryTheory.Functor.IsCovering
