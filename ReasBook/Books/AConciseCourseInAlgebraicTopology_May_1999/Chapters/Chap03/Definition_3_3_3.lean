import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Groupoid.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]

/-- Definition 3.3.3: a covering functor of groupoids is surjective on objects and induces a
bijection from each star `Under e` to the star `Under (p.obj e)` via the canonical functor
`Under.post p`. -/
class IsCovering (p : E ⥤ B) : Prop where
  /-- A covering functor is surjective on objects. -/
  obj_surjective : Function.Surjective p.obj
  /-- A covering functor is bijective on the canonical star map at every object. -/
  star_bijective (e : E) : Function.Bijective ((Under.post p : Under e ⥤ Under (p.obj e)).obj)

namespace IsCovering

variable {p : E ⥤ B}

/-- In a covering functor, the canonical map on stars at any object is injective. -/
theorem starInjective (hp : IsCovering p) (e : E) :
    Function.Injective ((Under.post p : Under e ⥤ Under (p.obj e)).obj) :=
  (hp.star_bijective e).injective

/-- In a covering functor, the canonical map on stars at any object is surjective. -/
theorem starSurjective (hp : IsCovering p) (e : E) :
    Function.Surjective ((Under.post p : Under e ⥤ Under (p.obj e)).obj) :=
  (hp.star_bijective e).surjective

end IsCovering

/-- The identity functor on a groupoid is a covering functor. -/
instance (C : Type u₁) [Groupoid.{v₁} C] : IsCovering (𝟭 C) where
  obj_surjective c := ⟨c, rfl⟩
  star_bijective e := by
    simpa [Under.post] using (Function.bijective_id : Function.Bijective (id : Under e → Under e))

end Functor

end CategoryTheory
