import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

variable (D : Type u₁) [Category.{v₁} D]
variable (C : Type u₂) [Category.{v₂} C]
variable (F : D ⥤ C)
variable [HasLimit F]

/- Definition 2.6.4: the limit of a diagram `F` is the canonical object `limit F` of `C`. -/
#check (limit F : C)

/- The limit object carries its canonical cone over `F`. -/
recall limit.cone (F : D ⥤ C) [HasLimit F] : Cone F

/- Equivalently, the limit cone provides a diagram map from the constant diagram on `limit F`
to `F`. -/
#check ((limit.cone F).π : (Functor.const D).obj (limit F) ⟶ F)

/- Its component at an object `j : D` is the canonical projection `limit.π F j`. -/
variable (j : D)

#check (limit.π F j : limit F ⟶ F.obj j)

/- The cone-level map and the componentwise projections agree through the canonical theorem
`limit.cone_π`. -/
recall limit.cone_π {F : D ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π F

/- The canonical cone on `limit F` is terminal among cones over `F`. -/
recall limit.isLimit (F : D ⥤ C) [HasLimit F] : IsLimit (limit.cone F)
