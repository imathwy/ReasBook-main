import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall: `CategoryTheory.Under` and `CategoryTheory.Groupoid.vertexGroup` are the
-- canonical star and vertex-group owners attached to an object of a groupoid.

universe u v

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Groupoid.{v} C]
variable {x : C}

/- Definition 3.3.2 (1): the star `St_C(x)` is the canonical under-category `Under x`, whose
objects are morphisms of `C` with source `x`. -/
#check Under x

/- The star inherits its category structure from the canonical mathlib instance on `Under x`. -/
#check (inferInstance : Category (Under x))

/- Definition 3.3.2 (2): `π(C, x)` is the vertex group at `x`, i.e. the group structure on the
loop type `x ⟶ x` whose multiplication is categorical composition in the groupoid `C`. -/
#check (Groupoid.vertexGroup x : Group (x ⟶ x))

/- The inverse in `π(C, x)` is the categorical inverse of the loop in the groupoid. -/
#check (Groupoid.vertexGroup.inv_eq_inv x : ∀ γ : x ⟶ x, γ⁻¹ = CategoryTheory.inv γ)

end CategoryTheory
