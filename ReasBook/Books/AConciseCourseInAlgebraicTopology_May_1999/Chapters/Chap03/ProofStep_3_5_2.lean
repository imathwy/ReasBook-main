import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped Pointwise

namespace CategoryTheory.Functor

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- ProofStep 3.5.2: if `g : X ⥤ E` lifts `f : X ⥤ B` through `p : E ⥤ B` and sends the chosen
base object `x₀` to the chosen point `e₀` of the fiber over `f.obj x₀`, then the image of the
vertex group at `x₀` under `f` is contained in the image of the vertex group at `e₀.1` under
`p`, viewed inside the vertex group at `f.obj x₀`. -/
-- Proof sketch: for any loop `γ : x₀ ⟶ x₀`, the morphism `g.map γ` is a loop at `g.obj x₀`, hence
-- after transporting along `g.obj x₀ = e₀.1` it becomes a loop at `e₀.1` whose image under `p`
-- is exactly `f.map γ` because `g ⋙ p = f`.
theorem mapVertexGroup_range_le_of_lift {p : E ⥤ B} {f : X ⥤ B} {g : X ⥤ E} (x₀ : X)
    (e₀ : p.Fiber (f.obj x₀)) (hg : g ⋙ p = f) (hg₀ : g.obj x₀ = e₀.1) :
    (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
  have he₀ : e₀ = ⟨g.obj x₀, congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg⟩ := by
    apply Subtype.ext
    exact hg₀.symm
  cases he₀
  cases hg
  intro γ hγ
  rcases hγ with ⟨δ, rfl⟩
  exact ⟨g.map δ, rfl⟩

/-- Companion to ProofStep 3.5.2: when the chosen fiber point is the image of `x₀` under the
lift `g`, the subgroup inclusion is expressed using the fiber witness induced directly by
`hg : g ⋙ p = f`. -/
  theorem mapVertexGroup_range_le_of_lift_imagePoint {p : E ⥤ B} {f : X ⥤ B} {g : X ⥤ E}
      (x₀ : X) (hg : g ⋙ p = f) :
      (Functor.mapVertexGroup f x₀).range ≤
        (congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg) ▸
          (Functor.mapVertexGroup p (g.obj x₀)).range := by
    simpa using
    (mapVertexGroup_range_le_of_lift x₀
      ⟨g.obj x₀, congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg⟩ hg rfl)

end CategoryTheory.Functor
