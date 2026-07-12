import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Linear.Basic

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe w v u

-- `tool_search` did not expose a `lean_leansearch` semantic search tool in this environment, so
-- the owner/API choice here was verified directly against mathlib's `CategoryTheory.Linear` and
-- `DirectSum.Decomposition` interfaces.

/-- Definition 22.25.1: A graded category over `R` is an `R`-linear category in which
every morphism module `X ⟶ Y` is equipped with a direct-sum decomposition into degree pieces
indexed by `ℤ`, identity morphisms are homogeneous of degree `0`, and the composite of
homogeneous morphisms of degrees `i` and `j` has degree `i + j`. -/
@[stacks 09L2]
class GradedCategory (R : outParam (Type w)) [Semiring R] (C : Type u) [Category.{v} C]
    [Preadditive C]
    extends Linear R C where
  /-- The degree-`i` part `Hom^i(X, Y)` of the graded `R`-module `Hom(X, Y)`. -/
  homDegree (X Y : C) (i : ℤ) : Submodule R (X ⟶ Y)
  /-- The direct-sum decomposition `Hom(X, Y) = ⨁ i, Hom^i(X, Y)`. -/
  homDecomposition (X Y : C) : DirectSum.Decomposition (homDegree X Y)
  /-- Identity morphisms are homogeneous of degree `0`. -/
  id_mem_homDegree_zero (X : C) : 𝟙 X ∈ homDegree X X 0
  /-- Composition preserves degrees: the composite of a degree-`i` morphism and a degree-`j`
  morphism has degree `i + j`. -/
  comp_mem {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
      (hf : f ∈ homDegree X Y i) (hg : g ∈ homDegree Y Z j) :
      f ≫ g ∈ homDegree X Z (i + j)

namespace GradedCategory

/- Lean surface notation for the source-facing degree piece `Hom^i(X, Y)`. -/
scoped notation:max "Hom^" i:max "(" X ", " Y ")" => GradedCategory.homDegree X Y i

section

variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]

open scoped GradedCategory

/-- Each graded hom family in a graded category comes with its specified direct-sum
decomposition. -/
instance instHomDecomposition [h : GradedCategory R C] (X Y : C) :
    DirectSum.Decomposition (fun i ↦ (Hom^i(X, Y) : Submodule R (X ⟶ Y))) :=
  h.homDecomposition X Y

end

end GradedCategory

end CategoryTheory
