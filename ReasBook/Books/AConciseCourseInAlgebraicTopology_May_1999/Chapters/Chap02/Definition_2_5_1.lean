import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory FundamentalGroupoid
open scoped FundamentalGroupoid

variable (X : Type u) [TopologicalSpace X]
variable {X} {x y : X}

/- Definition 2.5.1: the fundamental groupoid `Π(X)` is canonically `FundamentalGroupoid X`;
equivalently, as the value of the fundamental-groupoid functor on `TopCat.of X`, it is
`πₓ (TopCat.of X)`. Its objects are the points of `X`, and its morphisms are endpoint-fixed
homotopy classes of paths. -/
#check (FundamentalGroupoid X)

/- The bundled functorial presentation of `Π(X)` is `πₓ (TopCat.of X)`. -/
#check (πₓ (TopCat.of X))

/- The objects of the fundamental groupoid are canonically identified with the points of `X`. -/
recall FundamentalGroupoid.equiv (X : Type u) : FundamentalGroupoid X ≃ X

/- A point of `X` determines the corresponding object of `Π(X)`. -/
recall FundamentalGroupoid.mk (x : X) : FundamentalGroupoid X

/- A homotopy class of paths from `x` to `y` defines a morphism in the fundamental groupoid. -/
recall FundamentalGroupoid.fromPath (p : Path.Homotopic.Quotient x y) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y

/- In the bundled functorial presentation, every morphism in the fundamental groupoid can be
viewed as an endpoint-fixed homotopy class of paths. -/
recall FundamentalGroupoid.toPath {Y : TopCat} {x₀ x₁ : πₓ Y} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient x₀.as x₁.as
