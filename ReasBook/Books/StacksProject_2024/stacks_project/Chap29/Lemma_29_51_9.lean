import StacksProject_2024.Chap29.Definition_29_51_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 29.51.9: for integral schemes, once the induced tower of finite function-field
extensions `R(Z) → R(Y) → R(X)` is in scope, the relative degrees satisfy
`deg(X/Z) = deg(X/Y) deg(Y/Z)`. -/
@[stacks 02NZ]
theorem functionFieldDegree_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [Algebra Y.functionField X.functionField]
    [Algebra Z.functionField Y.functionField]
    [Algebra Z.functionField X.functionField]
    [IsScalarTower Z.functionField Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [FiniteDimensional Z.functionField Y.functionField] :
    letI : FiniteDimensional Z.functionField X.functionField :=
      FiniteDimensional.trans Z.functionField Y.functionField X.functionField
    (f ≫ g).functionFieldDegree = f.functionFieldDegree * g.functionFieldDegree := by
  letI : FiniteDimensional Z.functionField X.functionField :=
    FiniteDimensional.trans Z.functionField Y.functionField X.functionField
  simpa [functionFieldDegree, Nat.mul_comm] using
    (Module.finrank_mul_finrank Z.functionField Y.functionField X.functionField).symm

end AlgebraicGeometry.Scheme.Hom
