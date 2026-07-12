import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Semantic search note: the dedicated `lean_leansearch` MCP tool was unavailable in this
session. Local Chapter 29 precedent uses `Scheme.functionField`, `FiniteDimensional`, and
`Module.finrank` for the induced extension of function fields. The source tag evidence agrees on
`02NY`. -/

/-- Definition 29.51.8: for a dominant locally finite type morphism `f : X ⟶ Y` of integral
schemes, once `R(Y) ⊆ R(X)` is finite, or any equivalent condition of Lemma 29.51.7 holds, the
degree `deg(X/Y)` is `[R(X) : R(Y)]`. -/
@[stacks 02NY]
noncomputable abbrev functionFieldDegree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] : ℕ :=
  Module.finrank Y.functionField X.functionField

/-- The function-field degree of a dominant locally finite type morphism is the finrank of
`R(Y) ⊆ R(X)`. -/
@[stacks 02NY]
theorem functionFieldDegree_eq_finrank {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] :
    f.functionFieldDegree = Module.finrank Y.functionField X.functionField := sorry

/-- Under the finite-extension hypothesis, the function-field degree is positive. -/
@[stacks 02NY]
theorem functionFieldDegree_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] :
    0 < f.functionFieldDegree := sorry

end AlgebraicGeometry.Scheme.Hom
