import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/-- Lemma 21.9.1: for a family `U : ι → C`, the functor of (21.9.0.1), namely
`cechComplexFunctor U : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ CochainComplex AddCommGrpCat ℕ`, is an exact
functor. -/
-- Proof sketch: in degree `p`, the Čech complex is a product of evaluation functors
-- `ℱ ↦ ℱ.obj (op W)`, and evaluation is exact on abelian presheaves. Exactness of finite limits
-- and finite colimits in cochain complexes is checked degreewise, so the whole Čech complex
-- functor is exact.
theorem cechComplexFunctor_exact
    {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat) (CochainComplex AddCommGrpCat ℕ) (cechComplexFunctor U) :=
  sorry

end CategoryTheory
