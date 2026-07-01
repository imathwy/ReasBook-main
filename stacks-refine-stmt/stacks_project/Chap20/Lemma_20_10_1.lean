import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_project.Chap20.«20_10_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

variable (U : Opens X.carrier) {ι : Type u}
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

-- Proof sketch: by `20.10.0.1`, the functor is the composite of the restricted-sections functor
-- `moduleSectionsOnOverPresheaf U` with the Čech complex functor on `(Over U)ᵒᵖ`. For each
-- `V : Over U`, evaluation at `V` is exact on presheaves of modules, and restriction of scalars is
-- exact on module categories. Hence `moduleSectionsOnOverPresheaf U` is exact. The functor
-- `CategoryTheory.cechComplexFunctor 𝒰` is exact because each degree is a product of exact
-- evaluation functors, and finite limits and colimits in cochain complexes are computed
-- degreewise. Therefore the composite is exact.
/-- Lemma 20.10.1: for an indexed family `𝒰` of objects of `Over U`, the Čech complex functor of
Equation `20.10.0.1`
`ringedSpaceModuleCechComplexFunctor U 𝒰 :
  PMod(\mathcal O_X) ⥤ \operatorname{CochainComplex}(\operatorname{Mod}(\mathcal O_X(U)), \mathbf N)`
is an exact functor. -/
theorem ringedSpaceModuleCechComplexFunctor_exact (𝒰 : ι → Over U) :
    exactFunctor
      (ringedSpacePresheafModules X)
      (CochainComplex (ModuleCat.{u} (X.presheaf.obj (op U))) ℕ)
      (ringedSpaceModuleCechComplexFunctor U 𝒰) := sorry

end AlgebraicGeometry.RingedSpace
