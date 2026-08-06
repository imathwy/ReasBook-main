import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic

open CategoryTheory
open AlgebraicTopology

noncomputable section

-- Semantic recall via `lean_leansearch`:
-- `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq` and
-- `AlgebraicTopology.AlternatingFaceMapComplex.d_squared` are the canonical owners for the
-- alternating-sum boundary and the identity `d ≫ d = 0`, while
-- `AlgebraicTopology.SSet.singularChainComplexFunctor` and
-- `AlgebraicTopology.singularChainComplexFunctor` package the resulting simplicial and
-- topological singular chain complexes.

/- Integral simplicial singular chains on a simplicial set. -/
abbrev integralSimplicialSingularChains : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (SSet.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/- Integral singular chains on a topological space. -/
abbrev integralTopologicalSingularChains : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The integral simplicial singular chain complex `C_*(X)` of a simplicial set `X`. -/
abbrev simplicialSingularChains (X : SSet) : ChainComplex (ModuleCat ℤ) ℕ :=
  integralSimplicialSingularChains.obj X

/-- The integral singular chain complex `C_*(X)` of a topological space `X`. -/
abbrev topologicalSingularChains (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  integralTopologicalSingularChains.obj X

/- Lean notation for the textbook singular chain complex `C_*(X)` of a topological space. -/
scoped[SingularChains] notation "C_*(" X ")" => topologicalSingularChains X

open scoped SingularChains

/-- `simplicialSingularChains X` is definitionally `integralSimplicialSingularChains.obj X`. -/
@[simp] theorem simplicialSingularChains_def (X : SSet) :
    simplicialSingularChains X = integralSimplicialSingularChains.obj X :=
  rfl

/-- `topologicalSingularChains X` is definitionally `integralTopologicalSingularChains.obj X`. -/
@[simp] theorem topologicalSingularChains_def (X : TopCat) :
    topologicalSingularChains X = integralTopologicalSingularChains.obj X :=
  rfl

/- Construction 16.1.6. The singular differential is canonically formalized by the alternating
face-map differential: `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq` identifies the
boundary as `∑ i, (-1) ^ i • d_i`, and `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`
is the theorem that the simplicial identities imply `d ≫ d = 0`. Specializing this
alternating-face-map construction to the singular simplicial set yields the simplicial singular
chain complex. In this file, the corresponding integral simplicial and topological singular chain
functors are named `integralSimplicialSingularChains` and
`integralTopologicalSingularChains`, while their objectwise chain complexes are
`simplicialSingularChains X`, `topologicalSingularChains X`, and, for topological spaces in the
`SingularChains` scope, `C_*(X)`. -/
#check AlternatingFaceMapComplex.obj_d_eq
#check AlternatingFaceMapComplex.d_squared
#check integralSimplicialSingularChains
#check integralTopologicalSingularChains

section

variable (K : SSet) (X : TopCat)

#check simplicialSingularChains K
#check topologicalSingularChains X
#check C_*(X)

end
