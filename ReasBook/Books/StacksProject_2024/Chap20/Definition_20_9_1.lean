import StacksProject_2024.Chap20.«20_9_0_1»

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u uι

section

variable {X : TopCat.{u}} {ι : Type uι}
variable (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ)

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Definition 20.9.1:
- primary domain: Čech complexes and Čech cohomology of abelian presheaves on indexed families of
  opens of a topological space;
- sampled owner API:
  `FormalCoproduct.cochainComplexFunctor`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `cechComplexFunctor`,
  `HomologicalComplex.homologyFunctor`,
  `indexedOpenCoverCechCohomology`;
- `source-facing`: the Čech complex and its degree-`i` cohomology for a family `U : ι → Opens X`;
- `core/canonical`: `cechComplexFunctor U`;
- `bridge/view`: the opens-specific finite-product witness `opensHasFiniteProducts X`, factored out
  to the local Chapter 20 Čech prelude instead of being redefined here.

Primitive data are only the family `U` and the additive presheaf `F`. The finite intersections,
restriction maps, differential, and resulting cochain complex are derived by the owner
`cechComplexFunctor U`, and degree-`i` Čech cohomology is then derived by
`HomologicalComplex.homologyFunctor`. This file should therefore recall the canonical owner
directly, rather than reintroducing a parallel tuplewise/intersectionwise implementation.
-/

/- Core/canonical owner: the Čech complex attached to a family in a category with finite products
is `cechComplexFunctor`. -/
recall cechComplexFunctor

/- Definition 20.9.1: for an abelian presheaf `F` on a topological space `X` and an indexed
family of opens `U`, the Čech complex is the specialization `((cechComplexFunctor U).obj F :
CochainComplex AddCommGrpCat ℕ)`. -/
#check ((cechComplexFunctor U).obj F : CochainComplex AddCommGrpCat ℕ)

/- Companion check: the degree-`i` Čech cohomology group is the degree-`i` homology object of the
canonical Čech complex above. -/
#check ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
  ((cechComplexFunctor U).obj F) : AddCommGrpCat)

end
