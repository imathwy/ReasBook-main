import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory TopologicalSpace

noncomputable section

universe u uι

namespace TopCat.Presheaf

section

variable {X : TopCat.{u}} {ι : Type uι}

/- Domain-style sampling for Definition 20.9.1:
- primary domain: the Čech complex and Čech cohomology of an additive presheaf on a topological
  space with respect to an indexed family of opens;
- sampled owner API:
  `cechComplexFunctor`,
  `HomologicalComplex.homology`,
  `(inferInstance : HasFiniteProducts (Opens X))`;
- `source-facing`: `TopCat.Presheaf.cechComplex` and `TopCat.Presheaf.cechCohomology`;
- `core/canonical`: `cechComplexFunctor U` and `((cechComplexFunctor U).obj F).homology i`;
- `bridge/view`: the canonical finite-product structure on `Opens X`, supplied upstream by
  typeclass inference.

Primitive data are only the indexed family `U : ι → Opens X` and the additive presheaf `F`.
Finite intersections, Čech differentials, and homology are all derived from the canonical owner
`cechComplexFunctor U`. This file therefore keeps the source-facing topological-space names as thin
abbreviations over that owner rather than reintroducing a parallel tuplewise implementation.
-/

/-- Definition 20.9.1: for an abelian presheaf `F` on a topological space `X` and an indexed
family of opens `U`, the associated Čech complex is the specialization of the canonical owner
`cechComplexFunctor U` to `F`. -/
@[stacks 01EF]
abbrev cechComplex (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) :
    CochainComplex AddCommGrpCat.{max u uι} ℕ :=
  (cechComplexFunctor U).obj F

/-- The degree-`i` Čech cohomology group of the presheaf `F` with respect to the family `U`. -/
abbrev cechCohomology (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ) :
    AddCommGrpCat.{max u uι} :=
  (cechComplex U F).homology i

/-- The source-facing Čech cohomology owner is the degree-`i` homology object of the associated
Čech complex. -/
@[simp] theorem cechComplex_homology
    (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ) :
    (cechComplex U F).homology i = cechCohomology U F i :=
  rfl

end

end TopCat.Presheaf
