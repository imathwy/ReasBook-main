import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.AdmissibleShortExact
import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_10
import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace CochainComplex

/-
Source/core/bridge triage for 22.8.1.1:
- `source-facing`: the triangle `K ⟶ L ⟶ M ⟶ K[1]` attached to an admissible short exact sequence
  of differential graded modules;
- `core/canonical`: the homotopy-category owner
  `CochainComplex.trianglehOfDegreewiseSplit` attached to a chosen degreewise splitting of the
  underlying short complex;
- `bridge/view`: the independence-of-splitting comparison
  `trianglehOfDegreewiseSplit_iso_of_splittings` and the distinguishedness bridge
  `triangle_mk_mem_distTriang_of_degreewise_split_short_complex`.
-/

/- Source-facing recall: the Chapter 22 owner for an admissible short exact sequence of
differential graded modules is `IsAdmissibleShortExact`, specialized to the graded-forgetful
system `dgModuleUnderlyingGradedHomSystem` in the cochain-complex model. -/
recall IsAdmissibleShortExact

/- Companion bridge for `22.8.1.1`: in the canonical cochain-complex model for differential
graded `A`-modules, the Chapter 22 admissibility predicate is exactly the existence of a
degreewise splitting of the underlying short complex, so an admissible short exact sequence can be
fed directly to `trianglehOfDegreewiseSplit`. -/
recall CochainComplex.isAdmissibleShortExact_iff_nonempty_degreewiseSplitting

/- 22.8.1.1: for an admissible short exact sequence of differential graded modules, the displayed
triangle `K ⟶ L ⟶ M ⟶ K[1]` in the homotopy category is the canonical owner
`trianglehOfDegreewiseSplit` attached to a chosen degreewise splitting of the underlying short
complex. -/
recall trianglehOfDegreewiseSplit

/- Companion recall: changing the degreewise splitting changes the associated triangle only by the
canonical identity-on-terms isomorphism from Lemma 13.9.10. -/
recall trianglehOfDegreewiseSplit_iso_of_splittings

/- Companion recall: once the ambient homotopy category carries its canonical pretriangulated
structure, the associated triangle is distinguished. -/
recall triangle_mk_mem_distTriang_of_degreewise_split_short_complex

end CochainComplex
