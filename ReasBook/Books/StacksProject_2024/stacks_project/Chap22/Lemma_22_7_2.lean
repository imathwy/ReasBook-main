import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_14_11
import StacksProject_2024.stacks_project.Chap22.AdmissibleShortExact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.CochainComplex

universe u

namespace CochainComplex

/- Source/core/bridge triage for Lemma 22.7.2:
- `source-facing`: a chosen degreewise splitting of the underlying short complex of a short exact
  sequence of differential graded `A`-modules.
- `core/canonical`: the Chapter 12 bridge theorem
  `ShortComplex.homologyMap_homOfDegreewiseSplit_eq_δ`.
- `bridge/view`: the Chapter 22 admissibility owner
  `IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem`, whose equivalence with chosen
  degreewise splittings is publicized by
  `isAdmissibleShortExact_iff_nonempty_degreewiseSplitting`. -/

/-
Lemma 22.7.2: for a degreewise splitting `σ` of a short exact sequence
`0 ⟶ K ⟶ L ⟶ M ⟶ 0` of differential graded `A`-modules, the cohomology boundary map induced by
the canonical connecting morphism `homOfDegreewiseSplit S σ : M ⟶ K[1]` is the connecting
morphism in the associated long exact cohomology sequence. This is a pure canonical recall item:
the split-data statement is already owned by
`CategoryTheory.ShortComplex.homologyMap_homOfDegreewiseSplit_eq_δ`. For admissible short exact
sequences, the companion recall below converts admissibility into such a choice of `σ`.
-/
#check CategoryTheory.ShortComplex.homologyMap_homOfDegreewiseSplit_eq_δ

/- Companion recall: in the DG-module model, admissibility is exactly the existence of degreewise
splittings of the underlying short complex. -/
recall isAdmissibleShortExact_iff_nonempty_degreewiseSplitting

/- Companion recall: the degree-`n` component of `homOfDegreewiseSplit S σ` is the textbook
formula `sⁿ ≫ d_Lⁿ ≫ πⁿ⁺¹`. -/
recall homOfDegreewiseSplit_f

end CochainComplex
