import Mathlib
import stacks_project.Chap04.Definition_4_22_2
import stacks_project.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits ComplexShape

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbCpxSeq" => SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local notation "ev" => HomologicalComplex.eval AddCommGrpCat (up ℤ)
local notation "H" => HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)

/- Domain-style sampling for Lemma 12.31.7 in the inverse-limit/cohomology domain:
- owner abstractions:
  * `SequentialInverseSystem.IsMittagLeffler`
  * `IsEssentiallyConstantCofilteredDiagram`
  * `HomologicalComplex.eval`, `HomologicalComplex.homologyFunctor`, and
    `ShortComplex.ShortExact.homology_exact₂`
- sampled supporting declarations:
  * `SequentialInverseSystem.inverseLimit_shortExact_of_isMittagLeffler_left` in
    `Lemma_12_31_3`
  * `ShortComplex.ShortExact.isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃` in
    `Lemma_12_31_6`
  * `ShortComplex.ShortExact.homology_exact₂` in mathlib's
    `Algebra/Homology/HomologySequence`

This item is `source-facing`: its primitive data are the inverse system `A` together with the
Mittag-Leffler hypotheses on the degree `-2` and `-1` evaluation towers and the essential
constancy hypothesis on the degree `-1` homology tower. The comparison morphism
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is derived from the
owner functor `HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)`, so the public statement
should expose that canonical morphism directly rather than introduce any parallel wrapper API. -/

-- Proof sketch: form the short exact sequences of cocycles, objects, and coboundaries in degrees
-- `-1` and `0`; Lemma `12.31.3` gives exactness after taking inverse limits once the relevant
-- Mittag-Leffler conditions are known, and Lemma `12.31.6` upgrades the essential constancy of
-- `H^{-1}` to the Mittag-Leffler property for the cocycle tower. Chasing the resulting exact
-- sequences shows that the canonical map `H^0(lim A_i) ⟶ lim H^0(A_i)` is an isomorphism.
/-- Lemma 12.31.7: for a sequential inverse system of cochain complexes of abelian groups, if the
systems in degrees `-2` and `-1` are Mittag-Leffler and the degree `-1` cohomology system is
essentially constant, then the canonical comparison morphism
`H^0(\varprojlim A_i) \to \varprojlim H^0(A_i)` given by
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is an isomorphism. -/
theorem cohomologyLimitComparison_zero_isIso_of_isMittagLeffler_negTwo_negOne_and_essentiallyConstant_homology_negOne
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsEssentiallyConstantCofilteredDiagram (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := sorry

end SequentialInverseSystem

end CategoryTheory
