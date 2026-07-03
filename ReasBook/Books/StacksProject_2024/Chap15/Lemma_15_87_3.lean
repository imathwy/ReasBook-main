import Mathlib
import stacks_project.Chap15.Lemma_15_87_14_Emmanouil

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbCpxSeq" => SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local notation "H" => HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)
local notation "ev" => HomologicalComplex.eval AddCommGrpCat (up ℤ)

/- Domain-style sampling for Lemma 15.87.3:
- primary domain: derived inverse limits of sequential inverse systems of abelian groups and the
  comparison map from cohomology of a termwise inverse limit to the inverse limit of cohomology;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `HomologicalComplex.eval`,
  `HomologicalComplex.homologyFunctor`,
  `ShortComplex.ShortExact.isIso_g_iff`;
- best owner abstraction: the vanishing hypotheses are canonically owned by
  `SequentialInverseSystem.firstDerivedLimit`, while the degree and cohomology towers are
  derived from the input tower of cochain complexes by postcomposing with
  `HomologicalComplex.eval` and `HomologicalComplex.homologyFunctor`; the source-facing
  comparison morphism itself is the canonical `limit.post A (H 0)`, and the `IsIso` conclusion is
  derived API from the more primitive short exact sequence via
  `ShortComplex.ShortExact.isIso_g_iff`;
- primitive data: the tower `A : AbCpxSeq`;
- derived API: the three `R^1 lim` objects, the canonical comparison morphism
  `limit.post A (H 0)`, the short exact sequence it fits into, and the resulting `IsIso`
  criterion.

Source/core/bridge triage:
- `source-facing`: the short exact sequence and its `IsIso` corollary with explicit vanishing
  hypotheses;
- `core/canonical`: `SequentialInverseSystem.firstDerivedLimit`, `limit.post`, and
  `ShortComplex.ShortExact.isIso_g_iff`;
- `bridge/view`: the Mittag-Leffler sufficient criterion below. -/

/-- Under the vanishing of `R^1 \!\varprojlim` for the degree `-2` and `-1` towers, the canonical
comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` sits in the expected Milnor
short exact sequence with left term `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`. -/
theorem inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1))) :
    ∃ (ι :
        firstDerivedLimit (A ⋙ H (-1)) ⟶
          (H 0).obj (limit A))
      (hι :
        ι ≫ limit.post A (H 0) = 0),
      (ShortComplex.mk ι (limit.post A (H 0)) hι).ShortExact := sorry

-- Proof sketch: first produce the canonical short exact sequence above from the vanishing of the
-- degree `-2` and `-1` obstruction towers. Then apply the owner criterion
-- `ShortComplex.ShortExact.isIso_g_iff`: vanishing of `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`
-- identifies the left term with zero, so the right map is an isomorphism.
/-- Lemma 15.87.3: for a sequential inverse system of cochain complexes of abelian groups, if the
`R^1 \!\varprojlim` terms of the degree `-2`, degree `-1`, and `H^{-1}` towers vanish, then the
canonical comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` is an isomorphism.
-/
theorem inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1)))
    (hHnegOne : IsZero <| firstDerivedLimit (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  rcases inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
      A hAnegTwo hAnegOne with
    ⟨ι, hι, hshort⟩
  exact (ShortComplex.ShortExact.isIso_g_iff hshort).2 hHnegOne

-- Proof sketch: the Mittag-Leffler criterion from the preceding Chapter 15 development implies
-- the vanishing of `R^1 \!\varprojlim` for each of the three towers, so the main theorem above
-- applies directly.
/-- A sufficient criterion for Lemma 15.87.3: it is enough that the degree `-2`, degree `-1`,
and `H^{-1}` towers are Mittag-Leffler. -/
theorem inverse_limit_zero_cohomology_comparison_isIso_of_isMittagLeffler
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsMittagLeffler (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  have hAnegTwo' : IsZero <| firstDerivedLimit (A ⋙ ev (-2)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ ev (-2))).1 hAnegTwo).1
  have hAnegOne' : IsZero <| firstDerivedLimit (A ⋙ ev (-1)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ ev (-1))).1 hAnegOne).1
  have hHnegOne' : IsZero <| firstDerivedLimit (A ⋙ H (-1)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ H (-1))).1 hHnegOne).1
  exact inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    A hAnegTwo' hAnegOne' hHnegOne'

end SequentialInverseSystem

end CategoryTheory
