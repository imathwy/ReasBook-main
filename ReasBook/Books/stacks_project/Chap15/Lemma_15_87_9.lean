import Mathlib
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap15.«15_87_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "DAbSeq" => DerivedCategory AbSeq

/- Domain-style sampling for Lemma 15.87.9:
- primary domain: derived inverse limits of sequential inverse systems of abelian groups and
  their stagewise realization in `D(\operatorname{Ab})`;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `stagewiseAbelianGroupDerivedTower`,
  `CategoryTheory.additiveFunctorTotalRightDerived`,
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`;
- best owner abstraction: the source-facing statement should stay a specialization asserting that
  the chosen object `R lim(K)` is a derived limit, while the actual owner remains the canonical
  Chapter `13` predicate `IsDerivedLimit` applied to the chapter owner
  `stagewiseAbelianGroupDerivedTower K`;
- primitive data: only the object `K : D(\operatorname{Ab}(\mathbf N))`;
- derived API: the stagewise tower `stagewiseAbelianGroupDerivedTower K` and the chosen derived
  inverse-limit object `R lim(K)`.

Source/core/bridge triage:
- `source-facing`: the specialization of the Stacks Project statement to
  `K ∈ D(\operatorname{Ab}(\mathbf N))`;
- `core/canonical`: `IsDerivedLimit`;
- `bridge/view`: `stagewiseAbelianGroupDerivedTower`. -/

-- Proof sketch: choose a representing inverse system of cochain complexes for `K`, evaluate it
-- stagewise to obtain the tower `(K_n^\bullet)_n` in `D(Ab)`, and apply the Milnor
-- distinguished-triangle formalism of Definition 13.34.1. The chosen right derived inverse-limit
-- functor from Lemma 15.87.1 identifies its value on `K` with the resulting derived limit object.
/-- Lemma 15.87.9: for `K ∈ D(\operatorname{Ab}(\mathbf N))`, the chosen object `R lim(K)` is a
derived limit of the inverse system `(K_n^\bullet)_n` in `D(\operatorname{Ab})` obtained by
evaluating `K` stagewise. Equivalently, `R lim(K)` fits into the canonical Milnor distinguished
triangle `R lim(K) ⟶ \prod_n K_n^\bullet ⟶ \prod_n K_n^\bullet ⟶ R lim(K)[1]`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DAbSeq) :
    IsDerivedLimit (stagewiseAbelianGroupDerivedTower K) (R lim(K)) := sorry
