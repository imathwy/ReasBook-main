import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.«15_87_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "DAbSeq" => DerivedCategory AbSeq

/-- Lemma 15.87.9: for `K ∈ D(\operatorname{Ab}(\mathbf N))`, the chosen object `R lim(K)` is a
derived limit of the inverse system `(K_n^\bullet)_n` in `D(\operatorname{Ab})` obtained by
evaluating `K` stagewise. Equivalently, `R lim(K)` fits into the canonical Milnor distinguished
triangle `R lim(K) ⟶ \prod_n K_n^\bullet ⟶ \prod_n K_n^\bullet ⟶ R lim(K)[1]`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DAbSeq) :
    IsDerivedLimit (stagewiseAbelianGroupDerivedTower K) (R lim(K)) := by
  -- This is the generic stagewise-evaluation Milnor triangle specialized to abelian groups.
  simpa [stagewiseAbelianGroupDerivedTower] using
    (CategoryTheory.derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
      (A := Ab) K)
