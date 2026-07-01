import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap06.Lemma_6_15_2
import stacks_project.Chap06.Lemma_6_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace

noncomputable section

universe u

private theorem addCommGrpCat_isIso_terminal_from_iff_isZero (A : AddCommGrpCat.{u}) :
    IsIso (terminal.from A) ↔ IsZero A := by
  have h :
      terminal.from A = (0 : A ⟶ ⊤_ AddCommGrpCat.{u}) := by
    simpa using
      (terminalIsTerminal.isZero).eq_of_tgt
        (terminal.from A) (0 : A ⟶ ⊤_ AddCommGrpCat.{u})
  rw [h, isIsoZero_iff_source_target_isZero]
  constructor
  · rintro ⟨hA, _⟩
    exact hA
  · intro hA
    exact ⟨hA, terminalIsTerminal.isZero⟩

section

variable {X : TopCat.{u}} {Z : Set X}

/- Domain-style sampling for Lemma 6.32.3:
- primary domain: sheaf pushforward along the inclusion of a closed subset in `TopCat`;
- sampled owner API:
  `TopCat.subsetInclusion`,
  `subsetSheafPushforward_fullyFaithful`,
  `closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem`,
  `IsTerminal.isZero`,
  `isIsoZero_iff_source_target_isZero`;
- `source-facing`: the abelian-sheaf reformulation in terms of zero stalks away from `Z`;
- `core/canonical`: the algebraic-structure pushforward owner theorem from Lemma 6.32.4;
- `bridge/view`: rewriting terminal stalks as zero objects.

Primitive data are only the closed subset `Z`, its canonical inclusion
`TopCat.subsetInclusion X Z`, and the sheaf `ℱ`. The fully faithful statement is already owned
upstream at the subset level, so this file keeps only the source-facing zero-stalk criterion as
new API. -/

local notation "iZ" => X.closedSubsetInclusion Z

/- Fully faithful recall for the pushforward functor on sheaves of abelian groups along the
inclusion of a closed subset. This is exactly the `AddCommGrpCat` specialization of
`subsetSheafPushforward_fullyFaithful`. -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: Lemma 6.32.4 characterizes the essential image by terminal stalks outside `Z`,
-- and in `AddCommGrpCat` terminal objects are exactly zero objects.
/-- Lemma 6.32.3: a sheaf of abelian groups on `X` lies in the essential image of pushforward
from a closed subset `Z ⊆ X` if and only if all of its stalks at points of `X \setminus Z` are
zero. -/
theorem closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage ℱ ↔
      ∀ x : X, x ∉ Z → IsZero (ℱ.presheaf.stalk x) := by
  simpa [addCommGrpCat_isIso_terminal_from_iff_isZero] using
    (closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem Z hZ ℱ)

end
