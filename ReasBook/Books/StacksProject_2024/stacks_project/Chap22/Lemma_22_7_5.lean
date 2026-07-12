import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_9_15
import StacksProject_2024.Chap22.Lemma_22_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open ComplexShape
open HomologicalComplex

universe u

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

-- Source/core/bridge triage:
-- - `source-facing`: the Chapter 22 existence theorem below, phrased using admissible
--   monomorphisms of differential graded `A`-modules;
-- - `core/canonical`: the Chapter 13 ladder replacement theorem
--   `ComposableArrows.exists_splitMono_homotopyReplacement`, once its upstream proof file is used
--   as the canonical implementation route;
-- - `bridge/view`: the Chapter 22 admissibility/termwise-split equivalence exported by
--   `Lemma_22_7_3`.

/-- Lemma 22.7.5: for a finite composable sequence of differential graded `A`-modules
`L₀ ⟶ L₁ ⟶ ⋯ ⟶ Lₙ`, there is a commutative ladder from another sequence
`M₀ ⟶ M₁ ⟶ ⋯ ⟶ Mₙ` to it such that each lower horizontal map is an admissible monomorphism and
each vertical comparison map `Mᵢ ⟶ Lᵢ` is a homotopy equivalence. -/
@[stacks 09JX]
theorem exists_admissibleMono_homotopyReplacement
    {n : ℕ} (L : ComposableArrows DGMod n) :
    ∃ (M : ComposableArrows DGMod n) (φ : M ⟶ L),
      (∀ i : ℕ, ∀ hi : i < n,
        IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (ComposableArrows.hom (M.arrow i hi))) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences (ModuleCat A) (up ℤ) (φ.app i)) := by
  obtain ⟨M, φ, hsplit, hhom, _, _, _⟩ :=
    ComposableArrows.exists_splitMono_homotopyReplacement L
  refine ⟨M, φ, ?_, hhom⟩
  intro i hi
  simpa [ComposableArrows.arrow] using
    isAdmissibleMono_of_termwiseSplitMono (hsplit ⟨i, hi⟩)

/-- Bridge companion for Lemma 22.7.5: the same replacement theorem, with the lower admissible
condition expressed on the canonical `Fin n` edge indexing of `ComposableArrows`. -/
theorem exists_admissibleMono_homotopyReplacement_finIndexed
    {n : ℕ} (L : ComposableArrows DGMod n) :
    ∃ (M : ComposableArrows DGMod n) (φ : M ⟶ L),
      (∀ i : Fin n,
        IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (M.map' i.1 (i.1 + 1))) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences (ModuleCat A) (up ℤ) (φ.app i)) := by
  obtain ⟨M, φ, hmono, hhom⟩ := exists_admissibleMono_homotopyReplacement L
  refine ⟨M, φ, ?_, hhom⟩
  intro i
  simpa [ComposableArrows.arrow] using hmono i.1 i.2

end

/- Companion recall for Lemma 22.7.5: the underlying replacement theorem is the canonical Chapter
13 ladder theorem `CategoryTheory.ComposableArrows.exists_splitMono_homotopyReplacement`, and the
present file only translates its split-monomorphism clause into the Chapter 22 admissible-mono
language. -/
recall CategoryTheory.ComposableArrows.exists_splitMono_homotopyReplacement
