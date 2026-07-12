import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Source/core/bridge triage:
- `source-facing`: the cohomology window
  `H^n(K) ⟶ H^n(L) ⟶ H^n(M) ⟶ H^(n + 1)(K)` attached to a short exact sequence of
  cochain complexes;
- `core/canonical`: `HomologicalComplex.HomologySequence.composableArrows₅` and
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `bridge/view`: specialization of those canonical owners to the cochain shape
  `ComplexShape.up ℤ`.
-/

/- 22.4.2.1: in the chapter context of a short exact sequence `K ⟶ L ⟶ M` of
differential graded modules, the displayed segment
`H^n(K) ⟶ H^n(L) ⟶ H^n(M) ⟶ H^(n + 1)(K)`
is the middle four-term window of the canonical long exact cohomology sequence. In the current
Lean environment this is the `ComplexShape.up ℤ` specialization of the owner
`HomologicalComplex.HomologySequence.composableArrows₅`, with adjacent exactness supplied by
`hS.homology_exact₂ n` and `hS.homology_exact₃ n (n + 1) (up_mk n (n + 1) rfl)`. -/
recall composableArrows₅

/- Companion exactness: the left and right adjacent exactness assertions in this source-facing
window are the canonical theorems `ShortComplex.ShortExact.homology_exact₂` and
`ShortComplex.ShortExact.homology_exact₃`. -/
recall ShortComplex.ShortExact.homology_exact₂
recall ShortComplex.ShortExact.homology_exact₃

/- Companion recall: the displayed boundary map `H^n(M) ⟶ H^(n + 1)(K)` is the canonical
connecting morphism `ShortComplex.ShortExact.δ`. -/
recall ShortComplex.ShortExact.δ

/- Companion exactness: the whole displayed five-term cohomology segment is exact by the owner
theorem `HomologicalComplex.HomologySequence.composableArrows₅_exact`; this theorem is its
source-facing specialization to cochain complexes. -/
theorem ShortComplex.ShortExact.cochainComposableArrows₅_exact
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ) :
    (composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).Exact :=
  composableArrows₅_exact hS n (n + 1) (up_mk n (n + 1) rfl)

end

end CategoryTheory
