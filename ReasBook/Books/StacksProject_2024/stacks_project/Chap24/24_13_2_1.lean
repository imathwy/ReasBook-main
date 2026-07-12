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
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ)

-- Semantic search note: `lean_leansearch` was unavailable in this runner; the owner/API choice
-- was checked against local Chapter 22/24 cohomology-sequence recall files and verified mathlib
-- names.

/- 24.13.2.1: in the sheaf-of-differential-graded-modules setting, the displayed cohomology
segment
`H^n(\mathcal K) ⟶ H^n(\mathcal L) ⟶ H^n(\mathcal M) ⟶ H^{n + 1}(\mathcal K)`
is the cochain-complex specialization of the canonical five-term fragment of the long exact
cohomology sequence attached to `hS`. -/
recall composableArrows₅

/- Companion exactness: the adjacent exactness assertions in the displayed source-facing window
are obtained by specializing the canonical owner theorems
`ShortComplex.ShortExact.homology_exact₂` and `ShortComplex.ShortExact.homology_exact₃`. -/
recall ShortComplex.ShortExact.homology_exact₂
recall ShortComplex.ShortExact.homology_exact₃

/- Companion recall: the boundary map
`H^n(\mathcal M) ⟶ H^{n + 1}(\mathcal K)` in that segment is the canonical connecting morphism
owned by `ShortComplex.ShortExact.δ`. -/
recall ShortComplex.ShortExact.δ

/- Companion exactness: the displayed five-term cohomology segment is exact by the canonical
owner theorem `HomologicalComplex.HomologySequence.composableArrows₅_exact`. -/
#check (composableArrows₅_exact hS n (n + 1) (up_mk n (n + 1) rfl) :
    (composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).Exact)

end

end CategoryTheory
