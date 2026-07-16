import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

noncomputable section

namespace Bifunction

section

variable {U V α : Type*} [ConditionallyCompleteLattice α]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.3.2 is used as a minimax-equality bridge for finite-valued
  kernels on a restricted product domain.
- `core/canonical`: once an explicit source-order saddle witness is available for
  `toWithTopBot K`, the primitive owner data are exactly
  `∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v`.
- `owner abstraction`: the conclusion is the Chapter 36 owner
  `HasSaddleValueOn C D (toWithTopBot K)` together with its defining equality view.

This file intentionally does not keep extra geometric/topological hypotheses on public theorem
surfaces when they are not part of this primitive bridge.
-/

/-- Primitive bridge for this item: an explicit source-order saddle point of `toWithTopBot K` on
`C × D` yields the Chapter 36 saddle-value owner on `C × D`. -/
theorem hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_of_exists_isSaddlePointOn h_saddle

/-- Equality view of `hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn`. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_exists_isSaddlePointOn
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    (hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn (C := C) (D := D) (K := K) h_saddle)

/-- Source-label bridge form: with an explicit saddle witness, no additional compactness-side data
are needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_isCompact_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Source-label bridge form: with an explicit saddle witness, no additional closed/bounded-side
data are needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_closed_bounded_side
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Source-label bridge form: with an explicit saddle witness, no additional bounded-side data are
needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_isBounded_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Equality view under the source closed/bounded-side label. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_closed_bounded_side
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    hasSaddleValueOn_toWithTopBot_of_closed_bounded_side (C := C) (D := D) (K := K) h_saddle

/-- Equality view under the source one-side-bounded label. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_isBounded_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    hasSaddleValueOn_toWithTopBot_of_isBounded_left_or_right (C := C) (D := D) (K := K) h_saddle

end

end Bifunction
