import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap03.Remark_3_11_1
import BauschkeLean.Chap20.Example_20_33
import BauschkeLean.Chap21.Corollary_21_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 21.16 states that finite-dimensional Chebyshev sets are closed and
  convex.
- `core/canonical`: the owner abstractions are the Chapter 3 theorem
  `isClosed_of_isChebyshev`, the projector maximality theorem
  `setValuedProjector_isMaximallyMonotone_of_isChebyshev`, and the Chapter 21 owner theorem
  `SetValuedOperator.convex_closure_range_of_maximal`.
- `bridge/view`: the only local bridge is the source-facing identity `(P[C]).range = C`, obtained
  directly from the best-approximation meaning of `P[C]`.

Primitive data: a set `C` and its Chebyshev witness `hC`.
Derived API: closedness is recalled directly, while convexity is derived by applying the maximal
monotone range-closure theorem to `P[C]` and rewriting its range back to `C`. -/

/- Corollary 21.16 (1): the closure statement is already the Chapter 3 owner theorem
`isClosed_of_isChebyshev`. -/
recall isClosed_of_isChebyshev

/-- Corollary 21.16 (2): in a finite-dimensional real Hilbert space, every Chebyshev set is
convex. -/
theorem convex_of_isChebyshev_finiteDimensional {C : Set H} (hC : IsChebyshev C) :
    Convex ℝ C := by
  have hmax : Maximal SetValuedOperator.IsMonotone (P[C]) :=
    setValuedProjector_isMaximallyMonotone_of_isChebyshev hC
  have hrange : (P[C]).range = C := by
    ext y
    rw [SetValuedOperator.mem_range_iff]
    constructor
    · rintro ⟨x, hy⟩
      exact (mem_setValuedProjector_iff.mp hy).1
    · intro hy
      refine ⟨y, mem_setValuedProjector_iff.mpr ?_⟩
      refine ⟨hy, ?_⟩
      simpa using (Metric.infDist_zero_of_mem_closure (subset_closure hy)).symm
  have hconv : Convex ℝ (closure (P[C]).range) :=
    SetValuedOperator.convex_closure_range_of_maximal (P[C]) hmax
  simpa [hrange, (isClosed_of_isChebyshev hC).closure_eq] using hconv
