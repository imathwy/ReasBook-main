import ConvexAnalysis_Rockafellar_1970.Chap07.Text_34_1_6
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_36_3

noncomputable section

universe u v

open scoped Rockafellar
namespace SaddleFunction

section

open Bifunction

variable {U : Type u} {V : Type v}
variable {β : Type*}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 36.3.1 says that an ambient saddle-point of a saddle bifunction lies
  in the effective domain, so the associated ambient Chapter 36 saddle value is finite.
- `core/canonical`: the primitive bridge datum is `IsProper K`, which is exactly what is needed
  to recover domain membership and pointwise finiteness from an ambient saddle-point.
- `bridge/view`: the file stays on the canonical Chapter 34/36 owners
  `dom`, `IsSaddlePoint`, `maximinValue`, and `minimaxValue`.

Primary domain:
- minimax and saddle-point theory for ambient-vs-domain bridges.

Layer target: `source-facing`, at the primitive owner layer needed for this corollary.
-/

-- Proof sketch: use the properness-only ambient/domain saddle-point bridge from Theorem 36.3 and
-- read off product-domain membership directly.
/-- If `(u, v)` is an ambient saddle-point for `K`, then `(u, v)` lies in `dom K`,
assuming only the primitive properness owner `IsProper K`. -/
theorem mem_dom_of_isSaddlePoint
    [Preorder β] [Bot β] [Top β]
    {K : U → V → β}
    (hK_proper : IsProper K)
  {u : U} {v : V}
  (hsp : IsSaddlePoint K u v) :
  (u, v) ∈ dom K :=
  (mem_dom_and_isSaddlePointOn_dom_of_isSaddlePoint
    hK_proper hsp).1

-- Proof sketch: first place `(u, v)` in `dom K` from the properness-only ambient/domain bridge;
-- then apply the Chapter 34 product-domain finiteness owner.
/-- An ambient saddle-point is finite pointwise, at the primitive owner layer:
`⊥ < K u v` and `K u v < ⊤`. -/
theorem finite_value_of_isSaddlePoint
    [Preorder β] [Bot β] [Top β]
    {K : U → V → β}
    (hK_proper : IsProper K)
    {u : U} {v : V}
    (hsp : IsSaddlePoint K u v) :
    ⊥ < K u v ∧ K u v < ⊤ := by
  exact bot_lt_and_lt_top_of_mem_dom (mem_dom_of_isSaddlePoint hK_proper hsp)

-- Proof sketch: use primitive finiteness of `K u v` from the previous theorem and identify both
-- ambient Chapter 36 values with `K u v` via the canonical saddle-point value owners.
/-- An ambient saddle-point forces finiteness of both ambient Chapter 36 values:
`maximinValue K` and `minimaxValue K`. -/
theorem finite_saddleValue_of_isSaddlePoint
    [CompleteLattice β]
    {K : U → V → β}
    (hK_proper : IsProper K)
    {u : U} {v : V}
    (hsp : IsSaddlePoint K u v) :
    (⊥ < maximinValue K ∧ maximinValue K < ⊤) ∧
      (⊥ < minimaxValue K ∧ minimaxValue K < ⊤) := by
  have hfin : ⊥ < K u v ∧ K u v < ⊤ :=
    finite_value_of_isSaddlePoint hK_proper hsp
  have hvalue_max : maximinValue K = K u v :=
    maximinValue_eq_of_isSaddlePoint hsp
  have hvalue_min : minimaxValue K = K u v :=
    minimaxValue_eq_of_isSaddlePoint hsp
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa [hvalue_max] using hfin.1, by simpa [hvalue_max] using hfin.2⟩
  · exact ⟨by simpa [hvalue_min] using hfin.1, by simpa [hvalue_min] using hfin.2⟩

end

end SaddleFunction
