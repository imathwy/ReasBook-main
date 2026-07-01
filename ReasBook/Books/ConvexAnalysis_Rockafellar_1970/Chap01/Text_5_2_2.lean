import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.2.2 records the effect of adding the indicator of a set `C` to a
  finite function `f`.
- `core/canonical`: the canonical owner is the intrinsic two-branch extension
  `C.piecewise f.toWithTopBot ⊤`.
- `bridge/view`: the source expression `f.toWithTopBot + δ(· | C)` is a thin bridge to this
  piecewise owner.

Domain-style sampling used here:
- `Function.toWithTopBot` from `Chap01.EOrder.Basic`;
- `Set.piecewise` as intrinsic owner for extension by `+∞`;
- the indicator notation `δ(· | C)` from `Defintion_4_8_1`.

Primitive data vs derived API:
- primitive data: a set `C : Set E` and an `α`-valued branch `f : E → α`;
- derived API: intrinsic pointwise branch formulas for `C.piecewise f.toWithTopBot ⊤`, and the
  source-facing branch formulas for `f.toWithTopBot + δ(· | C)` via the bridge theorem.

Layer target: owner-first API (`Set.piecewise`) plus source bridge formulas.
-/

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

section

variable {E : Type*}
variable {α : Type*}

namespace Function

/-! Text 5.2.2 owner-level branch laws (canonical surface). -/

@[simp] theorem piecewise_toWithTopBot_of_mem (f : E → α) (C : Set E)
    {x : E} (hx : x ∈ C) :
    (C.piecewise f.toWithTopBot ⊤) x = f x := by
  simp [hx, Function.toWithTopBot]

@[simp] theorem piecewise_toWithTopBot_of_notMem (f : E → α) (C : Set E)
    {x : E} (hx : x ∉ C) :
    (C.piecewise f.toWithTopBot ⊤) x = (⊤ : WithTopBot α) := by
  simp [hx]

/-! Text 5.2.2 source-facing branch laws (bridge surface). -/

section

variable [AddZeroClass α]

/-- Source-to-owner bridge: adding the indicator recovers the intrinsic piecewise extension. -/
theorem toWithTopBot_add_indicator_eq_piecewise (f : E → α) (C : Set E) :
    f.toWithTopBot + (δ[α](· | C)) = C.piecewise f.toWithTopBot ⊤ := by
  funext x
  by_cases hx : x ∈ C <;> simp [hx, Function.toWithTopBot]

/-- On `C`, adding `δ(· | C)` to `f` leaves the finite branch value unchanged. -/
@[simp] theorem toWithTopBot_add_indicator_of_mem (f : E → α) (C : Set E)
    {x : E} (hx : x ∈ C) :
    f.toWithTopBot x + δ[α](x | C) = f x := by
  calc
    f.toWithTopBot x + δ[α](x | C) = (C.piecewise f.toWithTopBot ⊤) x := by
      simpa using congrFun (toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)) x
    _ = f x := piecewise_toWithTopBot_of_mem (f := f) (C := C) hx

-- Off `C`, adding `δ(· | C)` to `f` yields `+∞`.
@[simp] theorem toWithTopBot_add_indicator_of_notMem (f : E → α) (C : Set E)
    {x : E} (hx : x ∉ C) :
    f.toWithTopBot x + δ[α](x | C) = (⊤ : WithTopBot α) := by
  calc
    f.toWithTopBot x + δ[α](x | C) = (C.piecewise f.toWithTopBot ⊤) x := by
      simpa using congrFun (toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)) x
    _ = (⊤ : WithTopBot α) := piecewise_toWithTopBot_of_notMem (f := f) (C := C) hx

end

end Function

end

/- Text 5.2.2 source-to-owner bridge formula. -/
recall Function.toWithTopBot_add_indicator_eq_piecewise

/- Text 5.2.2 canonical owner branch, on-set. -/
recall Function.piecewise_toWithTopBot_of_mem

/- Text 5.2.2 canonical owner branch, off-set. -/
recall Function.piecewise_toWithTopBot_of_notMem

/- Text 5.2.2 source formula, on-set bridge branch: `f + δ(· | C)` agrees with `f` on `C`. -/
recall Function.toWithTopBot_add_indicator_of_mem

/- Text 5.2.2 source formula, off-set bridge branch: `f + δ(· | C)` is `+∞` outside `C`. -/
recall Function.toWithTopBot_add_indicator_of_notMem
