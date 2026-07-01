import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_7_0

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.0 introduces the lineality space of a proper convex function via
  its recession function.
- `core/canonical`: the primitive chapter owner remains `Function.constancySpace`, but this
  numbered item is function-facing, so the canonical owner surface should be the intrinsic
  function owner `Function.lineal f`, not the derived expression
  `Function.constancySpace ((f)₀⁺)` scattered across theorem headers.
- `bridge/view`: membership bridges are inherited from Definition 8.7.0 and restated directly on
  the function-facing owner.
- Primitive data vs derived API: primitive data are still only the recession function and the
  `Function.constancySpace` owner; `Function.lineal` is the intrinsic function-facing owner built
  from them.
- Layer target: `core/canonical` owner on functions, with thin bridge theorems.

Domain-style sampling used here:
- `Function.recessionCone` and `Function.mem_recessionCone_iff` from Definition 8.5.0;
- `Function.constancySpace`, `Function.mem_constancySpace_iff_mem_recessionCone`, and
  `Function.mem_constancySpace_iff` from Definition 8.7.0;
- `Function.recessionFunction` and notation `(f)₀⁺` from Corollary 8.5.1;
- the set-side owner `Set.lineal` / `Set.mem_lineal_iff` from Definitions 8.4.2 and 8.4.3;
- mathlib's bundled cone owner `PointedCone.lineal`.
-/

open scoped Rockafellar

namespace Function

section

variable {E α : Type*}
variable [Add E] [Neg E]
variable [AddGroup α] [ConditionallyCompleteLattice α]

/-- Definition 8.9.0: the lineality space of a function `f` is the constancy space of its
recession function. -/
def lineal (f : E → WithTopBot α) : Set E :=
  Function.constancySpace ((f)₀⁺)

namespace Rockafellar

scoped[Rockafellar] notation "lin(" f ")" => Function.lineal f

end Rockafellar

/-- Unfolding bridge: `lineal f` is definitionally the constancy space of the recession function
`(f)₀⁺`. -/
theorem lineal_eq_constancySpace (f : E → WithTopBot α) :
    lin(f) = Function.constancySpace ((f)₀⁺) :=
  rfl

/-- Canonicalization bridge: the derived expression `Function.constancySpace ((f)₀⁺)` rewrites to
the function-facing owner `lin(f)`. -/
@[simp] theorem constancySpace_recessionFunction_eq_lineal (f : E → WithTopBot α) :
    Function.constancySpace ((f)₀⁺) = lin(f) :=
  rfl

/-- Membership in `lineal f` means both `y` and `-y` are nonpositive directions for `(f)₀⁺`. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone {f : E → WithTopBot α} {y : E} :
    y ∈ lin(f) ↔ y ∈ Function.recessionCone ((f)₀⁺) ∧ -y ∈ Function.recessionCone ((f)₀⁺) := by
  change y ∈ Function.constancySpace ((f)₀⁺) ↔
      y ∈ Function.recessionCone ((f)₀⁺) ∧ -y ∈ Function.recessionCone ((f)₀⁺)
  simpa using
    (Function.mem_constancySpace_iff_mem_recessionCone (f₀ := ((f)₀⁺)) (y := y))

/-- Membership in `lineal f` is exactly the textbook pair of nonpositivity inequalities for
the recession function. -/
@[simp] theorem mem_lineal_iff {f : E → WithTopBot α} {y : E} :
    y ∈ lin(f) ↔ ((f)₀⁺) y ≤ 0 ∧ ((f)₀⁺) (-y) ≤ 0 := by
  change y ∈ Function.constancySpace ((f)₀⁺) ↔ ((f)₀⁺) y ≤ 0 ∧ ((f)₀⁺) (-y) ≤ 0
  exact (Function.mem_constancySpace_iff (f₀ := ((f)₀⁺)) (y := y))

end

end Function
