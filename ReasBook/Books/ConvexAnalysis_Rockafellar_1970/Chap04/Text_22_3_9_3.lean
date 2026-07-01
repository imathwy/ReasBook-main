import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_9_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*}
variable {I J : Type*}

open scoped Matrix

local notation "X" => J → 𝕜
local notation "Y" => I → 𝕜

/-!
Source/core/bridge triage for this item.

- `source-facing`: this example identifies the system `x ≥ 0`, `Ax = a` as a special case of the
  general primal systems introduced in Text 22.3.9.1.
- `core/canonical`: the owner abstractions are `GeneralPrimalSystem` and
  `GeneralPrimalSystem.IsSolution` on split coordinate blocks `(x, y)`.
- `bridge/view`: the interval family with `[0, ∞)` on independent coordinates and `[a_i, a_i]` on
  dependent coordinates bridges the matrix equality system to the general primal owner API, with
  preorder-level theorems phrased intrinsically as interval membership
  `x ∈ Ici 0` and `A *ᵥ x ∈ Icc a a`, and `PartialOrder` corollaries recovering the textbook
  matrix-equality surface `A *ᵥ x = a`.
- Domain-style sampling: this item reuses the project declarations `GeneralPrimalSystem`,
  `GeneralPrimalSystem.ofIntervals`, `GeneralPrimalSystem.IsSolution`, the owner theorem
  `GeneralPrimalSystem.isSolution_mulVec_iff`, `GeneralPrimalSystem.feasible_iff`,
  and the mathlib interval APIs `ordConnected_Ici` and `ordConnected_Icc`.
- Primitive data vs derived API: the interval family with `[0, ∞)` and `[a_i, a_i]` together with
  the matrix `A` are the primitive source-facing specialization data; pair-form and feasibility
  equivalences are derived bridge API.
-/

namespace GeneralPrimalSystem

/-- Text 22.3.9.3: the system `x ≥ 0`, `Ax = a` is represented by the general primal system whose
independent-coordinate intervals are `[0, ∞)` and dependent-coordinate intervals are `[a_i, a_i]`.
Over `PartialOrder`, this recovers the singleton/equality specialization. -/
def ofNonnegativeEq
    [Preorder 𝕜] [Zero 𝕜]
    (A : Matrix I J 𝕜) (a : Y) : GeneralPrimalSystem 𝕜 J I :=
  GeneralPrimalSystem.ofIntervals
    (fun _ : J ↦ Set.Ici (0 : 𝕜))
    (fun i : I ↦ Set.Icc (a i) (a i))
    (fun _ ↦ Set.ordConnected_Ici)
    (fun _ ↦ Set.ordConnected_Icc)
    A

section LinearPreorder

variable [Preorder 𝕜] [NonUnitalNonAssocSemiring 𝕜] [Fintype J]

/-- Pair-level intrinsic interval bridge for `GeneralPrimalSystem.ofNonnegativeEq A a`. -/
theorem ofNonnegativeEq_isSolution_iff_mem_Ici_Icc
    (A : Matrix I J 𝕜) (a : Y) (x : X) (y : Y) :
    (ofNonnegativeEq A a).IsSolution x y ↔
      x ∈ Set.Ici (0 : X) ∧ y ∈ Set.Icc a a ∧ y = A *ᵥ x := by
  refine
    (GeneralPrimalSystem.isSolution_iff (system := ofNonnegativeEq A a) (x := x) (y := y)).trans
      ?_
  constructor
  · rintro ⟨hx, hy, hEq⟩
    refine ⟨?_, ?_, hEq⟩
    · simpa [Set.mem_Ici, Pi.le_def, ofNonnegativeEq] using hx
    · simpa [Set.mem_Icc, Pi.le_def, forall_and, ofNonnegativeEq] using hy
  · rintro ⟨hx, hy, hEq⟩
    refine ⟨?_, ?_, hEq⟩
    · simpa [Set.mem_Ici, Pi.le_def, ofNonnegativeEq] using hx
    · simpa [Set.mem_Icc, Pi.le_def, forall_and, ofNonnegativeEq] using hy

/-- Pair-level order bridge for `GeneralPrimalSystem.ofNonnegativeEq A a`. -/
theorem ofNonnegativeEq_isSolution_iff_le
    (A : Matrix I J 𝕜) (a : Y) (x : X) (y : Y) :
    (ofNonnegativeEq A a).IsSolution x y ↔
      0 ≤ x ∧ a ≤ y ∧ y ≤ a ∧ y = A *ᵥ x := by
  constructor
  · intro hxy
    rcases
        (ofNonnegativeEq_isSolution_iff_mem_Ici_Icc (A := A) (a := a) (x := x) (y := y)).1 hxy with
      ⟨hx, hy, hEq⟩
    have hy' : a ≤ y ∧ y ≤ a := by
      simpa [Set.mem_Icc] using hy
    exact ⟨by simpa [Set.mem_Ici] using hx, hy'.1, hy'.2, hEq⟩
  · rintro ⟨hx, hLower, hUpper, hxy⟩
    exact (ofNonnegativeEq_isSolution_iff_mem_Ici_Icc (A := A) (a := a) (x := x) (y := y)).2
      ⟨by simpa [Set.mem_Ici] using hx, by simpa [Set.mem_Icc] using And.intro hLower hUpper, hxy⟩

-- Proof sketch: apply the pair-level interval bridge theorem at the canonical choice
-- `y = A *ᵥ x`.
/-- Solutions of `GeneralPrimalSystem.ofNonnegativeEq A a` at the canonical pair `(x, A *ᵥ x)` are
exactly
those with interval membership `x ∈ Set.Ici 0` and `A *ᵥ x ∈ Set.Icc a a`. -/
theorem ofNonnegativeEq_isSolution_mulVec_iff_mem_Ici_Icc
    (A : Matrix I J 𝕜) (a : Y) (x : X) :
    (ofNonnegativeEq A a).IsSolution x (A *ᵥ x) ↔
      x ∈ Set.Ici (0 : X) ∧ A *ᵥ x ∈ Set.Icc a a := by
  simpa [ofNonnegativeEq_isSolution_iff_mem_Ici_Icc] using
    (ofNonnegativeEq_isSolution_iff_mem_Ici_Icc (A := A) (a := a) (x := x)
      (y := A *ᵥ x))

-- Proof sketch: rewrite interval-membership bridges using order notation.
/-- Solutions of `GeneralPrimalSystem.ofNonnegativeEq A a` at the canonical pair `(x, A *ᵥ x)` are
exactly
those with `0 ≤ x` and `a ≤ A *ᵥ x ≤ a`. -/
theorem ofNonnegativeEq_isSolution_mulVec_iff_le
    (A : Matrix I J 𝕜) (a : Y) (x : X) :
    (ofNonnegativeEq A a).IsSolution x (A *ᵥ x) ↔
      0 ≤ x ∧ a ≤ A *ᵥ x ∧ A *ᵥ x ≤ a := by
  simpa [Set.mem_Ici, Set.mem_Icc] using
    (ofNonnegativeEq_isSolution_mulVec_iff_mem_Ici_Icc (A := A) (a := a) (x := x))

-- Proof sketch: apply `GeneralPrimalSystem.feasible_iff` and simplify the specialized
-- interval constraints.
/-- Intrinsic interval bridge for feasibility of `GeneralPrimalSystem.ofNonnegativeEq A a`. -/
theorem ofNonnegativeEq_feasible_iff_exists_mem_Ici_Icc
    (A : Matrix I J 𝕜) (a : Y) :
    (ofNonnegativeEq A a).Feasible ↔
      ∃ x : X, x ∈ Set.Ici (0 : X) ∧ A *ᵥ x ∈ Set.Icc a a := by
  refine (GeneralPrimalSystem.feasible_iff (system := ofNonnegativeEq A a)).trans ?_
  simp [Set.mem_Ici, Set.mem_Icc, Pi.le_def, forall_and, ofNonnegativeEq]

/-- Feasibility of the generalized primal system attached to `x ≥ 0`, `Ax = a` is equivalent to the
existence of `x` with `0 ≤ x` and `a ≤ A *ᵥ x ≤ a`. -/
theorem ofNonnegativeEq_feasible_iff_exists_le
    (A : Matrix I J 𝕜) (a : Y) :
    (ofNonnegativeEq A a).Feasible ↔
      ∃ x : X, 0 ≤ x ∧ a ≤ A *ᵥ x ∧ A *ᵥ x ≤ a := by
  simpa [Set.mem_Ici, Set.mem_Icc] using
    (ofNonnegativeEq_feasible_iff_exists_mem_Ici_Icc (A := A) (a := a))

end LinearPreorder

section LinearPartialOrder

variable [PartialOrder 𝕜] [NonUnitalNonAssocSemiring 𝕜] [Fintype J]

/-- Over a partial order, the preorder-level constraints `a ≤ Ax ≤ a` are equivalent to `Ax = a`.
This recovers the equality-language specialization `x ≥ 0`, `Ax = a`. -/
theorem ofNonnegativeEq_isSolution_mulVec_iff_eq
    (A : Matrix I J 𝕜) (a : Y) (x : X) :
    (ofNonnegativeEq A a).IsSolution x (A *ᵥ x) ↔
      0 ≤ x ∧ A *ᵥ x = a := by
  constructor
  · intro hx
    rcases (ofNonnegativeEq_isSolution_mulVec_iff_le (A := A) (a := a) (x := x)).1 hx with
      ⟨hNonneg, hLower, hUpper⟩
    exact ⟨hNonneg, le_antisymm hUpper hLower⟩
  · rintro ⟨hNonneg, hEq⟩
    refine (ofNonnegativeEq_isSolution_mulVec_iff_le (A := A) (a := a) (x := x)).2 ?_
    refine ⟨hNonneg, ?_, ?_⟩ <;> simp [hEq]

/-- Over a partial order, feasibility for `GeneralPrimalSystem.ofNonnegativeEq A a` is equivalent
to the
matrix-language existence statement `∃ x, 0 ≤ x ∧ A *ᵥ x = a`. -/
theorem ofNonnegativeEq_feasible_iff_eq
    (A : Matrix I J 𝕜) (a : Y) :
    (ofNonnegativeEq A a).Feasible ↔
      ∃ x : X, 0 ≤ x ∧ A *ᵥ x = a := by
  constructor
  · intro hfeas
    rcases (ofNonnegativeEq_feasible_iff_exists_le (A := A) (a := a)).1 hfeas with
      ⟨x, hNonneg, hLower, hUpper⟩
    exact ⟨x, hNonneg, le_antisymm hUpper hLower⟩
  · rintro ⟨x, hNonneg, hEq⟩
    refine (ofNonnegativeEq_feasible_iff_exists_le (A := A) (a := a)).2 ?_
    refine ⟨x, hNonneg, ?_, ?_⟩ <;> simp [hEq]

end LinearPartialOrder

end GeneralPrimalSystem

end
