import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_9_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} [Preorder 𝕜]
variable {J I : Type*}

open scoped BigOperators Matrix

local notation "X" => J → 𝕜
local notation "Y" => I → 𝕜

/-
Source/core/bridge triage:
- `source-facing`: this example specializes the general primal-system format from Text 22.3.9.1
  to the linear inequality system `Ax ≤ a`.
- `core/canonical`: the owner abstraction is `GeneralPrimalSystem`; the concrete data here are the
  matrix `A` and the interval families with unrestricted independent coordinates and upper
  half-lines `(-∞, a_i]` on dependent coordinates.
- `bridge/view`: the companion theorems identify solutions of this specialized primal system at
  `(x, y)` by `y = A *ᵥ x ∧ y ∈ Set.Iic a`, with textbook matrix inequality surfaces
  `y ≤ a` and `A *ᵥ x ≤ a` as derived bridges.
- Domain-style sampling: this item reuses `GeneralPrimalSystem`,
  `GeneralPrimalSystem.ofIntervals`, `GeneralPrimalSystem.IsSolution`, the owner theorems
  `GeneralPrimalSystem.isSolution_iff`, `GeneralPrimalSystem.Feasible`,
  `GeneralPrimalSystem.feasible_iff`, and the mathlib interval APIs
  `Set.ordConnected_univ` and `Set.ordConnected_Iic`.
- Primitive data vs derived API: the interval family and matrix `A` are primitive source-facing
  data for this specialization; tuple-level and feasibility equivalence theorems are derived bridge
  API.
-/

namespace GeneralPrimalSystem

/-- Text 22.3.9.2: the system `Ax ≤ a` is the general primal system with unrestricted independent
coordinates and dependent intervals `(-∞, a_i]`. -/
def ofLe (A : Matrix I J 𝕜) (a : Y) :
    GeneralPrimalSystem 𝕜 J I :=
  GeneralPrimalSystem.ofIntervals
    (fun _ : J ↦ (Set.univ : Set 𝕜))
    (fun i : I ↦ Set.Iic (a i))
    (fun _ ↦ Set.ordConnected_univ)
    (fun _ ↦ Set.ordConnected_Iic)
    A

section Linear

variable [NonUnitalNonAssocSemiring 𝕜] [Fintype J]

-- Proof sketch: specialize `GeneralPrimalSystem.isSolution_iff`; independent-coordinate
-- interval-membership conditions are vacuous because they are `Set.univ`, and dependent-coordinate
-- membership in `Set.Iic (a i)` reassembles as membership in the product interval `Set.Iic a`.
/-- Pair-level intrinsic interval bridge for `GeneralPrimalSystem.ofLe A a`: solving with
coordinates
`(x, y)` means the matrix block relation `y = A *ᵥ x` together with dependent-interval membership
`y ∈ Set.Iic a`. -/
theorem ofLe_isSolution_iff
    (A : Matrix I J 𝕜) (a : Y) (x : X) (y : Y) :
    (ofLe A a).IsSolution x y ↔
      y = A *ᵥ x ∧ y ∈ Set.Iic a := by
  refine
    (GeneralPrimalSystem.isSolution_iff (system := ofLe A a) (x := x) (y := y)).trans
      ?_
  constructor
  · rintro ⟨_, hy, hxy⟩
    exact ⟨hxy, by simpa [Set.mem_Iic, Pi.le_def, ofLe] using hy⟩
  · rintro ⟨hxy, hy⟩
    refine ⟨?_, ?_, hxy⟩
    · intro j
      simp [ofLe]
    · simpa [Set.mem_Iic, Pi.le_def, ofLe] using hy

-- Proof sketch: unfold `Set.Iic` membership in function space.
/-- Pair-level order bridge for `GeneralPrimalSystem.ofLe A a`: solving with coordinates `(x, y)`
means the matrix block relation `y = A *ᵥ x` together with the weak inequality family `y ≤ a`. -/
theorem ofLe_isSolution_iff_le
    (A : Matrix I J 𝕜) (a : Y) (x : X) (y : Y) :
    (ofLe A a).IsSolution x y ↔
      y = A *ᵥ x ∧ y ≤ a := by
  simpa [Set.mem_Iic] using
    (ofLe_isSolution_iff (A := A) (a := a) (x := x) (y := y))

-- Proof sketch: apply the intrinsic pair-level bridge theorem at `y = A *ᵥ x`.
/-- Solutions of `GeneralPrimalSystem.ofLe A a` at the canonical pair `(x, A *ᵥ x)` are exactly the
vectors `x` with `A *ᵥ x ∈ Set.Iic a`. -/
theorem ofLe_isSolution_mulVec_iff
    (A : Matrix I J 𝕜) (a : Y) (x : X) :
    (ofLe A a).IsSolution x (A *ᵥ x) ↔
      A *ᵥ x ∈ Set.Iic a := by
  simpa [ofLe_isSolution_iff] using
    (ofLe_isSolution_iff (A := A) (a := a) (x := x) (y := A *ᵥ x))

-- Proof sketch: rewrite `Set.Iic` membership as pointwise order.
/-- Solutions of `GeneralPrimalSystem.ofLe A a` at the canonical pair `(x, A *ᵥ x)` are exactly the
vectors `x` satisfying `Ax ≤ a`. -/
theorem ofLe_isSolution_mulVec_iff_le
    (A : Matrix I J 𝕜) (a : Y) (x : X) :
    (ofLe A a).IsSolution x (A *ᵥ x) ↔
      A *ᵥ x ≤ a := by
  simpa [Set.mem_Iic] using
    (ofLe_isSolution_mulVec_iff (A := A) (a := a) (x := x))

-- Proof sketch: apply `GeneralPrimalSystem.feasible_iff` and simplify the specialized interval
-- constraints.
/-- Intrinsic interval bridge for feasibility of `GeneralPrimalSystem.ofLe A a`. -/
theorem ofLe_feasible_iff
    (A : Matrix I J 𝕜) (a : Y) :
    (ofLe A a).Feasible ↔
      ∃ x : X, A *ᵥ x ∈ Set.Iic a := by
  refine (GeneralPrimalSystem.feasible_iff (system := ofLe A a)).trans ?_
  simp [Set.mem_Iic, Pi.le_def, ofLe]

-- Proof sketch: rewrite `Set.Iic` membership as pointwise order.
/-- Feasibility of the generalized primal system attached to `Ax ≤ a` is equivalent to the usual
matrix-language existence statement for `Ax ≤ a`. -/
theorem ofLe_feasible_iff_exists_le
    (A : Matrix I J 𝕜) (a : Y) :
    (ofLe A a).Feasible ↔
      ∃ x : X, A *ᵥ x ≤ a := by
  simpa [Set.mem_Iic] using
    (ofLe_feasible_iff (A := A) (a := a))

end Linear

end GeneralPrimalSystem

end
