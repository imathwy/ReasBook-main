import Mathlib
import Mathlib.Algebra.Group.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_22_3_9_1 (from Chap04) -/
open scoped BigOperators Matrix

section

/-
Source/core/bridge triage:
- `source-facing`: Text 22.3.9.1 introduces interval constraints on the independent coordinates,
  interval constraints on the dependent coordinates, and matrix equations linking the two blocks.
- `core/canonical`: the owner abstraction keeps those two coordinate blocks explicit via
  `(J → 𝕜)` and `(I → 𝕜)` instead of flattening to one concrete finite-coordinate type.
- `bridge/view`: `Set.OrdConnected` is the chapter-level owner abstraction for intervals,
  while `GeneralPrimalSystem.IsSolution` uses the primitive matrix equation `y = A *ᵥ x`;
  the intrinsic relation-set owner is the primary bridge view, and the canonical
  linear-relation subspace is a derived linear bridge view.
- Primitive data vs derived API: intervalhood on each coordinate block and the coefficient matrix
  are primitive; the relation-set owner and subspace owner are derived API.
-/

/-- Text 22.3.9.1: a general primal system is given by intervals on independent coordinates,
intervals on dependent coordinates, and a matrix giving the affine relation `y = A *ᵥ x`. -/
structure GeneralPrimalSystem (𝕜 : Type*) [Preorder 𝕜] (J I : Type*) where
  /-- Interval constraints on the independent coordinates. -/
  leftIntervals : J → Set 𝕜
  /-- Interval constraints on the dependent coordinates. -/
  rightIntervals : I → Set 𝕜
  /-- Each independent-coordinate constraint is an interval. -/
  left_ordConnected (j : J) : Set.OrdConnected (leftIntervals j)
  /-- Each dependent-coordinate constraint is an interval. -/
  right_ordConnected (i : I) : Set.OrdConnected (rightIntervals i)
  /-- The coefficient matrix `A = (α_ij)` of the dependent-coordinate equations. -/
  coeffs : Matrix I J 𝕜

namespace GeneralPrimalSystem

variable {𝕜 : Type*} [Preorder 𝕜] {J I : Type*}

/-- Product-set owner for admissible independent-coordinate vectors. -/
def leftSet (system : GeneralPrimalSystem 𝕜 J I) : Set (J → 𝕜) :=
  Set.pi Set.univ system.leftIntervals

/-- Product-set owner for admissible dependent-coordinate vectors. -/
def rightSet (system : GeneralPrimalSystem 𝕜 J I) : Set (I → 𝕜) :=
  Set.pi Set.univ system.rightIntervals

@[simp] theorem mem_leftSet_iff (system : GeneralPrimalSystem 𝕜 J I) (x : J → 𝕜) :
    x ∈ system.leftSet ↔ ∀ j : J, x j ∈ system.leftIntervals j := by
  simp [leftSet]

@[simp] theorem mem_rightSet_iff (system : GeneralPrimalSystem 𝕜 J I) (y : I → 𝕜) :
    y ∈ system.rightSet ↔ ∀ i : I, y i ∈ system.rightIntervals i := by
  simp [rightSet]

/-- Build a general primal system from interval families on the independent and dependent
coordinate blocks. -/
def ofIntervals
    (leftIntervals : J → Set 𝕜) (rightIntervals : I → Set 𝕜)
    (left_ordConnected : ∀ j : J, Set.OrdConnected (leftIntervals j))
    (right_ordConnected : ∀ i : I, Set.OrdConnected (rightIntervals i))
    (coeffs : Matrix I J 𝕜) :
    GeneralPrimalSystem 𝕜 J I :=
  { leftIntervals := leftIntervals
    rightIntervals := rightIntervals
    left_ordConnected := left_ordConnected
    right_ordConnected := right_ordConnected
    coeffs := coeffs }

@[simp] theorem ofIntervals_leftIntervals
    (leftIntervals : J → Set 𝕜) (rightIntervals : I → Set 𝕜)
    (left_ordConnected : ∀ j : J, Set.OrdConnected (leftIntervals j))
    (right_ordConnected : ∀ i : I, Set.OrdConnected (rightIntervals i))
    (coeffs : Matrix I J 𝕜) :
    (GeneralPrimalSystem.ofIntervals
      leftIntervals rightIntervals left_ordConnected right_ordConnected coeffs).leftIntervals =
      leftIntervals :=
  rfl

@[simp] theorem ofIntervals_rightIntervals
    (leftIntervals : J → Set 𝕜) (rightIntervals : I → Set 𝕜)
    (left_ordConnected : ∀ j : J, Set.OrdConnected (leftIntervals j))
    (right_ordConnected : ∀ i : I, Set.OrdConnected (rightIntervals i))
    (coeffs : Matrix I J 𝕜) :
    (GeneralPrimalSystem.ofIntervals
      leftIntervals rightIntervals left_ordConnected right_ordConnected coeffs).rightIntervals =
      rightIntervals :=
  rfl

@[simp] theorem ofIntervals_coeffs
    (leftIntervals : J → Set 𝕜) (rightIntervals : I → Set 𝕜)
    (left_ordConnected : ∀ j : J, Set.OrdConnected (leftIntervals j))
    (right_ordConnected : ∀ i : I, Set.OrdConnected (rightIntervals i))
    (coeffs : Matrix I J 𝕜) :
    (GeneralPrimalSystem.ofIntervals
      leftIntervals rightIntervals left_ordConnected right_ordConnected coeffs).coeffs =
      coeffs :=
  rfl

section Solution

variable [NonUnitalNonAssocSemiring 𝕜] [Fintype J]

/-- Intrinsic relation owner of a general primal system: the graph relation
`y = system.coeffs *ᵥ x` on split coordinate blocks. -/
def relation (system : GeneralPrimalSystem 𝕜 J I) : SetRel (J → 𝕜) (I → 𝕜) :=
  Function.graph (fun x : J → 𝕜 ↦ system.coeffs *ᵥ x)

/-- Membership in `system.relation` is exactly the matrix relation
`y = system.coeffs *ᵥ x`. -/
@[simp] theorem mem_relation_iff (system : GeneralPrimalSystem 𝕜 J I)
    (ζ : (J → 𝕜) × (I → 𝕜)) :
    ζ ∈ system.relation ↔ ζ.2 = system.coeffs *ᵥ ζ.1 := by
  rcases ζ with ⟨x, y⟩
  simp [relation, Function.graph, eq_comm]

/-- A point `(x, y)` solves a general primal system when each coordinate lies in its prescribed
interval and belongs to the intrinsic graph relation of the coefficient matrix. -/
def IsSolution (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) (y : I → 𝕜) : Prop :=
  x ∈ system.leftSet ∧
    y ∈ system.rightSet ∧
      (x, y) ∈ system.relation

/-- Expand `system.IsSolution` into product-set block conditions and the matrix relation. -/
@[simp] theorem isSolution_iff (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) (y : I → 𝕜) :
    system.IsSolution x y ↔
      x ∈ system.leftSet ∧
        y ∈ system.rightSet ∧
          y = system.coeffs *ᵥ x := by
  simp [IsSolution, mem_relation_iff]

/-- Coordinatewise bridge view for `system.IsSolution`. -/
@[simp] theorem isSolution_iff_forall (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) (y : I → 𝕜) :
    system.IsSolution x y ↔
      (∀ j : J, x j ∈ system.leftIntervals j) ∧
        (∀ i : I, y i ∈ system.rightIntervals i) ∧
          y = system.coeffs *ᵥ x := by
  simp [isSolution_iff]

/-- On the canonical choice `y = system.coeffs *ᵥ x`, the affine block is automatic. -/
@[simp] theorem isSolution_mulVec_iff (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) :
    system.IsSolution x (system.coeffs *ᵥ x) ↔
      x ∈ system.leftSet ∧
        system.coeffs *ᵥ x ∈ system.rightSet := by
  rw [isSolution_iff]
  simp

/-- Coordinatewise bridge view for `isSolution_mulVec_iff`. -/
@[simp] theorem isSolution_mulVec_iff_forall (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) :
    system.IsSolution x (system.coeffs *ᵥ x) ↔
      (∀ j : J, x j ∈ system.leftIntervals j) ∧
        (∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i) := by
  calc
    system.IsSolution x (system.coeffs *ᵥ x) ↔
        x ∈ system.leftSet ∧ system.coeffs *ᵥ x ∈ system.rightSet :=
      isSolution_mulVec_iff (system := system) (x := x)
    _ ↔
        (∀ j : J, x j ∈ system.leftIntervals j) ∧
          (∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i) := by
      simp

/-- Feasibility of a general primal system means existence of some solution pair `(x, y)`. -/
def Feasible (system : GeneralPrimalSystem 𝕜 J I) : Prop :=
  ∃ x : J → 𝕜, ∃ y : I → 𝕜, system.IsSolution x y

@[simp] theorem feasible_iff_exists_isSolution (system : GeneralPrimalSystem 𝕜 J I) :
    system.Feasible ↔ ∃ x : J → 𝕜, ∃ y : I → 𝕜, system.IsSolution x y :=
  Iff.rfl

/-- A general primal system has a solution exactly when there is a choice of independent
coordinates whose induced dependent coordinates satisfy the dependent intervals. -/
theorem exists_isSolution_iff (system : GeneralPrimalSystem 𝕜 J I) :
    (∃ x : J → 𝕜, ∃ y : I → 𝕜, system.IsSolution x y) ↔
      ∃ x : J → 𝕜,
        x ∈ system.leftSet ∧ system.coeffs *ᵥ x ∈ system.rightSet := by
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [isSolution_iff] at hxy
    rcases hxy with ⟨hx, hy, hEq⟩
    refine ⟨x, hx, ?_⟩
    simpa [hEq] using hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, system.coeffs *ᵥ x, ?_⟩
    rw [isSolution_iff]
    exact ⟨hx, hy, rfl⟩

/-- Coordinatewise bridge view for `exists_isSolution_iff`. -/
theorem exists_isSolution_iff_forall (system : GeneralPrimalSystem 𝕜 J I) :
    (∃ x : J → 𝕜, ∃ y : I → 𝕜, system.IsSolution x y) ↔
      ∃ x : J → 𝕜,
        (∀ j : J, x j ∈ system.leftIntervals j) ∧
          ∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i := by
  calc
    (∃ x : J → 𝕜, ∃ y : I → 𝕜, system.IsSolution x y) ↔
        ∃ x : J → 𝕜, x ∈ system.leftSet ∧ system.coeffs *ᵥ x ∈ system.rightSet :=
      exists_isSolution_iff (system := system)
    _ ↔
        ∃ x : J → 𝕜,
          (∀ j : J, x j ∈ system.leftIntervals j) ∧
            ∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i := by
      simp

/-- Feasibility is equivalent to solvability at the canonical dependent coordinates
`y = system.coeffs *ᵥ x`. -/
theorem feasible_iff (system : GeneralPrimalSystem 𝕜 J I) :
    system.Feasible ↔
      ∃ x : J → 𝕜,
        x ∈ system.leftSet ∧ system.coeffs *ᵥ x ∈ system.rightSet := by
  exact (feasible_iff_exists_isSolution (system := system)).trans
    (exists_isSolution_iff (system := system))

/-- Coordinatewise bridge view for `feasible_iff`. -/
theorem feasible_iff_forall (system : GeneralPrimalSystem 𝕜 J I) :
    system.Feasible ↔
      ∃ x : J → 𝕜,
        (∀ j : J, x j ∈ system.leftIntervals j) ∧
          ∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i := by
  calc
    system.Feasible ↔
        ∃ x : J → 𝕜, x ∈ system.leftSet ∧ system.coeffs *ᵥ x ∈ system.rightSet :=
      feasible_iff (system := system)
    _ ↔
        ∃ x : J → 𝕜,
          (∀ j : J, x j ∈ system.leftIntervals j) ∧
            ∀ i : I, (system.coeffs *ᵥ x) i ∈ system.rightIntervals i := by
      simp

/-- Intrinsic bridge view: `system.IsSolution` is equivalent to interval membership plus
relation membership of `(x, y)`. -/
@[simp] theorem isSolution_iff_mem_relation (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) (y : I → 𝕜) :
    system.IsSolution x y ↔
      x ∈ system.leftSet ∧
        y ∈ system.rightSet ∧
          (x, y) ∈ system.relation :=
  Iff.rfl

end Solution

section Linear

variable [CommSemiring 𝕜] [Fintype J]

/-- The canonical owner subspace of a general primal system consists of the coordinate pairs
`(x, y)` satisfying the matrix relation encoded by `system.coeffs`. -/
def subspace (system : GeneralPrimalSystem 𝕜 J I) :
    Submodule 𝕜 ((J → 𝕜) × (I → 𝕜)) :=
  LinearMap.graph (Matrix.mulVecLin system.coeffs)

/-- Membership in `system.subspace` is exactly the matrix relation `y = system.coeffs *ᵥ x`. -/
@[simp] theorem mem_subspace_iff (system : GeneralPrimalSystem 𝕜 J I)
    (ζ : (J → 𝕜) × (I → 𝕜)) :
    ζ ∈ system.subspace ↔ ζ.2 = system.coeffs *ᵥ ζ.1 := by
  rw [subspace, LinearMap.mem_graph_iff]
  simp

/-- Linear bridge view: `system.IsSolution` is equivalent to interval membership plus subspace
membership of `(x, y)`. -/
@[simp] theorem isSolution_iff_mem_subspace (system : GeneralPrimalSystem 𝕜 J I)
    (x : J → 𝕜) (y : I → 𝕜) :
    system.IsSolution x y ↔
      x ∈ system.leftSet ∧
        y ∈ system.rightSet ∧
          (x, y) ∈ system.subspace := by
  rw [isSolution_iff_mem_relation, mem_relation_iff, mem_subspace_iff]

end Linear

end GeneralPrimalSystem

end

/-! ### Text_22_3_9_2 (from Chap04) -/
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

/-! ### Text_22_3_9_3 (from Chap04) -/
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

/-! ### Text_22_3_11 (from Chap04) -/
open Function

/-!
Source/core/bridge triage:
- `source-facing`: Text 22.3.11 introduces support as the index set of nonzero coordinates of a
  coordinate function.
- `core/canonical`: the existing mathlib owner is `support` for functions into a type
  with zero; concrete coordinate models are only downstream specializations.
- `bridge/view`: the textbook display `{j | ζ_j ≠ 0}` is exactly the membership
  predicate given by `mem_support`.
- Domain-style sampling used here: `support`, `mem_support`, and
  `support_subset_iff`.
- Layer target: `bridge/view`, so this item should be a direct canonical recall rather than a new
  local wrapper around the same support notion.
- Abstraction checks:
  - codomain/ambient layer: only `[Zero M]` is needed; no scalar, order, or topology structure.
  - owner layer: intrinsic owner `support` is already the canonical layer.
  - topology language: no ambient/intrinsic topology owner appears in this item.
-/

/- Text 22.3.11: the support of a coordinate function is the canonical set
`support z` of indices whose coordinates are nonzero. -/
recall support

/- Membership in the support is exactly the coordinatewise nonvanishing condition. -/
recall mem_support

/- The primitive support-inclusion owner uses the direct nonzero-membership formulation. -/
recall support_subset_iff

/- Textbook bridge form: support inclusion is equivalent to vanishing outside the containing
index set. -/
recall support_subset_iff'

/-! ### Text_22_3_12 (from Chap04) -/
open Function

section

variable {ι : Type*} {E : Type*} [Zero E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.3.12 introduces the notion of an elementary vector of a linear
  subspace of `ℝ^N`.
- `core/canonical`: the primitive owner is set-based `Set.IsElementary S z`, with support
  minimality expressed by the order-theoretic owner `MinimalFor` applied to
  `Function.support`.
- `bridge/view`: the textbook phrasing "there does not exist a nonzero vector with strictly
  smaller support" is exposed through a single owner-side specification theorem; the
  submodule surface is a thin bridge to the primitive set owner.

Domain-style sampling used here:
- `Set.IsElementary` as the primitive owner layer for support-minimality;
- `Submodule 𝕜 (ι → E)` as the canonical linear bridge owner for chapter-facing use;
- `Function.support` for coordinate support;
- `MinimalFor` and `minimalFor_iff_forall_lt` for inclusion-minimal support.

Primitive data vs derived API:
- primitive owner data: the canonical owner predicate
  `MinimalFor (fun y ↦ y ∈ S ∧ y ≠ 0) support z`;
- derived API: membership/nonzero projection lemmas, support-minimality, the textbook
  strict-subset specification theorem, and the submodule bridge.

Layer target: `source-facing`, with a primitive set owner and a submodule bridge.
-/

namespace Set

/-- Primitive owner for Text 22.3.12: a vector `z` in a carrier set of vectors is elementary when
it is nonzero and its support is minimal, under inclusion, among supports of nonzero vectors from
that carrier. -/
def IsElementary (S : Set (ι → E)) (z : ι → E) : Prop :=
  MinimalFor (fun y : ι → E ↦ y ∈ S ∧ y ≠ 0) support z

/-- The set of elementary vectors of a carrier set. -/
def elementary (S : Set (ι → E)) : Set (ι → E) :=
  S.IsElementary

@[simp] theorem mem_elementary (S : Set (ι → E)) (z : ι → E) :
    z ∈ S.elementary ↔ S.IsElementary z :=
  Iff.rfl

namespace IsElementary

variable {S : Set (ι → E)} {z y w : ι → E}

/-- An elementary vector lies in its carrier set. -/
theorem mem (hz : S.IsElementary z) : z ∈ S :=
  hz.prop.1

/-- An elementary vector is nonzero. -/
theorem ne_zero (hz : S.IsElementary z) : z ≠ 0 :=
  hz.prop.2

/-- An elementary vector has support minimal among supports of nonzero vectors in its carrier
set. -/
theorem support_minimal (hz : S.IsElementary z) (hyS : y ∈ S) (hy0 : y ≠ 0)
    (hsubset : support y ⊆ support z) :
    support z ⊆ support y :=
  hz.le_of_le ⟨hyS, hy0⟩ hsubset

/-- Primitive support-minimal specification equivalent to the owner predicate. -/
theorem iff_mem_ne_zero_and_support_minimal :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  constructor
  · intro hz
    refine ⟨hz.mem, hz.ne_zero, ?_⟩
    intro y hyS hy0 hy_subset
    exact hz.support_minimal hyS hy0 hy_subset
  · rintro ⟨hzS, hz0, hminimal⟩
    rw [Set.IsElementary, minimalFor_iff_forall_lt]
    refine ⟨⟨hzS, hz0⟩, ?_⟩
    intro y hyss hy
    exact hyss.2 (hminimal hy.1 hy.2 hyss.1)

/-- The textbook strict-subset formulation is equivalent to the primitive owner predicate. -/
theorem iff_mem_ne_zero_and_support_ssubset_eq_zero :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → support y ⊂ support z → y = 0 := by
  constructor
  · intro hz
    refine ⟨hz.mem, hz.ne_zero, ?_⟩
    intro y hyS hyss
    by_contra hy0
    exact hz.not_prop_of_lt hyss ⟨hyS, hy0⟩
  · rintro ⟨hzS, hz0, hssubset_zero⟩
    refine (iff_mem_ne_zero_and_support_minimal (S := S) (z := z)).2 ⟨hzS, hz0, ?_⟩
    intro y hyS hy0 hy_subset
    by_contra hz_not_subset
    have hy_ne : support y ≠ support z := by
      intro hy_eq
      exact hz_not_subset hy_eq.symm.subset
    have hyss : support y ⊂ support z :=
      Set.ssubset_iff_subset_ne.2 ⟨hy_subset, hy_ne⟩
    exact hy0 (hssubset_zero hyS hyss)

/-- The textbook strict-subset exclusion form is a direct bridge from the canonical owner-side
strict-subset-zero criterion. -/
theorem iff_mem_ne_zero_and_not_exists_support_ssubset :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ S ∧ y ≠ 0 ∧ support y ⊂ support z := by
  constructor
  · rintro hz
    rcases (iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z)).1 hz with
      ⟨hzS, hz0, hssubset_zero⟩
    refine ⟨hzS, hz0, ?_⟩
    rintro ⟨y, hyS, hy0, hyss⟩
    exact hy0 (hssubset_zero hyS hyss)
  · rintro ⟨hzS, hz0, hno_strict_subset⟩
    refine (iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z)).2 ⟨hzS, hz0, ?_⟩
    intro y hyS hyss
    by_contra hy0
    exact hno_strict_subset ⟨y, hyS, hy0, hyss⟩

/-- Any vector in the same carrier set whose support is strictly smaller than that of an
elementary vector must itself be zero. -/
theorem eq_zero_of_support_ssubset (hz : S.IsElementary z) (hwS : w ∈ S)
    (hw : support w ⊂ support z) :
    w = 0 := by
  by_contra hw0
  exact hz.not_prop_of_lt hw ⟨hwS, hw0⟩

end IsElementary

variable {S : Set (ι → E)} {z : ι → E}

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to membership/nonzero plus support minimality among nonzero vectors of `S`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_minimal :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_minimal (S := S) (z := z))

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to membership/nonzero plus strict-subset vanishing in `S`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → support y ⊂ support z → y = 0 := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z))

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to the textbook strict-subset exclusion criterion. -/
theorem mem_elementary_iff_mem_ne_zero_and_not_exists_support_ssubset :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ S ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset (S := S) (z := z))

end Set

end

section

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
  [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace Submodule

/-- Text 22.3.12 on the canonical linear owner: a vector `z` in a submodule is elementary when it
is elementary in the carrier set of that submodule. -/
def IsElementary (L : Submodule 𝕜 (ι → E)) (z : ι → E) : Prop :=
  (L : Set (ι → E)).IsElementary z

/-- The owner-side set of elementary vectors of `L`. -/
def elementary (L : Submodule 𝕜 (ι → E)) : Set (ι → E) :=
  (L : Set (ι → E)).elementary

@[simp] theorem mem_elementary (L : Submodule 𝕜 (ι → E)) (z : ι → E) :
    z ∈ L.elementary ↔ L.IsElementary z :=
  Iff.rfl

namespace IsElementary

variable {L : Submodule 𝕜 (ι → E)} {z y w : ι → E}

/-- An elementary vector lies in its subspace. -/
theorem mem (hz : L.IsElementary z) : z ∈ L := by
  exact Set.IsElementary.mem hz

/-- An elementary vector is nonzero. -/
theorem ne_zero (hz : L.IsElementary z) : z ≠ 0 :=
  Set.IsElementary.ne_zero hz

/-- An elementary vector has support minimal among the supports of nonzero vectors in its
subspace. -/
theorem support_minimal (hz : L.IsElementary z) (hyL : y ∈ L) (hy0 : y ≠ 0)
    (hsubset : support y ⊆ support z) :
    support z ⊆ support y :=
  Set.IsElementary.support_minimal hz hyL hy0 hsubset

/-- Primitive support-minimal specification equivalent to the canonical owner predicate. -/
theorem iff_mem_ne_zero_and_support_minimal :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_minimal
      (S := (L : Set (ι → E))) (z := z))

/-- The textbook strict-subset formulation is equivalent to the canonical owner predicate for
elementary vectors. -/
theorem iff_mem_ne_zero_and_support_ssubset_eq_zero :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → support y ⊂ support z → y = 0 := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero
      (S := (L : Set (ι → E))) (z := z))

/-- The textbook strict-subset exclusion criterion is a bridge theorem from the canonical
strict-subset-zero owner form. -/
theorem iff_mem_ne_zero_and_not_exists_support_ssubset :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ L ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset
      (S := (L : Set (ι → E))) (z := z))

/-- Any vector in the same subspace whose support is strictly smaller than that of an elementary
vector must itself be zero. -/
theorem eq_zero_of_support_ssubset (hz : L.IsElementary z) (hwL : w ∈ L)
    (hw : support w ⊂ support z) :
    w = 0 :=
  Set.IsElementary.eq_zero_of_support_ssubset hz hwL hw

end IsElementary

variable {L : Submodule 𝕜 (ι → E)} {z : ι → E}

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to membership/nonzero plus support minimality among nonzero vectors
of `L`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_minimal :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_support_minimal (L := L) (z := z))

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to membership/nonzero plus strict-subset vanishing in `L`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → support y ⊂ support z → y = 0 := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero (L := L) (z := z))

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to the textbook strict-subset exclusion criterion. -/
theorem mem_elementary_iff_mem_ne_zero_and_not_exists_support_ssubset :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ L ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset
      (L := L) (z := z))

end Submodule

end
