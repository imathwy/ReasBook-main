import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
