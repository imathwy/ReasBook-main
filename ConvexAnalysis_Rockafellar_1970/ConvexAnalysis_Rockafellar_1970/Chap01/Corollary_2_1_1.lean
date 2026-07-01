import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_0_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

universe u v

section Pairing

variable {R : Type v}
variable {X : Type*} {Y : Type*}
variable [HasPairing X Y R] {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.1.1 says that the solution set of an arbitrary family of linear
  inequalities `⟪x, b i⟫ₚ ≤ β i` is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s`; the relevant canonical closure result is
  `convex_iInter`.
- `bridge/view`: the textbook set `{x | ∀ i, ⟪x, b_i⟫ₚ ≤ β_i}` is the intersection of the chapter's
  owner half-spaces `closedHalfSpaceLE (b i) (β i)`.
- Primitive data vs derived API: the family `b`, the thresholds `β`, and the corresponding closed
  half-spaces are primitive data; convexity of their common intersection is derived API and should
  remain a theorem.
- Domain-style sampling: this item reuses the chapter owner half-space constructor
  `closedHalfSpaceLE`, the owner-side membership lemma `mem_closedHalfSpaceLE_iff`, the
  owner-side convexity theorem `closedHalfSpaceLE_convex`, and the intersection closure theorem
  `convex_iInter`.
-- Layer target for `setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE`: `bridge/view`.
-- This bridge only identifies the textbook inequality presentation with the owner
-- half-space intersection, so it belongs to the primitive pairing-inequality layer
-- `[LE R] [HasPairing X Y R]`.
-/

namespace LinearConstraintRelation

/-- The indexed owner subset cut out by weak linear inequalities `⟪x, b i⟫ₚ ≤ β i`. -/
def leFeasible [LE R] (b : I → Y) (β : I → R) : Set X :=
  {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i}

/-- The owner weak feasible set is the indexed intersection of weak pairing half-spaces. -/
theorem leFeasible_eq_iInter_closedHalfSpaceLE
    [LE R]
    (b : I → Y) (β : I → R) :
    leFeasible b β = ⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X) :=
by
  ext x
  simp [leFeasible, closedHalfSpaceLE]

/-- Membership in `leFeasible b β` is exactly the pointwise weak inequality family
`⟪x, b i⟫ₚ ≤ β i`. -/
@[simp] theorem mem_leFeasible
    [LE R]
    (b : I → Y) (β : I → R) (x : X) :
    x ∈ leFeasible b β ↔ ∀ i, ⟪x, b i⟫ₚ ≤ β i :=
  Iff.rfl

/-- The weak owner feasible set is exactly the textbook pointwise weak inequality set. -/
theorem leFeasible_eq_setOf
    [LE R]
    (b : I → Y) (β : I → R) :
    leFeasible b β = {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} :=
  rfl

end LinearConstraintRelation

/-- The textbook weak-inequality feasible set is exactly the weak owner feasible set. -/
theorem setOf_forall_pairing_le_eq_leFeasible
    [LE R]
    (b : I → Y) (β : I → R) :
    {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} = (LinearConstraintRelation.leFeasible b β : Set X) := by
  simpa using (LinearConstraintRelation.leFeasible_eq_setOf (b := b) (β := β)).symm

/-- The textbook weak-inequality feasible set is exactly the intersection of the owner closed
half-spaces attached to the indexed inequalities. -/
theorem setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE [LE R]
    (b : I → Y) (β : I → R) :
    {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} = ⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (setOf_forall_pairing_le_eq_leFeasible (b := b) (β := β))

end Pairing

section FunctionalPrimitive

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X] {I : Sort u}

namespace LinearMap

/-- Canonical linear-map owner form: an indexed family of linear maps `g i`
cuts out a convex weak feasible set. -/
theorem convex_setOf_forall_le
    (g : I → X →ₗ[𝕜] R) (β : I → R) :
    Convex 𝕜 {x : X | ∀ i, g i x ≤ β i} := by
  simpa [Set.iInter_setOf] using
    (convex_iInter fun i ↦ convex_halfSpace_le (g i).isLinear (β i))

end LinearMap

/-- Intrinsic linear-inequality closure: any indexed family of linear maps
`x ↦ g i x` defines a convex weak feasible set. -/
theorem convex_setOf_forall_le_of_forall_isLinear
    (g : I → X → R) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (g i)) :
    Convex 𝕜 {x : X | ∀ i, g i x ≤ β i} := by
  let gLinear : I → X →ₗ[𝕜] R := fun i ↦ IsLinearMap.mk' (g i) (hlin i)
  simpa [gLinear] using
    (LinearMap.convex_setOf_forall_le (𝕜 := 𝕜) (R := R) (X := X) (g := gLinear) (β := β))

end FunctionalPrimitive

section LinearPrimitive

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*}
variable [HasPairing X Y R] {I : Sort u}

-- Proof sketch: apply `convex_iInter` to the owner family
-- `i ↦ closedHalfSpaceLE (b i) (β i)`, using
-- `closedHalfSpaceLE_convex_of_isLinear` pointwise from the primitive linearity assumptions.
-- Then obtain the textbook set-builder statement by rewriting with
-- `LinearConstraintRelation.leFeasible_eq_setOf`.
namespace LinearConstraintRelation

/-- Canonical bundled-linear-map form: the weak owner feasible set is convex when each indexed
constraint map is presented as a linear map equal to the corresponding pairing evaluation. -/
theorem convex_leFeasible_of_forall_linearMap
    (b : I → Y) (β : I → R)
    (g : I → X →ₗ[𝕜] R)
    (hpair : ∀ i x, g i x = (⟪x, b i⟫ₚ : R)) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  have hset : leFeasible b β = {x : X | ∀ i, g i x ≤ β i} := by
    ext x
    constructor
    · intro hx i
      simpa [hpair i x] using hx i
    · intro hx i
      simpa [hpair i x] using hx i
  rw [hset]
  exact LinearMap.convex_setOf_forall_le (𝕜 := 𝕜) (R := R) (X := X) (g := g) (β := β)

/-- The indexed weak owner feasible set is convex when each pairing evaluation
`x ↦ ⟪x, b i⟫ₚ` is linear. This is the primitive linear-data layer of Corollary 2.1.1. -/
theorem convex_leFeasible_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  let gLinear : I → X →ₗ[𝕜] R := fun i ↦ IsLinearMap.mk' (fun x : X ↦ (⟪x, b i⟫ₚ : R)) (hlin i)
  exact convex_leFeasible_of_forall_linearMap (b := b) (β := β) (g := gLinear)
    (hpair := by
      intro i x
      rfl)

end LinearConstraintRelation

/-- Primitive intersection view of Corollary 2.1.1 under per-constraint linearity assumptions. -/
theorem convex_iInter_closedHalfSpaceLE_family_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.convex_leFeasible_of_forall_isLinear
      (b := b) (β := β) hlin)

/-- Primitive textbook set-builder view of Corollary 2.1.1 under per-constraint linearity
assumptions. -/
theorem convex_setOf_forall_pairing_le_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.convex_leFeasible_of_forall_isLinear
      (b := b) (β := β) hlin)

end LinearPrimitive

section Linear

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Bridge form: the indexed weak owner feasible set is convex under a linear pairing. -/
theorem convex_leFeasible (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  exact LinearConstraintRelation.convex_leFeasible_of_forall_linearMap
    (𝕜 := 𝕜) (X := X) (Y := Y) (R := 𝕜) (b := b) (β := β)
    (g := fun i ↦ HasLinearPairing.pairingLinear.flip (b i))
    (hpair := by
      intro i x
      simp [HasLinearPairing.pairing_eq_pairingLinear])

end LinearConstraintRelation

/-- Bridge form: the owner intersection of indexed weak pairing half-spaces is convex under a
linear pairing. -/
theorem convex_iInter_closedHalfSpaceLE_family
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.convex_leFeasible (X := X) (b := b) (β := β))

/-- Bridge form: Corollary 2.1.1 under a linear pairing owner. -/
theorem convex_setOf_forall_pairing_le
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.convex_leFeasible (X := X) (b := b) (β := β))

/-- Corollary 2.1.1, stated coordinate-free: the common solution set of any family of linear weak
inequalities is convex. -/
theorem convex_linear_inequality_solution_set
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} :=
  convex_setOf_forall_pairing_le (X := X) (Y := Y) (b := b) (β := β)

end Linear
