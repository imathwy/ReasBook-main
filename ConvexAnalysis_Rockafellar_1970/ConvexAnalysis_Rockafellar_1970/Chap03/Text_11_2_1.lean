import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*}
variable [HasPairing X Y 𝕜] {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Text 11.2.1 states that the solution set of a system of weak linear
  inequalities `⟪x, b i⟫ₚ ≤ β i` is a closed convex subset of `R^n`; the coordinate-free pairing
  statement here specializes back to that textbook form.
- `core/canonical`: for this all-`≤` source item, the earlier chapter owner is already the
  textbook feasible set together with its canonical half-space presentation
  `setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE`; there is no need to route through the
  later mixed-relation system wrapper.
- `bridge/view`: the displayed set `{x | ∀ i, ⟪x, b i⟫ₚ ≤ β i}` is the intersection of the owner
  closed half-spaces `closedHalfSpaceLE (b i) (β i)`.
- Primitive data vs derived API: the family of normals `b` and thresholds `β` are primitive data;
  the half-space-intersection presentation and closedness are derived API, while the convexity
  clause is already owned upstream by `convex_setOf_forall_pairing_le`.
- Domain-style sampling: this item reuses the chapter declarations
  `setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE`, `convex_setOf_forall_pairing_le`,
  `closedHalfSpaceLE`, `LowerSemicontinuous.isClosed_preimage`, and `isClosed_iInter`.
- Layer target: `source-facing`, extending the earlier Chapter 1 all-`≤` item from convexity to
  closedness without introducing a parallel owner.
-/

-- Proof sketch: rewrite the displayed feasible set as the intersection of the owner half-spaces
-- `closedHalfSpaceLE (b i) (β i)` and apply `isClosed_iInter`. Lower semicontinuity and
-- continuity are bridge hypotheses that supply closedness of each half-space factor.
namespace LinearConstraintRelation

/-- Primitive owner form: the indexed weak feasible set is closed once each indexed owner
half-space is closed. -/
theorem isClosed_leFeasible_of_forall_isClosed_closedHalfSpaceLE
    [LE 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hclosed : ∀ i, IsClosed (closedHalfSpaceLE (b i) (β i) : Set X)) :
    IsClosed (leFeasible b β : Set X) := by
  rw [leFeasible_eq_iInter_closedHalfSpaceLE]
  exact isClosed_iInter hclosed

/-- The indexed weak owner feasible set is closed once each indexed pairing map is lower
semicontinuous. -/
theorem isClosed_leFeasible_of_forall_lowerSemicontinuous
    [LinearOrder 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hlsc : ∀ i, LowerSemicontinuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed (leFeasible b β : Set X) := by
  refine isClosed_leFeasible_of_forall_isClosed_closedHalfSpaceLE (b := b) (β := β) (fun i ↦ ?_)
  simpa [closedHalfSpaceLE_eq_preimage] using (hlsc i).isClosed_preimage (β i)

/-- Continuous indexed pairing maps give the closed weak owner feasible set. -/
theorem isClosed_leFeasible_of_forall_continuous
    [TopologicalSpace 𝕜] [Preorder 𝕜] [ClosedIicTopology 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hcont : ∀ i, Continuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed (leFeasible b β : Set X) := by
  refine isClosed_leFeasible_of_forall_isClosed_closedHalfSpaceLE (b := b) (β := β) (fun i ↦ ?_)
  simpa [closedHalfSpaceLE_eq_preimage] using isClosed_Iic.preimage (hcont i)

end LinearConstraintRelation

/-- The owner intersection of indexed weak pairing half-spaces is closed once each indexed pairing
map is lower semicontinuous. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_forall_lowerSemicontinuous
    [LinearOrder 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hlsc : ∀ i, LowerSemicontinuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.isClosed_leFeasible_of_forall_lowerSemicontinuous
      (b := b) (β := β) hlsc)

/-- The owner intersection of indexed weak pairing half-spaces is closed once each indexed pairing
map is continuous. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_forall_continuous
    [TopologicalSpace 𝕜] [Preorder 𝕜] [ClosedIicTopology 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hcont : ∀ i, Continuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.isClosed_leFeasible_of_forall_continuous
      (b := b) (β := β) hcont)

-- Proof sketch: use the owner theorem
-- `LinearConstraintRelation.isClosed_leFeasible_of_forall_lowerSemicontinuous` and rewrite with
-- `LinearConstraintRelation.leFeasible_eq_setOf`.
/-- The weak-inequality pairing feasible set is closed once each indexed pairing map is lower
semicontinuous. -/
theorem isClosed_setOf_forall_pairing_le_of_forall_lowerSemicontinuous
    [LinearOrder 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hlsc : ∀ i, LowerSemicontinuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.isClosed_leFeasible_of_forall_lowerSemicontinuous
      (b := b) (β := β) hlsc)

/-- The weak-inequality pairing feasible set is closed once each indexed pairing map is
continuous. -/
theorem isClosed_setOf_forall_pairing_le_of_forall_continuous
    [TopologicalSpace 𝕜] [Preorder 𝕜] [ClosedIicTopology 𝕜]
    (b : I → Y) (β : I → 𝕜)
    (hcont : ∀ i, Continuous (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    IsClosed {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.isClosed_leFeasible_of_forall_continuous
      (b := b) (β := β) hcont)

section

variable [TopologicalSpace 𝕜] [Preorder 𝕜] [ClosedIicTopology 𝕜]
variable [HasContinuousPairing X Y 𝕜]

namespace LinearConstraintRelation

/-- Bridge form: the indexed weak owner feasible set is closed under a continuous pairing. -/
theorem isClosed_leFeasible (b : I → Y) (β : I → 𝕜) :
    IsClosed (leFeasible b β : Set X) := by
  exact isClosed_leFeasible_of_forall_continuous (b := b) (β := β)
    (fun i ↦ HasContinuousPairing.continuous_pairing_left (b i))

end LinearConstraintRelation

/-- Bridge form: the owner intersection of indexed weak pairing half-spaces is closed under a
continuous pairing. -/
theorem isClosed_iInter_closedHalfSpaceLE (b : I → Y) (β : I → 𝕜) :
    IsClosed (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.isClosed_leFeasible (b := b) (β := β))

-- Proof sketch: use the bridge owner theorem `LinearConstraintRelation.isClosed_leFeasible` and
-- rewrite with `LinearConstraintRelation.leFeasible_eq_setOf`.
/-- Bridge form: the weak-inequality pairing feasible set is closed under a continuous pairing. -/
theorem isClosed_setOf_forall_pairing_le (b : I → Y) (β : I → 𝕜) :
    IsClosed {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.isClosed_leFeasible (b := b) (β := β))

end

end
