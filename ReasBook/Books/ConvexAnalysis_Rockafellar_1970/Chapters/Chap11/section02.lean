import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_11_2_1 (from Chap03) -/
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

/-! ### Theorem_11_2 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
  [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.2 is the separation statement that a nonempty relatively open convex
  set and a disjoint nonempty affine set can be separated by a hyperplane containing the affine
  set.
- `core/canonical`: the primitive relative-openness owner data is the equation `ri[𝕜](·) = ·`,
  together with `Convex 𝕜`, `AffineSubspace 𝕜 V`, and the Chapter 11 separation relation
  `AffineSubspace.Separates`. The source-facing predicate `IsRelativelyOpen 𝕜` is kept as a thin
  bridge.
- `bridge/view`: the textbook phrase “one of the open half-spaces associated with `H` contains
  `C`” is represented owner-theoretically by `H.Separates C M` together with
  `Disjoint C H`; unpacking `H.Separates` recovers the normal equation
  `H = affineHyperplane b β` and the open half-space alternative.
- Primitive data vs derived API: the primitive inputs are the owner equality
  `ri[𝕜](C) = C`, convexity and nonemptiness of `C`, the
  affine-set owner `M`, its intrinsic nonemptiness as `∃ x, x ∈ M`, and the disjointness
  assumption. The containing hyperplane
  and its separation-side properties are theorem-level content and should not be packaged into a
  new structure.
- Domain-style sampling used here: `ri[𝕜](·)`, `AffineSubspace`, the owner relation
  `AffineSubspace.Separates`, and its canonical witness presentation through `affineHyperplane`.
- Layer target: this item stays `source-facing`, but its main public conclusion is refined to the
  affine-subspace owner `H` rather than a raw `∃ b, ∃ β` witness shell.
- Ambient refinement: although Rockafellar states the theorem in `R^n`, the separation owner is
  already pairing-based in `Text_11_0_1`, and relative interior/convexity are scalar-polymorphic.
  So the public theorem surface is upgraded from real inner-product self-pairing to a finite-
  dimensional Hausdorff topological `𝕜`-vector space equipped with an explicit pairing owner.
-/

/-- Theorem 11.2 on the canonical owner layer: if `C` is a nonempty convex set with
`ri[𝕜](C) = C` in a finite-dimensional Hausdorff topological `𝕜`-vector space and `M` is a
nonempty affine set disjoint from `C`, then there is a hyperplane `H` containing `M` such that
`H` separates `C` from `M` and is disjoint from `C`. Unpacking `H.Separates C M` recovers the
textbook open-half-space form.
Specializing to `𝕜 = ℝ` and the inner-product pairing on `V` gives the source `R^n` model. -/
-- Proof sketch: if `M` is already a hyperplane, convexity and relative openness force `C` to lie
-- on one side of it. Otherwise, translate so that `M` becomes a linear subspace and enlarge `M`
-- inductively by one dimension inside a line through the origin that misses the projected convex
-- slice; after finitely many steps this produces a codimension-one affine set containing the
-- original `M` and still disjoint from `C`, whose associated open half-space contains `C`.
theorem exists_separating_hyperplane_containing_of_disjoint_ri_eq_self_convex
    (M : AffineSubspace 𝕜 V) {C : Set V} (hC_ri : ri[𝕜](C) = C) (hC_conv : Convex 𝕜 C)
    (hC_nonempty : C.Nonempty) (hM_nonempty : ∃ x, x ∈ M)
    (hdisj : Disjoint C M) :
    ∃ H : AffineSubspace 𝕜 V, M ≤ H ∧ H.Separates Y C M ∧ Disjoint C H := sorry

/-- Source-facing bridge form of Theorem 11.2: `IsRelativelyOpen 𝕜 C` rewrites to the canonical
owner equation `ri[𝕜](C) = C`. -/
theorem exists_separating_hyperplane_containing_of_disjoint_relativelyOpen_convex
    (M : AffineSubspace 𝕜 V) {C : Set V} (hC_open : IsRelativelyOpen 𝕜 C) (hC_conv : Convex 𝕜 C)
    (hC_nonempty : C.Nonempty) (hM_nonempty : ∃ x, x ∈ M)
    (hdisj : Disjoint C M) :
    ∃ H : AffineSubspace 𝕜 V, M ≤ H ∧ H.Separates Y C M ∧ Disjoint C H := by
  simpa [IsRelativelyOpen] using
    (exists_separating_hyperplane_containing_of_disjoint_ri_eq_self_convex
      M hC_open hC_conv hC_nonempty hM_nonempty hdisj)

end
