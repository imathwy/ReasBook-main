import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_1_4 (from Chap03) -/
/- Definition 3.1.4 is a source-facing recall in the chapter's affine-hyperplane domain.

Primary domain:
- affine hyperplanes, supporting hyperplanes, and separation of a point from a set in a real
  inner-product space. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ`
  setting.

Sampled owner-style declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and an offset;
- `AffineHyperplane.IsSupporting`, the owner-level support predicate;
- `hyperplane`, the coordinate carrier view of an affine hyperplane;
- `StrictlySeparatesPointFromWith`, the coordinate strict point-versus-set bridge;
- mathlib `Set.IsExposed`, a nearby exposed-face owner that is stronger than this source-facing
  point-versus-set hyperplane recall.

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the textbook hyperplane, supporting-hyperplane, and point-versus-set separation
  notions;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: the coordinate carrier `hyperplane g γ`, together with
  `IsSupportingHyperplane`, `SeparatesPointFromWith`, and
  `StrictlySeparatesPointFromWith`.

Primitive data:
- the nonzero normal vector and offset packaged by `AffineHyperplane`.

Derived API:
- the owner-level support and point-separation predicates on `AffineHyperplane`;
- the coordinate bridge declarations `hyperplane`, `IsSupportingHyperplane`,
  `SeparatesPointFromWith`, and `StrictlySeparatesPointFromWith`.

The later two-set separation layer already has its own numbered recall in `Definition_3_12.lean`.
This file therefore recalls only the source-facing owner and bridge declarations for
Definition 3.1.4 instead of keeping a broader inventory that duplicated later chapter material.
-/

recall AffineHyperplane
recall AffineHyperplane.IsSupporting
recall AffineHyperplane.SeparatesPointFrom
recall AffineHyperplane.StrictlySeparatesPointFrom
recall hyperplane
recall IsSupportingHyperplane
recall SeparatesPointFromWith
recall StrictlySeparatesPointFromWith

/-! ### Definition_3_1_4_1 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.1.4.1 lives in the affine-hyperplane / support / point-separation domain.

Sampled owner-style declarations:
- this file's source-facing owner `AffineHyperplane`, whose primitive data are a nonzero normal
  vector and an offset;
- the coordinate carrier bridge `hyperplane g γ`, used downstream when the source is written in
  normal-offset coordinates;
- mathlib `AffineSubspace`, the ambient carrier-level affine owner;
- mathlib `AffineSubspace.SOppSide`, the ambient side-relation API relative to an affine carrier.

Best owner abstraction:
- `AffineHyperplane`

Primitive data:
- a nonzero normal vector and an offset.

Derived API:
- the carrier and the four half-spaces of an affine hyperplane;
- supporting and point-separation predicates on the owner;
- the coordinate bridge surface `hyperplane`, `IsSupportingHyperplane`,
  `SeparatesPointFromWith`, and `StrictlySeparatesPointFromWith`.

`AffineSubspace` and the side-relation API are useful ambient comparison points, but they do not
replace the chapter owner here: the source-facing object carries chosen normal/offset coordinates,
and the later chapter theorems repeatedly reuse that owner-level data directly.
-/

/-- Definition 3.1.4.1: an affine hyperplane in a real inner-product space is determined by a
nonzero normal vector and an offset. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `ℝⁿ` presentation. The carrier set and the support/separation predicates below are
derived from this owner object. -/
structure AffineHyperplane (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  normal_ne_zero : normal ≠ 0
  offset : ℝ

local notation "HPlane" => AffineHyperplane E

namespace AffineHyperplane

/-- The carrier of an affine hyperplane is its defining level set. -/
def carrier (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x = H.offset}

/-- An affine hyperplane coerces to its defining carrier set. This is not `SetLike`, since
different normal/offset pairs can determine the same geometric hyperplane. -/
instance : Coe (AffineHyperplane E) (Set E) where
  coe H := H.carrier

/-- An affine hyperplane can be used as its carrier membership predicate. -/
instance : Membership E (AffineHyperplane E) where
  mem H x := x ∈ (H : Set E)

/-- Membership in the coerced set of an affine hyperplane is exactly its defining level-set
equation. -/
@[simp] theorem mem_coe {H : HPlane} {x : E} :
    x ∈ (H : Set E) ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- Membership in an affine hyperplane is exactly the defining inner-product equation
`⟪H.normal, x⟫ = H.offset`. -/
@[simp] theorem mem_iff {H : HPlane} {x : E} :
    x ∈ H ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- Membership in the carrier of `H` is exactly the defining inner-product equation
`⟪H.normal, x⟫ = H.offset`. -/
@[simp] theorem mem_carrier_iff {H : HPlane} {x : E} :
    x ∈ H.carrier ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- The closed half-space on the lower side of `H`. -/
def closedLowerHalfspace (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x ≤ H.offset}

/-- Membership in the closed lower half-space of `H` is the defining inequality
`⟪H.normal, x⟫ ≤ H.offset`. -/
@[simp] theorem mem_closedLowerHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.closedLowerHalfspace ↔ inner ℝ H.normal x ≤ H.offset := Iff.rfl

/-- The closed half-space on the upper side of `H`. -/
def closedUpperHalfspace (H : HPlane) : Set E :=
  {x | H.offset ≤ inner ℝ H.normal x}

/-- Membership in the closed upper half-space of `H` is the defining inequality
`H.offset ≤ ⟪H.normal, x⟫`. -/
@[simp] theorem mem_closedUpperHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.closedUpperHalfspace ↔ H.offset ≤ inner ℝ H.normal x := Iff.rfl

/-- The open half-space on the lower side of `H`. -/
def openLowerHalfspace (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x < H.offset}

/-- Membership in the open lower half-space of `H` is the defining strict inequality
`⟪H.normal, x⟫ < H.offset`. -/
@[simp] theorem mem_openLowerHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.openLowerHalfspace ↔ inner ℝ H.normal x < H.offset := Iff.rfl

/-- The open half-space on the upper side of `H`. -/
def openUpperHalfspace (H : HPlane) : Set E :=
  {x | H.offset < inner ℝ H.normal x}

/-- Membership in the open upper half-space of `H` is the defining strict inequality
`H.offset < ⟪H.normal, x⟫`. -/
@[simp] theorem mem_openUpperHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.openUpperHalfspace ↔ H.offset < inner ℝ H.normal x := Iff.rfl

/-- `H` supports `Q` when `Q` lies in the closed lower half-space of `H` and `H` meets `Q`. -/
def IsSupporting (H : HPlane) (Q : Set E) : Prop :=
  Q ⊆ H.closedLowerHalfspace ∧ (Q ∩ H.carrier).Nonempty

namespace IsSupporting

theorem le_offset {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) {x : E} (hx : x ∈ Q) : inner ℝ H.normal x ≤ H.offset := by
  exact h.1 hx

theorem contact_nonempty {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) : (Q ∩ H.carrier).Nonempty :=
  h.2

theorem exists_contact_point {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) : ∃ x ∈ Q, inner ℝ H.normal x = H.offset := by
  rcases h.contact_nonempty with ⟨x, hxQ, hxH⟩
  exact ⟨x, hxQ, mem_carrier_iff.mp hxH⟩

end IsSupporting

/-- `H` separates the point `x₀` from `Q` when `Q` lies in the closed lower half-space of `H` and
`x₀` lies on or beyond the opposite side. -/
def SeparatesPointFrom (H : HPlane) (Q : Set E) (x₀ : E) : Prop :=
  Q ⊆ H.closedLowerHalfspace ∧
    x₀ ∈ H.closedUpperHalfspace

/-- `H` strictly separates the point `x₀` from `Q` when one of the two defining inequalities is
strict. -/
def StrictlySeparatesPointFrom (H : HPlane) (Q : Set E) (x₀ : E) : Prop :=
  H.SeparatesPointFrom Q x₀ ∧
    (Q ⊆ H.openLowerHalfspace ∨ x₀ ∈ H.openUpperHalfspace)

end AffineHyperplane

/-- Coordinate bridge for the carrier of the hyperplane with normal vector `g` and offset `γ`.
When `g = 0`, this level set is `∅` or `Set.univ`, so the mathematically faithful owner notion is
`AffineHyperplane`, not this unrestricted carrier. -/
def hyperplane (g : E) (γ : ℝ) : Set E :=
  {x | inner ℝ g x = γ}

/-- Membership in `hyperplane g γ` is exactly the defining inner-product equation
`⟪g, x⟫ = γ`. -/
@[simp] theorem mem_hyperplane_iff {g x : E} {γ : ℝ} :
    x ∈ hyperplane g γ ↔ inner ℝ g x = γ := Iff.rfl

@[simp] theorem AffineHyperplane.carrier_eq_hyperplane (H : HPlane) :
    H.carrier = hyperplane H.normal H.offset := rfl

/-- The hyperplane `hyperplane g γ` supports `Q` when `g ≠ 0` and `Q` lies in the closed half-space
`⟪g, x⟫ ≤ γ`, and the hyperplane actually meets `Q`. -/
def IsSupportingHyperplane (Q : Set E) (g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).IsSupporting Q

namespace IsSupportingHyperplane

theorem ne_zero {Q : Set E} {g : E} {γ : ℝ} (h : IsSupportingHyperplane Q g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem isSupporting {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).IsSupporting Q := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem le_offset {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) {x : E} (hx : x ∈ Q) : inner ℝ g x ≤ γ := by
  simpa using h.isSupporting.le_offset hx

theorem contact_nonempty {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) : (Q ∩ hyperplane g γ).Nonempty := by
  simpa using h.isSupporting.contact_nonempty

theorem exists_contact_point {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) : ∃ x ∈ Q, inner ℝ g x = γ := by
  simpa using h.isSupporting.exists_contact_point

end IsSupportingHyperplane

namespace AffineHyperplane

@[simp] theorem isSupportingHyperplane_iff {H : HPlane} {Q : Set E} :
    IsSupportingHyperplane Q H.normal H.offset ↔ H.IsSupporting Q := by
  constructor
  · intro h
    simpa using h.isSupporting
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

/-- The hyperplane `hyperplane g γ` separates the point `x₀` from `Q` when `Q` lies in the closed
half-space `⟪g, x⟫ ≤ γ` and `x₀` lies on or beyond the opposite side. -/
def SeparatesPointFromWith (Q : Set E) (x₀ g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).SeparatesPointFrom Q x₀

namespace SeparatesPointFromWith

theorem ne_zero {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem separatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).SeparatesPointFrom Q x₀ := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem le_offset {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) {x : E} (hx : x ∈ Q) : inner ℝ g x ≤ γ := by
  exact h.separatesPointFrom.1 hx

theorem offset_le {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) : γ ≤ inner ℝ g x₀ := by
  exact h.separatesPointFrom.2

end SeparatesPointFromWith

namespace AffineHyperplane

@[simp] theorem separatesPointFromWith_iff {H : HPlane} {Q : Set E} {x₀ : E} :
    SeparatesPointFromWith Q x₀ H.normal H.offset ↔ H.SeparatesPointFrom Q x₀ := by
  constructor
  · intro h
    simpa using h.separatesPointFrom
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

/-- The hyperplane `hyperplane g γ` strictly separates `x₀` from `Q` when it separates `x₀` from
`Q` and at least one of the two defining inequalities is strict. -/
def StrictlySeparatesPointFromWith (Q : Set E) (x₀ g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).StrictlySeparatesPointFrom Q x₀

namespace StrictlySeparatesPointFromWith

theorem ne_zero {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem strictlySeparatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).StrictlySeparatesPointFrom Q x₀ := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem separatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).SeparatesPointFrom Q x₀ :=
  h.strictlySeparatesPointFrom.1

end StrictlySeparatesPointFromWith

namespace AffineHyperplane

@[simp] theorem strictlySeparatesPointFromWith_iff {H : HPlane} {Q : Set E} {x₀ : E} :
    StrictlySeparatesPointFromWith Q x₀ H.normal H.offset ↔ H.StrictlySeparatesPointFrom Q x₀ := by
  constructor
  · intro h
    simpa using h.strictlySeparatesPointFrom
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

end

/-! ### Lemma_3_1_4 (from Chap03) -/
open scoped WithTopConvexAnalysis

/- Lemma 3.1.4 is a source-facing recall in the chapter's univariate closed-convex continuity
domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `dom f`, `withTopRealPart` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional` from `Lemma_3_4`
- mathlib `continuousWithinAt_iff_continuousAt_restrict`

Best owner abstraction:
- `ClosedConvexFunction f`, with `dom f` and `withTopRealPart f` as the canonical derived
  domain/view data.

Primitive data:
- the effective domain `dom f`
- the finite-value representative `withTopRealPart f`
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: continuity of the finite-value representative on the effective domain
- core/canonical: `ClosedConvexFunction`
- bridge/view: the restriction-based continuity formalization on the effective-domain subtype

This file therefore recalls the upstream owner theorem directly instead of maintaining a second
proof of the same continuity statement.
-/

recall ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
    {f : ℝ → WithTop ℝ} (hf : ClosedConvexFunction f) :
    ContinuousOn (withTopRealPart f) (dom f)

/-! ### Theorem_3_1_4 (from Chap03) -/
/- Theorem 3.1.4 is a source-facing recall in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and their real sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexFunction`
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Source/core/bridge triage:
- source-facing: the sublevel-set consequence recorded as Theorem 3.1.4
- core/canonical: `ClosedConvexFunction`
- bridge/view: the epigraph-based owner API behind `ClosedConvexFunction`

Primitive data:
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- the recalled owner theorem `ClosedConvexFunction.isClosed_convex_sublevelSet`

This file therefore reuses the canonical owner theorem directly, without rebuilding the broader
five-result package that previously overreached the source theorem. -/

recall ClosedConvexFunction.isClosed_convex_sublevelSet

/-! ### Theorem_3_1_4_1 (from Chap03) -/
/- Theorem 3.1.4.1 is a recall-only file in the chapter's affine-hyperplane strong-separation
domain.

Relevant sampled declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and offset
- `AreStronglySeparable` in `Definition_3_12`, the set-level owner predicate
- `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side` in `Theorem_3_1_13`, the
  chapter owner theorem with the natural argument order
- `areStronglySeparable_of_disjoint_closed_convex_of_one_bounded` in `Theorem_3_15`, the exact
  source-facing theorem surface already present upstream

Best owner abstraction:
- `AreStronglySeparable`

Primitive data:
- the sets `Q₁`, `Q₂`
- nonemptiness, closedness, convexity, disjointness, and one-sided boundedness

Derived API:
- the existing chapter theorem
  `areStronglySeparable_of_disjoint_closed_convex_of_one_bounded`

Source/core/bridge triage:
- source-facing: this numbered theorem item
- core/canonical: `AreStronglySeparable`
- bridge/view: this recall-only file, which now reuses the exact upstream theorem surface instead
  of keeping a second renamed declaration

The previous version duplicated the exact theorem interface already provided by `Theorem_3_15`
under a longer local name. This file now recalls that existing theorem directly, keeping the
source semantics unchanged while removing the parallel wrapper API.
-/

/- Theorem 3.1.4.1 is the direct chapter recall of the existing strong-separation theorem with the
same interface. -/
recall areStronglySeparable_of_disjoint_closed_convex_of_one_bounded

/-! ### Theorem_3_1_4_2 (from Chap03) -/
noncomputable section

universe u

open Filter
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Theorem 3.1.4.2: a frontier point admits a sequence from the complement converging
to it. -/
lemma exists_complement_sequence_tendsto_of_mem_frontier
    {Q : Set E} {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ y : ℕ → E, (∀ n, y n ∉ Q) ∧ Tendsto y atTop (nhds x₀) := by
  -- Rewrite the frontier point as a limit point of the complement.
  have hx₀_closure_compl : x₀ ∈ closure Qᶜ := by
    have hx₀' : x₀ ∈ closure Q ∩ closure Qᶜ := by
      simpa [frontier_eq_closure_inter_closure] using hx₀
    exact hx₀'.2
  -- Sequentialize the closure statement to obtain the desired approximating sequence.
  rcases (mem_closure_iff_seq_limit.mp hx₀_closure_compl) with ⟨y, hy_mem, hy_tendsto⟩
  refine ⟨y, ?_, hy_tendsto⟩
  intro n hyQ
  exact hy_mem n hyQ

/-- Helper for Theorem 3.1.4.2: the Euclidean projection fixes every point already in the feasible
set. -/
lemma euclideanProjection_eq_self_of_mem
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x : E} (hx : x ∈ Q) :
    euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x = x := by
  -- The ambient point itself is a valid projection point once it already lies in `Q`.
  have hxproj : IsProjectionPointOn Q x x := by
    refine ⟨hx, ?_⟩
    simp [Metric.infDist_zero_of_mem hx]
  simpa using
    (hxproj.eq_euclideanProjection hQ_nonempty hQ_closed hQ_convex).symm

/-- Helper for Theorem 3.1.4.2: the normalized displacement from an exterior point to its
projection onto `Q` has unit norm. -/
lemma normalized_projection_direction_norm_eq_one
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {y : E} (hy : y ∉ Q) :
    let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
    let g := ‖y - p‖⁻¹ • (y - p)
    ‖g‖ = 1 := by
  -- The projection point cannot coincide with the exterior point.
  dsimp
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
  have hp : IsProjectionPointOn Q y p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex y
  have hy_sub_ne : y - p ≠ 0 := by
    intro hzero
    have hyp : y = p := sub_eq_zero.mp hzero
    exact hy (hyp.symm ▸ hp.1)
  have hnorm_ne : ‖y - p‖ ≠ 0 := norm_ne_zero_iff.mpr hy_sub_ne
  -- Normalize the nonzero displacement vector.
  calc
    ‖‖y - p‖⁻¹ • (y - p)‖ = |‖y - p‖⁻¹| * ‖y - p‖ := norm_smul _ _
    _ = ‖y - p‖⁻¹ * ‖y - p‖ := by
      rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    _ = 1 := by
      field_simp [hnorm_ne]

/-- Helper for Theorem 3.1.4.2: the normalized projection displacement defines a supporting
inequality at the projection point. -/
lemma normalized_projection_direction_le_offset
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {y x : E} (hx : x ∈ Q) :
    let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
    let g := ‖y - p‖⁻¹ • (y - p)
    inner ℝ g x ≤ inner ℝ g p := by
  -- The projection variational inequality gives the correct sign on the displacement.
  dsimp
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
  let g := ‖y - p‖⁻¹ • (y - p)
  have hp : IsProjectionPointOn Q y p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex y
  have hinner : inner ℝ (y - p) (x - p) ≤ 0 := by
    have hproj : 0 ≤ inner ℝ (p - y) (x - p) :=
      hp.inner_sub_nonneg hQ_convex hx
    have hproj' : 0 ≤ -inner ℝ (y - p) (x - p) := by
      rw [← inner_neg_left]
      simpa [sub_eq_add_neg] using hproj
    exact neg_nonneg.mp hproj'
  have hscaled : inner ℝ g (x - p) ≤ 0 := by
    rw [show g = ‖y - p‖⁻¹ • (y - p) by rfl, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hinner
  -- Rewrite the left-hand side around the projection point.
  calc
    inner ℝ g x = inner ℝ g ((x - p) + p) := by abel_nf
    _ = inner ℝ g (x - p) + inner ℝ g p := by rw [inner_add_right]
    _ ≤ 0 + inner ℝ g p := by linarith
    _ = inner ℝ g p := by simp

/-- Helper for Theorem 3.1.4.2: projection points onto the same convex set move no faster than
their base points. -/
lemma projectionPoint_dist_le_dist
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁) (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  -- Compare each projection point against the other one as a feasible competitor.
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  -- Rearranging isolates the squared norm of `p₁ - p₂`.
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 3.1.4.2: the Euclidean projection map onto a convex set is nonexpansive. -/
lemma euclideanProjection_lipschitzWith
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    LipschitzWith 1 (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex) := by
  -- Apply the projection-point distance estimate to the chosen projection selector.
  refine LipschitzWith.mk_one ?_
  intro x₁ x₂
  exact projectionPoint_dist_le_dist hQ_convex
    (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₁)
    (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₂)

/-- Helper for Theorem 3.1.4.2: projecting a sequence converging to a feasible boundary point
still converges to that boundary point. -/
lemma tendsto_projection_of_tendsto_boundary_point
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀Q : x₀ ∈ Q) {y : ℕ → E}
    (hy : Tendsto y atTop (nhds x₀)) :
    Tendsto (fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n)) atTop (nhds x₀) := by
  -- Compose convergence with the nonexpansive projection map and identify the limit projection.
  have hproj_tendsto :
      Tendsto (fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n))
        atTop
        (nhds (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀)) := by
    exact
      (euclideanProjection_lipschitzWith Q hQ_nonempty hQ_closed hQ_convex).continuous.continuousAt.tendsto.comp hy
  simpa [euclideanProjection_eq_self_of_mem Q hQ_nonempty hQ_closed hQ_convex hx₀Q] using
    hproj_tendsto

/- Theorem 3.1.4.2 lies in the chapter's supporting-hyperplane domain.

Primary domain:
- supporting hyperplanes of closed convex sets in finite-dimensional real inner-product spaces.

Relevant sampled declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and an offset;
- `AffineHyperplane.IsSupporting`, the owner-level support predicate;
- `hyperplane`, the coordinate carrier used by the textbook statement;
- `IsSupportingHyperplane`, the coordinate bridge spelling of support.

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the existence of a supporting hyperplane through a boundary point;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: `hyperplane g γ` together with `IsSupportingHyperplane Q g γ`.

Primitive data:
- the closed convex set `Q` and the boundary point `x₀`.

Derived API:
- the owner-level witness `H : AffineHyperplane E` supporting `Q` through `x₀`;
- the coordinate witness pair `(g, γ)` obtained by unpacking `H`.

The supporting object is intrinsically an `AffineHyperplane`, so this file now exposes that
owner-level theorem directly. The textbook `(g, γ)` statement is kept as a thin bridge companion,
since later files in the chapter still reuse the coordinate witness shape.
-/

/-- Theorem 3.1.4.2 on the owner surface: if `Q` is a closed convex set in a finite-dimensional
real inner-product space and `x₀` is a boundary point of `Q`, then there exists an affine
hyperplane `H` such that `x₀ ∈ H` and `H` supports `Q`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: choose points `y_k ∉ Q` converging to `x₀`, project them to `Q`, and normalize
-- the displacement vectors `y_k - π_Q(y_k)` to unit normals `g_k`. The projection inequality
-- gives supporting affine hyperplanes `H_k`; compactness of the unit sphere and convergence of
-- the projections yield a limit hyperplane `H` supporting `Q` and passing through `x₀`.
theorem exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ H : AffineHyperplane E, x₀ ∈ H ∧ H.IsSupporting Q := by
  -- First recover that the boundary point is feasible, hence `Q` is nonempty.
  have hx₀_closure : x₀ ∈ closure Q := by
    have hx₀' : x₀ ∈ closure Q ∩ closure Qᶜ := by
      simpa [frontier_eq_closure_inter_closure] using hx₀
    exact hx₀'.1
  have hx₀Q : x₀ ∈ Q := by
    simpa [hQ_closed.closure_eq] using hx₀_closure
  let hQ_nonempty : Q.Nonempty := ⟨x₀, hx₀Q⟩
  -- Follow the source proof: approach `x₀` from outside `Q`, then project back to `Q`.
  rcases exists_complement_sequence_tendsto_of_mem_frontier hx₀ with ⟨y, hy_out, hy_tendsto⟩
  let p : ℕ → E := fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n)
  let g : ℕ → E := fun n ↦ ‖y n - p n‖⁻¹ • (y n - p n)
  have hp_tendsto : Tendsto p atTop (nhds x₀) := by
    simpa [p] using
      tendsto_projection_of_tendsto_boundary_point Q hQ_nonempty hQ_closed hQ_convex hx₀Q hy_tendsto
  have hg_norm : ∀ n, ‖g n‖ = 1 := by
    intro n
    simpa [p, g] using
      normalized_projection_direction_norm_eq_one Q hQ_nonempty hQ_closed hQ_convex (hy_out n)
  have hg_mem_sphere : ∀ n, g n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    exact hg_norm n
  -- Compactness of the unit sphere yields a convergent subsequence of normalized normals.
  rcases (isCompact_sphere (0 : E) 1).tendsto_subseq hg_mem_sphere with
    ⟨gStar, hgStar_sphere, φ, hφ_mono, hφ_tendsto⟩
  have hgStar_ne_zero : gStar ≠ 0 := by
    intro hgStar_zero
    have hgStar_norm : ‖gStar‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hgStar_sphere
      exact hgStar_sphere
    rw [hgStar_zero] at hgStar_norm
    norm_num at hgStar_norm
  have hp_subseq_tendsto : Tendsto (fun n ↦ p (φ n)) atTop (nhds x₀) :=
    hp_tendsto.comp hφ_mono.tendsto_atTop
  have hsupport : ∀ x ∈ Q, inner ℝ gStar x ≤ inner ℝ gStar x₀ := by
    intro x hx
    -- Pass the pointwise support inequalities to the subsequential limit.
    have hleft :
        Tendsto (fun n ↦ inner ℝ (g (φ n)) x) atTop (nhds (inner ℝ gStar x)) :=
      Filter.Tendsto.inner hφ_tendsto tendsto_const_nhds
    have hright :
        Tendsto (fun n ↦ inner ℝ (g (φ n)) (p (φ n))) atTop (nhds (inner ℝ gStar x₀)) :=
      Filter.Tendsto.inner hφ_tendsto hp_subseq_tendsto
    have hineq : ∀ n, inner ℝ (g (φ n)) x ≤ inner ℝ (g (φ n)) (p (φ n)) := by
      intro n
      simpa [p, g] using
        normalized_projection_direction_le_offset
          Q hQ_nonempty hQ_closed hQ_convex hx
    exact le_of_tendsto_of_tendsto' hleft hright hineq
  -- Package the limit normal into the supporting affine hyperplane through `x₀`.
  refine ⟨⟨gStar, hgStar_ne_zero, inner ℝ gStar x₀⟩, ?_, ?_⟩
  · simp
  · constructor
    · intro x hx
      simpa [AffineHyperplane.closedLowerHalfspace] using hsupport x hx
    · refine ⟨x₀, hx₀Q, ?_⟩
      simp

/-- Theorem 3.1.4.2 in textbook coordinates: if `Q` is a closed convex set in a finite-dimensional
real inner-product space and `x₀` is a boundary point of `Q`, then there exist a normal vector `g`
and a scalar `γ` such that `x₀` lies on `hyperplane g γ` and this hyperplane supports `Q`. The
textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
theorem exists_supporting_hyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ g : E, ∃ γ : ℝ, x₀ ∈ hyperplane g γ ∧ IsSupportingHyperplane Q g γ := by
  rcases
      exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex
        Q hQ_closed hQ_convex hx₀ with
    ⟨H, hx₀H, hH⟩
  refine ⟨H.normal, H.offset, ?_, ?_⟩
  · simpa [AffineHyperplane.carrier_eq_hyperplane] using hx₀H
  · simpa using hH

end

/-! ### Corollary_3_1_5 (from Chap03) -/
universe u

open scoped ConvexAnalysis SupportFunction

/- Corollary 3.1.5 belongs to the chapter's support-function comparison domain.

Primary domain:
- support functions of subsets of a real inner-product space and the extended-real effective
  domain.

Sampled owner declarations:
- `extendedRealEffectiveDomain` / `dom`
- `supportFunction`
- `subset_of_supportFunction_le_on_domain`
- `supportFunction_eq_on_common_domain_implies_eq`

Best owner abstraction:
- the support-function comparison theorem pair from `Theorem_3_17`, organized over the primitive
  data `supportFunction Q` and `dom ξ[Q]`

Source-facing layer:
- the textbook inclusion and equality criteria for closed convex sets stated via support-function
  comparison on the finite-value domain.

Core/canonical layer:
- `subset_of_supportFunction_le_on_domain`
- `supportFunction_eq_on_common_domain_implies_eq`

Bridge/view:
- none; this file only recalls the owner theorems.

Primitive data:
- `supportFunction Q`
- `dom ξ[Q]`

Derived API:
- inclusion from support-function comparison on the finite-value domain
- equality from agreement on the common finite-value domain

This file therefore keeps no parallel local support-function or effective-domain wrapper, and
recalls the chapter owner theorems directly at the intrinsic real Hilbert-space layer rather than
only at the concrete `ℝⁿ` specialization. -/

/- Corollary 3.1.5 (1) recalls the canonical support-function comparison theorem from
`Theorem_3_17`. -/
recall subset_of_supportFunction_le_on_domain
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q₁ Q₂ : Set E) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₂_closed : IsClosed Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hξ : ∀ g ∈ dom ξ[Q₂], ξ[Q₁] g ≤ ξ[Q₂] g) :
    Q₁ ⊆ Q₂

/- Corollary 3.1.5 (2) recalls the canonical equality criterion obtained by comparing support
functions on their common finite-value domain; the shared-domain hypothesis already handles the
empty/nonempty bookkeeping. -/
recall supportFunction_eq_on_common_domain_implies_eq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂

/-! ### Corollary_3_1_5_1 (from Chap03) -/
/- Corollary 3.1.5.1 lies in the chapter's extended-valued convex-analysis / subgradient domain.

Primary domain:
- subgradients and subdifferentials for `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `IsSubgradientAt`
- `subdifferential`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the subdifferential owner API together with the minimizer-pairing theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `x0 ∈ Q`
- the minimizing hypothesis `IsMinOn f Q xStar`

Derived API:
- the subgradient-membership view `g ∈ subdifferential f x0`
- the pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: the corollary that a subgradient at a feasible point has nonnegative pairing with
  the displacement to a minimizer
- core/canonical: `subdifferential` and the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the chapter theorem `subgradient_inner_sub_nonneg_of_isMinOn`

The previous file introduced a second public theorem whose only extra step was rewriting the
primitive predicate `IsSubgradientAt` as membership in the owner set `subdifferential` via
`mem_subdifferential_iff`, and it had no downstream users. This file therefore recalls the
canonical chapter theorem directly instead of keeping a parallel wrapper around the owner
abstraction. -/

recall subgradient_inner_sub_nonneg_of_isMinOn

/-! ### Definition_3_1_5 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u v

/- Definition 3.1.5 is the chapter's source-facing owner for extended-valued subgradients.

Primary domain:
- convex analysis of extended-real-valued functions on real inner product spaces.

Relevant owner-style declarations sampled before refinement:
- `withTopEffectiveDomain`
- `withTopRealPart`
- `ConvexOn ℝ (dom f) (withTopRealPart f)`
- there is no mathlib owner for this exact extended-valued subgradient notion

Best owner abstraction:
- the primitive predicate `IsSubgradientAt`

Primitive data:
- `dom f` from `Definition_3_3`
- the feasible-set condition for constrained subgradients
- the ambient inner-product-space structure used by the affine support inequality

Derived API:
- `subdifferential`
- `constrainedSubdifferential`
- their atomic membership lemmas

Source/core/bridge triage:
- source-facing: Definition 3.1.5's subgradient and subdifferential notions
- core/canonical: the owner bridge `withTopEffectiveDomain` from `Definition_3_3`
- bridge/view: the set-valued APIs derived from `IsSubgradientAt`

The textbook states the notion on `ℝⁿ`, but the source-facing owner declarations only need a real
inner-product space over a seminormed additive group. This file therefore keeps the same
mathematical meaning while lifting the owner API to that intrinsic ambient structure, so downstream
Euclidean uses specialize directly instead of carrying a second local wrapper layer. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Definition 3.1.5, generalized from the textbook Euclidean setting: a vector `g` is a
subgradient of an `ℝ ∪ {+∞}`-valued function `f` at `x0` if `x0` lies in the effective domain of
`f` and the affine function `y ↦ f x0 + ⟪g, y - x0⟫` supports `f` from below on that domain. -/
def IsSubgradientAt (f : V → WithTop ℝ) (x0 g : V) : Prop :=
  x0 ∈ dom f ∧
    ∀ ⦃y : V⦄, y ∈ dom f →
      f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)

/-- A subgradient can only be taken at a point of `dom f`. -/
-- Proof sketch: project the first conjunct from the definition of `IsSubgradientAt`.
theorem IsSubgradientAt.mem_dom
    {f : V → WithTop ℝ} {x0 g : V} (hg : IsSubgradientAt f x0 g) :
    x0 ∈ dom f :=
  hg.1

section AffinePullback

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Precomposing by an affine map pulls a subgradient back along the adjoint of the linear part. -/
theorem IsSubgradientAt.comp_affineMap
    {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {f : W → WithTop ℝ} {g : V →ᵃ[ℝ] W} {x0 : V} {h : W}
    (hh : IsSubgradientAt f (g x0) h) :
    IsSubgradientAt (f ∘ g) x0 (g.linear.adjoint h) := by
  refine ⟨?_, ?_⟩
  · simpa [Function.comp] using hh.mem_dom
  · intro y hy
    have hy' : g y ∈ dom f := by
      simpa [Function.comp] using hy
    have hineq := hh.2 hy'
    have hgsub : g y - g x0 = g.linear (y - x0) := by
      simpa using (g.linearMap_vsub y x0).symm
    have hinner : inner ℝ h (g y - g x0) = inner ℝ (g.linear.adjoint h) (y - x0) := by
      rw [hgsub, ← g.linear.adjoint_inner_left]
    rw [hinner] at hineq
    simpa [Function.comp] using hineq

end AffinePullback

/-- The subdifferential of `f` at `x0` is the set of all subgradients of `f` at `x0`. -/
def subdifferential (f : V → WithTop ℝ) (x0 : V) : Set V :=
  {g | IsSubgradientAt f x0 g}

/- Lean surface notation for the textbook unconstrained subdifferential `∂f(x0)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂ " f:arg "(" x:arg ")" =>
  subdifferential f x

/-- Membership in the subdifferential is exactly the defining subgradient inequality on the
effective domain. -/
-- Proof sketch: unfold `subdifferential`; membership in the defining set is exactly
-- `IsSubgradientAt f x0 g`.
@[simp]
theorem mem_subdifferential_iff
    {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂ f(x0) ↔ IsSubgradientAt f x0 g :=
  Iff.rfl

namespace IsSubgradientAt

/-- For a real-valued function, the canonical `WithTop`-valued subgradient owner is exactly the
usual real-valued affine lower-support inequality. -/
theorem coe_real_iff
    {f : V → ℝ} {x0 g : V} :
    IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x0 g ↔
      ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := by
  constructor
  · intro hg y
    have hy : y ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        (((f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa using hg.2 hy
    exact_mod_cast hineq
  · intro h
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hineq :
        (((f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast h y
    simpa using hineq

end IsSubgradientAt

/-- Membership in the lifted subdifferential of a real-valued function is exactly the usual
real-valued affine lower-support inequality. -/
@[simp]
theorem mem_subdifferential_coe_real_iff
    {f : V → ℝ} {x0 g : V} :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x0) ↔
      ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := by
  rw [mem_subdifferential_iff, IsSubgradientAt.coe_real_iff]

/-- The constrained subdifferential of `f` at `x0` relative to `Q` is the set of vectors whose
affine minorant inequality holds for every `y ∈ Q`, with `x0` itself constrained to lie in `Q`
and in the effective domain of `f`. -/
def constrainedSubdifferential
    (Q : Set V) (f : V → WithTop ℝ) (x0 : V) :
    Set V :=
  {g | x0 ∈ Q ∧
      x0 ∈ dom f ∧
      ∀ ⦃y : V⦄, y ∈ Q →
        f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)}

/- Lean surface notation for the textbook constrained subdifferential `∂_Q f(x0)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂[" Q "] " f:arg "(" x:arg ")" =>
  constrainedSubdifferential Q f x

/-- Membership in the constrained subdifferential is exactly its defining affine lower-support
condition on `Q`. -/
@[simp]
theorem mem_constrainedSubdifferential_iff
    {Q : Set V} {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂[Q] f(x0) ↔
      x0 ∈ Q ∧
        x0 ∈ dom f ∧
        ∀ ⦃y : V⦄, y ∈ Q →
          f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ) :=
  Iff.rfl

end

/-! ### Definition_3_1_5_1 (from Chap03) -/
open scoped WithTopConvexAnalysis

universe u

/- This item is a source-facing recall in the chapter's extended-valued constrained
subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`, the upstream source-facing owner for affine lower-support inequalities on the
  effective domain;
- `subdifferential`, the unconstrained set-valued owner derived from `IsSubgradientAt`;
- `constrainedSubdifferential`, the canonical owner for the textbook constrained subdifferential;
- `mem_constrainedSubdifferential_iff`, the defining membership expansion for that owner.

Best owner abstraction:
- `constrainedSubdifferential`

Primitive data:
- a feasible set `Q`
- an extended-real-valued function `f`
- a base point `x0`

Derived API:
- the source-facing notation `∂[Q] f(x0)`
- `mem_constrainedSubdifferential_iff`

Source/core/bridge triage:
- source-facing: the textbook constrained subdifferential `∂_Q f(x₀)`
- core/canonical: `constrainedSubdifferential`
- bridge/view: `mem_constrainedSubdifferential_iff`

This file therefore reuses the existing chapter owner directly instead of introducing a Euclidean
wrapper, a theorem-shaped alias, or a second local notation shell. The recall signatures below
match the upstream binder surface exactly. -/

/- Definition 3.1.5.1: the constrained subdifferential of an extended-real-valued function `f`
at a point `x₀` relative to a set `Q` is the canonical set `constrainedSubdifferential Q f x₀`,
written `∂[Q] f(x₀)`, consisting of all vectors whose affine support inequality holds for every
`y ∈ Q`, with `x₀` itself lying in `Q ∩ dom f`. -/
recall constrainedSubdifferential
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : Set V) (f : V → WithTop ℝ) (x0 : V) : Set V

/-- Membership in the constrained subdifferential unfolds to the feasibility condition
`x₀ ∈ Q ∩ dom f` together with the affine lower-support inequality on `Q`. -/
recall mem_constrainedSubdifferential_iff
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Q : Set V} {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂[Q] f(x0) ↔
      x0 ∈ Q ∧
        x0 ∈ dom f ∧
        ∀ ⦃y : V⦄, y ∈ Q →
          f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)

/-! ### Definition_3_1_5_2 (from Chap03) -/
/- Definition 3.1.5.2 is the textbook positive-part map `x ↦ (x)_+`. In mathlib this notion is
owned by the notation class `PosPart`, whose canonical map is `posPart`, written `x⁺`.

Primary domain:
- positive-part operations in ordered additive algebra.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `posPart_eq_ite`

Best owner abstraction:
- `posPart`

Primitive data:
- none in this file; the positive-part operation is supplied upstream by mathlib instances.

Derived API:
- `posPart_def`
- `posPart_eq_ite`

Source/core/bridge triage:
- source-facing: the textbook positive-part map `x ↦ (x)_+`
- core/canonical: `posPart`
- bridge/view: `posPart_def` and `posPart_eq_ite`, giving the lattice and linear-order formulas

This file therefore recalls the owner declaration directly together with its canonical lattice and
linear-order formulas. Downstream specializations should use these upstream bridge lemmas directly
instead of introducing parallel public shell theorems. -/

recall posPart {α : Type*} [PosPart α] : α → α

recall posPart_def
    {α : Type*} [Lattice α] [AddGroup α] (a : α) :
    a⁺ = a ⊔ 0

recall posPart_eq_ite
    {α : Type*} [LinearOrder α] [AddGroup α] {a : α} :
    a⁺ = if 0 ≤ a then a else 0

/-! ### Definition_3_1_5_3 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis
open scoped NormalCone

universe u

/- Definition 3.1.5.3 belongs to the chapter's canonical normal-cone API for the sublevel set
`{x ∈ dom f | f x ≤ f x0}`.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant sampled declarations:
- `normalCone`
- `neg_mem_normalCone_iff`
- `extendedRealEffectiveDomain`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Owner abstraction:
- `normalCone`

Primitive data:
- `extendedRealEffectiveDomain f`
- the source-facing sublevel set `{x ∈ dom f | f x ≤ f x0}`

Derived API:
- the textbook spelling with the explicit domain condition and the inequality
  `inner ℝ g (x0 - x) ≥ 0`

This file therefore states the numbered item as a bridge from the owner abstraction instead of
introducing a parallel local predicate.

Source/core/bridge triage:
- source-facing: the textbook inequality for the sublevel set `{x ∈ dom f | f x ≤ f x0}`
- core/canonical: `normalCone`
- bridge/view: `neg_mem_normalCone_iff` specialized to that source-facing set-builder

The base-point finiteness assumption `x0 ∈ dom f` is redundant for this normal-cone equivalence:
the set itself already records the only finiteness data used by the owner theorem. -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Definition 3.1.5.3: membership of `-g` in the normal
cone to the sublevel set `{x ∈ dom f | f x ≤ f x₀}` at `x₀` is
equivalent to the textbook inequality `⟪g, x₀ - x⟫ ≥ 0` for every `x` with `f x ≤ f x₀`. -/
-- Proof sketch: specialize `neg_mem_normalCone_iff` to the sublevel set
-- `{x | x ∈ dom f ∧ f x ≤ f x0}` and unpack the resulting set membership.
theorem level_set_inequality_at_iff
    {f : V → EReal} {x0 g : V} :
    (-g) ∈ N[{x | x ∈ dom f ∧ f x ≤ f x0}] x0 ↔
      ∀ ⦃x : V⦄, x ∈ dom f →
        f x ≤ f x0 →
          inner ℝ g (x0 - x) ≥ 0 := by
  rw [neg_mem_normalCone_iff]
  constructor
  · intro hg x hx hxlevel
    exact hg x ⟨hx, hxlevel⟩
  · intro hg x hx
    exact hg hx.1 hx.2

end

/-! ### Definition_3_1_5_4 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

/- Definition 3.1.5.4 lives in the chapter's extended-valued convex-analysis domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner product spaces.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `mem_subdifferential_iff`
- `constrainedSubdifferential`

Best owner abstraction:
- the pointwise owner `subdifferential` from `Definition_3_1_5`

Primitive data reused from upstream owners:
- the pointwise subdifferentials `subdifferential f x`
- the indexing set `X`

Derived API introduced here:
- `commonRegularSubdifferential`
- the textbook surface notation `∂̂ f(X)`
- `mem_commonRegularSubdifferential_iff`
- the real-valued bridge/view `commonRegularSubdifferentialOn`
- `mem_commonRegularSubdifferentialOn_iff`

Source/core/bridge triage:
- source-facing: the common regular subdifferential `commonRegularSubdifferential f X`
- core/canonical: the pointwise owner `subdifferential`
- bridge/view: `mem_commonRegularSubdifferential_iff` and
  `commonRegularSubdifferentialOn`

The textbook states the notion on `ℝⁿ`, but this construction depends only on the ambient real
inner-product-space structure already used by the upstream subdifferential owner. This file
therefore keeps the same mathematical meaning while matching that owner ambient generality, so
Euclidean downstream uses specialize directly without a second local wrapper layer. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Definition 3.1.5.4: the common regular subdifferential of `f` on `X` is the intersection of
the pointwise subdifferentials `∂f(x)` over all `x ∈ X`. -/
def commonRegularSubdifferential (f : V → WithTop ℝ) (X : Set V) : Set V :=
  ⋂ x ∈ X, ∂ f(x)

/- Lean surface notation for the textbook common subdifferential `∂̂ f(X)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂̂ " f:arg "(" X:arg ")" =>
  commonRegularSubdifferential f X

/-- Membership in the common regular subdifferential means belonging to every pointwise
subdifferential `∂f(x)` for `x ∈ X`. -/
@[simp] theorem mem_commonRegularSubdifferential_iff
    {f : V → WithTop ℝ} {X : Set V} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x) := by
  simp [commonRegularSubdifferential]

/-- Every common regular subgradient on `X` is a pointwise subgradient at each `x ∈ X`. -/
theorem commonRegularSubdifferential_subset_subdifferential
    {f : V → WithTop ℝ} {X : Set V} {x : V} (hx : x ∈ X) :
    ∂̂ f(X) ⊆ ∂ f(x) := by
  intro g hg
  exact (mem_commonRegularSubdifferential_iff.mp hg) x hx

section Bridge

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bridge/view: the common regular subdifferential of a real-valued function on `X` is the
common regular subdifferential of its canonical `WithTop ℝ` lift. Public theorem surfaces for
real-valued objectives can therefore use the textbook notation `∂̂ f(X)` directly. -/
abbrev commonRegularSubdifferentialOn (X : Set V) (f : V → ℝ) : Set V :=
  commonRegularSubdifferential (fun x ↦ (f x : WithTop ℝ)) X

/- Real-valued surface notation for the common regular subdifferential, reusing the same
textbook spelling `∂̂ f(X)` as the upstream `WithTop` owner. -/
scoped[WithTopConvexAnalysis] notation:max "∂̂ " f:arg "(" X:arg ")" =>
  commonRegularSubdifferentialOn X f

/-- For real-valued objectives, membership in `∂̂ f(X)` is exactly the pointwise affine
lower-support inequality on every `x ∈ X`. -/
theorem mem_commonRegularSubdifferentialOn_iff
    {X : Set V} {f : V → ℝ} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, ∀ y : V, f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg x hx
    exact mem_subdifferential_coe_real_iff.mp <|
      (mem_commonRegularSubdifferential_iff.mp hg) x hx
  · intro hg
    rw [mem_commonRegularSubdifferential_iff]
    intro x hx
    exact mem_subdifferential_coe_real_iff.mpr <| hg x hx

end Bridge

/-! ### Definition_3_1_5_5 (from Chap03) -/
universe u v

open Set

/- Definition 3.1.5.5 lies in the source-facing domain of bounded intersections for set-valued
maps.

Primary domain:
- bounded intersections of set-valued maps.

Sampled owner-style declarations:
- `Set.iInter`;
- `Set.mem_iInter₂`.

Best owner abstraction:
- the common-value set attached to a set-valued map on a set.

Primitive data:
- a domain type `α`;
- a codomain type `β`;
- a set-valued map `S : α → Set β`;
- an index set `X : Set α`.

Derived API:
- the bounded-intersection owner `⋂ x ∈ X, S x`;
- the membership bridge `Set.mem_iInter₂`.

Source/core/bridge triage:
- source-facing: `commonValueSet`;
- core/canonical: `Set.iInter`;
- bridge/view: `Set.mem_iInter₂`.

This file keeps the source-facing object aligned with the textbook notation `\hat{\mathcal S}(X)`
while realizing it directly by the canonical bounded intersection over `X`. -/

section

variable {α : Type u} {β : Type v}

/-- Definition 3.1.5.5: for a set-valued map `S` and a set `X`, the common-value set
`\hat{\mathcal S}(X)` is the bounded intersection `⋂ x ∈ X, S x`. -/
def commonValueSet (S : α → Set β) (X : Set α) : Set β :=
  ⋂ x ∈ X, S x

/-- Helper for Definition 3.1.5.5: membership in the common-value set is equivalent to belonging
to every value `S x` with `x ∈ X`. -/
theorem mem_commonValueSet_iff {S : α → Set β} {X : Set α} {y : β} :
    y ∈ commonValueSet S X ↔ ∀ x ∈ X, y ∈ S x := by
  -- Unfold the source-facing owner to the canonical bounded intersection.
  change y ∈ (⋂ x ∈ X, S x : Set β) ↔ ∀ x ∈ X, y ∈ S x
  -- The generic owner theorem for bounded intersections closes the membership bridge.
  exact Set.mem_iInter₂

end

/-! ### Lemma_3_1_5 (from Chap03) -/
/- Lemma 3.1.5 is now a recall-only surface in the chapter's finite directional-derivative
domain.

Sampled owner-style declarations:
- `convexDirectionalDerivative` in `Theorem_3_21`, the owner extended-valued directional
  derivative;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the owner
  convexity theorem for the theorem-level finite directional-derivative view;
- `convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior`, whose canonical pointwise
  scaling surface is the owner projection `map_smul`, and
  `convexDirectionalDerivativeReal_affine_support_of_mem_interior` in `Lemma_3_1_3_1`, the
  source-facing real directional-derivative consequences.

Best owner abstraction:
- `convexDirectionalDerivative`, together with its theorem-level finite directional-derivative
  view.

Primitive data:
- none in this file; all directional-derivative data is already owned upstream.

Derived API:
- the recalled real-valued consequences used at this point in the chapter.

Source/core/bridge triage:
- source-facing: the real-valued convexity, positive-homogeneity, and affine-support statements;
- core/canonical: `convexDirectionalDerivative`;
- bridge/view: this recall surface.

The previous version duplicated the same real-valued theorem surface with local proofs. This file
now recalls the canonical chapter declarations directly instead of keeping a second parallel copy.
-/

recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_affine_support_of_mem_interior

/-! ### Lemma_3_1_5_1 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/-
Lemma 3.1.5.1 lies in the chapter's extended-valued constrained-subdifferential / closed-convex
domain.

Sampled owner-style declarations:
- `∂[Q] f(x)` / `constrainedSubdifferential` in `Definition_3_1_5`, the owner local subgradient
  object;
- `mem_constrainedSubdifferential_iff` in `Definition_3_1_5`, the atomic membership expansion for
  that owner;
- `convexOn_of_constrainedSubdifferential_nonempty` in `Lemma_3_6`, the canonical convexity
  consequence of pointwise constrained-subdifferential nonemptiness;
- `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty` in `Lemma_3_6`, the companion
  lower-semicontinuity consequence.

Best owner abstraction:
- the constrained-subdifferential owner `∂[Q] f(x)` together with its atomic membership lemma;
- the two exact owner consequences already proved in `Lemma_3_6`.

Primitive data:
- the feasible set `Q`;
- the `WithTop ℝ`-valued objective `f`;
- pointwise nonemptiness of `∂[Q] f(x)` on `Q`.

Derived API in this file:
- the atomic finiteness consequence `Q ⊆ dom f`;
- the exact owner recalls for convexity and lower semicontinuity on `Q`.

Source/core/bridge triage:
- source-facing: the textbook pointwise-subgradient hypothesis and its atomic finiteness
  consequence `Q ⊆ dom f`;
- core/canonical: `dom f`, `∂[Q] f(x)`, `mem_constrainedSubdifferential_iff`, and the two owner
  consequence theorems from `Lemma_3_6`;
- bridge/view: none in this file.

This file therefore keeps only the genuinely new atomic finiteness theorem at the weakest ambient
subgradient layer, and reuses the exact convexity and lower-semicontinuity owner theorems by
direct recall instead of exporting a stronger repackaging layer.
-/

section DomainFiniteness

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Q : Set V} {f : V → WithTop ℝ}

/-- Lemma 3.1.5.1: if every point of `Q` has a nonempty constrained subdifferential, then `f` is
finite on `Q`. The convexity conclusion, which does require convexity of `Q`, and the companion
lower-semicontinuity conclusion are already the exact owner theorems recalled just below. -/
-- Proof sketch: membership in `∂[Q] f(x)` already contains the primitive
-- domain fact `x ∈ dom f`, so pointwise nonemptiness on `Q` immediately yields `Q ⊆ dom f`.
theorem subset_withTopEffectiveDomain_of_constrainedSubdifferential_nonempty
    (hsubgrad : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) :
    Q ⊆ dom f := by
  intro x hx
  rcases hsubgrad x hx with ⟨g, hg⟩
  simpa using (mem_constrainedSubdifferential_iff.mp hg).2.1

end DomainFiniteness

section RecallConsequences

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {f : E → WithTop ℝ}

/- Lemma 3.1.5.1's convexity conclusion is the exact owner theorem already proved in `Lemma_3_6`.
The hypothesis block stays source-faithful; only the redundant local wrapper is removed. -/
recall convexOn_of_constrainedSubdifferential_nonempty

/- Lemma 3.1.5.1's lower-semicontinuity conclusion is the exact owner theorem already proved in
`Lemma_3_6`. -/
recall lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty

end RecallConsequences

end

/-! ### Proposition_3_1_5_1 (from Chap03) -/
/- Proposition 3.1.5.1 lies in the chapter's real positive-part / subdifferential domain.

Primary domain:
- the one-dimensional subdifferential of the positive-part function.

Relevant owner-style declarations sampled before refinement:
- `posPart` and `posPart_def`, the canonical positive-part owner and its `max` specialization;
- `real_posPart_subdifferential_at_zero_eq_Icc` in `Proposition_3_12`, the earlier chapter theorem
  with the exact source-facing interface;
- the recall-only bridge in `Proposition_3_13`, which now reuses that owner directly.

Best owner abstraction:
- `real_posPart_subdifferential_at_zero_eq_Icc`.

Primitive data:
- none in this file; the statement is already completely owned upstream.

Derived API:
- this recall-only bridge for the numbered textbook item.

Source/core/bridge triage:
- source-facing: the textbook claim identifying the subdifferential of `x ↦ max x 0` at `0`;
- core/canonical: the earlier chapter theorem `real_posPart_subdifferential_at_zero_eq_Icc`;
- bridge/view: this file only, which recalls that owner theorem instead of exporting a third
  parallel theorem shell.

The previous version duplicated an exact theorem already present upstream. This refinement removes
that duplicate wheel and reuses the earlier chapter owner directly. -/

/- Proposition 3.1.5.1: for the real positive-part function `x ↦ max x 0`, the set of real
numbers `g` satisfying the global affine lower-support inequality
`max x 0 ≥ max 0 0 + g * (x - 0)` for every `x` is exactly the interval `[0, 1]`. -/
recall real_posPart_subdifferential_at_zero_eq_Icc
