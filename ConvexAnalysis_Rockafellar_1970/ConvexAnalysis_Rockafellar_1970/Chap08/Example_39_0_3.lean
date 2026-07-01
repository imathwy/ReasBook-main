import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Example 39.0.3 defines, from a map `B`, the process sending a
  nonnegative `u` to the lower set `{x | x ≤ B u}` and sending negative `u` to `∅`.
- `core/canonical`: convex processes in this chapter already live on the relation owner
  `A : SetRel U X` via `A.IsConvexProcess R`.
- `bridge/view`: the source set-valued formula is therefore best encoded directly as the graph
  relation `{(u, x) | 0 ≤ u ∧ x ≤ B u}` attached to `B`.

Primary mathematical domain:
- lower-set processes on ordered types, with linear-map convexity as a specialization.

Domain-style sampling used here:
- `SetRel`, `SetRel.inv`, and `SetRel.image` from `Mathlib.Data.Rel`;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- order inequalities `0 ≤ u` and `x ≤ B u`.

Primitive data vs derived API:
- primitive owner data: a map `B : U → X`;
- primitive source-facing object: the relation `Function.lowerSetProcess B`;
- derived API: graph membership, the forward-fiber formulas on `SetRel.image ({u} : Set U)`, and
  the linear-map convex-process property.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

namespace Function

section

variable {U : Type v} [Zero U] [LE U]
variable {X : Type w} [LE X]

/-- Example 39.0.3: for a map `B` between ordered types, the associated
process is the relation sending `u` to `{x | x ≤ B u}` when `u ≥ 0`, and to `∅` otherwise. On the
canonical relation owner, this is exactly the graph relation `0 ≤ u ∧ x ≤ B u`. -/
def lowerSetProcess (B : U → X) : SetRel U X :=
  {(u, x) | 0 ≤ u ∧ x ≤ B u}

-- Proof sketch: unfold `Function.lowerSetProcess` and the `SetRel` membership notation; the
-- statement is definitional.
/-- Membership in `B.lowerSetProcess` is the conjunction `u ≥ 0` and `x ≤ B u`. -/
@[simp] theorem mem_lowerSetProcess_iff
    (B : U → X) {u : U} {x : X} :
    u ~[B.lowerSetProcess] x ↔ 0 ≤ u ∧ x ≤ B u := by
  rfl

end

section

variable {U : Type v} [Zero U] [LE U]
variable {X : Type w} [Preorder X]

/-- Membership in `B.lowerSetProcess` as lower-set membership. -/
@[simp] theorem mem_lowerSetProcess_iff_mem_Iic
    (B : U → X) {u : U} {x : X} :
    u ~[B.lowerSetProcess] x ↔ 0 ≤ u ∧ x ∈ Set.Iic (B u) := by
  simp [Set.mem_Iic, B.mem_lowerSetProcess_iff]

-- Proof sketch: expand `SetRel.image` on the singleton `{u}` and unfold graph membership in
-- `B.lowerSetProcess`; splitting on `0 ≤ u` yields the source-facing piecewise process formula.
-- The fiber of `B.lowerSetProcess` is the source piecewise map:
-- `Set.Iic (B u)` on `u ≥ 0`, and `∅` on `¬ (0 ≤ u)`.
open Classical in theorem lowerSetProcess_image_singleton
    (B : U → X) (u : U) :
    B.lowerSetProcess.image ({u} : Set U) =
      if 0 ≤ u then Set.Iic (B u) else (∅ : Set X) := by
  by_cases hu : 0 ≤ u
  · ext x
    simp [Function.lowerSetProcess, hu]
  · ext x
    simp [Function.lowerSetProcess, hu]

attribute [simp] lowerSetProcess_image_singleton

-- Proof sketch: specialize `lowerSetProcess_image_singleton` at a nonnegative `u`.
/-- For `u ≥ 0`, the fiber is the lower set `Set.Iic (B u)`. -/
@[simp] theorem lowerSetProcess_image_singleton_of_nonneg
    (B : U → X) {u : U} (hu : 0 ≤ u) :
    B.lowerSetProcess.image ({u} : Set U) = Set.Iic (B u) := by
  simp [Function.lowerSetProcess_image_singleton, hu]

-- Proof sketch: specialize `lowerSetProcess_image_singleton` at `¬ (0 ≤ u)`.
/-- For `¬ (0 ≤ u)`, the fiber of `B.lowerSetProcess` at `u` is empty. -/
@[simp] theorem lowerSetProcess_image_singleton_of_not_nonneg
    (B : U → X) {u : U} (hu : ¬ 0 ≤ u) :
    B.lowerSetProcess.image ({u} : Set U) = (∅ : Set X) := by
  simp [Function.lowerSetProcess_image_singleton, hu]

end

end Function

namespace LinearMap

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [Module R U] [Preorder U] [AddLeftMono U]
variable [PosSMulMono R U]
variable {X : Type w} [AddCommMonoid X] [Module R X] [Preorder X] [AddLeftMono X]
variable [PosSMulMono R X]

-- Proof sketch: on the graph relation `{(u, x) | 0 ≤ u ∧ x ≤ B u}`, addition preserves both the
-- nonnegativity condition on `u` and the upper-bound condition on `x` by linearity of `B` and
-- ordered-module monotonicity. Positive scalar multiplication does the same, and `(0, 0)` belongs
-- to the graph because `B 0 = 0`.
/-- This lower-set relation attached to a linear map is a convex process. -/
theorem lowerSetProcess_isConvexProcess
    (B : U →ₗ[R] X) :
    (Function.lowerSetProcess B).IsConvexProcess R := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro c p hc hp
      rcases p with ⟨u, x⟩
      rcases hp with ⟨hu, hx⟩
      refine ⟨smul_nonneg (le_of_lt hc) hu, ?_⟩
      simpa [map_smul] using smul_le_smul_of_nonneg_left hx (le_of_lt hc)
    · intro p hp q hq a b ha hb hab
      rcases p with ⟨u1, x1⟩
      rcases q with ⟨u2, x2⟩
      rcases hp with ⟨hu1, hx1⟩
      rcases hq with ⟨hu2, hx2⟩
      refine ⟨add_nonneg (smul_nonneg ha hu1) (smul_nonneg hb hu2), ?_⟩
      have h1 : a • x1 ≤ a • B u1 := smul_le_smul_of_nonneg_left hx1 ha
      have h2 : b • x2 ≤ b • B u2 := smul_le_smul_of_nonneg_left hx2 hb
      have hsum : a • x1 + b • x2 ≤ a • B u1 + b • B u2 := add_le_add h1 h2
      simpa [map_add, map_smul] using hsum
  · exact ⟨le_rfl, by simp⟩

end

end LinearMap
