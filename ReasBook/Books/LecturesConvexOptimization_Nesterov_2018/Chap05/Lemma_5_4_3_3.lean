import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 5.4.3.3 lies in the Chapter 5 cone-barrier domain.

Sampled owner-style declarations in this domain:
* mathlib `ConvexCone ℝ (E × ℝ)`, the canonical owner for cone domains in the intrinsic ambient
  product space;
* project `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs,
  which realizes the second-order cone as the epigraph of `x ↦ ‖x‖`;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, the canonical `L²` product owner for
  the ambient inner-product geometry of the barrier statement;
* project `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, which already
  states a Chapter 5 logarithmic barrier theorem on that canonical `L²` owner over complete real
  inner-product spaces;
* project `IsSelfConcordantBarrierOnWith`, the canonical barrier owner targeted by the theorem
  below.

Source/core/bridge triage:
* source-facing: the explicit second-order cone barrier formula;
* core/canonical: the second-order cone itself, best owned as `ConvexCone ℝ (E × ℝ)`;
* bridge/view: the membership and evaluation lemmas exposing the textbook formulas directly.

The refinement here is therefore to keep the explicit textbook cone and barrier on raw pairs, use
the canonical `ConvexCone` owner for the cone data, realize its carrier through the chapter
epigraph owner instead of a duplicate set-builder, and state the barrier theorem on the canonical
`L²` product owner `WithLp 2 (E × ℝ)` via the bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook model `ℝⁿ × ℝ`. -/

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
theorem secondOrderCone_smul_mem {τ : ℝ} (hτ : 0 < τ) {p : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) :
    ‖(τ • p).1‖ ≤ (τ • p).2 := by
  calc
    ‖(τ • p).1‖ = τ * ‖p.1‖ := by
      simp [norm_smul, Real.norm_of_nonneg hτ.le]
    _ ≤ τ * p.2 := mul_le_mul_of_nonneg_left hp hτ.le
    _ = (τ • p).2 := by rfl

omit [NormedSpace ℝ E] in
/-- The second-order cone is closed under vector addition. -/
theorem secondOrderCone_add_mem {p q : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) (hq : ‖q.1‖ ≤ q.2) :
    ‖(p + q).1‖ ≤ (p + q).2 := by
  calc
    ‖(p + q).1‖ ≤ ‖p.1‖ + ‖q.1‖ := norm_add_le _ _
    _ ≤ p.2 + q.2 := add_le_add hp hq
    _ = (p + q).2 := rfl

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
def secondOrderCone (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ConvexCone ℝ (E × ℝ) where
  carrier := constrainedEpigraph (Set.univ : Set E) fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)
  smul_mem' := fun {_c} hc {_x} hx ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_smul_mem hc (by simpa [constrainedEpigraph] using hx)
  add_mem' := fun {_x} hx {_y} hy ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_add_mem
        (by simpa [constrainedEpigraph] using hx)
        (by simpa [constrainedEpigraph] using hy)

namespace SecondOrderCone

/- Source-facing notation for the second-order cone owner as a subset of `E × ℝ`. -/
scoped notation "K₂[" E "]" => (secondOrderCone E : Set (E × ℝ))

end SecondOrderCone

open scoped SecondOrderCone

-- Proof sketch: unfold `secondOrderCone`; membership is exactly the displayed norm inequality in
-- the defining set-builder.
/-- Membership in `secondOrderCone` means that the scalar coordinate dominates the Euclidean norm
of the vector coordinate. -/
@[simp]
theorem mem_secondOrderCone_iff (p : E × ℝ) :
    p ∈ K₂[E] ↔ ‖p.1‖ ≤ p.2 := by
  change p ∈ constrainedEpigraph (Set.univ : Set E) (fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)) ↔
      ‖p.1‖ ≤ p.2
  simp [constrainedEpigraph]

-- Proof sketch: `secondOrderCone` is the closed sublevel set of the continuous function
-- `p ↦ ‖p.1‖ - p.2`, so its interior is obtained by replacing the weak inequality by the strict
-- inequality `‖p.1‖ < p.2`.
/-- A point lies in the interior of `secondOrderCone` exactly when its scalar coordinate is
strictly larger than the Euclidean norm of its vector coordinate. -/
theorem mem_interior_secondOrderCone_iff (p : E × ℝ) :
    p ∈ interior K₂[E] ↔ ‖p.1‖ < p.2 := sorry

/-- The logarithmic barrier `(x, t) ↦ -log (t^2 - ‖x‖^2)` on the second-order cone. -/
def secondOrderConeBarrier : E × ℝ → ℝ :=
  fun p ↦ -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ))

-- Proof sketch: unfold `secondOrderConeBarrier`.
omit [NormedSpace ℝ E] in
/-- Evaluating `secondOrderConeBarrier` reproduces the textbook formula
`(x, t) ↦ -log (t^2 - ‖x‖^2)`. -/
@[simp]
theorem secondOrderConeBarrier_apply (p : E × ℝ) :
    secondOrderConeBarrier p =
      -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) := rfl

variable [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: restrict the function to an arbitrary affine line `α ↦ (x + α • h, t + α * τ)`
-- inside `E × ℝ` and compute the derivatives of
-- `-log ((t + α * τ)^2 - ‖x + α • h‖^2)` as in the textbook. The inequality
-- `(t * τ - ⟪x, h⟫)^2 ≥ (t^2 - ‖x‖^2) * (τ^2 - ‖h‖^2)` gives the barrier-parameter bound with
-- `ν = 2`, and the same one-dimensional derivative computation yields the standard
-- self-concordance part on the interior domain `‖x‖ < t`.
/-- Lemma 5.4.3.3: the function `(x, t) ↦ -log (t^2 - ‖x‖^2)` is a `2`-self-concordant barrier
for the second-order cone `K₂ = {(x, t) ∈ E × ℝ | ‖x‖ ≤ t}`, viewed on the canonical `L²`
product owner `WithLp 2 (E × ℝ)` through the canonical raw-pair bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ × ℝ` statement. -/
theorem secondOrderConeBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior K₂[E])
      2
      (secondOrderConeBarrier ∘ ofZ) := sorry
