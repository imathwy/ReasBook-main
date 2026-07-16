import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace Rockafellar

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.12 defines the set `C₁` in `ℝ^n` by coordinatewise nonnegativity and
  the inequality `ξ₁ + ⋯ + ξ_n ≤ 1`, then identifies its polar.
- `core/canonical`: the project owner abstraction is `Set.polar` for polars of subsets of `ℝ^n`;
  coordinatewise nonnegativity is stated directly because `EuclideanSpace` carries no canonical
  lattice order instance.
- `bridge/view`: the source-facing set is the intersection of the coordinatewise nonnegative set with the
  affine half-space `∑ i, x i ≤ 1`; the companion lemma `mem_unitSimplexSet_iff` expands this back
  to the textbook coordinatewise description.

Domain-style sampling used here:
- `Set.polar` and `Set.mem_polar_iff` from Text 14.0.5;
- direct coordinate evaluation on `EuclideanSpace ℝ (Fin n)`;
- `stdSimplex` from Text 5.5.0.3 as the nearby exact-mass simplex owner, not reused here
  because the source set allows total mass at most `1`.

Primitive data vs derived API:
- primitive datum: the subset `unitSimplexSet n`, built from coordinatewise nonnegativity and
  the half-space `∑ i, x i ≤ 1`;
- derived API: the coordinatewise membership expansion `mem_unitSimplexSet_iff` and the explicit
  coordinatewise description of `(unitSimplexSet n)ᵒ`.

Layer target: `source-facing`.
-/

/-- The example set `C₁` of points in `ℝ^n` with nonnegative coordinates whose coordinate sum is
at most `1`. -/
def unitSimplexSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} ∩
    {x : EuclideanSpace ℝ (Fin n) | ∑ i, x i ≤ 1}

/-- Membership in `unitSimplexSet n` is the textbook conjunction of coordinatewise nonnegativity
and the bound `∑ i, x i ≤ 1`. -/
theorem mem_unitSimplexSet_iff {x : E} :
    x ∈ unitSimplexSet n ↔ (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  rfl

-- Proof sketch: rewrite membership in `(unitSimplexSet n)ᵒ` using
-- `Set.mem_polar_iff_swap`.
-- Evaluating the defining inequality on the standard basis vectors yields `xStar i ≤ 1` for every
-- coordinate. Conversely, if every coordinate of `xStar` is at most `1`, then for any
-- `x ∈ unitSimplexSet n` one has `⟪x, xStar⟫ = ∑ i, x i * xStar i ≤ ∑ i, x i ≤ 1` by
-- `mem_unitSimplexSet_iff`.
/-- Text 14.0.12: if `C₁ = {x ∈ ℝ^n | 0 ≤ x i` for all `i` and `∑ i, x i ≤ 1}`, then
`C₁ᵒ = {xStar ∈ ℝ^n | xStar i ≤ 1` for all `i`}. -/
theorem polar_unitSimplexSet_eq_coordinatewise_le_one :
    (unitSimplexSet n)ᵒ[ℝ] = {xStar : E | ∀ i : Fin n, xStar i ≤ 1} := by
  ext xStar
  rw [Set.mem_setOf_eq, Set.mem_polar_iff_swap]
  constructor
  · intro hx i
    have hsingle : EuclideanSpace.single i (1 : ℝ) ∈ unitSimplexSet n := by
      rw [mem_unitSimplexSet_iff]
      constructor
      · intro j
        by_cases h : j = i
        · subst h
          simp [EuclideanSpace.single]
        · simp [EuclideanSpace.single, h]
      · simp [EuclideanSpace.single]
    have hinner := hx (EuclideanSpace.single i (1 : ℝ)) hsingle
    rw [show (⟪EuclideanSpace.single i (1 : ℝ), xStar⟫ₚ : ℝ) = xStar i by
      simpa [innerₗ_apply_apply] using EuclideanSpace.inner_single_left i (1 : ℝ) xStar] at hinner
    simpa using hinner
  · intro hcoord x hx
    rcases mem_unitSimplexSet_iff.mp hx with ⟨hx_nonneg, hx_sum⟩
    calc
      (⟪x, xStar⟫ₚ : ℝ) = ∑ i, xStar i * x i := by
        change inner ℝ x xStar = ∑ i, xStar i * x i
        simp [PiLp.inner_apply, real_inner_eq_re_inner]
      _ ≤ ∑ i, 1 * x i := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_right (hcoord i) (hx_nonneg i)
      _ = ∑ i, x i := by simp
      _ ≤ 1 := hx_sum

end
