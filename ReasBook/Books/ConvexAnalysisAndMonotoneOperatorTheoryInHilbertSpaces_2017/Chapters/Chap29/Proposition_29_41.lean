import BauschkeLean.Chap04.Definition_4_1
import BauschkeLean.Chap04.Definition_4_26
import BauschkeLean.Chap08.Proposition_8_37
import BauschkeLean.Chap09.Theorem_9_1
import BauschkeLean.Chap17.Proposition_17_41
import BauschkeLean.Chap29.Definition_29_40
import BauschkeLean.Chap29.Example_29_20

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` only surfaced generic convex sublevel and projection owners,
-- so this item uses the project-local Chapter 29 owner
-- `continuousConvexSubgradientProjector`, the Chapter 3 metric projection notation `P[C, hC]`,
-- and the Chapter 4 fixed-point/demiclosedness predicates.

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The supporting closed halfspace from `(29.70)` attached to the point `x` and the selected
subgradient of `f` at `x`. -/
def continuousConvexSubgradientProjectorSupportingHalfspace
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) (s : Selection (∂ f.toEReal))
    (x : H) : Set H :=
  innerProductClosedSublevelSet
    (continuousConvexSelectedSubgradient f hcont hconv s x)
    (ξ - f x + ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ)

section SupportingHalfspace

variable (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
variable (hconv : _root_.ConvexOn ℝ Set.univ f) (s : Selection (∂ f.toEReal))

local notation "C" => lowerLevelSet f.toEReal.asEReal ξ
local notation "Hξ" =>
  continuousConvexSubgradientProjectorSupportingHalfspace f ξ hcont hconv s

/-- Membership in the supporting halfspace from `(29.70)` is exactly the corresponding inner-product
inequality. -/
theorem mem_continuousConvexSubgradientProjectorSupportingHalfspace_iff
    {x y : H} :
    y ∈ Hξ x ↔
      ⟪y, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ ≤
        ξ - f x + ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := by
  simp [continuousConvexSubgradientProjectorSupportingHalfspace,
    mem_innerProductClosedSublevelSet_iff]

/-- Part (2) of Proposition 29.41: the lower level set
`C = lev_{≤ ξ} f` is contained in the supporting halfspace `(29.70)`. -/
theorem lowerLevelSet_subset_continuousConvexSubgradientProjectorSupportingHalfspace
    (x : H) :
    C ⊆ Hξ x := by
  intro z hz
  rw [mem_continuousConvexSubgradientProjectorSupportingHalfspace_iff]
  have hu_mem :
      continuousConvexSelectedSubgradient f hcont hconv s x ∈ (∂ f.toEReal) x := by
    exact continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s x
  have hsub :
      ⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ + f x ≤ f z := by
    -- Convert the selected-subgradient inequality to a real affine bound at `z`.
    have hsubE :
        (((⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ + f x : ℝ) :
            EReal) ≤ (f z : EReal)) := by
      simpa using
        (mem_subdifferential_iff
          f.toEReal x (continuousConvexSelectedSubgradient f hcont hconv s x)).1 hu_mem z
    exact_mod_cast hsubE
  have hzC : f z ≤ ξ := by
    simpa [Function.toEReal_apply] using
      (mem_lowerLevelSet_iff f.toEReal.asEReal ξ z).1 hz
  -- Rearranging the affine bound is exactly the supporting-halfspace inequality.
  have hineq :
      ⟪z, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ ≤
        ξ - f x + ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := by
    have haux :
        f x + ⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ ≤ ξ := by
      have hsub' :
          f x + ⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ ≤ f z := by
        simpa [add_comm] using hsub
      exact le_trans hsub' hzC
    have hdecomp :
        ⟪z, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ =
          ⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ +
            ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := by
      rw [inner_sub_left]
      ring
    calc
      ⟪z, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ
          = ⟪z - x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ +
              ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := hdecomp
      _ ≤ (ξ - f x) + ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := by
            linarith
      _ = ξ - f x + ⟪x, continuousConvexSelectedSubgradient f hcont hconv s x⟫_ℝ := by
            ring
  exact hineq

end SupportingHalfspace

section Proposition_29_41

variable (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
variable (hconv : _root_.ConvexOn ℝ Set.univ f)
variable (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
variable (s : Selection (∂ f.toEReal))

local notation "C" => lowerLevelSet f.toEReal.asEReal ξ
local notation "G" => continuousConvexSubgradientProjector f ξ hcont hconv hC s
local notation "Hξ" =>
  continuousConvexSubgradientProjectorSupportingHalfspace f ξ hcont hconv s

/-
The Chebyshev proof genuinely uses the nonemptiness hypothesis `hC` to rule out the empty
degenerate halfspace when the selected subgradient vanishes.
-/
include hC in
/-- The supporting halfspace from `(29.70)` is a Chebyshev set. -/
theorem continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
    (x : H) :
    IsChebyshev (Hξ x) := by
  let u := continuousConvexSelectedSubgradient f hcont hconv s x
  by_cases hu : u = 0
  · have hfx : f x ≤ ξ := by
      by_contra hfx
      exact
        (selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
          f ξ hcont hconv hC s (lt_of_not_ge hfx)) hu
    have hη : 0 ≤ ξ - f x + ⟪x, u⟫_ℝ := by
      simp [u, hu, hfx]
    -- In the degenerate branch, the supporting halfspace is the whole space.
    simpa [continuousConvexSubgradientProjectorSupportingHalfspace, u, hu] using
      innerProductClosedSublevelSet_isChebyshev_of_eq_zero_of_nonneg hu hη
  · -- In the nondegenerate branch, Example 29.20 gives Chebyshevness directly.
    simpa [continuousConvexSubgradientProjectorSupportingHalfspace, u] using
      innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu

/-- Part (1) of Proposition 29.41: the fixed-point set of the subgradient projector associated with
`(f, ξ, s)` is exactly the lower level set `C = lev_{≤ ξ} f`. -/
theorem continuousConvexSubgradientProjector_fixedPoints_eq_lowerLevelSet
    :
    Function.fixedPoints G = C := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_fixedPoints_iff] at hx
    by_cases hxC : x ∈ C
    · exact hxC
    have hxlt : ξ < f x := by
      have hnot : ¬ f x ≤ ξ := by
        intro hfx
        apply hxC
        exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).2 <| by
          simpa [Function.toEReal_apply] using hfx
      exact lt_of_not_ge hnot
    let u := continuousConvexSelectedSubgradient f hcont hconv s x
    have hu_ne : u ≠ 0 := by
      exact
        selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
          f ξ hcont hconv hC s hxlt
    have hfix :
        x + (((ξ - f x) / (‖u‖ ^ 2)) • u) = x := by
      have hx' : G x = x := hx
      rw [continuousConvexSubgradientProjector_apply_of_lt f ξ hcont hconv hC s hxlt] at hx'
      simpa [u] using hx'
    have hsmul :
        (((ξ - f x) / (‖u‖ ^ 2)) • u) = 0 := by
      calc
        (((ξ - f x) / (‖u‖ ^ 2)) • u)
            = (x + (((ξ - f x) / (‖u‖ ^ 2)) • u)) - x := by
                abel_nf
        _ = x - x := by rw [hfix]
        _ = 0 := by simp
    have hfalse : False := by
      rcases smul_eq_zero.mp hsmul with hscalar | hu0
      · have hnum_ne : ξ - f x ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxlt)
        have hden_ne : ‖u‖ ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu_ne)
        rcases div_eq_zero_iff.mp hscalar with hnum0 | hden0
        · exact hnum_ne hnum0
        · exact hden_ne hden0
      · exact hu_ne hu0
    exact False.elim hfalse
  · intro hx
    rw [Function.mem_fixedPoints_iff]
    -- Points in the lower level set lie on the inactive branch of the projector.
    exact continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hx

/-- Part (3) of Proposition 29.41: evaluating the subgradient projector at `x` gives the metric
projection of `x` onto the supporting halfspace `(29.70)`. -/
theorem continuousConvexSubgradientProjector_eq_projectionPoint_supportingHalfspace
    (x : H) :
    G x = P[Hξ x, continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
      f ξ hcont hconv hC s x] x := by
  by_cases hxC : x ∈ C
  · have hxH : x ∈ Hξ x :=
      lowerLevelSet_subset_continuousConvexSubgradientProjectorSupportingHalfspace
        f ξ hcont hconv s x hxC
    have hbest : IsBestApproximation x (Hξ x) x := by
      -- In the feasible branch, `x` already lies in the halfspace, so it is its own projection.
      refine ⟨hxH, ?_⟩
      simpa using (Metric.infDist_zero_of_mem hxH).symm
    have hproj :
        P[Hξ x, continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
          f ξ hcont hconv hC s x] x = x := by
      exact
        (eq_projectionPoint_of_isBestApproximation
          (Hξ x)
          (continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
            f ξ hcont hconv hC s x)
          hbest).symm
    -- Both maps fix feasible points.
    rw [continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hxC, hproj]
  · have hxlt : ξ < f x := by
      have hnot : ¬ f x ≤ ξ := by
        intro hfx
        apply hxC
        exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).2 <| by
          simpa [Function.toEReal_apply] using hfx
      exact lt_of_not_ge hnot
    let u := continuousConvexSelectedSubgradient f hcont hconv s x
    have hu_ne : u ≠ 0 := by
      exact
        selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
          f ξ hcont hconv hC s hxlt
    have hnot_feasible :
        ¬ ⟪x, u⟫_ℝ ≤ ξ - f x + ⟪x, u⟫_ℝ := by
      linarith
    -- In the active branch, both formulas reduce to the same explicit halfspace correction.
    calc
      G x = x + (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
        simpa [u] using
          (continuousConvexSubgradientProjector_apply_of_lt
            f ξ hcont hconv hC s hxlt)
      _ =
          P[Hξ x, continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
            f ξ hcont hconv hC s x] x := by
          symm
          simpa [continuousConvexSubgradientProjectorSupportingHalfspace, u, hnot_feasible] using
            (projectionPoint_innerProductClosedSublevelSet_eq_piecewise_of_ne_zero
              (u := u) (η := ξ - f x + ⟪x, u⟫_ℝ) hu_ne x)

/-- Part (4) of Proposition 29.41: the subgradient projector associated with `(f, ξ, s)` is firmly
quasinonexpansive. -/
theorem firmlyQuasinonexpansive_continuousConvexSubgradientProjector
    :
    FirmlyQuasinonexpansive G := by
  rw [firmlyQuasinonexpansive_iff]
  intro x y hy
  have hyC : y ∈ C := by
    rw [← continuousConvexSubgradientProjector_fixedPoints_eq_lowerLevelSet f ξ hcont hconv hC s]
    rw [Function.mem_fixedPoints_iff]
    exact hy
  have hyH : y ∈ Hξ x :=
    lowerLevelSet_subset_continuousConvexSubgradientProjectorSupportingHalfspace
      f ξ hcont hconv s x hyC
  let u := continuousConvexSelectedSubgradient f hcont hconv s x
  have hH_convex : Convex ℝ (Hξ x) := by
    -- Convexity comes from the linear preimage of the real ray `(-∞, η]`.
    simpa [continuousConvexSubgradientProjectorSupportingHalfspace, u,
      innerProductClosedSublevelSet, innerSLFlip_apply_apply] using
      (convex_Iic (ξ - f x + ⟪x, u⟫_ℝ)).linear_preimage
        (innerSLFlip ℝ u).toLinearMap
  have hproj :
      G x ∈ Hξ x ∧ ∀ z ∈ Hξ x, ⟪z - G x, x - G x⟫_ℝ ≤ 0 := by
    -- The projection characterization packages both membership and the variational inequality.
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (continuousConvexSubgradientProjectorSupportingHalfspace_isChebyshev
          f ξ hcont hconv hC s x)
        hH_convex).1 <|
        continuousConvexSubgradientProjector_eq_projectionPoint_supportingHalfspace
          f ξ hcont hconv hC s x
  have hinner : ⟪y - G x, x - G x⟫_ℝ ≤ 0 := hproj.2 y hyH
  have hcross : 0 ≤ 2 * ⟪x - G x, G x - y⟫_ℝ := by
    have hrewrite : ⟪x - G x, G x - y⟫_ℝ = -⟪y - G x, x - G x⟫_ℝ := by
      calc
        ⟪x - G x, G x - y⟫_ℝ = ⟪x - G x, -(y - G x)⟫_ℝ := by
          simp
        _ = -⟪x - G x, y - G x⟫_ℝ := by
          rw [inner_neg_right]
        _ = -⟪y - G x, x - G x⟫_ℝ := by
          rw [real_inner_comm]
    linarith [hinner, hrewrite]
  have hnorm :
      ‖x - y‖ ^ 2 =
        ‖x - G x‖ ^ 2 + 2 * ⟪x - G x, G x - y⟫_ℝ + ‖G x - y‖ ^ 2 := by
    -- Expand the Pythagorean decomposition around the projection point `G x`.
    have hdecomp : x - y = (x - G x) + (G x - y) := by
      abel_nf
    calc
      ‖x - y‖ ^ 2 = ‖(x - G x) + (G x - y)‖ ^ 2 := by rw [hdecomp]
      _ = ‖x - G x‖ ^ 2 + 2 * ⟪x - G x, G x - y⟫_ℝ + ‖G x - y‖ ^ 2 := by
            simpa using norm_add_sq_real (x - G x) (G x - y)
  have hdisp : ‖x - G x‖ ^ 2 = ‖G x - x‖ ^ 2 := by
    rw [norm_sub_rev]
  nlinarith [hnorm, hcross, hdisp]

/-- Part (5) of Proposition 29.41: the excess value `max {f(x) - ξ, 0}` is the
product of the norm of the selected subgradient at `x` and the displacement of
the subgradient projector. -/
theorem max_sub_eq_norm_selectedSubgradient_mul_norm_residual
    (x : H) :
    max (f x - ξ) 0 =
      ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ *
        ‖G x - x‖ := by
  by_cases hxC : x ∈ C
  · have hfx : f x ≤ ξ := by
      simpa [Function.toEReal_apply] using
        (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).1 hxC
    -- On the lower level set, the projector fixes `x`, so both sides vanish.
    rw [continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hxC]
    simp [hfx]
  · have hxlt : ξ < f x := by
      have hnot : ¬ f x ≤ ξ := by
        intro hfx
        apply hxC
        exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).2 <| by
          simpa [Function.toEReal_apply] using hfx
      exact lt_of_not_ge hnot
    let u := continuousConvexSelectedSubgradient f hcont hconv s x
    have hu_ne : u ≠ 0 := by
      exact
        selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
          f ξ hcont hconv hC s hxlt
    have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu_ne
    have hres :
        G x - x = (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
      calc
        G x - x = (x + (((ξ - f x) / (‖u‖ ^ 2)) • u)) - x := by
          rw [continuousConvexSubgradientProjector_apply_of_lt f ξ hcont hconv hC s hxlt]
        _ = (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
          abel_nf
    have hnorm_res : ‖G x - x‖ = (f x - ξ) / ‖u‖ := by
      have hquot_nonpos : ((ξ - f x) / (‖u‖ ^ 2) : ℝ) ≤ 0 := by
        refine div_nonpos_of_nonpos_of_nonneg ?_ ?_
        · linarith
        · positivity
      calc
        ‖G x - x‖ = ‖(((ξ - f x) / (‖u‖ ^ 2)) • u)‖ := by rw [hres]
        _ = |((ξ - f x) / (‖u‖ ^ 2) : ℝ)| * ‖u‖ := norm_smul _ _
        _ = -((ξ - f x) / (‖u‖ ^ 2)) * ‖u‖ := by
          rw [abs_of_nonpos hquot_nonpos]
        _ = (f x - ξ) / ‖u‖ := by
          field_simp [hu_norm_ne]
          ring
    -- The active-branch displacement has exactly the norm prescribed by the textbook formula.
    calc
      max (f x - ξ) 0 = f x - ξ := by
        apply max_eq_left
        linarith
      _ = ‖u‖ * ‖G x - x‖ := by
        rw [hnorm_res]
        field_simp [hu_norm_ne]
      _ = ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ * ‖G x - x‖ := by
        simp [u]

/-- Helper for Proposition 29.41: on the active branch `ξ < f x`, the residual vector
`x - G x` is the displayed positive scalar multiple of the selected subgradient. -/
lemma sub_subgradientProjector_eq_sub_div_normSq_smul_selectedSubgradient_of_lt
    {x : H} (hx : ξ < f x) :
    x - G x =
      (((f x - ξ) / (‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
        continuousConvexSelectedSubgradient f hcont hconv s x) := by
  let u := continuousConvexSelectedSubgradient f hcont hconv s x
  have hactive :
      G x = x + (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
    -- Start from the active-branch projector formula and freeze the selected subgradient as `u`.
    simpa [u] using
      (continuousConvexSubgradientProjector_apply_of_lt f ξ hcont hconv hC s hx)
  -- Route correction: rewrite `x - G x` once in the source-facing residual orientation, rather
  -- than repeatedly flipping the sign inside clause (6).
  calc
    x - G x = x - (x + (((ξ - f x) / (‖u‖ ^ 2)) • u)) := by rw [hactive]
    _ = -((((ξ - f x) / (‖u‖ ^ 2)) • u)) := by
          abel_nf
    _ = (((f x - ξ) / (‖u‖ ^ 2)) • u) := by
          rw [← neg_smul]
          congr 1
          ring
    _ =
        (((f x - ξ) / (‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
          continuousConvexSelectedSubgradient f hcont hconv s x) := by
            simp [u]

/-- Helper for Proposition 29.41: on the active branch `ξ < f x`, the squared residual norm is
the displayed scalar quotient. -/
lemma normSq_residual_eq_sub_sq_div_normSq_selectedSubgradient_of_lt
    {x : H} (hx : ξ < f x) :
    ‖G x - x‖ ^ 2 =
      (f x - ξ) ^ 2 / (‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2) := by
  let u := continuousConvexSelectedSubgradient f hcont hconv s x
  have hu_ne : u ≠ 0 := by
    exact
      selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
        f ξ hcont hconv hC s hx
  have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu_ne
  have hden_ne : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 hu_norm_ne
  have hres :
      G x - x = (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
    -- Keep the active branch in the `G x - x` orientation for the norm computation.
    calc
      G x - x = (x + (((ξ - f x) / (‖u‖ ^ 2)) • u)) - x := by
        rw [continuousConvexSubgradientProjector_apply_of_lt f ξ hcont hconv hC s hx]
      _ = (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
            abel_nf
  calc
    ‖G x - x‖ ^ 2 = ‖(((ξ - f x) / (‖u‖ ^ 2)) • u)‖ ^ 2 := by rw [hres]
    _ = (|((ξ - f x) / (‖u‖ ^ 2) : ℝ)| ^ 2) * (‖u‖ ^ 2) := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow]
    _ = (((ξ - f x) / (‖u‖ ^ 2)) ^ 2) * (‖u‖ ^ 2) := by
          rw [sq_abs]
    _ = (f x - ξ) ^ 2 / (‖u‖ ^ 2) := by
          field_simp [hden_ne]
          ring
    _ =
        (f x - ξ) ^ 2 / (‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2) := by
            simp [u]

/-- Part (6) of Proposition 29.41: the residual vector of the subgradient
projector is collinear with the selected subgradient at `x` with the displayed
scalar factor. -/
theorem max_sub_smul_residual_eq_norm_sq_smul_selectedSubgradient
    (x : H) :
    max (f x - ξ) 0 • (x - G x) =
      ‖G x - x‖ ^ 2 •
        continuousConvexSelectedSubgradient f hcont hconv s x := by
  by_cases hxC : x ∈ C
  · have hfx : f x ≤ ξ := by
      simpa [Function.toEReal_apply] using
        (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).1 hxC
    -- On the lower level set, the projector fixes `x`, so the vector identity is trivial.
    rw [continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hxC]
    simp [hfx]
  · have hxlt : ξ < f x := by
      have hnot : ¬ f x ≤ ξ := by
        intro hfx
        apply hxC
        exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).2 <| by
          simpa [Function.toEReal_apply] using hfx
      exact lt_of_not_ge hnot
    let u := continuousConvexSelectedSubgradient f hcont hconv s x
    have hres :
        x - G x = (((f x - ξ) / (‖u‖ ^ 2)) • u) := by
      -- Normalize the active branch once before comparing scalar coefficients.
      simpa [u] using
        (sub_subgradientProjector_eq_sub_div_normSq_smul_selectedSubgradient_of_lt
          f ξ hcont hconv hC s hxlt)
    have hnormsq :
        ‖G x - x‖ ^ 2 = (f x - ξ) ^ 2 / (‖u‖ ^ 2) := by
      simpa [u] using
        (normSq_residual_eq_sub_sq_div_normSq_selectedSubgradient_of_lt
          f ξ hcont hconv hC s hxlt)
    have hmax : max (f x - ξ) 0 = f x - ξ := by
      apply max_eq_left
      linarith
    calc
      max (f x - ξ) 0 • (x - G x)
          = max (f x - ξ) 0 • ((((f x - ξ) / (‖u‖ ^ 2)) • u)) := by rw [hres]
      _ = (max (f x - ξ) 0 * ((f x - ξ) / (‖u‖ ^ 2))) • u := by
            rw [smul_smul]
      _ = (((f x - ξ) ^ 2) / (‖u‖ ^ 2)) • u := by
            rw [hmax]
            congr 1
            rw [div_eq_mul_inv, pow_two]
            ring
      _ = ‖G x - x‖ ^ 2 • u := by rw [hnormsq]
      _ = ‖G x - x‖ ^ 2 • continuousConvexSelectedSubgradient f hcont hconv s x := by
            simp [u]

/-- Helper for Proposition 29.41: every point of the lower level set is an ambient continuity
point of the associated continuous-convex subgradient projector. -/
lemma continuousAt_continuousConvexSubgradientProjector_of_mem_lowerLevelSet
    {xbar : H} (hxbar : xbar ∈ C) :
    ContinuousAt G xbar := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro y hy
  have hGxbar : G xbar = xbar := by
    -- The projector fixes every feasible point.
    exact continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hxbar
  have hbound : ‖G y - xbar‖ ≤ 2 * ‖y - xbar‖ := by
    by_cases hyC : y ∈ C
    · have hGy : G y = y := by
        exact continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
          f ξ hcont hconv hC s hyC
      calc
        ‖G y - xbar‖ = ‖y - xbar‖ := by rw [hGy]
        _ ≤ 2 * ‖y - xbar‖ := by
              nlinarith [norm_nonneg (y - xbar)]
    · let u := continuousConvexSelectedSubgradient f hcont hconv s y
      have hylt : ξ < f y := by
        have hnot : ¬ f y ≤ ξ := by
          intro hfy
          apply hyC
          exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ y).2 <| by
            simpa [Function.toEReal_apply] using hfy
        exact lt_of_not_ge hnot
      have hu_mem : u ∈ (∂ f.toEReal) y := by
        exact continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s y
      have hxbar_le : f xbar ≤ ξ := by
        simpa [Function.toEReal_apply] using
          (mem_lowerLevelSet_iff f.toEReal.asEReal ξ xbar).1 hxbar
      have hsub :
          ⟪xbar - y, u⟫_ℝ + f y ≤ f xbar := by
        -- Evaluate the selected-subgradient inequality at the feasible point `xbar`.
        have hsubE :
            (((⟪xbar - y, u⟫_ℝ + f y : ℝ) : EReal) ≤ (f xbar : EReal)) := by
          simpa [u] using
            (mem_subdifferential_iff f.toEReal y u).1 hu_mem xbar
        exact_mod_cast hsubE
      have hu_ne : u ≠ 0 := by
        exact
          selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
            f ξ hcont hconv hC s hylt
      have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.2 hu_ne
      have hscalar :
          f y - ξ ≤ ‖y - xbar‖ * ‖u‖ := by
        have hinner :
            ⟪y - xbar, u⟫_ℝ ≤ ‖y - xbar‖ * ‖u‖ := by
          exact real_inner_le_norm _ _
        have haux : f y - ξ ≤ ⟪y - xbar, u⟫_ℝ := by
          have hsub' : ⟪xbar - y, u⟫_ℝ + f y ≤ ξ := le_trans hsub hxbar_le
          have hrewrite : ⟪xbar - y, u⟫_ℝ = -⟪y - xbar, u⟫_ℝ := by
            calc
              ⟪xbar - y, u⟫_ℝ = ⟪-(y - xbar), u⟫_ℝ := by
                simp
              _ = -⟪y - xbar, u⟫_ℝ := by
                    rw [inner_neg_left]
          calc
            f y - ξ ≤ -⟪xbar - y, u⟫_ℝ := by
              linarith
            _ = ⟪y - xbar, u⟫_ℝ := by
              rw [hrewrite]
              ring
        exact le_trans haux hinner
      have hprod :
          ‖u‖ * ‖G y - y‖ ≤ ‖u‖ * ‖y - xbar‖ := by
        have hmax :
            max (f y - ξ) 0 = f y - ξ := by
          apply max_eq_left
          linarith
        calc
          ‖u‖ * ‖G y - y‖ = f y - ξ := by
            symm
            simpa [u, hmax, mul_comm] using
              (max_sub_eq_norm_selectedSubgradient_mul_norm_residual
                f ξ hcont hconv hC s y)
          _ ≤ ‖y - xbar‖ * ‖u‖ := hscalar
          _ = ‖u‖ * ‖y - xbar‖ := by ring
      have hres_le : ‖G y - y‖ ≤ ‖y - xbar‖ := by
        exact le_of_mul_le_mul_left hprod hu_norm_pos
      have hdecomp : G y - xbar = (G y - y) + (y - xbar) := by
        abel_nf
      calc
        ‖G y - xbar‖ = ‖(G y - y) + (y - xbar)‖ := by rw [hdecomp]
        _ ≤ ‖G y - y‖ + ‖y - xbar‖ := norm_add_le _ _
        _ ≤ ‖y - xbar‖ + ‖y - xbar‖ := by
              linarith
        _ = 2 * ‖y - xbar‖ := by ring
  have hyε : 2 * ‖y - xbar‖ < ε := by
    rw [dist_eq_norm] at hy
    linarith
  -- The uniform local estimate collapses the continuity proof to one metric inequality.
  rw [dist_eq_norm, hGxbar]
  exact lt_of_le_of_lt hbound hyε

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: coercing a convex real-valued function through `toEReal`
preserves convexity on the full effective domain. -/
lemma convexOnToERealOfConvexOnUniv
    (hfconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Function.effectiveDomain_toEReal]
  · simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hfconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * f x + (1 - a) * f y : ℝ) : EReal)
    exact_mod_cast hreal

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: subgradients of `f.toEReal` satisfy the real-valued support
inequality for `f`. -/
lemma subgradientRealInequalityOfMemToERealSubdifferential
    {x u y : H} (hu : u ∈ (∂ f.toEReal) x) :
    inner ℝ (y - x) u + f x ≤ f y := by
  have htest :
      (inner ℝ (y - x) u : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := u)).1 hu y
  exact EReal.coe_le_coe_iff.mp <| by
    simpa [Function.toEReal_apply, EReal.coe_add] using htest

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: the standard buffered test point stays inside the ball with
radius enlarged by one. -/
lemma bufferTestPoint_mem_ball
    {x₀ x u : H} {R : ℝ}
    (hx : x ∈ Metric.ball x₀ R) :
    x + ((‖u‖ + 1 : ℝ)⁻¹) • u ∈ Metric.ball x₀ (R + 1) := by
  let t : ℝ := (‖u‖ + 1)⁻¹
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_mul_lt_one : t * ‖u‖ < 1 := by
    have hden : 0 < ‖u‖ + 1 := by
      positivity
    dsimp [t]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one hden).2 (by linarith [norm_nonneg u])
  have hstep : dist (x + t • u) x = t * ‖u‖ := by
    rw [dist_eq_norm]
    have hsub : x + t • u - x = t • u := by
      abel_nf
    rw [hsub, norm_smul, Real.norm_of_nonneg ht_nonneg]
  rw [Metric.mem_ball] at hx ⊢
  calc
    dist (x + t • u) x₀ ≤ dist (x + t • u) x + dist x x₀ := dist_triangle _ _ _
    _ = t * ‖u‖ + dist x x₀ := by rw [hstep]
    _ < 1 + R := by linarith
    _ = R + 1 := by ring

/-- Helper for Proposition 29.41: the buffered scalar inequality cancels to `a ≤ β`. -/
lemma norm_le_of_invAddOne_mul_sq_le
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hineq : (((a + 1 : ℝ)⁻¹) * a ^ 2) ≤ β * ((((a + 1 : ℝ)⁻¹) * a))) :
    a ≤ β := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hβ
  have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  let c : ℝ := (((a + 1 : ℝ)⁻¹) * a)
  have hc_pos : 0 < c := by
    dsimp [c]
    have hinv_pos : 0 < ((a + 1 : ℝ)⁻¹) := by
      positivity
    exact mul_pos hinv_pos ha_pos
  have hscaled : c * a ≤ c * β := by
    dsimp [c]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hineq
  exact le_of_mul_le_mul_left hscaled hc_pos

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: a subgradient on a ball where `f` is Lipschitz has norm at most
the Lipschitz constant after enlarging the ball by one unit. -/
lemma norm_le_of_memSubdifferential_of_lipschitzOnBufferBall
    {x₀ x u : H} {R : ℝ} {β : NNReal}
    (hx : x ∈ Metric.ball x₀ R)
    (hLip : LipschitzOnWith β f (Metric.ball x₀ (R + 1)))
    (hu : u ∈ (∂ f.toEReal) x) :
    ‖u‖ ≤ β := by
  let t : ℝ := (‖u‖ + 1)⁻¹
  let y : H := x + t • u
  have hy : y ∈ Metric.ball x₀ (R + 1) := by
    simpa [y, t] using bufferTestPoint_mem_ball (x := x) (x₀ := x₀) (u := u) (R := R) hx
  have hx_buffer : x ∈ Metric.ball x₀ (R + 1) := by
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hy_sub : y - x = t • u := by
    dsimp [y]
    abel_nf
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hsubgrad :
      t * ‖u‖ ^ 2 + f x ≤ f y := by
    have htest := subgradientRealInequalityOfMemToERealSubdifferential
      (f := f) (x := x) (u := u) (y := y) hu
    rw [hy_sub, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using htest
  have hdist : dist y x = t * ‖u‖ := by
    rw [dist_eq_norm, hy_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
  have hLip_real :
      f y - f x ≤ β * dist y x := by
    have hdist' : dist (f y) (f x) ≤ β * dist y x := hLip.dist_le_mul y hy x hx_buffer
    have habs : |f y - f x| ≤ β * dist y x := by
      simpa [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg] using hdist'
    exact le_trans (le_abs_self (f y - f x)) habs
  have hscaled :
      t * ‖u‖ ^ 2 ≤ β * (t * ‖u‖) := by
    have hleft : t * ‖u‖ ^ 2 ≤ f y - f x := by
      linarith
    have hright : f y - f x ≤ β * (t * ‖u‖) := by
      simpa [hdist] using hLip_real
    exact le_trans hleft hright
  exact norm_le_of_invAddOne_mul_sq_le
    (a := ‖u‖) (β := β) (norm_nonneg u) β.2 <| by
      simpa [t, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: bounded-set boundedness of a continuous convex real-valued
function yields bounded subdifferential images on bounded sets. -/
lemma subdifferentialImage_bounded_of_boundedOnEveryBoundedSet
    (hconvE : ConvexOn f.toEReal (effectiveDomain f.toEReal))
    (hbounded :
      ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B))
    (B : Set H) (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B) := by
  by_cases hBempty : B.Nonempty
  · rcases hBempty with ⟨x₀, hx₀⟩
    rcases hB.subset_ball x₀ with ⟨R, hR⟩
    have hRpos : 0 < R := by
      simpa [Metric.mem_ball] using hR hx₀
    have hx₀_dom : x₀ ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hball_dom : Metric.ball x₀ (2 * R) ⊆ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hR1pos : 0 < R + 1 := by linarith
    have hball_dom_big : Metric.ball x₀ (2 * (R + 1)) ⊆ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hbig_bounded :
        Bornology.IsBounded
          (((fun y ↦ (f.toEReal y : EReal).toReal) '' Metric.ball x₀ (2 * (R + 1))) : Set ℝ) := by
      simpa [Function.toEReal_apply] using
        hbounded (Metric.ball x₀ (2 * (R + 1))) Metric.isBounded_ball
    let β : NNReal :=
      ⟨Metric.diam
          (((fun z ↦ (f.toEReal z : EReal).toReal) '' Metric.ball x₀ (2 * (R + 1))) : Set ℝ) /
            (R + 1),
        by positivity⟩
    have hLip :
        LipschitzOnWith β f (Metric.ball x₀ (R + 1)) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro x hx y hy
      simpa [β, dist_eq_norm, Real.norm_eq_abs, Function.toEReal_apply] using
        lipschitz_bound_on_ball_of_bounded_image
          (f := f.toEReal) hconvE
          hR1pos hx₀_dom hball_dom_big hbig_bounded hx hy
          (by simp [Function.effectiveDomain_toEReal])
          (by simp [Function.effectiveDomain_toEReal])
    have hsubset :
        SetValuedOperator.image (∂ f.toEReal) B ⊆ Metric.closedBall (0 : H) β := by
      intro u hu
      rcases (SetValuedOperator.mem_image _ _ _).1 hu with ⟨x, hxB, hux⟩
      have hx_ball : x ∈ Metric.ball x₀ R := hR hxB
      have hnorm : ‖u‖ ≤ β :=
        norm_le_of_memSubdifferential_of_lipschitzOnBufferBall
          (f := f) hx_ball hLip hux
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hnorm
    exact Metric.isBounded_closedBall.subset hsubset
  · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
    simp [SetValuedOperator.image, hB']

/-- Helper for Proposition 29.41: a bounded subdifferential image gives a uniform norm bound on
the selected subgradient over the same set. -/
lemma selectedSubgradient_norm_le_of_boundedSubdifferentialImage
    (B : Set H)
    (hBimg : Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B)) :
    ∃ σ : ℝ, 0 ≤ σ ∧
      ∀ {y : H}, y ∈ B →
        ‖continuousConvexSelectedSubgradient f hcont hconv s y‖ ≤ σ := by
  obtain ⟨R, hR⟩ := hBimg.subset_closedBall (0 : H)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro y hy
  have hy_mem :
      continuousConvexSelectedSubgradient f hcont hconv s y ∈
        SetValuedOperator.image (∂ f.toEReal) B := by
    apply (SetValuedOperator.mem_image _ _ _).2
    refine ⟨y, hy, ?_⟩
    exact continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s y
  have hy_ball :
      continuousConvexSelectedSubgradient f hcont hconv s y ∈ Metric.closedBall (0 : H) R :=
    hR hy_mem
  rw [Metric.mem_closedBall, dist_eq_norm] at hy_ball
  have hy_norm : ‖continuousConvexSelectedSubgradient f hcont hconv s y‖ ≤ R := by
    simpa using hy_ball
  exact le_trans hy_norm (le_max_left _ _)

omit [CompleteSpace H] in
/-- Helper for Proposition 29.41: continuous convex real-valued functions are weakly sequentially
lower semicontinuous after coercion to `EReal`. -/
lemma weakSequentialLsc_toEReal_of_continuousConvex
    (hfΓ : f.toEReal ∈ Γ₀(H))
    {xSeq : ℕ → H} {xbar : H}
    (hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (nhds (toWeakSpace ℝ H xbar))) :
    (f xbar : EReal) ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
  have htfae :
      List.TFAE
        [ (∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (nhds (toWeakSpace ℝ H y)) →
                (f y : EReal) ≤ Filter.liminf (fun n ↦ (f (u n) : EReal)) atTop),
          (∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
              Tendsto u atTop (nhds y) →
                (f y : EReal) ≤ Filter.liminf (fun n ↦ (f (u n) : EReal)) atTop),
          LowerSemicontinuous f.toEReal.asEReal,
          WeaklyLowerSemicontinuous f.toEReal.asEReal ] := by
    exact convex_lowerSemicontinuity_tfae (convex_epigraph_asEReal_of_mem_gammaZero hfΓ)
  have hweak_seq :
      ∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
        Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (nhds (toWeakSpace ℝ H y)) →
          (f y : EReal) ≤ Filter.liminf (fun n ↦ (f (u n) : EReal)) atTop := by
    exact (List.TFAE.out htfae 0 2).2 hfΓ.1
  simpa using hweak_seq hweak

/-- Part (7) of Proposition 29.41: if `G xₙ - xₙ → 0` and `xₙ → x̄`
strongly, then `x̄ ∈ C`. -/
theorem mem_lowerLevelSet_of_subgradientProjector_residual_tendsto_zero_of_tendsto
    (xSeq : ℕ → H) (xbar : H)
    (hres : Tendsto (fun n ↦ G (xSeq n) - xSeq n) atTop (nhds 0))
    (hlim : Tendsto xSeq atTop (nhds xbar)) :
    xbar ∈ C := by
  let hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOnToERealOfConvexOnUniv (f := f) hconv
  have hxbar_cont : ContinuousPoint f.toEReal xbar := by
    refine ⟨1, by norm_num, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simpa [Function.toEReal_apply] using (hcont.continuousAt : ContinuousAt f xbar)
  obtain ⟨ρ, hρpos, hnearby_bounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousPoint
      (f := f.toEReal) hconv_toEReal hxbar_cont
  have hball_image_bounded :
      Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) (Metric.ball xbar ρ)) := by
    refine hnearby_bounded.subset ?_
    intro u hu
    rcases (SetValuedOperator.mem_image _ _ _).1 hu with ⟨y, hy, huy⟩
    exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, huy⟩⟩
  obtain ⟨σ, hσ_nonneg, hσ_bound⟩ :=
    selectedSubgradient_norm_le_of_boundedSubdifferentialImage
      (f := f) (hcont := hcont) (hconv := hconv) (s := s)
      (B := Metric.ball xbar ρ) hball_image_bounded
  have hball_eventually : ∀ᶠ n in atTop, xSeq n ∈ Metric.ball xbar ρ := by
    exact hlim.eventually (Metric.ball_mem_nhds xbar hρpos)
  have hineq_eventually :
      ∀ᶠ n in atTop, f (xSeq n) ≤ ξ + σ * ‖G (xSeq n) - xSeq n‖ := by
    filter_upwards [hball_eventually] with n hn
    have hscalar :
        f (xSeq n) - ξ ≤ σ * ‖G (xSeq n) - xSeq n‖ := by
      calc
        f (xSeq n) - ξ
            ≤ max (f (xSeq n) - ξ) 0 := le_max_left _ _
        _ =
            ‖continuousConvexSelectedSubgradient f hcont hconv s (xSeq n)‖ *
              ‖G (xSeq n) - xSeq n‖ := by
                simpa using
                  (max_sub_eq_norm_selectedSubgradient_mul_norm_residual
                    f ξ hcont hconv hC s (xSeq n))
        _ ≤ σ * ‖G (xSeq n) - xSeq n‖ := by
              gcongr
              exact hσ_bound hn
    linarith
  have hf_tendsto :
      Tendsto (fun n ↦ f (xSeq n)) atTop (nhds (f xbar)) := by
    exact (hcont.continuousAt : ContinuousAt f xbar).tendsto.comp hlim
  have hres_norm_tendsto :
      Tendsto (fun n ↦ ‖G (xSeq n) - xSeq n‖) atTop (nhds 0) := by
    simpa using hres.norm
  have hright_tendsto :
      Tendsto (fun n ↦ ξ + σ * ‖G (xSeq n) - xSeq n‖) atTop (nhds ξ) := by
    have hmul :
        Tendsto (fun n ↦ σ * ‖G (xSeq n) - xSeq n‖) atTop (nhds (σ * 0)) := by
      exact tendsto_const_nhds.mul hres_norm_tendsto
    simpa using tendsto_const_nhds.add hmul
  have hfxbar_le : f xbar ≤ ξ :=
    le_of_tendsto_of_tendsto hf_tendsto hright_tendsto hineq_eventually
  exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ xbar).2 <| by
    simpa [Function.toEReal_apply] using hfxbar_le

/-- Part (8) of Proposition 29.41: if `G xₙ - xₙ → 0`, if `xₙ ⇀ x̄`,
and if `f` is bounded on every bounded subset of `H`, then `x̄ ∈ C`. -/
theorem mem_lowerLevelSet_of_subgradientProjector_residual_tendsto_zero_of_tendsto_weakly
    (hbounded :
      ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B))
    (xSeq : ℕ → H) (xbar : H)
    (hres : Tendsto (fun n ↦ G (xSeq n) - xSeq n) atTop (nhds 0))
    (hlim :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (nhds (toWeakSpace ℝ H xbar))) :
    xbar ∈ C := by
  let hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOnToERealOfConvexOnUniv (f := f) hconv
  let hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have hxSeq_bounded : Bornology.IsBounded (Set.range xSeq) :=
    bounded_range_of_tendsto_weakly hlim
  have himage_bounded :
      Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) (Set.range xSeq)) :=
    subdifferentialImage_bounded_of_boundedOnEveryBoundedSet
      (f := f) hconv_toEReal hbounded (Set.range xSeq) hxSeq_bounded
  obtain ⟨σ, hσ_nonneg, hσ_bound⟩ :=
    selectedSubgradient_norm_le_of_boundedSubdifferentialImage
      (f := f) (hcont := hcont) (hconv := hconv) (s := s)
      (B := Set.range xSeq) himage_bounded
  have hineq :
      ∀ n : ℕ, f (xSeq n) ≤ ξ + σ * ‖G (xSeq n) - xSeq n‖ := by
    intro n
    have hscalar :
        f (xSeq n) - ξ ≤ σ * ‖G (xSeq n) - xSeq n‖ := by
      calc
        f (xSeq n) - ξ
            ≤ max (f (xSeq n) - ξ) 0 := le_max_left _ _
        _ =
            ‖continuousConvexSelectedSubgradient f hcont hconv s (xSeq n)‖ *
              ‖G (xSeq n) - xSeq n‖ := by
                simpa using
                  (max_sub_eq_norm_selectedSubgradient_mul_norm_residual
                    f ξ hcont hconv hC s (xSeq n))
        _ ≤ σ * ‖G (xSeq n) - xSeq n‖ := by
              gcongr
              exact hσ_bound (Set.mem_range_self n)
    linarith
  have hres_norm_tendsto :
      Tendsto (fun n ↦ ‖G (xSeq n) - xSeq n‖) atTop (nhds 0) := by
    simpa using hres.norm
  have hbound_tendsto :
      Tendsto (fun n ↦ ((ξ + σ * ‖G (xSeq n) - xSeq n‖ : ℝ) : EReal)) atTop (nhds (ξ : EReal)) := by
    have hreal :
        Tendsto (fun n ↦ ξ + σ * ‖G (xSeq n) - xSeq n‖) atTop (nhds ξ) := by
      have hmul :
          Tendsto (fun n ↦ σ * ‖G (xSeq n) - xSeq n‖) atTop (nhds (σ * 0)) := by
        exact tendsto_const_nhds.mul hres_norm_tendsto
      simpa using tendsto_const_nhds.add hmul
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hliminf_le :
      Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop ≤
        Filter.liminf (fun n ↦ ((ξ + σ * ‖G (xSeq n) - xSeq n‖ : ℝ) : EReal)) atTop := by
    exact Filter.liminf_le_liminf (Eventually.of_forall fun n ↦ by exact_mod_cast hineq n)
  have hfxbar_le :
      (f xbar : EReal) ≤ (ξ : EReal) := by
    calc
      (f xbar : EReal)
          ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop :=
            weakSequentialLsc_toEReal_of_continuousConvex
              (f := f) hfΓ hlim
      _ ≤ Filter.liminf (fun n ↦ ((ξ + σ * ‖G (xSeq n) - xSeq n‖ : ℝ) : EReal)) atTop :=
            hliminf_le
      _ = (ξ : EReal) := hbound_tendsto.liminf_eq
  have hfxbar_le_real : f xbar ≤ ξ := by
    exact_mod_cast hfxbar_le
  exact (mem_lowerLevelSet_iff f.toEReal.asEReal ξ xbar).2 <| by
    simpa [Function.toEReal_apply] using hfxbar_le_real

/-- Part (9) of Proposition 29.41: if `f` is bounded on every bounded subset of
`H`, then the residual map `Id - G` is demiclosed at `0`. -/
theorem demiclosedAt_zero_id_sub_continuousConvexSubgradientProjector
    (hbounded :
      ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B)) :
    DemiclosedAt (Set.univ : Set H)
      (fun x : Set.univ ↦ (x : H) - G x)
      0 := by
  intro xSeq x hweak hres
  have hres' :
      Tendsto (fun n ↦ G (xSeq n : H) - (xSeq n : H)) atTop (nhds 0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hres.neg
  have hxC :
      (x : H) ∈ C :=
    mem_lowerLevelSet_of_subgradientProjector_residual_tendsto_zero_of_tendsto_weakly
      f ξ hcont hconv hC s hbounded
      (fun n ↦ (xSeq n : H)) (x : H) hres' (by simpa using hweak)
  have hfix : G (x : H) = (x : H) :=
    continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hxC
  simp [hfix]

/-- Part (10) of Proposition 29.41: the subgradient projector associated with
`(f, ξ, s)` is continuous on the lower level set `C = lev_{≤ ξ} f`. -/
theorem continuousOn_continuousConvexSubgradientProjector_lowerLevelSet
    :
    ContinuousOn G C := by
  intro x hx
  -- The boundary estimate upgrades to ambient continuity, hence also to continuity within `C`.
  exact
    (continuousAt_continuousConvexSubgradientProjector_of_mem_lowerLevelSet
      f ξ hcont hconv hC s hx).continuousWithinAt

/-- Helper for Proposition 29.41: differentiability on the active set `ξ < f`
yields the canonical Gâteaux derivative field built from `gradientWithin`. -/
lemma hasGateauxDerivativeOn_toDual_gradientWithin_activeSet_of_differentiableOn
    (hcont : Continuous f)
    (hdiff : DifferentiableOn ℝ f {x | ξ < f x}) :
    HasGateauxDerivativeOn
      (fun x ↦ (f x : EReal).toReal)
      (fun x ↦ InnerProductSpace.toDualMap ℝ H (gradientWithin f {x | ξ < f x} x))
      {x | ξ < f x} := by
  intro x hx
  have hx_nhds : {x | ξ < f x} ∈ 𝓝 x := by
    -- The active set is open because `f` is continuous.
    exact (isOpen_lt continuous_const hcont).mem_nhds hx
  -- On the open active set, `gradientWithin` is the genuine Gâteaux derivative field.
  simpa [Function.toEReal_apply] using
    ((hdiff x hx).hasGradientWithinAt.hasFDerivWithinAt.hasGateauxDerivativeWithinAt hx_nhds :
      HasGateauxDerivativeWithinAt
        f
        (InnerProductSpace.toDualMap ℝ H (gradientWithin f {x | ξ < f x} x))
        {x | ξ < f x}
        x)

/-- Helper for Proposition 29.41: on the active set `ξ < f`, the canonical gradient field is
nonzero because it matches the selected subgradient. -/
lemma gradientWithin_ne_zero_onActive
    (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal))
    (hdiff : DifferentiableOn ℝ f {x | ξ < f x}) {x : H}
    (hx : ξ < f x) :
    gradientWithin f {x | ξ < f x} x ≠ 0 := by
  have hgrad :
      HasGateauxDerivativeOn
        (fun y ↦ (f y : EReal).toReal)
        (fun y ↦ InnerProductSpace.toDualMap ℝ H (gradientWithin f {x | ξ < f x} y))
        {x | ξ < f x} := by
    simpa using
      (hasGateauxDerivativeOn_toDual_gradientWithin_activeSet_of_differentiableOn
        (f := f) (ξ := ξ) hcont hdiff)
  have hselected_ne :
      continuousConvexSelectedSubgradient f hcont hconv s x ≠ 0 :=
    selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
      f ξ hcont hconv hC s hx
  -- Rewrite the selected subgradient through the active-set gradient formula.
  rw [selectedSubgradient_eq_gradientOnActive
    f ξ hcont hconv s
    (fun y ↦ gradientWithin f {x | ξ < f x} y)
    hgrad hx] at hselected_ne
  simpa using hselected_ne

/-- Helper for Proposition 29.41: on an open set `D` contained in `effectiveDomain f`, a
prescribed Gâteaux gradient field is continuous within `D` at every point where the finite-valued
representative of `f` is Fréchet differentiable. -/
lemma continuousWithinAt_gradientField_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn
        (fun y ↦ (f y : EReal).toReal)
        (fun y ↦ InnerProductSpace.toDualMap ℝ H (gradf y))
        D)
    {x : H} (hx : x ∈ D)
    (hdiff : DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x) :
    ContinuousWithinAt gradf D x := by
  have hx_int : x ∈ interior (effectiveDomain f) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hD_open.mem_nhds hx) hD_dom
  let g : H → ℝ := fun y ↦ (f y : EReal).toReal
  have hgrad_u : HasGradientAt g (gradient g x) x := by
    simpa [g] using hdiff.hasGradientAt
  have hu_single : (∂ f) x = ({gradient g x} : Set H) := by
    exact
      subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
        (f := f) hf (x := x) (g := gradient g x) hx_int <| by
          simpa [g] using hgrad_u.hasFDerivAt.hasGateauxDerivativeAt
  have hgradx_sub : gradf x ∈ (∂ f) x := by
    have hgradAt :
        HasGateauxDerivativeAt
          (fun y ↦ (f y : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ H (gradf x))
          x := by
      exact hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgrad x hx)
    have hsub :
        (∂ f) x = ({gradf x} : Set H) := by
      exact
        subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
          (f := f) hf (x := x) (g := gradf x) hx_int hgradAt
    simp [hsub]
  have hu_eq : gradf x = gradient g x := by
    have : gradf x ∈ ({gradient g x} : Set H) := by
      simpa [hu_single] using hgradx_sub
    simpa using this
  obtain ⟨ρ, hρpos, M, hMpos, hMbound⟩ :=
    subgradient_norm_bound_on_small_ball_of_mem_interior_effectiveDomain hf hx_int
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hx) with ⟨σ, hσpos, hσD⟩
  rw [continuousWithinAt_iff_continuousAt_restrict gradf hx]
  rw [Metric.continuousAt_iff]
  intro ε hε
  let B : ℝ := max 1 (M + ‖gradient g x‖)
  have hBpos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let κ : ℝ := ε ^ 2 / (8 * B)
  have hκpos : 0 < κ := by
    dsimp [κ]
    positivity
  obtain ⟨η, hηpos, hηbound⟩ :=
    frechet_remainder_bound_on_ball
      (f := f) (x := x) (u := gradient g x)
      (by simpa [g] using hgrad_u) κ hκpos
  let δ : ℝ := min (ρ / 2) (min (η / 4) (σ / 4))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le_rho2 : δ ≤ ρ / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_eta4 : δ ≤ η / 4 := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_lt_rho : δ < ρ := by
    linarith
  have htwoδ_lt_eta : 2 * δ < η := by
    linarith
  have htwoδ_lt_sigma : 2 * δ < σ := by
    have hδ_le_sigma4 : δ ≤ σ / 4 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  have hy_ball : (y : H) ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hy
  have hy_rho : (y : H) ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball] at hy_ball ⊢
    exact lt_of_lt_of_le hy_ball hδ_lt_rho.le
  have hv_sub : gradf y ∈ (∂ f) (y : H) := by
    have hyD : (y : H) ∈ D := y.2
    have hy_int : (y : H) ∈ interior (effectiveDomain f) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hD_open.mem_nhds hyD) hD_dom
    have hgradAt :
        HasGateauxDerivativeAt
          (fun z ↦ (f z : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ H (gradf y))
          y := by
      exact hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgrad y hyD)
    have hsub :
        (∂ f) (y : H) = ({gradf y} : Set H) := by
      exact
        subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
          (f := f) hf (x := y) (g := gradf y) hy_int hgradAt
    simp [hsub]
  have hv_norm : ‖gradf y‖ ≤ M := hMbound _ hy_rho _ hv_sub
  have hvu_norm : ‖gradf y - gradient g x‖ ≤ B := by
    calc
      ‖gradf y - gradient g x‖ ≤ ‖gradf y‖ + ‖gradient g x‖ := norm_sub_le _ _
      _ ≤ M + ‖gradient g x‖ := by
            gcongr
      _ ≤ B := by
            dsimp [B]
            exact le_max_right _ _
  let zPoint : H := (y : H) + (δ / B) • (gradf y - gradient g x)
  have hz_dist : dist zPoint x ≤ 2 * δ := by
    simpa [zPoint] using
      step_point_dist_le_two_mul_delta_of_norm_sub_le hy_ball hBpos hvu_norm
  have hz_eta : zPoint ∈ Metric.ball x η := by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hz_dist htwoδ_lt_eta
  have hz_sigma : zPoint ∈ Metric.ball x σ := by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hz_dist htwoδ_lt_sigma
  have hz_dom : zPoint ∈ effectiveDomain f := hD_dom (hσD hz_sigma)
  have hy_dom : (y : H) ∈ effectiveDomain f := hD_dom y.2
  let R : H → ℝ := fun z ↦
    (f z : EReal).toReal - (f x : EReal).toReal - ⟪gradient g x, z - x⟫_ℝ
  have hy_nonneg : 0 ≤ R y := by
    have hu_mem_sub : gradient g x ∈ (∂ f) x := by
      simp [hu_single]
    simpa [R] using
      (remainder_norm_le_norm_mul_of_two_subgradients
        (x := x) (y := (y : H)) (u := gradient g x) (v := gradf y)
        (hD_dom hx) hy_dom hu_mem_sub hv_sub).1
  have hstep :
      (δ / B) * ‖gradf y - gradient g x‖ ^ 2 ≤ R zPoint - R y := by
    simpa [R, zPoint] using
      remainder_gap_lower_bound_of_mem_subdifferential_step
        (x := x) (y := (y : H)) (u := gradient g x) (v := gradf y) (t := δ / B) hy_dom hz_dom hv_sub
  have hz_remainder : R zPoint ≤ κ * ‖zPoint - x‖ := by
    have hz_norm : ‖R zPoint‖ ≤ κ * ‖zPoint - x‖ := by
      simpa [R] using hηbound zPoint hz_eta
    exact le_trans (le_abs_self _) hz_norm
  have hmain : (δ / B) * ‖gradf y - gradient g x‖ ^ 2 ≤ κ * ‖zPoint - x‖ := by
    exact le_trans (le_trans hstep (sub_le_self _ hy_nonneg)) hz_remainder
  have hδ_div_B_pos : 0 < δ / B := div_pos hδpos hBpos
  have hdiv :
      ‖gradf y - gradient g x‖ ^ 2 ≤ (κ * ‖zPoint - x‖) / (δ / B) := by
    have hmain' : ‖gradf y - gradient g x‖ ^ 2 * (δ / B) ≤ κ * ‖zPoint - x‖ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    exact (le_div_iff₀ hδ_div_B_pos).2 hmain'
  have hnorm_sq : ‖gradf y - gradient g x‖ ^ 2 ≤ ε ^ 2 / 4 := by
    have hz_small : κ * ‖zPoint - x‖ ≤ κ * (2 * δ) := by
      have hz_dist' : ‖zPoint - x‖ ≤ 2 * δ := by
        simpa [dist_eq_norm] using hz_dist
      exact mul_le_mul_of_nonneg_left hz_dist' (le_of_lt hκpos)
    have hdiv' :
        ‖gradf y - gradient g x‖ ^ 2 ≤ (κ * (2 * δ)) / (δ / B) := by
      exact le_trans hdiv <| by
        exact (div_le_div_of_nonneg_right hz_small (le_of_lt hδ_div_B_pos))
    have hrewrite : (κ * (2 * δ)) / (δ / B) = 2 * κ * B := by
      field_simp [hδpos.ne', hBpos.ne']
    have hκ_eval : 2 * κ * B = ε ^ 2 / 4 := by
      dsimp [κ]
      field_simp [hBpos.ne']
      norm_num
    calc
      ‖gradf y - gradient g x‖ ^ 2 ≤ (κ * (2 * δ)) / (δ / B) := hdiv'
      _ = 2 * κ * B := hrewrite
      _ = ε ^ 2 / 4 := hκ_eval
  have hnorm_half : ‖gradf y - gradient g x‖ ≤ ε / 2 := by
    nlinarith [sq_nonneg ‖gradf y - gradient g x‖, hnorm_sq]
  have hnorm_lt : ‖gradf y - gradient g x‖ < ε := by
    linarith
  simpa [Metric.mem_ball, dist_eq_norm, hu_eq] using hnorm_lt

/-- Helper for Proposition 29.41: if `f` is differentiable on the active set `Cᶜ`, then the
subgradient projector is continuous there. -/
lemma continuousOn_continuousConvexSubgradientProjector_compl_lowerLevelSet_of_differentiableOn
    (hdiff : DifferentiableOn ℝ f Cᶜ) :
    ContinuousOn G Cᶜ := by
  let D : Set H := {x | ξ < f x}
  have hCcompl_eq_D : Cᶜ = D := by
    ext x
    simp [D, mem_lowerLevelSet_iff, Function.toEReal_apply, not_le]
  have hDopen : IsOpen D := by
    -- The active set is the strict superlevel set of the continuous function `f`.
    exact isOpen_lt continuous_const hcont
  have hDdom : D ⊆ effectiveDomain f.toEReal := by
    intro x hx
    simp [Function.effectiveDomain_toEReal]
  have hdiffD : DifferentiableOn ℝ f D := by
    simpa [hCcompl_eq_D] using hdiff
  have hgrad :
      HasGateauxDerivativeOn
        (fun y ↦ (f y : EReal).toReal)
        (fun y ↦ InnerProductSpace.toDualMap ℝ H (gradientWithin f D y))
        D := by
    simpa [D] using
      (hasGateauxDerivativeOn_toDual_gradientWithin_activeSet_of_differentiableOn
        (f := f) (ξ := ξ) hcont hdiffD)
  let hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  intro x hx
  have hxD : x ∈ D := by
    simpa [hCcompl_eq_D] using hx
  have hdiffAt : DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
    -- Openness upgrades differentiability within `D` to ambient differentiability at `x`.
    simpa [Function.toEReal_apply] using
      ((hdiffD x hxD).differentiableAt (hDopen.mem_nhds hxD))
  have hgradWithin :
      ContinuousWithinAt (fun y ↦ gradientWithin f D y) D x := by
    -- Route correction: use the pointwise continuity criterion on the open active set instead of
    -- trying to globalize continuity of the gradient field first.
    exact
      continuousWithinAt_gradientField_of_mem_gammaZero_of_hasGateauxDerivativeOn
        (hf := hfΓ) hDopen hDdom (fun y ↦ gradientWithin f D y) hgrad hxD hdiffAt
  have hgradAt : ContinuousAt (fun y ↦ gradientWithin f D y) x := by
    exact hgradWithin.continuousAt (hDopen.mem_nhds hxD)
  have hden_ne : ‖gradientWithin f D x‖ ^ 2 ≠ 0 := by
    have hgrad_ne : gradientWithin f D x ≠ 0 := by
      simpa [D] using
        (gradientWithin_ne_zero_onActive
          (f := f) (ξ := ξ) hcont hconv hC s
          hdiffD hxD)
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hgrad_ne)
  let F : H → H :=
    fun y ↦ y + (((ξ - f y) / (‖gradientWithin f D y‖ ^ 2)) • gradientWithin f D y)
  have hF_eq_G : ∀ y ∈ D, F y = G y := by
    intro y hy
    -- On the active set, the projector is exactly the explicit gradient branch formula.
    symm
    simpa [F] using
      (continuousConvexSubgradientProjector_apply_of_lt_of_hasGateauxDerivativeOn
        f ξ hcont hconv hC s
        (fun z ↦ gradientWithin f D z)
        (by simpa using hgrad)
        hy)
  have hF_contAt : ContinuousAt F x := by
    -- The explicit active formula is continuous because its denominator stays away from zero.
    dsimp [F]
    have hscalarAt :
        ContinuousAt (fun y ↦ (ξ - f y) / (‖gradientWithin f D y‖ ^ 2)) x := by
      refine ContinuousAt.div ?_ ?_ hden_ne
      · exact continuousAt_const.sub (hcont.continuousAt : ContinuousAt f x)
      · exact (hgradAt.norm).pow 2
    refine continuousAt_id.add ?_
    exact hscalarAt.smul hgradAt
  have hG_contWithin_D : ContinuousWithinAt G D x := by
    exact hF_contAt.continuousWithinAt.congr
      (fun y hy ↦ (hF_eq_G y hy).symm)
      (hF_eq_G x hxD).symm
  simpa [hCcompl_eq_D] using hG_contWithin_D

/-- Proposition 29.41 (11): if `f` is Fréchet differentiable on `H \ C`, then the subgradient
projector associated with `(f, ξ, s)` is continuous on all of `H`. -/
theorem continuous_continuousConvexSubgradientProjector_of_differentiableOn_compl_lowerLevelSet
    (hdiff : DifferentiableOn ℝ f Cᶜ) :
    Continuous G := by
  have hCcompl_open : IsOpen Cᶜ := by
    -- The active set is the strict superlevel set `ξ < f`, hence open.
    rw [show Cᶜ = {x | ξ < f x} by
      ext x
      simp [mem_lowerLevelSet_iff, Function.toEReal_apply, not_le]]
    exact isOpen_lt continuous_const hcont
  have hcontActive :
      ContinuousOn G Cᶜ :=
    continuousOn_continuousConvexSubgradientProjector_compl_lowerLevelSet_of_differentiableOn
      f ξ hcont hconv hC s hdiff
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ C
  · -- Feasible points are handled by the lower-level-set continuity theorem.
    exact
      continuousAt_continuousConvexSubgradientProjector_of_mem_lowerLevelSet
        f ξ hcont hconv hC s hx
  · have hxCcompl : x ∈ Cᶜ := by
      simpa using hx
    -- On the open active set, continuity within `Cᶜ` upgrades to ordinary continuity.
    exact (hcontActive x hxCcompl).continuousAt (hCcompl_open.mem_nhds hxCcompl)

end Proposition_29_41

end

end ERealFunction
