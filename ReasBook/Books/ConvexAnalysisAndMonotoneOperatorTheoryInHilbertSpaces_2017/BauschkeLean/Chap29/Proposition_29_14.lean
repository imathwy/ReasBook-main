import Mathlib.Geometry.Euclidean.Projection
import BauschkeLean.Chap04.Proposition_4_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open EuclideanGeometry
open scoped InnerProductSpace

/- Source/core/bridge triage:
- `source-facing`: Proposition 29.14 studies the projector `P_C` onto a nonempty closed affine
  subspace and the reflector `2P_C - Id`.
- `core/canonical`: the repository owner for `P_C` on closed affine subspaces is `projectionPoint`,
  while mathlib's canonical affine operators are `orthogonalProjection C` and `reflection C`.
- `bridge/view`: Chapter 4 already identifies `projectionPoint` with `orthogonalProjection C`; this
  file keeps the proposition source-facing in terms of `P_C` and keeps a thin source-facing
  reflection bridge in the canonical owner language. -/

section CanonicalCompanions

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
variable {C : AffineSubspace ℝ 𝓗} [Nonempty C] [C.direction.HasOrthogonalProjection]

/-- Companion bridge: the canonical affine reflection across `C` is the source reflector
`2P_C - Id` written using `orthogonalProjection C`. -/
theorem reflection_eq_two_smul_orthogonalProjection_sub (x : 𝓗) :
    reflection C x = (2 : ℝ) • orthogonalProjection C x - x := by
  simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (reflection_apply' C x)

end CanonicalCompanions

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : AffineSubspace ℝ 𝓗}
variable (hC_nonempty : (C : Set 𝓗).Nonempty) (hC_closed : IsClosed (C : Set 𝓗))

local notation "P" =>
  projectionPoint (C : Set 𝓗)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

/-- Part (1) of Proposition 29.14: the ambient projection map onto a nonempty closed affine
subspace is weakly continuous. -/
theorem projectionPoint_weaklyContinuous :
    WeaklyContinuous (fun x : (Set.univ : Set 𝓗) ↦ P x) := by
  exact
    projectionPoint_weaklyContinuous_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed

/-- Part (2) of Proposition 29.14: the projection residual `x - P_C x` is orthogonal to the
direction subspace `C - C`. -/
theorem sub_projectionPoint_mem_direction_orthogonal (x : 𝓗) :
    x - P x ∈ C.directionᗮ := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hEq : x - P x = x -ᵥ (orthogonalProjection C x : C) := by
    simpa [vsub_eq_sub] using congrArg (fun z : 𝓗 ↦ x - z)
      (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed x)
  rw [hEq]
  exact vsub_orthogonalProjection_mem_direction_orthogonal C x

/-- Helper for Proposition 29.14: the difference of two projection residuals remains orthogonal to
the direction subspace of `C`. -/
private lemma residual_difference_mem_direction_orthogonal (x y : 𝓗) :
    (x - P x) - (y - P y) ∈ C.directionᗮ := by
  -- Both residuals already lie in `C.directionᗮ`, and this orthogonal complement is a submodule.
  exact
    Submodule.sub_mem C.directionᗮ
      (sub_projectionPoint_mem_direction_orthogonal hC_nonempty hC_closed x)
      (sub_projectionPoint_mem_direction_orthogonal hC_nonempty hC_closed y)

/-- Helper for Proposition 29.14: the projected difference is orthogonal to the residual
difference. -/
private lemma projection_difference_inner_residual_difference_eq_zero (x y : 𝓗) :
    ⟪P x - P y, (x - P x) - (y - P y)⟫_ℝ = 0 := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hPx : P x ∈ (C : Set 𝓗) := by
    exact
      projectionPoint_mem (C : Set 𝓗)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) x
  have hPy : P y ∈ (C : Set 𝓗) := by
    exact
      projectionPoint_mem (C : Set 𝓗)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) y
  have hdir : P x - P y ∈ C.direction := by
    simpa [vsub_eq_sub] using C.vsub_mem_direction hPx hPy
  -- Convert the affine-subspace geometry into a vanishing inner product in the ambient space.
  exact
    Submodule.inner_right_of_mem_orthogonal hdir
      (residual_difference_mem_direction_orthogonal hC_nonempty hC_closed x y)

/-- Proposition 29.14 (3): the difference `x - y` splits orthogonally into its projected part and
its residual part relative to `C`. -/
theorem norm_sq_sub_eq_add_norm_sq_projection_difference_add_norm_sq_residual_difference
    (x y : 𝓗) :
    ‖x - y‖ ^ (2 : ℕ) =
      ‖P x - P y‖ ^ (2 : ℕ) + ‖(x - P x) - (y - P y)‖ ^ (2 : ℕ) := by
  have hsplit : x - y = (P x - P y) + ((x - P x) - (y - P y)) := by
    -- Rearrange the difference into its projected and residual components.
    abel_nf
  -- Expand the squared norm of the orthogonal sum and kill the mixed term.
  calc
    ‖x - y‖ ^ (2 : ℕ)
        = ‖(P x - P y) + ((x - P x) - (y - P y))‖ ^ (2 : ℕ) := by
            rw [hsplit]
    _ = ‖P x - P y‖ ^ (2 : ℕ) +
          2 * ⟪P x - P y, (x - P x) - (y - P y)⟫_ℝ +
          ‖(x - P x) - (y - P y)‖ ^ (2 : ℕ) := by
            rw [norm_add_sq_real]
    _ = ‖P x - P y‖ ^ (2 : ℕ) + ‖(x - P x) - (y - P y)‖ ^ (2 : ℕ) := by
          rw [projection_difference_inner_residual_difference_eq_zero
            hC_nonempty hC_closed x y]
          ring

/-- Part (4) of Proposition 29.14: the reflector `2P_C - Id` preserves distances. -/
theorem norm_reflector_sub_eq (x y : 𝓗) :
    ‖(((2 : ℝ) • P x - x) - ((2 : ℝ) • P y - y))‖ = ‖x - y‖ := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hx :
      (2 : ℝ) • P x - x = reflection C x := by
    rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed]
    simpa using (reflection_eq_two_smul_orthogonalProjection_sub x).symm
  have hy :
      (2 : ℝ) • P y - y = reflection C y := by
    rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed]
    simpa using (reflection_eq_two_smul_orthogonalProjection_sub y).symm
  calc
    ‖(((2 : ℝ) • P x - x) - ((2 : ℝ) • P y - y))‖ = ‖reflection C x - reflection C y‖ := by
      rw [hx, hy]
    _ = dist (reflection C x) (reflection C y) := by
      rw [dist_eq_norm]
    _ = dist x y := by
      exact (reflection C).dist_map x y
    _ = ‖x - y‖ := by
      exact dist_eq_norm x y

/-- Part (5) of Proposition 29.14: the squared norm of the projected difference is the inner
product of `x - y` with that projected difference. -/
theorem norm_sq_projection_difference_eq_inner_sub_projection_difference
    (x y : 𝓗) :
    ‖P x - P y‖ ^ (2 : ℕ) = ⟪x - y, P x - P y⟫_ℝ := by
  exact
    norm_sq_projectionPoint_sub_eq_inner_sub_projectionPoint_sub_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed x y

/-- Part (6) of Proposition 29.14: the squared norm of the residual difference is the inner
product of `x - y` with that residual difference. -/
theorem norm_sq_residual_difference_eq_inner_sub_residual_difference
    (x y : 𝓗) :
    ‖(x - P x) - (y - P y)‖ ^ (2 : ℕ) =
      ⟪x - y, (x - P x) - (y - P y)⟫_ℝ := by
  let r := (x - P x) - (y - P y)
  have hsplit : x - y = (P x - P y) + r := by
    -- Use the same orthogonal decomposition as in part (iii).
    dsimp [r]
    abel_nf
  -- Expand the first argument of the inner product along the orthogonal splitting.
  calc
    ‖r‖ ^ (2 : ℕ) = ⟪r, r⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
    _ = ⟪P x - P y, r⟫_ℝ + ⟪r, r⟫_ℝ := by
      rw [projection_difference_inner_residual_difference_eq_zero
        hC_nonempty hC_closed x y]
      simp [r]
    _ = ⟪(P x - P y) + r, r⟫_ℝ := by
      rw [inner_add_left]
    _ = ⟪x - y, r⟫_ℝ := by
      rw [hsplit]

/-- Part (7) of Proposition 29.14: for any point `z` of the affine subspace, the squared residual
norm at `x` is the inner product of `x - z` with that residual. -/
theorem norm_sq_sub_projectionPoint_eq_inner_sub_sub_projectionPoint
    (x : 𝓗) (z : C) :
    ‖x - P x‖ ^ (2 : ℕ) = ⟪x - z, x - P x⟫_ℝ := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hPx : P x ∈ (C : Set 𝓗) := by
    exact
      projectionPoint_mem (C : Set 𝓗)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) x
  have hdir : P x - (z : 𝓗) ∈ C.direction := by
    simpa [vsub_eq_sub] using C.vsub_mem_direction hPx z.property
  have horth : ⟪P x - (z : 𝓗), x - P x⟫_ℝ = 0 := by
    exact
      Submodule.inner_right_of_mem_orthogonal hdir
        (sub_projectionPoint_mem_direction_orthogonal hC_nonempty hC_closed x)
  have hsplit : x - (z : 𝓗) = (P x - (z : 𝓗)) + (x - P x) := by
    -- Separate the displacement to `z` into its direction and residual pieces.
    abel_nf
  -- Expand the inner product after the orthogonal decomposition of `x - z`.
  calc
    ‖x - P x‖ ^ (2 : ℕ) = ⟪x - P x, x - P x⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
    _ = ⟪P x - (z : 𝓗), x - P x⟫_ℝ + ⟪x - P x, x - P x⟫_ℝ := by
      rw [horth]
      simp
    _ = ⟪(P x - (z : 𝓗)) + (x - P x), x - P x⟫_ℝ := by
      rw [inner_add_left]
    _ = ⟪x - z, x - P x⟫_ℝ := by
      rw [hsplit]

end

end
