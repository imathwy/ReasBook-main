import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SoftThreshold

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.33 is `source-facing`: the source object is projection onto the closed `ℓ¹` ball,
while the chapter's `core/canonical` owners are the set-valued projection map `Proj[C]` from
Theorem 6.24, the coordinatewise soft-thresholding operator `T_[λ]` from Definition 6.3, the
Euclidean `ℓ¹` owner `l1n[·]` from Example 6.8, and the generic sublevel-set projection bridge
from Theorem 6.30. The correct ambient owner is therefore the intrinsic finite Euclidean product
`EuclideanSpace ℝ ι`, with `ι = Fin n` only as the textbook specialization `ℝ^n`. Primitive
data: the source-facing set `B_{l1n[·]}[0, α]`. Derived API: the identification of `B₁[α]` as
an `ℓ¹` sublevel set, the evaluation of the canonical level-set residual as
`λ ↦ l1n[T_[λ] x] - α`, and the reduction of the active projection branch to the existing proximal
singleton formula from Example 6.8. -/

/-- The closed `ℓ¹` ball `B_{l1n[·]}[0, α]` in a finite Euclidean product, specializing to `ℝ^n`
when `ι = Fin n`. -/
def l1ClosedBall (α : ℝ) : Set E :=
  {x | l1n[x] ≤ α}

/-- Textbook notation for the closed `ℓ¹` ball centered at the origin. -/
notation "B₁[" α "]" => l1ClosedBall α

local notation "F" => fun y : E ↦ ((l1n[y] : ℝ) : EReal)

-- Proof sketch: unfold `l1ClosedBall`; membership is definitionally the inequality
-- `l1n[x] ≤ α`.
/-- A vector belongs to `B_{l1n[·]}[0, α]` exactly when its Euclidean coordinates have `ℓ¹` norm at
most `α`. -/
@[simp] theorem mem_l1ClosedBall_iff (α : ℝ) (x : E) :
    x ∈ B₁[α] ↔ l1n[x] ≤ α :=
  Iff.rfl

-- Proof sketch: unfold `l1ClosedBall`; the sublevel-set condition for the real-valued owner
-- `y ↦ l1n[y]` is definitionally the same inequality `l1n[y] ≤ α`.
/-- The closed `ℓ¹` ball is the `α`-sublevel set of the Euclidean `ℓ¹` norm owner. -/
theorem l1ClosedBall_eq_sublevel_euclidean_l1_norm (α : ℝ) :
    B₁[α] = F ⁻¹' Set.Iic (α : EReal) := by
  ext x
  simp [l1ClosedBall]

-- Proof sketch: the Euclidean `ℓ¹` owner never takes the value `⊥`, is finite at the origin,
-- is lower semicontinuous because it comes from a continuous real-valued norm, and is convex
-- because it is the ambient norm composed with the linear equivalence `WithLp.linearEquiv 1`.
/-- Helper for Example 6.33: the Euclidean `ℓ¹` owner is proper, lower semicontinuous, and
convex. -/
lemma euclidean_l1_owner_proper_closed_convex :
    IsProperExtendedRealFunction F ∧ LowerSemicontinuous F ∧ is_convex_function F := by
  refine ⟨?_, ?_, ?_⟩
  · -- Properness reduces to excluding `⊥` everywhere and exhibiting one finite point.
    refine ⟨?_, ?_⟩
    · intro y
      change (((l1n[y] : ℝ) : EReal)) ≠ ⊥
      simp
    · refine ⟨0, ?_⟩
      change (((l1n[(0 : E)] : ℝ) : EReal)) < ⊤
      simp
  · -- Lower semicontinuity follows from continuity of the real-valued `ℓ¹` norm.
    have hcont : Continuous (fun y : E ↦ l1n[y]) := by
      change Continuous (fun y : E ↦ ‖WithLp.toLp (p := (1 : ENNReal)) y.ofLp‖)
      have hofLp : Continuous (fun y : E ↦ y.ofLp) :=
        PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : ι ↦ ℝ)
      exact continuous_norm.comp
        ((PiLp.continuous_toLp (p := (1 : ENNReal)) (β := fun _ : ι ↦ ℝ)).comp hofLp)
    exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · -- Convexity is inherited from the ambient norm through the linear `toLp` identification.
    have hne_bot : ∀ y ∈ effective_domain F, F y ≠ ⊥ := by
      intro y hy
      change (((l1n[y] : ℝ) : EReal)) ≠ ⊥
      simp
    rw [is_convex_function_iff_convexOn_toReal hne_bot]
    let l1Map : E →ₗ[ℝ] WithLp (1 : ENNReal) (ι → ℝ) :=
      ((WithLp.linearEquiv (p := (1 : ENNReal)) (K := ℝ) (V := ι → ℝ)).symm.toLinearMap).comp
        ((WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := ι → ℝ)).toLinearMap)
    have hconv : ConvexOn ℝ Set.univ (fun y : E ↦ ‖l1Map y‖) := by
      simpa using convexOn_univ_norm.comp_linearMap l1Map
    simpa [l1Map, effective_domain, EuclideanSpace.l1Norm] using hconv

-- Proof sketch: specialize the canonical level-set residual from Theorem 6.30 to the
-- Euclidean `ℓ¹` owner `F`. For a nonnegative multiplier, Example 6.8 identifies the scaled
-- proximal singleton with `T_[λ] x`, so the residual evaluates to `l1n[T_[λ] x] - α`.
/-- Evaluating the canonical level-set residual for the Euclidean `ℓ¹` owner at a nonnegative
multiplier gives the textbook scalar function `l1n[T_[λ] x] - α`. -/
theorem l1ClosedBallProjectionResidual_eq
    (α : ℝ) (x : E) (lam : NNReal) :
    level_set_projection_residual F α x lam =
      ((l1n[T_[(lam : ℝ)] x] - α : ℝ) : EReal) := by
  -- The scaled proximal problem is exactly Example 6.8 with threshold `λ`.
  have hprox : prox[((lam : EReal) • F)] x = {T_[(lam : ℝ)] x} := by
    change prox[(fun y : E ↦ (((lam : ℝ) * l1n[y] : ℝ) : EReal))] x = {T_[(lam : ℝ)] x}
    simpa using
      prox_euclidean_l1_eq_singleton_softThreshold lam.2 x
  -- Singleton collapse turns the generic residual into the source-facing scalar expression.
  calc
    level_set_projection_residual F α x lam = F (T_[(lam : ℝ)] x) - α := by
      have hcollapse :
          sInf (F '' prox[((lam : EReal) • F)] x) - α =
            sInf (F '' {T_[(lam : ℝ)] x}) - α := by
        exact congrArg (fun s : Set E ↦ sInf (F '' s) - α) hprox
      calc
        level_set_projection_residual F α x lam = sInf (F '' {T_[(lam : ℝ)] x}) - α := by
          simpa [level_set_projection_residual] using hcollapse
        _ = F (T_[(lam : ℝ)] x) - α := by
          simp
    _ = ((l1n[T_[(lam : ℝ)] x] - α : ℝ) : EReal) := by
      simp [EReal.coe_sub]

-- Proof sketch: identify the displayed function with the canonical residual by
-- `l1ClosedBallProjectionResidual_eq`, then apply Theorem 6.30(3) to the Euclidean `ℓ¹` owner
-- `F`.
/-- The source-facing residual function `λ ↦ l1n[T_[λ] x] - α` is nonincreasing on the
nonnegative multiplier domain. -/
theorem l1ClosedBallProjectionResidual_antitone
    (α : ℝ) (x : E) :
    Antitone (fun lam : NNReal ↦ l1n[T_[(lam : ℝ)] x] - α) := by
  rcases euclidean_l1_owner_proper_closed_convex (ι := ι) with
    ⟨hf_proper, hf_closed, hf_convex⟩
  intro lam₁ lam₂ hle
  -- The generic residual is antitone on the nonnegative half-line.
  have hantiOn :=
    level_set_projection_residual_antitoneOn_nonneg F α hf_proper hf_closed hf_convex x
  have hlam₁ : (lam₁ : ℝ) ∈ Set.Ici 0 := lam₁.2
  have hlam₂ : (lam₂ : ℝ) ∈ Set.Ici 0 := lam₂.2
  have hle_real : (lam₁ : ℝ) ≤ (lam₂ : ℝ) := hle
  have hanti := hantiOn hlam₁ hlam₂ hle_real
  -- Rewriting both residuals recovers the textbook monotonicity statement.
  rw [l1ClosedBallProjectionResidual_eq α x lam₂, l1ClosedBallProjectionResidual_eq α x lam₁] at hanti
  exact_mod_cast hanti

-- Proof sketch: if `x ∈ B₁[α]`, then `x` is already feasible, so its distance to the closed
-- `ℓ¹` ball is zero and the projection set is the singleton `{x}`.
/-- A point already lying in the closed `ℓ¹` ball projects to itself. -/
theorem projection_mapping_l1ClosedBall_eq_singleton_of_mem
    (α : ℝ) (x : E) (hx : x ∈ B₁[α]) :
    Proj[B₁[α]] x = {x} := by
  -- Feasibility makes `x` itself a projection point because its distance to `x` is zero.
  have hx_proj : x ∈ Proj[B₁[α]] x := by
    rw [mem_projection_mapping_iff]
    refine ⟨hx, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    simp [norm_nonneg]
  have hf_convex := (euclidean_l1_owner_proper_closed_convex (ι := ι)).2.2
  have hne_bot : ∀ y ∈ effective_domain F, F y ≠ ⊥ := by
    intro y hy
    change (((l1n[y] : ℝ) : EReal)) ≠ ⊥
    simp
  have hl1_convex_eff :
      ConvexOn ℝ (effective_domain F) (fun y : E ↦ (F y).toReal) :=
    convexOn_toReal_of_is_convex_function hf_convex hne_bot
  have hl1_convex : ConvexOn ℝ Set.univ (fun y : E ↦ l1n[y]) := by
    simpa [effective_domain] using hl1_convex_eff
  -- The `ℓ¹` ball is the sublevel set of a convex real-valued owner.
  have hball_convex_set : Convex ℝ ({y : E | l1n[y] ≤ α} : Set E) := by
    simpa using hl1_convex.convex_le α
  -- Convexity makes the projection set a singleton once one projection point is known.
  have hx_proj_set : x ∈ Proj[{y : E | l1n[y] ≤ α}] x := by
    simpa [l1ClosedBall] using hx_proj
  have hsubsingleton : (Proj[{y : E | l1n[y] ≤ α}] x).Subsingleton :=
    projection_mapping_subsingleton ({y : E | l1n[y] ≤ α} : Set E) hball_convex_set x
  have hprojection_set : Proj[{y : E | l1n[y] ≤ α}] x = {x} :=
    hsubsingleton.eq_singleton_of_mem hx_proj_set
  simpa [l1ClosedBall] using hprojection_set

-- Proof sketch: rewrite `B₁[α]` as the sublevel set of the Euclidean `ℓ¹` norm via
-- `l1ClosedBall_eq_sublevel_euclidean_l1_norm`. The bridge `l1ClosedBallProjectionResidual_eq`
-- converts the textbook equation `l1n[T_[λ] x] = α` to the canonical residual equation from
-- Theorem 6.30, whose positive-root branch already captures the active-constraint case without a
-- separate hypothesis `x ∉ B₁[α]`. In the only feasible-edge case compatible with the displayed
-- root condition, namely `x = 0` and `α = 0`, one has `T_[λ] x = x`, so
-- `projection_mapping_l1ClosedBall_eq_singleton_of_mem` gives the same singleton. Example 6.8
-- then identifies the proximal singleton in the active branch with `T_[λ] x`.
/-- Example 6.33: let `C = B_{l1n[·]}[0, α] = {x | l1n[x] ≤ α}` in a finite Euclidean product,
specializing to `ℝ^n` when `ι = Fin n`. If a positive multiplier `λ` satisfies the textbook
active-constraint equation `l1n[T_[λ] x] = α`, then the set-valued projection onto `C` is the
singleton `{T_[λ] x}`. The root condition already forces the active branch except in the
degenerate feasible case `x = 0`, `α = 0`, where the same conclusion holds by
`projection_mapping_l1ClosedBall_eq_singleton_of_mem`. Together with
`projection_mapping_l1ClosedBall_eq_singleton_of_mem`, this gives the textbook piecewise formula
for `P_C(x)`. -/
theorem projection_mapping_l1ClosedBall_eq_singleton_of_root
    (α : ℝ) (x : E) (lam : PosReal)
    (hroot : l1n[T_[(lam : ℝ)] x] = α) :
    Proj[B₁[α]] x = {T_[(lam : ℝ)] x} := by
  rcases euclidean_l1_owner_proper_closed_convex (ι := ι) with
    ⟨hf_proper, hf_closed, hf_convex⟩
  let lamNN : NNReal := ⟨(lam : ℝ), le_of_lt lam.2⟩
  have hlam_nonneg : 0 ≤ (lam : ℝ) := le_of_lt lam.2
  -- The root hypothesis is exactly the vanishing of the generic residual after specialization.
  have hphi : level_set_projection_residual F α x (lam : ℝ) = 0 := by
    calc
      level_set_projection_residual F α x (lam : ℝ) =
          ((l1n[T_[(lam : ℝ)] x] - α : ℝ) : EReal) := by
            simpa [lamNN] using l1ClosedBallProjectionResidual_eq α x lamNN
      _ = 0 := by
        exact_mod_cast sub_eq_zero.mpr hroot
  -- Theorem 6.30 identifies the active projection branch with the scaled proximal map.
  have hsublevel :
      Proj[F ⁻¹' Set.Iic (α : EReal)] x = prox[((lam : EReal) • F)] x :=
    projection_mapping_sublevel_eq_scaled_prox_of_level_set_projection_residual_eq_zero
      F α hf_proper hf_closed hf_convex x lam hphi
  -- Example 6.8 rewrites that scaled proximal singleton as the soft-thresholded point.
  calc
    Proj[B₁[α]] x = Proj[F ⁻¹' Set.Iic (α : EReal)] x := by
      rw [l1ClosedBall_eq_sublevel_euclidean_l1_norm]
    _ = prox[((lam : EReal) • F)] x := hsublevel
    _ = {T_[(lam : ℝ)] x} := by
      change prox[(fun y : E ↦ (((lam : ℝ) * l1n[y] : ℝ) : EReal))] x = {T_[(lam : ℝ)] x}
      simpa using
        prox_euclidean_l1_eq_singleton_softThreshold hlam_nonneg x

end
