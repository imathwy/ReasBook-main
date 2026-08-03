import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap18.Proposition_18_22
import BauschkeLean.Chap29.Example_29_43
import BauschkeLean.Chap29.Proposition_29_49

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology

/- Source/core/bridge triage:
- `source-facing`: Corollary 29.50 is the Polyak subgradient projection recursion `(29.86)` on a
  closed convex set `C` together with its weak convergence to a constrained minimizer.
- `core/canonical`: the reusable owners already present in the repository are `Argmin[C] f.toEReal`
  for constrained minimizers, `continuousConvexSelectedSubgradient` for the chosen subgradient
  field, `HasUniformRelaxationMargins` for the source step-size hypothesis, and
  `relaxedOperatorIteration` for generated iterates.
- `bridge/view`: the file keeps the source step formula and now exposes the orbit itself as a
  recursive owner, plus a bridge showing that any sequence satisfying `(29.86)` is exactly that
  canonical orbit. -/

universe u

namespace ERealFunction

noncomputable section

/-- A nonempty constrained argmin set forces the constraint set itself to be nonempty. -/
theorem constraintSet_nonempty_of_argminOn_nonempty
    {H : Type u} {C : Set H} {f : H → ℝ}
    (hargmin : (Argmin[C] f.toEReal).Nonempty) :
    C.Nonempty := by
  rcases hargmin with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance instDecidablePredConstraintSet (C : Set H) :
    DecidablePred (fun x : H ↦ x ∈ C) := Classical.decPred _

/-- The one-step Polyak subgradient projection update from Corollary 29.50, written with the
canonical minimum value `sInf (f '' C)` and the global selected subgradient associated with the
selection `s` of `∂ f`. -/
noncomputable def polyakSubgradientProjectionStep
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℝ) (s : Selection (∂ f.toEReal)) :
    H → H :=
  fun x ↦
    let u := continuousConvexSelectedSubgradient f hcont hconv s x
    let _ : DecidableEq H := Classical.decEq H
    if _hu : u ≠ 0 then
      P[C, isChebyshev_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex]
        (x + (α * ((sInf (f '' C) - f x) / ‖u‖ ^ 2)) • u)
    else
      x

/-- On the active branch where the selected subgradient is nonzero, the Polyak update is the
metric projection of the displayed affine subgradient step onto `C`. -/
theorem polyakSubgradientProjectionStep_apply_of_ne_zero
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℝ) (s : Selection (∂ f.toEReal)) {x : H}
    (hu : continuousConvexSelectedSubgradient f hcont hconv s x ≠ 0) :
    polyakSubgradientProjectionStep f C hC_closed hC_convex hC_nonempty hcont hconv α s x =
      P[C, isChebyshev_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex]
        (x + (α *
          ((sInf (f '' C) - f x) /
            ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
          continuousConvexSelectedSubgradient f hcont hconv s x) := by
  simp [polyakSubgradientProjectionStep, hu]

/-- On the inactive branch where the selected subgradient vanishes, the Polyak update fixes `x`. -/
theorem polyakSubgradientProjectionStep_apply_of_eq_zero
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℝ) (s : Selection (∂ f.toEReal)) {x : H}
    (hu : continuousConvexSelectedSubgradient f hcont hconv s x = 0) :
    polyakSubgradientProjectionStep f C hC_closed hC_convex hC_nonempty hcont hconv α s x = x := by
  simp [polyakSubgradientProjectionStep, hu]

/-- The Polyak subgradient projection orbit from Corollary 29.50, generated recursively from the
initial point `x0` by the step formula `(29.86)`. -/
noncomputable def polyakSubgradientProjectionOrbit
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℕ → ℝ) (s : Selection (∂ f.toEReal)) (x0 : H) : ℕ → H
  | 0 => x0
  | n + 1 =>
      polyakSubgradientProjectionStep
        f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s
        (polyakSubgradientProjectionOrbit
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 n)

/-- The Polyak orbit starts at the prescribed initial point `x0`. -/
@[simp] theorem polyakSubgradientProjectionOrbit_zero
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℕ → ℝ) (s : Selection (∂ f.toEReal)) (x0 : H) :
    polyakSubgradientProjectionOrbit
      f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 0 = x0 := by
  rfl

/-- Each successor of the Polyak orbit is obtained by one application of the Polyak update with
the current parameter `α n`. -/
@[simp] theorem polyakSubgradientProjectionOrbit_succ
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℕ → ℝ) (s : Selection (∂ f.toEReal)) (x0 : H) (n : ℕ) :
    polyakSubgradientProjectionOrbit
      f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 (n + 1) =
      polyakSubgradientProjectionStep
        f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s
        (polyakSubgradientProjectionOrbit
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 n) := by
  rfl

/-- The recursively generated Polyak orbit is exactly the Chapter 5 relaxed iteration of the
operator family `n ↦ polyakSubgradientProjectionStep ... (α n) s` with constant relaxation
`1`. -/
theorem polyakSubgradientProjectionOrbit_eq_relaxedOperatorIteration
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℕ → ℝ) (s : Selection (∂ f.toEReal)) (x0 : H) :
    polyakSubgradientProjectionOrbit f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 =
      relaxedOperatorIteration
        (fun n ↦
          polyakSubgradientProjectionStep
            f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s)
        (fun _ ↦ (1 : ℝ))
        x0 := by
  funext n
  induction n with
  | zero =>
      simp [polyakSubgradientProjectionOrbit]
  | succ n ih =>
      rw [polyakSubgradientProjectionOrbit_succ, relaxedOperatorIteration_succ, ih]
      simp

/-- Any sequence starting at `x0` and satisfying the Polyak recursion `(29.86)` is the canonical
Polyak orbit generated from `x0`. -/
theorem eq_polyakSubgradientProjectionOrbit_of_zero_of_succ
    (f : H → ℝ) (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℕ → ℝ) (s : Selection (∂ f.toEReal)) (x0 : H) {x : ℕ → H}
    (hx_zero : x 0 = x0)
    (hx_succ :
      ∀ n : ℕ,
        x (n + 1) =
          polyakSubgradientProjectionStep
            f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (x n)) :
    x = polyakSubgradientProjectionOrbit
      f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 := by
  funext n
  induction n with
  | zero =>
      simpa using hx_zero
  | succ n ih =>
      rw [hx_succ n, polyakSubgradientProjectionOrbit_succ, ih]

/-- Helper for Corollary 29.50: every feasible point gives an upper bound on the constrained
minimum value `sInf (f '' C)`. -/
theorem sInf_image_le_of_mem_constraint
    {C : Set H} {f : H → ℝ}
    (hargmin : (Argmin[C] f.toEReal).Nonempty)
    {x : H} (hx : x ∈ C) :
    sInf (f '' C) ≤ f x := by
  -- Route correction: avoid the earlier `EReal` coercion bridge and work directly on `f '' C`.
  rcases hargmin with ⟨y, hy⟩
  rcases mem_argminOn_iff.mp hy with ⟨hyC, hyminE⟩
  have hymin : ∀ z ∈ C, f y ≤ f z := by
    -- Translate the constrained minimality back to a real-valued lower-bound statement.
    intro z hz
    exact EReal.coe_le_coe_iff.mp ((isMinOn_iff.mp hyminE) z hz)
  have hbelow : BddBelow (f '' C) := by
    -- The minimizing value `f y` is a lower bound for the whole image `f '' C`.
    refine ⟨f y, ?_⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hymin w hw
  exact csInf_le hbelow (Set.mem_image_of_mem f hx)

/-- Helper for Corollary 29.50: an argmin witness realizes the constrained infimum
`sInf (f '' C)`. -/
theorem argmin_value_eq_sInf_image
    {C : Set H} {f : H → ℝ} {x : H} (hx : x ∈ Argmin[C] f.toEReal) :
    f x = sInf (f '' C) := by
  -- Route correction: prove the real infimum identity directly, instead of transporting through
  -- an `EReal`-valued `IsMinOn` statement.
  rcases mem_argminOn_iff.mp hx with ⟨hxC, hxminE⟩
  have hxmin : ∀ z ∈ C, f x ≤ f z := by
    -- The constrained argmin inequality is finite on both sides, so it descends to `ℝ`.
    intro z hz
    exact EReal.coe_le_coe_iff.mp ((isMinOn_iff.mp hxminE) z hz)
  have hbelow : BddBelow (f '' C) := by
    -- The minimizing value `f x` is itself a lower bound for `f '' C`.
    refine ⟨f x, ?_⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hxmin w hw
  apply le_antisymm
  · -- As a lower bound attained by `x`, `f x` lies below the infimum of the image.
    refine le_csInf ?_ ?_
    · exact ⟨f x, Set.mem_image_of_mem f hxC⟩
    · intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact hxmin w hw
  · -- Conversely, the infimum never exceeds any point of the image, in particular `f x`.
    exact csInf_le hbelow (Set.mem_image_of_mem f hxC)

/-- Helper for Corollary 29.50: the explicit distance selection takes each point to a member of
`∂ ((fun y ↦ Metric.infDist y C).toEReal)` by using `0` on `C` and the normalized projection
residual outside `C`. -/
theorem distanceToSetSelection_mem_subdifferential
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} :
    (if hx : x ∈ C then
        (0 : H)
      else
        (Metric.infDist x C)⁻¹ •
          (x - P[C, isChebyshev_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex] x)) ∈
      (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x := by
  -- Route correction: use the Chapter 18 zero-branch and singleton-branch owners directly.
  by_cases hx : x ∈ C
  · -- On `C`, the zero vector satisfies the local affine minorant characterization.
    simpa [hx] using
      (Set.distanceToSet_mem_subdifferential_iff_zero_value_local
        (C := C) (x := x) (u := (0 : H)) hx).2
        (by
          intro y
          simpa using (Metric.infDist_nonneg (x := y) (s := C)))
  · -- Outside `C`, the explicit normalized projection residual is the unique subgradient.
    let P_C := P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
    let u : H := (Metric.infDist x C)⁻¹ • (x - P_C x)
    have hxlt : 0 < Metric.infDist x C := by
      simpa using (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
    have hp_char :
        P_C x ∈ C ∧ ∀ z ∈ C, ⟪z - P_C x, x - P_C x⟫_ℝ ≤ 0 := by
      exact
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl
    have hres_norm : ‖x - P_C x‖ = Metric.infDist x C := by
      simpa [P_C, dist_eq_norm] using
        (projectionPoint_isBestApproximation C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x).2
    have hres_ne : x - P_C x ≠ 0 := by
      intro hzero
      have hdist_zero : Metric.infDist x C = 0 := by
        rw [← hres_norm]
        simp [hzero]
      exact (ne_of_gt hxlt) hdist_zero
    have hu_norm : ‖u‖ = 1 := by
      -- Normalizing the nonzero projection residual produces a unit vector.
      simpa [u, hres_norm] using norm_smul_inv_norm hres_ne
    intro y
    let q : H := P_C y
    have hq_mem : q ∈ C := projectionPoint_mem C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
    have hq_dist : ‖y - q‖ = Metric.infDist y C := by
      simpa [q, P_C, dist_eq_norm] using
        (projectionPoint_isBestApproximation C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y).2
    have hq_nonpos : ⟪q - P_C x, x - P_C x⟫_ℝ ≤ 0 := hp_char.2 q hq_mem
    have hq_nonpos_u : ⟪q - P_C x, u⟫_ℝ ≤ 0 := by
      have hu_def : u = (Metric.infDist x C)⁻¹ • (x - P_C x) := rfl
      rw [hu_def, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hxlt.le) hq_nonpos
    have hu_self : ⟪x - P_C x, u⟫_ℝ = Metric.infDist x C := by
      have hu_def : u = (Metric.infDist x C)⁻¹ • (x - P_C x) := rfl
      rw [hu_def, real_inner_smul_right, real_inner_self_eq_norm_sq, hres_norm]
      field_simp [ne_of_gt hxlt]
    have hsplit :
        ⟪y - x, u⟫_ℝ + Metric.infDist x C = ⟪y - P_C x, u⟫_ℝ := by
      have hdecomp : y - x = (y - P_C x) - (x - P_C x) := by
        abel
      rw [hdecomp, inner_sub_left, hu_self]
      ring
    have hyq_split :
        ⟪y - P_C x, u⟫_ℝ = ⟪y - q, u⟫_ℝ + ⟪q - P_C x, u⟫_ℝ := by
      have hdecomp : y - P_C x = (y - q) + (q - P_C x) := by
        abel
      rw [hdecomp, inner_add_left]
    have hyq_le : ⟪y - q, u⟫_ℝ ≤ ‖y - q‖ := by
      calc
        ⟪y - q, u⟫_ℝ ≤ ‖y - q‖ * ‖u‖ := real_inner_le_norm _ _
        _ = ‖y - q‖ := by rw [hu_norm, mul_one]
    apply (Set.distanceToSet_mem_subdifferential_iff_real_local
      (C := C) (x := x)
      (u := if hx' : x ∈ C then
          (0 : H)
        else
          (Metric.infDist x C)⁻¹ •
            (x - P[C, isChebyshev_of_nonempty_isClosed_convex
              hC_nonempty hC_closed hC_convex] x))).2
    intro y
    let q : H := P_C y
    have hq_mem : q ∈ C := projectionPoint_mem C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
    have hq_dist : ‖y - q‖ = Metric.infDist y C := by
      simpa [q, P_C, dist_eq_norm] using
        (projectionPoint_isBestApproximation C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y).2
    have hq_nonpos : ⟪q - P_C x, x - P_C x⟫_ℝ ≤ 0 := hp_char.2 q hq_mem
    have hq_nonpos_u : ⟪q - P_C x, u⟫_ℝ ≤ 0 := by
      have hu_def : u = (Metric.infDist x C)⁻¹ • (x - P_C x) := rfl
      rw [hu_def, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hxlt.le) hq_nonpos
    have hu_self : ⟪x - P_C x, u⟫_ℝ = Metric.infDist x C := by
      have hu_def : u = (Metric.infDist x C)⁻¹ • (x - P_C x) := rfl
      rw [hu_def, real_inner_smul_right, real_inner_self_eq_norm_sq, hres_norm]
      field_simp [ne_of_gt hxlt]
    have hsplit :
        ⟪y - x, u⟫_ℝ + Metric.infDist x C = ⟪y - P_C x, u⟫_ℝ := by
      have hdecomp : y - x = (y - P_C x) - (x - P_C x) := by
        abel
      rw [hdecomp, inner_sub_left, hu_self]
      ring
    have hyq_split :
        ⟪y - P_C x, u⟫_ℝ = ⟪y - q, u⟫_ℝ + ⟪q - P_C x, u⟫_ℝ := by
      have hdecomp : y - P_C x = (y - q) + (q - P_C x) := by
        abel
      rw [hdecomp, inner_add_left]
    have hyq_le : ⟪y - q, u⟫_ℝ ≤ ‖y - q‖ := by
      calc
        ⟪y - q, u⟫_ℝ ≤ ‖y - q‖ * ‖u‖ := real_inner_le_norm _ _
        _ = ‖y - q‖ := by rw [hu_norm, mul_one]
    -- Rewrite the target's explicit piecewise subgradient into the local normalized residual `u`.
    simpa only [u, hx, P_C] using
      (calc
        ⟪y - x, u⟫_ℝ + Metric.infDist x C = ⟪y - P_C x, u⟫_ℝ := hsplit
        _ = ⟪y - q, u⟫_ℝ + ⟪q - P_C x, u⟫_ℝ := hyq_split
        _ ≤ ⟪y - q, u⟫_ℝ := by linarith
        _ ≤ ‖y - q‖ := hyq_le
        _ = Metric.infDist y C := hq_dist)

/-- Helper for Corollary 29.50: an explicit selection of the distance-to-set subdifferential,
using `0` on `C` and the normalized projection residual outside `C`. -/
noncomputable def distanceToSetSelection
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Selection (∂ (fun y : H ↦ Metric.infDist y C).toEReal) :=
  fun x ↦
    ⟨if hx : x.1 ∈ C then
        (0 : H)
      else
        (Metric.infDist x.1 C)⁻¹ •
          (x.1 - P[C, isChebyshev_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex] x.1),
      distanceToSetSelection_mem_subdifferential hC_nonempty hC_closed hC_convex⟩

/-- Helper for Corollary 29.50: the Chapter 29 projector for the distance-to-set component is
exactly the metric projection onto `C`. -/
theorem distanceToSetProjector_eq_metricProjection
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (x : H) :
    continuousConvexSubgradientProjector
        (fun y : H ↦ Metric.infDist y C)
        0
        (Metric.continuous_infDist_pt C)
        (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
          hC_nonempty hC_closed hC_convex)
        (by
          rcases hC_nonempty with ⟨z, hz⟩
          exact ⟨z, by
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz]⟩)
        (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
        x =
      P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] x := by
  let P_C := P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
  by_cases hx : x ∈ C
  · -- Inside `C`, both the Chapter 29 projector and the metric projection fix `x`.
    have hx_level :
        x ∈ lowerLevelSet (fun y : H ↦ Metric.infDist y C).toEReal.asEReal 0 := by
      rw [mem_lowerLevelSet_iff]
      simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hx]
    rw [ERealFunction.continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      (fun y : H ↦ Metric.infDist y C) 0
      (Metric.continuous_infDist_pt C)
      (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
        hC_nonempty hC_closed hC_convex)
      (by
        rcases hC_nonempty with ⟨z, hz⟩
        exact ⟨z, by
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz]⟩)
      (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
      hx_level]
    simpa [P_C] using
      (projectionPoint_eq_self_of_mem
        (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
        (hC_convex := hC_convex) hx).symm
  · have hxlt : 0 < Metric.infDist x C := by
      simpa using (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
    have hsel :
        continuousConvexSelectedSubgradient
            (fun y : H ↦ Metric.infDist y C)
            (Metric.continuous_infDist_pt C)
            (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
              hC_nonempty hC_closed hC_convex)
            (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
            x =
          (Metric.infDist x C)⁻¹ • (x - P_C x) := by
      -- Outside `C`, the selected distance subgradient is exactly the normalized residual.
      simp [continuousConvexSelectedSubgradient, distanceToSetSelection, hx, P_C]
    have hres_norm : ‖x - P_C x‖ = Metric.infDist x C := by
      -- The metric projection realizes the infimum distance by definition.
      simpa [P_C] using
        projection_residual_norm_eq_infDist
          (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
          (hC_convex := hC_convex) x
    have hres_ne : x - P_C x ≠ 0 := by
      intro hzero
      have hdist_zero : Metric.infDist x C = 0 := by
        rw [← hres_norm]
        simp [hzero]
      exact (ne_of_gt hxlt) hdist_zero
    have hsel_norm :
        ‖(Metric.infDist x C)⁻¹ • (x - P_C x)‖ = 1 := by
      simpa [hres_norm] using norm_smul_inv_norm hres_ne
    rw [ERealFunction.continuousConvexSubgradientProjector_apply_of_lt
      (fun y : H ↦ Metric.infDist y C) 0
      (Metric.continuous_infDist_pt C)
      (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
        hC_nonempty hC_closed hC_convex)
      (by
        rcases hC_nonempty with ⟨z, hz⟩
        exact ⟨z, by
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz]⟩)
      (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
      hxlt]
    rw [hsel]
    have hdist_ne : Metric.infDist x C ≠ 0 := ne_of_gt hxlt
    have hscalar :
        (-Metric.infDist x C) * (Metric.infDist x C)⁻¹ = (-1 : ℝ) := by
      field_simp [hdist_ne]
    calc
      x +
          (((0 - Metric.infDist x C) /
                ‖(Metric.infDist x C)⁻¹ • (x - P_C x)‖ ^ 2) •
            ((Metric.infDist x C)⁻¹ • (x - P_C x)))
          =
        x + ((-Metric.infDist x C) • ((Metric.infDist x C)⁻¹ • (x - P_C x))) := by
            rw [hsel_norm]
            norm_num
      _ = x + (((-Metric.infDist x C) * (Metric.infDist x C)⁻¹) • (x - P_C x)) := by
            rw [smul_smul]
      _ = x + ((-1 : ℝ) • (x - P_C x)) := by rw [hscalar]
      _ = x + (P_C x - x) := by simp
      _ = P_C x := by abel

/-- Helper for Corollary 29.50: subtracting a real constant preserves subdifferential
membership for real-valued objectives. -/
theorem shiftedObjectiveSelection_mem_subdifferential
    {f : H → ℝ} {x u : H} (hu : u ∈ (∂ f.toEReal) x) (μ : ℝ) :
    u ∈ (∂ (fun y : H ↦ f y - μ).toEReal) x := by
  -- Rewrite both subdifferential conditions to real inequalities and cancel the constant shift.
  rw [mem_subdifferential_iff] at hu ⊢
  intro y
  have hreal : ⟪y - x, u⟫_ℝ + f x ≤ f y := by
    have hcast :
        (((⟪y - x, u⟫_ℝ + f x : ℝ) : EReal)) ≤ (((f y : ℝ) : EReal)) := by
      calc
        (((⟪y - x, u⟫_ℝ + f x : ℝ) : EReal))
            = (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
                rw [← EReal.coe_add]
        _ ≤ (f y : EReal) := hu y
        _ = (((f y : ℝ) : EReal)) := by simp
    exact_mod_cast hcast
  have hshift : ⟪y - x, u⟫_ℝ + (f x - μ) ≤ f y - μ := by
    linarith
  calc
    (⟪y - x, u⟫_ℝ : EReal) + (((f x - μ : ℝ) : EReal))
        = (((⟪y - x, u⟫_ℝ + (f x - μ) : ℝ) : EReal)) := by
            rw [← EReal.coe_add]
    _ ≤ (((f y - μ : ℝ) : EReal)) := by
          exact_mod_cast hshift
    _ = (((fun z : H ↦ f z - μ).toEReal y : EReal)) := by
          simp [Function.toEReal_apply]

/-- Helper for Corollary 29.50: the original selected subgradient field also selects from the
shifted objective `y ↦ f y - μ`. -/
noncomputable def shiftedObjectiveSelection
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (s : Selection (∂ f.toEReal)) (μ : ℝ) :
    Selection (∂ (fun y : H ↦ f y - μ).toEReal) :=
  fun x ↦
    ⟨continuousConvexSelectedSubgradient f hcont hconv s x.1,
      shiftedObjectiveSelection_mem_subdifferential
        (continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s x.1) μ⟩

/-- Helper for Corollary 29.50: if a feasible point has vanishing selected subgradient, then it
already attains the constrained minimum value `sInf (f '' C)`. -/
theorem feasible_value_eq_sInf_of_selectedSubgradient_eq_zero
    {C : Set H} (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hargmin : (Argmin[C] f.toEReal).Nonempty) (s : Selection (∂ f.toEReal))
    {x : H} (hxC : x ∈ C)
    (hu0 : continuousConvexSelectedSubgradient f hcont hconv s x = 0) :
    f x = sInf (f '' C) := by
  have hargmin_nonempty := hargmin
  rcases hargmin_nonempty with ⟨p, hp⟩
  have hsub :
      continuousConvexSelectedSubgradient f hcont hconv s x ∈ (∂ f.toEReal) x :=
    continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s x
  rw [hu0, mem_subdifferential_iff] at hsub
  have hxp : f x ≤ f p := by
    have hxp_zero :
        (0 : EReal) + (((f x : ℝ) : EReal)) ≤ (((f p : ℝ) : EReal)) := by
      have hxp_zero_inner :
          (⟪p - x, (0 : H)⟫_ℝ : EReal) + (Function.toEReal f x : EReal) ≤
            (Function.toEReal f p : EReal) := hsub p
      simpa [Function.toEReal_apply, inner_zero_right] using hxp_zero_inner
    have hxp_cast : (f x : EReal) ≤ (f p : EReal) := by
      simpa using hxp_zero
    exact EReal.coe_le_coe_iff.mp hxp_cast
  have hsInf_le : sInf (f '' C) ≤ f x := sInf_image_le_of_mem_constraint hargmin hxC
  have hp_eq : f p = sInf (f '' C) := argmin_value_eq_sInf_image hp
  exact le_antisymm (by simpa [hp_eq] using hxp) hsInf_le

/-- Helper for Corollary 29.50: the alternating two-function family used to reduce the Polyak
recursion to Proposition 29.49. -/
noncomputable def polyakAlternatingFamily
    (f : H → ℝ) (C : Set H) : Fin 2 → H → ℝ
  | 0 => fun y ↦ f y - sInf (f '' C)
  | 1 => fun y ↦ Metric.infDist y C

/-- Helper for Corollary 29.50: the even component of the alternating family is the shifted
objective `f - sInf (f '' C)`. -/
@[simp] theorem polyakAlternatingFamily_zero
    (f : H → ℝ) (C : Set H) :
    polyakAlternatingFamily f C 0 = fun y ↦ f y - sInf (f '' C) := by
  rfl

/-- Helper for Corollary 29.50: the odd component of the alternating family is the distance-to-set
objective `d_C`. -/
@[simp] theorem polyakAlternatingFamily_one
    (f : H → ℝ) (C : Set H) :
    polyakAlternatingFamily f C 1 = fun y ↦ Metric.infDist y C := by
  rfl

/-- Helper for Corollary 29.50: the alternating control sequence picks the shifted-objective
component on even steps and the distance component on odd steps. -/
noncomputable def polyakAlternatingIndex : ℕ → Fin 2 :=
  fun n ↦ ⟨n % 2, by
    omega⟩

/-- Helper for Corollary 29.50: even alternating indices select the shifted-objective component. -/
@[simp] theorem polyakAlternatingIndex_even (n : ℕ) :
    polyakAlternatingIndex (2 * n) = 0 := by
  apply Fin.ext
  simp [polyakAlternatingIndex]

/-- Helper for Corollary 29.50: odd alternating indices select the distance component. -/
@[simp] theorem polyakAlternatingIndex_odd (n : ℕ) :
    polyakAlternatingIndex (2 * n + 1) = 1 := by
  apply Fin.ext
  simp [polyakAlternatingIndex]

/-- Helper for Corollary 29.50: the alternating relaxed iteration uses the Polyak parameter `α n`
on even steps and the full projection parameter `1` on odd steps. -/
noncomputable def polyakAlternatingRelaxation
    (α : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ if n % 2 = 0 then α (n / 2) else 1

/-- Helper for Corollary 29.50: the even alternating relaxation parameter is `α n`. -/
@[simp] theorem polyakAlternatingRelaxation_even
    (α : ℕ → ℝ) (n : ℕ) :
    polyakAlternatingRelaxation α (2 * n) = α n := by
  simp [polyakAlternatingRelaxation]

/-- Helper for Corollary 29.50: the odd alternating relaxation parameter is `1`. -/
@[simp] theorem polyakAlternatingRelaxation_odd
    (α : ℕ → ℝ) (n : ℕ) :
    polyakAlternatingRelaxation α (2 * n + 1) = 1 := by
  simp [polyakAlternatingRelaxation]

/-- Helper for Corollary 29.50: the common zero lower-level set of the alternating `Fin 2`
family `{f - sInf (f '' C), Metric.infDist · C}` is exactly `Argmin[C] f.toEReal`. -/
theorem polyakConstraintSet_eq_argminOn
    {C : Set H} (hC_closed : IsClosed C) (f : H → ℝ)
    (hargmin : (Argmin[C] f.toEReal).Nonempty) :
    cyclicSubgradientProjectorConstraintSet (polyakAlternatingFamily f C) =
      Argmin[C] f.toEReal := by
  let μ : ℝ := sInf (f '' C)
  let hC_nonempty : C.Nonempty := constraintSet_nonempty_of_argminOn_nonempty hargmin
  -- Route correction: work with the stable alternating-family owner instead of a let-bound
  -- `Fin 2` family so the two lower-level conditions rewrite componentwise.
  ext x
  constructor
  · intro hx
    rw [mem_cyclicSubgradientProjectorConstraintSet_iff] at hx
    have hx_shift :
        x ∈ lowerLevelSet ((polyakAlternatingFamily f C 0).toEReal.asEReal) 0 := hx 0
    have hx_dist :
        x ∈ lowerLevelSet ((polyakAlternatingFamily f C 1).toEReal.asEReal) 0 := hx 1
    have hfx_le : f x ≤ μ := by
      have hfx_sub_leE : (((f x - μ : ℝ) : EReal)) ≤ (0 : EReal) := by
        exact
          (by
            simpa [polyakAlternatingFamily, μ, Function.toEReal_apply] using
              (mem_lowerLevelSet_iff
                ((polyakAlternatingFamily f C 0).toEReal.asEReal) 0 x).1 hx_shift)
      have hfx_sub_le : (f x : ℝ) - μ ≤ 0 := by
        exact_mod_cast hfx_sub_leE
      linarith
    have hdist_le : Metric.infDist x C ≤ 0 := by
      simpa [polyakAlternatingFamily, Function.toEReal_apply] using
        (mem_lowerLevelSet_iff ((polyakAlternatingFamily f C 1).toEReal.asEReal) 0 x).1 hx_dist
    have hdist_zero : Metric.infDist x C = 0 := by
      exact le_antisymm hdist_le (Metric.infDist_nonneg (x := x) (s := C))
    have hxC : x ∈ C := by
      rw [hC_closed.mem_iff_infDist_zero hC_nonempty]
      exact hdist_zero
    have hμ_le : μ ≤ f x := sInf_image_le_of_mem_constraint hargmin hxC
    have hfx_eq : f x = μ := by
      linarith
    rw [mem_argminOn_iff]
    constructor
    · exact hxC
    · rw [isMinOn_iff]
      intro z hz
      exact EReal.coe_le_coe_iff.mpr <| by
        calc
          f x = μ := hfx_eq
          _ ≤ f z := sInf_image_le_of_mem_constraint hargmin hz
  · intro hx
    rw [mem_cyclicSubgradientProjectorConstraintSet_iff]
    intro j
    fin_cases j
    · -- The shifted-objective component vanishes exactly at constrained minimizers.
      rw [mem_lowerLevelSet_iff]
      have hfx_eq : f x = μ := by
        simpa [μ] using argmin_value_eq_sInf_image hx
      simpa [polyakAlternatingFamily, μ, Function.toEReal_apply, hfx_eq]
    · -- The distance component vanishes because argmin points lie in `C`.
      rw [mem_lowerLevelSet_iff]
      have hxC : x ∈ C := (mem_argminOn_iff.mp hx).1
      simpa [polyakAlternatingFamily, Function.toEReal_apply, Metric.infDist_zero_of_mem hxC]

/-- Helper for Corollary 29.50: if `f x` already equals the constrained infimum, then the
shifted-objective projector fixes `x`. -/
theorem shiftedObjectiveProjector_apply_of_eq_sInf
    {C : Set H} (f : H → ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hargmin : (Argmin[C] f.toEReal).Nonempty)
    (s : Selection (∂ f.toEReal)) {x : H}
    (hfx : f x = sInf (f '' C)) :
    let μ : ℝ := sInf (f '' C)
    let hshift_nonempty :
        (lowerLevelSet (fun y : H ↦ f y - μ).toEReal.asEReal 0).Nonempty := by
          rcases hargmin with ⟨p, hp⟩
          refine ⟨p, ?_⟩
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp, μ]
    continuousConvexSubgradientProjector
        (fun y : H ↦ f y - μ) 0
        (hcont.sub continuous_const)
        (by simpa [sub_eq_add_neg] using hconv.add_const (-μ))
        hshift_nonempty
        (shiftedObjectiveSelection f hcont hconv s μ)
        x = x := by
  -- Reaching the zero lower level set for the shifted objective turns the projector into the
  -- identity.
  dsimp
  have hx_level :
      x ∈ lowerLevelSet (fun y : H ↦ f y - sInf (f '' C)).toEReal.asEReal 0 := by
    rw [mem_lowerLevelSet_iff]
    simpa [Function.toEReal_apply, hfx]
  exact
    continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      (fun y : H ↦ f y - sInf (f '' C)) 0
      (hcont.sub continuous_const)
      (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
      (by
        rcases hargmin with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        rw [mem_lowerLevelSet_iff]
        simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
      (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
      hx_level

/-- Helper for Corollary 29.50: on the strict branch `sInf (f '' C) < f x`, relaxing the
shifted-objective projector produces the textbook Polyak predictor. -/
theorem shiftedObjectiveRelaxedStep_apply_of_lt
    {C : Set H} (f : H → ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hargmin : (Argmin[C] f.toEReal).Nonempty)
    (s : Selection (∂ f.toEReal)) {x : H} (α : ℝ)
    (hxlt : sInf (f '' C) < f x) :
    let μ : ℝ := sInf (f '' C)
    let hshift_nonempty :
        (lowerLevelSet (fun y : H ↦ f y - μ).toEReal.asEReal 0).Nonempty := by
          rcases hargmin with ⟨p, hp⟩
          refine ⟨p, ?_⟩
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp, μ]
    let Gshift :=
      continuousConvexSubgradientProjector
        (fun y : H ↦ f y - μ) 0
        (hcont.sub continuous_const)
        (by simpa [sub_eq_add_neg] using hconv.add_const (-μ))
        hshift_nonempty
        (shiftedObjectiveSelection f hcont hconv s μ)
    x + α • (Gshift x - x) =
      x + (α * ((μ - f x) /
        ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
        continuousConvexSelectedSubgradient f hcont hconv s x := by
  -- Expanding the strict shifted-projector branch reduces the relaxed step to a single scalar
  -- multiple of the selected subgradient.
  dsimp
  have hshift_eq :
      continuousConvexSubgradientProjector
          (fun y : H ↦ f y - sInf (f '' C)) 0
          (hcont.sub continuous_const)
          (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
          (by
            rcases hargmin with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
          (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
          x =
        x + (((sInf (f '' C) - f x) /
          ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2) •
          continuousConvexSelectedSubgradient f hcont hconv s x) := by
    simpa [continuousConvexSelectedSubgradient, shiftedObjectiveSelection, sub_eq_add_neg]
      using
        (continuousConvexSubgradientProjector_apply_of_lt
          (fun y : H ↦ f y - sInf (f '' C)) 0
          (hcont.sub continuous_const)
          (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
          (by
            rcases hargmin with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
          (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
          (by simpa [sub_eq_add_neg] using hxlt))
  rw [hshift_eq]
  simp [sub_eq_add_neg, smul_add, smul_sub, smul_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Corollary 29.50: one relaxed shifted-objective step followed by the full
distance-to-set projector is exactly one Polyak update from a feasible point. -/
theorem polyakTwoStep_eq_step_of_mem_constraint
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hargmin : (Argmin[C] f.toEReal).Nonempty)
    (s : Selection (∂ f.toEReal)) {x : H} (hxC : x ∈ C) (α : ℝ) :
    let μ : ℝ := sInf (f '' C)
    let hC_nonempty : C.Nonempty := constraintSet_nonempty_of_argminOn_nonempty hargmin
    let hshift_nonempty :
        (lowerLevelSet (fun y : H ↦ f y - μ).toEReal.asEReal 0).Nonempty := by
          rcases hargmin with ⟨p, hp⟩
          refine ⟨p, ?_⟩
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp, μ]
    let Gshift :=
      continuousConvexSubgradientProjector
        (fun y : H ↦ f y - μ) 0
        (hcont.sub continuous_const)
        (by simpa [sub_eq_add_neg] using hconv.add_const (-μ))
        hshift_nonempty
        (shiftedObjectiveSelection f hcont hconv s μ)
    let Gdist :=
      continuousConvexSubgradientProjector
        (fun y : H ↦ Metric.infDist y C) 0
        (Metric.continuous_infDist_pt C)
        (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
          hC_nonempty hC_closed hC_convex)
        (by
          rcases hC_nonempty with ⟨z, hz⟩
          refine ⟨z, ?_⟩
          rw [mem_lowerLevelSet_iff]
          simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
        (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
    Gdist (x + α • (Gshift x - x)) =
      polyakSubgradientProjectionStep
        f C hC_closed hC_convex hC_nonempty hcont hconv α s x := by
  -- Split on whether `x` already attains the constrained infimum; this is the stable Chapter 29
  -- normal form for the shifted projector.
  dsimp
  let hC_nonempty : C.Nonempty := constraintSet_nonempty_of_argminOn_nonempty hargmin
  have hμ_le : sInf (f '' C) ≤ f x := sInf_image_le_of_mem_constraint hargmin hxC
  by_cases hfx : f x = sInf (f '' C)
  · -- On the minimizing branch, both the shifted projector and the Polyak step fix `x`.
    have hshift_fix :
        continuousConvexSubgradientProjector
            (fun y : H ↦ f y - sInf (f '' C)) 0
            (hcont.sub continuous_const)
            (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
            (by
              rcases hargmin with ⟨p, hp⟩
              refine ⟨p, ?_⟩
              rw [mem_lowerLevelSet_iff]
              simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
            (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
            x = x := by
      simpa using shiftedObjectiveProjector_apply_of_eq_sInf f hcont hconv hargmin s hfx
    have hdist_fix :
        continuousConvexSubgradientProjector
            (fun y : H ↦ Metric.infDist y C) 0
            (Metric.continuous_infDist_pt C)
            (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
              hC_nonempty hC_closed hC_convex)
            (by
              rcases hC_nonempty with ⟨z, hz⟩
              refine ⟨z, ?_⟩
              rw [mem_lowerLevelSet_iff]
              simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
            (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
            x = x := by
      rw [distanceToSetProjector_eq_metricProjection hC_nonempty hC_closed hC_convex]
      simpa using
        (projectionPoint_eq_self_of_mem
          (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
          (hC_convex := hC_convex) hxC)
    have hpolyak_fix :
        polyakSubgradientProjectionStep
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x = x := by
      by_cases hu : continuousConvexSelectedSubgradient f hcont hconv s x = 0
      · exact polyakSubgradientProjectionStep_apply_of_eq_zero
          f C hC_closed hC_convex hC_nonempty hcont hconv α s hu
      · rw [polyakSubgradientProjectionStep_apply_of_ne_zero
          f C hC_closed hC_convex hC_nonempty hcont hconv α s hu]
        have hproj_fix :
            P[C, isChebyshev_of_nonempty_isClosed_convex
              hC_nonempty hC_closed hC_convex]
              (x + (α *
                ((sInf (f '' C) - f x) /
                  ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
                continuousConvexSelectedSubgradient f hcont hconv s x) = x := by
          have harg :
              x + (α *
                ((sInf (f '' C) - f x) /
                  ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
                continuousConvexSelectedSubgradient f hcont hconv s x = x := by
            simp [hfx]
          rw [harg]
          simpa using
            (projectionPoint_eq_self_of_mem
              (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
              (hC_convex := hC_convex) hxC)
        exact hproj_fix
    calc
      continuousConvexSubgradientProjector
          (fun y : H ↦ Metric.infDist y C) 0
          (Metric.continuous_infDist_pt C)
          (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            hC_nonempty hC_closed hC_convex)
          (by
            rcases hC_nonempty with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
          (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
          (x + α •
            (continuousConvexSubgradientProjector
              (fun y : H ↦ f y - sInf (f '' C)) 0
              (hcont.sub continuous_const)
              (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
              (by
                rcases hargmin with ⟨p, hp⟩
                refine ⟨p, ?_⟩
                rw [mem_lowerLevelSet_iff]
                simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
              (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
              x - x))
          =
        continuousConvexSubgradientProjector
          (fun y : H ↦ Metric.infDist y C) 0
          (Metric.continuous_infDist_pt C)
          (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            hC_nonempty hC_closed hC_convex)
          (by
            rcases hC_nonempty with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
          (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
          x := by simpa [hshift_fix]
      _ = x := hdist_fix
      _ = polyakSubgradientProjectionStep
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x := hpolyak_fix.symm
  · -- On the strict branch, the shifted relaxed step is the Polyak predictor and the distance
    -- projector is the metric projection onto `C`.
    have hxlt : sInf (f '' C) < f x := lt_of_le_of_ne hμ_le (Ne.symm hfx)
    have hu_ne :
        continuousConvexSelectedSubgradient f hcont hconv s x ≠ 0 := by
      intro hu0
      have hfx' :=
        feasible_value_eq_sInf_of_selectedSubgradient_eq_zero
          f hcont hconv hargmin s hxC hu0
      exact hfx hfx'
    have hstep_eq :
        x +
            α •
              (continuousConvexSubgradientProjector
                (fun y : H ↦ f y - sInf (f '' C)) 0
                (hcont.sub continuous_const)
                (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
                (by
                  rcases hargmin with ⟨p, hp⟩
                  refine ⟨p, ?_⟩
                  rw [mem_lowerLevelSet_iff]
                  simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
                (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
                x - x) =
          x + (α *
            ((sInf (f '' C) - f x) /
              ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
            continuousConvexSelectedSubgradient f hcont hconv s x := by
      simpa using
        shiftedObjectiveRelaxedStep_apply_of_lt
          f hcont hconv hargmin s α hxlt
    calc
      continuousConvexSubgradientProjector
          (fun y : H ↦ Metric.infDist y C) 0
          (Metric.continuous_infDist_pt C)
          (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            hC_nonempty hC_closed hC_convex)
          (by
            rcases hC_nonempty with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
          (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
          (x + α •
            (continuousConvexSubgradientProjector
              (fun y : H ↦ f y - sInf (f '' C)) 0
              (hcont.sub continuous_const)
              (by simpa [sub_eq_add_neg] using hconv.add_const (-(sInf (f '' C))))
              (by
                rcases hargmin with ⟨p, hp⟩
                refine ⟨p, ?_⟩
                rw [mem_lowerLevelSet_iff]
                simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp])
              (shiftedObjectiveSelection f hcont hconv s (sInf (f '' C)))
              x - x))
          =
        continuousConvexSubgradientProjector
          (fun y : H ↦ Metric.infDist y C) 0
          (Metric.continuous_infDist_pt C)
          (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            hC_nonempty hC_closed hC_convex)
          (by
            rcases hC_nonempty with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            rw [mem_lowerLevelSet_iff]
            simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz])
          (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
          (x + (α *
            ((sInf (f '' C) - f x) /
              ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
            continuousConvexSelectedSubgradient f hcont hconv s x) := by
              rw [hstep_eq]
      _ =
        P[C, isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex]
          (x + (α *
            ((sInf (f '' C) - f x) /
              ‖continuousConvexSelectedSubgradient f hcont hconv s x‖ ^ 2)) •
            continuousConvexSelectedSubgradient f hcont hconv s x) := by
              rw [distanceToSetProjector_eq_metricProjection
                hC_nonempty hC_closed hC_convex]
      _ =
        polyakSubgradientProjectionStep
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x := by
            rw [polyakSubgradientProjectionStep_apply_of_ne_zero
              f C hC_closed hC_convex hC_nonempty hcont hconv α s hu_ne]

/-- Helper for Corollary 29.50: every Polyak update remains in the constraint set `C`. -/
theorem polyakSubgradientProjectionStep_mem_constraint
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty) (f : H → ℝ)
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (α : ℝ) (s : Selection (∂ f.toEReal)) {x : H} (hxC : x ∈ C) :
    polyakSubgradientProjectionStep
      f C hC_closed hC_convex hC_nonempty hcont hconv α s x ∈ C := by
  by_cases hu : continuousConvexSelectedSubgradient f hcont hconv s x = 0
  · -- The inactive branch leaves the feasible point unchanged.
    simpa [polyakSubgradientProjectionStep, hu] using hxC
  · -- The active branch is a metric projection onto `C`.
    rw [polyakSubgradientProjectionStep_apply_of_ne_zero
      f C hC_closed hC_convex hC_nonempty hcont hconv α s hu]
    exact projectionPoint_mem C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) _

/-- Corollary 29.50: let `C` be a closed convex subset of the real Hilbert space `H`, let
`f : H → ℝ` be continuous and convex with `Argmin[C] f.toEReal` nonempty, and assume either that
`f` is bounded on every bounded subset of `H`, or that `f.toEReal.asEReal∗` is supercoercive, or
that `H` is finite-dimensional. If the relaxation parameters `αₙ` admit uniform positive margins
from `0` and `2` (hence lie in `]0, 2[`), then the recursively defined Polyak orbit `(29.86)`
from `x0 ∈ C` converges weakly to a minimizer of `f` over `C`. -/
theorem polyakSubgradientProjection_exists_weakLimit_mem_argminOn
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hargmin : (Argmin[C] f.toEReal).Nonempty)
    (hcase :
      (∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B)) ∨
        Supercoercive (f.toEReal.asEReal∗) ∨
        FiniteDimensional ℝ H)
    (α : ℕ → ℝ)
    (hα_uniform : HasUniformRelaxationMargins α)
    (s : Selection (∂ f.toEReal))
    (x0 : H) (hx0 : x0 ∈ C) :
    ∃ p ∈ Argmin[C] f.toEReal,
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (polyakSubgradientProjectionOrbit
              f C hC_closed hC_convex
              (constraintSet_nonempty_of_argminOn_nonempty hargmin) hcont hconv α s x0 n))
        atTop
        (nhds (toWeakSpace ℝ H p)) := by
  let μ : ℝ := sInf (f '' C)
  let hC_nonempty : C.Nonempty := constraintSet_nonempty_of_argminOn_nonempty hargmin
  have hshift_nonempty :
      (lowerLevelSet (fun y : H ↦ f y - μ).toEReal.asEReal 0).Nonempty := by
    -- An argmin witness also lies in the zero lower level set of the shifted objective.
    rcases hargmin with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [mem_lowerLevelSet_iff]
    simpa [Function.toEReal_apply, argmin_value_eq_sInf_image hp, μ]
  have hconstraint_nonempty :
      (cyclicSubgradientProjectorConstraintSet (polyakAlternatingFamily f C)).Nonempty := by
    -- The alternating feasibility set is exactly `Argmin[C] f.toEReal`.
    rw [polyakConstraintSet_eq_argminOn (C := C) hC_closed f hargmin]
    exact hargmin
  let hcontAlt : ∀ j : Fin 2, Continuous (polyakAlternatingFamily f C j)
    | ⟨0, _⟩ => by
        -- The shifted objective inherits continuity from `f`.
        simpa [polyakAlternatingFamily, μ] using hcont.sub continuous_const
    | ⟨1, _⟩ => by
        -- The distance-to-set objective is continuous.
        simpa [polyakAlternatingFamily] using Metric.continuous_infDist_pt C
  let hconvAlt : ∀ j : Fin 2, _root_.ConvexOn ℝ Set.univ (polyakAlternatingFamily f C j)
    | ⟨0, _⟩ => by
        -- Subtracting a constant preserves convexity.
        simpa [polyakAlternatingFamily, μ, sub_eq_add_neg] using hconv.add_const (-μ)
    | ⟨1, _⟩ => by
        -- The distance-to-set function is convex on the whole space.
        simpa [polyakAlternatingFamily] using
          Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            hC_nonempty hC_closed hC_convex
  let sAlt : ∀ j : Fin 2, Selection (∂ ((polyakAlternatingFamily f C j).toEReal))
    | ⟨0, _⟩ => by
        -- The shifted objective uses the same selected subgradient field as `f`.
        simpa [polyakAlternatingFamily, μ] using shiftedObjectiveSelection f hcont hconv s μ
    | ⟨1, _⟩ => by
        -- The distance component uses the explicit normalized residual selection.
        simpa [polyakAlternatingFamily] using
          distanceToSetSelection C hC_nonempty hC_closed hC_convex
  have hf_bounded :
      ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B) := by
    -- Each textbook alternative reduces to boundedness of `f` on bounded sets.
    intro B hB
    rcases hcase with hbounded | hsuper | hfd
    · exact hbounded B hB
    · exact
        boundedOnEveryBoundedSet_of_supercoerciveConjugate_of_continuous_convex
          f hcont hconv hsuper B hB
    · letI : FiniteDimensional ℝ H := hfd
      exact boundedOnEveryBoundedSet_of_convex_finiteDimensional_local f hconv B hB
  have hboundedAlt :
      ∀ j : Fin 2, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((polyakAlternatingFamily f C j) '' B) := by
    intro j B hB
    fin_cases j
    · -- Shifting the bounded image `f '' B` by `-μ` preserves boundedness in `ℝ`.
      have hfB : Bornology.IsBounded (f '' B) := hf_bounded B hB
      rcases hfB.subset_ball μ with ⟨R, hR⟩
      refine (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℝ) R)).subset ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxball : f x ∈ Metric.ball μ R := hR (by exact ⟨x, hx, rfl⟩)
      simpa [polyakAlternatingFamily, μ, Metric.mem_ball, Real.dist_eq, sub_eq_add_neg] using hxball
    · -- The distance-to-set image is bounded by the distance to any fixed point of `C`.
      rcases hC_nonempty with ⟨z, hz⟩
      rcases hB.subset_ball z with ⟨R, hR⟩
      refine (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℝ) R)).subset ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxR : dist x z < R := by
        simpa [Metric.mem_ball] using hR hx
      have hyR : Metric.infDist x C < R := by
        exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hz) hxR
      simpa [polyakAlternatingFamily, Metric.mem_ball, Real.dist_eq,
        abs_of_nonneg (Metric.infDist_nonneg (x := x) (s := C))] using hyR
  have hcaseAlt :
      (∀ j : Fin 2, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((polyakAlternatingFamily f C j) '' B)) ∨
      (∀ j : Fin 2, Supercoercive ((polyakAlternatingFamily f C j).toEReal.asEReal∗)) ∨
      FiniteDimensional ℝ H := by
    -- Proposition 29.49 only needs the bounded-on-bounded-sets branch for this alternating pair.
    exact Or.inl hboundedAlt
  have hidx : HasWindowControl polyakAlternatingIndex := by
    refine ⟨2, by norm_num, ?_⟩
    intro j n
    fin_cases j
    · -- Every length-two window contains an even index.
      by_cases hn : n % 2 = 0
      · refine ⟨0, by norm_num, ?_⟩
        apply Fin.ext
        simp [polyakAlternatingIndex, hn]
      · refine ⟨1, by norm_num, ?_⟩
        apply Fin.ext
        have hn1 : (n + 1) % 2 = 0 := by omega
        simp [polyakAlternatingIndex, hn1]
    · -- Every length-two window also contains an odd index.
      by_cases hn : n % 2 = 0
      · refine ⟨1, by norm_num, ?_⟩
        apply Fin.ext
        have hn1 : (n + 1) % 2 = 1 := by omega
        simp [polyakAlternatingIndex, hn1]
      · refine ⟨0, by norm_num, ?_⟩
        apply Fin.ext
        have hn1 : n % 2 = 1 := by omega
        simp [polyakAlternatingIndex, hn1]
  have hlamAlt : HasUniformRelaxationMargins (polyakAlternatingRelaxation α) := by
    refine
      ⟨min hα_uniform.ε 1, min hα_uniform.δ 1,
        lt_min hα_uniform.epsilon_pos zero_lt_one,
        lt_min hα_uniform.delta_pos zero_lt_one, ?_, ?_⟩
    · -- Even steps inherit the lower margin from `α`, while odd steps equal `1`.
      intro n
      by_cases hn : n % 2 = 0
      · rw [polyakAlternatingRelaxation, if_pos hn]
        exact le_trans (min_le_left _ _) (hα_uniform.epsilon_le (n / 2))
      · rw [polyakAlternatingRelaxation, if_neg hn]
        exact min_le_right _ _
    · -- Even steps inherit the upper margin from `α`, while odd steps equal `1`.
      intro n
      by_cases hn : n % 2 = 0
      · rw [polyakAlternatingRelaxation, if_pos hn]
        have hαn := hα_uniform.le_two_sub_delta (n / 2)
        have hmin : min hα_uniform.δ 1 ≤ hα_uniform.δ := min_le_left _ _
        linarith
      · rw [polyakAlternatingRelaxation, if_neg hn]
        have hmin : min hα_uniform.δ 1 ≤ (1 : ℝ) := min_le_right _ _
        linarith
  let T :=
    controlledSubgradientProjectorSequence
      (polyakAlternatingFamily f C) hcontAlt hconvAlt hconstraint_nonempty sAlt
      polyakAlternatingIndex
  let y := relaxedOperatorIteration T (polyakAlternatingRelaxation α) x0
  let Gshift :=
    continuousConvexSubgradientProjector
      (fun z : H ↦ f z - μ) 0
      (hcont.sub continuous_const)
      (by simpa [sub_eq_add_neg] using hconv.add_const (-μ))
      hshift_nonempty
      (shiftedObjectiveSelection f hcont hconv s μ)
  have hdist_nonempty :
      (lowerLevelSet (fun z : H ↦ Metric.infDist z C).toEReal.asEReal 0).Nonempty := by
    -- The distance-to-set lower level set is nonempty because every point of `C` lies in it.
    rcases hC_nonempty with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [mem_lowerLevelSet_iff]
    simpa [Function.toEReal_apply, Metric.infDist_zero_of_mem hz]
  let Gdist :=
    continuousConvexSubgradientProjector
      (fun z : H ↦ Metric.infDist z C) 0
      (Metric.continuous_infDist_pt C)
      (Set.convexOn_univ_infDist_of_nonempty_isClosed_convex_local
        hC_nonempty hC_closed hC_convex)
      hdist_nonempty
      (distanceToSetSelection C hC_nonempty hC_closed hC_convex)
  rcases
      exists_tendsto_weakly_to_constraintSet_of_cyclic_relaxed_subgradientProjectorIterates
        (polyakAlternatingFamily f C) hcontAlt hconvAlt hconstraint_nonempty hcaseAlt
        polyakAlternatingIndex hidx (polyakAlternatingRelaxation α) hlamAlt sAlt x0
    with ⟨p, hp_constraint, hy_tendsto⟩
  have hp_argmin : p ∈ Argmin[C] f.toEReal := by
    -- Rewrite Proposition 29.49's feasibility point into the constrained argmin set.
    simpa [polyakConstraintSet_eq_argminOn (C := C) hC_closed f hargmin] using hp_constraint
  have hy_twoSucc :
      ∀ n : ℕ,
        y (2 * n + 2) =
          Gdist (y (2 * n) + α n • (Gshift (y (2 * n)) - y (2 * n))) := by
    have hT_even : ∀ n : ℕ, T (2 * n) = Gshift := by
      intro n
      -- Route correction: normalize the even controlled projector to the named shifted owner.
      unfold T controlledSubgradientProjectorSequence cyclicSubgradientProjectorFamily
      rw [polyakAlternatingIndex_even]
      rfl
    have hT_odd : ∀ n : ℕ, T (2 * n + 1) = Gdist := by
      intro n
      -- Normalize the odd controlled projector to the named distance owner.
      unfold T controlledSubgradientProjectorSequence cyclicSubgradientProjectorFamily
      rw [polyakAlternatingIndex_odd]
      rfl
    intro n
    have hy_odd :
        y (2 * n + 2) =
          y (2 * n + 1) +
            polyakAlternatingRelaxation α (2 * n + 1) •
              (T (2 * n + 1) (y (2 * n + 1)) - y (2 * n + 1)) := by
      -- Expand the odd relaxed successor before substituting the normalized operator owner.
      simpa [y] using
        (relaxedOperatorIteration_succ T (polyakAlternatingRelaxation α) x0 (2 * n + 1))
    have hy_even :
        y (2 * n + 1) =
          y (2 * n) +
            polyakAlternatingRelaxation α (2 * n) •
              (T (2 * n) (y (2 * n)) - y (2 * n)) := by
      -- Expand the preceding even relaxed successor so the Polyak parameter `α n` appears.
      simpa [y] using
        (relaxedOperatorIteration_succ T (polyakAlternatingRelaxation α) x0 (2 * n))
    have hy_even_arg :
        Gdist (y (2 * n + 1)) =
          Gdist
            (y (2 * n) +
              polyakAlternatingRelaxation α (2 * n) •
                (T (2 * n) (y (2 * n)) - y (2 * n))) :=
      congrArg Gdist hy_even
    have hstep_even_arg :
        Gdist
            (y (2 * n) +
              polyakAlternatingRelaxation α (2 * n) •
                (T (2 * n) (y (2 * n)) - y (2 * n))) =
          Gdist (y (2 * n) + α n • (Gshift (y (2 * n)) - y (2 * n))) := by
      congr 1
      rw [polyakAlternatingRelaxation_even, hT_even n]
    calc
      y (2 * n + 2)
          = y (2 * n + 1) +
              polyakAlternatingRelaxation α (2 * n + 1) •
                (T (2 * n + 1) (y (2 * n + 1)) - y (2 * n + 1)) := hy_odd
      _ = y (2 * n + 1) + (1 : ℝ) • (Gdist (y (2 * n + 1)) - y (2 * n + 1)) := by
            rw [polyakAlternatingRelaxation_odd, hT_odd n]
      _ = y (2 * n + 1) + (Gdist (y (2 * n + 1)) - y (2 * n + 1)) := by simp
      _ = Gdist (y (2 * n + 1)) := by abel
      _ =
          Gdist
            (y (2 * n) +
              polyakAlternatingRelaxation α (2 * n) •
                (T (2 * n) (y (2 * n)) - y (2 * n))) := hy_even_arg
      _ = Gdist (y (2 * n) + α n • (Gshift (y (2 * n)) - y (2 * n))) := hstep_even_arg
  let z : ℕ → H := fun n ↦ y (2 * n)
  have hz_zero : z 0 = x0 := by
    -- The even subsequence starts from the original initial point.
    simp [z, y]
  have hz_feasible : ∀ n : ℕ, z n ∈ C := by
    intro n
    induction n with
    | zero =>
        simpa [z, y] using hx0
    | succ n ih =>
        have hz_step :
            z (n + 1) =
              polyakSubgradientProjectionStep
                f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (z n) := by
          calc
            z (n + 1) = y (2 * n + 2) := by
              have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
              simp [z, htwo]
            _ = Gdist (y (2 * n) + α n • (Gshift (y (2 * n)) - y (2 * n))) := hy_twoSucc n
            _ =
              polyakSubgradientProjectionStep
                f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (y (2 * n)) := by
                  have ih' : y (2 * n) ∈ C := by simpa [z] using ih
                  simpa [Gdist, Gshift, μ, hC_nonempty] using
                    (polyakTwoStep_eq_step_of_mem_constraint
                      (C := C) hC_closed hC_convex f hcont hconv hargmin s
                      (x := y (2 * n)) ih' (α n))
            _ =
              polyakSubgradientProjectionStep
                f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (z n) := by
                  simp [z]
        rw [hz_step]
        exact
          polyakSubgradientProjectionStep_mem_constraint
            (C := C) hC_closed hC_convex hC_nonempty f hcont hconv (α n) s ih
  have hz_succ :
      ∀ n : ℕ,
        z (n + 1) =
          polyakSubgradientProjectionStep
            f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (z n) := by
    intro n
    -- Once feasibility is known, the two-step alternating recursion is exactly one Polyak step.
    calc
      z (n + 1) = y (2 * n + 2) := by
        have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
        simp [z, htwo]
      _ = Gdist (y (2 * n) + α n • (Gshift (y (2 * n)) - y (2 * n))) := hy_twoSucc n
      _ =
        polyakSubgradientProjectionStep
          f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (y (2 * n)) := by
            have hznC : y (2 * n) ∈ C := by simpa [z] using hz_feasible n
            simpa [Gdist, Gshift, μ, hC_nonempty] using
              (polyakTwoStep_eq_step_of_mem_constraint
                (C := C) hC_closed hC_convex f hcont hconv hargmin s
                (x := y (2 * n)) hznC (α n))
      _ =
        polyakSubgradientProjectionStep
          f C hC_closed hC_convex hC_nonempty hcont hconv (α n) s (z n) := by
            simp [z]
  have hz_eq :
      z =
        polyakSubgradientProjectionOrbit
          f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 := by
    -- The even subsequence satisfies the same initial value and recursion as the Polyak orbit.
    exact
      eq_polyakSubgradientProjectionOrbit_of_zero_of_succ
        f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 hz_zero hz_succ
  have hy_even_orbit :
      ∀ n : ℕ,
        y (2 * n) =
          polyakSubgradientProjectionOrbit
            f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 n := by
    intro n
    have hzn := congrArg (fun w : ℕ → H ↦ w n) hz_eq
    simpa [z] using hzn
  have hEvenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    simpa [two_mul] using Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
  have hEvenTendsto : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    hEvenMono.tendsto_atTop
  have hy_even_tendsto :
      Tendsto ((fun n : ℕ ↦ toWeakSpace ℝ H (y n)) ∘ fun n : ℕ ↦ 2 * n)
        atTop (nhds (toWeakSpace ℝ H p)) := by
    -- Weak convergence of the alternating orbit passes to its even subsequence.
    simpa using hy_tendsto.comp hEvenTendsto
  have horbit_eq_comp :
      ((fun n : ℕ ↦ toWeakSpace ℝ H (y n)) ∘ fun n : ℕ ↦ 2 * n) =
        fun n : ℕ ↦
          toWeakSpace ℝ H
            (polyakSubgradientProjectionOrbit
              f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 n) := by
    funext n
    simp [Function.comp, hy_even_orbit n]
  have horbit_tendsto :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (polyakSubgradientProjectionOrbit
              f C hC_closed hC_convex hC_nonempty hcont hconv α s x0 n))
        atTop
        (nhds (toWeakSpace ℝ H p)) := by
    rw [← horbit_eq_comp]
    exact hy_even_tendsto
  exact ⟨p, hp_argmin, by simpa [hC_nonempty] using horbit_tendsto⟩

end

end ERealFunction
