import Mathlib
import BauschkeLean.Chap02.Example_2_57
import BauschkeLean.Chap03.Proposition_3_30
import BauschkeLean.Chap17.Example_17_8
import BauschkeLean.Chap12.Corollary_12_18
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.GammaZeroConjugate

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped ContinuousLinearMap Gradient InnerProductSpace

universe u

namespace ContinuousLinearMap

noncomputable section

variable {H : Type u}

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.36 records convex-analytic properties of the quadratic potential
  `q[A]` and its Fenchel conjugate.
- `core/canonical`: the owner abstractions are the chapter-level quadratic-potential owner `q[A]`
  and the canonical `Γ₀(H)`-valued conjugate owner `q⋆[A, hA_mono]`.
- `bridge/view`: this file should therefore use the existing conjugate owner from
  `GammaZeroConjugate`, not a parallel local `quadraticPotentialConjugate` wrapper.
-/

section QuadraticPotential

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 17 36: monotonicity of `A` controls the Jensen gap of the quadratic
potential `q[A]` on affine combinations. -/
lemma quadraticPotential_convex_combo_le_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x y : H) :
    q[A] (a • x + (1 - a) • y) ≤ a * q[A] x + (1 - a) * q[A] y := by
  -- Expand the quadratic potential at the convex combination and isolate the monotone defect.
  have hmono : 0 ≤ ⟪x - y, A (x - y)⟫_ℝ := by
    simpa [real_inner_comm] using hA_mono (x - y)
  have hdecomp :
      a * q[A] x + (1 - a) * q[A] y - q[A] (a • x + (1 - a) • y) =
        (1 / 2 : ℝ) * (a * (1 - a)) * ⟪x - y, A (x - y)⟫_ℝ := by
    simp [quadraticPotential_apply, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, sub_eq_add_neg]
    ring
  have hab_nonneg : 0 ≤ a * (1 - a) := mul_nonneg ha0 (sub_nonneg.mpr ha1)
  have hgap_nonneg :
      0 ≤ a * q[A] x + (1 - a) * q[A] y - q[A] (a • x + (1 - a) • y) := by
    rw [hdecomp]
    exact mul_nonneg (mul_nonneg (by norm_num) hab_nonneg) hmono
  linarith

/-- Helper for Proposition 17 36: the quadratic potential has Fréchet derivative represented by
the canonical bilinear-form differential at `x`. -/
lemma quadraticPotential_hasFDerivAt
    (A : H →L[ℝ] H) (x : H) :
    HasFDerivAt (q[A])
      ((1 / 2 : ℝ) •
        ((((A.toSesqForm.precompR H) x) (ContinuousLinearMap.id ℝ H) +
            ((A.toSesqForm.precompL H) (ContinuousLinearMap.id ℝ H)) x))) x := by
  have hquad : HasFDerivAt (fun y : H ↦ A.toSesqForm y y)
      ((((A.toSesqForm.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((A.toSesqForm.precompL H) (ContinuousLinearMap.id ℝ H)) x)) x := by
    simpa using
      (A.toSesqForm.hasFDerivAt_of_bilinear
        (ContinuousLinearMap.id ℝ H).hasFDerivAt
        (ContinuousLinearMap.id ℝ H).hasFDerivAt)
  -- Differentiate the diagonal bilinear form first, then scale by `1 / 2`.
  convert hquad.const_smul (1 / 2 : ℝ) using 1

-- Proof sketch: `q[A]` is continuous as a quadratic form built from a bounded
-- linear operator, so its `EReal` coercion is lower semicontinuous. Convexity is the monotone
-- quadratic-form criterion from Example 17.8, with the scalar factor `1 / 2` preserving convexity.
/-- The quadratic potential of a monotone bounded operator, viewed as a `]-∞,+∞]`-valued
function, belongs to `Γ₀(H)`. -/
theorem quadraticPotential_mem_gammaZero_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    (q[A]).toEReal ∈ Γ₀(H) := by
  have hcont : Continuous (q[A]) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (quadraticPotential_hasFDerivAt A x).continuousAt
  have hconv : ConvexOn ℝ Set.univ (q[A]) := by
    -- Convert the Jensen-gap estimate into the standard `ConvexOn` owner on `Set.univ`.
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb_eq : b = 1 - a := by
      linarith
    have ha1 : a ≤ 1 := by
      linarith
    rw [hb_eq]
    exact quadraticPotential_convex_combo_le_of_isMonotone A hA_mono ha ha1 x y
  exact real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (q[A]) hcont hconv

/- Lean cannot parse the textbook subscripted star `q_A^*`, so we use the bracketed surface
`q⋆[A, hA_mono]` for the canonical `Γ₀(H)`-valued conjugate of `q_A`. -/
scoped notation:max "q⋆[" A:max ", " hA_mono:max "]" =>
  (Function.toEReal (q[A]))∗[quadraticPotential_mem_gammaZero_of_isMonotone A hA_mono]

-- Proof sketch: rewrite `q[A]` as the positive scalar multiple
-- `(1 / 2) • (fun x ↦ ⟪x, A x⟫_ℝ)` and apply the monotone quadratic-form criterion from
-- Example 17.8.
/-- Proposition 17 36 (1): clause (i). If `A` is monotone, then its quadratic potential
`q_A(x) = (1 / 2) ⟪x, A x⟫_ℝ` is convex on all of `H`. -/
theorem quadraticPotential_convexOn_univ_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    ConvexOn ℝ Set.univ (q[A]) := by
  -- Convert the Jensen-gap estimate into the standard `ConvexOn` owner on `Set.univ`.
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  rw [hb_eq]
  exact quadraticPotential_convex_combo_le_of_isMonotone A hA_mono ha ha1 x y

-- Proof sketch: `q[A]` is a continuous bilinear expression in `x` built from the
-- continuous linear map `A`.
/-- Proposition 17.36 (2): clause (i). The quadratic potential `q_A` is continuous. -/
theorem quadraticPotential_continuous
    (A : H →L[ℝ] H) :
    Continuous (q[A]) := by
  -- Fréchet differentiability at every point gives continuity pointwise.
  rw [continuous_iff_continuousAt]
  intro x
  exact (quadraticPotential_hasFDerivAt A x).continuousAt

-- Proof sketch: differentiate the quadratic form using Example 2.57, specialized to the affine
-- term `u = 0` and then scaled by `1 / 2`.
/-- Proposition 17.36 (3): clause (i). The quadratic potential `q_A` is Fréchet differentiable on
`H`. -/
theorem quadraticPotential_differentiable
    (A : H →L[ℝ] H) :
    Differentiable ℝ (q[A]) := by
  -- Reuse the pointwise derivative formula established above.
  intro x
  exact (quadraticPotential_hasFDerivAt A x).differentiableAt

end QuadraticPotential

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Example 2.57 gives the gradient of `x ↦ ⟪x, A x⟫_ℝ` as
-- `x ↦ (A + A.adjoint) x`; divide by `2` and use self-adjointness to simplify to `A x`.
/-- Proposition 17.36 (4): clause (i). If `A` is self-adjoint, then the gradient of `q_A` is the
operator `A`. -/
theorem gradient_quadraticPotential_eq_of_isSelfAdjoint
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) :
    ∇ (q[A]) = A := by
  have hgrad : ∀ x : H, HasGradientAt (q[A]) (A x) x := by
    intro x
    have hscaled :
        HasGradientAt
          (fun y : H ↦ (1 / 2 : ℝ) * quadratic_affine_functional A 0 y)
          ((1 / 2 : ℝ) • ((A + A.adjoint) x)) x := by
      have hquad :
          HasGradientAt (quadratic_affine_functional A 0) ((A + A.adjoint) x) x := by
        simpa [quadratic_affine_functional] using quadratic_affine_functional_hasGradientAt A 0 x
      rw [hasGradientAt_iff_hasFDerivAt]
      convert hquad.hasFDerivAt.const_smul (1 / 2 : ℝ) using 1
      · ext y
        simp
    have hq :
        HasGradientAt (q[A]) ((1 / 2 : ℝ) • ((A + A.adjoint) x)) x := by
      convert hscaled using 1
      ext y
      rw [ContinuousLinearMap.quadraticPotential_apply, quadratic_affine_functional]
      simpa using (real_inner_comm y (A y)).symm
    have hq' :
        HasGradientAt (q[A]) ((((1 / 2 : ℝ) + (1 / 2 : ℝ)) • A x)) x := by
      convert hq using 1
      simp [ContinuousLinearMap.add_apply, hA_self.adjoint_eq, smul_add, ← add_smul]
    convert hq' using 1
    norm_num
  exact gradient_eq hgrad

-- Proof sketch: use the identities `A A⁺ = P_(range A)` and `(A⁺)⁺ = A` for closed-range
-- self-adjoint operators, then rewrite the quadratic form of `A⁺` at `u` as the quadratic form of
-- `A` at `A⁺ u`.
/-- Proposition 17.36 (5): clause (ii), first identity. For a closed-range self-adjoint operator,
the quadratic potential of `A⁺` is `q_A ∘ A⁺`. -/
theorem quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) (hA_closed : IsClosed (A.range : Set H)) :
    q[A⁺[hA_closed]] = (q[A]) ∘ A⁺[hA_closed] :=
  by
  ext u
  let m : H := A⁺[hA_closed] u
  have hproj : A m = closedRangeProjection A hA_closed u := by
    -- The Moore-Penrose projection identity identifies the range component of `u`.
    simpa [m] using apply_moorePenroseInverse_eq_rangeProjection A hA_closed u
  have hm_mem_adjoint : m ∈ (A.adjoint.range : Set H) := by
    rw [← range_moorePenroseInverse_eq_adjoint_range A hA_closed]
    refine ⟨u, ?_⟩
    simp [m]
  have hm_mem : m ∈ (A.range : Set H) := by
    simpa [hA_self.adjoint_eq] using hm_mem_adjoint
  have hres_orth : u - A m ∈ (A.range : Submodule ℝ H)ᗮ := by
    -- The projection residual is orthogonal to the closed range.
    letI : CompleteSpace A.range := hA_closed.completeSpace_coe
    have horth :
        u - closedRangeProjection A hA_closed u ∈ (A.range : Submodule ℝ H)ᗮ := by
      change u - A.range.starProjection u ∈ (A.range : Submodule ℝ H)ᗮ
      exact A.range.sub_starProjection_mem_orthogonal u
    rw [hproj]
    exact horth
  have hinner_zero : ⟪u - A m, m⟫_ℝ = 0 := by
    simpa [real_inner_comm] using
      (Submodule.mem_orthogonal' (A.range : Submodule ℝ H) (u - A m)).1 hres_orth m hm_mem
  have hinner_eq : ⟪u, m⟫_ℝ = ⟪A m, m⟫_ℝ := by
    have hsub : ⟪u, m⟫_ℝ - ⟪A m, m⟫_ℝ = 0 := by
      simpa [inner_sub_left] using hinner_zero
    exact sub_eq_zero.mp hsub
  -- Replace the first pairing by the projected range component, then commute the inner product.
  calc
    q[A⁺[hA_closed]] u = (1 / 2 : ℝ) * ⟪u, m⟫_ℝ := by simp [quadraticPotential_apply, m]
    _ = (1 / 2 : ℝ) * ⟪A m, m⟫_ℝ := by rw [hinner_eq]
    _ = (1 / 2 : ℝ) * ⟪m, A m⟫_ℝ := by rw [real_inner_comm]
    _ = q[A] m := by simp [quadraticPotential_apply, m]
    _ = ((q[A]) ∘ A⁺[hA_closed]) u := by rfl

omit [CompleteSpace H] in
/-- Helper for Proposition 17 36: the quadratic potential of a monotone operator is pointwise
nonnegative. -/
lemma quadraticPotential_nonneg_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (x : H) :
    0 ≤ q[A] x := by
  -- Monotonicity gives nonnegativity of the diagonal quadratic form, and the factor `1 / 2`
  -- preserves the sign.
  have hmono : 0 ≤ ⟪x, A x⟫_ℝ := by
    simpa [real_inner_comm] using hA_mono x
  simp [quadraticPotential_apply]
  nlinarith

/-- Helper for Proposition 17 36: for a self-adjoint operator, the quadratic potential is constant
along kernel directions. -/
lemma quadraticPotential_eq_of_add_mem_ker
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) {x k : H} (hk : k ∈ A.ker) :
    q[A] (x + k) = q[A] x := by
  -- The kernel component is annihilated by `A`, and self-adjointness kills the remaining mixed
  -- term.
  have hk_zero : A k = 0 := (LinearMap.mem_ker).1 hk
  have hcross : ⟪k, A x⟫_ℝ = 0 := by
    calc
      ⟪k, A x⟫_ℝ = ⟪A k, x⟫_ℝ := by
        simpa [hA_self.adjoint_eq] using (ContinuousLinearMap.adjoint_inner_right A k x)
      _ = 0 := by simp [hk_zero]
  calc
    q[A] (x + k) = (1 / 2 : ℝ) * ⟪x + k, A (x + k)⟫_ℝ := by
      simp [quadraticPotential_apply]
    _ = (1 / 2 : ℝ) * ⟪x + k, A x⟫_ℝ := by
      simp [map_add, hk_zero]
    _ = (1 / 2 : ℝ) * (⟪x, A x⟫_ℝ + ⟪k, A x⟫_ℝ) := by
      rw [inner_add_left]
    _ = (1 / 2 : ℝ) * ⟪x, A x⟫_ℝ := by rw [hcross, add_zero]
    _ = q[A] x := by simp [quadraticPotential_apply]

/-- Helper for Proposition 17 36: the Moore-Penrose inverse vanishes on `ker A` for a
self-adjoint closed-range operator. -/
lemma moorePenroseInverse_eq_zero_of_mem_ker_of_isSelfAdjoint
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) (hA_closed : IsClosed (A.range : Set H))
    {k : H} (hk : k ∈ A.ker) :
    A⁺[hA_closed] k = 0 := by
  have hk_orth : k ∈ A.rangeᗮ := by
    simpa [ContinuousLinearMap.orthogonal_range, hA_self.adjoint_eq] using hk
  have himage_zero : A (A⁺[hA_closed] k) = 0 := by
    calc
      A (A⁺[hA_closed] k) = closedRangeProjection A hA_closed k := by
        simpa using apply_moorePenroseInverse_eq_rangeProjection A hA_closed k
      _ = 0 := closedRangeProjection_eq_zero_of_mem_orthogonalRange A hA_closed hk_orth
  have hmem_ker : A⁺[hA_closed] k ∈ A.ker := by
    exact (LinearMap.mem_ker).2 himage_zero
  have hmem_orth : A⁺[hA_closed] k ∈ A.kerᗮ :=
    moorePenroseInverse_mem_orthogonalKer A hA_closed k
  have hinner_zero :
      ⟪A⁺[hA_closed] k, A⁺[hA_closed] k⟫_ℝ = 0 := by
    exact (Submodule.mem_orthogonal' A.ker (A⁺[hA_closed] k)).1 hmem_orth
      (A⁺[hA_closed] k) hmem_ker
  exact inner_self_eq_zero.mp hinner_zero

/-- Helper for Proposition 17 36: on a range point `u = A z`, the Fenchel defect of the quadratic
potential is the translated negative quadratic potential at `x - z`. -/
lemma pairing_sub_quadraticPotential_eq_quadraticPotential_sub_of_eq_apply
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) {u z : H} (hu : u = A z) (x : H) :
    ⟪x, u⟫_ℝ - q[A] x = q[A] z - q[A] (x - z) := by
  -- Route correction: the range-side conjugate proof needs the source square-completion identity
  -- as a standalone rewrite instead of expanding it repeatedly inside the supremum.
  subst hu
  have hsym : ⟪x, A z⟫_ℝ = ⟪A x, z⟫_ℝ := by
    simpa [hA_self.adjoint_eq] using (ContinuousLinearMap.adjoint_inner_right A x z)
  have hsym' : ⟪z, A x⟫_ℝ = ⟪x, A z⟫_ℝ := by
    calc
      ⟪z, A x⟫_ℝ = ⟪A z, x⟫_ℝ := by
        simpa [hA_self.adjoint_eq] using (ContinuousLinearMap.adjoint_inner_right A z x)
      _ = ⟪x, A z⟫_ℝ := by rw [real_inner_comm]
  calc
    ⟪x, A z⟫_ℝ - q[A] x = ⟪A x, z⟫_ℝ - q[A] x := by rw [hsym]
    _ = q[A] z - q[A] (x - z) := by
      simp [quadraticPotential_apply, map_sub, inner_sub_left, inner_sub_right, real_inner_comm,
        hsym']
      ring

/-- Helper for Proposition 17 36: on the range of a monotone self-adjoint closed-range operator,
the conjugate of `q[A]` equals the quadratic potential of `A⁺`. -/
lemma quadraticPotentialConjugate_apply_eq_moorePenroseInverse_of_mem_range
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) {u : H} (hu : u ∈ A.range) :
    (q⋆[A, hA_mono]).asEReal u = (q[A⁺[hA_closed]]).toEReal.asEReal u := by
  let m : H := A⁺[hA_closed] u
  have hm_apply : A m = u := by
    calc
      A m = closedRangeProjection A hA_closed u := by
        simpa [m] using apply_moorePenroseInverse_eq_rangeProjection A hA_closed u
      _ = u := closedRangeProjection_eq_self_of_mem_range A hA_closed hu
  have hupper :
      (q⋆[A, hA_mono]).asEReal u ≤ (q[A⁺[hA_closed]]).toEReal.asEReal u := by
    change (q[A]).toEReal.asEReal∗ u ≤ (q[A⁺[hA_closed]]).toEReal.asEReal u
    rw [conjugate_apply]
    refine iSup_le ?_
    intro x
    have hdefect :
        ⟪x, u⟫_ℝ - q[A] x = q[A] m - q[A] (x - m) :=
      pairing_sub_quadraticPotential_eq_quadraticPotential_sub_of_eq_apply A hA_self hm_apply.symm x
    have hnonneg : 0 ≤ q[A] (x - m) :=
      quadraticPotential_nonneg_of_isMonotone A hA_mono (x - m)
    have hreal :
        ⟪x, u⟫_ℝ - q[A] x ≤ q[A] m := by
      rw [hdefect]
      linarith
    have hereal :
        (((⟪x, u⟫_ℝ - q[A] x : ℝ) : EReal)) ≤ ((q[A] m : ℝ) : EReal) := by
      exact_mod_cast hreal
    calc
      (((⟪x, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x)
          = (((⟪x, u⟫_ℝ - q[A] x : ℝ) : EReal)) := by
              simp [Function.asEReal_apply, Function.toEReal_apply]
      _ ≤ ((q[A] m : ℝ) : EReal) := hereal
      _ = (q[A⁺[hA_closed]]).toEReal.asEReal u := by
            rw [quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse
              A hA_self hA_closed]
            simp [m]
  have hlower :
      (q[A⁺[hA_closed]]).toEReal.asEReal u ≤ (q⋆[A, hA_mono]).asEReal u := by
    change (q[A⁺[hA_closed]]).toEReal.asEReal u ≤ (q[A]).toEReal.asEReal∗ u
    rw [conjugate_apply]
    have hm_eval :
        ((q[A⁺[hA_closed]]).toEReal.asEReal u : EReal) =
          (((⟪m, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal m) := by
      have hreal :
          q[A⁺[hA_closed]] u = ⟪m, u⟫_ℝ - q[A] m := by
        rw [quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse A hA_self hA_closed]
        rw [Function.comp_apply, quadraticPotential_apply, hm_apply]
        ring
      calc
        (q[A⁺[hA_closed]]).toEReal.asEReal u = (((q[A⁺[hA_closed]] u : ℝ) : EReal)) := by
          simp [Function.asEReal_apply, Function.toEReal_apply]
        _ = (((⟪m, u⟫_ℝ - q[A] m : ℝ) : EReal)) := by
          exact_mod_cast hreal
        _ = (((⟪m, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal m) := by
          rw [Function.asEReal_apply, Function.toEReal_apply, quadraticPotential_apply,
            EReal.coe_mul]
          rw [← EReal.coe_mul, ← EReal.coe_sub]
    calc
      (q[A⁺[hA_closed]]).toEReal.asEReal u
          = (((⟪m, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal m) := hm_eval
      _ ≤ ⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x) := by
            exact le_iSup
              (fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x)) m
  exact le_antisymm hupper hlower

/-- Helper for Proposition 17 36: off the range of a monotone self-adjoint closed-range operator,
the conjugate of `q[A]` is infinite. -/
lemma quadraticPotentialConjugate_apply_eq_top_of_not_mem_range
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) {u : H} (hu : u ∉ A.range) :
    (q⋆[A, hA_mono]).asEReal u = ⊤ := by
  let k : H := u - closedRangeProjection A hA_closed u
  have hk_orth : k ∈ A.rangeᗮ := by
    letI : CompleteSpace A.range := hA_closed.completeSpace_coe
    change u - A.range.starProjection u ∈ (A.range : Submodule ℝ H)ᗮ
    exact A.range.sub_starProjection_mem_orthogonal u
  have hk_mem : k ∈ A.ker := by
    simpa [k, ContinuousLinearMap.orthogonal_range, hA_self.adjoint_eq] using hk_orth
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hu_eq : u = closedRangeProjection A hA_closed u := by
      rw [← sub_eq_zero]
      simpa [k] using hk0
    exact hu (hu_eq.symm ▸ closedRangeProjection_mem_range A hA_closed u)
  have hinner_pos : 0 < ⟪k, u⟫_ℝ := by
    have hproj_mem : closedRangeProjection A hA_closed u ∈ A.range :=
      closedRangeProjection_mem_range A hA_closed u
    have horth_zero : ⟪k, closedRangeProjection A hA_closed u⟫_ℝ = 0 := by
      exact (Submodule.mem_orthogonal' (A.range : Submodule ℝ H) k).1 hk_orth
        (closedRangeProjection A hA_closed u) hproj_mem
    have hself :
        ⟪k, u⟫_ℝ = ⟪k, k⟫_ℝ := by
      calc
        ⟪k, u⟫_ℝ = ⟪k, k + closedRangeProjection A hA_closed u⟫_ℝ := by
          simp [k, sub_eq_add_neg, add_comm, add_left_comm]
        _ = ⟪k, k⟫_ℝ + ⟪k, closedRangeProjection A hA_closed u⟫_ℝ := by
          rw [inner_add_right]
        _ = ⟪k, k⟫_ℝ := by rw [horth_zero, add_zero]
    rw [hself]
    have hnorm : 0 < ‖k‖ ^ (2 : ℕ) := by
      have hk_norm : 0 < ‖k‖ := norm_pos_iff.mpr hk_ne
      positivity
    simpa [real_inner_self_eq_norm_sq] using hnorm
  change (q[A]).toEReal.asEReal∗ u = ⊤
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  let t : ℝ := |M| / ⟪k, u⟫_ℝ + 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hM_lt : M < t * ⟪k, u⟫_ℝ := by
    have hden_pos : 0 < ⟪k, u⟫_ℝ := hinner_pos
    have hEq : t * ⟪k, u⟫_ℝ = |M| + ⟪k, u⟫_ℝ := by
      dsimp [t]
      field_simp [hden_pos.ne']
    rw [hEq]
    have hM_le : M ≤ |M| := le_abs_self M
    linarith
  have hk_quad_zero : q[A] (t • k) = 0 := by
    have hk_zero : A k = 0 := (LinearMap.mem_ker).1 hk_mem
    simp [quadraticPotential_apply, hk_zero]
  have hterm :
      ((M : ℝ) : EReal) <
        ((((⟪t • k, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal (t • k))) := by
    have hinner_t : ⟪t • k, u⟫_ℝ = t * ⟪k, u⟫_ℝ := by
      simpa using inner_smul_left k u t
    have hterm_eq :
        ((((⟪t • k, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal (t • k))) =
          ((t * ⟪k, u⟫_ℝ : ℝ) : EReal) := by
      rw [Function.asEReal_apply, Function.toEReal_apply, hinner_t, hk_quad_zero]
      simp
    calc
      ((M : ℝ) : EReal) < ((t * ⟪k, u⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hM_lt
      _ = (((⟪t • k, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal (t • k)) := by
        rw [hterm_eq]
  exact lt_of_lt_of_le hterm <|
    le_iSup (fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x)) (t • k)

-- Proof sketch: outside `range A`, the conjugate of `q_A` is infinite by translation along
-- `ker A`; on `range A`, write `u = A z` and apply the Fenchel--Young equality together with the
-- projection identity `A A⁺ = P_(range A)`.
/-- Proposition 17.36 (7): clause (iii). For a monotone self-adjoint closed-range operator, the
Fenchel conjugate of `q_A` is `ι_(range A) + q_{A⁺}`. -/
theorem quadraticPotentialConjugate_eq_setIndicator_range_add_moorePenroseInverse
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q⋆[A, hA_mono]).asEReal =
      (ι[(A.range : Set H)]).asEReal +
        (q[A⁺[hA_closed]]).toEReal.asEReal := by
  ext u
  by_cases hu : u ∈ A.range
  · have hconj :=
      quadraticPotentialConjugate_apply_eq_moorePenroseInverse_of_mem_range
        A hA_mono hA_self hA_closed hu
    calc
      (q⋆[A, hA_mono]).asEReal u = (q[A⁺[hA_closed]]).toEReal.asEReal u := hconj
      _ = ((ι[(A.range : Set H)]).asEReal + (q[A⁺[hA_closed]]).toEReal.asEReal) u := by
            simp [indicator_apply, hu]
  · have hconj :=
      quadraticPotentialConjugate_apply_eq_top_of_not_mem_range
        A hA_mono hA_self hA_closed hu
    have hfinite : (q[A⁺[hA_closed]]).toEReal.asEReal u ≠ ⊥ := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using
        (EReal.coe_ne_bot (q[A⁺[hA_closed]] u))
    calc
      (q⋆[A, hA_mono]).asEReal u = ⊤ := hconj
      _ = ((ι[(A.range : Set H)]).asEReal + (q[A⁺[hA_closed]]).toEReal.asEReal) u := by
            rw [Pi.add_apply]
            have hind : (ι[(A.range : Set H)]).asEReal u = ⊤ := by
              simp [Function.asEReal_apply, indicator_apply, hu]
            rw [hind]
            exact (EReal.top_add_of_ne_bot hfinite).symm

-- Proof sketch: combine the range-indicator formula for `q_A^*` with the kernel/range
-- decomposition `u = (u - A A⁺ u) + A A⁺ u`; the kernel component is absorbed by `ι_(ker A)`,
-- while the range component is evaluated by clause (iii).
/-- Proposition 17.36 (6): clause (ii), second identity. For a monotone self-adjoint
closed-range operator, `q_{A⁺}` is the infimal convolution of `ι_(ker A)` with `q_A^*`. -/
theorem quadraticPotential_moorePenroseInverse_eq_setIndicator_ker_infimalConvolution_conjugate
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q[A⁺[hA_closed]]).toEReal.asEReal =
      ι[(A.ker : Set H)] □ q⋆[A, hA_mono] := by
  ext u
  rw [infimalConvolution_apply]
  let k : H := u - A (A⁺[hA_closed] u)
  have hk_orth : k ∈ A.rangeᗮ := by
    letI : CompleteSpace A.range := hA_closed.completeSpace_coe
    have horth :
        u - closedRangeProjection A hA_closed u ∈ (A.range : Submodule ℝ H)ᗮ := by
      change u - A.range.starProjection u ∈ (A.range : Submodule ℝ H)ᗮ
      exact A.range.sub_starProjection_mem_orthogonal u
    have hproj :
        A (A⁺[hA_closed] u) = closedRangeProjection A hA_closed u := by
      simpa using apply_moorePenroseInverse_eq_rangeProjection A hA_closed u
    have hproj' :
        A (moorePenroseInverse A hA_closed u) = closedRangeProjection A hA_closed u := by
      simpa using hproj
    change u - A (moorePenroseInverse A hA_closed u) ∈ (A.range : Submodule ℝ H)ᗮ
    rw [hproj']
    exact horth
  have hk_mem : k ∈ A.ker := by
    simpa [k, ContinuousLinearMap.orthogonal_range, hA_self.adjoint_eq] using hk_orth
  have hk_range : u - k ∈ A.range := by
    refine ⟨A⁺[hA_closed] u, ?_⟩
    simp [k]
  have hsame_of_mem_ker {y : H} (hy : y ∈ A.ker) :
      q[A⁺[hA_closed]] (u - y) = q[A⁺[hA_closed]] u := by
    have hsub :
        A⁺[hA_closed] (u - y) = A⁺[hA_closed] u := by
      rw [map_sub]
      simp [moorePenroseInverse_eq_zero_of_mem_ker_of_isSelfAdjoint A hA_self hA_closed hy]
    calc
      q[A⁺[hA_closed]] (u - y) = (q[A] ∘ A⁺[hA_closed]) (u - y) := by
        rw [quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse A hA_self hA_closed]
      _ = q[A] (A⁺[hA_closed] u) := by
        simp [Function.comp_apply, hsub]
      _ = (q[A] ∘ A⁺[hA_closed]) u := by rfl
      _ = q[A⁺[hA_closed]] u := by
        rw [quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse A hA_self hA_closed]
  have hleft :
      (q[A⁺[hA_closed]]).toEReal.asEReal u ≤
        ⨅ y : H, ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) +
          (q⋆[A, hA_mono]).asEReal (u - y) := by
    refine le_iInf ?_
    intro y
    by_cases hy : y ∈ A.ker
    · by_cases hrange : u - y ∈ A.range
      · have hfull :=
          congrFun
            (quadraticPotentialConjugate_eq_setIndicator_range_add_moorePenroseInverse
              A hA_mono hA_self hA_closed) (u - y)
        have hconj :
            (q⋆[A, hA_mono]).asEReal (u - y) =
              (q[A⁺[hA_closed]]).toEReal.asEReal (u - y) := by
          simpa [indicator_apply, hrange] using hfull
        calc
          (q[A⁺[hA_closed]]).toEReal.asEReal u
              = (q[A⁺[hA_closed]]).toEReal.asEReal (u - y) := by
                  simpa [Function.asEReal_apply, Function.toEReal_apply] using
                    congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) (hsame_of_mem_ker hy).symm
          _ ≤ ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) +
                (q⋆[A, hA_mono]).asEReal (u - y) := by
                  rw [hconj]
                  simp [indicator_apply, hy]
      · have hfull :=
          congrFun
            (quadraticPotentialConjugate_eq_setIndicator_range_add_moorePenroseInverse
              A hA_mono hA_self hA_closed) (u - y)
        have hconj : (q⋆[A, hA_mono]).asEReal (u - y) = ⊤ := by
          simpa [indicator_apply, hrange] using hfull
        rw [hconj]
        simp [indicator_apply, hy]
    · have hconj_ne_bot : (q⋆[A, hA_mono]).asEReal (u - y) ≠ ⊥ := by
        exact ne_of_gt (q⋆[A, hA_mono] (u - y)).2
      have htop :
          ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) +
              (q⋆[A, hA_mono]).asEReal (u - y) = ⊤ := by
        have hind : ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
          simp [indicator_apply, hy]
        rw [hind]
        exact EReal.top_add_of_ne_bot hconj_ne_bot
      rw [htop]
      exact le_top
  have hright :
      (⨅ y : H, ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) +
          (q⋆[A, hA_mono]).asEReal (u - y)) ≤
        (q[A⁺[hA_closed]]).toEReal.asEReal u := by
    have hfull :=
      congrFun
        (quadraticPotentialConjugate_eq_setIndicator_range_add_moorePenroseInverse
          A hA_mono hA_self hA_closed) (u - k)
    have hconj :
        (q⋆[A, hA_mono]).asEReal (u - k) =
          (q[A⁺[hA_closed]]).toEReal.asEReal (u - k) := by
      simpa [indicator_apply, hk_range] using hfull
    calc
      (⨅ y : H, ((ι[(A.ker : Set H)] y : Set.Ioi (⊥ : EReal)) : EReal) +
          (q⋆[A, hA_mono]).asEReal (u - y))
          ≤ ((ι[(A.ker : Set H)] k : Set.Ioi (⊥ : EReal)) : EReal) +
              (q⋆[A, hA_mono]).asEReal (u - k) := iInf_le _ k
      _ = (q[A⁺[hA_closed]]).toEReal.asEReal (u - k) := by
            rw [hconj]
            simp [indicator_apply, hk_mem]
      _ = (q[A⁺[hA_closed]]).toEReal.asEReal u := by
            simpa [Function.asEReal_apply, Function.toEReal_apply] using
              congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) (hsame_of_mem_ker hk_mem)
  exact le_antisymm hleft hright

-- Proof sketch: evaluate the identity from clause (iii) at `A x`, where the range indicator
-- vanishes, then use clause (ii) together with `(A⁺)⁺ = A` for closed-range operators.
/-- Proposition 17.36 (8): clause (iv). For a monotone self-adjoint closed-range operator, the
Fenchel conjugate of `q_A` composed with `A` is `q_A`. -/
theorem conjugate_quadraticPotential_comp_eq_quadraticPotential
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q⋆[A, hA_mono]).asEReal ∘ A = (q[A]).toEReal.asEReal := by
  funext x
  let m : H := A⁺[hA_closed] (A x)
  have hm_eq :
      m = closedRangeProjection (adjoint A)
        (adjoint_range_isClosed_of_isClosed_range A hA_closed) x := by
    simpa [m] using apply_moorePenroseInverse_comp_eq_adjointRangeProjection A hA_closed x
  have hm_range : m = closedRangeProjection A hA_closed x := by
    simpa [hA_self.adjoint_eq] using hm_eq
  have hdiff_orth : x - m ∈ A.rangeᗮ := by
    letI : CompleteSpace A.range := hA_closed.completeSpace_coe
    have horth : x - A.range.starProjection x ∈ (A.range : Submodule ℝ H)ᗮ := by
      exact A.range.sub_starProjection_mem_orthogonal x
    change x - m ∈ (A.range : Submodule ℝ H)ᗮ
    rw [hm_range]
    rw [show closedRangeProjection A hA_closed x = A.range.starProjection x by rfl]
    exact horth
  have hdiff_ker : x - m ∈ A.ker := by
    simpa [ContinuousLinearMap.orthogonal_range, hA_self.adjoint_eq] using hdiff_orth
  have hq :
      q[A] x = q[A] m := by
    simpa [m, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (quadraticPotential_eq_of_add_mem_ker A hA_self (x := m) (k := x - m) hdiff_ker)
  calc
    (q⋆[A, hA_mono]).asEReal (A x)
        = (q[A⁺[hA_closed]]).toEReal.asEReal (A x) := by
            exact quadraticPotentialConjugate_apply_eq_moorePenroseInverse_of_mem_range
              A hA_mono hA_self hA_closed ⟨x, rfl⟩
    _ = q[A] m := by
          rw [quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse
            A hA_self hA_closed]
          simp [m]
    _ = (q[A]).toEReal.asEReal x := by
          simpa [Function.asEReal_apply, Function.toEReal_apply] using
            congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hq.symm

end Hilbert

end

end ContinuousLinearMap
