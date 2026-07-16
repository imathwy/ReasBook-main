import Mathlib
import Mathlib.Geometry.Manifold.Immersion
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Example_1_9
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_07.Problem_1_8
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_6
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Lemma_4_21

-- Declarations for this item will be appended below by the statement pipeline.

open Topology Manifold Filter
open scoped ContDiff FourierTransform Manifold Matrix Torus

noncomputable section

local notation "T2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)
local notation "R2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓘(ℝ))

-- The source curve uses the analyst-normalized circle character `t ↦ e^{2π i t}`, which mathlib
-- provides canonically as `Real.fourierChar` with notation `𝐞`.

/-- The torus curve `t ↦ (e^{2π i t}, e^{2π i α t})`, expressed in the project model
`𝕋² = S¹ × S¹`. -/
def denseTorusCurve (α : ℝ) : ℝ → 𝕋^{2} :=
  fun t ↦ ![𝐞 t, 𝐞 (α * t)]

/-- Helper for Example 4.20: the Fourier character has period `1` on integer shifts. -/
lemma fourierChar_int_eq_one (n : ℤ) : 𝐞 (n : ℝ) = 1 := by
  -- Rewrite the Fourier character as the circle exponential at an integral multiple of `2π`.
  rw [Real.fourierChar_apply']
  simpa [mul_comm, mul_left_comm, mul_assoc] using Circle.exp_int_mul_two_pi n

/-- Helper for Example 4.20: two Fourier-character values agree exactly when their arguments differ
by an integer. -/
lemma fourierChar_eq_iff_exists_int {x y : ℝ} :
    𝐞 x = 𝐞 y ↔ ∃ m : ℤ, x = y + m := by
  constructor
  · intro hxy
    rw [Real.fourierChar_apply', Real.fourierChar_apply'] at hxy
    rcases Circle.exp_eq_exp.mp hxy with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  · rintro ⟨m, rfl⟩
    -- Integer shifts disappear because the circle exponential is `2π`-periodic.
    rw [Real.fourierChar_apply', Real.fourierChar_apply']
    exact (Circle.exp_eq_exp).2 ⟨m, by ring⟩

/-- Helper for Example 4.20: the analyst-normalized Fourier character is surjective onto the
circle. -/
-- TODO(Example 4.20): derive surjectivity from `Circle.exp_surjective` by rescaling angles by
-- `2 * π`.
lemma fourierChar_surjective : Function.Surjective (fun t : ℝ ↦ 𝐞 t) := by
  intro z
  rcases Circle.exp_surjective z with ⟨s, rfl⟩
  refine ⟨s / (2 * Real.pi), ?_⟩
  -- Rescaling the usual angle parameter by `2π` matches the normalized Fourier character.
  have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    𝐞 (s / (2 * Real.pi)) = Circle.exp (2 * Real.pi * (s / (2 * Real.pi))) := by
      rw [Real.fourierChar_apply']
    _ = Circle.exp s := by
      congr 1
      field_simp [htwo_pi]

/-- Helper for Example 4.20: the irrational integer orbit of `α` is dense on the circle under the
Fourier character. -/
-- TODO(Example 4.20): transport `AddCircle.denseRange_zsmul_coe_iff` through
-- `AddCircle.toCircle`, then identify the resulting orbit with `n ↦ 𝐞 (α * n)`.
lemma denseRange_fourierChar_int_mul (α : ℝ) (hα : Irrational α) :
    DenseRange (fun n : ℤ ↦ 𝐞 (α * n)) := by
  let a : AddCircle (1 : ℝ) := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) α
  have hAddCircle :
      DenseRange (fun n : ℤ ↦ n • a) := by
    -- The irrationality hypothesis is exactly the `AddCircle` density criterion at period `1`.
    simpa [a] using
      (AddCircle.denseRange_zsmul_coe_iff (a := α) (p := 1)).2 (by simpa using hα)
  have hCircle :
      DenseRange (fun x : AddCircle (1 : ℝ) ↦ AddCircle.homeomorphCircle one_ne_zero x) :=
    (AddCircle.homeomorphCircle one_ne_zero).surjective.denseRange
  have hComp :
      DenseRange
        (fun n : ℤ ↦ AddCircle.homeomorphCircle one_ne_zero (n • a)) :=
    DenseRange.comp hCircle hAddCircle (AddCircle.homeomorphCircle one_ne_zero).continuous
  have hEq :
      (fun n : ℤ ↦ AddCircle.homeomorphCircle one_ne_zero (n • a)) =
        (fun n : ℤ ↦ 𝐞 (α * n)) := by
    funext n
    -- Identify the `AddCircle` orbit with the normalized circle character orbit.
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul]
    dsimp [a]
    rw [AddCircle.toCircle_apply_mk, Real.fourierChar_apply']
    have hone : Circle.exp (2 * Real.pi / 1 * α) = Circle.exp (2 * Real.pi * α) := by
      congr 1
      ring
    rw [hone]
    rw [← Circle.exp_zsmul (2 * Real.pi * α) n]
    congr 1
    ring
  simpa [hEq] using hComp

/-- Helper for Example 4.20: the irrational integer orbit on the circle returns arbitrarily close
to `1`. -/
-- TODO(Example 4.20): combine Dirichlet approximation with the standard estimate
-- `‖exp (I * t) - 1‖ ≤ |t|`.
lemma dense_circle_integer_orbit_near_one (α : ℝ) (hα : Irrational α) :
    ∀ ε > 0, ∃ n : ℤ, n ≠ 0 ∧ dist (𝐞 (α * n)) 1 < ε := by
  let _ := hα
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) / (N + 1) < ε / (2 * Real.pi) := by
    have hε' : 0 < ε / (2 * Real.pi) := by
      positivity
    rcases exists_nat_one_div_lt hε' with ⟨N, hN⟩
    exact ⟨N, by simpa [Nat.cast_add, Nat.cast_one] using hN⟩
  rcases dirichlet_approximation_theorem α (show 0 < N + 1 by omega) with
    ⟨n, m, hn_pos, -, hnm⟩
  refine ⟨n, ?_, ?_⟩
  · -- Dirichlet returns a positive integer, hence in particular a nonzero one.
    linarith
  · -- Rewrite by the integer shift `m`, then estimate the circle distance through the complex norm.
    have hshift : 𝐞 (α * n) = 𝐞 (α * n - m) := by
      apply (fourierChar_eq_iff_exists_int).2
      refine ⟨m, by ring⟩
    have hnorm :
        ‖Complex.exp (Complex.I * (2 * Real.pi * (α * n - m))) - 1‖ ≤
          ‖2 * Real.pi * (α * n - m)‖ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (α * n - m)))
    have hbound : ‖2 * Real.pi * (α * n - m)‖ < ε := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      have hlt : |(n : ℝ) * α - m| < ε / (2 * Real.pi) := by
        have hN' : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) < ε / (2 * Real.pi) := by
          simpa [Nat.cast_add, Nat.cast_one] using hN
        simpa [mul_comm] using lt_trans hnm hN'
      have hlt' : (2 * Real.pi) * |(n : ℝ) * α - m| < ε := by
        have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
        have := (mul_lt_mul_of_pos_left hlt htwo_pi_pos)
        simpa [div_eq_mul_inv, htwo_pi_pos.ne', mul_assoc, mul_left_comm, mul_comm] using this
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlt'
    change dist (((𝐞 (α * n) : Circle) : ℂ)) ((1 : ℂ)) < ε
    calc
      dist (((𝐞 (α * n) : Circle) : ℂ)) (1 : ℂ)
          = ‖Complex.exp (Complex.I * (2 * Real.pi * (α * n - m))) - 1‖ := by
              rw [hshift, Real.fourierChar_apply', Circle.coe_exp, dist_eq_norm]
              simp [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ‖2 * Real.pi * (α * n - m)‖ := hnorm
      _ < ε := hbound

/-- Helper for Example 4.20: the integer samples of the dense torus curve accumulate at the base
point `γ(0)`. -/
-- TODO(Example 4.20): use continuity of the fixed-first-coordinate inclusion
-- `w ↦ (1, w)` together with the circle-return lemma above.
lemma dense_torus_integer_samples_cluster_at_zero (α : ℝ) (hα : Irrational α) :
    ∀ ε > 0, ∃ n : ℤ, n ≠ 0 ∧ dist (denseTorusCurve α n) (denseTorusCurve α 0) < ε := by
  intro ε hε
  let vertical : Circle → 𝕋^{2} := fun w ↦ ![1, w]
  have hvertical_cont : Continuous vertical := by
    -- The fixed-first-coordinate inclusion into the torus is continuous.
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [vertical] using (continuous_const : Continuous fun _ : Circle ↦ (1 : Circle))
    · simpa [vertical] using (continuous_id : Continuous fun a : Circle ↦ a)
  have hbase : vertical 1 = denseTorusCurve α 0 := by
    -- At the base point, the vertical inclusion lands exactly on `γ(0) = (1, 1)`.
    ext i
    fin_cases i <;> simp [vertical, denseTorusCurve]
  have hpre :
      vertical ⁻¹' Metric.ball (denseTorusCurve α 0) ε ∈ 𝓝 (1 : Circle) := by
    have hcontAt : ContinuousAt vertical (1 : Circle) := hvertical_cont.continuousAt
    have hball :
        vertical ⁻¹' Metric.ball (vertical 1) ε ∈ 𝓝 (1 : Circle) :=
      hcontAt (Metric.ball_mem_nhds _ hε)
    simpa [hbase] using hball
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδpos, hδsub⟩
  rcases dense_circle_integer_orbit_near_one α hα δ hδpos with ⟨n, hn0, hnδ⟩
  refine ⟨n, hn0, ?_⟩
  -- Applying the continuous vertical inclusion transfers the circle return estimate to the torus.
  have hmem :
      vertical (𝐞 (α * n)) ∈ Metric.ball (denseTorusCurve α 0) ε := by
    exact hδsub hnδ
  have hvertical_n : vertical (𝐞 (α * n)) = denseTorusCurve α n := by
    ext i
    fin_cases i
    · simp [vertical, denseTorusCurve, fourierChar_int_eq_one]
    · simp [vertical, denseTorusCurve]
  simpa [Metric.mem_ball, hvertical_n] using hmem

/-- Helper for Example 4.20: the integer samples of the irrational torus curve have the base point
as an accumulation point in the torus. -/
-- TODO(Example 4.20): prove that `denseTorusCurve α 0` lies in the closure of the nonzero integer
-- samples, then rewrite that closure statement as an accumulation-point statement.
lemma dense_torus_integer_samples_accPt (α : ℝ) (hα : Irrational α) :
    AccPt (denseTorusCurve α 0) (𝓟 (Set.range fun n : ℤ ↦ denseTorusCurve α n)) := by
  rw [accPt_iff_nhds]
  intro s hs
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hεpos, hεsub⟩
  rcases dense_torus_integer_samples_cluster_at_zero α hα ε hεpos with ⟨n, hn0, hnε⟩
  refine ⟨denseTorusCurve α n, ?_, ?_⟩
  · -- The chosen nonzero sample lies in the neighborhood and in the integer-sample set.
    refine ⟨hεsub hnε, ⟨n, rfl⟩⟩
  · -- Nonzero integer samples are distinct from the base point by injectivity.
    intro hEq
    have hcoord : 𝐞 (α * n) = 1 := by
      simpa [denseTorusCurve] using congrArg (fun z : 𝕋^{2} ↦ z 1) hEq
    have hcoord' : 𝐞 (α * n) = 𝐞 (0 : ℝ) := by
      simpa [Real.fourierChar_apply'] using hcoord
    rcases (fourierChar_eq_iff_exists_int (x := α * n) (y := 0)).1 hcoord' with ⟨m, hm⟩
    have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hαrat : α = (m : ℝ) / n := by
      apply (eq_div_iff hn_real).2
      linarith
    exact (hα.ne_rational m n) hαrat

/-- Helper for Example 4.20: subtracting an integral multiple of `2π` from an angle branch leaves
the branch property unchanged. -/
theorem IsAngleFunction.sub_int_mul_two_pi {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}
    (hθ : IsAngleFunction θ) (m : ℤ) :
    IsAngleFunction (fun z ↦ θ z - m * (2 * Real.pi)) := by
  constructor
  · -- Subtracting a constant preserves continuity.
    exact hθ.1.sub continuous_const
  · intro z
    -- Integer `2π`-shifts exponentiate to `1`, so the circle value is unchanged.
    calc
      Circle.exp (θ z - m * (2 * Real.pi))
          = Circle.exp (θ z) / Circle.exp (m * (2 * Real.pi)) := by
            rw [Circle.exp_sub]
      _ = Circle.exp (θ z) / 1 := by
            rw [Circle.exp_int_mul_two_pi]
      _ = Circle.exp (θ z) := by simp
      _ = z := hθ.2 z

/-- Helper for Example 4.20: around `Circle.exp x` there is an angle branch taking the value `x`
at that point. -/
theorem exists_angleFunction_through_exp (x : ℝ) :
    ∃ (U : TopologicalSpace.Opens Circle) (hxU : Circle.exp x ∈ U) (θ : U → ℝ),
      IsAngleFunction θ ∧ θ ⟨Circle.exp x, hxU⟩ = x := by
  let U : TopologicalSpace.Opens Circle :=
    ⟨{z : Circle | z ≠ -Circle.exp x}, isOpen_compl_singleton⟩
  have hxU : Circle.exp x ∈ U := by
    -- The open arc omits only the antipode of `Circle.exp x`.
    change Circle.exp x ≠ -Circle.exp x
    simpa [eq_comm] using Circle.neg_ne_self (Circle.exp x)
  have hmissing : -Circle.exp x ∉ U := by
    simp [U]
  rcases exists_angleFunction_of_missing_point (U := U) (c := -Circle.exp x) hmissing with
    ⟨θ₀, hθ₀⟩
  let z₀ : U := ⟨Circle.exp x, hxU⟩
  have hθ₀x : Circle.exp (θ₀ z₀) = Circle.exp x := by
    simpa using hθ₀.2 z₀
  rcases Circle.exp_eq_exp.mp hθ₀x with ⟨m, hm⟩
  let θ : U → ℝ := fun z ↦ θ₀ z - m * (2 * Real.pi)
  have hθ : IsAngleFunction θ := hθ₀.sub_int_mul_two_pi m
  refine ⟨U, hxU, θ, hθ, ?_⟩
  -- The integer shift is chosen so the branch value at `Circle.exp x` is exactly `x`.
  have hshift : θ₀ z₀ - m * (2 * Real.pi) = x := by
    linarith
  simpa [θ] using hshift

/-- Helper for Example 4.20: extend an angle branch by `0` outside its domain so it can serve as
the inverse of a local circle chart. -/
noncomputable def angleFunction_extension {U : TopologicalSpace.Opens Circle} (θ : U → ℝ) :
    Circle → ℝ :=
  let _ : DecidablePred fun z : Circle ↦ z ∈ U := Classical.decPred _
  fun z ↦ if hz : z ∈ U then θ ⟨z, hz⟩ else 0

/-- Helper for Example 4.20: the circle exponential is a smooth local diffeomorphism, obtained
from a local angle branch through each point. -/
theorem circle_exp_isLocalDiffeomorph_from_angle_branch :
    IsLocalDiffeomorph (𝓘(ℝ)) (𝓡 1) (∞ : ℕ∞ω) Circle.exp := by
  intro x
  obtain ⟨U, hxU, θ, hθ, hθx⟩ := exists_angleFunction_through_exp x
  -- The source-faithful local inverse is the chosen angle branch near `Circle.exp x`.
  refine ⟨
    { toPartialEquiv :=
        { toFun := Circle.exp
          invFun := angleFunction_extension θ
          source := hθ.openImage
          target := U
          map_source' := fun {y} hy ↦ hθ.mapsTo_circleExp_openImage hy
          map_target' := by
            intro z hz
            refine ⟨⟨z, hz⟩, ?_⟩
            -- On the target set, the ambient extension reduces to the original branch.
            by_cases h : z ∈ U
            · simp [angleFunction_extension, h]
            · exact (h hz).elim
          left_inv' := by
            intro y hy
            -- On the branch image, the angle branch inverts `Circle.exp`.
            have hyU : Circle.exp y ∈ U := hθ.mapsTo_circleExp_openImage hy
            have hbranch :=
              congrArg (fun f : hθ.openImage → ℝ ↦ f ⟨y, hy⟩) hθ.theta_comp_circleExpOpenImage
            simpa [Function.comp, angleFunction_extension, IsAngleFunction.circleExpOpenImage, hyU]
              using hbranch
          right_inv' := by
            intro z hz
            -- On the target open set, exponentiating the branch value recovers the circle point.
            by_cases h : z ∈ U
            · simpa [angleFunction_extension, h] using hθ.2 ⟨z, h⟩
            · exact (h hz).elim }
      open_source := hθ.openImage.2
      open_target := U.2
      contMDiffOn_toFun := by
        -- The forward map is the globally smooth circle exponential.
        simpa using (contMDiff_circleExp).contMDiffOn
      contMDiffOn_invFun := by
        intro z hz
        -- Near a target point, the ambient extension agrees with the smooth branch `θ`.
        have hθz :
            ContMDiffAt (I := 𝓡 1) (I' := 𝓘(ℝ)) (n := (∞ : ℕ∞ω))
              (angleFunction_extension θ) z := by
          rw [← contMDiffAt_subtype_iff
            (U := U)
            (f := angleFunction_extension θ)
            (x := ⟨z, hz⟩)]
          simpa [angleFunction_extension] using hθ.contMDiff ⟨z, hz⟩
        exact hθz.contMDiffWithinAt },
    ?_, ?_⟩
  · change x ∈ hθ.openImage
    exact ⟨⟨Circle.exp x, hxU⟩, hθx⟩
  · intro y hy
    rfl

/-- Helper for Example 4.20: the coordinatewise circle exponential map on `Fin 2 → ℝ` lands in
the torus model. -/
def torusCircleExp : (Fin 2 → ℝ) → 𝕋^{2} :=
  fun y i ↦ Circle.exp (y i)

/-- Helper for Example 4.20: the affine line whose image under `torusCircleExp` is the torus
curve. -/
def scaledLine (α : ℝ) : ℝ → (Fin 2 → ℝ) :=
  fun t ↦ ![2 * Real.pi * t, 2 * Real.pi * α * t]

/-- Helper for Example 4.20: on `Fin n → ℝ`, the product real model is the same as the ambient
self model. -/
theorem modelWithCornersSelf_fin_fun_eq_pi (n : ℕ) :
    (𝓘(ℝ, Fin n → ℝ)) = ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)) := by
  -- Both models are assembled from the identity charts on each coordinate.
  ext x <;>
    simp [ModelWithCorners.pi, modelWithCornersSelf_partialEquiv, PartialEquiv.pi_refl]

/-- Helper for Example 4.20: the finite-product charted-space structure on `Fin n → ℝ` agrees
with the ambient self-charted-space structure. -/
theorem chartedSpaceSelf_fin_fun_eq_pi (n : ℕ) :
    piChartedSpace (fun _ : Fin n ↦ ℝ) (fun _ : Fin n ↦ ℝ) =
      chartedSpaceSelf (Fin n → ℝ) := by
  have hpiRefl :
      OpenPartialHomeomorph.pi (fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ) =
        OpenPartialHomeomorph.refl (Fin n → ℝ) := by
    refine OpenPartialHomeomorph.ext _ _ (fun x ↦ rfl) (fun x ↦ rfl) ?_
    ext x
    simp [OpenPartialHomeomorph.pi]
  ext1
  · ext e
    constructor
    · rintro ⟨f, hf, rfl⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at hf
      have hconst : f = fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ := by
        funext i
        simpa using hf i
      subst hconst
      exact hpiRefl
    · intro he
      subst he
      exact ⟨fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ, by simp, hpiRefl⟩
  · funext x
    simp [ChartedSpace.chartAt, hpiRefl]

/-- Helper for Example 4.20: the coordinatewise torus covering map is an immersion because it is
the product of the local diffeomorphisms `Circle.exp`. -/
lemma torus_circle_exp_isImmersion :
    IsImmersion R2Model T2Model ∞ torusCircleExp := by
  have hLocal : IsLocalDiffeomorph R2Model T2Model (∞ : ℕ∞ω) torusCircleExp := by
    -- Product local diffeomorphisms are local diffeomorphisms coordinatewise.
    simpa [torusCircleExp] using
      isLocalDiffeomorph_pi (f := fun _ : Fin 2 ↦ Circle.exp)
        (fun _ : Fin 2 ↦ circle_exp_isLocalDiffeomorph_from_angle_branch)
  have hSmooth : ContMDiff R2Model T2Model ∞ torusCircleExp := hLocal.contMDiff
  -- A local diffeomorphism has invertible manifold derivative, hence injective derivative.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hSmooth).2 ?_
  intro x
  rw [← hLocal.mfderivToContinuousLinearEquiv_coe (by simp) x]
  exact (hLocal.mfderivToContinuousLinearEquiv (by simp) x).injective

/-- Helper for Example 4.20: the affine lift `t ↦ (2πt, 2παt)` is smooth for the raw product real
model. -/
lemma scaledLine_contMDiff (α : ℝ) :
    ContMDiff 𝓘(ℝ) R2Model ∞ (scaledLine α) := by
  rw [chartedSpaceSelf_fin_fun_eq_pi 2]
  have hSelf : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ (scaledLine α) := by
    rw [contMDiff_iff_contDiff, contDiff_pi]
    intro i
    fin_cases i
    · -- The first coordinate is the linear function `t ↦ 2π t`.
      simpa [scaledLine, mul_assoc, mul_left_comm, mul_comm] using
        (contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun t : ℝ ↦ (2 * Real.pi) * t)
    · -- The second coordinate is the linear function `t ↦ 2πα t`.
      simpa [scaledLine, mul_assoc, mul_left_comm, mul_comm] using
        (contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun t : ℝ ↦ (2 * Real.pi * α) * t)
  simpa [modelWithCornersSelf_fin_fun_eq_pi] using hSelf

/-- Helper for Example 4.20: the manifold derivative of `scaledLine α` is injective because its
first coordinate is multiplication by `2π`. -/
lemma scaledLine_fderiv_injective (α : ℝ) (t : ℝ) :
    Function.Injective (fderiv ℝ (scaledLine α) t) := by
  let L0 : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi)
  let L1 : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi * α)
  have h0 : HasFDerivAt (fun s : ℝ ↦ (2 * Real.pi) * s) L0 t := by
    simpa [L0, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using (hasDerivAt_const_mul (x := t) (c := 2 * Real.pi)).hasFDerivAt
  have h1 : HasFDerivAt (fun s : ℝ ↦ (2 * Real.pi * α) * s) L1 t := by
    simpa [L1, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using (hasDerivAt_const_mul (x := t) (c := 2 * Real.pi * α)).hasFDerivAt
  have hpi : HasFDerivAt (scaledLine α) (ContinuousLinearMap.pi ![L0, L1]) t := by
    -- Package the two scalar derivatives into a derivative for the `Fin 2 → ℝ` tuple.
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa [scaledLine] using h0
    · simpa [scaledLine] using h1
  rw [hpi.fderiv]
  intro v w h
  -- Projecting to the first coordinate reduces injectivity to cancellation by `2π`.
  have hcoord : v * (2 * Real.pi) = w * (2 * Real.pi) := by
    simpa [L0, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using congrArg (fun z : Fin 2 → ℝ ↦ z 0) h
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact mul_right_cancel₀ htwo_pi_ne hcoord

/-- Helper for Example 4.20: the manifold derivative of `scaledLine α` is injective because its
first coordinate is multiplication by `2π`. -/
lemma scaledLine_mfderiv_injective (α : ℝ) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) R2Model (scaledLine α) t) := by
  rw [chartedSpaceSelf_fin_fun_eq_pi 2]
  change Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Fin 2 → ℝ) (scaledLine α) t)
  have hmf :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Fin 2 → ℝ) (scaledLine α) t = fderiv ℝ (scaledLine α) t := by
    exact mfderiv_eq_fderiv (f := scaledLine α) (x := t)
  rw [hmf]
  exact scaledLine_fderiv_injective α t

/-- Helper for Example 4.20: the affine lift is an immersion because its manifold derivative is
injective at every parameter. -/
lemma scaled_line_isImmersion (α : ℝ) :
    IsImmersion 𝓘(ℝ) R2Model ∞ (scaledLine α) := by
  have hSmooth : ContMDiff 𝓘(ℝ) R2Model ∞ (scaledLine α) := scaledLine_contMDiff α
  -- The Euclidean-model immersion criterion reduces the proof to derivative injectivity.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hSmooth).2 ?_
  intro t
  exact scaledLine_mfderiv_injective α t

/-- Helper for Example 4.20: the dense torus curve factors through the affine lift and the
coordinatewise circle exponential. -/
lemma denseTorusCurve_factorization (α : ℝ) :
    denseTorusCurve α = torusCircleExp ∘ scaledLine α := by
  -- Both sides have the same two circle coordinates after unfolding the definitions.
  funext t
  ext i
  fin_cases i
  · simp [denseTorusCurve, torusCircleExp, scaledLine, Real.fourierChar_apply']
  · simp [denseTorusCurve, torusCircleExp, scaledLine, Real.fourierChar_apply', mul_assoc]

/-- Example 4.20 (1): the torus curve
`t ↦ (e^{2π i t}, e^{2π i α t})` is a smooth immersion of `ℝ` into `𝕋²`. -/
-- TODO(Example 4.20): build the source-faithful immersion proof by composing the affine line
-- `t ↦ (t, α t)` with a local-diffeomorphic torus covering chart.
theorem denseTorusCurve_isImmersion (α : ℝ) :
    IsImmersion 𝓘(ℝ) T2Model ∞ (denseTorusCurve α) := by
  -- The source proof factors `γ` as the affine line `t ↦ (2πt, 2παt)` followed by the torus
  -- covering map `(x, y) ↦ (exp x, exp y)`.
  simpa [denseTorusCurve_factorization, Function.comp] using
    Manifold.IsImmersion.comp torus_circle_exp_isImmersion (scaled_line_isImmersion α)

/-- Example 4.20 (2): for irrational `α`, the torus curve
`t ↦ (e^{2π i t}, e^{2π i α t})` is injective. -/
theorem denseTorusCurve_injective (α : ℝ) (hα : Irrational α) :
    Function.Injective (denseTorusCurve α) := by
  intro t₁ t₂ hEq
  -- Compare the two torus coordinates and convert each equality into an integer shift.
  have h₀ : 𝐞 t₁ = 𝐞 t₂ := by
    simpa using congrArg (fun z : 𝕋^{2} ↦ z 0) hEq
  have h₁ : 𝐞 (α * t₁) = 𝐞 (α * t₂) := by
    simpa using congrArg (fun z : 𝕋^{2} ↦ z 1) hEq
  rcases fourierChar_eq_iff_exists_int.1 h₀ with ⟨m, hm⟩
  rcases fourierChar_eq_iff_exists_int.1 h₁ with ⟨n, hn⟩
  have hsub : t₁ - t₂ = m := by
    linarith
  have hαsub : α * (t₁ - t₂) = n := by
    linarith
  by_cases hm_zero : m = 0
  · -- If the first-coordinate period is trivial, the parameters coincide.
    have hm_real : (m : ℝ) = 0 := by exact_mod_cast hm_zero
    linarith
  · -- Otherwise `α = n / m` would be rational, contradicting irrationality.
    have hm_real : (m : ℝ) ≠ 0 := by exact_mod_cast hm_zero
    have hαrat : α = (n : ℝ) / m := by
      apply (eq_div_iff hm_real).2
      simpa [hsub] using hαsub
    exfalso
    exact (hα.ne_rational n m) hαrat

/-- Example 4.20 (3): for irrational `α`, this injective immersed torus curve is not a
topological embedding, equivalently not a homeomorphism onto its image. -/
-- TODO(Example 4.20): combine the accumulation-point helper for integer samples with the fact
-- that the image of an embedding of `ℤ` is discrete.
theorem denseTorusCurve_not_isEmbedding (α : ℝ) (hα : Irrational α) :
    ¬ IsEmbedding (denseTorusCurve α) := by
  intro hEmb
  let S : Set ℝ := Set.range fun n : {n : ℤ // n ≠ 0} ↦ (n : ℝ)
  have hImageClosure : denseTorusCurve α 0 ∈ closure (denseTorusCurve α '' S) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases dense_torus_integer_samples_cluster_at_zero α hα ε hε with ⟨n, hn0, hnε⟩
    refine ⟨denseTorusCurve α n, ?_, ?_⟩
    · refine ⟨(n : ℝ), ?_, rfl⟩
      exact ⟨⟨n, hn0⟩, rfl⟩
    · simpa [dist_comm] using hnε
  have hzeroClosure : (0 : ℝ) ∈ closure S := by
    -- Pull the closure statement back along the hypothetical embedding.
    rw [hEmb.closure_eq_preimage_closure_image S]
    simpa using hImageClosure
  have hzeroNotClosure : (0 : ℝ) ∉ closure S := by
    intro hclosure
    rw [Metric.mem_closure_iff] at hclosure
    rcases hclosure (1 / 2) (by positivity) with ⟨y, hyS, hy⟩
    rcases hyS with ⟨n, rfl⟩
    have habs : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs n.2
    rw [dist_eq_norm, Real.norm_eq_abs] at hy
    have hy' : |((n : ℤ) : ℝ)| < 1 / 2 := by
      simpa [sub_eq_add_neg, abs_neg] using hy
    linarith
  exact hzeroNotClosure hzeroClosure

/-- Example 4.20 (4): for irrational `α`, the image of the torus curve
`t ↦ (e^{2π i t}, e^{2π i α t})` is dense in `𝕋²`. -/
-- TODO(Example 4.20): fix the first torus coordinate exactly, then use dense vertical orbits from
-- `denseRange_fourierChar_int_mul` and push closure along the vertical inclusion.
theorem denseTorusCurve_denseRange (α : ℝ) (hα : Irrational α) :
    DenseRange (denseTorusCurve α) := by
  intro z
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases fourierChar_surjective (z 0) with ⟨s, hs⟩
  let c : Circle := 𝐞 (α * s)
  let vertical : Circle → 𝕋^{2} := fun w ↦ ![z 0, w]
  have hvertical_cont : Continuous vertical := by
    -- Fixing the first torus coordinate gives a continuous vertical inclusion.
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [vertical] using (continuous_const : Continuous fun _ : Circle ↦ z 0)
    · simpa [vertical] using (continuous_id : Continuous fun a : Circle ↦ a)
  have hvertical_base : vertical (z 1) = z := by
    -- This inclusion passes through the target point itself.
    ext i
    fin_cases i <;> simp [vertical]
  have hpre :
      vertical ⁻¹' Metric.ball z ε ∈ 𝓝 (z 1) := by
    have hcontAt : ContinuousAt vertical (z 1) := hvertical_cont.continuousAt
    have hball :
        vertical ⁻¹' Metric.ball (vertical (z 1)) ε ∈ 𝓝 (z 1) :=
      hcontAt (Metric.ball_mem_nhds _ hε)
    simpa [hvertical_base] using hball
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδpos, hδsub⟩
  have hmul_dense : DenseRange (fun n : ℤ ↦ c * 𝐞 (α * n)) := by
    -- Multiplying a dense orbit by a fixed circle element preserves density.
    refine DenseRange.comp (Function.Surjective.denseRange ?_) (denseRange_fourierChar_int_mul α hα)
      (continuous_const.mul continuous_id)
    intro w
    refine ⟨c⁻¹ * w, by simp [c]⟩
  have hz1_closure : z 1 ∈ closure (Set.range fun n : ℤ ↦ c * 𝐞 (α * n)) :=
    hmul_dense (z 1)
  rcases Metric.mem_closure_iff.mp hz1_closure δ hδpos with ⟨w, ⟨n, rfl⟩, hwn⟩
  refine ⟨denseTorusCurve α (s + n), ?_, ?_⟩
  · -- The point `γ(s + n)` lies in the range by definition.
    exact ⟨s + n, rfl⟩
  · -- Fix the first coordinate exactly and use the dense second-coordinate orbit.
    have hmem :
        vertical (c * 𝐞 (α * n)) ∈ Metric.ball z ε := by
      have hwball : c * 𝐞 (α * n) ∈ Metric.ball (z 1) δ := by
        simpa [Metric.mem_ball, dist_comm] using hwn
      exact hδsub hwball
    have hfirst : 𝐞 (s + n) = z 0 := by
      calc
        𝐞 (s + n) = 𝐞 s * 𝐞 (n : ℝ) := by
          simpa using AddChar.map_add_eq_mul Real.fourierChar s (n : ℝ)
        _ = z 0 := by simp [hs, fourierChar_int_eq_one n]
    have hsecond : 𝐞 (α * (s + n)) = c * 𝐞 (α * n) := by
      calc
        𝐞 (α * (s + n)) = 𝐞 (α * s + α * n) := by congr 1; ring
        _ = 𝐞 (α * s) * 𝐞 (α * n) := by
              simpa using AddChar.map_add_eq_mul Real.fourierChar (α * s) (α * n)
        _ = c * 𝐞 (α * n) := by simp [c]
    have hpoint : vertical (c * 𝐞 (α * n)) = denseTorusCurve α (s + n) := by
      ext i
      fin_cases i
      · simpa [vertical, denseTorusCurve] using
          congrArg (fun z : Circle ↦ (z : ℂ)) hfirst.symm
      · simpa [vertical, denseTorusCurve] using
          congrArg (fun z : Circle ↦ (z : ℂ)) hsecond.symm
    simpa [Metric.mem_ball, hpoint, dist_comm] using hmem
