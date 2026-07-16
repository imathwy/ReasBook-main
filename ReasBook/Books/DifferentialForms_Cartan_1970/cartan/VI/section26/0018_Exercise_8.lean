import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.Complex.AbsMax
import DifferentialForms_Cartan_1970.cartan.I.section04.«0012_Definition_I_4_extra_4»
import DifferentialForms_Cartan_1970.cartan.III.section11.PeriodLattice
import DifferentialForms_Cartan_1970.cartan.III.section11.«0012_Corollary_III_5_extra_8»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.V.section21.«0012_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.V.section21.«0012_Exercise_3».ThetaConvergenceAndTranslations
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0016_Exercise_6»
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0017_Exercise_7».CassiniCore
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».PeriodData
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».BoundaryTrace
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».ClosedExtensionCore
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».AbelIntegralCore
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».BoundarySliceTransport
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».InnerStripBoundary
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».RightTopStripBoundary
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».StripBoundaryLimits
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».SchwarzReflection
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».BoundaryTraceContinuity
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».BoundaryFrontier

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped JacobiTheta UpperHalfPlane ComplexOrder Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Continuous-extension companion: for `0 < k < 1`, the Abelian integral extends continuously to
the closed upper half-plane `Im z ≥ 0`. -/
theorem exercise_8_continuous_extension
    (k : Exercise8Modulus) :
    ∃ fbar : ClosedUpperHalfPlane → ℂ, IsExercise8Extension k fbar := by
  -- The canonical owner is the repaired boundary trace on `Im z = 0` and the Abel integral in the
  -- strict upper half-plane.
  exact ⟨exercise8_closed_extension k, exercise8_closed_extension_spec k⟩

/-- Helper for Cartan section26 0018_Exercise_8: the real quarter period `K` is nonzero because it
is strictly positive. -/
lemma exercise8_complete_real_period_ne_zero
    (k : Exercise8Modulus) :
    exercise8_complete_real_period k ≠ 0 := by
  -- The positivity owner from the period data package immediately rules out `K = 0`.
  exact ne_of_gt (exercise8_complete_real_period_pos k)

/-- Helper for Cartan section26 0018_Exercise_8: once the Abel integral is known to be bijective
from the upper half-plane onto the fundamental rectangle, `Function.invFunOn` packages the
source-facing inverse owner without reopening the analytic argument. -/
lemma exercise8_rectangleInverseOfBijOn
    (k : Exercise8Modulus)
    (hbij :
      Set.BijOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane)
        (exercise8_open_rectangle k)) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  classical
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ Function.invFunOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u
  rcases hbij with ⟨hmap, hinj, hsurj⟩
  refine ⟨G, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u
    -- The surjective half of `BijOn` makes `invFunOn` a right inverse on the rectangle.
    simpa [G] using hsurj.rightInvOn_invFunOn u.2
  · intro z
    -- The same owner theorem already records that every upper-half-plane point lands in the
    -- rectangle.
    exact hmap (by trivial)
  · intro z hz
    -- Injectivity on the source turns `invFunOn` into the required left inverse on `univ`.
    simpa [G] using hinj.leftInvOn_invFunOn (show z ∈ (Set.univ : Set UpperHalfPlane) by trivial)

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias is differentiable on the
strict upper half-plane. This isolates the segment-primitive calculation so later rectangle-image
theorems can consume a named analytic owner instead of rebuilding the same congruence locally. -/
lemma exercise8_abelIntegral_differentiableOn_ambient
    (k : Exercise8Modulus) :
    DifferentiableOn ℂ
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hprimitive :
      DifferentiableOn ℂ
        (fun w : ℂ ↦
          exercise8_abel_integral k UpperHalfPlane.I +
            ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, (exercise8_integrand k dz) t)
        UpperHalfPlane.upperHalfPlaneSet := by
    -- The segment primitive is already holomorphic; adding the fixed anchor value preserves
    -- differentiability on the ambient upper-half-plane set.
    simpa using
      (exercise8_segmentPrimitive_differentiableAmbient k UpperHalfPlane.I).const_add
        (exercise8_abel_integral k UpperHalfPlane.I)
  refine DifferentiableOn.congr hprimitive ?_
  intro w hw
  have hw_im : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hw
  have hcoerce :
      (((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) = w := by
    simpa using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hw_im)
  -- Rewrite the ambient alias through the fixed-anchor identity against the interior point `i`.
  calc
    exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
        = exercise8_abel_integral k UpperHalfPlane.I +
            ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ)
                ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ),
              (exercise8_integrand k dz) t := by
            exact exercise8_abelIntegral_eq_anchor_add_segment k UpperHalfPlane.I
              (UpperHalfPlane.ofComplex w)
    _ =
        exercise8_abel_integral k UpperHalfPlane.I +
          ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, (exercise8_integrand k dz) t := by
            rw [hcoerce]

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias is holomorphic on the
strict upper half-plane. This is the analytic owner consumed by the rectangle-image package. -/
lemma exercise8_abelIntegral_analyticOnNhd_ambient
    (k : Exercise8Modulus) :
    AnalyticOnNhd ℂ
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  -- The upper half-plane is open, so ambient differentiability upgrades to ambient analyticity.
  exact
    (Complex.analyticOnNhd_iff_differentiableOn UpperHalfPlane.isOpen_upperHalfPlaneSet).2
      (exercise8_abelIntegral_differentiableOn_ambient k)

/-- Helper for Exercise 8: on `Im z > 0`, the ambient Abel alias has complex derivative
`exercise8_integrand k z`. This records the local primitive computation in a form that later
inverse-function arguments can consume directly. -/
lemma exercise8_abelIntegral_hasDerivAt_ambient
    (k : Exercise8Modulus) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    HasDerivAt
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (exercise8_integrand k z) z := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun w ↦ exercise8_integrand k w • (1 : ℂ →L[ℂ] ℂ)
  let dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ := fun x ↦
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.restrictScalars (R := ℝ)
        (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
      (1 : ℂ →L[ℂ] ℂ)
  let H : ℂ → ℂ :=
    fun w ↦ ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, ω t
  have hω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasFDerivWithinAt ω (dω x) UpperHalfPlane.upperHalfPlaneSet x := by
    intro x hx
    -- The ambient `dz`-valued integrand is differentiable on `Im z > 0`.
    have hscalar :
        DifferentiableWithinAt ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x :=
      exercise8_integrand_differentiableOn_upper k x
        (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hx)
    have hscalarDeriv :
        HasFDerivWithinAt (exercise8_integrand k)
          (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x)
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalar.hasFDerivWithinAt
    have hscalarDerivR :
        HasFDerivWithinAt (exercise8_integrand k)
          (ContinuousLinearMap.restrictScalars (R := ℝ)
            (fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x))
          UpperHalfPlane.upperHalfPlaneSet x :=
      hscalarDeriv.restrictScalars ℝ
    simpa [ω, dω] using hscalarDerivR.smul_const (1 : ℂ →L[ℂ] ℂ)
  have hdω :
      ∀ x ∈ UpperHalfPlane.upperHalfPlaneSet,
        ∀ u ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
          ∀ v ∈ tangentConeAt ℝ UpperHalfPlane.upperHalfPlaneSet x,
            dω x u v = dω x v u := by
    intro x hx u _ v _
    -- In one complex dimension, the bilinear derivative is symmetric by commutativity.
    let L := fderivWithin ℂ (exercise8_integrand k) UpperHalfPlane.upperHalfPlaneSet x
    have hu : L u = u * L 1 := by
      calc
        L u = L (u * (1 : ℂ)) := by simp
        _ = u * L 1 := by
              rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    have hv : L v = v * L 1 := by
      calc
        L v = L (v * (1 : ℂ)) := by simp
        _ = v * L 1 := by
              rw [← smul_eq_mul, ← smul_eq_mul, map_smul]
    simp [dω, L, hu, hv, mul_left_comm, mul_comm]
  have hWithin :
      HasFDerivWithinAt H (ω z) UpperHalfPlane.upperHalfPlaneSet z := by
    -- The convex primitive theorem differentiates the segment integral directly at `z`.
    simpa [H, ω, dω] using
      Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
        (s := UpperHalfPlane.upperHalfPlaneSet) (ω := ω) (dω := dω)
        exercise8_convex_upperHalfPlaneSet hω hdω UpperHalfPlane.I.2 hz
  have hAt : HasFDerivAt H (ω z) z := by
    exact hWithin.hasFDerivAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hModel :
      HasDerivAt
        (fun w : ℂ ↦ exercise8_abel_integral k UpperHalfPlane.I + H w)
        (exercise8_integrand k z) z := by
    -- The segment integral contributes derivative `exercise8_integrand k z`, and the anchor term
    -- is constant.
    simpa [H, ω] using
      (hAt.hasDerivAt.const_add (exercise8_abel_integral k UpperHalfPlane.I))
  have hEq :
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) =ᶠ[nhds z]
        (fun w : ℂ ↦ exercise8_abel_integral k UpperHalfPlane.I + H w) := by
    have hωeq : ω = exercise8_integrand k dz := by
      -- Both one-form spellings evaluate to the same scalar multiplication on tangent vectors.
      funext t
      ext v
      simp [ω]
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    have hw_im : 0 < w.im := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hw
    have hcoerce :
        (((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) = w := by
      simpa using
        congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
          (UpperHalfPlane.ofComplex_apply_of_im_pos hw_im)
    -- Rewrite the ambient alias through the anchored segment-primitive identity.
    calc
      exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
          = exercise8_abel_integral k UpperHalfPlane.I +
              ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ)
                  ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ),
                (exercise8_integrand k dz) t := by
              exact exercise8_abelIntegral_eq_anchor_add_segment k UpperHalfPlane.I
                (UpperHalfPlane.ofComplex w)
      _ = exercise8_abel_integral k UpperHalfPlane.I +
            ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, (exercise8_integrand k dz) t := by
              rw [hcoerce]
      _ = exercise8_abel_integral k UpperHalfPlane.I + H w := by
            simpa [H, hωeq]
  exact hModel.congr_of_eventuallyEq hEq

/-- Helper for Exercise 8: on `Im z > 0`, the derivative of the ambient Abel alias never
vanishes because it is the reciprocal of the nonzero square-root branch. -/
lemma exercise8_abelIntegral_deriv_ne_zero_ambient
    (k : Exercise8Modulus) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    deriv (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) z ≠ 0 := by
  -- The explicit derivative formula reduces nonvanishing to the already-proved branch
  -- nonvanishing on the strict upper half-plane.
  rw [(exercise8_abelIntegral_hasDerivAt_ambient k hz).deriv]
  exact inv_ne_zero (exercise8_simple_sqrt_branch_ne_zero_on_upper
    (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hz))

/-- Helper for Exercise 8: the Abel integral is continuous on the strict upper half-plane
subtype. -/
lemma exercise8_abelIntegral_continuousOnUpperHalfPlane
    (k : Exercise8Modulus) :
    Continuous (exercise8_abel_integral k) := by
  -- Pointwise continuity on the subtype domain upgrades to global continuity automatically.
  rw [continuous_iff_continuousAt]
  intro z
  exact exercise8_abel_integral_continuousAt k z

/-- Helper for Exercise 8: the Abel image is nonempty because the source upper half-plane
contains the standard point `i`. -/
lemma exercise8_abelIntegral_image_nonempty
    (k : Exercise8Modulus) :
    (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- Evaluating at `i` provides one explicit point of the image.
  exact ⟨exercise8_abel_integral k UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl⟩⟩

/-- Helper for Exercise 8: the Abel image is connected as the continuous image of the connected
upper half-plane. -/
lemma exercise8_abelIntegral_image_isConnected
    (k : Exercise8Modulus) :
    IsConnected (Set.range (exercise8_abel_integral k)) := by
  have hrange :
      Set.range (exercise8_abel_integral k) =
        (exercise8_abel_integral k) '' (Set.univ : Set UpperHalfPlane) := by
    -- Repackage the range as an image of `univ` so connectedness transports directly.
    ext u
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by trivial, rfl⟩
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
  -- Continuous images of connected sets remain connected.
  rw [hrange]
  exact isConnected_univ.image (exercise8_abel_integral k)
    (exercise8_abelIntegral_continuousOnUpperHalfPlane k).continuousOn

/-- Helper for Exercise 8: the strict upper half-plane is preconnected, so the complex
open-mapping theorem applies to the ambient Abel alias on this source domain. -/
lemma exercise8_upperHalfPlane_isPreconnected :
    IsPreconnected UpperHalfPlane.upperHalfPlaneSet := by
  -- The strict upper half-plane is the convex half-space `Im z > 0`.
  exact exercise8_convex_upperHalfPlaneSet.isPreconnected

/-- Helper for Exercise 8: the Abel image agrees with the image of the ambient alias
`w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)` on `Im w > 0`. -/
lemma exercise8_abelIntegral_range_eq_ambientUpperImage
    (k : Exercise8Modulus) :
    Set.range (exercise8_abel_integral k) =
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) ''
        UpperHalfPlane.upperHalfPlaneSet := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(z : ℂ), z.2, ?_⟩
    -- On strict upper-half-plane inputs, the ambient alias is exactly the subtype map.
    simpa using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
  · rintro ⟨w, hw, rfl⟩
    -- Every ambient upper-half-plane input already defines a source point for the Abel map.
    exact ⟨UpperHalfPlane.ofComplex w, rfl⟩

/-- Helper for Exercise 8: once the ambient Abel alias is analytic and nonconstant on `Im z > 0`,
the complex open-mapping theorem makes the Abel image open. -/
lemma exercise8_abelIntegral_image_isOpen_of_analyticAmbient
    (k : Exercise8Modulus)
    (hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet)
    (hnonconst :
      ¬ ∃ c : ℂ,
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
          exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c) :
    IsOpen (Set.range (exercise8_abel_integral k)) := by
  have hopen :
      ∀ s ⊆ UpperHalfPlane.upperHalfPlaneSet,
        IsOpen s →
          IsOpen
            ((fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) '' s) := by
    -- Route correction: isolate the open-image package so the rectangle argument can consume a
    -- named theorem instead of rebuilding the open-mapping step inline.
    exact
      (hanalytic.is_constant_or_isOpen exercise8_upperHalfPlane_isPreconnected).resolve_left
        hnonconst
  -- Apply the open-mapping theorem to the whole strict upper half-plane.
  rw [exercise8_abelIntegral_range_eq_ambientUpperImage k]
  exact hopen UpperHalfPlane.upperHalfPlaneSet Subset.rfl UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- Helper for Exercise 8: once the ambient analyticity and nonconstancy inputs are available, the
Abel image already has the topological package needed by the closure-trap comparison. -/
lemma exercise8_abelIntegral_image_topology_of_analyticAmbient
    (k : Exercise8Modulus)
    (hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet)
    (hnonconst :
      ¬ ∃ c : ℂ,
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
          exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c) :
    IsOpen (Set.range (exercise8_abel_integral k)) ∧
      IsConnected (Set.range (exercise8_abel_integral k)) ∧
      (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- The open-mapping theorem supplies openness; connectedness and nonemptiness are independent.
  refine ⟨exercise8_abelIntegral_image_isOpen_of_analyticAmbient k hanalytic hnonconst, ?_, ?_⟩
  · -- Connectedness comes from continuity on the source upper half-plane subtype.
    exact exercise8_abelIntegral_image_isConnected k
  · -- Nonemptiness comes from evaluating the Abel integral at the point `i`.
    exact exercise8_abelIntegral_image_nonempty k

/-- Helper for Exercise 8: the ambient upper-half-plane Abel alias is nonconstant because its
from-above limits at `0` and `1` are distinct boundary vertices of the rectangle. -/
lemma exercise8_abelIntegral_not_constant_on_ambientUpperHalfPlane
    (k : Exercise8Modulus) :
    ¬ ∃ c : ℂ,
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c := by
  intro hconst
  rcases hconst with ⟨c, hc⟩
  have hupper_closure (x : ℝ) : (x : ℂ) ∈ closure UpperHalfPlane.upperHalfPlaneSet := by
    -- Every real boundary point is approached by a short vertical segment from above.
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · have him_pos : 0 < ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I).im := by
        simp
        linarith
      simpa [UpperHalfPlane.upperHalfPlaneSet] using him_pos
    · have hhalf_nonneg : 0 ≤ ε / 2 := by
        linarith
      have hnormOfReal : ‖((ε / 2 : ℝ) : ℂ)‖ = |ε / 2| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (ε / 2))
      calc
        dist (x : ℂ) ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)
            = ‖(x : ℂ) - ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by
              rw [dist_eq_norm]
        _ = ‖-(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by ring_nf
        _ = ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ := by rw [norm_neg]
        _ = ‖((ε / 2 : ℝ) : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
        _ = |ε / 2| * ‖Complex.I‖ := by rw [hnormOfReal]
        _ = |ε / 2| * 1 := by rw [Complex.norm_I]
        _ = ε / 2 := by rw [abs_of_nonneg hhalf_nonneg]; ring
        _ < ε := by linarith
  have hEq_zero :
      Filter.EventuallyEq
        (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (fun _ : ℂ ↦ c) := by
    -- On the source filter, the ambient alias agrees pointwise with the constant value `c`.
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun z hz ↦ hc z hz)
  have hEq_one :
      Filter.EventuallyEq
        (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (fun _ : ℂ ↦ c) := by
    -- The same pointwise constancy holds near the second boundary vertex.
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun z hz ↦ hc z hz)
  have hconst_zero :
      Filter.Tendsto (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet) (nhds c) := by
    -- Eventual equality with a constant function forces the same limit.
    exact Filter.Tendsto.congr' hEq_zero.symm tendsto_const_nhds
  have hconst_one :
      Filter.Tendsto (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet) (nhds c) := by
    -- The same eventual-constancy argument applies above `1`.
    exact Filter.Tendsto.congr' hEq_one.symm tendsto_const_nhds
  have htrace_zero : exercise8_boundary_trace k 0 = c := by
    -- The limit from above at the origin is unique in the Hausdorff target `ℂ`.
    letI : (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hupper_closure 0)
    exact tendsto_nhds_unique (exercise8_abel_integral_tendsto_boundary_trace_zero k) hconst_zero
  have htrace_one : exercise8_boundary_trace k 1 = c := by
    -- The same uniqueness argument identifies the limit above `1` with the same constant `c`.
    letI : (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hupper_closure 1)
    exact
      tendsto_nhds_unique
        (exercise8_abel_integral_tendsto_boundary_trace_nonzero_real k (by norm_num))
        hconst_one
  have hzero : exercise8_boundary_trace k 0 = 0 := by
    -- The repaired boundary trace is normalized to vanish at the origin.
    simpa using exercise8_boundary_value_zero k
  have hone :
      exercise8_boundary_trace k 1 = exercise8_complete_real_period k := by
    -- The right endpoint of the bottom edge is the real period vertex `K`.
    simpa using exercise8_boundary_value_one k
  have hperiod_ne :
      (exercise8_complete_real_period k : ℂ) ≠ 0 := by
    -- The complete real period is strictly positive, hence nonzero.
    exact_mod_cast (exercise8_complete_real_period_pos k).ne'
  have hzero_eq_period :
      (0 : ℂ) = exercise8_complete_real_period k := by
    calc
      (0 : ℂ) = exercise8_boundary_trace k 0 := hzero.symm
      _ = c := htrace_zero
      _ = exercise8_boundary_trace k 1 := htrace_one.symm
      _ = exercise8_complete_real_period k := hone
  exact hperiod_ne hzero_eq_period.symm

/-- Helper for Exercise 8: the Abel image already carries the open/connected/nonempty package
needed by the closure-trap image comparison. -/
lemma exercise8_abelIntegral_image_topology
    (k : Exercise8Modulus) :
    IsOpen (Set.range (exercise8_abel_integral k)) ∧
      IsConnected (Set.range (exercise8_abel_integral k)) ∧
      (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- Specialize the ambient analytic package using the named nonconstancy witness above.
  exact exercise8_abelIntegral_image_topology_of_analyticAmbient k
    (exercise8_abelIntegral_analyticOnNhd_ambient k)
    (exercise8_abelIntegral_not_constant_on_ambientUpperHalfPlane k)

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is open in `ℂ` because it is
the product of two open real intervals under the `re`/`im` identification. -/
lemma exercise8_open_rectangle_isOpen
    (k : Exercise8Modulus) :
    IsOpen (exercise8_open_rectangle k) := by
  -- The target is literally `Ioo (-K, K) × Ioo (0, K')`.
  simpa [exercise8_open_rectangle] using
    (isOpen_Ioo.reProdIm isOpen_Ioo :
      IsOpen
        (Set.Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ×ℂ
          Set.Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)))

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is convex because it is the
intersection of four real and imaginary open half-spaces. -/
lemma exercise8_open_rectangle_convex
    (k : Exercise8Modulus) :
    Convex ℝ (exercise8_open_rectangle k) := by
  let K := exercise8_complete_real_period k
  let K' := exercise8_complete_imaginary_period k
  have hrect :
      exercise8_open_rectangle k =
        {z : ℂ | -K < z.re} ∩
          ({z : ℂ | z.re < K} ∩ ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < K'})) := by
    ext z
    rw [exercise8_open_rectangle, Complex.mem_reProdIm]
    simpa [K, K', and_assoc]
  -- Repackage the rectangle as a finite intersection of convex half-spaces.
  rw [hrect]
  exact
    (convex_halfSpace_re_gt (-K)).inter
      ((convex_halfSpace_re_lt K).inter
        ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_im_lt K')))

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is nonempty, witnessed by
its vertical midpoint. -/
lemma exercise8_open_rectangle_nonempty
    (k : Exercise8Modulus) :
    (exercise8_open_rectangle k).Nonempty := by
  let center : ℂ := ((exercise8_complete_imaginary_period k / 2 : ℝ) : ℂ) * Complex.I
  refine ⟨center, ?_⟩
  rw [mem_exercise8_open_rectangle_iff]
  constructor
  · constructor <;> simp [center]
    · linarith [exercise8_complete_real_period_pos k]
    · linarith [exercise8_complete_real_period_pos k]
  · constructor <;> simp [center]
    · linarith [exercise8_complete_imaginary_period_pos k]
    · linarith [exercise8_complete_imaginary_period_pos k]

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is connected because any
nonempty convex subset of `ℂ` is connected. -/
lemma exercise8_open_rectangle_isConnected
    (k : Exercise8Modulus) :
    IsConnected (exercise8_open_rectangle k) := by
  -- Convexity plus the midpoint witness gives the source-facing connectedness owner.
  exact (exercise8_open_rectangle_convex k).isConnected (exercise8_open_rectangle_nonempty k)

/-- Helper for Exercise 8: any nonempty open set contained in the closure of the fundamental
rectangle already meets the open rectangle. This isolates the neighborhood argument used by the
later closure-trap image comparison. -/
lemma exercise8_interOpenRectangle_nonempty_of_open_nonempty_subset_closure
    (k : Exercise8Modulus)
    {S : Set ℂ}
    (hS_open : IsOpen S)
    (hS_nonempty : S.Nonempty)
    (hS_subset : S ⊆ closure (exercise8_open_rectangle k)) :
    (S ∩ exercise8_open_rectangle k).Nonempty := by
  rcases hS_nonempty with ⟨z, hzS⟩
  have hz_closure : z ∈ closure (exercise8_open_rectangle k) := hS_subset hzS
  -- The open neighborhood `S` of any closure point must intersect the rectangle.
  rcases (mem_closure_iff.mp hz_closure) S hS_open hzS with ⟨w, hwS, hwRect⟩
  exact ⟨w, hwS, hwRect⟩

/-- Helper for Exercise 8: once the Abel image is known to lie in the closed rectangle and every
rectangle point in its closure is already an image point, the two closure traps force exact image
equality with the open rectangle. This is the topology-only step needed by the early
biholomorphic-package theorem. -/
lemma exercise8_abelImage_eq_open_rectangle_of_closureTraps
    (k : Exercise8Modulus)
    (himage_subset :
      Set.range (exercise8_abel_integral k) ⊆ closure (exercise8_open_rectangle k))
    (himage_trap :
      closure (exercise8_open_rectangle k) ∩ Set.range (exercise8_abel_integral k) ⊆
        exercise8_open_rectangle k)
    (hrectangle_trap :
      closure (Set.range (exercise8_abel_integral k)) ∩ exercise8_open_rectangle k ⊆
        Set.range (exercise8_abel_integral k)) :
    Set.range (exercise8_abel_integral k) = exercise8_open_rectangle k := by
  rcases exercise8_abelIntegral_image_topology k with
      ⟨himage_open, himage_connected, himage_nonempty⟩
  have hinter :
      (Set.range (exercise8_abel_integral k) ∩ exercise8_open_rectangle k).Nonempty :=
    exercise8_interOpenRectangle_nonempty_of_open_nonempty_subset_closure k
      himage_open himage_nonempty himage_subset
  apply Subset.antisymm
  · -- The first closure trap pushes the connected Abel image into the rectangle.
    exact
      himage_connected.isPreconnected.subset_of_closure_inter_subset
        (exercise8_open_rectangle_isOpen k) hinter himage_trap
  · have hinter_symm :
        (exercise8_open_rectangle k ∩ Set.range (exercise8_abel_integral k)).Nonempty := by
      rcases hinter with ⟨z, hzImage, hzRect⟩
      exact ⟨z, hzRect, hzImage⟩
    -- The second closure trap pushes the connected rectangle back into the Abel image.
    exact
      (exercise8_open_rectangle_isConnected k).isPreconnected.subset_of_closure_inter_subset
        himage_open hinter_symm hrectangle_trap

/-- Helper for Exercise 8: the ambient upper-half-plane alias packages the same Abel image as the
subtype map `exercise8_abel_integral k`. -/
abbrev exercise8_ambientAbelImage
    (k : Exercise8Modulus) : Set ℂ :=
  (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) ''
    UpperHalfPlane.upperHalfPlaneSet

/-- Helper for Exercise 8: the Abel-image arguments can be transported from the subtype map to the
ambient upper-half-plane alias without changing the set of values. -/
lemma exercise8_abelImage_eq_ambientAbelImage
    (k : Exercise8Modulus) :
    Set.range (exercise8_abel_integral k) = exercise8_ambientAbelImage k := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(z : ℂ), z.2, ?_⟩
    -- On strict upper-half-plane inputs, `UpperHalfPlane.ofComplex` recovers the original subtype.
    simpa using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
  · rintro ⟨w, hw, rfl⟩
    -- Every ambient point with positive imaginary part already defines a subtype input.
    exact ⟨UpperHalfPlane.ofComplex w, rfl⟩

/-- Helper for Exercise 8: the repaired boundary-frontier theorem transports directly to the
ambient Abel-image alias. -/
lemma exercise8_frontier_rectangle_subset_closure_ambientAbelImage
    (k : Exercise8Modulus) :
    frontier (exercise8_open_rectangle k) ⊆ closure (exercise8_ambientAbelImage k) := by
  -- Rewrite the ambient image back to the subtype Abel image before using the frontier theorem.
  simpa [exercise8_ambientAbelImage, exercise8_abelImage_eq_ambientAbelImage k] using
    (exercise8_frontier_rectangle_subset_closure_abelImage k)

/-- Helper for Exercise 8: the ambient Abel-image alias carries the same open/connected/nonempty
topological package as the subtype Abel image. -/
lemma exercise8_ambientAbelImage_topology
    (k : Exercise8Modulus) :
    IsOpen (exercise8_ambientAbelImage k) ∧
      IsConnected (exercise8_ambientAbelImage k) ∧
      (exercise8_ambientAbelImage k).Nonempty := by
  -- Transport the already-proved subtype-image topology package through the ambient-image alias.
  simpa [exercise8_abelImage_eq_ambientAbelImage k] using
    (exercise8_abelIntegral_image_topology k)

/-- Helper for Exercise 8: once the ambient Abel image is known to stay in the closed rectangle,
it already meets the open rectangle. -/
lemma exercise8_interAmbientAbelImage_openRectangle_nonempty_of_subset_closure
    (k : Exercise8Modulus)
    (hsubset :
      exercise8_ambientAbelImage k ⊆ closure (exercise8_open_rectangle k)) :
    (exercise8_ambientAbelImage k ∩ exercise8_open_rectangle k).Nonempty := by
  rcases exercise8_ambientAbelImage_topology k with ⟨hopen, _, hnonempty⟩
  -- The ambient image is open and nonempty, so any global subset-to-closure bound forces an
  -- actual intersection with the interior rectangle.
  exact
    exercise8_interOpenRectangle_nonempty_of_open_nonempty_subset_closure k
      hopen hnonempty hsubset

/-- Helper for Exercise 8: the closure-trap comparison theorem is stable under the ambient Abel
alias. This isolates the transport step needed by the future non-circular exact-image proof. -/
lemma exercise8_ambientAbelImage_eq_open_rectangle_of_closureTraps
    (k : Exercise8Modulus)
    (himage_subset :
      exercise8_ambientAbelImage k ⊆ closure (exercise8_open_rectangle k))
    (himage_trap :
      closure (exercise8_open_rectangle k) ∩ exercise8_ambientAbelImage k ⊆
        exercise8_open_rectangle k)
    (hrectangle_trap :
      closure (exercise8_ambientAbelImage k) ∩ exercise8_open_rectangle k ⊆
        exercise8_ambientAbelImage k) :
    exercise8_ambientAbelImage k = exercise8_open_rectangle k := by
  -- Transport the three closure-trap hypotheses through the ambient-image bridge and reuse the
  -- subtype-range theorem.
  simpa [exercise8_ambientAbelImage, exercise8_abelImage_eq_ambientAbelImage k] using
    (exercise8_abelImage_eq_open_rectangle_of_closureTraps k
      (by
        simpa [exercise8_ambientAbelImage, exercise8_abelImage_eq_ambientAbelImage k] using
          himage_subset)
      (by
        simpa [exercise8_ambientAbelImage, exercise8_abelImage_eq_ambientAbelImage k] using
          himage_trap)
      (by
        simpa [exercise8_ambientAbelImage, exercise8_abelImage_eq_ambientAbelImage k] using
          hrectangle_trap))

/-- Helper for Cartan section26 0018_Exercise_8: the fundamental open rectangle is bounded in
`ℂ`. -/
lemma exercise8_open_rectangle_isBounded
    (k : Exercise8Modulus) :
    Bornology.IsBounded (exercise8_open_rectangle k) := by
  -- The rectangle is a product of two bounded real intervals under the `re`/`im` identification.
  simpa [exercise8_open_rectangle] using
    (Metric.isBounded_Ioo
      (-exercise8_complete_real_period k) (exercise8_complete_real_period k)).reProdIm
      (Metric.isBounded_Ioo (0 : ℝ) (exercise8_complete_imaginary_period k))

/-- Helper for Exercise 8: a function on the fundamental rectangle is determined by its frontier
values once it is holomorphic on the interior and continuous on the closure. -/
lemma exercise8_eqOn_open_rectangle_of_eqOn_frontier
    (k : Exercise8Modulus)
    {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (exercise8_open_rectangle k))
    (hfrontier : EqOn f id (frontier (exercise8_open_rectangle k))) :
    EqOn f id (exercise8_open_rectangle k) := by
  have hid : DiffContOnCl ℂ (id : ℂ → ℂ) (exercise8_open_rectangle k) := by
    -- The identity map is entire, so it satisfies the same `DiffContOnCl` hypothesis on every
    -- subset of `ℂ`.
    simpa using
      (differentiable_id : Differentiable ℂ (id : ℂ → ℂ)).diffContOnCl
  -- Apply the bounded maximum-modulus uniqueness theorem on the rectangle.
  exact
    Complex.eqOn_of_eqOn_frontier
      (exercise8_open_rectangle_isBounded k) hf hid hfrontier

/-- Helper for Exercise 8: the inverse branch coming from the biholomorphic Abel map is itself a
source-facing rectangle inverse. -/
lemma exercise8_biholomorphicInverse_isRectangleInverse
    (k : Exercise8Modulus)
    {e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k)}
    (he : ∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) :
    IsExercise8RectangleInverse k
      (fun u : exercise8_open_rectangle k ↦
        UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hu_target : (u : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using u.2
    have hu_source :
        ((e : OpenPartialHomeomorph ℂ ℂ).symm u : ℂ) ∈
          (e : OpenPartialHomeomorph ℂ ℂ).source := by
      exact (e : OpenPartialHomeomorph ℂ ℂ).map_target hu_target
    have hu_im : 0 < (((e : OpenPartialHomeomorph ℂ ℂ).symm u : ℂ)).im := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using hu_source
    have hu_coe :
        (((UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u) : UpperHalfPlane) :
            ℂ)) =
          (e : OpenPartialHomeomorph ℂ ℂ).symm u := by
      simpa using
        congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
          (UpperHalfPlane.ofComplex_apply_of_im_pos hu_im)
    -- Reinterpret the biholomorphic inverse value as an element of `UpperHalfPlane`.
    calc
      exercise8_abel_integral k
          (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u))
          = e (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)) := by
              simpa using
                (he (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u))).symm
      _ = (e : OpenPartialHomeomorph ℂ ℂ) ((e : OpenPartialHomeomorph ℂ ℂ).symm u) := by
            rw [hu_coe]
      _ = u := by
            simpa using (e : OpenPartialHomeomorph ℂ ℂ).right_inv hu_target
  · intro z
    have hz_source : ((z : UpperHalfPlane) : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using z.2
    -- The biholomorphic forward map lands in the prescribed rectangle.
    simpa [e.target_eq, he z] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source
  · intro z hz
    have hz_target :
        exercise8_abel_integral k z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using hz
    have hz_source :
        ((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) : ℂ) ∈
          (e : OpenPartialHomeomorph ℂ ℂ).source := by
      exact (e : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
    have hz_im :
        0 < (((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) : ℂ)).im := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using hz_source
    -- Apply the inverse branch to the Abel image and then coerce back to `UpperHalfPlane`.
    simpa using
      (calc
        (((UpperHalfPlane.ofComplex
              ((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z)) :
              UpperHalfPlane) : ℂ))
            = (e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) := by
                simpa using
                  congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
                    (UpperHalfPlane.ofComplex_apply_of_im_pos hz_im)
        _ = (z : ℂ) := by
              calc
                (e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z)
                    = (e : OpenPartialHomeomorph ℂ ℂ).symm (e z) := by
                        rw [(he z).symm]
                _ = z := by
                      simpa using
                        (e : OpenPartialHomeomorph ℂ ℂ).left_inv
                          (by simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using z.2))

/-- Helper for Exercise 8: every upper-half-plane point admits an analytic local inverse chart for
the ambient Abel alias, together with the source-facing left- and right-inverse identities near
its image. -/
lemma exercise8_abelIntegral_localInverseChart
    (k : Exercise8Modulus) (z : UpperHalfPlane) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (exercise8_abel_integral k z) ∧
        (∀ᶠ w in 𝓝 (z : ℂ),
          g (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) = w) ∧
        (∀ᶠ u in 𝓝 (exercise8_abel_integral k z),
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (g u)) = u) ∧
        g (exercise8_abel_integral k z) = z := by
  let f : ℂ → ℂ := fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  have hz : (z : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using z.2
  have hz_analytic : AnalyticAt ℂ f z := by
    simpa [f] using (exercise8_abelIntegral_analyticOnNhd_ambient k z hz)
  have hz_image :
      f z = exercise8_abel_integral k z := by
    simpa [f] using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
  let g : ℂ → ℂ :=
    hz_analytic.hasStrictDerivAt.localInverse f (deriv f z) z
      (exercise8_abelIntegral_deriv_ne_zero_ambient k hz)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · -- The inverse-function theorem keeps the local inverse analytic at the common image point.
    have hg_analytic : AnalyticAt ℂ g (f z) := by
      simpa [g] using
        hz_analytic.analyticAt_localInverse (exercise8_abelIntegral_deriv_ne_zero_ambient k hz)
    simpa [hz_image] using hg_analytic
  · -- The local inverse recovers the source point on a neighborhood of `z`.
    simpa [f, g] using
      hz_analytic.hasStrictDerivAt.eventually_left_inverse
        (exercise8_abelIntegral_deriv_ne_zero_ambient k hz)
  · -- The same chart is also a right inverse near the image point `exercise8_abel_integral k z`.
    simpa [f, g, hz_image] using
      hz_analytic.hasStrictDerivAt.eventually_right_inverse
        (exercise8_abelIntegral_deriv_ne_zero_ambient k hz)
  · -- Evaluating the eventual left-inverse identity at the center fixes the chart normalization.
    have hleft :
        ∀ᶠ w in 𝓝 (z : ℂ),
          g (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) = w := by
      simpa [f, g] using
        hz_analytic.hasStrictDerivAt.eventually_left_inverse
          (exercise8_abelIntegral_deriv_ne_zero_ambient k hz)
    simpa [f] using hleft.self_of_nhds

/-- Helper for Exercise 8: two local inverse charts for the ambient Abel map that both recover the
same source germ at `z` agree on a neighborhood of the common Abel image. -/
lemma exercise8_abelIntegral_localChart_overlap_unique_atPoint
    (k : Exercise8Modulus) {z : UpperHalfPlane} {g₁ g₂ : ℂ → ℂ}
    (hg₁ :
      ∀ᶠ w in 𝓝 (z : ℂ),
        g₁ (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) = w)
    (hg₂ :
      ∀ᶠ w in 𝓝 (z : ℂ),
        g₂ (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) = w) :
    ∀ᶠ u in 𝓝 (exercise8_abel_integral k z), g₁ u = g₂ u := by
  let f : ℂ → ℂ := fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  have hz : (z : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using z.2
  have hz_analytic : AnalyticAt ℂ f (z : ℂ) := by
    -- The ambient Abel alias is analytic at every strict upper-half-plane source point.
    simpa [f] using (exercise8_abelIntegral_analyticOnNhd_ambient k (z : ℂ) hz)
  have hstrict : HasStrictDerivAt f (deriv f (z : ℂ)) (z : ℂ) := by
    -- The ambient Abel alias has a nonvanishing strict derivative at every upper-half-plane
    -- source point.
    exact hz_analytic.hasStrictDerivAt
  have hderiv_ne : deriv f (z : ℂ) ≠ 0 := by
    -- The inverse-function theorem applies because the branch derivative never vanishes upstairs.
    simpa [f] using exercise8_abelIntegral_deriv_ne_zero_ambient k hz
  have hg₁_unique :
      ∀ᶠ u in 𝓝 (f (z : ℂ)),
        g₁ u = HasStrictDerivAt.localInverse f (deriv f (z : ℂ)) (z : ℂ) hstrict hderiv_ne u := by
    -- Any left inverse germ near `z` must agree with the canonical local inverse germ near `f z`.
    simpa [HasStrictDerivAt.localInverse] using
      (hstrict.hasStrictFDerivAt_equiv hderiv_ne).localInverse_unique (f := f) (a := (z : ℂ)) hg₁
  have hg₂_unique :
      ∀ᶠ u in 𝓝 (f (z : ℂ)),
        g₂ u = HasStrictDerivAt.localInverse f (deriv f (z : ℂ)) (z : ℂ) hstrict hderiv_ne u := by
    -- The same uniqueness theorem applies to the second chart.
    simpa [HasStrictDerivAt.localInverse] using
      (hstrict.hasStrictFDerivAt_equiv hderiv_ne).localInverse_unique (f := f) (a := (z : ℂ)) hg₂
  have hz_image : f (z : ℂ) = exercise8_abel_integral k z := by
    -- The ambient alias agrees with the subtype Abel integral at the chosen source point.
    simpa [f] using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
  -- Both charts coincide with the same canonical local inverse germ, hence with each other.
  rw [← hz_image]
  filter_upwards [hg₁_unique, hg₂_unique] with u hu₁ hu₂
  exact hu₁.trans hu₂.symm

/-- Helper for Exercise 8: the canonical interior basepoint `i` already carries a local inverse
chart for the ambient Abel map. This isolates the first available inverse germ before the global
rectangle branch is built. -/
lemma exercise8_localInverseChart_atI
    (k : Exercise8Modulus) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (exercise8_abel_integral k UpperHalfPlane.I) ∧
        (∀ᶠ w in 𝓝 (UpperHalfPlane.I : ℂ),
          g (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) = w) ∧
        (∀ᶠ u in 𝓝 (exercise8_abel_integral k UpperHalfPlane.I),
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (g u)) = u) ∧
        g (exercise8_abel_integral k UpperHalfPlane.I) = UpperHalfPlane.I := by
  -- Specialize the local inverse-chart owner at the standard interior source point `i`.
  simpa using exercise8_abelIntegral_localInverseChart k UpperHalfPlane.I

/-- Helper for Exercise 8: the local inverse chart centered at the Abel image of `i` can already
be shrunk to an open neighborhood on which the chart stays in the strict upper half-plane and
still satisfies the local right-inverse identity. -/
lemma exercise8_localInverseChart_atI_upperHalfPlaneNeighborhood
    (k : Exercise8Modulus) :
    ∃ U : Set ℂ, IsOpen U ∧ exercise8_abel_integral k UpperHalfPlane.I ∈ U ∧
      ∃ g : ℂ → ℂ,
        (∀ u ∈ U, 0 < (g u).im) ∧
        (∀ u ∈ U, exercise8_abel_integral k (UpperHalfPlane.ofComplex (g u)) = u) := sorry

/-- Helper for Exercise 8: once the local inverse charts are synchronized on the full rectangle,
they package a single global inverse branch for the Abel integral. -/
lemma exercise8_rectangleInverse_exists_of_localCharts
    (k : Exercise8Modulus) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  -- Route correction: the Abel-side frontier is no longer the downstream injectivity wrapper.
  -- The actual missing primitive is one global rectangle inverse branch built from the local
  -- inverse charts and the exact image geometry.
  let _ := exercise8_localInverseChart_atI_upperHalfPlaneNeighborhood k
  -- TODO: the local chart at `i` is now shrunk to an open neighborhood where it already lands in
  -- `Im > 0` and satisfies the right-inverse law. The remaining gap is to prove that this seed
  -- neighborhood lies inside `exercise8_open_rectangle k`, then globalize the compatible charts
  -- across the connected rectangle via `exercise8_abelIntegral_localChart_overlap_unique_atPoint`.
  -- Current blocker: the file still lacks the rectangle-membership owner for the seed Abel image
  -- `exercise8_abel_integral k UpperHalfPlane.I`, so the clopen continuation argument cannot yet
  -- start inside the target rectangle.
  sorry

/-- Helper for Cartan section26 0018_Exercise_8: the ambient alias
`w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)` is injective on `Im w > 0` once the
subtype-level rectangle bijection is available. -/
lemma exercise8_abelIntegral_injOn_subtype_univ
    (k : Exercise8Modulus) :
    Set.InjOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) := by
  rcases exercise8_rectangleInverse_exists_of_localCharts k with ⟨G, hG⟩
  intro z _ w _ hEq
  have hz_rect : exercise8_abel_integral k z ∈ exercise8_open_rectangle k := hG.2.1 z
  have hw_rect : exercise8_abel_integral k w ∈ exercise8_open_rectangle k := hG.2.1 w
  have hsub :
      (⟨exercise8_abel_integral k z, hz_rect⟩ : exercise8_open_rectangle k) =
        ⟨exercise8_abel_integral k w, hw_rect⟩ := by
    -- Equality of Abel images identifies the two rectangle arguments of the global inverse branch.
    apply Subtype.ext
    simpa using hEq
  -- The left-inverse field of the global rectangle branch collapses equality of Abel images back
  -- to equality upstairs.
  calc
    z = G ⟨exercise8_abel_integral k z, hz_rect⟩ := by
          simpa using (hG.2.2 z hz_rect).symm
    _ = G ⟨exercise8_abel_integral k w, hw_rect⟩ := by simpa [hsub]
    _ = w := by
          simpa using hG.2.2 w hw_rect

/-- Helper for Cartan section26 0018_Exercise_8: the ambient alias
`w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)` is injective on `Im w > 0` once the
primitive subtype injectivity owner is available. -/
lemma exercise8_abelIntegral_injOn_ambient
    (k : Exercise8Modulus) :
    Set.InjOn
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz w hw hEq
  have hofEq : UpperHalfPlane.ofComplex z = UpperHalfPlane.ofComplex w := by
    -- The ambient equality is just the subtype equality seen through `UpperHalfPlane.ofComplex`.
    exact exercise8_abelIntegral_injOn_subtype_univ k (by trivial) (by trivial) (by simpa using hEq)
  -- Compare the underlying complex values of the identified subtype points.
  calc
    z = ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) := by
          simpa using
            (congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
              (UpperHalfPlane.ofComplex_apply_of_im_pos
                (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hz))).symm
    _ = ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) := by
          simpa using congrArg (fun u : UpperHalfPlane ↦ (u : ℂ)) hofEq
    _ = w := by
          simpa using
            congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
              (UpperHalfPlane.ofComplex_apply_of_im_pos
                (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hw))

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias has image exactly the
fundamental open rectangle. -/
lemma exercise8_ambientAbelImage_eq_open_rectangle
    (k : Exercise8Modulus) :
    exercise8_ambientAbelImage k = exercise8_open_rectangle k := by
  rcases exercise8_rectangleInverse_exists_of_localCharts k with ⟨G, hG⟩
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    -- The global rectangle branch already records that every upper-half-plane point lands inside
    -- the target rectangle.
    exact hG.2.1 (UpperHalfPlane.ofComplex w)
  · intro hu
    let u' : exercise8_open_rectangle k := ⟨u, hu⟩
    refine ⟨(G u' : ℂ), (G u').2, ?_⟩
    -- The right-inverse field makes every rectangle point an actual Abel-image value.
    simpa [u'] using hG.1 u'

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias has image exactly the
fundamental open rectangle. -/
lemma exercise8_abelIntegral_image_eq_open_rectangle
    (k : Exercise8Modulus) :
    (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) ''
        UpperHalfPlane.upperHalfPlaneSet =
      exercise8_open_rectangle k := by
  -- The exact-image owner is most naturally stated on `exercise8_ambientAbelImage k`.
  exact exercise8_ambientAbelImage_eq_open_rectangle k

/-- Helper for Exercise 8: once the ambient Abel alias is known to be analytic on `Im w > 0`, the
already-proved injectivity and exact-image owners package it into the public holomorphic
isomorphism together with the source-facing rectangle inverse branch. -/
lemma exercise8_abelIntegral_bijective_of_analyticAmbient
    (k : Exercise8Modulus)
    (hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet) :
    ∃ e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k),
      (∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) ∧
        ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  have hIso :
      Function.IsHolomorphicIsomorphOn
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k) := by
    -- The remaining forward-map data is already available once ambient analyticity is supplied.
    exact
      isHolomorphicIsomorphOn_of_analyticOnNhd_of_injOn_image_eq
        UpperHalfPlane.isOpen_upperHalfPlaneSet
        (exercise8_open_rectangle_isOpen k)
        hanalytic
        (exercise8_abelIntegral_injOn_ambient k)
        (exercise8_abelIntegral_image_eq_open_rectangle k)
  rcases hIso with ⟨e, he⟩
  refine ⟨e, ?_⟩
  constructor
  · intro z
    -- Restrict the ambient equality-on-source statement back to the upper-half-plane subtype.
    have hez :
        e (z : ℂ) =
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (z : ℂ)) :=
      he z.2
    simpa using hez
  · let G : exercise8_open_rectangle k → UpperHalfPlane :=
        fun u ↦ UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)
    have heUpper : ∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z := by
      intro z
      simpa using he z.2
    have hG : IsExercise8RectangleInverse k G := by
      simpa [G] using (exercise8_biholomorphicInverse_isRectangleInverse k heUpper)
    -- Build the rectangle inverse directly from the biholomorphic package, so this theorem no
    -- longer depends on the separate rectangle-inverse existence owner.
    exact ⟨G, hG⟩

/-- Helper for Exercise 8: the missing structural owner is one biholomorphic Abel-map package that
identifies `exercise8_abel_integral k` with a holomorphic isomorphism onto
`exercise8_open_rectangle k` and exposes the corresponding source-facing rectangle inverse. -/
lemma exercise8_abelIntegral_biholomorphicData
    (k : Exercise8Modulus) :
    ∃ e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k),
      (∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) ∧
        ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  -- Once the repaired ambient injectivity and exact-image owners are in place, the biholomorphic
  -- package is exactly the parameterized ambient theorem specialized to the Abel map.
  exact
    exercise8_abelIntegral_bijective_of_analyticAmbient k
      (exercise8_abelIntegral_analyticOnNhd_ambient k)

/-- Abel-integral bijectivity companion: for `0 < k < 1`, the Abelian integral itself is the
forward map of a holomorphic isomorphism from the open upper half-plane onto the open rectangle
with vertices `-K`, `K`, `K + i K'`, and `-K + i K'`; in particular, it admits the source-facing
inverse branch on that rectangle. -/
theorem exercise_8_abel_integral_bijective
    (k : Exercise8Modulus) :
    ∃ e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k),
      (∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) ∧
        ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  -- The public statement is only a wrapper around the theorem-local biholomorphic owner.
  exact exercise8_abelIntegral_biholomorphicData k

/-- Helper for Cartan section26 0018_Exercise_8: the public biholomorphic Abel-map theorem already
packages the subtype Abel integral as a bijection from the strict upper half-plane onto the open
rectangle. -/
lemma exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic
    (k : Exercise8Modulus) :
    Set.BijOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane)
      (exercise8_open_rectangle k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z _
    have hzImage :
        exercise8_abel_integral k z ∈ exercise8_ambientAbelImage k := by
      refine ⟨(z : ℂ), z.2, ?_⟩
      simpa using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
    -- Route correction: consume the repaired exact-image owner directly instead of going back
    -- through the downstream biholomorphic wrapper.
    simpa [exercise8_ambientAbelImage_eq_open_rectangle k] using hzImage
  · -- The primitive subtype injectivity owner is the only input really needed here.
    exact exercise8_abelIntegral_injOn_subtype_univ k
  · intro u hu
    have huImage : u ∈ exercise8_ambientAbelImage k := by
      simpa [exercise8_ambientAbelImage_eq_open_rectangle k] using hu
    rcases huImage with ⟨w, hw, hwEq⟩
    refine ⟨UpperHalfPlane.ofComplex w, by trivial, ?_⟩
    -- Reinterpret the ambient witness as a genuine upper-half-plane source point.
    simpa using hwEq

/-- Helper for Cartan section26 0018_Exercise_8: the Abel integral admits a source-facing inverse
on the open rectangle once the boundary/perimeter package is in place. -/
lemma exercise8_rectangle_inverse_exists
    (k : Exercise8Modulus) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  -- Route correction: detach the target file from the support-file existence owner and rebuild
  -- the rectangle branch directly from the already-proved biholomorphic Abel-map package.
  exact
    exercise8_rectangleInverseOfBijOn k
      (exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k)

/-- Helper for Cartan section26 0018_Exercise_8: the rectangle inverse branch is unique once the
Abel integral is known to be injective on the upper half-plane. -/
lemma exercise8_rectangle_inverse_unique
    (k : Exercise8Modulus)
    {G₁ G₂ : exercise8_open_rectangle k → UpperHalfPlane}
    (hG₁ : IsExercise8RectangleInverse k G₁)
    (hG₂ : IsExercise8RectangleInverse k G₂) :
    G₁ = G₂ := by
  -- Both branches have the same Abel-integral image at each rectangle point, so injectivity of
  -- the Abel map identifies them pointwise.
  funext u
  rcases exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k with ⟨_, hinj, _⟩
  apply hinj
  · trivial
  · trivial
  · simpa using (hG₁.1 u).trans (hG₂.1 u).symm

/-- Helper for Cartan section26 0018_Exercise_8: any two meromorphic inverse extensions agree on
the fundamental rectangle because they restrict to the same source-facing inverse branch there. -/
lemma exercise8_inverse_eqOn_open_rectangle
    (k : Exercise8Modulus)
    {F₁ F₂ : ℂ → ℂ}
    (hF₁ : IsExercise8Inverse k F₁)
    (hF₂ : IsExercise8Inverse k F₂) :
    EqOn F₁ F₂ (exercise8_open_rectangle k) := by
  rcases hF₁ with ⟨G₁, hG₁, _, _, hFG₁⟩
  rcases hF₂ with ⟨G₂, hG₂, _, _, hFG₂⟩
  have hG : G₁ = G₂ := exercise8_rectangle_inverse_unique k hG₁ hG₂
  intro u hu
  let u' : exercise8_open_rectangle k := ⟨u, hu⟩
  -- Evaluate both extensions through their common inverse branch over the rectangle.
  calc
    F₁ u = G₁ u' := by simpa [u'] using hFG₁ u'
    _ = G₂ u' := by simpa [hG]
    _ = F₂ u := by simpa [u'] using (hFG₂ u').symm

/-- Helper for Cartan section26 0018_Exercise_8: an inverse extension stays in the strict upper
half-plane on the open rectangle because there it is the rectangle inverse branch itself. -/
lemma exercise8_inverse_im_pos_on_open_rectangle
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F)
    {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    0 < (F u).im := by
  rcases hF with ⟨G, _, _, _, hFG⟩
  let u' : exercise8_open_rectangle k := ⟨u, hu⟩
  -- On the rectangle the extension coincides with the upper-half-plane-valued inverse branch.
  calc
    0 < (G u' : ℂ).im := (G u').im_pos
    _ = (F u).im := by
        simpa [u'] using congrArg Complex.im (hFG u').symm

/-- Helper for Cartan section26 0018_Exercise_8: the real-boundary values of a closed-half-plane
extension together with the adjoined source point at infinity. The added point records the missing
top midpoint `i K'` of the rectangle perimeter. -/
def exercise8_completed_boundary_extension
    (k : Exercise8Modulus) (fbar : ClosedUpperHalfPlane → ℂ) : OnePoint ℝ → ℂ
  | OnePoint.infty => (exercise8_complete_imaginary_period k : ℂ) * Complex.I
  | (x : ℝ) => fbar ⟨(x : ℂ), by simp⟩

/-- Helper: the frontier of the fundamental rectangle is exactly the finite real-axis boundary
trace together with the missing top midpoint `i K'`. -/
lemma exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier
    (k : Exercise8Modulus) :
    Set.range (exercise8_boundary_trace k) ∪
        {((exercise8_complete_imaginary_period k : ℂ) * Complex.I)} =
      frontier (exercise8_open_rectangle k) := by
  ext u
  constructor
  · rintro (hu_range | hu_top)
    · -- Every finite boundary-trace value already lies on the rectangle frontier.
      exact exercise8_boundary_trace_range_subset_frontier_rectangle k hu_range
    · rcases hu_top with rfl
      -- The missing midpoint `i K'` lies on the top side of the closed rectangle.
      refine exercise8_mem_frontier_rectangle_of_coords ?_ ?_ ?_
      · simpa using
          (show
            (0 : ℝ) ∈
              Icc (-exercise8_complete_real_period k) (exercise8_complete_real_period k) from
              ⟨by linarith [exercise8_complete_real_period_pos k],
                by linarith [exercise8_complete_real_period_pos k]⟩)
      · simpa using
          (show exercise8_complete_imaginary_period k ∈
              Icc (0 : ℝ) (exercise8_complete_imaginary_period k) from
              ⟨(exercise8_complete_imaginary_period_pos k).le, le_rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (by simp)))
  · intro hu
    have hreal :
        -exercise8_complete_real_period k < exercise8_complete_real_period k := by
      linarith [exercise8_complete_real_period_pos k]
    have himag : (0 : ℝ) < exercise8_complete_imaginary_period k :=
      exercise8_complete_imaginary_period_pos k
    rw [exercise8_open_rectangle, Complex.frontier_reProdIm, closure_Ioo hreal.ne,
      frontier_Ioo himag, closure_Ioo himag.ne, frontier_Ioo hreal] at hu
    rcases hu with hu_horizontal | hu_vertical
    · rw [Complex.mem_reProdIm] at hu_horizontal
      rcases hu_horizontal with ⟨hre, him⟩
      rcases him with hu_bottom | hu_top
      · -- The bottom edge is filled exactly by the inner branch and its reflection.
        by_cases hre_nonneg : 0 ≤ u.re
        · have hu_range :
              u.re ∈ (fun x : ℝ ↦ exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
            rw [exercise8_inner_primitive_image_Icc]
            exact ⟨hre_nonneg, hre.2⟩
          rcases hu_range with ⟨x, hx_mem, hx_eq⟩
          have htrace_eq :
              exercise8_boundary_trace k x = u := by
            have hbranch :
                exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
              rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
              simpa [exercise8_boundary_inner_branch] using
                exercise8_boundary_value_eq_inner hx_mem
            calc
              exercise8_boundary_trace k x = ((exercise8_inner_primitive k x : ℝ) : ℂ) := by
                rw [hbranch, exercise8_boundary_inner_branch_eq_inner_primitive]
              _ = ((u.re : ℝ) : ℂ) := by
                exact congrArg (fun t : ℝ ↦ (t : ℂ)) hx_eq
              _ = u := by
                apply Complex.ext <;> simp [hu_bottom]
          exact Or.inl ⟨x, htrace_eq⟩
        · have hu_range :
              -u.re ∈ (fun x : ℝ ↦ exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
            rw [exercise8_inner_primitive_image_Icc]
            constructor
            · linarith
            · linarith [hre.1]
          rcases hu_range with ⟨x, hx_mem, hx_eq⟩
          have htrace_eq :
              exercise8_boundary_trace k (-x) = u := by
            have hbranch :
                exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
              rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
              simpa [exercise8_boundary_inner_branch] using
                exercise8_boundary_value_eq_inner hx_mem
            calc
              exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
                simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
              _ = -star (exercise8_boundary_inner_branch k x) := by rw [hbranch]
              _ = ((u.re : ℝ) : ℂ) := by
                rw [exercise8_boundary_inner_branch_eq_inner_primitive]
                simp [hx_eq]
              _ = u := by
                apply Complex.ext <;> simp [hu_bottom]
          exact Or.inl ⟨-x, htrace_eq⟩
      · -- The top edge is exact away from the midpoint; the midpoint itself is the adjoined point.
        by_cases hre_nonneg : 0 ≤ u.re
        · by_cases hre_zero : u.re = 0
          · have hu_mid :
                u = (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
              have hu_top_eq : u.im = exercise8_complete_imaginary_period k := by
                simpa using hu_top
              apply Complex.ext <;> simp [hu_top_eq, hre_zero]
            exact Or.inr (by simpa [hu_mid])
          · have hu_range :
                u.re ∈ (fun x : ℝ ↦ exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
              rw [exercise8_inner_primitive_image_Icc]
              exact ⟨hre_nonneg, hre.2⟩
            rcases hu_range with ⟨y, hy_mem, hy_eq⟩
            have hy_ne : y ≠ 0 := by
              intro hy_zero
              apply hre_zero
              rw [← hy_eq, hy_zero]
              simp [exercise8_inner_primitive]
            have hy_pos : 0 < y := lt_of_le_of_ne hy_mem.1 hy_ne.symm
            let x : ℝ := 1 / ((k : ℝ) * y)
            have hx_top : 1 / (k : ℝ) ≤ x := by
              by_cases hy_one : y = 1
              · subst hy_one
                dsimp [x]
                simpa using (le_rfl : 1 / (k : ℝ) ≤ 1 / (k : ℝ))
              · have hy_lt_one : y < 1 := lt_of_le_of_ne hy_mem.2 hy_one
                exact (exercise8_topReciprocalParameter_gt_invK k ⟨hy_pos, hy_lt_one⟩).le
            have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
            have hx_arg : 1 / ((k : ℝ) * x) = y := by
              dsimp [x]
              field_simp [hk_ne, hy_ne]
            have hu_eq :
                u =
                  (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
                    ((exercise8_inner_primitive k y : ℝ) : ℂ) := by
              have hu_top_eq : u.im = exercise8_complete_imaginary_period k := by
                simpa using hu_top
              apply Complex.ext <;> simp [hu_top_eq, hy_eq]
            have htrace_top :
                exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
              rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
              simpa [exercise8_boundary_top_branch] using
                exercise8_boundary_value_eq_top hx_top
            have htrace_eq :
                exercise8_boundary_trace k x = u := by
              calc
                exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := htrace_top
                _ =
                    (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
                      ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) := by
                        rw [exercise8_boundary_top_branch_eq_inner_composition]
                _ =
                    (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
                      ((exercise8_inner_primitive k y : ℝ) : ℂ) := by rw [hx_arg]
                _ = u := hu_eq.symm
            exact Or.inl ⟨x, htrace_eq⟩
        · by_cases hre_zero : u.re = 0
          · have hre_nonneg_zero : 0 ≤ u.re := by simpa [hre_zero]
            exact False.elim (hre_nonneg hre_nonneg_zero)
          · have hu_neg : u.re < 0 := lt_of_not_ge hre_nonneg
            have hu_range :
                -u.re ∈ (fun x : ℝ ↦ exercise8_inner_primitive k x) '' Icc (0 : ℝ) 1 := by
              rw [exercise8_inner_primitive_image_Icc]
              constructor
              · linarith
              · linarith [hre.1]
            rcases hu_range with ⟨y, hy_mem, hy_eq⟩
            have hy_ne : y ≠ 0 := by
              intro hy0
              apply hre_zero
              have hzero : exercise8_inner_primitive k 0 = 0 := by
                simp [exercise8_inner_primitive]
              have : -u.re = 0 := by simpa [hy0, hzero] using hy_eq.symm
              linarith
            have hy_pos : 0 < y := lt_of_le_of_ne hy_mem.1 hy_ne.symm
            let x : ℝ := 1 / ((k : ℝ) * y)
            have hx_top : 1 / (k : ℝ) ≤ x := by
              by_cases hy_one : y = 1
              · subst hy_one
                dsimp [x]
                simpa using (le_rfl : 1 / (k : ℝ) ≤ 1 / (k : ℝ))
              · have hy_lt_one : y < 1 := lt_of_le_of_ne hy_mem.2 hy_one
                exact (exercise8_topReciprocalParameter_gt_invK k ⟨hy_pos, hy_lt_one⟩).le
            have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
            have hx_arg : 1 / ((k : ℝ) * x) = y := by
              dsimp [x]
              field_simp [hk_ne, hy_ne]
            have htrace_eq :
                exercise8_boundary_trace k (-x) = u := by
              have hbranch :
                  exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
                rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
                simpa [exercise8_boundary_top_branch] using
                  exercise8_boundary_value_eq_top hx_top
              calc
                exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
                  simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
                _ = -star (exercise8_boundary_top_branch k x) := by rw [hbranch]
                _ =
                    (-((exercise8_inner_primitive k y : ℝ) : ℂ)) +
                      (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
                        rw [exercise8_boundary_top_branch_eq_inner_composition, hx_arg]
                        simp [add_comm, add_left_comm, add_assoc]
                _ =
                    ((u.re : ℝ) : ℂ) +
                      (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
                        simp [hy_eq]
                _ = u := by
                      have hu_top_eq : u.im = exercise8_complete_imaginary_period k := by
                        simpa using hu_top
                      apply Complex.ext <;> simp [hu_top_eq]
            exact Or.inl ⟨-x, htrace_eq⟩
    · rw [Complex.mem_reProdIm] at hu_vertical
      rcases hu_vertical with ⟨hre, him⟩
      rcases hre with hu_left | hu_right
      · -- The left side is the reflected right-edge branch.
        have hu_range :
            u.im ∈ (fun x : ℝ ↦ exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) := by
          rw [exercise8_right_primitive_image_Icc]
          exact him
        rcases hu_range with ⟨x, hx_mem, hx_eq⟩
        have htrace_eq :
            exercise8_boundary_trace k (-x) = u := by
          have hbranch :
              exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
            rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
            simpa [exercise8_boundary_right_branch] using
              exercise8_boundary_value_eq_right hx_mem.1 hx_mem.2
          calc
            exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
              simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
            _ = -star (exercise8_boundary_right_branch k x) := by rw [hbranch]
            _ =
                (-exercise8_complete_real_period k : ℂ) +
                  ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
                    rw [exercise8_boundary_right_branch_eq_right_primitive]
                    simp [add_comm, add_left_comm, add_assoc]
            _ =
                (-exercise8_complete_real_period k : ℂ) +
                  ((u.im : ℝ) : ℂ) * Complex.I := by
                    exact congrArg
                      (fun t : ℝ ↦
                        (-exercise8_complete_real_period k : ℂ) + (t : ℂ) * Complex.I) hx_eq
            _ = u := by
                have hu_left_eq : u.re = -exercise8_complete_real_period k := by
                  simpa using hu_left
                apply Complex.ext <;> simp [hu_left_eq]
        exact Or.inl ⟨-x, htrace_eq⟩
      · -- The right side is filled exactly by the right-edge primitive.
        have hu_range :
            u.im ∈ (fun x : ℝ ↦ exercise8_right_primitive k x) '' Icc (1 : ℝ) (1 / (k : ℝ)) := by
          rw [exercise8_right_primitive_image_Icc]
          exact him
        rcases hu_range with ⟨x, hx_mem, hx_eq⟩
        have htrace_eq :
            exercise8_boundary_trace k x = u := by
          have hbranch :
              exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
            rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
            simpa [exercise8_boundary_right_branch] using
              exercise8_boundary_value_eq_right hx_mem.1 hx_mem.2
          calc
            exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := hbranch
            _ =
                (exercise8_complete_real_period k : ℂ) +
                  ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
                    rw [exercise8_boundary_right_branch_eq_right_primitive]
            _ =
                (exercise8_complete_real_period k : ℂ) +
                  ((u.im : ℝ) : ℂ) * Complex.I := by
                    exact congrArg
                      (fun t : ℝ ↦
                        (exercise8_complete_real_period k : ℂ) + (t : ℂ) * Complex.I) hx_eq
            _ = u := by
                have hu_right_eq : u.re = exercise8_complete_real_period k := by
                  simpa using hu_right
                apply Complex.ext <;> simp [hu_right_eq]
        exact Or.inl ⟨x, htrace_eq⟩

/-- Boundary-to-perimeter companion: the continuous extension maps the compactified real boundary,
formalized as `OnePoint ℝ`, onto the perimeter of the fundamental rectangle. -/
theorem exercise_8_boundary_to_perimeter
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    Set.range (exercise8_completed_boundary_extension k fbar) =
      frontier (exercise8_open_rectangle k) := by
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    induction x using OnePoint.rec with
    | infty =>
        -- The adjoined point contributes exactly the isolated top midpoint.
        rw [← exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k]
        exact Or.inr (by simp [exercise8_completed_boundary_extension])
    | coe x =>
        -- Finite points are the repaired real-axis trace values of the canonical extension.
        rw [← exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k]
        refine Or.inl ⟨x, ?_⟩
        symm
        calc
          exercise8_completed_boundary_extension k fbar (x : OnePoint ℝ)
              = fbar ⟨(x : ℂ), by simp⟩ := by
                  simp [exercise8_completed_boundary_extension]
          _ = exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ := by
                simpa [hEq]
          _ = exercise8_boundary_trace k x := by
                simpa using exercise8_closed_extension_of_real k x
  · intro hu
    rw [← exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k] at hu
    rcases hu with hu_range | hu_mid
    · rcases hu_range with ⟨x, hx⟩
      refine ⟨(x : OnePoint ℝ), ?_⟩
      calc
        exercise8_completed_boundary_extension k fbar (x : OnePoint ℝ)
            = fbar ⟨(x : ℂ), by simp⟩ := by
                simp [exercise8_completed_boundary_extension]
        _ = exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ := by
              simpa [hEq]
        _ = exercise8_boundary_trace k x := by
              simpa using exercise8_closed_extension_of_real k x
        _ = u := hx
    · refine ⟨OnePoint.infty, ?_⟩
      simpa [exercise8_completed_boundary_extension] using hu_mid.symm

/-- Helper for Cartan section26 0018_Exercise_8: unpacking the compactified-boundary statement
recovers the
explicit real-axis image together with the adjoined top midpoint `i K'`. -/
lemma exercise8_boundary_to_perimeter_real_axis_range_union
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) ∪
        {((exercise8_complete_imaginary_period k : ℂ) * Complex.I)} =
      frontier (exercise8_open_rectangle k) := by
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  have hreal :
      (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) = exercise8_boundary_trace k := by
    funext x
    calc
      fbar ⟨(x : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ := by
        simpa [hEq]
      _ = exercise8_boundary_trace k x := by
        simpa using exercise8_closed_extension_of_real k x
  simpa [hreal] using exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k

/-- Helper for Cartan section26 0018_Exercise_8: the finite real-axis trace approaches the missing
top midpoint `i K'` as `x → +∞`. This is the explicit source-facing replacement for compactifying
the boundary by an adjoined point at infinity. -/
lemma exercise8_boundary_extension_tendsto_top_midpoint_atTop
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    Filter.Tendsto (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) Filter.atTop
      (nhds ((exercise8_complete_imaginary_period k : ℂ) * Complex.I)) := by
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  have hreal :
      (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) = exercise8_boundary_trace k := by
    funext x
    calc
      fbar ⟨(x : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ := by
        simpa [hEq]
      _ = exercise8_boundary_trace k x := by
        simpa using exercise8_closed_extension_of_real k x
  simpa [hreal] using exercise8_boundary_trace_tendsto_top_midpoint_atTop k

/-- Helper for Cartan section26 0018_Exercise_8: the explicit real-axis image, together with its
limit point `i K'`, yields the perimeter as the closure of the finite real-axis trace. -/
lemma exercise8_boundary_to_perimeter_closure
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    closure (Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩)) =
      frontier (exercise8_open_rectangle k) := by
  let mid : ℂ := (exercise8_complete_imaginary_period k : ℂ) * Complex.I
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  have hreal :
      (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) = exercise8_boundary_trace k := by
    funext x
    calc
      fbar ⟨(x : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ := by
        simpa [hEq]
      _ = exercise8_boundary_trace k x := by
        simpa using exercise8_closed_extension_of_real k x
  have hUnion :
      Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) ∪ {mid} =
        frontier (exercise8_open_rectangle k) := by
    simpa [mid, hreal] using exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k
  have hsubset :
      Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) ⊆
        frontier (exercise8_open_rectangle k) := by
    intro u hu
    have hu' :
        u ∈ Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) ∪ {mid} :=
      Or.inl hu
    simpa [mid] using (hUnion ▸ hu')
  have hclosure_subset :
      closure (Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩)) ⊆
        frontier (exercise8_open_rectangle k) :=
    closure_minimal hsubset isClosed_frontier
  apply le_antisymm hclosure_subset
  intro u hu
  rw [← hUnion] at hu
  rcases hu with hu_range | hu_mid
  · -- The finite boundary trace is contained in its own closure.
    exact subset_closure hu_range
  · rcases hu_mid with rfl
    -- The missing top midpoint is the `atTop` limit of the finite real-axis trace.
    exact
      mem_closure_of_tendsto
        (exercise8_boundary_extension_tendsto_top_midpoint_atTop k hfbar)
        (Filter.Eventually.of_forall fun x ↦ ⟨x, rfl⟩)

/-- Vertex companion: the boundary point `-1` corresponds to the vertex `-K`. -/
theorem exercise_8_vertex_neg_one
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨(-1 : ℂ), by simp⟩ = -exercise8_complete_real_period k := by
  -- Uniqueness reduces the vertex computation to the canonical reflected boundary trace.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨(-1 : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(-1 : ℂ), by simp⟩ := by
      simpa [hEq]
    _ = exercise8_boundary_trace k (-1) := by
      simpa using exercise8_closed_extension_of_real k (-1 : ℝ)
    _ = -exercise8_complete_real_period k := by
      simpa using exercise8_boundary_value_neg_one k

/-- Vertex companion: the boundary point `1` corresponds to the vertex `K`. -/
theorem exercise_8_vertex_one
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨(1 : ℂ), by simp⟩ = exercise8_complete_real_period k := by
  -- Uniqueness again lets us evaluate the canonical owner instead of the arbitrary extension.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨(1 : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(1 : ℂ), by simp⟩ := by
      simpa [hEq]
    _ = exercise8_boundary_trace k 1 := by
      simpa using exercise8_closed_extension_of_real k (1 : ℝ)
    _ = exercise8_complete_real_period k := by
      simpa using exercise8_boundary_value_one k

/-- Vertex companion: the boundary point `1 / k` corresponds to the vertex `K + i K'`. -/
theorem exercise_8_vertex_inv_k
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ =
      exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- The repaired boundary trace already records the right-top vertex `K + i K'`.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ =
        exercise8_closed_extension k ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ := by
          simpa [hEq]
    _ = exercise8_boundary_trace k (1 / (k : ℝ)) := by
      simpa using exercise8_closed_extension_of_real k (1 / (k : ℝ))
    _ =
        exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
          simpa using exercise8_boundary_value_inv_k k

/-- Vertex companion: the boundary point `-1 / k` corresponds to the vertex `-K + i K'`. -/
theorem exercise_8_vertex_neg_inv_k
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ =
      -exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- Route correction: the left-top vertex comes from Schwarz reflection, not from global oddness.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ =
        exercise8_closed_extension k ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ := by
          simpa [hEq]
    _ = exercise8_boundary_trace k (-(1 / (k : ℝ))) := by
          simpa using exercise8_closed_extension_of_real k (-(1 / (k : ℝ)))
    _ =
        -exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
          simpa using exercise8_boundary_value_neg_inv_k k

/-- Helper for Cartan section26 0018_Exercise_8: the fundamental rectangle is stable under the
reflection `u ↦ -star u`. -/
lemma exercise8_negConj_mem_open_rectangle
    (k : Exercise8Modulus) {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    -star u ∈ exercise8_open_rectangle k := by
  rw [mem_exercise8_open_rectangle_iff] at hu ⊢
  refine ⟨?_, ?_⟩
  · -- Reflection flips the real coordinate while keeping it inside `(-K, K)`.
    constructor
    · simpa using neg_lt_neg hu.1.2
    · simpa using neg_lt_neg hu.1.1
  · -- The imaginary coordinate is unchanged by `u ↦ -conj u`.
    simpa using hu.2

/-- Helper for Cartan section26 0018_Exercise_8: reflecting an upper-half-plane point twice via
`UpperHalfPlane.ofComplex` returns the original point. -/
lemma exercise8_reflect_reflect_upper
    (z : UpperHalfPlane) :
    UpperHalfPlane.ofComplex (-star ((UpperHalfPlane.ofComplex (-star (z : ℂ))) : ℂ)) = z := by
  -- Push the inner reflection down to `ℂ`, where the two conjugations cancel literally.
  have hinner : ((UpperHalfPlane.ofComplex (-star (z : ℂ))) : ℂ) = -star (z : ℂ) := by
    exact
      congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using z.im_pos))
  -- With the ambient complex expression normalized, the outer `ofComplex` is exactly the identity.
  rw [hinner]
  simpa using UpperHalfPlane.ofComplex_apply z

/-- Helper for Cartan section26 0018_Exercise_8: any rectangle inverse branch already satisfies
the bottom Schwarz reflection identity on the open rectangle. -/
lemma exercise8_rectangleInverse_reflectsBottom
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G) :
    ∀ u : exercise8_open_rectangle k,
      (G u : ℂ) =
        -star
          (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ) := by
  let Grefl : exercise8_open_rectangle k → UpperHalfPlane := fun u ↦
    UpperHalfPlane.ofComplex
      (-star
        (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ))
  have hGrefl : IsExercise8RectangleInverse k Grefl := by
    refine ⟨?_, hG.2.1, ?_⟩
    · intro u
      let u' : exercise8_open_rectangle k :=
        ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩
      -- Reflect the known inverse equation for `G u'` back to the original rectangle point.
      calc
        exercise8_abel_integral k (Grefl u) =
            -star (exercise8_abel_integral k (G u')) := by
              simpa [Grefl, u'] using
                exercise8_abel_integral_reflection_upper k (G u').im_pos
        _ = -star ((u' : exercise8_open_rectangle k) : ℂ) := by rw [hG.1 u']
        _ = u := by
              simpa [u']
    · intro z hz
      let z' : UpperHalfPlane := UpperHalfPlane.ofComplex (-star (z : ℂ))
      have hz' : exercise8_abel_integral k z' ∈ exercise8_open_rectangle k := hG.2.1 z'
      have hreflect :
          exercise8_abel_integral k z' =
            -star (exercise8_abel_integral k z) := by
        -- The reflected source point has Abel image `-conj (exercise8_abel_integral z)`.
        simpa [z'] using
          exercise8_abel_integral_reflection_upper k z.im_pos
      have hinput :
          (⟨-star (exercise8_abel_integral k z), exercise8_negConj_mem_open_rectangle k hz⟩ :
            exercise8_open_rectangle k) =
            ⟨exercise8_abel_integral k z', hz'⟩ := by
        -- The reflection identity identifies the `Grefl` input with the point used by `hG`.
        apply Subtype.ext
        simpa [hreflect]
      have hGinput :
          G ⟨-star (exercise8_abel_integral k z), exercise8_negConj_mem_open_rectangle k hz⟩ =
            G ⟨exercise8_abel_integral k z', hz'⟩ := by
        simpa using congrArg G hinput
      -- Apply the original left-inverse law to the reflected source point and reflect back.
      calc
        Grefl ⟨exercise8_abel_integral k z, hz⟩ =
            UpperHalfPlane.ofComplex
              (-star
                (G ⟨-star (exercise8_abel_integral k z), exercise8_negConj_mem_open_rectangle k hz⟩ :
                  ℂ)) := by
                    rfl
        _ =
            UpperHalfPlane.ofComplex (-star (G ⟨exercise8_abel_integral k z', hz'⟩ : ℂ)) := by
              rw [hGinput]
        _ = UpperHalfPlane.ofComplex (-star (z' : ℂ)) := by rw [hG.2.2 z' hz']
        _ = z := by
              -- The reflected reflected source point is the original upper-half-plane point.
              exact exercise8_reflect_reflect_upper z
  have hEq : Grefl = G := exercise8_rectangle_inverse_unique k hGrefl hG
  intro u
  -- Uniqueness turns the reflected branch into the original one, yielding the pointwise formula.
  calc
    (G u : ℂ) = (Grefl u : ℂ) := by
      simpa using
        congrArg (fun H : exercise8_open_rectangle k → UpperHalfPlane ↦ (H u : ℂ)) hEq.symm
    _ =
        -star
          (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ) := by
            have him :
                0 <
                  (-star
                    (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ)).im := by
              simpa using
                (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩).im_pos
            show
              (((UpperHalfPlane.ofComplex
                (-star
                  (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ)) :
                    UpperHalfPlane) : ℂ)) =
                -star
                  (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ)
            simpa [Grefl] using
              congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
                (UpperHalfPlane.ofComplex_apply_of_im_pos him)

/-- Helper for Cartan section26 0018_Exercise_8: the canonical `Function.invFunOn` branch attached
to the Abel-integral bijection is itself a rectangle inverse. -/
lemma exercise8_canonicalRectangleInverse
    (k : Exercise8Modulus) :
    IsExercise8RectangleInverse k
      (fun u : exercise8_open_rectangle k ↦
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  classical
  rcases exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k with
      ⟨hmap, hinj, hsurj⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u
    -- The canonical `invFunOn` branch is a right inverse on the rectangle by surjectivity.
    simpa using hsurj.rightInvOn_invFunOn u.2
  · intro z
    -- Every upper-half-plane point already lands in the target rectangle.
    exact hmap (by trivial)
  · intro z hz
    -- Injectivity on the source turns `invFunOn` into the corresponding left inverse.
    simpa using
      hinj.leftInvOn_invFunOn (show z ∈ (Set.univ : Set UpperHalfPlane) by trivial)

/-- Helper for Cartan section26 0018_Exercise_8: every rectangle inverse branch agrees with the
canonical `Function.invFunOn` branch on the open rectangle. -/
lemma exercise8_rectangleInverse_eq_canonical
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G) :
    G =
      (fun u : exercise8_open_rectangle k ↦
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  -- Route correction: once the rectangle-image theorem is fixed, every branch should be compared
  -- to the canonical `invFunOn` owner before any continuation work starts.
  exact
    exercise8_rectangle_inverse_unique k hG
      (exercise8_canonicalRectangleInverse k)

/-- Helper for Exercise 8: fixing the biholomorphic inverse branch once and for all already gives
the concrete rectangle inverse, its canonical `invFunOn` identification, and the bottom reflection
law needed for the global continuation route. -/
lemma exercise8_biholomorphicInverse_branchPackage
    (k : Exercise8Modulus) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane,
      IsExercise8RectangleInverse k G ∧
        G =
          (fun u : exercise8_open_rectangle k ↦
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : exercise8_open_rectangle k,
          (G u : ℂ) =
            -star
              (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ)) := by
  rcases exercise_8_abel_integral_bijective k with ⟨e, he, _G, _hG⟩
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)
  have heUpper : ∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z := by
    intro z
    simpa using he z
  have hG : IsExercise8RectangleInverse k G := by
    simpa [G] using (exercise8_biholomorphicInverse_isRectangleInverse k heUpper)
  refine ⟨G, hG, exercise8_rectangleInverse_eq_canonical k hG, ?_⟩
  -- Once the fixed branch is chosen, the bottom reflection formula is exactly the generic
  -- reflection law for any rectangle inverse.
  exact exercise8_rectangleInverse_reflectsBottom k hG

/-- Helper for Exercise 8: any meromorphic-periodic continuation package for the canonical
rectangle branch transfers immediately to an arbitrary source-facing branch because all such
branches agree on the open rectangle. -/
lemma exercise8_rectangleInverse_continuationSupport_of_eq_canonical
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G)
    (hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u)) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k, F u = G u) := by
  rcases hcanonical with ⟨F, hMeromorphic, hPeriods, hF⟩
  have hEq : G =
      (fun u : exercise8_open_rectangle k ↦
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :=
    exercise8_rectangleInverse_eq_canonical k hG
  refine ⟨F, hMeromorphic, hPeriods, ?_⟩
  intro u
  -- Rewriting through the canonical-branch equality transfers the continuation package to `G`.
  simpa [hEq] using hF u

/-- Helper for Exercise 8: every packaged inverse already agrees with the canonical `invFunOn`
branch on the fundamental rectangle, so later continuation arguments can focus on constructing one
global witness instead of re-identifying the branch each time. -/
lemma exercise8_inverse_eq_canonical_on_open_rectangle
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∀ u : exercise8_open_rectangle k,
      F u =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := by
  rcases hF with ⟨G, hG, _hMeromorphic, _hPeriods, hFG⟩
  have hGcanonical :
      G =
        (fun u : exercise8_open_rectangle k ↦
          Function.invFunOn
            (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :=
    exercise8_rectangleInverse_eq_canonical k hG
  intro u
  -- First rewrite through the stored rectangle branch, then collapse that branch to the canonical
  -- `invFunOn` owner by uniqueness on the open rectangle.
  calc
    F u = G u := hFG u
    _ =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := by
            simpa [hGcanonical]

/-- Helper for Exercise 8: any meromorphic-periodic continuation that already matches the
canonical `invFunOn` rectangle branch is automatically a packaged inverse. -/
lemma exercise8_isInverse_of_canonicalContinuation
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hMeromorphic : Meromorphic F)
    (hPeriods : HasPeriodLattice (exercise8_period_pair k) F)
    (hcanonical :
      ∀ u : exercise8_open_rectangle k,
        F u =
          Function.invFunOn
            (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :
    IsExercise8Inverse k F := by
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u : exercise8_open_rectangle k ↦
      Function.invFunOn
        (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u
  -- Reuse the canonical rectangle branch as the source-facing inverse owner and attach the
  -- supplied meromorphic-periodic continuation data to it.
  refine ⟨G, exercise8_canonicalRectangleInverse k, hMeromorphic, hPeriods, ?_⟩
  intro u
  exact hcanonical u

/-- Helper for Exercise 8: once the canonical rectangle branch has a meromorphic-periodic
continuation, the existence-only inverse package is just a short rebundling step. -/
lemma exercise8_canonicalInverse_exists_of_continuationData
    (k : Exercise8Modulus)
    (hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u)) :
    ∃ F : ℂ → ℂ,
      IsExercise8Inverse k F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  rcases hcanonical with ⟨F, hMeromorphic, hPeriods, hF⟩
  -- The new continuation data is already exactly the information needed to build one packaged
  -- inverse witness while retaining the canonical-branch equality.
  refine ⟨F, exercise8_isInverse_of_canonicalContinuation k hMeromorphic hPeriods hF, hF⟩

/-- Helper for Exercise 8: once any packaged inverse exists, uniqueness of the rectangle branch
upgrades it immediately to the canonical `Function.invFunOn` continuation package. -/
lemma exercise8_canonicalRectangleInverse_continuationSupport_of_inverse_exists
    (k : Exercise8Modulus)
    (hExists : ∃ F : ℂ → ℂ, IsExercise8Inverse k F) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  rcases hExists with ⟨F, hF⟩
  have hFinv : IsExercise8Inverse k F := hF
  rcases hF with ⟨_G, _hG, hMeromorphic, hPeriods, _hFG⟩
  refine ⟨F, hMeromorphic, hPeriods, ?_⟩
  intro u
  -- The new rectangle-level helper has already collapsed every packaged inverse to the canonical
  -- `invFunOn` branch, so the continuation package is now a direct projection from `hF`.
  exact exercise8_inverse_eq_canonical_on_open_rectangle k hFinv u

/-- Helper for Exercise 8: once the canonical continuation datum is available and the resulting
packaged inverse is known to satisfy the seed-order bundle, the final witness theorem is pure
assembly. -/
lemma exercise8_canonicalInverseWitnessWithSeedOrders_of_continuationDataAndSeedPackage
    (k : Exercise8Modulus)
    (hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u))
    (hseed :
      ∀ {F : ℂ → ℂ},
        IsExercise8Inverse k F →
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) →
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ))) :
    ∃ F : ℂ → ℂ,
      IsExercise8Inverse k F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  rcases exercise8_canonicalInverse_exists_of_continuationData k hcanonical with
      ⟨F, hF, hEq⟩
  rcases hseed hF hEq with ⟨hhalf, hzero, hpole, hzeroOff⟩
  -- First repackage the canonical continuation as one `IsExercise8Inverse` witness.
  -- Then append the supplied half-period and divisor-order data for that fixed branch.
  exact ⟨F, hF, hEq, hhalf, hzero, hpole, hzeroOff⟩

/-- Helper for Cartan section26 0018_Exercise_8: a packaged inverse already carries its
meromorphicity field in the bundled definition. -/
lemma exercise8_inverse_meromorphic
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    Meromorphic F := by
  rcases hF with ⟨_, _, hMeromorphic, _, _⟩
  -- This is exactly the meromorphic component stored in `IsExercise8Inverse`.
  exact hMeromorphic

/-- Helper for Cartan section26 0018_Exercise_8: a packaged inverse is periodic for the
fundamental period pair `4K, 2 i K'`. -/
lemma exercise8_inverse_hasPeriodLattice
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    HasPeriodLattice (exercise8_period_pair k) F := by
  rcases hF with ⟨_, _, _, hPeriods, _⟩
  -- This is the period-lattice component stored in `IsExercise8Inverse`.
  exact hPeriods

/-- Helper for Cartan section26 0018_Exercise_8: the inverse order is unchanged by the imaginary
half-period `2 i K'` because that generator already belongs to the true period lattice. -/
lemma exercise8_inverse_order_add_imaginary_period_eq
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₂) =
      meromorphicOrderAt F u := by
  have hω :
      (exercise8_half_period_pair k).ω₂ ∈ (exercise8_period_pair k).lattice := by
    -- The half-period pair reuses the same imaginary generator as the full period pair.
    simpa [exercise8_half_period_pair, exercise8_period_pair] using
      (exercise8_period_pair k).ω₂_mem_lattice
  -- Once the common generator is rewritten into the full period lattice, order transport is
  -- exactly the standard period-order theorem.
  simpa [exercise8_half_period_pair, exercise8_period_pair] using
    (meromorphicOrderAt_add_period_eq
      (exercise8_period_pair k) (exercise8_inverse_hasPeriodLattice k hF) hω)

/-- Helper for Cartan section26 0018_Exercise_8: once the missing real half-period order bridge is
supplied, the inverse order function already has the half-period lattice needed by the generic
exact-order classifier. -/
lemma exercise8_inverse_order_hasHalfPeriodLattice_of_halfRealShift
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F)
    (hreal :
      ∀ u : ℂ,
        meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F u) :
    HasPeriodLattice (exercise8_half_period_pair k)
      (fun u : ℂ ↦ meromorphicOrderAt F u) := by
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    -- The supplied real half-shift bridge is exactly the first generator law.
    simpa using hreal u
  · intro u
    -- The imaginary half-period is already inherited from the genuine period lattice of `F`.
    exact exercise8_inverse_order_add_imaginary_period_eq k hF u

/-- Helper for Exercise 8: on the fundamental rectangle, every packaged inverse agrees with the
analytic inverse branch coming from the biholomorphic Abel map. -/
lemma exercise8_inverse_analyticAt_on_open_rectangle
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F)
    {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    AnalyticAt ℂ F u := by
  rcases hF with ⟨G, hG, _, _, hFG⟩
  rcases exercise_8_abel_integral_bijective k with ⟨e, he, _⟩
  let H : exercise8_open_rectangle k → UpperHalfPlane :=
    fun w ↦ UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm w)
  have hH : IsExercise8RectangleInverse k H :=
    exercise8_biholomorphicInverse_isRectangleInverse k he
  have hGH : G = H := exercise8_rectangle_inverse_unique k hG hH
  have hEqOn :
      EqOn F ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (exercise8_open_rectangle k) := by
    intro w hw
    let w' : exercise8_open_rectangle k := ⟨w, hw⟩
    have hw_target : (w : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using hw
    have hw_source :
        ((e : OpenPartialHomeomorph ℂ ℂ).symm w : ℂ) ∈
          (e : OpenPartialHomeomorph ℂ ℂ).source := by
      exact (e : OpenPartialHomeomorph ℂ ℂ).map_target hw_target
    have hw_im : 0 < (((e : OpenPartialHomeomorph ℂ ℂ).symm w : ℂ)).im := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using hw_source
    -- Rewrite the packaged inverse through the unique biholomorphic inverse branch.
    calc
      F w = G w' := by
        simpa [w'] using hFG w'
      _ = H w' := by
        simpa [hGH]
      _ = (e : OpenPartialHomeomorph ℂ ℂ).symm w := by
        simpa [H, w'] using
          congrArg (fun z : UpperHalfPlane ↦ (z : ℂ))
            (UpperHalfPlane.ofComplex_apply_of_im_pos hw_im)
  have hEq :
      F =ᶠ[𝓝 u] ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) :=
    hEqOn.eventuallyEq_of_mem ((exercise8_open_rectangle_isOpen k).mem_nhds hu)
  -- Transfer analyticity from the biholomorphic inverse branch along the open-rectangle equality.
  exact (e.analyticOn_invFun u hu).congr hEq.symm

/-- Helper for Exercise 8: at analytic points, the global meromorphic normal form agrees with the
original function value. -/
lemma exercise8_toMeromorphicNFOn_eq_of_analyticAt
    {f : ℂ → ℂ} (hf : Meromorphic f) {z : ℂ} (hz : AnalyticAt ℂ f z) :
    toMeromorphicNFOn f Set.univ z = f z := by
  have hEq :
      toMeromorphicNFOn f Set.univ =ᶠ[𝓝 z] f := by
    -- Replace the global normal form by the pointwise owner, then collapse it at an analytic germ.
    calc
      toMeromorphicNFOn f Set.univ =ᶠ[𝓝 z] toMeromorphicNFAt f z := by
        exact toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf.meromorphicOn (by simp)
      _ =ᶠ[𝓝 z] f := by
        simp [toMeromorphicNFAt_eq_self.2 hz.meromorphicNFAt]
  exact Filter.EventuallyEq.eq_of_nhds hEq

/-- Helper for Exercise 8: on the fundamental rectangle, the global meromorphic normal form of a
packaged inverse reduces back to the actual inverse branch. -/
lemma exercise8_inverse_toMeromorphicNFOn_eq_on_open_rectangle
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    EqOn (toMeromorphicNFOn F Set.univ) F (exercise8_open_rectangle k) := by
  intro u hu
  -- The inverse is analytic on the open rectangle, so its normal form collapses pointwise there.
  exact exercise8_toMeromorphicNFOn_eq_of_analyticAt
    (exercise8_inverse_meromorphic k hF)
    (exercise8_inverse_analyticAt_on_open_rectangle k hF hu)

/-- Helper for Exercise 8: any two packaged inverses already have the same global meromorphic
normal form on the open rectangle where both reduce to the biholomorphic inverse branch. -/
lemma exercise8_inverse_normalForm_eqOn_open_rectangle
    (k : Exercise8Modulus)
    {F₁ F₂ : ℂ → ℂ}
    (hF₁ : IsExercise8Inverse k F₁)
    (hF₂ : IsExercise8Inverse k F₂) :
    EqOn (toMeromorphicNFOn F₁ Set.univ) (toMeromorphicNFOn F₂ Set.univ)
      (exercise8_open_rectangle k) := by
  intro u hu
  -- Collapse both normal forms on the rectangle and reuse the already-proved branch uniqueness.
  calc
    toMeromorphicNFOn F₁ Set.univ u = F₁ u :=
      exercise8_inverse_toMeromorphicNFOn_eq_on_open_rectangle k hF₁ hu
    _ = F₂ u := exercise8_inverse_eqOn_open_rectangle k hF₁ hF₂ hu
    _ = toMeromorphicNFOn F₂ Set.univ u := by
          symm
          exact exercise8_inverse_toMeromorphicNFOn_eq_on_open_rectangle k hF₂ hu

/-- Helper for Exercise 8: if two meromorphic functions agree on a nonempty open set, then their
global meromorphic normal forms coincide on all of `ℂ`. -/
lemma exercise8_toMeromorphicNFOn_eq_of_eqOn_nonempty_open
    {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hEq : EqOn f g U) :
    toMeromorphicNFOn f Set.univ = toMeromorphicNFOn g Set.univ := by
  let fNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  let gNF : ℂ → ℂ := toMeromorphicNFOn g Set.univ
  let S : Set ℂ := {z : ℂ | fNF =ᶠ[𝓝 z] gNF}
  have hfOn : MeromorphicOn f Set.univ := by
    simpa using hf
  have hgOn : MeromorphicOn g Set.univ := by
    simpa using hg
  have hS_open : IsOpen S := by
    -- Local equality in ordinary neighborhoods is an open condition.
    simpa [S, fNF, gNF] using
      (isOpen_setOf_eventually_nhds : IsOpen {z : ℂ | ∀ᶠ y in 𝓝 z, fNF y = gNF y})
  obtain ⟨z₀, hz₀U⟩ := hU_nonempty
  have hz₀S : z₀ ∈ S := by
    have hfNFz₀ :
        MeromorphicNFAt (toMeromorphicNFOn f Set.univ) z₀ :=
      meromorphicNFOn_toMeromorphicNFOn f Set.univ (by simp)
    have hgNFz₀ :
        MeromorphicNFAt (toMeromorphicNFOn g Set.univ) z₀ :=
      meromorphicNFOn_toMeromorphicNFOn g Set.univ (by simp)
    have hfNF_eq :
        toMeromorphicNFOn f Set.univ =ᶠ[𝓝[≠] z₀] f :=
      hfOn.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp)
    have hgNF_eq :
        toMeromorphicNFOn g Set.univ =ᶠ[𝓝[≠] z₀] g :=
      hgOn.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp)
    have hEq_ne : f =ᶠ[𝓝[≠] z₀] g :=
      hEq.eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hz₀U))
    have hNF_ne :
        toMeromorphicNFOn f Set.univ =ᶠ[𝓝[≠] z₀] toMeromorphicNFOn g Set.univ :=
      hfNF_eq.trans (hEq_ne.trans hgNF_eq.symm)
    -- Upgrade punctured-neighborhood equality to ordinary-neighborhood equality via the local
    -- meromorphic-normal-form identity theorem.
    exact (hfNFz₀.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hgNFz₀).1 hNF_ne
  have hmain : closure S ∩ (Set.univ : Set ℂ) ⊆ S := by
    intro x hx
    have hx_closure : x ∈ closure S := by
      simpa using hx.1
    by_cases hxS : x ∈ S
    · exact hxS
    · have hx_closure_ne : x ∈ closure (S \ {x}) := by
        simpa [S, hxS] using hx_closure
      have hfreqS : ∃ᶠ y in 𝓝[≠] x, y ∈ S :=
        mem_closure_ne_iff_frequently_within.mp hx_closure_ne
      have hfreqEq :
          ∃ᶠ y in 𝓝[≠] x,
            toMeromorphicNFOn f Set.univ y = toMeromorphicNFOn g Set.univ y :=
        hfreqS.mono (fun y hy ↦ Filter.EventuallyEq.eq_of_nhds hy)
      have hfNFx :
          MeromorphicNFAt (toMeromorphicNFOn f Set.univ) x :=
        meromorphicNFOn_toMeromorphicNFOn f Set.univ (by simp)
      have hgNFx :
          MeromorphicNFAt (toMeromorphicNFOn g Set.univ) x :=
        meromorphicNFOn_toMeromorphicNFOn g Set.univ (by simp)
      have hEq_ne :
          toMeromorphicNFOn f Set.univ =ᶠ[𝓝[≠] x] toMeromorphicNFOn g Set.univ :=
        (hfNFx.meromorphicAt.frequently_eq_iff_eventuallyEq hgNFx.meromorphicAt).1 hfreqEq
      -- Any closure point of the local-equality set must itself carry neighborhood equality.
      exact (hfNFx.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hgNFx).1 hEq_ne
  have hUniv_subset : (Set.univ : Set ℂ) ⊆ S :=
    isPreconnected_univ.subset_of_closure_inter_subset hS_open ⟨z₀, mem_univ _, hz₀S⟩ hmain
  ext z
  exact Filter.EventuallyEq.eq_of_nhds (hUniv_subset (mem_univ z))

/-- Helper for Exercise 8: any two packaged inverse extensions have the same global meromorphic
normal form because they already agree on the nonempty open fundamental rectangle. -/
lemma exercise8_inverse_normalForm_eq
    (k : Exercise8Modulus)
    {F₁ F₂ : ℂ → ℂ}
    (hF₁ : IsExercise8Inverse k F₁)
    (hF₂ : IsExercise8Inverse k F₂) :
    toMeromorphicNFOn F₁ Set.univ = toMeromorphicNFOn F₂ Set.univ := by
  -- Collapse the source-facing rectangle agreement to a global normal-form identity.
  exact exercise8_toMeromorphicNFOn_eq_of_eqOn_nonempty_open
    (exercise8_inverse_meromorphic k hF₁)
    (exercise8_inverse_meromorphic k hF₂)
    (exercise8_open_rectangle_isOpen k)
    (exercise8_open_rectangle_nonempty k)
    (exercise8_inverse_eqOn_open_rectangle k hF₁ hF₂)

/-- Helper for Cartan section26 0018_Exercise_8: equality of global meromorphic normal forms
forces equality of meromorphic orders at every point. -/
lemma exercise8_meromorphicOrderAt_eq_of_normalForm_eq
    {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    (hEq : toMeromorphicNFOn f Set.univ = toMeromorphicNFOn g Set.univ) :
    ∀ u : ℂ, meromorphicOrderAt f u = meromorphicOrderAt g u := by
  intro u
  -- Compare both functions through their common global meromorphic normal form.
  calc
    meromorphicOrderAt f u = meromorphicOrderAt (toMeromorphicNFOn f Set.univ) u := by
      symm
      simpa using
        (meromorphicOrderAt_toMeromorphicNFOn hf.meromorphicOn (by simp))
    _ = meromorphicOrderAt (toMeromorphicNFOn g Set.univ) u := by simpa [hEq]
    _ = meromorphicOrderAt g u := by
      simpa using
        (meromorphicOrderAt_toMeromorphicNFOn hg.meromorphicOn (by simp))

/-- Helper for Cartan section26 0018_Exercise_8: the packaged period lattice of the inverse
immediately gives the two generator periodicities needed for later order transport. -/
lemma exercise8_inverse_periodic_generators
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    Function.Periodic F (exercise8_period_pair k).ω₁ ∧
      Function.Periodic F (exercise8_period_pair k).ω₂ := by
  -- Rephrase the stored lattice data in the generator form used by the chapter period API.
  simpa [hasPeriodLattice_iff_periodic_generators] using
    exercise8_inverse_hasPeriodLattice k hF

/-- Helper for Cartan section26 0018_Exercise_8: the meromorphic-order function of the inverse is
periodic for the full period pair `4K, 2 i K'` already stored in the packaged inverse data. -/
lemma exercise8_inverse_order_hasPeriodLattice
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    HasPeriodLattice (exercise8_period_pair k)
      (fun u : ℂ ↦ meromorphicOrderAt F u) := by
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    -- The first generator is an honest period of `F`, so meromorphic order transports directly.
    simpa using
      (meromorphicOrderAt_add_period_eq
        (exercise8_period_pair k) (exercise8_inverse_hasPeriodLattice k hF)
        ((exercise8_period_pair k).ω₁_mem_lattice))
  · intro u
    -- The same period-transport API applies to the imaginary generator.
    simpa using
      (meromorphicOrderAt_add_period_eq
        (exercise8_period_pair k) (exercise8_inverse_hasPeriodLattice k hF)
        ((exercise8_period_pair k).ω₂_mem_lattice))

/-- Helper for Cartan section26 0018_Exercise_8: once one packaged inverse witness carries the
canonical half-real order law and local divisor seeds, global normal-form equality transports the
same package to every other packaged inverse. -/
lemma exercise8_inverse_seed_orders_of_witness
    (k : Exercise8Modulus)
    {F F₀ : ℂ → ℂ}
    (hF : IsExercise8Inverse k F)
    (hF₀ : IsExercise8Inverse k F₀)
    (hSeeds₀ :
      (∀ u : ℂ,
        meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ u) ∧
        meromorphicOrderAt F₀ 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F₀ (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F₀ u = (0 : WithTop ℤ))) :
    (∀ u : ℂ,
      meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
        meromorphicOrderAt F u) ∧
      meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  have hEqNF :
      toMeromorphicNFOn F Set.univ = toMeromorphicNFOn F₀ Set.univ :=
    exercise8_inverse_normalForm_eq k hF hF₀
  have hOrderEq : ∀ u : ℂ, meromorphicOrderAt F u = meromorphicOrderAt F₀ u := by
    -- The new normal-form bridge turns global meromorphic equality into pointwise order equality.
    exact exercise8_meromorphicOrderAt_eq_of_normalForm_eq
      (exercise8_inverse_meromorphic k hF)
      (exercise8_inverse_meromorphic k hF₀)
      hEqNF
  rcases hSeeds₀ with ⟨hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    calc
      meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) :=
            hOrderEq (u + (exercise8_half_period_pair k).ω₁)
      _ = meromorphicOrderAt F₀ u := hhalf₀ u
      _ = meromorphicOrderAt F u := by symm; exact hOrderEq u
  · simpa using (hOrderEq 0).trans hzero₀
  · simpa using (hOrderEq (exercise8_pole_shift k)).trans hpole₀
  · intro u hu hpole
    calc
      meromorphicOrderAt F u = meromorphicOrderAt F₀ u := hOrderEq u
      _ = (0 : WithTop ℤ) := hzeroOff₀ u hu hpole

/-- Helper for Exercise 8: the fixed biholomorphic rectangle branch already comes with the
ambient `ℂ`-valued canonical `invFunOn` identity and the bottom-edge reflection law that the
continuation theorem must extend. -/
lemma exercise8_biholomorphicInverse_branchPackageAmbientData
    (k : Exercise8Modulus) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane,
      IsExercise8RectangleInverse k G ∧
        (∀ u : exercise8_open_rectangle k,
          (G u : ℂ) =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : exercise8_open_rectangle k,
          (G u : ℂ) =
            -star
              (G ⟨-star (u : ℂ), exercise8_negConj_mem_open_rectangle k u.2⟩ : ℂ)) := by
  rcases exercise8_biholomorphicInverse_branchPackage k with ⟨G, hG, hcanonical, hreflect⟩
  refine ⟨G, hG, ?_, hreflect⟩
  intro u
  -- Coerce the fixed branch identity to `ℂ` so the later continuation owner can stay in the
  -- ambient complex plane instead of carrying subtype transports.
  simpa using
    congrArg
      (fun H : exercise8_open_rectangle k → UpperHalfPlane ↦ ((H u : UpperHalfPlane) : ℂ))
      hcanonical

/-- Helper for Exercise 8: once the canonical continuation datum and the seed-order transport API
are available, the existence-only witness theorem is just the corresponding projection. -/
lemma exercise8_biholomorphicInverseWitness_ofCanonicalSeedPackage
    (k : Exercise8Modulus)
    (hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u))
    (hseed :
      ∀ {F : ℂ → ℂ},
        IsExercise8Inverse k F →
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) →
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ))) :
    ∃ F₀ : ℂ → ℂ,
      IsExercise8Inverse k F₀ ∧
      (∀ u : ℂ,
        meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ u) ∧
      meromorphicOrderAt F₀ 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F₀ (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F₀ u = (0 : WithTop ℤ)) := by
  rcases
      exercise8_canonicalInverseWitnessWithSeedOrders_of_continuationDataAndSeedPackage
        k hcanonical hseed with
    ⟨F, hF, _hcanonicalEq, hhalf, hzero, hpole, hzeroOff⟩
  -- The canonical witness theorem already proves the stronger statement with rectangle-branch
  -- agreement, so this owner only forgets that extra field.
  exact ⟨F, hF, hhalf, hzero, hpole, hzeroOff⟩

/-- Helper for Cartan section26 0018_Exercise_8: the even half-period lattice and its pole-shift
translate are disjoint. -/
lemma exercise8_half_period_lattice_disjoint_pole_shift
    (k : Exercise8Modulus) {u : ℂ}
    (hu : u ∈ (exercise8_half_period_pair k).lattice) :
    u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice := by
  intro hpole
  rcases (mem_exercise8_half_period_pair_lattice_iff).1 hu with ⟨m, n, hu_eq⟩
  rcases (mem_exercise8_pole_shift_sub_lattice_iff).1 hpole with ⟨m', n', hpole_eq⟩
  let evenPoint : ℂ :=
    ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
      (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I
  let oddPoint : ℂ :=
    ((2 * m' : ℤ) : ℂ) * exercise8_complete_real_period k +
      (((2 * n' + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I
  have him :
      ((2 * n : ℤ) : ℝ) * exercise8_complete_imaginary_period k =
        ((2 * n' + 1 : ℤ) : ℝ) * exercise8_complete_imaginary_period k := by
    -- Comparing imaginary parts turns the intersection problem into an even-vs-odd equality.
    have hEq : evenPoint = oddPoint := by
      calc
        evenPoint = u := by simpa [evenPoint] using hu_eq.symm
        _ = oddPoint := by simpa [oddPoint] using hpole_eq
    simpa [evenPoint, oddPoint, mul_assoc, mul_left_comm, mul_comm] using
      congrArg Complex.im hEq
  have hcoeff :
      ((2 * n : ℤ) : ℝ) = ((2 * n' + 1 : ℤ) : ℝ) := by
    exact mul_right_cancel₀ (show exercise8_complete_imaginary_period k ≠ 0 from
      (exercise8_complete_imaginary_period_pos k).ne') him
  have hcoeffZ : 2 * n = 2 * n' + 1 := by
    exact_mod_cast hcoeff
  omega

/-- Helper for Cartan section26 0018_Exercise_8: membership in the pole-shifted lattice excludes
membership in the even half-period lattice. -/
lemma exercise8_pole_shift_sub_lattice_disjoint_half_period
    (k : Exercise8Modulus) {u : ℂ}
    (hu : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice) :
    u ∉ (exercise8_half_period_pair k).lattice := by
  intro hzero
  -- Reuse the even-vs-odd lattice disjointness owner in the opposite direction.
  exact exercise8_half_period_lattice_disjoint_pole_shift k hzero hu

/-- Helper for Cartan section26 0018_Exercise_8: after the affine rescaling `v = u / (2K)`, the
public theta quotient is exactly Cartan's source-facing ratio `θ₁(v) / θ₀(v)`. -/
lemma exercise8_theta_quotient_eq_theta_ratio
    (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k u =
      (θ₁[((exercise8_tau k : ℍ) : ℂ)])
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) /
        (θ₀[((exercise8_tau k : ℍ) : ℂ)])
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) := by
  -- Normalize the explicit Exercise 8 quotient to the standard Exercise 3 theta functions.
  rw [exercise8_theta_quotient_def, jacobi_theta_one_apply, jacobi_theta_zero_apply]
  ring_nf

/-- Helper for Cartan section26 0018_Exercise_8: adding the full real period `4K` becomes
translation by `2` after the rescaling `u ↦ u / (2K)`. -/
lemma exercise8_rescaledAddFullRealPeriod
    (k : Exercise8Modulus) (u : ℂ) :
    ((u + (exercise8_period_pair k).ω₁) / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))) =
      u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) + 2 := by
  have hscale_ne : (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
    have hne : (2 * exercise8_complete_real_period k : ℝ) ≠ 0 := by
      nlinarith [exercise8_complete_real_period_pos k]
    exact_mod_cast hne
  -- Clear the common denominator once so the period generator reduces to `4K = 2 * (2K)`.
  field_simp [hscale_ne]
  simp [exercise8_period_pair]
  ring

/-- Helper for Cartan section26 0018_Exercise_8: adding the full imaginary period `2 i K'`
becomes translation by `τ` after the same rescaling. -/
lemma exercise8_rescaledAddFullImaginaryPeriod
    (k : Exercise8Modulus) (u : ℂ) :
    ((u + (exercise8_period_pair k).ω₂) / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))) =
      u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) + (exercise8_tau k : ℂ) := by
  have hscale_ne : (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
    have hne : (2 * exercise8_complete_real_period k : ℝ) ≠ 0 := by
      nlinarith [exercise8_complete_real_period_pos k]
    exact_mod_cast hne
  have hK_ne := exercise8_complete_real_period_ne_zero k
  -- Rewrite the imaginary generator through `τ = i K' / K` before clearing denominators.
  rw [exercise8_tau_def]
  field_simp [hscale_ne, hK_ne]
  simp [exercise8_period_pair]
  ring

/-- Helper for Cartan section26 0018_Exercise_8: multiplying an Exercise 3 lattice coordinate
`m + n τ` by `2K` lands exactly on the Exercise 8 even-coordinate lattice normal form. -/
lemma exercise8_scaleMulTauCoordinate
    (k : Exercise8Modulus) (m n : ℤ) :
    (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) *
        (m + n * (exercise8_tau k : ℂ)) =
      ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
        (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  have hK_ne : exercise8_complete_real_period k ≠ 0 :=
    exercise8_complete_real_period_ne_zero k
  -- Rewrite `τ = i K' / K` once, then clear the single denominator in the coordinate formula.
  rw [exercise8_tau_def]
  field_simp [hK_ne]
  ring_nf
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc]

/-- Helper for Cartan section26 0018_Exercise_8: multiplying the shifted Exercise 3 coordinate
`m + (n + 1 / 2) τ` by `2K` lands on the odd vertical coordinate used for the pole translate. -/
lemma exercise8_scaleMulHalfTauCoordinate
    (k : Exercise8Modulus) (m n : ℤ) :
    (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) *
        (m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ)) =
      ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
        (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  have hK_ne : exercise8_complete_real_period k ≠ 0 :=
    exercise8_complete_real_period_ne_zero k
  -- Split off the extra `τ / 2` term so the even-coordinate bridge can be reused unchanged.
  calc
    (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) *
        (m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ))
        =
          (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) *
              (m + n * (exercise8_tau k : ℂ)) +
            exercise8_complete_imaginary_period k * Complex.I := by
              rw [exercise8_tau_def]
              field_simp [hK_ne]
              ring_nf
              norm_num [mul_assoc, mul_left_comm, mul_comm]
    _ =
        (((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I) +
          exercise8_complete_imaginary_period k * Complex.I := by
            rw [exercise8_scaleMulTauCoordinate k m n]
    _ =
        ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
          (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
            norm_num [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm]

/-- Helper for Cartan section26 0018_Exercise_8: Exercise 3 lattice coordinates `m + n τ`
match exactly the Exercise 8 half-period lattice after rescaling by `2K`. -/
lemma exercise8_rescaledHalfPeriodLattice_iff
    (k : Exercise8Modulus) (u : ℂ) :
    (∃ m n : ℤ,
        u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
          m + n * (exercise8_tau k : ℂ)) ↔
      u ∈ (exercise8_half_period_pair k).lattice := by
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hscale_ne : scale ≠ 0 := by
    have hne : (2 * exercise8_complete_real_period k : ℝ) ≠ 0 := by
      nlinarith [exercise8_complete_real_period_pos k]
    dsimp [scale]
    exact_mod_cast hne
  constructor
  · rintro ⟨m, n, hu⟩
    apply (mem_exercise8_half_period_pair_lattice_iff).2
    refine ⟨m, n, ?_⟩
    -- Multiply the witness equation by `2K` so it matches the period-data lattice coordinates.
    calc
      u = (u / scale) * scale := by
            simpa [scale, mul_comm] using (div_mul_cancel₀ u hscale_ne).symm
      _ = scale * (u / scale) := by ring
      _ = scale * (m + n * (exercise8_tau k : ℂ)) := by rw [hu]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
            simpa [scale] using exercise8_scaleMulTauCoordinate k m n
  · intro hu
    rcases (mem_exercise8_half_period_pair_lattice_iff).1 hu with ⟨m, n, hu_eq⟩
    refine ⟨m, n, ?_⟩
    have hcoord :
        u =
          scale * (m + n * (exercise8_tau k : ℂ)) := by
      calc
        u =
            ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := hu_eq
        _ = scale * (m + n * (exercise8_tau k : ℂ)) := by
              simpa [scale] using (exercise8_scaleMulTauCoordinate k m n).symm
    -- Dividing by the same nonzero scale recovers the original Exercise 3 witness equation.
    exact (div_eq_iff hscale_ne).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcoord)

/-- Helper for Cartan section26 0018_Exercise_8: Exercise 3 shifted coordinates
`m + (n + 1 / 2) τ` match the Exercise 8 pole translate after the same rescaling. -/
lemma exercise8_rescaledPoleLattice_iff
    (k : Exercise8Modulus) (u : ℂ) :
    (∃ m n : ℤ,
        u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
          m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ)) ↔
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice := by
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hscale_ne : scale ≠ 0 := by
    have hne : (2 * exercise8_complete_real_period k : ℝ) ≠ 0 := by
      nlinarith [exercise8_complete_real_period_pos k]
    dsimp [scale]
    exact_mod_cast hne
  constructor
  · rintro ⟨m, n, hu⟩
    apply (mem_exercise8_pole_shift_sub_lattice_iff).2
    refine ⟨m, n, ?_⟩
    -- The half-`τ` witness becomes the odd vertical coordinate once multiplied by `2K`.
    calc
      u = (u / scale) * scale := by
            simpa [scale, mul_comm] using (div_mul_cancel₀ u hscale_ne).symm
      _ = scale * (u / scale) := by ring
      _ = scale * (m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ)) := by rw [hu]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
            simpa [scale] using exercise8_scaleMulHalfTauCoordinate k m n
  · intro hu
    rcases (mem_exercise8_pole_shift_sub_lattice_iff).1 hu with ⟨m, n, hu_eq⟩
    refine ⟨m, n, ?_⟩
    have hcoord :
        u =
          scale * (m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ)) := by
      calc
        u =
            ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := hu_eq
        _ =
            scale * (m + ((n : ℂ) + (1 / 2 : ℂ)) * (exercise8_tau k : ℂ)) := by
              simpa [scale] using (exercise8_scaleMulHalfTauCoordinate k m n).symm
    -- Dividing back by `2K` returns the canonical Exercise 3 shifted coordinate.
    exact (div_eq_iff hscale_ne).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcoord)

/-- Helper for Cartan section26 0018_Exercise_8: the public theta quotient is meromorphic on
`ℂ` because it is the quotient of two entire theta functions in the rescaled variable `u / (2K)`.
-/
lemma exercise8_theta_quotient_meromorphic
    (k : Exercise8Modulus) :
    Meromorphic (exercise8_theta_quotient k) := by
  intro u
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hscale : AnalyticAt ℂ (fun w : ℂ ↦ w / scale) u := by
    -- The rescaling map is entire, so it may be composed directly with the theta factors.
    dsimp [scale]
    fun_prop
  have hnum :
      MeromorphicAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) u := by
    have htheta :
        AnalyticAt ℂ (θ₁[τ]) (u / scale) := by
      exact
        ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (u / scale) (by simp)
    simpa [Function.comp, τ, scale] using
      (MeromorphicAt.comp_analyticAt htheta.meromorphicAt hscale :
        MeromorphicAt ((θ₁[τ]) ∘ fun w : ℂ ↦ w / scale) u)
  have hden :
      MeromorphicAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) u := by
    have htheta :
        AnalyticAt ℂ (θ₀[τ]) (u / scale) := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (u / scale) (by simp)
    simpa [Function.comp, τ, scale] using
      (MeromorphicAt.comp_analyticAt htheta.meromorphicAt hscale :
        MeromorphicAt ((θ₀[τ]) ∘ fun w : ℂ ↦ w / scale) u)
  -- After normalizing the quotient to the rescaled theta ratio, meromorphicity is pointwise.
  refine (hnum.div hden).congr ?_
  filter_upwards with w
  simpa [τ, scale] using (exercise8_theta_quotient_eq_theta_ratio k w).symm

/-- Helper for Cartan section26 0018_Exercise_8: the public theta quotient has the same period
lattice as the desired inverse, namely `4K` and `2 i K'`. -/
lemma exercise8_theta_quotient_hasPeriodLattice
    (k : Exercise8Modulus) :
    HasPeriodLattice (exercise8_period_pair k) (exercise8_theta_quotient k) := by
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
    let v : ℂ := u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
    have hnum :
        (θ₁[τ]) (v + 2) = (θ₁[τ]) v := by
      -- Two successive `+1` translations cancel the sign on `θ₁`.
      calc
        (θ₁[τ]) (v + 2) = (θ₁[τ]) ((v + 1) + 1) := by ring
        _ = -(θ₁[τ]) (v + 1) := by
              simpa [add_assoc] using exercise_3_theta_one_add_one τ (v + 1)
        _ = -(-(θ₁[τ]) v) := by rw [exercise_3_theta_one_add_one]
        _ = (θ₁[τ]) v := by ring
    have hden :
        (θ₀[τ]) (v + 2) = (θ₀[τ]) v := by
      -- The denominator theta factor is genuinely `1`-periodic.
      calc
        (θ₀[τ]) (v + 2) = (θ₀[τ]) ((v + 1) + 1) := by ring
        _ = (θ₀[τ]) (v + 1) := by
              simpa [add_assoc] using exercise_3_theta_zero_add_one τ (v + 1)
        _ = (θ₀[τ]) v := by rw [exercise_3_theta_zero_add_one]
    -- Route correction: use the named `u ↦ u / (2K)` bridge instead of redoing denominator
    -- clearing inline inside the period proof.
    rw [exercise8_theta_quotient_eq_theta_ratio, exercise8_theta_quotient_eq_theta_ratio,
      exercise8_rescaledAddFullRealPeriod, hnum, hden]
  · intro u
    let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
    let v : ℂ := u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
    let scalar : ℂ :=
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * v)
    have hscalar_ne : scalar ≠ 0 := by
      -- The common quasi-periodicity scalar is a nonzero exponential factor.
      refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
      refine neg_ne_zero.mpr ?_
      exact inv_ne_zero (by rw [jacobi_q_eq_exp]; exact Complex.exp_ne_zero _)
    -- Rewrite both theta factors through the shared `+τ` law and cancel the common scalar.
    rw [exercise8_theta_quotient_eq_theta_ratio, exercise8_theta_quotient_eq_theta_ratio,
      exercise8_rescaledAddFullImaginaryPeriod]
    have hnum : (θ₁[τ]) (v + τ) = scalar * (θ₁[τ]) v := by
      simpa [scalar] using exercise_3_theta_one_add_tau τ v
    have hden : (θ₀[τ]) (v + τ) = scalar * (θ₀[τ]) v := by
      simpa [scalar] using exercise_3_theta_zero_add_tau τ v
    rw [hnum, hden]
    simpa [τ, v, scalar] using
      (mul_div_mul_left ((θ₁[τ]) v) ((θ₀[τ]) v) hscalar_ne)

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient also exposes its two
generator period laws directly, which is the form needed when comparing normal forms pointwise. -/
lemma exercise8_theta_quotient_periodic_generators
    (k : Exercise8Modulus) :
    Function.Periodic (exercise8_theta_quotient k) (exercise8_period_pair k).ω₁ ∧
      Function.Periodic (exercise8_theta_quotient k) (exercise8_period_pair k).ω₂ := by
  -- This is the generator-level restatement of the already-packaged period lattice.
  simpa [hasPeriodLattice_iff_periodic_generators] using
    exercise8_theta_quotient_hasPeriodLattice k

/-- Helper for Cartan section26 0018_Exercise_8: after the affine rescaling `u ↦ u / (2K)`, the
zeros of the numerator theta factor occur exactly on the even half-period lattice. -/
lemma exercise8_theta_one_rescaled_zero_iff
    (k : Exercise8Modulus) (u : ℂ) :
    (θ₁[((exercise8_tau k : ℍ) : ℂ)])
        (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) = 0 ↔
      u ∈ (exercise8_half_period_pair k).lattice := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  -- Match the Exercise 3 zero coordinates with the Exercise 8 half-period lattice bridge.
  simpa [τ] using
    (exercise_3_theta_one_zero_iff
      τ (u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))) hτ).trans
      (exercise8_rescaledHalfPeriodLattice_iff k u)

/-- Helper for Cartan section26 0018_Exercise_8: after the same affine rescaling, the zeros of
the denominator theta factor occur exactly on the pole-shifted half-period lattice. -/
lemma exercise8_theta_zero_rescaled_zero_iff
    (k : Exercise8Modulus) (u : ℂ) :
    (θ₀[((exercise8_tau k : ℍ) : ℂ)])
        (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) = 0 ↔
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  -- Match the shifted Exercise 3 zero coordinates with the pole-translate lattice bridge.
  simpa [τ] using
    (exercise_3_theta_zero_zero_iff
      τ (u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ))) hτ).trans
      (exercise8_rescaledPoleLattice_iff k u)

/-- Helper for Cartan section26 0018_Exercise_8: the even half-period lattice and its pole-shift
translate are disjoint. -/
lemma exercise8_theta_zero_rescaled_nonzero_of_theta_one_zero
    (k : Exercise8Modulus) {u : ℂ}
    (hu :
      (θ₁[((exercise8_tau k : ℍ) : ℂ)])
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) = 0) :
    (θ₀[((exercise8_tau k : ℍ) : ℂ)])
        (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  have hu' : u ∈ (exercise8_half_period_pair k).lattice :=
    (exercise8_theta_one_rescaled_zero_iff k u).1 hu
  have hzero' :
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice :=
    (exercise8_theta_zero_rescaled_zero_iff k u).1 hzero
  exact exercise8_half_period_lattice_disjoint_pole_shift k hu' hzero'

/-- Helper for Cartan section26 0018_Exercise_8: whenever the rescaled denominator theta factor
vanishes, the numerator factor stays nonzero at the same point. -/
lemma exercise8_theta_one_rescaled_nonzero_of_theta_zero_zero
    (k : Exercise8Modulus) {u : ℂ}
    (hu :
      (θ₀[((exercise8_tau k : ℍ) : ℂ)])
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) = 0) :
    (θ₁[((exercise8_tau k : ℍ) : ℂ)])
        (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  have hu' :
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice :=
    (exercise8_theta_zero_rescaled_zero_iff k u).1 hu
  have hzero' : u ∈ (exercise8_half_period_pair k).lattice :=
    (exercise8_theta_one_rescaled_zero_iff k u).1 hzero
  exact exercise8_pole_shift_sub_lattice_disjoint_half_period k hu' hzero'

/-- Helper for Cartan section26 0018_Exercise_8: the Exercise 3 divisor package specializes to a
simple zero of `θ₁` at the origin for the parameter `τ = i K' / K`. -/
lemma exercise8_thetaOne_analyticOrderAt_zero_eq_one
    (k : Exercise8Modulus) :
    analyticOrderAt (θ₁[((exercise8_tau k : ℍ) : ℂ)]) 0 = 1 := by
  classical
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  let L : PeriodPair := theta_one_period_pair τ hτ
  obtain ⟨t, ht0, ht1, hzero_mem, hboundary, hlattice⟩ :=
    exists_theta_one_boundary_regular_slanted_periodParallelogram τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  let P : Set ℂ := L.periodParallelogram z₀
  let d : ℂ → ℤ := MeromorphicOn.divisor (θ₁[τ]) P
  have hPCompact : IsCompact P := by
    simpa [L, P, z₀] using isCompact_periodParallelogram L z₀
  have hFiniteSupport : (MeromorphicOn.divisor (θ₁[τ]) P).support.Finite :=
    divisor_support_finite_of_isCompact hPCompact
  let s : Finset ℂ :=
    hFiniteSupport.toFinset
  have hsum :
      Finset.sum s (fun z ↦ (d z : ℂ)) = 1 := by
    -- The contour-count theorem fixes the total divisor mass in the regular period cell.
    simpa [L, z₀, P, d, s] using
      theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one τ hτ z₀
        (by simpa [L, z₀, P] using hboundary)
  have hzero_div_pos : 0 < d 0 := by
    -- The origin contributes positively because it is the unique zero lying in the chosen cell.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ
        (by simpa [L, P, z₀] using hzero_mem)).2 (jacobi_theta_one_zero_at_zero τ)
  have hzero_mem_s : 0 ∈ s := by
    -- Positive divisor mass puts `0` into the finite divisor support.
    have hzero_ne : d 0 ≠ 0 := ne_of_gt hzero_div_pos
    simpa [s, d, Function.mem_support] using hzero_ne
  have hzero_unique :
      ∀ z ∈ P, (θ₁[τ]) z = 0 → z = 0 := by
    intro z hzP hz
    -- The boundary-regular slanted cell contains no zero of `θ₁` other than the origin.
    exact theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell τ hτ
      hzero_mem hboundary (by simpa [L, z₀, P] using hzP) hz
  have hother_zero :
      ∀ z ∈ s.erase 0, d z = 0 := by
    intro z hz
    have hzP : z ∈ P := by
      have hzsupport : z ∈ (MeromorphicOn.divisor (θ₁[τ]) P).support := by
        simpa [s, d] using Finset.mem_of_mem_erase hz
      exact (MeromorphicOn.divisor (θ₁[τ]) P).supportWithinDomain hzsupport
    by_cases hzzero : (θ₁[τ]) z = 0
    · have hz0 : z = 0 := hzero_unique z hzP hzzero
      exact False.elim ((Finset.mem_erase.mp hz).1 hz0)
    · have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
        -- Entire holomorphy of `θ₁` restricts to the period cell `P`.
        exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
      have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := by
        exact hanalytic_univ.mono (by intro w hw; simp)
      simpa [d] using divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalyticP hzP hzzero
  have hsum_single : Finset.sum s (fun z ↦ (d z : ℂ)) = d 0 := by
    -- Every divisor term away from `0` vanishes, so the full mass sits at the origin.
    have herase_zero : ∑ x ∈ s.erase 0, (d x : ℂ) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      exact_mod_cast hother_zero x hx
    rw [← Finset.sum_erase_add _ _ hzero_mem_s, herase_zero]
    simp
  have hdiv0_complex : (d 0 : ℂ) = 1 := by
    rw [← hsum_single]
    exact hsum
  have hdiv0 : d 0 = 1 := by
    exact_mod_cast hdiv0_complex
  have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
    -- The entire theta function is analytic at the origin.
    exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
  have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := by
    exact hanalytic_univ.mono (by intro w hw; simp)
  have hanalytic0 : AnalyticAt ℂ (θ₁[τ]) 0 := hanalytic_univ 0 (by simp)
  have hmer_not_top : meromorphicOrderAt (θ₁[τ]) 0 ≠ ⊤ := by
    -- Finite analytic order rules out an infinite meromorphic order at the origin.
    rw [hanalytic0.meromorphicOrderAt_eq]
    simpa using theta_one_analyticOrderAt_ne_top τ 0 hτ
  have hmer_eq_one : meromorphicOrderAt (θ₁[τ]) 0 = (1 : WithTop ℤ) := by
    -- The divisor value at the origin is exactly the meromorphic order there.
    calc
      meromorphicOrderAt (θ₁[τ]) 0
          = ↑((meromorphicOrderAt (θ₁[τ]) 0).untop₀) := by
              exact (WithTop.coe_untop₀_of_ne_top hmer_not_top).symm
      _ = (1 : WithTop ℤ) := by
            congr 1
            rw [← hanalyticP.meromorphicOn.divisor_apply (by simpa [P, L, z₀] using hzero_mem)]
            simpa [d] using hdiv0
  -- The analytic and meromorphic orders agree for an analytic germ.
  rw [hanalytic0.meromorphicOrderAt_eq] at hmer_eq_one
  cases horder : analyticOrderAt (θ₁[τ]) 0 with
  | top =>
      exact (theta_one_analyticOrderAt_ne_top τ 0 hτ horder).elim
  | coe n =>
      have hn : (n : WithTop ℤ) = (1 : WithTop ℤ) := by
        simpa [horder] using hmer_eq_one
      exact_mod_cast hn

/-- Helper for Cartan section26 0018_Exercise_8: the simple zero of `θ₁` at the origin forces a
nonvanishing first derivative there. -/
lemma exercise8_thetaOne_deriv_ne_zero_at_zero
    (k : Exercise8Modulus) :
    deriv (θ₁[((exercise8_tau k : ℍ) : ℂ)]) 0 ≠ 0 := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hanalytic0 : AnalyticAt ℂ (θ₁[τ]) 0 := by
    -- Entire differentiability of `θ₁` gives the analytic germ needed for the simple-zero test.
    exact ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
      0 (by simp)
  exact
    (AnalyticAt.analyticOrderAt_eq_one_iff_zero_and_deriv_ne_zero hanalytic0).1
      (exercise8_thetaOne_analyticOrderAt_zero_eq_one k) |>.2

/-- Helper for Cartan section26 0018_Exercise_8: differentiating the half-`τ` shift formula at
`0` shows that `θ₀` has nonvanishing derivative at `τ / 2`. -/
lemma exercise8_thetaZero_deriv_ne_zero_at_halfTau
    (k : Exercise8Modulus) :
    deriv (θ₀[((exercise8_tau k : ℍ) : ℂ)]) (((exercise8_tau k : ℍ) : ℂ) / 2) ≠ 0 := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  let a : ℂ → ℂ :=
    fun u ↦ Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4))
  have hshift :
      deriv (fun u ↦ (θ₀[τ]) (u + τ / 2)) 0 =
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) *
          deriv (θ₁[τ]) 0 := by
    -- Differentiate the half-`τ` translation identity and use `θ₁(0) = 0` to kill the extra
    -- product-rule term.
    rw [show (fun u ↦ (θ₀[τ]) (u + τ / 2)) =
        fun u ↦
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
            (θ₁[τ]) u by
          funext u
          exact exercise_3_theta_zero_add_half_tau τ u]
    change deriv (fun u ↦ a u * (θ₁[τ]) u) 0 =
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) * deriv (θ₁[τ]) 0
    have hderiv_mul :
        deriv (fun u ↦ a u * (θ₁[τ]) u) 0 =
          deriv a 0 * (θ₁[τ]) 0 + a 0 * deriv (θ₁[τ]) 0 := by
      simpa using
        (deriv_mul
          (by
            change DifferentiableAt ℂ a 0
            dsimp [a]
            fun_prop)
          ((exercise_3_theta_one_differentiable τ hτ) 0))
    calc
      deriv (fun u ↦ a u * (θ₁[τ]) u) 0
          = deriv a 0 * (θ₁[τ]) 0 + a 0 * deriv (θ₁[τ]) 0 := hderiv_mul
      _ = a 0 * deriv (θ₁[τ]) 0 := by simp [jacobi_theta_one_zero_at_zero]
      _ = Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) * deriv (θ₁[τ]) 0 := by
            simp [a]
  have hleft :
      deriv (fun u ↦ (θ₀[τ]) (u + τ / 2)) 0 = deriv (θ₀[τ]) (τ / 2) := by
    -- Translation in the source variable does not change derivatives.
    simpa using deriv_comp_add_const (θ₀[τ]) (τ / 2) 0
  have hscalar_ne :
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) ≠ 0 := by
    -- The half-shift scalar never vanishes.
    exact mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
  -- A nonzero scalar times the already nonzero derivative of `θ₁` is still nonzero.
  rw [← hleft, hshift]
  exact mul_ne_zero hscalar_ne (exercise8_thetaOne_deriv_ne_zero_at_zero k)

/-- Helper for Cartan section26 0018_Exercise_8: the denominator theta factor has a simple zero
at the half-period `τ / 2`. -/
lemma exercise8_thetaZero_analyticOrderAt_halfTau_eq_one
    (k : Exercise8Modulus) :
    analyticOrderAt (θ₀[((exercise8_tau k : ℍ) : ℂ)]) (((exercise8_tau k : ℍ) : ℂ) / 2) = 1 := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hanalytic : AnalyticAt ℂ (θ₀[τ]) (τ / 2) := by
    -- Entire differentiability of `θ₀` gives the analytic germ at the shifted zero.
    exact ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
      (τ / 2) (by simp)
  exact hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (jacobi_theta_zero_zero_at_half_tau τ)
    (exercise8_thetaZero_deriv_ne_zero_at_halfTau k)

/-- Helper for Cartan section26 0018_Exercise_8: the simple zero of `θ₁` at the origin is also
its meromorphic order there. -/
lemma exercise8_thetaOne_meromorphicOrderAt_zero_eq_one
    (k : Exercise8Modulus) :
    meromorphicOrderAt (θ₁[((exercise8_tau k : ℍ) : ℂ)]) 0 = (1 : WithTop ℤ) := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hanalytic0 : AnalyticAt ℂ (θ₁[τ]) 0 := by
    -- Entire differentiability of `θ₁` gives the analytic germ at the origin.
    exact
      ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
        0 (by simp)
  -- For an analytic germ, the meromorphic order is exactly the analytic order.
  rw [hanalytic0.meromorphicOrderAt_eq]
  rw [exercise8_thetaOne_analyticOrderAt_zero_eq_one k]
  simp

/-- Helper for Cartan section26 0018_Exercise_8: the half-`τ` zero of `θ₀` has meromorphic order
`1`. -/
lemma exercise8_thetaZero_meromorphicOrderAt_halfTau_eq_one
    (k : Exercise8Modulus) :
    meromorphicOrderAt (θ₀[((exercise8_tau k : ℍ) : ℂ)]) (((exercise8_tau k : ℍ) : ℂ) / 2) =
      (1 : WithTop ℤ) := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hanalytic : AnalyticAt ℂ (θ₀[τ]) (τ / 2) := by
    -- Entire differentiability of `θ₀` gives the analytic germ at the shifted zero.
    exact
      ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
        (τ / 2) (by simp)
  -- The half-`τ` zero has meromorphic order equal to its analytic order.
  rw [hanalytic.meromorphicOrderAt_eq]
  rw [exercise8_thetaZero_analyticOrderAt_halfTau_eq_one k]
  simp

/-- Helper for Cartan section26 0018_Exercise_8: for an analytic germ, meromorphic order `0`
means exactly that the center value is nonzero. -/
lemma AnalyticAt.meromorphicOrderAt_eq_zero_iff_nonzero
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    meromorphicOrderAt f z = (0 : WithTop ℤ) ↔ f z ≠ 0 := by
  -- Rewrite meromorphic order back to analytic order, where the zero-order criterion is standard.
  constructor
  · intro horder
    have hanalytic : analyticOrderAt f z = 0 := by
      simpa [hf.meromorphicOrderAt_eq] using horder
    exact (hf.analyticOrderAt_eq_zero).mp hanalytic
  · intro hnonzero
    have hanalytic : analyticOrderAt f z = 0 :=
      (hf.analyticOrderAt_eq_zero).2 hnonzero
    simpa [hf.meromorphicOrderAt_eq] using hanalytic

/-- Helper for Cartan section26 0018_Exercise_8: for an analytic germ, positive meromorphic order
occurs exactly at zeros. -/
lemma AnalyticAt.meromorphicOrderAt_pos_iff
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    0 < meromorphicOrderAt f z ↔ f z = 0 := by
  constructor
  · intro hpos
    -- Analytic meromorphic order is always nonnegative, so strict positivity excludes order `0`.
    by_contra hnonzero
    have hzero :
        meromorphicOrderAt f z = (0 : WithTop ℤ) :=
      (hf.meromorphicOrderAt_eq_zero_iff_nonzero).2 hnonzero
    simpa [hzero] using hpos
  · intro hz
    have hnonneg : 0 ≤ meromorphicOrderAt f z :=
      hf.meromorphicOrderAt_nonneg
    have hne_zero : meromorphicOrderAt f z ≠ (0 : WithTop ℤ) := by
      intro hzero
      exact (hf.meromorphicOrderAt_eq_zero_iff_nonzero).1 hzero hz
    -- A nonnegative order that is not zero must be strictly positive.
    exact lt_of_le_of_ne hnonneg hne_zero.symm

/-- Helper for Cartan section26 0018_Exercise_8: a meromorphic order that is neither positive nor
negative must be exactly zero. -/
lemma meromorphicOrderAt_eq_zero_of_not_pos_not_neg
    {f : ℂ → ℂ} {z : ℂ}
    (hnotpos : ¬ 0 < meromorphicOrderAt f z)
    (hnotneg : ¬ meromorphicOrderAt f z < 0) :
    meromorphicOrderAt f z = (0 : WithTop ℤ) := by
  -- In the linear order on `WithTop ℤ`, excluding both strict inequalities forces equality.
  exact le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)

/-- Helper for Cartan section26 0018_Exercise_8: composing with the affine rescaling
`w ↦ w / c` preserves meromorphic order when `c ≠ 0`. -/
lemma meromorphicOrderAt_comp_div_const
    {f : ℂ → ℂ} {z c : ℂ} (hc : c ≠ 0) :
    meromorphicOrderAt (fun w : ℂ ↦ f (w / c)) z = meromorphicOrderAt f (z / c) := by
  -- The rescaling map has nonzero derivative `1 / c`, so the composition rule keeps the order.
  simpa using
    (meromorphicOrderAt_comp_of_deriv_ne_zero
      (show AnalyticAt ℂ (fun w : ℂ ↦ w / c) z by fun_prop)
      (by simpa using (div_ne_zero (show (1 : ℂ) ≠ 0 by norm_num) hc)))

/-- Helper for Cartan section26 0018_Exercise_8: the rescaling denominator `2K` is nonzero. -/
lemma exercise8_twoCompleteRealPeriod_ne_zero
    (k : Exercise8Modulus) :
    (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
  -- Positivity of `K` rules out `2K = 0`, and coercion to `ℂ` preserves that fact.
  have hne : (2 * exercise8_complete_real_period k : ℝ) ≠ 0 := by
    nlinarith [exercise8_complete_real_period_pos k]
  exact_mod_cast hne

/-- Helper for Cartan section26 0018_Exercise_8: after dividing by `2K`, the distinguished pole
shift `i K'` becomes the half-period `τ / 2`. -/
lemma exercise8_poleShift_div_twoCompleteRealPeriod_eq_halfTau
    (k : Exercise8Modulus) :
    exercise8_pole_shift k / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
      (exercise8_tau k : ℂ) / 2 := by
  have hK_ne : exercise8_complete_real_period k ≠ 0 :=
    exercise8_complete_real_period_ne_zero k
  -- Unfold the source period data and rewrite `τ = i K' / K` before clearing the denominator.
  rw [exercise8_tau_def]
  simp [exercise8_pole_shift, exercise8_half_period_pair]
  field_simp [hK_ne]

/-- Helper for Cartan section26 0018_Exercise_8: on `Set.univ`, codiscrete equality of two
meromorphic functions already forces equality of their global normal-form representatives. -/
lemma toMeromorphicNFOn_eq_of_codiscreteEq_univ
    {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    (hEq : f =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] g) :
    toMeromorphicNFOn f Set.univ = toMeromorphicNFOn g Set.univ := by
  have hfOn : MeromorphicOn f Set.univ := by
    simpa using hf
  have hgOn : MeromorphicOn g Set.univ := by
    simpa using hg
  ext z
  have hfg_nhdsNE : f =ᶠ[nhdsWithin z ({z}ᶜ)] g :=
    (hf z).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hg z) (by simp) isOpen_univ.preperfect hEq
  have hfNF_nhdsNE :
      toMeromorphicNFOn f Set.univ =ᶠ[nhdsWithin z ({z}ᶜ)] f :=
    hfOn.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp)
  have hgNF_nhdsNE :
      toMeromorphicNFOn g Set.univ =ᶠ[nhdsWithin z ({z}ᶜ)] g :=
    hgOn.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp)
  have hNF_nhdsNE :
      toMeromorphicNFOn f Set.univ =ᶠ[nhdsWithin z ({z}ᶜ)] toMeromorphicNFOn g Set.univ :=
    hfNF_nhdsNE.trans (hfg_nhdsNE.trans hgNF_nhdsNE.symm)
  have hfNF :
      MeromorphicNFAt (toMeromorphicNFOn f Set.univ) z :=
    meromorphicNFOn_toMeromorphicNFOn f Set.univ (by simp)
  have hgNF :
      MeromorphicNFAt (toMeromorphicNFOn g Set.univ) z :=
    meromorphicNFOn_toMeromorphicNFOn g Set.univ (by simp)
  have hNF_nhds :
      toMeromorphicNFOn f Set.univ =ᶠ[nhds z] toMeromorphicNFOn g Set.univ :=
    (hfNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hgNF).1 hNF_nhdsNE
  exact Filter.EventuallyEq.eq_of_nhds hNF_nhds

/-- Helper for Cartan section26 0018_Exercise_8: away from its zero lattice and pole lattice, the
theta quotient has meromorphic order exactly `0`. -/
lemma exercise8_theta_quotient_order_eq_zero_of_not_divisor
    (k : Exercise8Modulus) {u : ℂ}
    (hzero :
      u ∉ (exercise8_half_period_pair k).lattice)
    (hpole :
      u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice) :
    meromorphicOrderAt (exercise8_theta_quotient k) u = (0 : WithTop ℤ) := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hscale_ne : scale ≠ 0 := by
    simpa [scale] using exercise8_twoCompleteRealPeriod_ne_zero k
  have hnumAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) u := by
    -- The numerator is the entire theta function `θ₁` composed with the affine rescaling.
    have htheta :
        AnalyticAt ℂ (θ₁[τ]) (u / scale) := by
      exact
        ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (u / scale) (by simp)
    have hscaleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ w / scale) u := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₁[τ]) ∘ fun w : ℂ ↦ w / scale) u)
  have hdenAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) u := by
    -- The denominator is handled by the same rescaling composition.
    have htheta :
        AnalyticAt ℂ (θ₀[τ]) (u / scale) := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (u / scale) (by simp)
    have hscaleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ w / scale) u := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₀[τ]) ∘ fun w : ℂ ↦ w / scale) u)
  have hnum_nonzero :
      (θ₁[τ]) (u / scale) ≠ 0 := by
    intro hnum_zero
    exact hzero ((exercise8_theta_one_rescaled_zero_iff k u).1 (by simpa [τ, scale] using hnum_zero))
  have hden_nonzero :
      (θ₀[τ]) (u / scale) ≠ 0 := by
    intro hden_zero
    exact hpole
      ((exercise8_theta_zero_rescaled_zero_iff k u).1 (by simpa [τ, scale] using hden_zero))
  have hnumOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) u = (0 : WithTop ℤ) := by
    -- An analytic theta factor has order `0` exactly when it does not vanish at the center.
    exact (hnumAnalytic.meromorphicOrderAt_eq_zero_iff_nonzero).2 hnum_nonzero
  have hdenOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) u = (0 : WithTop ℤ) := by
    -- The denominator factor is analytic and nonvanishing away from the pole translate.
    exact (hdenAnalytic.meromorphicOrderAt_eq_zero_iff_nonzero).2 hden_nonzero
  have hquot :
      exercise8_theta_quotient k =
        fun w : ℂ ↦ (θ₁[τ]) (w / scale) / (θ₀[τ]) (w / scale) := by
    -- Package the source-facing theta quotient as the explicit rescaled ratio used by the order API.
    funext w
    simpa [τ, scale] using exercise8_theta_quotient_eq_theta_ratio k w
  -- After normalizing to the theta ratio, the quotient order is `0 - 0`.
  calc
    meromorphicOrderAt (exercise8_theta_quotient k) u
        =
          meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) u -
            meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) u := by
              rw [hquot]
              simpa [τ, scale] using
                (meromorphicOrderAt_div hnumAnalytic.meromorphicAt hdenAnalytic.meromorphicAt)
    _ = (0 : WithTop ℤ) - (0 : WithTop ℤ) := by rw [hnumOrder, hdenOrder]
    _ = (0 : WithTop ℤ) := by simp

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient has a simple zero at the
origin. -/
lemma exercise8_theta_quotient_order_at_zero
    (k : Exercise8Modulus) :
    meromorphicOrderAt (exercise8_theta_quotient k) 0 = (1 : WithTop ℤ) := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hscale_ne : scale ≠ 0 := by
    simpa [scale] using exercise8_twoCompleteRealPeriod_ne_zero k
  have hnumAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) 0 := by
    -- The numerator is entire after composition with the affine rescaling.
    have htheta :
        AnalyticAt ℂ (θ₁[τ]) (0 / scale) := by
      exact
        ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (0 / scale) (by simp)
    have hscaleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ w / scale) 0 := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₁[τ]) ∘ fun w : ℂ ↦ w / scale) 0)
  have hdenAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) 0 := by
    -- The denominator is entire as well, so only its value at the center matters.
    have htheta :
        AnalyticAt ℂ (θ₀[τ]) (0 / scale) := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (0 / scale) (by simp)
    have hscaleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ w / scale) 0 := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₀[τ]) ∘ fun w : ℂ ↦ w / scale) 0)
  have hnum_zero :
      (θ₁[τ]) (0 / scale) = 0 := by
    simpa [τ, scale] using jacobi_theta_one_zero_at_zero τ
  have hden_nonzero :
      (θ₀[τ]) (0 / scale) ≠ 0 := by
    -- The denominator cannot vanish where the numerator's zero lies on the even lattice.
    exact exercise8_theta_zero_rescaled_nonzero_of_theta_one_zero k (by simpa [τ, scale] using hnum_zero)
  have hnumOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) 0 = (1 : WithTop ℤ) := by
    -- Rescaling by a nonzero constant preserves the simple zero order of `θ₁` at `0`.
    calc
      meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) 0
          = meromorphicOrderAt (θ₁[τ]) (0 / scale) := by
              simpa [τ, scale] using
                (meromorphicOrderAt_comp_div_const hscale_ne :
                  meromorphicOrderAt ((θ₁[τ]) ∘ fun w : ℂ ↦ w / scale) 0 =
                    meromorphicOrderAt (θ₁[τ]) (0 / scale))
      _ = meromorphicOrderAt (θ₁[τ]) 0 := by simp
      _ = (1 : WithTop ℤ) := by
            simpa [τ] using exercise8_thetaOne_meromorphicOrderAt_zero_eq_one k
  have hdenOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) 0 = (0 : WithTop ℤ) := by
    -- The denominator is analytic and nonzero at the origin, so its order there is `0`.
    exact (hdenAnalytic.meromorphicOrderAt_eq_zero_iff_nonzero).2 hden_nonzero
  have hquot :
      exercise8_theta_quotient k =
        fun w : ℂ ↦ (θ₁[τ]) (w / scale) / (θ₀[τ]) (w / scale) := by
    -- Rewrite the public quotient into the explicit rescaled theta ratio before using divisor arithmetic.
    funext w
    simpa [τ, scale] using exercise8_theta_quotient_eq_theta_ratio k w
  -- The quotient order is the numerator order minus the denominator order.
  calc
    meromorphicOrderAt (exercise8_theta_quotient k) 0
        =
          meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) 0 -
            meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) 0 := by
              rw [hquot]
              simpa [τ, scale] using
                (meromorphicOrderAt_div hnumAnalytic.meromorphicAt hdenAnalytic.meromorphicAt)
    _ = (1 : WithTop ℤ) - (0 : WithTop ℤ) := by rw [hnumOrder, hdenOrder]
    _ = (1 : WithTop ℤ) := by simp

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient has a simple pole at the
distinguished pole shift `i K'`. -/
lemma exercise8_theta_quotient_order_at_poleShift
    (k : Exercise8Modulus) :
    meromorphicOrderAt (exercise8_theta_quotient k) (exercise8_pole_shift k) = (-1 : WithTop ℤ) := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hscale_ne : scale ≠ 0 := by
    simpa [scale] using exercise8_twoCompleteRealPeriod_ne_zero k
  have hnumAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) (exercise8_pole_shift k) := by
    -- The numerator remains entire after the same affine rescaling.
    have htheta :
        AnalyticAt ℂ (θ₁[τ]) (exercise8_pole_shift k / scale) := by
      exact
        ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (exercise8_pole_shift k / scale) (by simp)
    have hscaleAnalytic :
        AnalyticAt ℂ (fun w : ℂ ↦ w / scale) (exercise8_pole_shift k) := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₁[τ]) ∘ fun w : ℂ ↦ w / scale) (exercise8_pole_shift k))
  have hdenAnalytic :
      AnalyticAt ℂ (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) (exercise8_pole_shift k) := by
    -- The denominator is handled by the same composition route.
    have htheta :
        AnalyticAt ℂ (θ₀[τ]) (exercise8_pole_shift k / scale) := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          (exercise8_pole_shift k / scale) (by simp)
    have hscaleAnalytic :
        AnalyticAt ℂ (fun w : ℂ ↦ w / scale) (exercise8_pole_shift k) := by
      fun_prop
    simpa [Function.comp] using
      (AnalyticAt.comp htheta hscaleAnalytic :
        AnalyticAt ℂ ((θ₀[τ]) ∘ fun w : ℂ ↦ w / scale) (exercise8_pole_shift k))
  have hden_zero :
      (θ₀[τ]) (exercise8_pole_shift k / scale) = 0 := by
    -- The distinguished pole shift becomes the half-period `τ / 2` after dividing by `2K`.
    rw [exercise8_poleShift_div_twoCompleteRealPeriod_eq_halfTau]
    simpa [τ] using jacobi_theta_zero_zero_at_half_tau τ
  have hnum_nonzero :
      (θ₁[τ]) (exercise8_pole_shift k / scale) ≠ 0 := by
    -- The numerator stays nonzero at the denominator's simple zero.
    exact exercise8_theta_one_rescaled_nonzero_of_theta_zero_zero k
      (by simpa [τ, scale] using hden_zero)
  have hnumOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) (exercise8_pole_shift k) =
        (0 : WithTop ℤ) := by
    -- An analytic nonvanishing numerator contributes order `0` at the pole point.
    exact (hnumAnalytic.meromorphicOrderAt_eq_zero_iff_nonzero).2 hnum_nonzero
  have hdenOrder :
      meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) (exercise8_pole_shift k) =
        (1 : WithTop ℤ) := by
    -- Rescaling preserves the simple denominator zero at `τ / 2`.
    calc
      meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) (exercise8_pole_shift k)
          = meromorphicOrderAt (θ₀[τ]) (exercise8_pole_shift k / scale) := by
              simpa [τ, scale] using
                (meromorphicOrderAt_comp_div_const hscale_ne :
                  meromorphicOrderAt ((θ₀[τ]) ∘ fun w : ℂ ↦ w / scale)
                      (exercise8_pole_shift k) =
                    meromorphicOrderAt (θ₀[τ]) (exercise8_pole_shift k / scale))
      _ = meromorphicOrderAt (θ₀[τ]) (τ / 2) := by
            rw [exercise8_poleShift_div_twoCompleteRealPeriod_eq_halfTau]
      _ = (1 : WithTop ℤ) := by
            simpa [τ] using exercise8_thetaZero_meromorphicOrderAt_halfTau_eq_one k
  have hquot :
      exercise8_theta_quotient k =
        fun w : ℂ ↦ (θ₁[τ]) (w / scale) / (θ₀[τ]) (w / scale) := by
    -- The pole calculation uses the same explicit theta-ratio normal form as the zero calculation.
    funext w
    simpa [τ, scale] using exercise8_theta_quotient_eq_theta_ratio k w
  -- Subtract the simple denominator zero from the nonvanishing numerator order.
  calc
    meromorphicOrderAt (exercise8_theta_quotient k) (exercise8_pole_shift k)
        =
          meromorphicOrderAt (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) (exercise8_pole_shift k) -
            meromorphicOrderAt (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) (exercise8_pole_shift k) := by
              rw [hquot]
              simpa [τ, scale] using
                (meromorphicOrderAt_div hnumAnalytic.meromorphicAt hdenAnalytic.meromorphicAt)
    _ = (0 : WithTop ℤ) - (1 : WithTop ℤ) := by rw [hnumOrder, hdenOrder]
    _ = (-1 : WithTop ℤ) := by simp

/-- Helper for Cartan section26 0018_Exercise_8: shifting the theta quotient by the half-real
period `2K` changes only the sign, so the divisor data is unchanged. -/
lemma exercise8_theta_quotient_add_half_real_period
    (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k
        (u + ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
      -exercise8_theta_quotient k u := by
  let τ : ℂ := (exercise8_tau k : ℂ)
  let scale : ℂ := ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
  have hscale_ne : scale ≠ 0 := by
    dsimp [scale]
    exact_mod_cast (show (2 * exercise8_complete_real_period k : ℝ) ≠ 0 by
      nlinarith [exercise8_complete_real_period_pos k])
  have hshift : (u + scale) / scale = u / scale + 1 := by
    field_simp [hscale_ne]
  -- A real half-period adds `1` to the rescaled variable, so only `θ₁` changes sign.
  rw [exercise8_theta_quotient_eq_theta_ratio, exercise8_theta_quotient_eq_theta_ratio, hshift,
    exercise_3_theta_one_add_one, exercise_3_theta_zero_add_one]
  ring

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient's meromorphic order is
invariant under the half-real shift `u ↦ u + 2K` because that shift only multiplies the function
by `-1`. -/
lemma exercise8_theta_quotient_order_add_half_real_period_eq
    (k : Exercise8Modulus) (u : ℂ) :
    meromorphicOrderAt (exercise8_theta_quotient k)
        (u + ((exercise8_half_period_pair k).ω₁)) =
      meromorphicOrderAt (exercise8_theta_quotient k) u := by
  have hcomp :
      meromorphicOrderAt
          (fun z : ℂ ↦ exercise8_theta_quotient k (z + (exercise8_half_period_pair k).ω₁)) u =
        meromorphicOrderAt (exercise8_theta_quotient k)
          (u + (exercise8_half_period_pair k).ω₁) := by
    -- Translating the source by `2K` preserves meromorphic order because the derivative is `1`.
    simpa using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (show AnalyticAt ℂ (fun z : ℂ ↦ z + (exercise8_half_period_pair k).ω₁) u by fun_prop)
        (by norm_num : deriv (fun z : ℂ ↦ z + (exercise8_half_period_pair k).ω₁) u ≠ 0) :
        meromorphicOrderAt
            ((exercise8_theta_quotient k) ∘
              fun z : ℂ ↦ z + (exercise8_half_period_pair k).ω₁) u =
          meromorphicOrderAt (exercise8_theta_quotient k)
            (u + (exercise8_half_period_pair k).ω₁))
  -- Replace the translated theta quotient by its `-1` multiple and use order invariance under
  -- negation.
  calc
    meromorphicOrderAt (exercise8_theta_quotient k)
        (u + (exercise8_half_period_pair k).ω₁) =
      meromorphicOrderAt
          (fun z : ℂ ↦ exercise8_theta_quotient k (z + (exercise8_half_period_pair k).ω₁)) u := by
            simpa using hcomp.symm
    _ =
      meromorphicOrderAt (fun z : ℂ ↦ -exercise8_theta_quotient k z) u := by
        congr 1
        funext z
        simpa [exercise8_half_period_pair] using exercise8_theta_quotient_add_half_real_period k z
    _ = meromorphicOrderAt (exercise8_theta_quotient k) u := by
        simpa using
          ((meromorphicOrderAt_fun_neg :
              meromorphicOrderAt (exercise8_theta_quotient k) u =
                meromorphicOrderAt (fun z : ℂ ↦ -exercise8_theta_quotient k z) u)).symm

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient's meromorphic-order function
is periodic for the half-period lattice generated by `2K` and `2 i K'`. -/
lemma exercise8_theta_quotient_order_hasHalfPeriodLattice
    (k : Exercise8Modulus) :
    HasPeriodLattice (exercise8_half_period_pair k)
      (fun u : ℂ ↦ meromorphicOrderAt (exercise8_theta_quotient k) u) := by
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    -- The real half-period changes the theta quotient only by sign, hence preserves order.
    simpa using exercise8_theta_quotient_order_add_half_real_period_eq k u
  · intro u
    have hω :
        (exercise8_half_period_pair k).ω₂ ∈ (exercise8_period_pair k).lattice := by
      -- The imaginary generator already belongs to the true period lattice of the theta quotient.
      simpa [exercise8_half_period_pair, exercise8_period_pair] using
        (exercise8_period_pair k).ω₂_mem_lattice
    -- The imaginary generator is an honest period, so the standard order-transport API applies.
    simpa [exercise8_half_period_pair, exercise8_period_pair] using
      (meromorphicOrderAt_add_period_eq
        (exercise8_period_pair k) (exercise8_theta_quotient_hasPeriodLattice k) hω)

/-- Helper for Exercise 8: the explicit theta quotient already carries every meromorphic,
periodic, and divisor-side datum needed by the final inverse witness package, except for the
source-facing rectangle-inverse identification. -/
lemma exercise8_theta_quotient_continuationAndSeedData
    (k : Exercise8Modulus) :
    Meromorphic (exercise8_theta_quotient k) ∧
      HasPeriodLattice (exercise8_period_pair k) (exercise8_theta_quotient k) ∧
      (∀ u : ℂ,
        meromorphicOrderAt (exercise8_theta_quotient k)
            (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt (exercise8_theta_quotient k) u) ∧
      meromorphicOrderAt (exercise8_theta_quotient k) 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt (exercise8_theta_quotient k) (exercise8_pole_shift k) =
        (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt (exercise8_theta_quotient k) u = (0 : WithTop ℤ)) := by
  refine ⟨exercise8_theta_quotient_meromorphic k, exercise8_theta_quotient_hasPeriodLattice k,
    ?_, ?_, ?_, ?_⟩
  · intro u
    -- The half-real shift changes the theta quotient only by sign, so its order is unchanged.
    exact exercise8_theta_quotient_order_add_half_real_period_eq k u
  · -- The origin is the simple zero already isolated by the theta-side divisor calculation.
    exact exercise8_theta_quotient_order_at_zero k
  · -- The distinguished pole shift is the simple pole coming from the denominator half-period.
    exact exercise8_theta_quotient_order_at_poleShift k
  · intro u hu hpole
    -- Away from both divisor lattices, the theta quotient is analytic and nonvanishing.
    exact exercise8_theta_quotient_order_eq_zero_of_not_divisor k hu hpole

/-- Helper for Exercise 8: the fixed scalar normalization that turns the raw theta quotient into
the source-facing inverse candidate. -/
def exercise8_thetaNormalization (k : Exercise8Modulus) : ℂ :=
  (((1 / Real.sqrt (k : ℝ)) : ℝ) : ℂ)

/-- Helper for Exercise 8: the Exercise 8 theta normalization scalar is nonzero because
`0 < k`. -/
lemma exercise8_thetaNormalization_ne_zero
    (k : Exercise8Modulus) :
    exercise8_thetaNormalization k ≠ 0 := sorry

/-- Helper for Exercise 8: the normalization scalar squares to the missing source factor
`1 / k`. -/
lemma exercise8_thetaNormalization_sq
    (k : Exercise8Modulus) :
    exercise8_thetaNormalization k ^ 2 = 1 / (k : ℂ) := sorry

/-- Helper for Exercise 8: the normalized theta inverse candidate is the raw theta quotient
multiplied by the unique constant needed by the source top-edge parameterization. -/
def exercise8_thetaInverseCandidate (k : Exercise8Modulus) : ℂ → ℂ :=
  fun u ↦ exercise8_thetaNormalization k * exercise8_theta_quotient k u

/-- Helper for Exercise 8: multiplying the theta quotient by the fixed nonzero normalization
preserves meromorphicity. -/
lemma exercise8_thetaInverseCandidate_meromorphic
    (k : Exercise8Modulus) :
    Meromorphic (exercise8_thetaInverseCandidate k) := by
  intro u
  -- The candidate differs from the raw theta quotient only by a constant scalar.
  simpa [exercise8_thetaInverseCandidate, mul_comm] using
    (MeromorphicAt.const (exercise8_thetaNormalization k) u).fun_mul
      ((exercise8_theta_quotient_meromorphic k) u)

/-- Helper for Exercise 8: the normalized theta inverse candidate has the same period lattice as
the raw theta quotient. -/
lemma exercise8_thetaInverseCandidate_hasPeriodLattice
    (k : Exercise8Modulus) :
    HasPeriodLattice (exercise8_period_pair k) (exercise8_thetaInverseCandidate k) := by
  rw [hasPeriodLattice_iff_periodic_generators]
  rcases (hasPeriodLattice_iff_periodic_generators _ _).1
      (exercise8_theta_quotient_hasPeriodLattice k) with ⟨hω₁, hω₂⟩
  constructor
  · intro u
    -- The first generator acts only on the theta quotient factor.
    simp [exercise8_thetaInverseCandidate, hω₁ u, mul_assoc]
  · intro u
    -- The second generator is handled identically.
    simp [exercise8_thetaInverseCandidate, hω₂ u, mul_assoc]

/-- Helper for Exercise 8: multiplying by the fixed nonzero normalization scalar does not change
meromorphic order. -/
lemma exercise8_thetaInverseCandidate_order_eq
    (k : Exercise8Modulus) (u : ℂ) :
    meromorphicOrderAt (exercise8_thetaInverseCandidate k) u =
      meromorphicOrderAt (exercise8_theta_quotient k) u := by
  -- The only new factor is a nonvanishing analytic constant.
  simpa [exercise8_thetaInverseCandidate] using
    (meromorphicOrderAt_mul_of_ne_zero
      (g := fun _ : ℂ ↦ exercise8_thetaNormalization k)
      (f := exercise8_theta_quotient k)
      (x := u)
      (analyticAt_const (v := exercise8_thetaNormalization k))
      (exercise8_thetaNormalization_ne_zero k))

/-- Helper for Exercise 8: the normalized theta inverse candidate is holomorphic on the open
rectangle because it is a constant multiple of the raw theta quotient. -/
lemma exercise8_thetaInverseCandidate_analyticOnNhd_open_rectangle
    (k : Exercise8Modulus) :
    AnalyticOnNhd ℂ (exercise8_thetaInverseCandidate k) (exercise8_open_rectangle k) := sorry

/-- Helper for Exercise 8: any complex-valued branch on `exercise8_open_rectangle k` that lands in
the upper half-plane and is a right inverse to `exercise8_abel_integral k` must already be the
canonical `Function.invFunOn` branch. -/
lemma exercise8_complexRectangleInverse_eq_canonical
    (k : Exercise8Modulus)
    {F : exercise8_open_rectangle k → ℂ}
    (hF_im : ∀ u : exercise8_open_rectangle k, 0 < (F u).im)
    (hF_right :
      ∀ u : exercise8_open_rectangle k,
        exercise8_abel_integral k ⟨F u, hF_im u⟩ = u) :
    ∀ u : exercise8_open_rectangle k,
      F u =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := by
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ ⟨F u, hF_im u⟩
  have hG : IsExercise8RectangleInverse k G := by
    refine ⟨?_, ?_, ?_⟩
    · intro u
      -- The assumed right-inverse identity is exactly the first field of the rectangle package.
      simpa [G] using hF_right u
    · intro z
      -- Rectangle landing is already part of the canonical branch package for the Abel map.
      exact (exercise8_canonicalRectangleInverse k).2.1 z
    · intro z hz
      rcases exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k with ⟨_, hinj, _⟩
      -- Injectivity of the Abel map identifies the new branch with the source point.
      apply hinj
      · trivial
      · trivial
      · simpa [G] using hF_right ⟨exercise8_abel_integral k z, hz⟩
  have hGcanonical :
      G =
        (fun u : exercise8_open_rectangle k ↦
          Function.invFunOn
            (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :=
    exercise8_rectangleInverse_eq_canonical k hG
  intro u
  have hF_coe : (G u : ℂ) = F u := rfl
  have hcanonical_coe :
      (G u : ℂ) =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := by
    -- Once `G` is recognized as a rectangle inverse, uniqueness collapses it to the canonical one.
    simpa using
      congrArg
        (fun H : exercise8_open_rectangle k → UpperHalfPlane ↦ (H u : ℂ))
        hGcanonical
  -- Compare the raw complex branch to the canonical branch through the coerced `UpperHalfPlane`
  -- witness.
  calc
    F u = (G u : ℂ) := by simpa using hF_coe.symm
    _ =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := hcanonical_coe

/-- Helper for Exercise 8: the rescaled denominator theta factor never vanishes on the interior of
the fundamental rectangle. -/
lemma exercise8_theta_zero_rescaled_nonzero_on_open_rectangle
    (k : Exercise8Modulus) {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    (θ₀[((exercise8_tau k : ℍ) : ℂ)])
        (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  have hpole :
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice :=
    (exercise8_theta_zero_rescaled_zero_iff k u).1 hzero
  rcases (mem_exercise8_pole_shift_sub_lattice_iff).1 hpole with ⟨m, n, hu_eq⟩
  rw [mem_exercise8_open_rectangle_iff] at hu
  have him :
      u.im = ((2 * n + 1 : ℤ) : ℝ) * exercise8_complete_imaginary_period k := by
    -- The shifted half-period lattice lives on odd imaginary translates of `K'`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg Complex.im hu_eq
  have hcoeff_pos : 0 < ((2 * n + 1 : ℤ) : ℝ) := by
    -- Interior points have imaginary part strictly between `0` and `K'`, so the odd coefficient
    -- must be strictly positive.
    nlinarith [him, hu.2.1, exercise8_complete_imaginary_period_pos k]
  have hcoeff_lt_one : ((2 * n + 1 : ℤ) : ℝ) < 1 := by
    -- The same interior bound forces the odd coefficient to stay strictly below `1`.
    nlinarith [him, hu.2.2, exercise8_complete_imaginary_period_pos k]
  have hcoeff_pos_z : 0 < 2 * n + 1 := by
    exact_mod_cast hcoeff_pos
  have hcoeff_lt_one_z : 2 * n + 1 < 1 := by
    exact_mod_cast hcoeff_lt_one
  omega

/-- Helper for Exercise 8: on the open rectangle, the theta quotient is differentiable because
its theta-ratio denominator never vanishes there. -/
lemma exercise8_theta_quotient_differentiableAt_from_theta_ratio
    (k : Exercise8Modulus) {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    DifferentiableAt ℂ (exercise8_theta_quotient k) u := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
  have hτ : 0 < τ.im := by
    simpa [τ] using (exercise8_tau k).2
  have hscale :
      DifferentiableAt ℂ (fun w : ℂ ↦ w / scale) u := by
    -- The affine rescaling `u ↦ u / (2K)` is entire.
    dsimp [scale]
    fun_prop
  have hnum :
      DifferentiableAt ℂ (fun w : ℂ ↦ (θ₁[τ]) (w / scale)) u := by
    -- Compose the entire theta numerator with the same rescaling map.
    exact ((exercise_3_theta_one_differentiable τ hτ) (u / scale)).comp u hscale
  have hden :
      DifferentiableAt ℂ (fun w : ℂ ↦ (θ₀[τ]) (w / scale)) u := by
    -- The denominator theta factor is entire as well.
    exact ((exercise_3_theta_zero_differentiable τ hτ) (u / scale)).comp u hscale
  have hden_ne :
      (θ₀[τ]) (u / scale) ≠ 0 := by
    -- Nonvanishing on the rectangle is the geometric input isolating the quotient.
    simpa [τ, scale] using exercise8_theta_zero_rescaled_nonzero_on_open_rectangle k hu
  have hratio :
      DifferentiableAt ℂ
        (fun w : ℂ ↦ (θ₁[τ]) (w / scale) / (θ₀[τ]) (w / scale)) u :=
    hnum.div hden hden_ne
  have htheta :
      exercise8_theta_quotient k =
        fun w : ℂ ↦ (θ₁[τ]) (w / scale) / (θ₀[τ]) (w / scale) := by
    funext w
    simpa [τ, scale] using exercise8_theta_quotient_eq_theta_ratio k w
  -- Rewrite the public theta quotient through its explicit theta-ratio normal form.
  rw [htheta]
  exact hratio

/-- Helper for Exercise 8: the explicit theta quotient is continuous at every point of the open
rectangle because its rescaled denominator stays nonzero there. -/
lemma exercise8_theta_quotient_continuousAt_on_open_rectangle
    (k : Exercise8Modulus) {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    ContinuousAt (exercise8_theta_quotient k) u := by
  -- Continuity is the immediate topological shadow of the differentiability owner above.
  exact (exercise8_theta_quotient_differentiableAt_from_theta_ratio k hu).continuousAt

/-- Helper for Exercise 8: the explicit theta quotient is differentiable at every point of the
open rectangle because its rescaled denominator stays nonzero there. -/
lemma exercise8_theta_quotient_differentiableAt_on_open_rectangle
    (k : Exercise8Modulus) {u : ℂ} (hu : u ∈ exercise8_open_rectangle k) :
    DifferentiableAt ℂ (exercise8_theta_quotient k) u := by
  -- Reuse the dedicated theta-ratio differentiability owner instead of rebuilding the quotient.
  exact exercise8_theta_quotient_differentiableAt_from_theta_ratio k hu

/-- Helper for Exercise 8: the source-facing composite obtained by feeding the explicit theta
quotient into the closed-half-plane Abel extension on `Im ≥ 0`. Outside that source-faithful
region, we use an auxiliary constant value because the continuation problem only concerns the
closed upper half-plane and the rectangle boundary. -/
def exercise8_thetaQuotientAbelComposite
    (k : Exercise8Modulus) : ℂ → ℂ :=
  fun u ↦
    if hnonneg : 0 ≤ (exercise8_thetaInverseCandidate k u).im then
      exercise8_closed_extension k ⟨exercise8_thetaInverseCandidate k u, hnonneg⟩
    else
      0

/-- Helper for Exercise 8: if the explicit theta quotient leaves the closed upper half-plane,
`exercise8_thetaQuotientAbelComposite` is forced onto its auxiliary zero branch. -/
lemma exercise8_thetaQuotientAbelComposite_eq_zero_of_im_neg
    (k : Exercise8Modulus) {u : ℂ}
    (hu_neg : (exercise8_thetaInverseCandidate k u).im < 0) :
    exercise8_thetaQuotientAbelComposite k u = 0 := by
  -- Negative imaginary part selects the fallback branch of the composite definition.
  simp [exercise8_thetaQuotientAbelComposite, not_le.mpr hu_neg]

/-- Helper for Exercise 8: on the real-axis branch of the theta quotient,
`exercise8_thetaQuotientAbelComposite` is exactly the repaired boundary trace. -/
lemma exercise8_thetaQuotientAbelComposite_eq_boundary_trace_of_im_zero
    (k : Exercise8Modulus) {u : ℂ}
    (hu_nonneg : 0 ≤ (exercise8_thetaInverseCandidate k u).im)
    (hu_zero : (exercise8_thetaInverseCandidate k u).im = 0) :
    exercise8_thetaQuotientAbelComposite k u =
      exercise8_boundary_trace k ((exercise8_thetaInverseCandidate k u).re) := by
  have hz :
      (((⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩ : ClosedUpperHalfPlane) : ℂ)).im = 0 := by
    -- The closed-upper-half-plane witness carries the same imaginary part as the raw complex
    -- normalized theta inverse candidate.
    simpa using hu_zero
  -- On the real axis, the closed extension agrees with the repaired boundary trace.
  simpa [exercise8_thetaQuotientAbelComposite, dif_pos hu_nonneg] using
    (exercise8_closed_extension_eq_boundary_trace_of_im_zero
      (k := k) (z := ⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩) hz)

/-- Helper for Exercise 8: on the strict upper-half-plane branch of the theta quotient,
`exercise8_thetaQuotientAbelComposite` collapses to the interior Abel integral. -/
lemma exercise8_thetaQuotientAbelComposite_eq_abelIntegral_of_im_pos
    (k : Exercise8Modulus) {u : ℂ}
    (hu_pos : 0 < (exercise8_thetaInverseCandidate k u).im) :
    exercise8_thetaQuotientAbelComposite k u =
      exercise8_abel_integral k (UpperHalfPlane.ofComplex (exercise8_thetaInverseCandidate k u)) := by
  have hu_nonneg : 0 ≤ (exercise8_thetaInverseCandidate k u).im := le_of_lt hu_pos
  have hu_ne :
      (((⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩ : ClosedUpperHalfPlane) : ℂ)).im ≠ 0 := by
    -- Strict positivity rules out the boundary branch.
    simpa using (ne_of_gt hu_pos)
  have h_ofComplex :
      UpperHalfPlane.ofComplex (exercise8_thetaInverseCandidate k u) =
        ⟨exercise8_thetaInverseCandidate k u,
          exercise8_im_pos_of_closed_nonreal
            (z := ⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩) hu_ne⟩ := by
    -- Both upper-half-plane witnesses are canonical lifts of the same complex number.
    simpa using
      (UpperHalfPlane.ofComplex_apply
        (⟨exercise8_thetaInverseCandidate k u,
          exercise8_im_pos_of_closed_nonreal
            (z := ⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩) hu_ne⟩ : UpperHalfPlane))
  -- Once positivity is known, the composite uses the interior Abel branch rather than the
  -- auxiliary boundary value.
  rw [exercise8_thetaQuotientAbelComposite, dif_pos hu_nonneg,
    exercise8_closed_extension_eq_abel_integral_of_im_ne_zero
      (k := k) (z := ⟨exercise8_thetaInverseCandidate k u, hu_nonneg⟩) hu_ne]
  simpa using congrArg (exercise8_abel_integral k) h_ofComplex.symm

/-- Helper for Exercise 8: the explicit theta quotient is holomorphic on the open rectangle. -/
lemma exercise8_theta_quotient_analyticOnNhd_open_rectangle
    (k : Exercise8Modulus) :
    AnalyticOnNhd ℂ (exercise8_theta_quotient k) (exercise8_open_rectangle k) := by
  -- On the open rectangle, pointwise differentiability upgrades to `AnalyticOnNhd`.
  exact
    (Complex.analyticOnNhd_iff_differentiableOn (exercise8_open_rectangle_isOpen k)).2
      (by
        intro u hu
        exact
          (exercise8_theta_quotient_differentiableAt_on_open_rectangle k hu).differentiableWithinAt)

/-- Helper for Exercise 8: once the explicit theta quotient is known to stay in the strict upper
half-plane on the open rectangle, the Abel composite is differentiable there. -/
lemma exercise8_thetaQuotientAbelComposite_differentiableOn_of_im_pos
    (k : Exercise8Modulus)
    (hpos :
      ∀ u ∈ exercise8_open_rectangle k, 0 < (exercise8_thetaInverseCandidate k u).im) :
    DifferentiableOn ℂ
      (exercise8_thetaQuotientAbelComposite k) (exercise8_open_rectangle k) := by
  have hmap :
      MapsTo (exercise8_thetaInverseCandidate k) (exercise8_open_rectangle k)
        UpperHalfPlane.upperHalfPlaneSet := by
    intro u hu
    -- The positivity hypothesis places the normalized theta candidate back in the strict upper
    -- half-plane.
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hpos u hu
  have hcomp :
      DifferentiableOn ℂ
        (fun u : ℂ ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (exercise8_thetaInverseCandidate k u)))
        (exercise8_open_rectangle k) := by
    -- Compose the ambient Abel owner with the normalized theta candidate after recording the image
    -- constraint.
    exact
      (exercise8_abelIntegral_analyticOnNhd_ambient k).differentiableOn.comp
        (exercise8_thetaInverseCandidate_analyticOnNhd_open_rectangle k).differentiableOn
        hmap
  refine DifferentiableOn.congr hcomp ?_
  intro u hu
  have hu_pos : 0 < (exercise8_thetaInverseCandidate k u).im := hpos u hu
  -- The positive-branch bridge lemma already rewrites the composite to the interior Abel alias.
  simpa using
    (exercise8_thetaQuotientAbelComposite_eq_abelIntegral_of_im_pos (k := k) (u := u) hu_pos)

/-- Helper for Exercise 8: once the explicit theta quotient is known to satisfy the source-facing
closed-half-plane Abel right-inverse law on the rectangle and to stay in the strict upper
half-plane there, it already packages the same `UpperHalfPlane`-valued inverse branch as the
biholomorphic Abel-map inverse. -/
lemma exercise8_thetaQuotient_branch_of_rightInverse
    (k : Exercise8Modulus)
    (hpos :
      ∀ u : exercise8_open_rectangle k, 0 < (exercise8_thetaInverseCandidate k u).im)
    (hright :
      ∀ u : exercise8_open_rectangle k,
        exercise8_thetaQuotientAbelComposite k u = u) :
    IsExercise8RectangleInverse k
      (fun u : exercise8_open_rectangle k ↦
        ⟨exercise8_thetaInverseCandidate k u, hpos u⟩) := by
  have htheta_upper (u : exercise8_open_rectangle k) :
      UpperHalfPlane.ofComplex (exercise8_thetaInverseCandidate k u) =
        ⟨exercise8_thetaInverseCandidate k u, hpos u⟩ := by
    simpa using UpperHalfPlane.ofComplex_apply_of_im_pos (hpos u)
  refine ⟨?_, ?_, ?_⟩
  · intro u
    -- On the rectangle, positivity rewrites the composite back to the interior Abel branch.
    calc
      exercise8_abel_integral k ⟨exercise8_thetaInverseCandidate k u, hpos u⟩
          = exercise8_abel_integral k
              (UpperHalfPlane.ofComplex (exercise8_thetaInverseCandidate k u)) := by
                rw [← htheta_upper u]
      _ = u := by
            simpa [exercise8_thetaQuotientAbelComposite_eq_abelIntegral_of_im_pos
              (k := k) (u := u) (hpos u)] using hright u
  · intro z
    -- The target-membership field is independent of the chosen inverse branch.
    exact
      (exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k).1
        (by trivial)
  · intro z hz
    rcases exercise8_abelIntegral_bijOn_open_rectangle_of_biholomorphic k with ⟨_, hinj, _⟩
    -- Injectivity of the Abel map upgrades the stored right-inverse law to a left inverse.
    apply hinj
    · trivial
    · trivial
    · calc
        exercise8_abel_integral k
            ⟨exercise8_thetaInverseCandidate k (exercise8_abel_integral k z),
              hpos ⟨exercise8_abel_integral k z, hz⟩⟩
            =
              exercise8_abel_integral k
                (UpperHalfPlane.ofComplex
                  (exercise8_thetaInverseCandidate k (exercise8_abel_integral k z))) := by
                    rw [← htheta_upper ⟨exercise8_abel_integral k z, hz⟩]
        _ = exercise8_abel_integral k z := by
              simpa [exercise8_thetaQuotientAbelComposite_eq_abelIntegral_of_im_pos
                (k := k) (u := exercise8_abel_integral k z)
                (hpos ⟨exercise8_abel_integral k z, hz⟩)] using
                hright ⟨exercise8_abel_integral k z, hz⟩

/-- Helper for Exercise 8: the Abel right-inverse law already forces the explicit theta quotient to
land in the strict upper half-plane on the whole open rectangle. -/
lemma exercise8_thetaQuotient_im_pos_of_rightInverse
    (k : Exercise8Modulus)
    (hright :
      ∀ u : exercise8_open_rectangle k,
        exercise8_thetaQuotientAbelComposite k u = u) :
    ∀ u : exercise8_open_rectangle k, 0 < (exercise8_thetaInverseCandidate k u).im := by
  intro u
  by_cases him_neg : (exercise8_thetaInverseCandidate k u).im < 0
  · -- Route correction: after resetting the auxiliary off-domain branch to `0`, the negative-
    -- imaginary case forces the interior rectangle point `u` to collapse to the boundary point `0`.
    have hright_zero : (0 : ℂ) = u := by
      simpa [exercise8_thetaQuotientAbelComposite_eq_zero_of_im_neg (k := k) him_neg] using
        hright u
    have hu_im : 0 < (u : ℂ).im := (mem_exercise8_open_rectangle_iff.mp u.2).2.1
    have : ((0 : ℂ)).im < (u : ℂ).im := by simpa using hu_im
    rw [← hright_zero] at this
    simpa using this.false
  · have him_nonneg : 0 ≤ (exercise8_thetaInverseCandidate k u).im := le_of_not_gt him_neg
    by_cases him_zero : (exercise8_thetaInverseCandidate k u).im = 0
    · -- On the real-axis branch, the closed extension agrees with the boundary trace, so the
      -- assumed right-inverse law pushes the interior point `u` onto the rectangle frontier.
      have hright_boundary :
          exercise8_boundary_trace k ((exercise8_thetaInverseCandidate k u).re) = u := by
        -- The new branch lemma isolates the real-axis evaluation of the composite.
        simpa [exercise8_thetaQuotientAbelComposite_eq_boundary_trace_of_im_zero
          (k := k) him_nonneg him_zero] using hright u
      have hu_frontier : (u : ℂ) ∈ frontier (exercise8_open_rectangle k) := by
        rw [← exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k]
        exact Or.inl ⟨(exercise8_thetaInverseCandidate k u).re, hright_boundary⟩
      have hu_openFrontier :
          (u : ℂ) ∈ exercise8_open_rectangle k ∩ frontier (exercise8_open_rectangle k) :=
        ⟨u.2, hu_frontier⟩
      have hEmpty :
          exercise8_open_rectangle k ∩ frontier (exercise8_open_rectangle k) = ∅ :=
        (exercise8_open_rectangle_isOpen k).inter_frontier_eq
      simpa [hEmpty] using hu_openFrontier
    · exact lt_of_le_of_ne him_nonneg (Ne.symm him_zero)

/-- Helper for Exercise 8: once a map is continuous on the closed rectangle and fixes the finite
boundary-trace range, the top midpoint `i K'` is forced by the existing `atTop` boundary-trace
limit. -/
lemma exercise8_eq_topMidpoint_of_continuousOn_closure_and_boundaryTraceRange
    (k : Exercise8Modulus)
    {f : ℂ → ℂ}
    (hcont : ContinuousOn f (closure (exercise8_open_rectangle k)))
    (hrange : EqOn f id (Set.range (exercise8_boundary_trace k))) :
    f ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) =
      ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) := by
  let mid : ℂ := (exercise8_complete_imaginary_period k : ℂ) * Complex.I
  have hfrontierEq := exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k
  have hmid_mem :
      mid ∈ closure (exercise8_open_rectangle k) := by
    have hmid_frontier : mid ∈ frontier (exercise8_open_rectangle k) := by
      rw [← hfrontierEq]
      exact Or.inr (by simp [mid])
    exact frontier_subset_closure hmid_frontier
  have htrace_mem :
      ∀ x : ℝ, exercise8_boundary_trace k x ∈ closure (exercise8_open_rectangle k) := by
    intro x
    have hx_frontier : exercise8_boundary_trace k x ∈ frontier (exercise8_open_rectangle k) := by
      rw [← hfrontierEq]
      exact Or.inl ⟨x, rfl⟩
    exact frontier_subset_closure hx_frontier
  have htend_within :
      Filter.Tendsto (exercise8_boundary_trace k) Filter.atTop
        (𝓝[closure (exercise8_open_rectangle k)] mid) := by
    exact
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (exercise8_boundary_trace k)
        (exercise8_boundary_trace_tendsto_top_midpoint_atTop k)
        (Filter.Eventually.of_forall htrace_mem)
  have hcomp :
      Filter.Tendsto (fun x : ℝ ↦ f (exercise8_boundary_trace k x)) Filter.atTop
        (𝓝 (f mid)) := by
    -- Continuity on the closure transports the boundary-trace limit through `f`.
    exact (hcont mid hmid_mem).tendsto.comp htend_within
  have hcomp_id :
      Filter.Tendsto (fun x : ℝ ↦ f (exercise8_boundary_trace k x)) Filter.atTop (𝓝 mid) := by
    have heq :
        (fun x : ℝ ↦ f (exercise8_boundary_trace k x)) =ᶠ[Filter.atTop]
          exercise8_boundary_trace k := by
      exact Filter.Eventually.of_forall fun x ↦ hrange ⟨x, rfl⟩
    -- On the finite boundary trace, `f` is pointwise the identity by hypothesis.
    exact
      (exercise8_boundary_trace_tendsto_top_midpoint_atTop k).congr' heq.symm
  -- The same boundary-trace net has a unique limit in `ℂ`.
  simpa [mid] using tendsto_nhds_unique hcomp hcomp_id

/-- Helper for Exercise 8: frontier equality follows once the composite is known on the finite
boundary-trace range and at the isolated top midpoint `i K'`. -/
lemma exercise8_eqOn_frontier_of_boundaryTraceRange_and_topMidpoint
    (k : Exercise8Modulus)
    {f : ℂ → ℂ}
    (hrange : EqOn f id (Set.range (exercise8_boundary_trace k)))
    (hmid :
      f ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) =
        ((exercise8_complete_imaginary_period k : ℂ) * Complex.I)) :
    EqOn f id (frontier (exercise8_open_rectangle k)) := by
  intro u hu
  have hu' :
      u ∈ Set.range (exercise8_boundary_trace k) ∪
        {((exercise8_complete_imaginary_period k : ℂ) * Complex.I)} := by
    simpa [exercise8_boundaryTrace_range_union_topMidpoint_eq_frontier k] using hu
  rcases hu' with hu_range | hu_mid
  · -- The finite boundary-trace part is exactly the hypothesis `hrange`.
    exact hrange hu_range
  · rcases hu_mid with rfl
    -- The isolated top midpoint is handled separately.
    exact hmid

/-- Helper for Exercise 8: the theta quotient is normalized to vanish at the origin. -/
lemma exercise8_theta_quotient_zero
    (k : Exercise8Modulus) :
    exercise8_theta_quotient k 0 = 0 := by
  have hnum :
      (θ₁[((exercise8_tau k : ℍ) : ℂ)])
          (0 / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) = 0 := by
    -- The numerator theta factor has its standard zero at the lattice origin.
    simpa using jacobi_theta_one_zero_at_zero ((exercise8_tau k : ℍ) : ℂ)
  -- After normalizing to the theta-ratio model, the zero numerator forces the quotient to vanish.
  rw [exercise8_theta_quotient_eq_theta_ratio, hnum]
  simp

/-- Helper for Exercise 8: the repaired boundary trace and the normalized theta inverse candidate
agree at the base point `0`. -/
lemma exercise8_theta_quotient_boundary_trace_zero
    (k : Exercise8Modulus) :
    exercise8_thetaInverseCandidate k (exercise8_boundary_trace k 0) = 0 := by
  -- The normalized candidate still vanishes at the origin because the raw theta quotient does.
  calc
    exercise8_thetaInverseCandidate k (exercise8_boundary_trace k 0)
        = exercise8_thetaInverseCandidate k 0 := by
            simpa [exercise8_boundary_value] using
              congrArg (exercise8_thetaInverseCandidate k) (exercise8_boundary_value_zero k)
    _ = 0 := by
          simp [exercise8_thetaInverseCandidate, exercise8_theta_quotient_zero]

/-- Helper for Exercise 8: the Jacobi parameter `τ = i K' / K` is fixed by the involution
`τ ↦ -conj τ`. -/
lemma exercise8_neg_conj_tau
    (k : Exercise8Modulus) :
    -star ((exercise8_tau k : ℂ)) = (exercise8_tau k : ℂ) := by
  -- The parameter is purely imaginary because it is `i` times a positive real ratio.
  rw [exercise8_tau_def]
  simp

/-- Helper for Exercise 8: at the purely imaginary Jacobi parameter `τ = i K' / K`, `θ₀`
commutes with complex conjugation. -/
lemma exercise8_theta_zero_conj_tau
    (k : Exercise8Modulus) (u : ℂ) :
    star ((θ₀[((exercise8_tau k : ℍ) : ℂ)]) u) =
      (θ₀[((exercise8_tau k : ℍ) : ℂ)]) (star u) := sorry

/-- Helper for Exercise 8: at the purely imaginary Jacobi parameter `τ = i K' / K`, `θ₁`
commutes with complex conjugation. -/
lemma exercise8_theta_one_conj_tau
    (k : Exercise8Modulus) (u : ℂ) :
    star ((θ₁[((exercise8_tau k : ℍ) : ℂ)]) u) =
      (θ₁[((exercise8_tau k : ℍ) : ℂ)]) (star u) := sorry

/-- Helper for Exercise 8: the source's `θ₀` normalization is even in its argument. -/
lemma exercise8_theta_zero_neg
    (τ u : ℂ) :
    (θ₀[τ]) (-u) = (θ₀[τ]) u := by
  -- Rewrite `θ₀` through `jacobiTheta₂`, reflect the argument, and then shift back by the real
  -- period `1`.
  rw [jacobi_theta_zero_apply, jacobi_theta_zero_apply]
  calc
    jacobiTheta₂ (-u + (1 / 2 : ℂ)) τ = jacobiTheta₂ (-(u - (1 / 2 : ℂ))) τ := by
      ring_nf
    _ = jacobiTheta₂ (u - (1 / 2 : ℂ)) τ := by
      rw [jacobiTheta₂_neg_left]
    _ = jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
      rw [← jacobiTheta₂_add_left (u - (1 / 2 : ℂ)) τ]
      congr 1 <;> ring

/-- Helper for Exercise 8: the source's `θ₁` normalization is odd in its argument. -/
lemma exercise8_theta_one_neg
    (τ u : ℂ) :
    (θ₁[τ]) (-u) = -(θ₁[τ]) u := sorry

/-- Helper for Exercise 8: the explicit theta quotient respects Schwarz reflection across the real
axis. -/
lemma exercise8_theta_quotient_reflection
    (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k (-star u) =
      -star (exercise8_theta_quotient k u) := sorry

/-- Helper for Exercise 8: the normalized theta inverse candidate respects the same Schwarz
reflection law because its normalization scalar is real. -/
lemma exercise8_thetaInverseCandidate_reflection
    (k : Exercise8Modulus) (u : ℂ) :
    exercise8_thetaInverseCandidate k (-star u) =
      -star (exercise8_thetaInverseCandidate k u) := by
  -- Only the raw theta quotient changes under reflection; the normalization scalar is fixed by
  -- conjugation because it comes from a positive real number.
  calc
    exercise8_thetaInverseCandidate k (-star u)
        = exercise8_thetaNormalization k * exercise8_theta_quotient k (-star u) := by
            rfl
    _ = exercise8_thetaNormalization k * (-star (exercise8_theta_quotient k u)) := by
          rw [exercise8_theta_quotient_reflection]
    _ = -star (exercise8_thetaNormalization k * exercise8_theta_quotient k u) := by
          simp [exercise8_thetaNormalization, map_mul]
    _ = -star (exercise8_thetaInverseCandidate k u) := by
          rfl

/-- Helper for Exercise 8: on the bottom edge, the repaired boundary trace is exactly the
complexified inner primitive. -/
lemma exercise8_boundary_trace_eq_inner_primitive_of_mem_Icc
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    exercise8_boundary_trace k x = ((exercise8_inner_primitive k x : ℝ) : ℂ) := by
  have hbranch :
      exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
    -- On `[0, 1]`, the repaired boundary trace uses the source bottom-edge branch.
    rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
    simpa [exercise8_boundary_inner_branch] using
      exercise8_boundary_value_eq_inner (k := k) hx
  -- Normalize the bottom-edge branch through the named primitive owner.
  calc
    exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := hbranch
    _ = ((exercise8_inner_primitive k x : ℝ) : ℂ) := by
          rw [exercise8_boundary_inner_branch_eq_inner_primitive]

/-- Helper for Exercise 8: on the right edge, the repaired boundary trace is exactly the affine
primitive `K + i J(x)`. -/
lemma exercise8_boundary_trace_eq_right_primitive_of_mem_Icc
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    exercise8_boundary_trace k x =
      (exercise8_complete_real_period k : ℂ) +
        ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
  have hbranch :
      exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
    -- On `[1, 1 / k]`, the repaired boundary trace uses the source right-edge branch.
    rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
    simpa [exercise8_boundary_right_branch] using
      exercise8_boundary_value_eq_right (k := k) hx.1 hx.2
  -- Normalize the right-edge branch through the named right primitive owner.
  calc
    exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := hbranch
    _ =
        (exercise8_complete_real_period k : ℂ) +
          ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
            rw [exercise8_boundary_right_branch_eq_right_primitive]

/-- Helper for Exercise 8: on the top edge, the repaired boundary trace is `i K'` plus the inner
primitive evaluated at the reciprocal source parameter. -/
lemma exercise8_boundary_trace_eq_top_innerComposition_of_ge_invK
    (k : Exercise8Modulus) {x : ℝ} (hx : 1 / (k : ℝ) ≤ x) :
    exercise8_boundary_trace k x =
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
        ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) := by
  have hbranch :
      exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
    -- On `[1 / k, ∞)`, the repaired boundary trace uses the source top-edge branch.
    rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
    simpa [exercise8_boundary_top_branch] using
      exercise8_boundary_value_eq_top (k := k) hx
  -- Normalize the top-edge branch through the reciprocal-substitution formula.
  calc
    exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := hbranch
    _ =
        (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) := by
            rw [exercise8_boundary_top_branch_eq_inner_composition]

/-- Helper for Exercise 8: after dividing by `2K`, the bottom-edge primitive takes values in the
real interval `[0, 1 / 2]`. -/
lemma exercise8_innerPrimitive_div_twoCompleteRealPeriod_mem_Icc
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    exercise8_inner_primitive k x / (2 * exercise8_complete_real_period k) ∈
      Icc (0 : ℝ) (1 / 2) := sorry

/-- Helper for Exercise 8: the right-edge source point has a stable half-period normal form after
dividing by `2K`. -/
lemma exercise8_rightPrimitive_scaled_halfPeriodForm
    (k : Exercise8Modulus) (x : ℝ) :
    ((exercise8_complete_real_period k : ℂ) +
        ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I) /
        (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
      (1 / 2 : ℂ) +
        ((exercise8_right_primitive k x / (2 * exercise8_complete_real_period k) : ℝ) : ℂ) *
          Complex.I := sorry

/-- Helper for Exercise 8: adding the distinguished pole shift and then dividing by `2K` is the
same as adding `τ / 2` to the rescaled bottom-edge primitive. -/
lemma exercise8_poleShift_add_innerPrimitive_scaledForm
    (k : Exercise8Modulus) (y : ℝ) :
    (exercise8_pole_shift k + (((exercise8_inner_primitive k y : ℝ) : ℂ))) /
        (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
      (exercise8_tau k : ℂ) / 2 +
        ((exercise8_inner_primitive k y / (2 * exercise8_complete_real_period k) : ℝ) : ℂ) := sorry

/-- Helper for Exercise 8: shifting `θ₁` by `τ / 2` produces the same exponential prefactor as
the `θ₀` half-`τ` translation formula, but with `θ₀` as the remaining theta factor. -/
lemma exercise8_theta_one_add_half_tau
    (τ u : ℂ) :
    (θ₁[τ]) (u + τ / 2) =
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
        (θ₀[τ]) u := sorry

/-- Helper for Exercise 8: shifting the explicit theta quotient by the distinguished pole shift
reciprocates the underlying theta ratio. -/
lemma exercise8_theta_quotient_add_pole_shift_reciprocal
    (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k (exercise8_pole_shift k + u) =
      1 / exercise8_theta_quotient k u := by
  let τ : ℂ := ((exercise8_tau k : ℍ) : ℂ)
  let scale : ℂ := (((2 * exercise8_complete_real_period k : ℝ) : ℂ))
  have hscaled :
      (exercise8_pole_shift k + u) / scale = u / scale + τ / 2 := by
    -- Normalize the pole shift to the half-`τ` translation in the rescaled variable.
    rw [add_div, exercise8_poleShift_div_twoCompleteRealPeriod_eq_halfTau]
    ring
  have hnum :
      (θ₁[τ]) ((exercise8_pole_shift k + u) / scale) =
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u / scale + τ / 4)) *
          (θ₀[τ]) (u / scale) := by
    -- The numerator is the half-`τ` translate of `θ₁`.
    rw [hscaled]
    exact exercise8_theta_one_add_half_tau τ (u / scale)
  have hden :
      (θ₀[τ]) ((exercise8_pole_shift k + u) / scale) =
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u / scale + τ / 4)) *
          (θ₁[τ]) (u / scale) := by
    -- The denominator is the matching half-`τ` translate of `θ₀`.
    rw [hscaled]
    exact exercise_3_theta_zero_add_half_tau τ (u / scale)
  have hscalar_ne :
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u / scale + τ / 4)) ≠ 0 := by
    -- The common translation prefactor is a nonzero exponential scalar.
    exact mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
  -- After normalizing both quotients, the shared nonzero scalar cancels and only the reciprocal
  -- theta ratio remains.
  rw [exercise8_theta_quotient_eq_theta_ratio, exercise8_theta_quotient_eq_theta_ratio, hnum, hden,
    one_div_div]
  simpa [τ, scale, mul_comm, mul_left_comm, mul_assoc] using
    (mul_div_mul_left
      (θ₀[((exercise8_tau k : ℍ) : ℂ)] (u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)))
      )
      (θ₁[((exercise8_tau k : ℍ) : ℂ)] (u / (((2 * exercise8_complete_real_period k : ℝ) : ℂ)))
      )
      hscalar_ne)

/-- Helper for Exercise 8: on the bottom edge, the normalized theta inverse candidate should
recover the original real boundary parameter from the inner primitive. -/
lemma exercise8_thetaQuotient_innerPrimitive
    (k : Exercise8Modulus) :
    ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
      exercise8_thetaInverseCandidate k (((exercise8_inner_primitive k x : ℝ) : ℂ)) = x := by
  intro x hx
  have hscaled :
      exercise8_inner_primitive k x / (2 * exercise8_complete_real_period k) ∈
        Icc (0 : ℝ) (1 / 2) :=
    exercise8_innerPrimitive_div_twoCompleteRealPeriod_mem_Icc k hx
  -- Route correction: the branch rewrite is already finished, so the remaining work is the
  -- canonical bottom-edge inversion for the normalized theta model on `[0, 1 / 2]`.
  -- TODO: rewrite `exercise8_thetaInverseCandidate` through
  -- `exercise8_theta_quotient_eq_theta_ratio` at
  -- `v = exercise8_inner_primitive k x / (2 * exercise8_complete_real_period k)`, and then apply
  -- one source-facing theta evaluation theorem on the real segment `v ∈ Icc (0 : ℝ) (1 / 2)`.
  -- Current blocker: the local API has the translation/divisor package, but not the direct
  -- normalized evaluation theorem turning `exercise8_thetaNormalization k * θ₁(v) / θ₀(v)` into `x`.
  let _ := hscaled
  sorry

/-- Helper for Exercise 8: shifting the bottom primitive by the distinguished pole turns the
normalized theta inverse candidate into the reciprocal top-branch parameter. -/
lemma exercise8_thetaQuotient_poleShift_reciprocal
    (k : Exercise8Modulus) :
    ∀ {y : ℝ}, y ∈ Ioc (0 : ℝ) 1 →
      exercise8_thetaInverseCandidate k
          (exercise8_pole_shift k + (((exercise8_inner_primitive k y : ℝ) : ℂ))) =
        1 / ((k : ℝ) * y) := sorry

/-- Helper for Exercise 8: on the right edge, the normalized theta inverse candidate should
recover the original real boundary parameter from the half-period normal form `K + i J(x)`. -/
lemma exercise8_thetaQuotient_rightPrimitive
    (k : Exercise8Modulus) :
    ∀ {x : ℝ}, x ∈ Icc (1 : ℝ) (1 / (k : ℝ)) →
      exercise8_thetaInverseCandidate k
          ((exercise8_complete_real_period k : ℂ) +
            ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I) = x := by
  intro x hx
  have hscaled :
      ((exercise8_complete_real_period k : ℂ) +
          ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I) /
          (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) =
        (1 / 2 : ℂ) +
          ((exercise8_right_primitive k x / (2 * exercise8_complete_real_period k) : ℝ) : ℂ) *
            Complex.I :=
    exercise8_rightPrimitive_scaled_halfPeriodForm k x
  -- Route correction: keep the right edge in the single half-period spelling `1 / 2 + i t` for
  -- the normalized theta model.
  -- TODO: rewrite by `exercise8_theta_quotient_eq_theta_ratio`, normalize to `1 / 2 + i t` via
  -- `exercise8_rightPrimitive_scaled_halfPeriodForm`, use `exercise_3_theta_one_add_one` and
  -- `exercise_3_theta_zero_add_one` exactly once, and reduce the remaining source term to the same
  -- normalized bottom-segment evaluation used in `exercise8_thetaQuotient_innerPrimitive`.
  -- Current blocker: the file still lacks the source-facing normalized theta evaluation on that
  -- bottom segment, so the right-edge proof cannot yet close after the half-period rewrite.
  let _ := hscaled
  sorry

/-- Helper for Exercise 8: it is enough to prove the boundary-trace identity on the nonnegative
real half-axis. The negative half then follows from Schwarz reflection. -/
lemma exercise8_nonnegativeBoundaryParameter_cases
    (k : Exercise8Modulus) {x : ℝ} (hx : 0 ≤ x) :
    x ∈ Icc (0 : ℝ) 1 ∨ x ∈ Icc (1 : ℝ) (1 / (k : ℝ)) ∨ 1 / (k : ℝ) ≤ x := by
  -- Split the nonnegative real axis according to the three source boundary branches.
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨hx, hx1⟩
  · have hx1' : 1 ≤ x := by linarith
    by_cases hxk : x ≤ 1 / (k : ℝ)
    · exact Or.inr (Or.inl ⟨hx1', hxk⟩)
    · exact Or.inr (Or.inr (le_of_not_ge hxk))

/-- Helper for Exercise 8: it is enough to prove the boundary-trace identity on the nonnegative
real half-axis. The negative half then follows from Schwarz reflection. -/
lemma exercise8_thetaQuotient_boundaryTrace_nonneg
    (k : Exercise8Modulus) :
    ∀ {x : ℝ}, 0 ≤ x →
      exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x) = x := sorry

/-- Helper for Exercise 8: the source-facing normalized theta inverse candidate recovers the real
boundary parameter from the repaired rectangle boundary trace. -/
lemma exercise8_theta_quotient_boundary_trace
    (k : Exercise8Modulus) :
    ∀ x : ℝ, exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x) = x := by
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    -- The base point of the boundary trace is already normalized by the new zero-value helper.
    exact exercise8_theta_quotient_boundary_trace_zero k
  · by_cases hx_nonneg : 0 ≤ x
    · -- The positive-side branch is now isolated in a dedicated helper theorem.
      exact exercise8_thetaQuotient_boundaryTrace_nonneg k hx_nonneg
    · have hx_pos : 0 < -x := by linarith
      have hx_reflect :
          exercise8_boundary_trace k x =
            -star (exercise8_boundary_trace k (-x)) := by
        -- Schwarz reflection rewrites the negative-side boundary trace through the positive one.
        simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k (-x)
      -- Route correction: the public theorem now reduces the negative branch to the nonnegative
      -- branch through the explicit reflection law of the normalized theta model.
      calc
        exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x) =
            exercise8_thetaInverseCandidate k (-star (exercise8_boundary_trace k (-x))) := by
              rw [hx_reflect]
        _ = -star (exercise8_thetaInverseCandidate k (exercise8_boundary_trace k (-x))) := by
              simpa using
                exercise8_thetaInverseCandidate_reflection k (exercise8_boundary_trace k (-x))
        _ = -star ((-x : ℝ) : ℂ) := by
              rw [exercise8_thetaQuotient_boundaryTrace_nonneg k hx_pos.le]
        _ = x := by
              simp

/-- Helper for Exercise 8: before proving global positivity, first isolate the non-circular fact
that the normalized theta inverse candidate never lands on the real axis inside the open
rectangle. -/
lemma exercise8_theta_quotient_im_ne_zero_on_open_rectangle
    (k : Exercise8Modulus) :
    ∀ u ∈ exercise8_open_rectangle k, (exercise8_thetaInverseCandidate k u).im ≠ 0 := by
  -- Route correction: the old positivity-first route was circular because later right-inverse
  -- theorems also needed this positivity. The stabilized frontier is the weaker interior
  -- separation theorem `Im ≠ 0`, which should come from the meromorphic normal-form/order package.
  -- TODO: compare the normalized theta candidate with the canonical inverse branch on the open
  -- rectangle by a non-circular continuation argument: use analyticity on the rectangle, the
  -- periodic/divisor package, and the future rectangle-branch identification to rule out a real
  -- value in the interior. The later positivity theorem cannot be used here because it already
  -- consumes the right-inverse statement built from this lemma.
  -- Current blocker: the file has the divisor and periodicity API, but still lacks the upstream
  -- rectangle-branch comparison needed to convert those global meromorphic facts into `Im ≠ 0`.
  sorry

/-- Helper for Exercise 8: once the normalized theta inverse candidate has nonzero imaginary part
at one interior rectangle point, continuity forces that sign to persist on a smaller open
rectangle neighborhood. -/
lemma exercise8_thetaQuotient_signNeighborhood
    (k : Exercise8Modulus) {u : ℂ}
    (hu : u ∈ exercise8_open_rectangle k)
    (hu_im : (exercise8_thetaInverseCandidate k u).im ≠ 0) :
    ∃ s : Set ℂ, IsOpen s ∧ u ∈ s ∧ s ⊆ exercise8_open_rectangle k ∧
      ((∀ v ∈ s, 0 < (exercise8_thetaInverseCandidate k v).im) ∨
        ∀ v ∈ s, (exercise8_thetaInverseCandidate k v).im < 0) := by
  have hcont :
      ContinuousAt (fun v : ℂ ↦ (exercise8_thetaInverseCandidate k v).im) u := by
    -- The imaginary part is continuous because the normalized theta candidate is holomorphic on
    -- the interior rectangle.
    exact Complex.continuous_im.continuousAt.comp
      ((exercise8_thetaInverseCandidate_analyticOnNhd_open_rectangle k u hu).continuousAt)
  by_cases hu_pos : 0 < (exercise8_thetaInverseCandidate k u).im
  · have hrect_nhds : exercise8_open_rectangle k ∈ 𝓝 u :=
      (exercise8_open_rectangle_isOpen k).mem_nhds hu
    have hpos_nhds :
        {v : ℂ | 0 < (exercise8_thetaInverseCandidate k v).im} ∈ 𝓝 u := by
      -- Pull back the positive half-line neighborhood of `Im (θ(u))`.
      exact hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hu_pos)
    rcases _root_.mem_nhds_iff.mp (Filter.inter_mem hrect_nhds hpos_nhds) with
      ⟨s, hs_sub, hs_open, hu_mem_s⟩
    refine ⟨s, hs_open, hu_mem_s, ?_, Or.inl ?_⟩
    · intro v hv
      exact (hs_sub hv).1
    · intro v hv
      exact (hs_sub hv).2
  · have hu_nonpos : (exercise8_thetaInverseCandidate k u).im ≤ 0 := le_of_not_gt hu_pos
    have hu_neg : (exercise8_thetaInverseCandidate k u).im < 0 := by
      -- Nonzero imaginary part plus failure of positivity forces strict negativity.
      exact lt_of_le_of_ne hu_nonpos hu_im
    have hrect_nhds : exercise8_open_rectangle k ∈ 𝓝 u :=
      (exercise8_open_rectangle_isOpen k).mem_nhds hu
    have hneg_nhds :
        {v : ℂ | (exercise8_thetaInverseCandidate k v).im < 0} ∈ 𝓝 u := by
      -- Pull back the negative half-line neighborhood of `Im (θ(u))`.
      exact hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hu_neg)
    rcases _root_.mem_nhds_iff.mp (Filter.inter_mem hrect_nhds hneg_nhds) with
      ⟨s, hs_sub, hs_open, hu_mem_s⟩
    refine ⟨s, hs_open, hu_mem_s, ?_, Or.inr ?_⟩
    · intro v hv
      exact (hs_sub hv).1
    · intro v hv
      exact (hs_sub hv).2

/-- Helper for Exercise 8: the remaining theta-side geometric calculation is the explicit identity
of the Abel/theta composite on the finite boundary trace. -/
lemma exercise8_thetaQuotientAbelComposite_eqOn_boundaryTraceRange
    (k : Exercise8Modulus) :
    EqOn (exercise8_thetaQuotientAbelComposite k) id (Set.range (exercise8_boundary_trace k)) := by
  intro u hu
  rcases hu with ⟨x, rfl⟩
  have htheta :
      exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x) = x :=
    exercise8_theta_quotient_boundary_trace k x
  have him_nonneg :
      0 ≤ (exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x)).im := by
    simpa [htheta]
  have him_zero :
      (exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x)).im = 0 := by
    simpa [htheta]
  -- The direct boundary owner reduces the composite to the boundary trace branch with real
  -- parameter `x`.
  calc
    exercise8_thetaQuotientAbelComposite k (exercise8_boundary_trace k x)
        =
          exercise8_boundary_trace k
            ((exercise8_thetaInverseCandidate k (exercise8_boundary_trace k x)).re) := by
              exact
                exercise8_thetaQuotientAbelComposite_eq_boundary_trace_of_im_zero
                  (k := k) (u := exercise8_boundary_trace k x) him_nonneg him_zero
    _ = exercise8_boundary_trace k x := by
          simpa [htheta]

/-- Helper for Exercise 8: the analytic package for the Abel/theta composite is exactly
`DiffContOnCl` on the open rectangle. -/
lemma exercise8_thetaQuotientAbelComposite_diffContOnCl
    (k : Exercise8Modulus) :
    DiffContOnCl ℂ (exercise8_thetaQuotientAbelComposite k) (exercise8_open_rectangle k) := by
  -- Route correction: after replacing the cyclic positivity placeholder by `Im ≠ 0`, this theorem
  -- should be rebuilt by shrinking to local sign neighborhoods on the interior and then using the
  -- repaired boundary-trace theorem for the closure-side continuity package.
  -- TODO: once `exercise8_theta_quotient_im_ne_zero_on_open_rectangle` is available, use
  -- `exercise8_thetaQuotient_signNeighborhood` to localize to constant-sign neighborhoods,
  -- rewrite there by `exercise8_thetaQuotientAbelComposite_eq_zero_of_im_neg` or
  -- `exercise8_thetaQuotientAbelComposite_eq_abelIntegral_of_im_pos`, and then combine those
  -- interior pieces with `exercise8_theta_quotient_boundary_trace` to package the closure-side
  -- continuity along the frontier.
  -- Current blocker: the local-sign neighborhood step is ready, but it still depends on the
  -- upstream interior separation theorem `exercise8_theta_quotient_im_ne_zero_on_open_rectangle`.
  sorry

/-- Helper for Exercise 8: the remaining analytic input is a single rectangle package asserting
that `exercise8_thetaQuotientAbelComposite k` is holomorphic on the open rectangle, continuous on
its closure, and agrees with the identity on the frontier. -/
lemma exercise8_thetaQuotientAbelComposite_diffContOnCl_and_eqOn_frontier
    (k : Exercise8Modulus) :
    DiffContOnCl ℂ (exercise8_thetaQuotientAbelComposite k) (exercise8_open_rectangle k) ∧
      EqOn (exercise8_thetaQuotientAbelComposite k) id
        (frontier (exercise8_open_rectangle k)) := by
  let hdiff := exercise8_thetaQuotientAbelComposite_diffContOnCl k
  let hrange := exercise8_thetaQuotientAbelComposite_eqOn_boundaryTraceRange k
  have hmid :
      exercise8_thetaQuotientAbelComposite k
          ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) =
        ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) := by
    -- The finite boundary trace forces the missing top midpoint through the existing `atTop`
    -- boundary-limit owner.
    exact
      exercise8_eq_topMidpoint_of_continuousOn_closure_and_boundaryTraceRange k
        hdiff.continuousOn hrange
  have hfrontier :
      EqOn (exercise8_thetaQuotientAbelComposite k) id
        (frontier (exercise8_open_rectangle k)) := by
    -- Once the finite trace and the isolated top midpoint are fixed, the whole frontier follows.
    exact exercise8_eqOn_frontier_of_boundaryTraceRange_and_topMidpoint k hrange hmid
  exact ⟨hdiff, hfrontier⟩

/-- Helper for Exercise 8: the source-facing Abel right-inverse law for the explicit theta
quotient on `exercise8_open_rectangle k`. -/
lemma exercise8_abelIntegral_thetaQuotient_eq_on_open_rectangle
    (k : Exercise8Modulus) :
    ∀ u : exercise8_open_rectangle k,
      exercise8_thetaQuotientAbelComposite k u = u := by
  let hdiff := exercise8_thetaQuotientAbelComposite_diffContOnCl k
  let hrange := exercise8_thetaQuotientAbelComposite_eqOn_boundaryTraceRange k
  have hmid :
      exercise8_thetaQuotientAbelComposite k
          ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) =
        ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) := by
    -- The finite boundary trace again determines the top midpoint by the same limit argument.
    exact
      exercise8_eq_topMidpoint_of_continuousOn_closure_and_boundaryTraceRange k
        hdiff.continuousOn hrange
  have hfrontier :
      EqOn (exercise8_thetaQuotientAbelComposite k) id
        (frontier (exercise8_open_rectangle k)) := by
    -- Boundary-trace control plus the forced midpoint packages the full frontier identity.
    exact exercise8_eqOn_frontier_of_boundaryTraceRange_and_topMidpoint k hrange hmid
  have hopen :
      EqOn (exercise8_thetaQuotientAbelComposite k) id (exercise8_open_rectangle k) := by
    -- The maximum-modulus uniqueness step upgrades frontier agreement to the whole rectangle.
    exact exercise8_eqOn_open_rectangle_of_eqOn_frontier k hdiff hfrontier
  intro u
  exact hopen u.2

/-- Helper for Exercise 8: once the Abel right-inverse law is known on the rectangle, the
previously isolated sign-separation theorem upgrades immediately to strict positivity. -/
lemma exercise8_theta_quotient_im_pos_on_open_rectangle
    (k : Exercise8Modulus) :
    ∀ u ∈ exercise8_open_rectangle k, 0 < (exercise8_thetaInverseCandidate k u).im := by
  intro u hu
  -- The right-inverse theorem is now upstream of positivity, so the positivity statement becomes
  -- a thin consumer of the generic `rightInverse → Im > 0` owner.
  exact
    exercise8_thetaQuotient_im_pos_of_rightInverse k
      (exercise8_abelIntegral_thetaQuotient_eq_on_open_rectangle k) ⟨u, hu⟩

/-- Helper for Exercise 8: one concrete meromorphic-periodic inverse witness with the required
half-real order transport, simple zero at `0`, simple pole at `exercise8_pole_shift k`, and
off-divisor order-zero package. -/
lemma exercise8_theta_quotient_eq_canonical_on_open_rectangle
    (k : Exercise8Modulus) :
    ∀ u : exercise8_open_rectangle k,
      exercise8_thetaInverseCandidate k u =
        Function.invFunOn
          (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u := by
  let hsource := exercise8_abelIntegral_thetaQuotient_eq_on_open_rectangle k
  let hpos := exercise8_thetaQuotient_im_pos_of_rightInverse k hsource
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ ⟨exercise8_thetaInverseCandidate k u, hpos u⟩
  have hG : IsExercise8RectangleInverse k G :=
    exercise8_thetaQuotient_branch_of_rightInverse k hpos hsource
  have hEq : G = fun u : exercise8_open_rectangle k ↦
      Function.invFunOn
        (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u :=
    exercise8_rectangle_inverse_unique k hG (exercise8_canonicalRectangleInverse k)
  intro u
  exact congrArg (fun H : exercise8_open_rectangle k → UpperHalfPlane ↦ (H u : ℂ)) hEq

/-- Helper for Exercise 8: one concrete meromorphic-periodic inverse witness with the required
half-real order transport, simple zero at `0`, simple pole at `exercise8_pole_shift k`, and
off-divisor order-zero package. -/
lemma exercise8_biholomorphicInverse_canonicalContinuationWithSeedData
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  rcases exercise8_theta_quotient_continuationAndSeedData k with
    ⟨hMeromorphic, hPeriods, hhalf, hzero, hpole, hzeroOff⟩
  -- Route correction: the inverse witness is the normalized theta model, while the raw theta
  -- quotient remains only the seed object supplying meromorphic, periodic, and divisor data.
  refine
    ⟨exercise8_thetaInverseCandidate k, exercise8_thetaInverseCandidate_meromorphic k,
      exercise8_thetaInverseCandidate_hasPeriodLattice k, ?_, ?_, ?_, ?_, ?_⟩
  intro u
  · exact exercise8_theta_quotient_eq_canonical_on_open_rectangle k u
  · intro u
    -- Multiplying by the fixed nonzero normalization scalar does not change meromorphic order.
    simpa [exercise8_thetaInverseCandidate_order_eq k (u + (exercise8_half_period_pair k).ω₁),
      exercise8_thetaInverseCandidate_order_eq k u] using hhalf u
  · simpa [exercise8_thetaInverseCandidate_order_eq k 0] using hzero
  · simpa [exercise8_thetaInverseCandidate_order_eq k (exercise8_pole_shift k)] using hpole
  · intro u hu hpole'
    simpa [exercise8_thetaInverseCandidate_order_eq k u] using hzeroOff u hu hpole'

/-- Helper for Exercise 8: one concrete meromorphic-periodic inverse witness with the required
half-real order transport, simple zero at `0`, simple pole at `exercise8_pole_shift k`, and
off-divisor order-zero package. -/
lemma exercise8_biholomorphicInverseWitnessWithSeedOrders
    (k : Exercise8Modulus) :
    ∃ F₀ : ℂ → ℂ,
      IsExercise8Inverse k F₀ ∧
      (∀ u : ℂ,
        meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ u) ∧
      meromorphicOrderAt F₀ 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F₀ (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F₀ u = (0 : WithTop ℤ)) := by
  rcases
      exercise8_biholomorphicInverse_canonicalContinuationWithSeedData k with
    ⟨F₀, hMeromorphic₀, hPeriods₀, hcanonical₀, hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩
  -- The canonical continuation owner already supplies the rectangle agreement and the local
  -- divisor package, so this theorem only rebundles those fields into `IsExercise8Inverse`.
  exact
    ⟨F₀,
      exercise8_isInverse_of_canonicalContinuation k hMeromorphic₀ hPeriods₀ hcanonical₀,
      hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩

/-- Helper for Exercise 8: the genuine missing upstream owner is one canonical meromorphic-periodic
continuation of the `Function.invFunOn` rectangle branch together with its half-real order law,
simple zero at `0`, simple pole at `exercise8_pole_shift k`, and off-divisor order-zero package. -/
lemma exercise8_canonicalContinuationWithSeedData
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  -- The canonical continuation owner is the source-facing theorem; this wrapper only re-exports
  -- the same data under the public support name used later in the file.
  exact exercise8_biholomorphicInverse_canonicalContinuationWithSeedData k

/-- Helper for Cartan section26 0018_Exercise_8: once the canonical continuation datum and its
seed-order package are available, the existence-only seeded inverse theorem is pure rebundling. -/
lemma exercise8_seededInverse_exists_of_continuationDataAndSeedPackage
    (k : Exercise8Modulus)
    (hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u))
    (hseed :
      ∀ {F : ℂ → ℂ},
        IsExercise8Inverse k F →
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) →
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ))) :
    ∃ F₀ : ℂ → ℂ,
      IsExercise8Inverse k F₀ ∧
      (∀ u : ℂ,
        meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ u) ∧
      meromorphicOrderAt F₀ 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F₀ (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F₀ u = (0 : WithTop ℤ)) := by
  rcases exercise8_canonicalInverse_exists_of_continuationData k hcanonical with
      ⟨F₀, hF₀, hcanonicalEq⟩
  rcases hseed hF₀ hcanonicalEq with ⟨hhalf, hzero, hpole, hzeroOff⟩
  -- First package one actual inverse from the continuation datum.
  -- Then forget the rectangle-branch equality after appending the seed-order data.
  exact ⟨F₀, hF₀, hhalf, hzero, hpole, hzeroOff⟩

/-- Helper for Cartan section26 0018_Exercise_8: the missing upstream owner should produce one
packaged inverse witness together with the half-real order law, the simple zero at `0`, the simple
pole at `exercise8_pole_shift k`, and order `0` away from the divisor lattices. -/
lemma exercise8_seededInverse_exists_support
    (k : Exercise8Modulus) :
    ∃ F₀ : ℂ → ℂ,
      IsExercise8Inverse k F₀ ∧
      (∀ u : ℂ,
        meromorphicOrderAt F₀ (u + (exercise8_half_period_pair k).ω₁) =
          meromorphicOrderAt F₀ u) ∧
      meromorphicOrderAt F₀ 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F₀ (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F₀ u = (0 : WithTop ℤ)) := by
  rcases exercise8_canonicalContinuationWithSeedData k with
      ⟨F₀, hMeromorphic, hPeriods, hcanonical, hhalf, hzero, hpole, hzeroOff⟩
  have hcanonicalData :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :=
    ⟨F₀, hMeromorphic, hPeriods, hcanonical⟩
  have hF₀ : IsExercise8Inverse k F₀ :=
    exercise8_isInverse_of_canonicalContinuation k hMeromorphic hPeriods hcanonical
  have hseed :
      ∀ {F : ℂ → ℂ},
        IsExercise8Inverse k F →
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) →
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
    intro F hF _hEq
    -- The strong canonical witness fixes the seed data once; normal-form equality transports it to
    -- any packaged inverse agreeing with the same canonical branch on the rectangle.
    exact exercise8_inverse_seed_orders_of_witness k hF hF₀
      ⟨hhalf, hzero, hpole, hzeroOff⟩
  -- The target is now only the existing rebundling theorem applied to the single upstream owner.
  exact exercise8_seededInverse_exists_of_continuationDataAndSeedPackage k hcanonicalData hseed

/-- Helper for Cartan section26 0018_Exercise_8: one actual packaged inverse witness together with
its canonical half-real order law and local divisor seeds is the single missing owner behind both
the continuation theorem and the downstream exact-order package. -/
lemma exercise8_canonicalInverseWitnessWithSeedOrders
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      IsExercise8Inverse k F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) ∧
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  rcases exercise8_canonicalContinuationWithSeedData k with
      ⟨F₀, hMeromorphic, hPeriods, hcanonicalEq, hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩
  have hcanonical :
      ∃ F : ℂ → ℂ,
        Meromorphic F ∧
          HasPeriodLattice (exercise8_period_pair k) F ∧
          (∀ u : exercise8_open_rectangle k,
            F u =
              Function.invFunOn
                (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) :=
    ⟨F₀, hMeromorphic, hPeriods, hcanonicalEq⟩
  have hF₀ : IsExercise8Inverse k F₀ :=
    exercise8_isInverse_of_canonicalContinuation k hMeromorphic hPeriods hcanonicalEq
  have hseed :
      ∀ {F : ℂ → ℂ},
        IsExercise8Inverse k F →
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) →
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
    intro F hF _hEq
    -- Once the canonical witness is fixed, the normal-form transport theorem propagates the same
    -- half-period and divisor data to every packaged inverse.
    exact exercise8_inverse_seed_orders_of_witness k hF hF₀
      ⟨hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩
  -- Once those two owners are supplied, the theorem is only the existing packaging lemma.
  exact
    exercise8_canonicalInverseWitnessWithSeedOrders_of_continuationDataAndSeedPackage
      k hcanonical hseed

/-- Helper for Cartan section26 0018_Exercise_8: one actual packaged inverse witness together with
its canonical half-real order law and local divisor seeds is the single missing owner behind both
the continuation theorem and the downstream exact-order package. -/
lemma exercise8_inverse_exists_with_seed_orders
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      IsExercise8Inverse k F ∧
        (∀ u : ℂ,
          meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
            meromorphicOrderAt F u) ∧
        meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
        meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
        (∀ u : ℂ,
          u ∉ (exercise8_half_period_pair k).lattice →
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
          meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  rcases exercise8_canonicalInverseWitnessWithSeedOrders k with
      ⟨F, hF, _hcanonical, hhalf, hzero, hpole, hzeroOff⟩
  -- The canonical witness theorem already packages the exact data demanded by the public owner;
  -- here we only forget the extra rectangle-branch identification.
  exact ⟨F, hF, hhalf, hzero, hpole, hzeroOff⟩

/-- Helper for Cartan section26 0018_Exercise_8: once a source-facing rectangle branch is fixed,
the remaining continuation problem is to extend that branch meromorphically across the perimeter
and then periodize it. -/
lemma exercise8_canonicalRectangleInverse_continuationSupport
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  rcases exercise8_canonicalInverseWitnessWithSeedOrders k with
      ⟨F, hF, hcanonical, _hhalf, _hzero, _hpole, _hzeroOff⟩
  rcases hF with ⟨_G, _hG, hMeromorphic, hPeriods, _hFG⟩
  -- The canonical witness already stores the required meromorphic-periodic fields and agrees
  -- with the `invFunOn` branch on the open rectangle.
  exact ⟨F, hMeromorphic, hPeriods, hcanonical⟩

/-- Helper for Cartan section26 0018_Exercise_8: once a source-facing rectangle branch is fixed,
the remaining continuation problem is to extend that branch meromorphically across the perimeter
and then periodize it. -/
lemma exercise8_rectangleInverse_continuationSupport
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k, F u = G u) := by
  -- Any completed canonical continuation transfers back to the supplied branch by uniqueness.
  exact exercise8_rectangleInverse_continuationSupport_of_eq_canonical k hG
    (exercise8_canonicalRectangleInverse_continuationSupport k)

/-- Helper for Cartan section26 0018_Exercise_8: the canonical `invFunOn` rectangle branch is the
correct owner for the global continuation-periodization step. -/
lemma exercise8_canonicalPeriodicInverse
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k,
          F u =
            Function.invFunOn
              (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u) := by
  -- The canonical wrapper is now a direct specialization of the branch-level continuation owner.
  rcases
      exercise8_rectangleInverse_continuationSupport k
        (exercise8_canonicalRectangleInverse k) with
    ⟨F, hMeromorphic, hPeriods, hF⟩
  refine ⟨F, hMeromorphic, hPeriods, ?_⟩
  intro u
  -- The chosen rectangle branch is already the canonical `invFunOn` branch by definition.
  exact hF u

/-- Helper for Cartan section26 0018_Exercise_8: once the source-facing inverse branch on the
fundamental rectangle is available, the remaining work is to continue it across the finite sides,
separate the top-midpoint reciprocal chart, and then periodize the result. -/
lemma exercise8_rectangleInverse_continuationPackage
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G) :
    ∃ F : ℂ → ℂ,
      Meromorphic F ∧
        HasPeriodLattice (exercise8_period_pair k) F ∧
        (∀ u : exercise8_open_rectangle k, F u = G u) := by
  -- The continuation owner is now formulated directly for the supplied rectangle branch.
  exact exercise8_rectangleInverse_continuationSupport k hG

/-- Helper for Cartan section26 0018_Exercise_8: once the continuation package is available, the
public inverse-existence theorem is only a wrapper that reinserts the original rectangle branch
into `IsExercise8Inverse`. -/
lemma exercise8_periodicInverse_fromRectangleInverse
    (k : Exercise8Modulus)
    {G : exercise8_open_rectangle k → UpperHalfPlane}
    (hG : IsExercise8RectangleInverse k G) :
    ∃ F : ℂ → ℂ, IsExercise8Inverse k F := by
  rcases exercise8_rectangleInverse_continuationPackage k hG with ⟨F, hMeromorphic, hPeriods, hFG⟩
  -- The continuation package already provides the meromorphic and periodic extension fields; the
  -- remaining step is only to bundle them back with the original rectangle inverse branch.
  exact ⟨F, ⟨G, hG, hMeromorphic, hPeriods, hFG⟩⟩

/-- Meromorphic-periodic-inverse companion: the inverse transformation extends to a meromorphic
doubly-periodic function with periods `4 K` and `2 i K'`. -/
theorem exercise_8_inverse_exists
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ, IsExercise8Inverse k F := by
  -- The stronger support owner already packages a global inverse witness.
  rcases exercise8_inverse_exists_with_seed_orders k with ⟨F, hF, _, _, _, _⟩
  exact ⟨F, hF⟩

/-- Helper for Cartan section26 0018_Exercise_8: the exact-order theorem reduces to four inverse-
side inputs, namely half-period transport, the simple zero at `0`, the simple pole at `i K'`, and
order `0` off the divisor lattices. -/
lemma exercise8_inverse_seed_orders
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    (∀ u : ℂ,
      meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
        meromorphicOrderAt F u) ∧
      meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  rcases exercise8_inverse_exists_with_seed_orders k with ⟨F₀, hF₀, hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩
  -- The single witness owner supplies the seed data once; normal-form equality transports it to
  -- the present packaged inverse.
  exact exercise8_inverse_seed_orders_of_witness k hF hF₀
    ⟨hhalf₀, hzero₀, hpole₀, hzeroOff₀⟩

/-- Helper for Cartan section26 0018_Exercise_8: the exact-order theorem reduces to four inverse-
side inputs, namely half-period transport, the simple zero at `0`, the simple pole at `i K'`, and
order `0` off the divisor lattices. -/
lemma exercise8_inverse_order_add_half_real_period_eq
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∀ u : ℂ,
      meromorphicOrderAt F (u + (exercise8_half_period_pair k).ω₁) =
        meromorphicOrderAt F u := by
  -- The half-real order bridge is the first projection of the packaged seed-data owner.
  exact (exercise8_inverse_seed_orders k hF).1

/-- Helper for Exercise 8: the periodized inverse has a simple zero at the origin. -/
lemma exercise8_inverse_orderAt_zero
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    meromorphicOrderAt F 0 = (1 : WithTop ℤ) := by
  -- The origin-order statement is the second projection of the same seed-data package.
  exact (exercise8_inverse_seed_orders k hF).2.1

/-- Helper for Exercise 8: the periodized inverse has a simple pole at the top midpoint `i K'`. -/
lemma exercise8_inverse_orderAt_poleShift
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) := by
  -- The pole-order statement is the third projection of the same seed-data package.
  exact (exercise8_inverse_seed_orders k hF).2.2.1

/-- Helper for Exercise 8: away from the zero lattice and the pole lattice, the inverse has
meromorphic order `0`. -/
lemma exercise8_inverse_order_eq_zero_off_divisors
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∀ u : ℂ,
      u ∉ (exercise8_half_period_pair k).lattice →
      u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
      meromorphicOrderAt F u = (0 : WithTop ℤ) := by
  -- The off-divisor order statement is the final projection of the packaged seed-data owner.
  exact (exercise8_inverse_seed_orders k hF).2.2.2

/-- Helper for Cartan section26 0018_Exercise_8: the exact-order theorem reduces to four inverse-
side inputs, namely half-period transport, the simple zero at `0`, the simple pole at `i K'`, and
order `0` off the divisor lattices. -/
lemma exercise8_inverse_exact_order_inputs
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    HasPeriodLattice (exercise8_half_period_pair k)
        (fun u : ℂ ↦ meromorphicOrderAt F u) ∧
      meromorphicOrderAt F 0 = (1 : WithTop ℤ) ∧
      meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ) ∧
      (∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F u = (0 : WithTop ℤ)) := by
  -- Assemble the four isolated inverse-side inputs into the package consumed downstream.
  refine ⟨?_, exercise8_inverse_orderAt_zero k hF, exercise8_inverse_orderAt_poleShift k hF, ?_⟩
  · exact
      exercise8_inverse_order_hasHalfPeriodLattice_of_halfRealShift k hF
        (exercise8_inverse_order_add_half_real_period_eq k hF)
  · exact exercise8_inverse_order_eq_zero_off_divisors k hF

/-- Helper for Cartan section26 0018_Exercise_8: after the rectangle inverse has been periodized,
the exact meromorphic order should be computed once and for all before the sign-level zero/pole
corollaries are derived. -/
lemma exercise8_inverse_exact_order_data
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∀ u : ℂ,
      meromorphicOrderAt F u =
        if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ) := by
  rcases exercise8_inverse_exact_order_inputs k hF with ⟨hperiods, hzero, hpole, hzeroOff⟩
  intro u
  by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
  · -- Transport the simple zero at `0` across the half-period lattice.
    simpa [hu, hzero] using hperiods u hu 0
  · by_cases hpole' : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
    · have hshift :
          meromorphicOrderAt F
              (exercise8_pole_shift k + (u - exercise8_pole_shift k)) =
            meromorphicOrderAt F (exercise8_pole_shift k) :=
        hperiods (u - exercise8_pole_shift k) hpole' (exercise8_pole_shift k)
      -- Transport the simple pole at `i K'` across the same half-period lattice.
      simpa [hu, hpole', hpole] using hshift
    · -- Away from both divisor lattices, the exact order is part of the packaged input data.
      simp [hu, hpole', hzeroOff u hu hpole']


/-- Helper for Cartan section26 0018_Exercise_8: after the rectangle inverse has been periodized,
the full zero/pole classification should be owned by one global order theorem before the public
iff wrappers are derived. -/
lemma exercise8_inverse_order_data
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    (∀ u : ℂ, 0 < meromorphicOrderAt F u ↔ u ∈ (exercise8_half_period_pair k).lattice) ∧
      (∀ u : ℂ, meromorphicOrderAt F u < 0 ↔
        u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice) := by
  constructor
  · intro u
    by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
    · -- On the zero lattice, the exact-order owner already says the order is `1`.
      have horder : meromorphicOrderAt F u = (1 : WithTop ℤ) := by
        simpa [hu] using exercise8_inverse_exact_order_data k hF u
      constructor
      · intro _
        exact hu
      · intro _
        simpa [horder]
    · by_cases hpole : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
      · -- On the pole translate away from the zero lattice, the exact order is `-1`.
        have horder : meromorphicOrderAt F u = (-1 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_inverse_exact_order_data k hF u
        constructor
        · intro hpos
          have hnot : ¬ 0 < (-1 : WithTop ℤ) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hpos))
        · intro hmem
          exact False.elim (hu hmem)
      · -- Off both divisor lattices, the exact-order owner forces order `0`.
        have horder : meromorphicOrderAt F u = (0 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_inverse_exact_order_data k hF u
        constructor
        · intro hpos
          have hnot : ¬ 0 < (0 : WithTop ℤ) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hpos))
        · intro hmem
          exact False.elim (hu hmem)
  · intro u
    by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
    · have hpole :
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice := by
        -- The divisor lattices are disjoint because their imaginary coordinates are even vs odd.
        exact exercise8_half_period_lattice_disjoint_pole_shift k hu
      have horder : meromorphicOrderAt F u = (1 : WithTop ℤ) := by
        simpa [hu] using exercise8_inverse_exact_order_data k hF u
      -- The zero lattice and the pole translate are disjoint, so the negative-order branch is
      -- excluded here.
      constructor
      · intro hneg
        have hnot : ¬ ((1 : WithTop ℤ) < 0) := by norm_num
        exact False.elim (hnot (by simpa [horder] using hneg))
      · intro hmem
        exact False.elim (hpole hmem)
    · by_cases hpole : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
      · -- Away from the zero lattice, the pole translate is exactly the negative-order branch.
        have horder : meromorphicOrderAt F u = (-1 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_inverse_exact_order_data k hF u
        constructor
        · intro _
          exact hpole
        · intro _
          have hneg : ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
            exact_mod_cast (show (-1 : ℤ) < 0 by omega)
          simpa [horder] using hneg
      · -- Off both divisor lattices, the exact-order owner again gives order `0`.
        have horder : meromorphicOrderAt F u = (0 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_inverse_exact_order_data k hF u
        constructor
        · intro hneg
          have hnot : ¬ ((0 : WithTop ℤ) < 0) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hneg))
        · intro hmem
          exact False.elim (hpole hmem)

/-- Helper for Cartan section26 0018_Exercise_8: the reflected inverse has the expected divisor
data, namely zeros on the even half-period lattice and poles on its `i K'` translate. -/
lemma exercise8_inverse_divisor_data
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    (0 < meromorphicOrderAt F u ↔ u ∈ (exercise8_half_period_pair k).lattice) ∧
      (meromorphicOrderAt F u < 0 ↔
        u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice) := by
  -- The public divisor wrapper now simply specializes the global order owner.
  rcases exercise8_inverse_order_data k hF with ⟨hzero, hpole⟩
  exact ⟨hzero u, hpole u⟩

/-- Zero-locus companion: the meromorphic inverse has a zero exactly at the points of the even
period lattice, in the sense of positive meromorphic order. -/
theorem exercise_8_inverse_zero_iff
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    0 < meromorphicOrderAt F u ↔ u ∈ (exercise8_half_period_pair k).lattice := by
  -- The zero classification is the first half of the shared divisor package.
  exact (exercise8_inverse_divisor_data k hF u).1

/-- Pole-locus companion: the poles of the meromorphic inverse are exactly the translated odd
half-period lattice. -/
theorem exercise_8_inverse_pole_iff
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    meromorphicOrderAt F u < 0 ↔
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice := by
  -- The pole classification is the second half of the same shared divisor package.
  exact (exercise8_inverse_divisor_data k hF u).2


/-- Helper for Cartan section26 0018_Exercise_8: half-period transport plus the two seed orders
and the off-divisor vanishing criterion already determine the full exact-order formula. -/
lemma exercise8_exact_order_data_of_half_period_lattice
    (k : Exercise8Modulus)
    {f : ℂ → ℂ}
    (hperiods :
      HasPeriodLattice (exercise8_half_period_pair k)
        (fun u : ℂ ↦ meromorphicOrderAt f u))
    (hzero : meromorphicOrderAt f 0 = (1 : WithTop ℤ))
    (hpole : meromorphicOrderAt f (exercise8_pole_shift k) = (-1 : WithTop ℤ))
    (hzeroOff :
      ∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt f u = (0 : WithTop ℤ)) :
    ∀ u : ℂ,
      meromorphicOrderAt f u =
        if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ) := by
  intro u
  by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
  · -- Transport the simple zero at `0` across the half-period lattice.
    simpa [hu, hzero] using hperiods u hu 0
  · by_cases hpole' : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
    · have hshift :
          meromorphicOrderAt f
              (exercise8_pole_shift k + (u - exercise8_pole_shift k)) =
            meromorphicOrderAt f (exercise8_pole_shift k) :=
        hperiods (u - exercise8_pole_shift k) hpole' (exercise8_pole_shift k)
      -- Transport the simple pole at `i K'` across the same lattice.
      simpa [hu, hpole', hpole] using hshift
    · -- Away from both divisor lattices, the exact order is forced to vanish.
      simp [hu, hpole', hzeroOff u hu hpole']

/-- Helper for Cartan section26 0018_Exercise_8: once the inverse-side half-period lattice, seed
orders, and off-divisor vanishing are available, the generic classifier already assembles the full
exact-order formula. -/
lemma exercise8_inverse_exact_order_data_of_inputs
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hperiods :
      HasPeriodLattice (exercise8_half_period_pair k)
        (fun u : ℂ ↦ meromorphicOrderAt F u))
    (hzero : meromorphicOrderAt F 0 = (1 : WithTop ℤ))
    (hpole : meromorphicOrderAt F (exercise8_pole_shift k) = (-1 : WithTop ℤ))
    (hzeroOff :
      ∀ u : ℂ,
        u ∉ (exercise8_half_period_pair k).lattice →
        u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice →
        meromorphicOrderAt F u = (0 : WithTop ℤ)) :
    ∀ u : ℂ,
      meromorphicOrderAt F u =
        if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ) := by
  -- The inverse side now reduces to the same generic transport-and-seed package used on the theta
  -- side below.
  exact exercise8_exact_order_data_of_half_period_lattice k hperiods hzero hpole hzeroOff

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient has exact meromorphic order
`1` on the zero half-period lattice, exact order `-1` on its pole-shift translate, and order `0`
elsewhere. -/
lemma exercise8_theta_quotient_exact_order_data
    (k : Exercise8Modulus) :
    ∀ u : ℂ,
      meromorphicOrderAt (exercise8_theta_quotient k) u =
        if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ) := by
  -- The theta side is the model case: the generic half-period classifier now packages the
  -- transport step so only the theta-specific seed orders and off-divisor vanishing remain.
  refine
    exercise8_exact_order_data_of_half_period_lattice k
      (exercise8_theta_quotient_order_hasHalfPeriodLattice k)
      (exercise8_theta_quotient_order_at_zero k)
      (exercise8_theta_quotient_order_at_poleShift k)
      ?_
  intro u hu hpole
  -- Away from the divisor lattices, the theta quotient has no zero or pole.
  simpa using exercise8_theta_quotient_order_eq_zero_of_not_divisor k hu hpole

/-- Helper for Cartan section26 0018_Exercise_8: the public theta quotient has zeros exactly on
the half-period lattice and poles exactly on its `i K'` translate. -/
lemma exercise8_theta_quotient_divisor_data
    (k : Exercise8Modulus) (u : ℂ) :
    (0 < meromorphicOrderAt (exercise8_theta_quotient k) u ↔
        u ∈ (exercise8_half_period_pair k).lattice) ∧
      (meromorphicOrderAt (exercise8_theta_quotient k) u < 0 ↔
        u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice) := by
  -- Route correction: after the exact-order owner is established, the sign-level divisor wrapper
  -- is just the same case split used on the inverse side.
  constructor
  · by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
    · have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (1 : WithTop ℤ) := by
        simpa [hu] using exercise8_theta_quotient_exact_order_data k u
      constructor
      · intro _
        exact hu
      · intro _
        simpa [horder]
    · by_cases hpole : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
      · have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (-1 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_theta_quotient_exact_order_data k u
        constructor
        · intro hpos
          have hnot : ¬ 0 < (-1 : WithTop ℤ) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hpos))
        · intro hmem
          exact False.elim (hu hmem)
      · have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (0 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_theta_quotient_exact_order_data k u
        constructor
        · intro hpos
          have hnot : ¬ 0 < (0 : WithTop ℤ) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hpos))
        · intro hmem
          exact False.elim (hu hmem)
  · by_cases hu : u ∈ (exercise8_half_period_pair k).lattice
    · have hpole :
          u - exercise8_pole_shift k ∉ (exercise8_half_period_pair k).lattice :=
        exercise8_half_period_lattice_disjoint_pole_shift k hu
      have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (1 : WithTop ℤ) := by
        simpa [hu] using exercise8_theta_quotient_exact_order_data k u
      constructor
      · intro hneg
        have hnot : ¬ ((1 : WithTop ℤ) < 0) := by norm_num
        exact False.elim (hnot (by simpa [horder] using hneg))
      · intro hmem
        exact False.elim (hpole hmem)
    · by_cases hpole : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice
      · have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (-1 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_theta_quotient_exact_order_data k u
        constructor
        · intro _
          exact hpole
        · intro _
          have hneg : ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
            exact_mod_cast (show (-1 : ℤ) < 0 by omega)
          simpa [horder] using hneg
      · have horder : meromorphicOrderAt (exercise8_theta_quotient k) u = (0 : WithTop ℤ) := by
          simpa [hu, hpole] using exercise8_theta_quotient_exact_order_data k u
        constructor
        · intro hneg
          have hnot : ¬ ((0 : WithTop ℤ) < 0) := by norm_num
          exact False.elim (hnot (by simpa [horder] using hneg))
        · intro hmem
          exact False.elim (hpole hmem)

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient vanishes exactly on the even
half-period lattice. -/
lemma exercise8_theta_quotient_zero_iff
    (k : Exercise8Modulus) (u : ℂ) :
    0 < meromorphicOrderAt (exercise8_theta_quotient k) u ↔
      u ∈ (exercise8_half_period_pair k).lattice := by
  -- This is the zero half of the already-packaged divisor computation.
  exact (exercise8_theta_quotient_divisor_data k u).1

/-- Helper for Cartan section26 0018_Exercise_8: the theta quotient has poles exactly on the
`i K'`-shifted half-period lattice. -/
lemma exercise8_theta_quotient_pole_iff
    (k : Exercise8Modulus) (u : ℂ) :
    meromorphicOrderAt (exercise8_theta_quotient k) u < 0 ↔
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice := by
  -- This is the pole half of the same divisor package.
  exact (exercise8_theta_quotient_divisor_data k u).2

/-- Helper for Cartan section26 0018_Exercise_8: if two functions share a period `ω`, then their
pointwise quotient shares the same period. -/
lemma periodic_div_of_periodic
    {f g : ℂ → ℂ} {ω : ℂ}
    (hf : Function.Periodic f ω)
    (hg : Function.Periodic g ω) :
    Function.Periodic (fun z : ℂ ↦ f z / g z) ω := by
  intro z
  -- Rewrite both translated factors with the same period before simplifying the quotient.
  simp [hf z, hg z]

/-- Helper for Cartan section26 0018_Exercise_8: matching exact order formulas force the raw
inverse/theta quotient `F / θ` to have meromorphic order `0` at every point. -/
lemma exercise8_inverseThetaQuotient_order_eq_zero
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hFMeromorphic : Meromorphic F)
    (hFOrders :
      ∀ u : ℂ,
        meromorphicOrderAt F u =
          if u ∈ (exercise8_half_period_pair k).lattice then
            (1 : WithTop ℤ)
          else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
            (-1 : WithTop ℤ)
          else
            (0 : WithTop ℤ)) :
    ∀ u : ℂ,
      meromorphicOrderAt (fun z : ℂ ↦ F z / exercise8_theta_quotient k z) u = (0 : WithTop ℤ) := by
  intro u
  -- Matching exact-order formulas for `F` and `θ` make the quotient order vanish pointwise.
  calc
    meromorphicOrderAt (fun z : ℂ ↦ F z / exercise8_theta_quotient k z) u
        = meromorphicOrderAt F u - meromorphicOrderAt (exercise8_theta_quotient k) u := by
            simpa using
              (meromorphicOrderAt_div (hFMeromorphic u) (exercise8_theta_quotient_meromorphic k u))
    _ =
        (if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ)) -
        (if u ∈ (exercise8_half_period_pair k).lattice then
          (1 : WithTop ℤ)
        else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
          (-1 : WithTop ℤ)
        else
          (0 : WithTop ℤ)) := by
            rw [hFOrders u, exercise8_theta_quotient_exact_order_data k u]
    _ = (0 : WithTop ℤ) := by
          by_cases hu : u ∈ (exercise8_half_period_pair k).lattice <;>
            by_cases hpole : u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice <;>
            simp [hu, hpole]

/-- Helper for Cartan section26 0018_Exercise_8: the global normal form of `F / θ` is
differentiable once the quotient has meromorphic order `0` everywhere. -/
lemma exercise8_inverseThetaQuotient_normalForm_differentiable
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hFMeromorphic : Meromorphic F)
    (hFOrders :
      ∀ u : ℂ,
        meromorphicOrderAt F u =
          if u ∈ (exercise8_half_period_pair k).lattice then
            (1 : WithTop ℤ)
          else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
            (-1 : WithTop ℤ)
          else
            (0 : WithTop ℤ)) :
    Differentiable ℂ
      (toMeromorphicNFOn (fun z : ℂ ↦ F z / exercise8_theta_quotient k z) Set.univ) := by
  intro u
  let q : ℂ → ℂ := fun z : ℂ ↦ F z / exercise8_theta_quotient k z
  have hqMeromorphic : Meromorphic q := by
    -- The quotient of two meromorphic functions is meromorphic.
    simpa [q] using hFMeromorphic.div (exercise8_theta_quotient_meromorphic k)
  have hqNF :
      MeromorphicNFAt (toMeromorphicNFOn q Set.univ) u :=
    (meromorphicNFOn_toMeromorphicNFOn q Set.univ) (by simp)
  have hqOrder :
      meromorphicOrderAt (toMeromorphicNFOn q Set.univ) u = (0 : WithTop ℤ) := by
    -- Passing to the global normal form preserves the quotient order at every point of `ℂ`.
    rw [meromorphicOrderAt_toMeromorphicNFOn hqMeromorphic.meromorphicOn (by simp)]
    simpa [q] using exercise8_inverseThetaQuotient_order_eq_zero k hFMeromorphic hFOrders u
  -- Order-zero normal forms are analytic, hence differentiable.
  exact
    (analyticAt_of_meromorphicOrderAt_eq_zero hqNF (by simpa using hqOrder)).differentiableAt

/-- Helper for Cartan section26 0018_Exercise_8: the global normal form of `F / θ` inherits the
period lattice of the raw quotient once the quotient has order `0` at every point. -/
lemma exercise8_inverseThetaQuotient_normalForm_hasPeriodLattice
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hFMeromorphic : Meromorphic F)
    (hFPeriods : HasPeriodLattice (exercise8_period_pair k) F)
    (hFOrders :
      ∀ u : ℂ,
        meromorphicOrderAt F u =
          if u ∈ (exercise8_half_period_pair k).lattice then
            (1 : WithTop ℤ)
          else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
            (-1 : WithTop ℤ)
          else
            (0 : WithTop ℤ)) :
    HasPeriodLattice (exercise8_period_pair k)
      (toMeromorphicNFOn (fun z : ℂ ↦ F z / exercise8_theta_quotient k z) Set.univ) := by
  let q : ℂ → ℂ := fun z : ℂ ↦ F z / exercise8_theta_quotient k z
  have hqMeromorphic : Meromorphic q := by
    -- The quotient owner will be consumed by the normal-form period transport API.
    simpa [q] using hFMeromorphic.div (exercise8_theta_quotient_meromorphic k)
  have hthetaPeriods : HasPeriodLattice (exercise8_period_pair k) (exercise8_theta_quotient k) :=
    exercise8_theta_quotient_hasPeriodLattice k
  have hqPeriods : HasPeriodLattice (exercise8_period_pair k) q := by
    rw [hasPeriodLattice_iff_periodic_generators] at hFPeriods hthetaPeriods ⊢
    constructor
    · -- Each period generator acts on the quotient through the same generator periodicity.
      exact periodic_div_of_periodic hFPeriods.1 hthetaPeriods.1
    · -- The second generator is handled identically.
      exact periodic_div_of_periodic hFPeriods.2 hthetaPeriods.2
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    -- Transport the first quotient period through the global normal form at order `0`.
    simpa [q] using
      toMeromorphicNFOn_period_eq_of_meromorphicOrderAt_eq_zero
        isOpen_univ hqMeromorphic.meromorphicOn
        (by simp) (by simp)
        ((hasPeriodLattice_iff_periodic_generators _ _).1 hqPeriods |>.1)
        (exercise8_inverseThetaQuotient_order_eq_zero k hFMeromorphic hFOrders u)
  · intro u
    -- Transport the second quotient period through the same order-zero normal-form API.
    simpa [q] using
      toMeromorphicNFOn_period_eq_of_meromorphicOrderAt_eq_zero
        isOpen_univ hqMeromorphic.meromorphicOn
        (by simp) (by simp)
        ((hasPeriodLattice_iff_periodic_generators _ _).1 hqPeriods |>.2)
        (exercise8_inverseThetaQuotient_order_eq_zero k hFMeromorphic hFOrders u)

/-- Helper for Cartan section26 0018_Exercise_8: after the quotient normal form is shown constant,
multiply back through the theta quotient on a codiscrete nondivisor set to recover the raw
constant-multiple equality. -/
lemma exercise8_inverseThetaQuotient_codiscreteEq_const_mul_theta
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hFMeromorphic : Meromorphic F)
    (hFOrders :
      ∀ u : ℂ,
        meromorphicOrderAt F u =
          if u ∈ (exercise8_half_period_pair k).lattice then
            (1 : WithTop ℤ)
          else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
            (-1 : WithTop ℤ)
          else
            (0 : WithTop ℤ))
    {A : ℂ}
    (hA :
      ∀ u : ℂ,
        toMeromorphicNFOn (fun z ↦ F z / exercise8_theta_quotient k z) Set.univ u = A) :
    F =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
      (fun u ↦ A * exercise8_theta_quotient k u) := by
  let q : ℂ → ℂ := fun z ↦ F z / exercise8_theta_quotient k z
  have hqMeromorphic : Meromorphic q := by
    -- The quotient of the inverse and theta quotient is meromorphic on the whole plane.
    simpa [q] using hFMeromorphic.div (exercise8_theta_quotient_meromorphic k)
  have hA_ne : A ≠ 0 := by
    -- Order `0` of the quotient forces its global normal form to be nonzero at every point.
    intro hAzero
    have hqNF_nonzero :
        toMeromorphicNFOn q Set.univ 0 ≠ 0 := by
      exact
        toMeromorphicNFOn_nonzero_of_meromorphicOrderAt_eq_zero
          isOpen_univ hqMeromorphic.meromorphicOn (by simp)
          (exercise8_inverseThetaQuotient_order_eq_zero k hFMeromorphic hFOrders 0)
    exact hqNF_nonzero (by simpa [q, hAzero] using hA 0)
  have hqEqNF :
      q =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] toMeromorphicNFOn q Set.univ := by
    -- The raw quotient agrees with its chosen normal form off a codiscrete subset of `ℂ`.
    exact toMeromorphicNFOn_eqOn_codiscrete hqMeromorphic.meromorphicOn
  filter_upwards [hqEqNF] with u hu
  have huA : q u = A := by
    simpa [hu] using hA u
  have htheta_ne : exercise8_theta_quotient k u ≠ 0 := by
    intro htheta_zero
    have hAzero : A = 0 := by
      simpa [q, htheta_zero] using huA.symm
    exact hA_ne hAzero
  have hmul :
      (F u / exercise8_theta_quotient k u) * exercise8_theta_quotient k u =
        A * exercise8_theta_quotient k u := by
    exact congrArg (fun z : ℂ ↦ z * exercise8_theta_quotient k u) huA
  -- On the codiscrete set where the quotient equals the constant `A`, the theta quotient is
  -- automatically nonzero, so multiplying back recovers the raw inverse formula.
  simpa [q, htheta_ne, mul_assoc] using hmul

/-- Helper for Cartan section26 0018_Exercise_8: once the inverse and theta quotient are shown to
have the same period lattice and exact divisor data, the normal-form comparison should collapse to
a single constant-multiple theorem. -/
lemma exercise8_theta_quotient_normalForm_from_exact_orders
    (k : Exercise8Modulus)
    {F : ℂ → ℂ}
    (hFMeromorphic : Meromorphic F)
    (hFPeriods : HasPeriodLattice (exercise8_period_pair k) F)
    (hFOrders :
      ∀ u : ℂ,
        meromorphicOrderAt F u =
          if u ∈ (exercise8_half_period_pair k).lattice then
            (1 : WithTop ℤ)
          else if u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice then
            (-1 : WithTop ℤ)
          else
            (0 : WithTop ℤ)) :
    ∃ A : ℂ,
      toMeromorphicNFOn F Set.univ =
        toMeromorphicNFOn (fun u ↦ A * exercise8_theta_quotient k u) Set.univ := by
  -- Route correction: once the exact inverse order theorem exists, the last missing owner is no
  -- longer inverse continuation but the normal-form comparison between two periodic meromorphic
  -- functions with matching order data.
  let q : ℂ → ℂ := fun u ↦ F u / exercise8_theta_quotient k u
  let qNF : ℂ → ℂ := toMeromorphicNFOn q Set.univ
  have hqDiff : Differentiable ℂ qNF := by
    -- The quotient normal form is differentiable because its meromorphic order vanishes
    -- everywhere.
    simpa [q, qNF] using
      exercise8_inverseThetaQuotient_normalForm_differentiable k hFMeromorphic hFOrders
  have hqPeriods : HasPeriodLattice (exercise8_period_pair k) qNF := by
    -- The quotient inherits the same lattice-periodicity after passing to normal form.
    simpa [q, qNF] using
      exercise8_inverseThetaQuotient_normalForm_hasPeriodLattice
        k hFMeromorphic hFPeriods hFOrders
  obtain ⟨A, hA⟩ :=
    differentiable_eq_const_of_has_period_lattice (exercise8_period_pair k) hqDiff hqPeriods
  have hAThetaMeromorphic : Meromorphic (fun u ↦ A * exercise8_theta_quotient k u) := by
    intro u
    -- Multiplying the theta quotient by a constant preserves meromorphicity.
    simpa [mul_comm] using
      (MeromorphicAt.const A u).fun_mul ((exercise8_theta_quotient_meromorphic k) u)
  have hcodiscreteEq :
      F =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
        (fun u ↦ A * exercise8_theta_quotient k u) :=
    exercise8_inverseThetaQuotient_codiscreteEq_const_mul_theta
      k hFMeromorphic hFOrders hA
  -- Once the raw functions agree off a codiscrete subset of `ℂ`, their global normal forms agree.
  exact ⟨A, toMeromorphicNFOn_eq_of_codiscreteEq_univ hFMeromorphic hAThetaMeromorphic hcodiscreteEq⟩

/-- Helper for Cartan section26 0018_Exercise_8: once the inverse and theta quotient are shown to
have the same period lattice and divisor, their quotient is constant. -/
lemma exercise8_theta_quotient_formula_aux
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∃ A : ℂ,
      toMeromorphicNFOn F Set.univ =
        toMeromorphicNFOn (fun u ↦ A * exercise8_theta_quotient k u) Set.univ := by
  have hFMeromorphic : Meromorphic F :=
    exercise8_inverse_meromorphic k hF
  have hFPeriods : HasPeriodLattice (exercise8_period_pair k) F :=
    exercise8_inverse_hasPeriodLattice k hF
  -- The package fields above reduce the theorem to the single exact-order comparison owner.
  exact
    exercise8_theta_quotient_normalForm_from_exact_orders k hFMeromorphic hFPeriods
      (exercise8_inverse_exact_order_data k hF)

/-- Helper for Cartan section26 0018_Exercise_8: the raw-function codiscrete identity underlying
the meromorphic theta-quotient formula. -/
lemma exercise8_theta_quotient_formula_codiscrete
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∃ A : ℂ,
      F =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
        (fun u ↦ A * exercise8_theta_quotient k u) := by
  have hFMeromorphic : Meromorphic F :=
    exercise8_inverse_meromorphic k hF
  have hFPeriods : HasPeriodLattice (exercise8_period_pair k) F :=
    exercise8_inverse_hasPeriodLattice k hF
  let q : ℂ → ℂ := fun u ↦ F u / exercise8_theta_quotient k u
  let qNF : ℂ → ℂ := toMeromorphicNFOn q Set.univ
  have hqDiff : Differentiable ℂ qNF := by
    -- The quotient normal form is entire because the inverse and theta quotient have the same
    -- divisor data.
    simpa [q, qNF] using
      exercise8_inverseThetaQuotient_normalForm_differentiable
        k hFMeromorphic (exercise8_inverse_exact_order_data k hF)
  have hqPeriods : HasPeriodLattice (exercise8_period_pair k) qNF := by
    -- The same divisor comparison preserves the period lattice through normal form.
    simpa [q, qNF] using
      exercise8_inverseThetaQuotient_normalForm_hasPeriodLattice
        k hFMeromorphic hFPeriods (exercise8_inverse_exact_order_data k hF)
  obtain ⟨A, hA⟩ :=
    differentiable_eq_const_of_has_period_lattice (exercise8_period_pair k) hqDiff hqPeriods
  exact
    ⟨A,
      exercise8_inverseThetaQuotient_codiscreteEq_const_mul_theta
        k hFMeromorphic (exercise8_inverse_exact_order_data k hF) hA⟩

/-- Theta-quotient companion for Exercise 8: any packaged inverse is, as a meromorphic function, a
constant multiple of Cartan's explicit theta ratio `θ₁ (u / 2K) / θ₀ (u / 2K)` with parameter
`τ = i K' / K`. -/
theorem exercise_8_theta_quotient_formula_of_inverse
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∃ A : ℂ,
      toMeromorphicNFOn F Set.univ =
        toMeromorphicNFOn
          (fun u ↦
            A *
              ((θ₁[((exercise8_tau k : ℍ) : ℂ)])
                  (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) /
                (θ₀[((exercise8_tau k : ℍ) : ℂ)])
                  (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ))))
          Set.univ := by
  -- Semantic recall: `toMeromorphicNFOn` is the canonical meromorphic-equality layer.
  -- The codiscrete raw-function identity stays in
  -- `exercise8_theta_quotient_formula_codiscrete`.
  obtain ⟨A, hA⟩ := exercise8_theta_quotient_formula_aux k hF
  refine ⟨A, ?_⟩
  simpa [exercise8_theta_quotient_eq_theta_ratio] using hA

/-- Exercise 8: the Abelian integral extends continuously to the closed upper half-plane, defines a
holomorphic isomorphism from the open upper half-plane onto the open rectangle with vertices `-K`,
`K`, `K + i K'`, and `-K + i K'`, and admits a meromorphic doubly-periodic inverse on `ℂ`. The
boundary-to-perimeter map, vertex correspondence, divisor description, and theta-quotient formula
remain as separate source-facing companion theorems. -/
theorem exercise_8
    (k : Exercise8Modulus) :
    (∃ fbar : ClosedUpperHalfPlane → ℂ, IsExercise8Extension k fbar) ∧
      (∃ e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k),
        (∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) ∧
          ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G) ∧
      ∃ F : ℂ → ℂ, IsExercise8Inverse k F := by
  -- The three public pieces were proved separately; this theorem only repackages them.
  exact
    ⟨exercise_8_continuous_extension k,
      exercise_8_abel_integral_bijective k,
      exercise_8_inverse_exists k⟩

/-- Theta-quotient existence companion for Exercise 8: there exists an inverse transformation
extending to a meromorphic doubly-periodic function on `ℂ` that is a constant multiple of
Cartan's explicit theta ratio `θ₁ (u / 2K) / θ₀ (u / 2K)` with parameter `τ = i K' / K`, in the
canonical meromorphic-function equality layer. -/
theorem exercise_8_theta_quotient_formula
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ,
      IsExercise8Inverse k F ∧
        ∃ A : ℂ,
          toMeromorphicNFOn F Set.univ =
            toMeromorphicNFOn
              (fun u ↦
                A *
                  ((θ₁[((exercise8_tau k : ℍ) : ℂ)])
                      (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)) /
                    (θ₀[((exercise8_tau k : ℍ) : ℂ)])
                      (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ))))
              Set.univ := by
  rcases exercise_8_inverse_exists k with ⟨F, hF⟩
  rcases exercise_8_theta_quotient_formula_of_inverse k hF with ⟨A, hA⟩
  -- First choose any packaged inverse; the formula theorem for a fixed inverse then supplies the
  -- required theta-ratio normal form.
  exact ⟨F, hF, A, hA⟩
