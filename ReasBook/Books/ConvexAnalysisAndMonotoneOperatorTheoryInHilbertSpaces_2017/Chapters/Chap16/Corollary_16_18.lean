import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap12.Definition_12_5
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- Helper for Corollary 16 18: a point in the relative interior of the effective domain is a
continuity point of the finite-valued restriction of `f` to that domain. -/
lemma continuousAtOnEffectiveDomain_of_mem_relativeInterior_effectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx_ri : x ∈ ri (effectiveDomain f)) :
    ContinuousAtOnEffectiveDomain f x := by
  let V : Submodule ℝ H := (_root_.affineSpan ℝ (effectiveDomain f)).direction
  let T : Set V := ((↑) : V → H) ⁻¹' (effectiveDomain f - ({x} : Set H))
  let φ : V →ᵃ[ℝ] H :=
    { toFun := fun v ↦ (v : H) + x
      linear := V.subtype
      map_vadd' := by
        intro p v
        change (((v + p : V) : H) + x) = (v : H) + (((p : V) : H) + x)
        simp [add_assoc] }
  let g : V → ℝ := fun v ↦ (f (φ v) : EReal).toReal
  have hx_dom : x ∈ effectiveDomain f := (Set.mem_relativeInterior_iff.mp hx_ri).1
  have hx_intrinsic : x ∈ intrinsicInterior ℝ (effectiveDomain f) := by
    -- Fact 6.14 identifies the source relative interior with the intrinsic interior.
    rw [← relativeInterior_eq_intrinsicInterior_of_finiteDimensional
      (ConvexOn.convex_effectiveDomain hconv)]
    exact hx_ri
  have hzero_int_T : (0 : V) ∈ interior T := by
    -- Fact 6.14 identifies intrinsic interior with interior in the translated direction chart.
    simpa [V, T] using
      (intrinsicInterior_mem_iff_zero_mem_interior_translated_direction_preimage
        (C := effectiveDomain f) hx_dom).mp hx_intrinsic
  have hconvV : _root_.ConvexOn ℝ (φ ⁻¹' effectiveDomain f) g := by
    -- Restrict the convex real representative of `f` to the translated direction chart.
    simpa [V, φ, g] using
      (ConvexOn.toReal_convexOn_effectiveDomain hconv).comp_affineMap φ
  have hzero_int : (0 : V) ∈ interior (φ ⁻¹' effectiveDomain f) := by
    -- The chart preimage is exactly the translated effective domain.
    simpa [T, φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero_int_T
  have hcontVWithin : ContinuousWithinAt g (interior (φ ⁻¹' effectiveDomain f)) (0 : V) := by
    -- Convex functions are continuous on the interior of their domain in the chart space.
    exact (_root_.ConvexOn.continuousOn_interior hconvV) 0 hzero_int
  have hcontV : ContinuousAt g (0 : V) := by
    -- Interior points give ordinary continuity because the interior is open.
    exact ContinuousWithinAt.continuousAt hcontVWithin (IsOpen.mem_nhds isOpen_interior hzero_int)
  have hyV_mem (y : effectiveDomain f) : y.1 - x ∈ V := by
    -- Every effective-domain point determines a translated direction vector.
    change y.1 - x ∈ (_root_.affineSpan ℝ (effectiveDomain f)).direction
    rw [direction_affineSpan]
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ y.2 hx_dom
  let j : effectiveDomain f → V := fun y ↦ ⟨y.1 - x, hyV_mem y⟩
  have hcontJ : Continuous j := by
    -- The chart map on the effective-domain subtype is continuous.
    exact Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) hyV_mem
  have hjx : j ⟨x, hx_dom⟩ = 0 := by
    -- The base point `x` maps to the chart origin.
    apply Subtype.ext
    simp [j]
  have hcontRestrict :
      ContinuousAt
        ((effectiveDomain f).restrict (fun y : H ↦ (f y : EReal).toReal))
        ⟨x, hx_dom⟩ := by
    -- The restricted function is the chart representative composed with the chart map.
    have hcomp :
        (effectiveDomain f).restrict (fun y : H ↦ (f y : EReal).toReal) = g ∘ j := by
      funext y
      simp [Set.restrict, g, j, φ, sub_eq_add_neg]
    rw [hcomp]
    exact ContinuousAt.comp_of_eq hcontV hcontJ.continuousAt hjx
  refine ⟨hx_dom, ?_⟩
  -- Translate subtype continuity back to continuity within the effective domain.
  exact
    (continuousWithinAt_iff_continuousAt_restrict
      (fun y : H ↦ (f y : EReal).toReal) hx_dom).2 hcontRestrict

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 16 18: a subgradient inequality produces a continuous affine minorant
with the same slope. -/
lemma hasContinuousAffineMinorantWithSlope_of_mem_subdifferential
    (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hu : u ∈ (∂ f) x) :
    HasContinuousAffineMinorantWithSlope f.asEReal u := by
  have hdom : (effectiveDomain f).Nonempty := ConvexOn.nonempty hconv
  have hx_sub : x ∈ SetValuedOperator.dom (∂ f) := by
    -- The chosen subgradient witnesses that `x` lies in the subdifferential domain.
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hx_dom : x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hdom hx_sub
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  rw [mem_subdifferential_iff] at hu
  let η : ℝ := (f x : EReal).toReal - ⟪x, u⟫_ℝ
  refine ⟨η, ?_⟩
  intro y
  have hshift :
      (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) =
        (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
    -- Recenter the affine function from slope/intercept form to the subgradient form at `x`.
    have hshift_real :
        ⟪y, u⟫_ℝ + η = ⟪y - x, u⟫_ℝ + (f x : EReal).toReal := by
      dsimp [η]
      rw [inner_sub_left]
      ring
    calc
      (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) =
          (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) := by
            exact congrArg (fun t : ℝ ↦ (t : EReal)) hshift_real
      _ = (⟪y - x, u⟫_ℝ : EReal) +
            ((((f x : EReal).toReal : ℝ) : EReal)) := by
            rw [EReal.coe_add]
      _ = (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
            rw [EReal.coe_toReal hx_top hx_bot]
  -- The subgradient inequality is exactly the desired affine minorant after the recentering.
  rw [hshift]
  exact hu y

-- Proof sketch: `effectiveDomain f` is nonempty and convex because `f` is convex on its
-- effective domain. Fact 6.14 then gives nonemptiness of the relative interior of this convex set
-- in finite dimension.
/-- Corollary 16 18 (1): clause (i). The relative interior of the effective domain of an
`]-∞,+∞]`-valued function that is convex on its effective domain is nonempty on a
finite-dimensional real Hilbert space. -/
theorem relativeInterior_effectiveDomain_nonempty_of_convexOn
    (hconv : ConvexOn f (effectiveDomain f))
    :
    (ri (effectiveDomain f)).Nonempty := by
  -- Fact 6.14 applies directly to the convex effective domain.
  exact relativeInterior_nonempty_of_finiteDimensional
    (ConvexOn.nonempty hconv) (ConvexOn.convex_effectiveDomain hconv)

-- Proof sketch: Corollary 8.41 yields local Lipschitz control, hence continuity of the finite
-- representative of `f`, at every point of `ri (effectiveDomain f)`. Proposition 16.17 then gives
-- a nonempty subdifferential at each such point.
/-- Corollary 16.18 (2): clause (i). Every point in the relative interior of the effective domain
of a function convex on its effective domain is a subdifferentiability point. -/
theorem relativeInterior_effectiveDomain_subset_subdifferentiabilityDomain_of_convexOn
    (hconv : ConvexOn f (effectiveDomain f))
    :
    ri (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := by
  intro x hx
  have hxcont :
      ContinuousAtOnEffectiveDomain f x :=
    continuousAtOnEffectiveDomain_of_mem_relativeInterior_effectiveDomain f hconv hx
  -- Proposition 16.17(ii) provides a nonempty subdifferential at each continuity point.
  change SubdifferentiableAt f x
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
  exact
    (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain f hconv hxcont).1

-- Proof sketch: by clause (i), choose `x ∈ ri (effectiveDomain f)` together with a subgradient
-- `u ∈ ∂ f x`. The defining subgradient inequality then exhibits the affine map
-- `y ↦ ⟪y, u⟫ + ((f x : EReal).toReal - ⟪x, u⟫)` as a continuous affine minorant of `f`.
/-- Corollary 16.18 (3): clause (ii). An `]-∞,+∞]`-valued function convex on its effective domain
on a finite-dimensional real Hilbert space admits a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_of_convexOn
    (hconv : ConvexOn f (effectiveDomain f))
    :
    ∃ u : H, HasContinuousAffineMinorantWithSlope f.asEReal u := by
  rcases relativeInterior_effectiveDomain_nonempty_of_convexOn f hconv with ⟨x, hx_ri⟩
  have hx_sub :
      SubdifferentiableAt f x :=
    relativeInterior_effectiveDomain_subset_subdifferentiabilityDomain_of_convexOn f hconv hx_ri
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff] at hx_sub
  rcases hx_sub with ⟨u, hu⟩
  -- Use the chosen subgradient to build the affine minorant with slope `u`.
  exact ⟨u, hasContinuousAffineMinorantWithSlope_of_mem_subdifferential f hconv hu⟩

end SubdifferentialContinuity

end ERealFunction
