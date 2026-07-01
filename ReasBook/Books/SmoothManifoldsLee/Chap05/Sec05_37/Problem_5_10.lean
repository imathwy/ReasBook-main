import Mathlib
import SmoothManifoldsLee.Chap04.Sec04_22.Theorem_4_5
import SmoothManifoldsLee.Chap04.Sec04_24.Exercise_4_16
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifoldsLee.Chap05.Sec05_30.Corollary_5_13
import SmoothManifoldsLee.Chap05.Sec05_35.Definition_5_35_extra_4
import SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

noncomputable section

local notation "Plane" => ℝ × ℝ

/-- The subset `M_a ⊆ ℝ²` cut out by the equation `y^2 = x (x - 1) (x - a)`. -/
def problem510Curve (a : ℝ) : Set Plane :=
  { p | p.2 ^ 2 = p.1 * (p.1 - 1) * (p.1 - a) }

-- Proof sketch: unfold `problem510Curve`; membership is exactly the defining equation.
/-- A point `(x,y)` lies in `M_a` exactly when it satisfies `y^2 = x (x - 1) (x - a)`. -/
theorem mem_problem510Curve_iff {a x y : ℝ} :
    (x, y) ∈ problem510Curve a ↔ y ^ 2 = x * (x - 1) * (x - a) := by
  -- This is just the defining predicate of `problem510Curve`.
  rfl

/-- Helper for Problem 5-10: the origin lies on the singular cubic `M_0`. -/
theorem problem510Curve_zero_origin_mem :
    (0 : Plane) ∈ problem510Curve 0 := by
  -- The defining equation is trivial at `(0, 0)`.
  rw [mem_problem510Curve_iff]
  norm_num

/-- Helper for Problem 5-10: the origin is isolated in `M_0`. -/
theorem problem510Curve_zero_isolated :
    ∃ U : Set Plane, IsOpen U ∧ (0 : Plane) ∈ U ∧
      U ∩ problem510Curve 0 = ({0} : Set Plane) := by
  refine ⟨Metric.ball (0 : Plane) (1 / 2 : ℝ), Metric.isOpen_ball, by
    simp [Metric.mem_ball], ?_⟩
  ext p
  constructor
  · rintro ⟨hpball, hpcurve⟩
    have hnorm : ‖p‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hpball
    have hx_abs : |p.1| < (1 / 2 : ℝ) := by
      have hx_norm : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      simpa [Real.norm_eq_abs] using lt_of_le_of_lt hx_norm hnorm
    have hx_le : p.1 - 1 ≤ 0 := by
      have hx_lt_half : p.1 < (1 / 2 : ℝ) := (abs_lt.mp hx_abs).2
      linarith
    have hx_sq_nonneg : 0 ≤ p.1 ^ (2 : ℕ) := sq_nonneg _
    have hy_sq_nonneg : 0 ≤ p.2 ^ (2 : ℕ) := sq_nonneg _
    have hcurve_eq : p.2 ^ (2 : ℕ) = p.1 ^ (2 : ℕ) * (p.1 - 1) := by
      rw [mem_problem510Curve_iff] at hpcurve
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpcurve
    have hprod_nonpos : p.1 ^ (2 : ℕ) * (p.1 - 1) ≤ 0 := by
      nlinarith
    have hy_zero_sq : p.2 ^ (2 : ℕ) = 0 := by
      nlinarith [hy_sq_nonneg, hprod_nonpos, hcurve_eq]
    have hy_zero : p.2 = 0 := by
      nlinarith
    have hx_prod_zero : p.1 ^ (2 : ℕ) * (p.1 - 1) = 0 := by
      simpa [hy_zero] using hcurve_eq
    have hx_zero : p.1 = 0 := by
      rcases mul_eq_zero.mp hx_prod_zero with hx_sq | hx_one
      · nlinarith
      · have : p.1 = 1 := sub_eq_zero.mp hx_one
        have habs : |(1 : ℝ)| < (1 / 2 : ℝ) := by simpa [this] using hx_abs
        norm_num at habs
    ext <;> simp [hx_zero, hy_zero]
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨by simp [Metric.mem_ball], problem510Curve_zero_origin_mem⟩

/-- Helper for Problem 5-10: any immersed-curve inclusion into the plane is continuous. -/
theorem immersed_curve_inclusion_continuous {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)) :
    Continuous (Subtype.val : S → Plane) := by
  -- Route correction: replace the missing Chapter 5 continuity bridge by the pointwise
  -- continuity consequence of immersion from Exercise 4.16.
  rw [continuous_iff_continuousAt]
  intro x
  exact (hImm.isImmersionAt x).continuousAt

/-- Helper for Problem 5-10: the singular cubic `M_0` admits no immersed-curve structure. -/
theorem problem510Curve_zero_no_immersed_curve_structure :
    ¬ (problem510Curve 0).AdmitsImmersedCurveStructure := by
  intro hCurve
  rcases hCurve with ⟨t, hCurve⟩
  let _ : TopologicalSpace (problem510Curve 0) := t
  rcases hCurve with ⟨cs, hs, hImm⟩
  let _ : ChartedSpace ℝ (problem510Curve 0) := cs
  let _ : IsManifold 𝓘(ℝ) ⊤ (problem510Curve 0) := hs
  let p : problem510Curve 0 := ⟨0, problem510Curve_zero_origin_mem⟩
  have hcont : Continuous (Subtype.val : problem510Curve 0 → Plane) :=
    immersed_curve_inclusion_continuous hImm
  have hsingletonOpen : IsOpen ({p} : Set (problem510Curve 0)) := by
    rcases problem510Curve_zero_isolated with ⟨U, hUopen, hpU, hUcap⟩
    have hEq :
        ({p} : Set (problem510Curve 0)) =
          (Subtype.val : problem510Curve 0 → Plane) ⁻¹' U := by
      ext q
      constructor
      · intro hq
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact hpU
      · intro hq
        have hq0 : (q : Plane) = 0 := by
          have hqmem : (q : Plane) ∈ U ∩ problem510Curve 0 := ⟨hq, q.2⟩
          have : (q : Plane) ∈ ({0} : Set Plane) := by
            simpa [hUcap] using hqmem
          simpa using this
        apply Set.mem_singleton_iff.mpr
        exact Subtype.ext hq0
    simpa [hEq] using hUopen.preimage hcont
  let e := chartAt ℝ p
  have hImageOpen : IsOpen ({e p} : Set ℝ) := by
    -- A chart is an open map on its source, so an isolated singleton would map to an open
    -- singleton in `ℝ`.
    have hImageOpenRaw :
        IsOpen (e '' (e.source ∩ ({p} : Set (problem510Curve 0)))) :=
      e.isOpen_image_source_inter hsingletonOpen
    have hSourceSingleton :
        e.source ∩ ({p} : Set (problem510Curve 0)) = ({p} : Set (problem510Curve 0)) := by
      ext q
      constructor
      · rintro ⟨_, hq⟩
        exact hq
      · intro hq
        refine ⟨?_, hq⟩
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact mem_chart_source ℝ p
    simpa [hSourceSingleton] using hImageOpenRaw
  have hImageSingleton : e '' ({p} : Set (problem510Curve 0)) = {e p} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases Set.mem_singleton_iff.mp hq with rfl
      simp
    · intro hx
      refine ⟨p, by simp, ?_⟩
      simpa using hx.symm
  exact not_isOpen_singleton (e p) hImageOpen

/-- Helper for Problem 5-10: the manifold derivative of an open-subset inclusion is an
isomorphism. -/
theorem problem510_mfderiv_open_subset_inclusion_isInvertible
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) [IsManifold I ∞ M] (p : U) :
    (mfderiv I I (Subtype.val : U → M) p).IsInvertible := by
  -- This is the same open-subset inclusion calculation used in the regular-level-set route.
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have hsymm : ContMDiffOn I I 1 e.symm (U : Set M) := by
    intro x hx
    have hcomp : ContMDiffWithinAt I I 1 (Subtype.val ∘ e.symm) (U : Set M) x := by
      refine contMDiffWithinAt_id.congr_of_mem ?_ hx
      intro y hy
      simpa [e] using e.right_inv (by simpa [e] using hy)
    have hiff :
        ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) (Subtype.val ∘ e.symm)
            (U : Set M) x ↔
          ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) e.symm (U : Set M) x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff e.symm (U : Set M) x
    simpa [ContMDiffWithinAt] using
      hiff.mp (by simpa [ContMDiffWithinAt] using hcomp)
  let Φ : PartialDiffeomorph I I U M 1 := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      simpa [e] using
        ((contMDiff_subtype_val : ContMDiff I I 1 (Subtype.val : U → M)).contMDiffOn :
          ContMDiffOn I I 1 (Subtype.val : U → M) Set.univ)
    contMDiffOn_invFun := by
      simpa [e] using hsymm }
  have hp : p ∈ Φ.source := by
    simp [Φ, e]
  have hlocal : IsLocalDiffeomorphAt I I 1 (Φ : U → M) p := by
    exact ⟨Φ, hp, fun x _ ↦ rfl⟩
  have hinv : (mfderiv I I (Φ : U → M) p).IsInvertible := by
    rw [← hlocal.mfderivToContinuousLinearEquiv_coe one_ne_zero]
    exact ContinuousLinearMap.isInvertible_equiv
  simpa [Φ, e] using hinv

/-- Helper for Problem 5-10: the canonical linear identification `ℝ ≃ ℝ¹`. -/
def problem510_real_to_r1_equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 5-10: the preferred map from `ℝ` to `ℝ¹`. -/
def problem510_real_to_r1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  problem510_real_to_r1_equiv

/-- Helper for Problem 5-10: the unique `ℝ¹` coordinate of `problem510_real_to_r1 t` is `t`. -/
theorem problem510_real_to_r1_apply (t : ℝ) :
    problem510_real_to_r1 t 0 = t := by
  -- The fixed equivalence is inverse to the standard identification `ℝ¹ ≃ ℝ`.
  simp [problem510_real_to_r1, problem510_real_to_r1_equiv]

/-- Helper for Problem 5-10: the linear identification `ℝ → ℝ¹` is a smooth submersion. -/
theorem problem510_real_to_r1_isSmoothSubmersion :
    Manifold.IsSmoothSubmersion 𝓘(ℝ, ℝ) (𝓡 1) problem510_real_to_r1 := by
  -- Linear equivalences are smooth and have everywhere-surjective derivative.
  refine ⟨?_, ?_⟩
  · simpa [problem510_real_to_r1] using
      problem510_real_to_r1_equiv.toContinuousLinearMap.contMDiff
  · intro x
    rw [mfderiv_eq_fderiv]
    have hderiv :
        fderiv ℝ problem510_real_to_r1 x =
          problem510_real_to_r1_equiv.toContinuousLinearMap := by
      simpa [problem510_real_to_r1] using
        (problem510_real_to_r1_equiv.toContinuousLinearMap.hasFDerivAt (x := x)).fderiv
    rw [hderiv]
    simpa [problem510_real_to_r1] using problem510_real_to_r1_equiv.surjective

/-- Helper for Problem 5-10: the defining polynomial whose zero set is `M_a`. -/
def problem510F (a : ℝ) : Plane → ℝ :=
  fun p ↦ p.2 ^ 2 - p.1 * (p.1 - 1) * (p.1 - a)

/-- Helper for Problem 5-10: `M_a` is exactly the zero fiber of `problem510F a`. -/
theorem problem510Curve_eq_zeroFiber (a : ℝ) :
    problem510Curve a = problem510F a ⁻¹' ({(0 : ℝ)} : Set ℝ) := by
  -- Unfolding both sides reduces the claim to the defining cubic equation.
  ext p
  rw [mem_problem510Curve_iff]
  constructor
  · intro hp
    change problem510F a p = 0
    dsimp [problem510F]
    linarith
  · intro hp
    change problem510F a p = 0 at hp
    dsimp [problem510F] at hp
    linarith

/-- Helper for Problem 5-10: the cubic polynomial `problem510F a` is smooth on all of `Plane`. -/
theorem problem510F_contDiff (a : ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (problem510F a) := by
  -- Rewrite to the explicit polynomial formula and use the standard smoothness rules.
  change ContDiff ℝ (⊤ : WithTop ℕ∞)
    (fun p : Plane ↦ p.2 ^ (2 : ℕ) - p.1 * (p.1 - 1) * (p.1 - a))
  fun_prop

/-- Helper for Problem 5-10: the Fréchet derivative of `problem510F a` has the expected gradient
pairing with the tangent vector. -/
theorem problem510F_fderiv_apply (a : ℝ) (p v : Plane) :
    fderiv ℝ (problem510F a) p v =
      (2 * p.2) * v.2 - (3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a) * v.1 := by
  sorry

/-- Helper for Problem 5-10: on the regular domain, the manifold derivative of `problem510F a`
is surjective. -/
theorem problem510F_mfderiv_surjective_of_regular {a : ℝ} {p : Plane}
    (hp : 2 * p.2 ≠ 0 ∨ 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0) :
    Function.Surjective (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) (problem510F a) p) := by
  sorry

/-- Helper for Problem 5-10: the open subset where one partial derivative of `problem510F a`
is nonzero. -/
def problem510RegularDomain (a : ℝ) : TopologicalSpace.Opens Plane :=
  ⟨{p : Plane | 2 * p.2 ≠ 0 ∨ 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0}, by
    -- The regular domain is the union of two complements of scalar zero sets.
    let Uy : Set Plane := {p : Plane | 2 * p.2 ≠ 0}
    let Ux : Set Plane := {p : Plane | 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0}
    have hUy_cont : Continuous fun p : Plane ↦ 2 * p.2 := by
      fun_prop
    have hUx_cont : Continuous fun p : Plane ↦ 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a := by
      fun_prop
    have hUy_open : IsOpen Uy := by
      simpa [Uy] using hUy_cont.isOpen_preimage {x : ℝ | x ≠ 0} (isOpen_ne (x := (0 : ℝ)))
    have hUx_open : IsOpen Ux := by
      simpa [Ux] using hUx_cont.isOpen_preimage {x : ℝ | x ≠ 0} (isOpen_ne (x := (0 : ℝ)))
    have hEq :
        {p : Plane | 2 * p.2 ≠ 0 ∨ 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0} =
          Uy ∪ Ux := by
      ext p
      simp [Uy, Ux]
    rw [hEq]
    exact hUy_open.union hUx_open⟩

/-- Helper for Problem 5-10: every point of `M_a` is regular when `a ≠ 0` and `a ≠ 1`. -/
theorem problem510Curve_subset_regularDomain {a : ℝ} {p : Plane}
    (hp : p ∈ problem510Curve a) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    p ∈ problem510RegularDomain a := by
  -- On the curve, if `y = 0` then `x` must be one of the three roots `0`, `1`, or `a`.
  rw [mem_problem510Curve_iff] at hp
  by_cases hy : p.2 = 0
  · -- On the zero slice, the cubic equation forces `x` to be one of the three roots.
    right
    have hxroots : p.1 * (p.1 - 1) * (p.1 - a) = 0 := by
      nlinarith [hp, hy]
    rcases mul_eq_zero.mp hxroots with hleft | hright
    · rcases mul_eq_zero.mp hleft with hx0 | hx1
      · simpa [hx0] using ha0
      · have hx1' : p.1 = 1 := sub_eq_zero.mp hx1
        have hneq : 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0 := by
          intro h
          rw [hx1'] at h
          apply ha1
          ring_nf at h
          linarith
        exact hneq
    · have hxa : p.1 = a := sub_eq_zero.mp hright
      have hneq : 3 * p.1 ^ (2 : ℕ) - 2 * (a + 1) * p.1 + a ≠ 0 := by
        intro h
        rw [hxa] at h
        have ha_ne_one : a - 1 ≠ 0 := by
          intro h'
          apply ha1
          linarith
        have : a * (a - 1) = 0 := by
          ring_nf at h
          linarith
        exact (mul_ne_zero ha0 ha_ne_one) this
      exact hneq
  · -- Off the zero slice, the `y`-partial derivative is already nonzero.
    left
    intro hzero
    exact hy (by nlinarith)

/-- Helper for Problem 5-10: restricting `problem510F a` to the regular domain only inserts the
derivative of the subtype inclusion. -/
theorem problem510RegularDomain_mfderiv_eq_comp_subtype_val (a : ℝ)
    (p : problem510RegularDomain a) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) (fun q : problem510RegularDomain a ↦ problem510F a q.1) p =
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) (problem510F a) p.1).comp
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
          (Subtype.val : problem510RegularDomain a → Plane) p) := by
  -- Use the smooth chain rule for the literal restriction `problem510F a ∘ Subtype.val`.
  have hsub :
      ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        (Subtype.val : problem510RegularDomain a → Plane) := by
    simpa using
      (contMDiff_subtype_val :
        ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
          (Subtype.val : problem510RegularDomain a → Plane))
  have hF : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) (problem510F a) := by
    rw [contMDiff_iff_contDiff]
    simpa using problem510F_contDiff a
  have hsub_diff :
      MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (Subtype.val : problem510RegularDomain a → Plane) p := by
    exact hsub.contMDiffAt.mdifferentiableAt (by simp)
  have hF_diff :
      MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) (problem510F a) p.1 := by
    exact hF.contMDiffAt.mdifferentiableAt (by simp)
  simpa [Function.comp] using mfderiv_comp p hF_diff hsub_diff

/-- Helper for Problem 5-10: the scalar restriction of `problem510F a` to the regular domain is a
smooth submersion. -/
theorem problem510RegularDomain_scalar_isSmoothSubmersion (a : ℝ) :
    Manifold.IsSmoothSubmersion 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ)
      (fun p : problem510RegularDomain a ↦ problem510F a p.1) := by
  sorry

/-- Helper for Problem 5-10: the `ℝ¹`-valued restriction of `problem510F a` to the regular domain
is a smooth submersion. -/
theorem problem510RegularDomain_isSmoothSubmersion (a : ℝ) :
    Manifold.IsSmoothSubmersion 𝓘(ℝ, Plane) (𝓡 1)
      (fun p : problem510RegularDomain a ↦ problem510_real_to_r1 (problem510F a p.1)) := by
  sorry

/-- Helper for Problem 5-10: the regular-domain zero-fiber inclusion has image exactly `M_a`. -/
theorem problem510_regular_zeroFiber_range_eq_curve (a : ℝ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Set.range
        (fun p :
          {q : problem510RegularDomain a |
            problem510_real_to_r1 (problem510F a q.1) = problem510_real_to_r1 0} ↦
          (p.1.1 : Plane)) =
      problem510Curve a := by
  -- Match the regular-domain fiber points with the original cubic equation in the ambient plane.
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have hq :
        problem510_real_to_r1 (problem510F a q.1.1) = problem510_real_to_r1 0 := by
      exact q.2
    have hzero : problem510F a q.1.1 = 0 := by
      exact problem510_real_to_r1_equiv.injective hq
    rw [problem510Curve_eq_zeroFiber]
    simpa using hzero
  · intro hp
    have hregular : p ∈ problem510RegularDomain a :=
      problem510Curve_subset_regularDomain hp ha0 ha1
    have hzero : problem510F a p = 0 := by
      rw [problem510Curve_eq_zeroFiber] at hp
      simpa using hp
    have hfiber : problem510_real_to_r1 (problem510F a p) = problem510_real_to_r1 0 := by
      simp [hzero]
    refine ⟨⟨⟨p, hregular⟩, ?_⟩, rfl⟩
    exact hfiber

/-- Helper for Problem 5-10: a regular level set modeled on `ℝ¹` can be re-packaged as an
embedded `ℝ`-curve by transporting its source charts through the fixed linear identification
`ℝ ≃ ℝ¹`. -/
theorem problem510_transport_embedded_submanifold_r1_to_real_plane {S : Set Plane}
    (hS :
      ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S,
        ∃ hs : IsManifold (𝓡 1) ∞ S,
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs
          let _ : IsManifold (𝓡 1) ∞ S := hs
          IsEmbeddedSubmanifold 𝓘(ℝ, Plane) (𝓡 1) S) :
    ∃ (_ : ChartedSpace ℝ S) (_ : IsManifold 𝓘(ℝ) ⊤ S),
      IsEmbeddedSubmanifold 𝓘(ℝ, Plane) 𝓘(ℝ) S := by
  sorry

/-- Helper for Problem 5-10: the nonsingular cubics `M_a` with `a ≠ 0, 1` are embedded curves. -/
theorem problem510Curve_regular_embedded_curve (a : ℝ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    (problem510Curve a).AdmitsEmbeddedCurveStructure := by
  sorry

/-- Helper for Problem 5-10: the node `(1, 0)` lies on the nodal cubic `M_1`. -/
theorem problem510Curve_one_node_mem :
    ((1 : ℝ), (0 : ℝ)) ∈ problem510Curve 1 := by
  -- The defining equation vanishes at the node.
  rw [mem_problem510Curve_iff]
  norm_num

/-- Helper for Problem 5-10: on `M_1`, the equation `x = 1` forces the node `(1, 0)`. -/
theorem problem510Curve_one_eq_node_of_mem_of_x_eq_one {q : Plane}
    (hq : q ∈ problem510Curve 1) (hx : q.1 = 1) :
    q = ((1 : ℝ), (0 : ℝ)) := by
  -- Substituting `x = 1` into the defining equation forces `y = 0`.
  rw [mem_problem510Curve_iff] at hq
  have hy : q.2 = 0 := by
    rw [hx] at hq
    nlinarith
  ext <;> simp [hx, hy]

/-- Helper for Problem 5-10: inside the small ball around the node, the equation `y = 0` also
forces the node itself. -/
theorem problem510Curve_one_eq_node_of_mem_ball_of_y_eq_zero {q : Plane}
    (hq : q ∈ problem510Curve 1)
    (hqball : q ∈ Metric.ball ((1 : ℝ), (0 : ℝ)) (1 / 2 : ℝ))
    (hy : q.2 = 0) :
    q = ((1 : ℝ), (0 : ℝ)) := by
  sorry

/-- Helper for Problem 5-10: the nodal cubic `M_1` is not an embedded curve. -/
theorem problem510Curve_one_not_embedded_curve :
    ¬ (problem510Curve 1).AdmitsEmbeddedCurveStructure := by
  sorry

-- TODO: build the immersed-curve topology on the nodal cubic by separating the two local branches
-- in the source smooth curve while keeping the same image subset in the plane.
/-- Helper for Problem 5-10: transport the source charted-space structure across a homeomorphism
onto a chosen subset of the plane. -/
noncomputable abbrev problem510_transport_subset_chartedSpace {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S) :
    ChartedSpace ℝ S :=
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  ChartedSpace.comp ℝ N S

/-- Helper for Problem 5-10: the transported range charted space is again a smooth `1`-manifold at
the outer regularity `⊤`. -/
lemma problem510_transport_subset_isManifold_top {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
    IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
  have hGroupoid : HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the already-known compatibility on the source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines a smooth manifold structure on the range.
  exact IsManifold.mk' 𝓘(ℝ) (⊤ : WithTop ℕ∞) S

/-- Helper for Problem 5-10: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma problem510_transport_subset_val_eq_comp_homeomorph_symm {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] {g : N → Plane} {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    (Subtype.val : S → Plane) = g ∘ e.symm := by
  -- Evaluate the factorization at a point of the transported subset and rewrite using
  -- `e (e.symm x) = x`.
  funext x
  simpa using he (e.symm x)

/-- Helper for Problem 5-10: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma problem510_transport_subset_val_isImmersionAt_explicit {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) (x : S) :
    let _ : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := problem510_transport_subset_isManifold_top e
    IsImmersionAtOfComplement hg.complement 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      (Subtype.val : S → Plane) x := by
  let instCharted : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    problem510_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  let hx := hCompImm (e.symm x)
  -- Transport the source chart of `g` across the homeomorphism onto `S`.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the point `x`.
    simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is the same pointwise statement as for `g`.
    have hxe : g (e.symm x) = (x : Plane) := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- The transported source chart stays in the maximal atlas after chart transport.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `Subtype.val ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = (z : Plane) := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- In the transported source chart, the inclusion `S ↪ ℝ²` has the same normal form as `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend 𝓘(ℝ)).target := by
      simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ((e (hx.domChart.symm u) : S) : Plane) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Problem 5-10: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma problem510_transport_subset_val_isImmersion_explicit {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    let _ : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := problem510_transport_subset_isManifold_top e
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) := by
  let instCharted : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    problem510_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Route correction: prove the global immersion by reusing the pointwise transported witness,
  -- rather than asking Lean to elaborate the full singleton-chart transport in one step.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  exact problem510_transport_subset_val_isImmersionAt_explicit hg e he x

/-- Helper for Problem 5-10: transporting the source manifold structure along a range equivalence
gives an immersed-curve structure on the image subset. -/
lemma problem510_transport_subset_isImmersedCurveWithTopology {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    Set.IsImmersedCurveWithTopology S (inferInstance : TopologicalSpace S) := by
  let instCharted : ChartedSpace ℝ S := problem510_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    problem510_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Package the transported atlas and manifold structure, then discharge immersion explicitly.
  refine ⟨instCharted, instManifold, ?_⟩
  simpa using problem510_transport_subset_val_isImmersion_explicit hg e he

/-- Helper for Problem 5-10: the cut source for the nodal cubic is the open subset
`ℝ \ {-1}`. -/
noncomputable abbrev problem510Curve_one_source : TopologicalSpace.Opens ℝ :=
  ⟨{t : ℝ | t ≠ -1}, isOpen_ne (x := (-1 : ℝ))⟩

/-- Helper for Problem 5-10: the ambient polynomial parametrization of the nodal cubic. -/
def problem510Curve_one_paramMap : ℝ → Plane :=
  fun t ↦ (t ^ 2, t * (t ^ 2 - 1))

/-- Helper for Problem 5-10: the standard real-axis inclusion used as the local immersion normal
form. -/
noncomputable def problem510_realAxisInclusion : ℝ → Plane :=
  fun u ↦ (u, 0)

/-- Helper for Problem 5-10: the real-axis inclusion is already in the target normal form for a
top-regularity immersion. -/
theorem problem510_realAxisInclusion_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) problem510_realAxisInclusion := by
  -- In the identity charts, the map is literally `u ↦ (u, 0)`.
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro u
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (by
      -- The normal form is assembled from the identity and constant maps on `ℝ`.
      simpa [problem510_realAxisInclusion] using
        ((continuous_id : Continuous fun x : ℝ ↦ x).prodMk continuous_const).continuousAt)
    (ContinuousLinearEquiv.refl ℝ Plane)
    (OpenPartialHomeomorph.refl ℝ)
    (OpenPartialHomeomorph.refl Plane)
  · simp
  · simp
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)).id_mem_maximalAtlas
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, Plane)).id_mem_maximalAtlas
  · intro x hx
    -- The written-in-charts map is definitionally the real-axis inclusion itself.
    simp [problem510_realAxisInclusion]

/-- Helper for Problem 5-10: away from the node, the nodal cubic is the zero-slice of the first
graph model `(u, v) ↦ (u², v + u (u² - 1))`. -/
noncomputable def problem510Curve_one_firstCoordinateGraph : Plane → Plane :=
  fun p ↦ (p.1 ^ 2, p.2 + p.1 * (p.1 ^ 2 - 1))

/-- Helper for Problem 5-10: near the node, the nodal cubic is the zero-slice of the second
graph model `(u, v) ↦ (v + u², u (u² - 1))`. -/
noncomputable def problem510Curve_one_secondCoordinateGraph : Plane → Plane :=
  fun p ↦ (p.2 + p.1 ^ 2, p.1 * (p.1 ^ 2 - 1))

/-- Helper for Problem 5-10: the first graph model sends the real-axis slice `v = 0` to the nodal
cubic parametrization. -/
theorem problem510Curve_one_firstCoordinateGraph_on_realAxis (t : ℝ) :
    problem510Curve_one_firstCoordinateGraph (problem510_realAxisInclusion t) =
      problem510Curve_one_paramMap t := by
  -- Setting the transverse coordinate to `0` leaves the original parametrization.
  simp [problem510Curve_one_firstCoordinateGraph, problem510_realAxisInclusion,
    problem510Curve_one_paramMap]

/-- Helper for Problem 5-10: the second graph model has the same zero-slice normalization. -/
theorem problem510Curve_one_secondCoordinateGraph_on_realAxis (t : ℝ) :
    problem510Curve_one_secondCoordinateGraph (problem510_realAxisInclusion t) =
      problem510Curve_one_paramMap t := by
  -- This is the symmetric zero-slice identity used at the node.
  simp [problem510Curve_one_secondCoordinateGraph, problem510_realAxisInclusion,
    problem510Curve_one_paramMap]

/-- Helper for Problem 5-10: the first graph model is `ω`-smooth on the ambient plane. -/
theorem problem510Curve_one_firstCoordinateGraph_contMDiff_top :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_firstCoordinateGraph := by
  -- Each coordinate is a polynomial in the two ambient coordinates.
  rw [contMDiff_iff_contDiff]
  simpa [problem510Curve_one_firstCoordinateGraph] using
    ((contDiff_fst.pow (2 : ℕ)).prodMk
      (contDiff_snd.add
        (contDiff_fst.mul ((contDiff_fst.pow (2 : ℕ)).sub contDiff_const))))

/-- Helper for Problem 5-10: the first graph model is pointwise `ω`-smooth. -/
theorem problem510Curve_one_firstCoordinateGraph_contMDiffAt_top (p : Plane) :
    ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_firstCoordinateGraph p := by
  -- This pointwise form is the input for the local inverse-function theorem.
  exact problem510Curve_one_firstCoordinateGraph_contMDiff_top.contMDiffAt

/-- Helper for Problem 5-10: the second graph model is `ω`-smooth on the ambient plane. -/
theorem problem510Curve_one_secondCoordinateGraph_contMDiff_top :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_secondCoordinateGraph := by
  -- Each coordinate is again a polynomial combination of the ambient coordinates.
  rw [contMDiff_iff_contDiff]
  simpa [problem510Curve_one_secondCoordinateGraph] using
    ((contDiff_snd.add (contDiff_fst.pow (2 : ℕ))).prodMk
      (contDiff_fst.mul ((contDiff_fst.pow (2 : ℕ)).sub contDiff_const)))

/-- Helper for Problem 5-10: the second graph model is pointwise `ω`-smooth. -/
theorem problem510Curve_one_secondCoordinateGraph_contMDiffAt_top (p : Plane) :
    ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_secondCoordinateGraph p := by
  -- This is the pointwise regularity input for the node chart.
  exact problem510Curve_one_secondCoordinateGraph_contMDiff_top.contMDiffAt

/-- Helper for Problem 5-10: a nonzero scalar multiple of the real line is an invertible
continuous linear map. -/
theorem problem510_real_line_map_isInvertible_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).IsInvertible := by
  have hc1 : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) 1 ≠ 0 := by
    simpa [ContinuousLinearMap.smulRight_apply] using hc
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  ext
  -- Every continuous linear endomorphism of `ℝ` is multiplication by its value at `1`.
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- Helper for Problem 5-10: the scalar cubic `u ↦ u (u² - 1)` has derivative `3u² - 1`. -/
theorem problem510Curve_one_cubic_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u * (u ^ (2 : ℕ) - 1)) (3 * t ^ (2 : ℕ) - 1) t := by
  sorry

/-- Helper for Problem 5-10: away from the node, the first graph model has the expected linearized
form at `(t, 0)`. -/
theorem problem510Curve_one_firstCoordinateGraph_fderiv_apply (t : ℝ) (w : Plane) :
    fderiv ℝ problem510Curve_one_firstCoordinateGraph (t, 0) w =
      (2 * t * w.1, w.2 + (3 * t ^ (2 : ℕ) - 1) * w.1) := by
  sorry

/-- Helper for Problem 5-10: at the node, the second graph model linearizes to `(u, v) ↦
  (v, -u)`. -/
theorem problem510Curve_one_secondCoordinateGraph_fderiv_apply (w : Plane) :
    fderiv ℝ problem510Curve_one_secondCoordinateGraph (0, 0) w = (w.2, -w.1) := by
  sorry

/-- Helper for Problem 5-10: the explicit invertible linearization of the first graph model away
from the node. -/
noncomputable def problem510Curve_one_firstCoordinateGraph_linearEquiv
    (t : ℝ) (ht : t ≠ 0) : Plane ≃L[ℝ] Plane := sorry

/-- Helper for Problem 5-10: the explicit invertible linearization of the second graph model at
the node. -/
noncomputable def problem510Curve_one_secondCoordinateGraph_linearEquiv :
    Plane ≃L[ℝ] Plane :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ))

/-- Helper for Problem 5-10: away from the node, the first graph model is a local diffeomorphism
because its derivative has nonzero first diagonal entry `2t`. -/
theorem problem510Curve_one_firstCoordinateGraph_isLocalDiffeomorphAt_top
    (t : ℝ) (ht : t ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_firstCoordinateGraph (t, 0) := by
  sorry

/-- Helper for Problem 5-10: at the node, the second graph model is a local diffeomorphism
because its derivative is the signed coordinate swap `(u, v) ↦ (v, -u)`. -/
theorem problem510Curve_one_secondCoordinateGraph_isLocalDiffeomorphAt_zero_top :
    IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_secondCoordinateGraph (0, 0) := by
  sorry

/-- Helper for Problem 5-10: the cut-source parametrization is the ambient parametrization
restricted to `ℝ \ {-1}`. -/
def problem510Curve_one_param : problem510Curve_one_source → Plane :=
  fun t ↦ problem510Curve_one_paramMap t

/-- Helper for Problem 5-10: the parametrization lands in the nodal cubic `M_1`. -/
theorem problem510Curve_one_param_mem (t : problem510Curve_one_source) :
    problem510Curve_one_param t ∈ problem510Curve 1 := by
  -- Substituting the explicit parametrization into the defining equation reduces to a polynomial
  -- identity.
  rw [mem_problem510Curve_iff]
  dsimp [problem510Curve_one_param, problem510Curve_one_paramMap]
  ring

/-- Helper for Problem 5-10: the cut-source parametrization viewed as a map into the subtype
`M_1`. -/
def problem510Curve_one_paramSubtype : problem510Curve_one_source → problem510Curve 1 :=
  fun t ↦ ⟨problem510Curve_one_param t, problem510Curve_one_param_mem t⟩

/-- Helper for Problem 5-10: the cut parametrization is injective after removing the branch point
`t = -1`. -/
theorem problem510Curve_one_param_injective :
    Function.Injective problem510Curve_one_param := by
  sorry

/-- Helper for Problem 5-10: every point of `M_1` comes from the cut parametrization. -/
theorem problem510Curve_one_param_surjective :
    Function.Surjective problem510Curve_one_paramSubtype := by
  sorry

/-- Helper for Problem 5-10: the cut parametrization is bijective onto the nodal cubic. -/
theorem problem510Curve_one_param_bijective :
    Function.Bijective problem510Curve_one_paramSubtype := by
  constructor
  · intro s t hst
    apply problem510Curve_one_param_injective
    exact congrArg Subtype.val hst
  · exact problem510Curve_one_param_surjective

/-- Helper for Problem 5-10: the cut parametrization gives an explicit equivalence from the source
interval to the nodal cubic subtype. -/
noncomputable def problem510Curve_one_equiv :
    problem510Curve_one_source ≃ problem510Curve 1 :=
  Equiv.ofBijective problem510Curve_one_paramSubtype problem510Curve_one_param_bijective

/-- Helper for Problem 5-10: the transported topology on `M_1` is the one pulled back from
`ℝ \ {-1}` by the explicit parametrization equivalence. -/
noncomputable abbrev problem510Curve_one_topology : TopologicalSpace (problem510Curve 1) :=
  problem510Curve_one_equiv.symm.topologicalSpace

/-- Helper for Problem 5-10: if the graph-model local inverse is defined at `x`, then the graph
image of `x` lies in the source of that local inverse. -/
theorem problem510Curve_one_graph_image_mem_localInverse_source
    {Γ : Plane → Plane} {p x : Plane}
    (hΓ : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) Γ p)
    (hx : x ∈ hΓ.localInverse.target) :
    Γ x ∈ hΓ.localInverse.source := by
  have hx_source : x ∈ hΓ.choose.source := by
    simpa using hx
  have hmap : hΓ.choose x ∈ hΓ.localInverse.source := by
    simpa using hΓ.choose.map_source hx_source
  simpa [hΓ.choose_spec.2 hx_source] using hmap

/-- Helper for Problem 5-10: the ambient nodal parametrization is an immersion at `t` once one of
the two graph models is a local diffeomorphism at `(t, 0)` and agrees with the zero slice. -/
theorem problem510Curve_one_paramMap_isImmersionAt_of_graph
    {Γ : Plane → Plane} {t : ℝ}
    (hΓ :
      IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        Γ (problem510_realAxisInclusion t))
    (hΓ_axis : ∀ u : ℝ, Γ (problem510_realAxisInclusion u) = problem510Curve_one_paramMap u) :
    IsImmersionAtOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_paramMap t := by
  sorry

/-- Helper for Problem 5-10: the ambient nodal parametrization is an immersion at every real
parameter; away from `0` use the first graph model, and at `0` use the second. -/
theorem problem510Curve_one_paramMap_isImmersionAt_top (t : ℝ) :
    IsImmersionAtOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      problem510Curve_one_paramMap t := by
  by_cases ht : t = 0
  · -- The node uses the symmetric graph model whose derivative swaps the coordinates.
    subst ht
    exact problem510Curve_one_paramMap_isImmersionAt_of_graph
      problem510Curve_one_secondCoordinateGraph_isLocalDiffeomorphAt_zero_top
      problem510Curve_one_secondCoordinateGraph_on_realAxis
  · -- Away from the node, the first graph model has invertible derivative because `2t ≠ 0`.
    exact problem510Curve_one_paramMap_isImmersionAt_of_graph
      (problem510Curve_one_firstCoordinateGraph_isLocalDiffeomorphAt_top t ht)
      problem510Curve_one_firstCoordinateGraph_on_realAxis

/-- Helper for Problem 5-10: the ambient nodal parametrization is a global immersion with the
fixed complement `ℝ`. -/
theorem problem510Curve_one_paramMap_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) problem510Curve_one_paramMap := by
  -- Package the pointwise normal forms supplied by the two graph-model branches.
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro t
  exact problem510Curve_one_paramMap_isImmersionAt_top t

/-- Helper for Problem 5-10: the cut parametrization should be proved to be an immersion by
straightening it locally as the zero section of an explicit local diffeomorphism on the plane. -/
theorem problem510Curve_one_param_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) problem510Curve_one_param := by
  -- Route correction: first prove the ambient map is an immersion by the two graph-model
  -- straightening charts, then restrict it along the open inclusion `ℝ \ {-1} ↪ ℝ`.
  simpa [problem510Curve_one_param, Function.comp] using
    Manifold.IsImmersion.ex416_comp problem510Curve_one_paramMap_isImmersion_top
      (Manifold.IsImmersion.of_opens (I := 𝓘(ℝ))
        (n := (⊤ : WithTop ℕ∞)) problem510Curve_one_source)

/-- Helper for Problem 5-10: the nodal cubic `M_1` admits an immersed-curve structure, although it
is not embedded as a curve with the subtype topology. -/
theorem problem510Curve_one_admits_immersed_curve_structure :
    (problem510Curve 1).AdmitsImmersedCurveStructure := by
  let _ : TopologicalSpace (problem510Curve 1) := problem510Curve_one_topology
  refine ⟨problem510Curve_one_topology, ?_⟩
  -- Transport the cut-source manifold structure across the explicit bijection onto `M_1`.
  simpa [problem510Curve_one_topology] using
    problem510_transport_subset_isImmersedCurveWithTopology problem510Curve_one_param_isImmersion
      ((problem510Curve_one_equiv.symm.homeomorph).symm) (fun t ↦ rfl)

-- Proof sketch: write `M_a` as the zero set of `F_a(x,y) = y^2 - x (x - 1) (x - a)`.  When
-- `a ≠ 0, 1`, the cubic has distinct roots, so `∇F_a` never vanishes on `M_a`, and the regular
-- level-set theorem gives an embedded smooth curve.  For `a = 0` or `a = 1`, the singular point
-- where the gradient vanishes prevents the subset topology from being locally a smooth
-- one-manifold.
/-- Problem 5-10 (1): the plane cubic `M_a` is an embedded smooth curve in `ℝ²` exactly when
`a` is different from both `0` and `1`. -/
theorem problem510Curve_isEmbeddedCurve_iff (a : ℝ) :
    (problem510Curve a).AdmitsEmbeddedCurveStructure ↔
      a ≠ 0 ∧ a ≠ 1 := by
  constructor
  · intro hEmbedded
    constructor
    · intro ha0
      subst ha0
      rcases hEmbedded with ⟨cs, hs, hEmb⟩
      let _ : ChartedSpace ℝ (problem510Curve 0) := cs
      let _ : IsManifold 𝓘(ℝ) ⊤ (problem510Curve 0) := hs
      exact problem510Curve_zero_no_immersed_curve_structure <|
        ⟨inferInstance, cs, hs, hEmb.isSmoothEmbedding_subtype_val.isImmersion⟩
    · intro ha1
      subst ha1
      exact problem510Curve_one_not_embedded_curve hEmbedded
  · intro ha
    -- The regular cases are exactly the nonsingular plane cubics.
    exact problem510Curve_regular_embedded_curve a ha.1 ha.2

-- Proof sketch: the regular cases `a ≠ 0, 1` are already embedded, hence immersed. If `a = 1`,
-- the node is modeled by separating the two crossing branches in the immersed source curve. If
-- `a = 0`, the set has an isolated point together with a one-dimensional branch, so no smooth
-- one-manifold structure can realize it as an immersed curve.
/-- Problem 5-10 (2): the plane cubic `M_a` admits a smooth immersed-curve structure exactly when
`a` is nonzero. -/
theorem problem510Curve_admitsImmersedCurveStructure_iff (a : ℝ) :
    (problem510Curve a).AdmitsImmersedCurveStructure ↔
      a ≠ 0 := by
  constructor
  · intro hImm ha0
    subst ha0
    exact problem510Curve_zero_no_immersed_curve_structure hImm
  · intro ha0
    by_cases ha1 : a = 1
    · subst ha1
      exact problem510Curve_one_admits_immersed_curve_structure
    · rcases problem510Curve_regular_embedded_curve a ha0 ha1 with ⟨cs, hs, hEmb⟩
      exact ⟨inferInstance, cs, hs, hEmb.isSmoothEmbedding_subtype_val.isImmersion⟩
