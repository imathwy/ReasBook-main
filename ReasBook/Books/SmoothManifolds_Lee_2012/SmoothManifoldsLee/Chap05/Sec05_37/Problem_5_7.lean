import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_49
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Pow

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- Helper for Problem 5-7: the manifold derivative of an open-subset inclusion is an
isomorphism. -/
theorem mfderiv_open_subset_inclusion_isInvertible
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) [IsManifold I (⊤ : WithTop ℕ∞) M] (p : U) :
    (mfderiv I I (Subtype.val : U → M) p).IsInvertible := by
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

/-- The cubic polynomial `F(x,y) = x^3 + xy + y^3` from Problem 5-7. -/
def problem_5_7_F : R2 → ℝ :=
  fun p ↦ p 0 ^ (3 : ℕ) + p 0 * p 1 + p 1 ^ (3 : ℕ)

-- Proof sketch: this is the defining coordinate formula of `problem_5_7_F`.
/-- The coordinate formula for the function `F` in Problem 5-7. -/
theorem problem_5_7_F_apply (p : R2) :
    problem_5_7_F p = p 0 ^ (3 : ℕ) + p 0 * p 1 + p 1 ^ (3 : ℕ) := rfl

/-- Helper for Problem 5-7: the second critical point of `problem_5_7_F` is
`(-1 / 3, -1 / 3)`. -/
def problem_5_7_singularPoint : R2 :=
  WithLp.toLp 2 ![-(1 / 3 : ℝ), -(1 / 3 : ℝ)]

/-- Helper for Problem 5-7: the singular point has both coordinates equal to `-1 / 3`. -/
theorem problem_5_7_singularPoint_apply (i : Fin 2) :
    problem_5_7_singularPoint i = -(1 / 3 : ℝ) := by
  -- Unfold the concrete `WithLp` vector and read off its coordinates.
  fin_cases i <;> simp [problem_5_7_singularPoint, PiLp.toLp_apply]

/-- Helper for Problem 5-7: the cubic vanishes at the origin. -/
theorem problem_5_7_F_zero : problem_5_7_F 0 = 0 := by
  -- Evaluate the defining polynomial at `(0,0)`.
  simp [problem_5_7_F]

/-- Helper for Problem 5-7: the cubic takes the value `1 / 27` at its nonzero critical point. -/
theorem problem_5_7_F_singularPoint :
    problem_5_7_F problem_5_7_singularPoint = (1 / 27 : ℝ) := by
  -- Substitute the critical-point coordinates into the cubic polynomial.
  norm_num [problem_5_7_F, problem_5_7_singularPoint, PiLp.toLp_apply]

/-- Helper for Problem 5-7: the cubic polynomial is smooth on all of `ℝ²`. -/
theorem problem_5_7_F_contDiff :
    ContDiff ℝ (⊤ : WithTop ℕ∞) problem_5_7_F := by
  -- Rewrite to the explicit polynomial formula, then apply the standard smoothness rules for
  -- coordinate projections, sums, products, and powers.
  change ContDiff ℝ (⊤ : WithTop ℕ∞)
    (fun p : R2 ↦ p 0 ^ (3 : ℕ) + p 0 * p 1 + p 1 ^ (3 : ℕ))
  fun_prop

/-- Helper for Problem 5-7: the Fréchet derivative of `problem_5_7_F` is the expected gradient
pairing with the tangent vector. -/
theorem problem_5_7_fderiv_apply (p v : R2) :
    fderiv ℝ problem_5_7_F p v =
      (3 * p 0 ^ (2 : ℕ) + p 1) * v 0 + (p 0 + 3 * p 1 ^ (2 : ℕ)) * v 1 := by
  -- Differentiate the two coordinate projections and combine them through the polynomial formula.
  have h0 :
      HasFDerivAt (fun q : R2 ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0
  have h1 :
      HasFDerivAt (fun q : R2 ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1
  have hF_raw :
      HasFDerivAt
        ((fun q : R2 ↦ q 0 ^ (3 : ℕ)) + ((fun q : R2 ↦ q 1 ^ (3 : ℕ)) + fun q : R2 ↦ q 0 * q 1))
        (((3 • p 0 ^ (3 - 1)) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) +
          ((3 • p 1 ^ (3 - 1)) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ) +
            (p 0 • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ) +
              p 1 • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)))) p := by
    -- Differentiate the three summands in the exact association order used below.
    exact (h0.pow 3).add ((h1.pow 3).add (h0.mul h1))
  have hF :
      HasFDerivAt problem_5_7_F
        (((3 • p 0 ^ (3 - 1)) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) +
          ((3 • p 1 ^ (3 - 1)) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ) +
            (p 0 • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ) +
              p 1 • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)))) p := by
    -- Fold the expanded polynomial back to the named function `problem_5_7_F`.
    convert hF_raw using 1
    funext q
    simp [problem_5_7_F, add_assoc, add_left_comm, add_comm]
  rw [hF.fderiv]
  -- Evaluate the resulting linear map on the tangent vector `v`.
  simp [PiLp.proj_apply, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm,
    smul_eq_mul, right_distrib, left_distrib]

/-- Helper for Problem 5-7: the manifold derivative is surjective exactly when the gradient is
nonzero. -/
theorem problem_5_7_mfderiv_surjective_iff (p : R2) :
    Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_5_7_F p) ↔
      ¬ (3 * p 0 ^ (2 : ℕ) + p 1 = 0 ∧ p 0 + 3 * p 1 ^ (2 : ℕ) = 0) := by
  rw [mfderiv_eq_fderiv]
  change Function.Surjective (fderiv ℝ problem_5_7_F p : R2 →L[ℝ] ℝ) ↔
    ¬ (3 * p 0 ^ (2 : ℕ) + p 1 = 0 ∧ p 0 + 3 * p 1 ^ (2 : ℕ) = 0)
  constructor
  · intro hsurj
    -- If both gradient coefficients vanished, the derivative would be the zero map.
    intro hgrad
    have hzero : fderiv ℝ problem_5_7_F p = 0 := by
      ext v
      rw [problem_5_7_fderiv_apply]
      simp [hgrad.1, hgrad.2]
    rw [hzero] at hsurj
    rcases hsurj 1 with ⟨v, hv⟩
    simpa using hv
  · intro hgrad
    -- A nonzero coefficient produces an explicit preimage of any target value.
    by_cases h0 : 3 * p 0 ^ (2 : ℕ) + p 1 = 0
    · have h1 : p 0 + 3 * p 1 ^ (2 : ℕ) ≠ 0 := by
        intro h1
        exact hgrad ⟨h0, h1⟩
      intro y
      refine ⟨WithLp.toLp 2 ![(0 : ℝ), y / (p 0 + 3 * p 1 ^ (2 : ℕ))], ?_⟩
      rw [problem_5_7_fderiv_apply]
      simp [PiLp.toLp_apply, h0]
      field_simp [h1]
    · intro y
      refine ⟨WithLp.toLp 2 ![y / (3 * p 0 ^ (2 : ℕ) + p 1), (0 : ℝ)], ?_⟩
      rw [problem_5_7_fderiv_apply]
      simp [PiLp.toLp_apply]
      field_simp [h0]

/-- Helper for Problem 5-7: the simultaneous vanishing of the two partial derivatives occurs only
at the two critical points of the cubic. -/
theorem problem_5_7_critical_point_iff (p : R2) :
    (3 * p 0 ^ (2 : ℕ) + p 1 = 0 ∧ p 0 + 3 * p 1 ^ (2 : ℕ) = 0) ↔
      p = 0 ∨ p = problem_5_7_singularPoint := by
  constructor
  · rintro ⟨h0, h1⟩
    by_cases hp0 : p 0 = 0
    · -- When `x = 0`, the first critical equation forces `y = 0`.
      have hp1 : p 1 = 0 := by
        nlinarith [h0]
      left
      ext i <;> fin_cases i <;> simp [hp0, hp1]
    · -- Otherwise, eliminate `y` and solve the resulting cubic equation in `x`.
      have hy : p 1 = -3 * p 0 ^ (2 : ℕ) := by
        nlinarith [h0]
      have hxeq : p 0 + 27 * p 0 ^ (4 : ℕ) = 0 := by
        nlinarith [h1, hy]
      have hxfactor : p 0 * (27 * p 0 ^ (3 : ℕ) + 1) = 0 := by
        nlinarith [hxeq]
      have hxcube : 27 * p 0 ^ (3 : ℕ) + 1 = 0 := by
        rcases mul_eq_zero.mp hxfactor with hzero | hzero
        · exact (hp0 hzero).elim
        · exact hzero
      have hp0val : p 0 = -(1 / 3 : ℝ) := by
        nlinarith [hxcube]
      have hp1val : p 1 = -(1 / 3 : ℝ) := by
        nlinarith [h0, hp0val]
      right
      ext i <;> fin_cases i <;> simp [problem_5_7_singularPoint_apply, hp0val, hp1val]
  · rintro (rfl | rfl)
    · -- The origin is visibly critical.
      constructor <;> norm_num
    · -- The translated singular point is also visibly critical.
      constructor <;> norm_num [problem_5_7_singularPoint_apply]

-- Proof sketch: compute the gradient `∇F(x,y) = (3x^2 + y, x + 3y^2)`, solve the critical-point
-- equations to get only `(0,0)` and `(-1/3,-1/3)`, and evaluate `F` at those points.
/-- The regular values of `problem_5_7_F` are exactly the real numbers other than `0` and
`1 / 27`. -/
theorem problem_5_7_isRegularValue_iff (c : ℝ) :
    (∀ p : R2,
        problem_5_7_F p = c →
          Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_5_7_F p)) ↔
      c ≠ 0 ∧ c ≠ (1 / 27 : ℝ) := by
  constructor
  · intro hc
    constructor
    · intro hc0
      have hsurj := hc 0 <| by simpa [hc0] using problem_5_7_F_zero
      exact
        ((problem_5_7_mfderiv_surjective_iff 0).1 hsurj)
          (by constructor <;> norm_num)
    · intro hc27
      have hsurj := hc problem_5_7_singularPoint <| by
        simpa [hc27] using problem_5_7_F_singularPoint
      exact
        ((problem_5_7_mfderiv_surjective_iff problem_5_7_singularPoint).1 hsurj)
          (by constructor <;> norm_num [problem_5_7_singularPoint_apply])
  · rintro ⟨hc0, hc27⟩
    intro p hp
    -- The only possible failures of surjectivity are the two critical points, whose fiber values
    -- are exactly the excluded values `0` and `1 / 27`.
    refine (problem_5_7_mfderiv_surjective_iff p).2 ?_
    intro hgrad
    rcases (problem_5_7_critical_point_iff p).1 hgrad with rfl | rfl
    · exact hc0 <| by simpa [hp] using problem_5_7_F_zero
    · exact hc27 <| by simpa [hp] using problem_5_7_F_singularPoint

/-- Helper for Problem 5-7: the canonical linear identification `ℝ ≃ ℝ¹`. -/
def problem_5_7_real_to_r1_equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 5-7: the preferred map from `ℝ` to `ℝ¹`. -/
def problem_5_7_real_to_r1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  problem_5_7_real_to_r1_equiv

/-- Helper for Problem 5-7: the `ℝ¹` coordinate of `problem_5_7_real_to_r1 t` is exactly `t`. -/
theorem problem_5_7_real_to_r1_apply (t : ℝ) :
    problem_5_7_real_to_r1 t 0 = t := by
  -- The chosen equivalence is the inverse of the standard identification `ℝ¹ ≃ ℝ`.
  simp [problem_5_7_real_to_r1, problem_5_7_real_to_r1_equiv]

/-- Helper for Problem 5-7: the linear identification `ℝ → ℝ¹` is a smooth submersion. -/
theorem problem_5_7_real_to_r1_isSmoothSubmersion :
    IsSmoothSubmersion 𝓘(ℝ, ℝ) (𝓡 1) problem_5_7_real_to_r1 := by
  -- The fixed linear equivalence is smooth, and its manifold derivative is itself everywhere.
  refine ⟨?_, ?_⟩
  · simpa [problem_5_7_real_to_r1] using
      problem_5_7_real_to_r1_equiv.toContinuousLinearMap.contMDiff
  · intro x
    rw [mfderiv_eq_fderiv]
    -- Replace the Fréchet derivative by the underlying continuous linear equivalence.
    have hderiv :
        fderiv ℝ problem_5_7_real_to_r1 x =
          problem_5_7_real_to_r1_equiv.toContinuousLinearMap := by
      simpa [problem_5_7_real_to_r1] using
        (problem_5_7_real_to_r1_equiv.toContinuousLinearMap.hasFDerivAt (x := x)).fderiv
    rw [hderiv]
    simpa [problem_5_7_real_to_r1] using problem_5_7_real_to_r1_equiv.surjective

/-- Helper for Problem 5-7: the open complement of the two critical points. -/
def problem_5_7_regularDomain : TopologicalSpace.Opens R2 :=
  ⟨{p : R2 | p ≠ 0 ∧ p ≠ problem_5_7_singularPoint},
    isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl⟩

/-- Helper for Problem 5-7: the regular-domain subtype avoids exactly the two critical points. -/
theorem problem_5_7_regularDomain_property (p : problem_5_7_regularDomain) :
    (p : R2) ≠ 0 ∧ (p : R2) ≠ problem_5_7_singularPoint :=
  p.2

/-- Helper for Problem 5-7: restricting `problem_5_7_F` to the open regular domain only inserts
the derivative of the subtype inclusion. -/
theorem problem_5_7_regularDomain_mfderiv_eq_comp_subtype_val (p : problem_5_7_regularDomain) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : problem_5_7_regularDomain ↦ problem_5_7_F q.1) p =
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_5_7_F p.1).comp
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : problem_5_7_regularDomain → R2) p) := by
  -- Route correction: use the direct scalar smoothness of `problem_5_7_F`, then apply the smooth
  -- chain rule to the literal restriction `problem_5_7_F ∘ Subtype.val`.
  have hsub :
      ContMDiff (𝓡 2) (𝓡 2) (⊤ : WithTop ℕ∞)
        (Subtype.val : problem_5_7_regularDomain → R2) := by
    simpa using
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) (⊤ : WithTop ℕ∞)
          (Subtype.val : problem_5_7_regularDomain → R2))
  have hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) problem_5_7_F := by
    rw [contMDiff_iff_contDiff]
    simpa using problem_5_7_F_contDiff
  have hsub_diff :
      MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : problem_5_7_regularDomain → R2) p := by
    exact hsub.contMDiffAt.mdifferentiableAt (by simp)
  have hF_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) problem_5_7_F p.1 := by
    exact hF.contMDiffAt.mdifferentiableAt (by simp)
  simpa [Function.comp] using
    (mfderiv_comp p hF_diff hsub_diff)

/-- Helper for Problem 5-7: the restriction of `F` to the regular domain is a smooth submersion
onto `ℝ`. -/
theorem problem_5_7_regularDomain_scalar_isSmoothSubmersion :
    IsSmoothSubmersion (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : problem_5_7_regularDomain ↦ problem_5_7_F p.1) := by
  sorry

/-- Helper for Problem 5-7: the `ℝ¹`-valued restriction of `F` to the regular domain is a smooth
submersion. -/
theorem problem_5_7_regularDomain_isSmoothSubmersion :
    IsSmoothSubmersion (𝓡 2) (𝓡 1)
      (fun p : problem_5_7_regularDomain ↦
        problem_5_7_real_to_r1 (problem_5_7_F p.1)) := by
  -- Route correction: package the composition directly, so the proof no longer depends on the
  -- Chapter 4 composition convenience theorem.
  have hscalar := problem_5_7_regularDomain_scalar_isSmoothSubmersion
  have hr1 := problem_5_7_real_to_r1_isSmoothSubmersion
  have hcomp :
      ContMDiff (𝓡 2) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : problem_5_7_regularDomain ↦ problem_5_7_real_to_r1 (problem_5_7_F p.1)) := by
    -- Smoothness follows from the chain rule for the fixed linear identification after the
    -- scalar regular-domain map.
    simpa [Function.comp] using hr1.contMDiff.comp hscalar.contMDiff
  refine ⟨by simpa using hcomp, ?_⟩
  intro p
  have hmdiff_outer :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) problem_5_7_real_to_r1 (problem_5_7_F p.1) := by
    exact hr1.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmdiff_inner :
      MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : problem_5_7_regularDomain ↦ problem_5_7_F q.1) p := by
    exact hscalar.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- The derivative of the composite is the composite of the two already-surjective derivatives.
  have hmfderiv :
      mfderiv (𝓡 2) (𝓡 1)
        (fun q : problem_5_7_regularDomain ↦ problem_5_7_real_to_r1 (problem_5_7_F q.1)) p =
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) problem_5_7_real_to_r1 (problem_5_7_F p.1)).comp
            (mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
              (fun q : problem_5_7_regularDomain ↦ problem_5_7_F q.1) p) := by
    simpa [Function.comp] using mfderiv_comp p hmdiff_outer hmdiff_inner
  rw [hmfderiv]
  simpa [Function.comp] using
    (hr1.surjective_mfderiv (problem_5_7_F p.1)).comp (hscalar.surjective_mfderiv p)

/-- Helper for Problem 5-7: a point on a nonexceptional fiber cannot be one of the two critical
points. -/
theorem problem_5_7_nonexceptional_fiber_point_regular
    {c : ℝ} {p : R2} (hp : problem_5_7_F p = c) (hc : c ≠ 0 ∧ c ≠ (1 / 27 : ℝ)) :
    p ≠ 0 ∧ p ≠ problem_5_7_singularPoint := by
  constructor
  · -- If `p = 0`, then the fiber value would be the excluded critical value `0`.
    intro hp0
    have hc0 : c = 0 := by
      calc
        c = problem_5_7_F p := hp.symm
        _ = problem_5_7_F 0 := by simpa [hp0]
        _ = 0 := problem_5_7_F_zero
    exact hc.1 hc0
  · -- If `p` were the nonzero critical point, then the fiber value would be the other excluded
    -- critical value `1 / 27`.
    intro hpsing
    have hc27 : c = (1 / 27 : ℝ) := by
      calc
        c = problem_5_7_F p := hp.symm
        _ = problem_5_7_F problem_5_7_singularPoint := by simpa [hpsing]
        _ = (1 / 27 : ℝ) := problem_5_7_F_singularPoint
    exact hc.2 hc27

/-- Helper for Problem 5-7: every regular fiber is locally a level set of the fixed smooth
submersion on the complement of the two critical points. -/
theorem problem_5_7_regular_value_has_local_submersion_level_model
    {c : ℝ} {p : R2} (hp : problem_5_7_F p = c) (hc : c ≠ 0 ∧ c ≠ (1 / 27 : ℝ)) :
    ∃ U : TopologicalSpace.Opens R2, p ∈ U ∧
      ∃ Φ : U → EuclideanSpace ℝ (Fin 1),
        IsSmoothSubmersion (𝓡 2) (𝓡 1) Φ ∧
          ∃ z : EuclideanSpace ℝ (Fin 1),
            {x : U | (x : R2) ∈ problem_5_7_F ⁻¹' {c}} = Φ ⁻¹' {z} := by
  -- The source proof uses the fixed regular domain: away from the two critical points, every
  -- regular fiber is already a fiber of one global smooth submersion.
  refine ⟨problem_5_7_regularDomain, ?_, ?_⟩
  · -- A point on a nonexceptional fiber cannot be one of the two critical points.
    exact problem_5_7_nonexceptional_fiber_point_regular hp hc
  · refine ⟨fun q : problem_5_7_regularDomain ↦ problem_5_7_real_to_r1 (problem_5_7_F q.1), ?_, ?_⟩
    · exact problem_5_7_regularDomain_isSmoothSubmersion
    · refine ⟨problem_5_7_real_to_r1 c, ?_⟩
      -- The chosen level is exactly the fiber over the distinguished `ℝ¹` point corresponding to `c`.
      ext x
      constructor
      · intro hx
        have hxc : problem_5_7_F x.1 = c := by
          simpa [Set.mem_preimage] using hx
        simpa [Set.mem_preimage, hxc]
      · intro hx
        have hx0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hx
        simpa [Set.mem_preimage, problem_5_7_real_to_r1_apply] using hx0

/-- Helper for Problem 5-7: after translating the singular point to the origin, the exceptional
`1 / 27` fiber factors as the line `u + v = 1` times the quadratic form
`u^2 - uv + v^2`. -/
theorem problem_5_7_translate_factorization (u v : ℝ) :
    problem_5_7_F (WithLp.toLp 2 ![u - (1 / 3 : ℝ), v - (1 / 3 : ℝ)]) - (1 / 27 : ℝ) =
      (u + v - 1) * (u ^ (2 : ℕ) - u * v + v ^ (2 : ℕ)) := by
  -- Route correction: prove the source translation identity directly, instead of rediscovering it
  -- inside the exceptional-fiber topology argument.
  -- Unfold the translated polynomial into a concrete cubic expression in `u` and `v`.
  simp [problem_5_7_F]
  -- Then factor the normalized polynomial by ring arithmetic.
  ring

/-- Helper for Problem 5-7: on the slice `x = t > 0`, the zero fiber changes sign between
`y = 0` and `y = -t`. -/
theorem problem_5_7_zero_slice_positive_x_signs (t : ℝ) :
    problem_5_7_F (WithLp.toLp 2 ![t, 0]) = t ^ (3 : ℕ) ∧
      problem_5_7_F (WithLp.toLp 2 ![t, -t]) = -(t ^ (2 : ℕ)) := by
  -- These explicit evaluations are the sign inputs for the IVT branch in the `x > 0` sector.
  constructor
  · simp [problem_5_7_F]
  · simp [problem_5_7_F]
    ring_nf
/-- Helper for Problem 5-7: on the slice `x = -t^2`, the zero fiber has a positive-`y` sign change
between `y = t` and `y = 2t`. -/
theorem problem_5_7_zero_slice_negative_x_positive_y_signs (t : ℝ) :
    problem_5_7_F (WithLp.toLp 2 ![-t ^ (2 : ℕ), t]) = -(t ^ (6 : ℕ)) ∧
      problem_5_7_F (WithLp.toLp 2 ![-t ^ (2 : ℕ), 2 * t]) =
        6 * t ^ (3 : ℕ) - t ^ (6 : ℕ) := by
  -- These are the two endpoint values used to force a zero in the `x < 0 < y` sector.
  constructor
  · simp [problem_5_7_F]
    ring
  · simp [problem_5_7_F]
    ring

/-- Helper for Problem 5-7: on the slice `x = -t^2`, the zero fiber has a negative-`y` sign change
between `y = -t` and `y = -t / 2`. -/
theorem problem_5_7_zero_slice_negative_x_negative_y_signs (t : ℝ) :
    problem_5_7_F (WithLp.toLp 2 ![-t ^ (2 : ℕ), -t]) = -(t ^ (6 : ℕ)) ∧
      problem_5_7_F (WithLp.toLp 2 ![-t ^ (2 : ℕ), -(t / 2)]) =
        (3 / 8 : ℝ) * t ^ (3 : ℕ) - t ^ (6 : ℕ) := by
  -- These are the two endpoint values used to force a zero in the `x < 0, y < 0` sector.
  constructor
  · simp [problem_5_7_F]
    ring
  · simp [problem_5_7_F]
    ring

/-- Helper for Problem 5-7: every nonzero point of the zero fiber lies in exactly one of the three
sign sectors used in the source proof. -/
theorem problem_5_7_zero_level_sign_sector {p : R2}
    (hp : problem_5_7_F p = 0) (hpne : p ≠ 0) :
    (0 < p 0 ∧ p 1 < 0) ∨ (p 0 < 0 ∧ 0 < p 1) ∨ (p 0 < 0 ∧ p 1 < 0) := by
  -- First exclude vanishing coordinates: on the zero fiber, either coordinate being zero forces
  -- the whole point to be the origin.
  have hp0_ne : p 0 ≠ 0 := by
    intro hp0
    have hp1 : p 1 = 0 := by
      rw [problem_5_7_F_apply] at hp
      have hp1cube : p 1 ^ (3 : ℕ) = 0 := by simpa [hp0] using hp
      exact eq_zero_of_pow_eq_zero hp1cube
    apply hpne
    ext i
    fin_cases i <;> simp [hp0, hp1]
  have hp1_ne : p 1 ≠ 0 := by
    intro hp1
    have hp0 : p 0 = 0 := by
      rw [problem_5_7_F_apply] at hp
      have hp0cube : p 0 ^ (3 : ℕ) = 0 := by simpa [hp1] using hp
      exact eq_zero_of_pow_eq_zero hp0cube
    apply hpne
    ext i
    fin_cases i <;> simp [hp0, hp1]
  rcases lt_or_gt_of_ne hp0_ne with hp0_lt | hp0_gt
  · rcases lt_or_gt_of_ne hp1_ne with hp1_lt | hp1_gt
    · exact Or.inr <| Or.inr ⟨hp0_lt, hp1_lt⟩
    · exact Or.inr <| Or.inl ⟨hp0_lt, hp1_gt⟩
  · rcases lt_or_gt_of_ne hp1_ne with hp1_lt | hp1_gt
    · exact Or.inl ⟨hp0_gt, hp1_lt⟩
    · exfalso
      have hpos : 0 < p 0 ^ (3 : ℕ) + p 0 * p 1 + p 1 ^ (3 : ℕ) := by
        positivity
      rw [problem_5_7_F_apply] at hp
      linarith

/-- Helper for Problem 5-7: on the zero fiber, vanishing `x` forces the point to be the origin. -/
theorem problem_5_7_zero_fiber_eq_origin_of_x_zero {p : R2}
    (hp : problem_5_7_F p = 0) (hx : p 0 = 0) :
    p = 0 := by
  -- Substitute `x = 0` into the cubic equation and solve for `y`.
  have hy : p 1 = 0 := by
    rw [problem_5_7_F_apply] at hp
    have hycube : p 1 ^ (3 : ℕ) = 0 := by simpa [hx] using hp
    exact eq_zero_of_pow_eq_zero hycube
  ext i
  fin_cases i <;> simp [hx, hy]

/-- Helper for Problem 5-7: on the zero fiber, vanishing `y` forces the point to be the origin. -/
theorem problem_5_7_zero_fiber_eq_origin_of_y_zero {p : R2}
    (hp : problem_5_7_F p = 0) (hy : p 1 = 0) :
    p = 0 := by
  -- Substitute `y = 0` into the cubic equation and solve for `x`.
  have hx : p 0 = 0 := by
    rw [problem_5_7_F_apply] at hp
    have hxcube : p 0 ^ (3 : ℕ) = 0 := by simpa [hy] using hp
    exact eq_zero_of_pow_eq_zero hxcube
  ext i
  fin_cases i <;> simp [hx, hy]

/-- Helper for Problem 5-7: every sufficiently small ball about the origin meets each of the three
local branches of the zero fiber. -/
theorem problem_5_7_zero_branch_witnesses_in_ball (ε : ℝ) (hε : 0 < ε) :
    (∃ p ∈ Metric.ball (0 : R2) ε, problem_5_7_F p = 0 ∧ 0 < p 0 ∧ p 1 < 0) ∧
      (∃ p ∈ Metric.ball (0 : R2) ε, problem_5_7_F p = 0 ∧ p 0 < 0 ∧ 0 < p 1) ∧
      (∃ p ∈ Metric.ball (0 : R2) ε, problem_5_7_F p = 0 ∧ p 0 < 0 ∧ p 1 < 0) := by
  sorry

/-- Helper for Problem 5-7: every ambient neighborhood of the origin meets all three local
branches of the zero fiber. -/
theorem problem_5_7_zero_level_sector_points_in_open (U : Set R2)
    (hU : IsOpen U) (h0U : (0 : R2) ∈ U) :
    (∃ p ∈ U, problem_5_7_F p = 0 ∧ 0 < p 0 ∧ p 1 < 0) ∧
      (∃ p ∈ U, problem_5_7_F p = 0 ∧ p 0 < 0 ∧ 0 < p 1) ∧
      (∃ p ∈ U, problem_5_7_F p = 0 ∧ p 0 < 0 ∧ p 1 < 0) := by
  -- Shrink the ambient open neighborhood to a ball around the origin, then reuse the uniform
  -- three-branch witness package from the previous lemma.
  obtain ⟨ε, hε_pos, hεU⟩ := Metric.isOpen_iff.mp hU (0 : R2) h0U
  rcases problem_5_7_zero_branch_witnesses_in_ball ε hε_pos with
    ⟨⟨p1, hp1_ball, hp1_zero, hp1x, hp1y⟩,
      ⟨⟨p2, hp2_ball, hp2_zero, hp2x, hp2y⟩,
        ⟨p3, hp3_ball, hp3_zero, hp3x, hp3y⟩⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨p1, hεU hp1_ball, hp1_zero, hp1x, hp1y⟩
  · exact ⟨p2, hεU hp2_ball, hp2_zero, hp2x, hp2y⟩
  · exact ⟨p3, hεU hp3_ball, hp3_zero, hp3x, hp3y⟩

/-- Helper for Problem 5-7: a preconnected subset of the punctured zero fiber cannot contain both
positive and negative `x`-coordinates. -/
theorem problem_5_7_preconnected_zero_fiber_no_mixed_x_sign
    {A : Set (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))} (hA : IsPreconnected A)
    (hA_nonzero : ∀ q ∈ A, (q : R2) ≠ 0) :
    ¬ ((∃ q ∈ A, 0 < (q : R2) 0) ∧ ∃ q ∈ A, (q : R2) 0 < 0) := by
  sorry

/-- Helper for Problem 5-7: a preconnected subset of the punctured zero fiber cannot contain both
positive and negative `y`-coordinates. -/
theorem problem_5_7_preconnected_zero_fiber_no_mixed_y_sign
    {A : Set (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))} (hA : IsPreconnected A)
    (hA_nonzero : ∀ q ∈ A, (q : R2) ≠ 0) :
    ¬ ((∃ q ∈ A, 0 < (q : R2) 1) ∧ ∃ q ∈ A, (q : R2) 1 < 0) := by
  sorry

/-- Helper for Problem 5-7: every nonexceptional fiber satisfies the local-submersion criterion,
so it carries an embedded-submanifold structure modelled on `ℝ¹`. -/
theorem problem_5_7_regular_level_embedded_submanifold_r1 {c : ℝ}
    (hc : c ≠ 0 ∧ c ≠ (1 / 27 : ℝ)) :
    ∃ tm : TopologicalManifold 1 (problem_5_7_F ⁻¹' {c}),
      let _ : TopologicalManifold 1 (problem_5_7_F ⁻¹' {c}) := tm
      ∃ hs : IsManifold (𝓡 1) (⊤ : WithTop ℕ∞) (problem_5_7_F ⁻¹' {c}),
        let _ : IsManifold (𝓡 1) (⊤ : WithTop ℕ∞) (problem_5_7_F ⁻¹' {c}) := hs
        IsEmbeddedSubmanifold (𝓡 2) (𝓡 1) (problem_5_7_F ⁻¹' {c}) := by
  sorry

/-- Helper for Problem 5-7: the singular point is isolated in the `c = 1 / 27` fiber. -/
theorem problem_5_7_level_one_over_twenty_seventh_isolated :
    ∃ U : Set R2, IsOpen U ∧ problem_5_7_singularPoint ∈ U ∧
      U ∩ (problem_5_7_F ⁻¹' ({(1 / 27 : ℝ)} : Set ℝ)) = {problem_5_7_singularPoint} := by
  refine ⟨Metric.ball problem_5_7_singularPoint (1 / 6 : ℝ), Metric.isOpen_ball, by simp, ?_⟩
  ext p
  constructor
  · rintro ⟨hpball, hpfiber⟩
    let u : ℝ := p 0 + 1 / 3
    let v : ℝ := p 1 + 1 / 3
    have hnorm : ‖p - problem_5_7_singularPoint‖ < (1 / 6 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hpball
    have hu_le : |u| ≤ ‖p - problem_5_7_singularPoint‖ := by
      simpa [u, problem_5_7_singularPoint_apply] using
        (PiLp.norm_apply_le (p - problem_5_7_singularPoint) 0)
    have hv_le : |v| ≤ ‖p - problem_5_7_singularPoint‖ := by
      simpa [v, problem_5_7_singularPoint_apply] using
        (PiLp.norm_apply_le (p - problem_5_7_singularPoint) 1)
    have hu_lt : |u| < (1 / 6 : ℝ) := lt_of_le_of_lt hu_le hnorm
    have hv_lt : |v| < (1 / 6 : ℝ) := lt_of_le_of_lt hv_le hnorm
    have huv_lt : |u + v| < (1 / 3 : ℝ) := by
      calc
        |u + v| ≤ |u| + |v| := by
          simpa [Real.norm_eq_abs] using (norm_add_le u v)
        _ < (1 / 6 : ℝ) + (1 / 6 : ℝ) := add_lt_add hu_lt hv_lt
        _ = (1 / 3 : ℝ) := by norm_num
    have hvec :
        WithLp.toLp 2 ![u - (1 / 3 : ℝ), v - (1 / 3 : ℝ)] = p := by
      ext i
      fin_cases i <;> simp [u, v, PiLp.toLp_apply]
    have hpval : problem_5_7_F p = (1 / 27 : ℝ) := by
      simpa [Set.mem_preimage] using hpfiber
    have hprod :
        (u + v - 1) * (u ^ (2 : ℕ) - u * v + v ^ (2 : ℕ)) = 0 := by
      calc
        (u + v - 1) * (u ^ (2 : ℕ) - u * v + v ^ (2 : ℕ)) =
            problem_5_7_F (WithLp.toLp 2 ![u - (1 / 3 : ℝ), v - (1 / 3 : ℝ)]) - (1 / 27 : ℝ) := by
              symm
              exact problem_5_7_translate_factorization u v
        _ = problem_5_7_F p - (1 / 27 : ℝ) := by rw [hvec]
        _ = 0 := by simp [hpval]
    have hline_ne : u + v - 1 ≠ 0 := by
      intro hline
      have hEqOne : u + v = (1 : ℝ) := by linarith
      have : |u + v| = (1 : ℝ) := by simpa [hEqOne]
      nlinarith
    have hquad : u ^ (2 : ℕ) - u * v + v ^ (2 : ℕ) = 0 := by
      rcases mul_eq_zero.mp hprod with hline | hquad
      · exact (hline_ne hline).elim
      · exact hquad
    have hsquares :
        (u - v) ^ (2 : ℕ) + u ^ (2 : ℕ) + v ^ (2 : ℕ) = 0 := by
      have hid :
          2 * (u ^ (2 : ℕ) - u * v + v ^ (2 : ℕ)) =
            (u - v) ^ (2 : ℕ) + u ^ (2 : ℕ) + v ^ (2 : ℕ) := by
        ring
      nlinarith [hid, hquad]
    have hu_zero : u = 0 := by
      nlinarith [hsquares]
    have hv_zero : v = 0 := by
      nlinarith [hsquares]
    have hp0 : p 0 = -(1 / 3 : ℝ) := by
      dsimp [u] at hu_zero
      nlinarith [hu_zero]
    have hp1 : p 1 = -(1 / 3 : ℝ) := by
      dsimp [v] at hv_zero
      nlinarith [hv_zero]
    have hp_eq : p = problem_5_7_singularPoint := by
      ext i
      fin_cases i <;> simp [problem_5_7_singularPoint_apply, hp0, hp1]
    simpa [hp_eq]
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨by simp, by simpa [Set.mem_preimage] using problem_5_7_F_singularPoint⟩

/-- Helper for Problem 5-7: the `c = 1 / 27` fiber cannot carry an embedded-curve structure
because its singular point is isolated in the induced topology. -/
theorem problem_5_7_level_one_over_twenty_seventh_not_embedded_submanifold :
    ¬ ∃ (_ : ChartedSpace ℝ (problem_5_7_F ⁻¹' ({(1 / 27 : ℝ)} : Set ℝ)))
        (_ : IsManifold 𝓘(ℝ) ⊤ (problem_5_7_F ⁻¹' ({(1 / 27 : ℝ)} : Set ℝ))),
        IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ)
          (problem_5_7_F ⁻¹' ({(1 / 27 : ℝ)} : Set ℝ)) := by
  intro hEmbedded
  rcases hEmbedded with ⟨cs, hs, hS⟩
  let S : Set R2 := problem_5_7_F ⁻¹' ({(1 / 27 : ℝ)} : Set ℝ)
  let _ : ChartedSpace ℝ S := cs
  let _ : IsManifold 𝓘(ℝ) ⊤ S := hs
  let p : S := ⟨problem_5_7_singularPoint, by simpa [S, Set.mem_preimage] using problem_5_7_F_singularPoint⟩
  have hsingletonOpen : IsOpen ({p} : Set S) := by
    rcases problem_5_7_level_one_over_twenty_seventh_isolated with ⟨U, hUopen, hpU, hUcap⟩
    have hEq : ({p} : Set S) = (Subtype.val : S → R2) ⁻¹' U := by
      ext q
      constructor
      · intro hq
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact hpU
      · intro hq
        have hq' : (q : R2) = problem_5_7_singularPoint := by
          have hqmem : (q : R2) ∈ U ∩ S := ⟨hq, q.2⟩
          have : (q : R2) ∈ ({problem_5_7_singularPoint} : Set R2) := by
            rw [← hUcap]
            exact hqmem
          simpa using this
        apply Set.mem_singleton_iff.mpr
        exact Subtype.ext hq'
    simpa [hEq] using hUopen.preimage continuous_subtype_val
  let e := chartAt ℝ p
  have hImageSingleton : e '' ({p} : Set S) = {e p} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases Set.mem_singleton_iff.mp hq with rfl
      simp
    · intro hx
      refine ⟨p, by simp, ?_⟩
      simpa using hx.symm
  have hImageOpen : IsOpen ({e p} : Set ℝ) := by
    -- A chart is an open map on its source, so the isolated singleton would map to an open
    -- singleton in `ℝ`.
    have hImageOpenRaw : IsOpen (e '' (e.source ∩ ({p} : Set S))) :=
      e.isOpen_image_source_inter hsingletonOpen
    have hSourceSingleton : e.source ∩ ({p} : Set S) = ({p} : Set S) := by
      ext q
      constructor
      · rintro ⟨_, hq⟩
        exact hq
      · intro hq
        refine ⟨?_, hq⟩
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact mem_chart_source ℝ p
    simpa [hSourceSingleton, hImageSingleton] using hImageOpenRaw
  exact not_isOpen_singleton (e p) hImageOpen

/-- Helper for Problem 5-7: the origin belongs to the zero fiber. -/
theorem problem_5_7_zero_fiber_origin_mem :
    (0 : R2) ∈ problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ) := by
  -- This is exactly the already computed value `problem_5_7_F 0 = 0`.
  simpa [Set.mem_preimage] using problem_5_7_F_zero

/-- Helper for Problem 5-7: an open subset of the zero fiber is the preimage of an ambient open
subset of `ℝ²` under the subtype inclusion. -/
theorem problem_5_7_zero_fiber_open_neighborhood_to_ambient_open
    {V : Set (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))} (hV : IsOpen V) :
    ∃ U : Set R2, IsOpen U ∧
      V = (Subtype.val : (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)) → R2) ⁻¹' U := by
  -- Unpack the induced-topology description of openness for the subtype.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.1 hV with ⟨U, hU, hEq⟩
  exact ⟨U, hU, hEq.symm⟩

/-- Helper for Problem 5-7: every open neighborhood of the origin in the zero fiber contains
subtype points on all three local branches. -/
theorem problem_5_7_zero_level_sector_points_in_subtype_open
    (V : Set (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))) (hV : IsOpen V)
    (h0V :
      (⟨0, problem_5_7_zero_fiber_origin_mem⟩ : problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)) ∈ V) :
    (∃ q ∈ V, 0 < (q : R2) 0 ∧ (q : R2) 1 < 0) ∧
      (∃ q ∈ V, (q : R2) 0 < 0 ∧ 0 < (q : R2) 1) ∧
      (∃ q ∈ V, (q : R2) 0 < 0 ∧ (q : R2) 1 < 0) := by
  rcases problem_5_7_zero_fiber_open_neighborhood_to_ambient_open hV with ⟨U, hU, hVU⟩
  have h0U : (0 : R2) ∈ U := by
    -- Re-express the subtype neighborhood as the pullback of an ambient open set and read off
    -- the origin's membership there.
    simpa [hVU] using h0V
  rcases problem_5_7_zero_level_sector_points_in_open U hU h0U with
    ⟨⟨p1, hp1U, hp1_zero, hp1x, hp1y⟩,
      ⟨⟨p2, hp2U, hp2_zero, hp2x, hp2y⟩,
        ⟨p3, hp3U, hp3_zero, hp3x, hp3y⟩⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Package the first ambient witness as a subtype point of `V`.
    refine ⟨⟨p1, by simpa [Set.mem_preimage] using hp1_zero⟩, ?_, hp1x, hp1y⟩
    simpa [hVU] using hp1U
  · -- Package the second ambient witness as a subtype point of `V`.
    refine ⟨⟨p2, by simpa [Set.mem_preimage] using hp2_zero⟩, ?_, hp2x, hp2y⟩
    simpa [hVU] using hp2U
  · -- Package the third ambient witness as a subtype point of `V`.
    refine ⟨⟨p3, by simpa [Set.mem_preimage] using hp3_zero⟩, ?_, hp3x, hp3y⟩
    simpa [hVU] using hp3U

/-- Helper for Problem 5-7: in a chart at the origin on the zero fiber, a sufficiently small
bounded interval pulls back to a punctured neighborhood split into two preconnected sides. -/
theorem problem_5_7_zero_chart_interval_two_side_cover
    [ChartedSpace ℝ (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))]
    [IsManifold 𝓘(ℝ) ⊤ (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))] :
    let S : Set R2 := problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)
    let p : S := ⟨0, problem_5_7_zero_fiber_origin_mem⟩
    let e := chartAt ℝ p
    ∃ δ : Set.Ioi (0 : ℝ),
      let W : Set S := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p + (δ : ℝ))
      let L : Set S := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p)
      let R : Set S := e.symm '' Set.Ioo (e p) (e p + (δ : ℝ))
      IsOpen W ∧ p ∈ W ∧ IsPreconnected L ∧ IsPreconnected R ∧
        L ∪ R = W \ ({p} : Set S) := by
  let S : Set R2 := problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)
  let p : S := ⟨0, problem_5_7_zero_fiber_origin_mem⟩
  let e := chartAt ℝ p
  let ep : ℝ := e p
  -- Choose a bounded interval around the chart center contained in the chart target.
  rcases Metric.mem_nhds_iff.mp (chart_target_mem_nhds (H := ℝ) p) with ⟨δ, hδpos, hδsub⟩
  have htarget :
      Set.Ioo (ep - δ) (ep + δ) ⊆ e.target := by
    simpa [ep, Real.ball_eq_Ioo] using hδsub
  refine ⟨⟨δ, hδpos⟩, ?_⟩
  let W : Set S := e.symm '' Set.Ioo (ep - δ) (ep + δ)
  let L : Set S := e.symm '' Set.Ioo (ep - δ) ep
  let R : Set S := e.symm '' Set.Ioo ep (ep + δ)
  have hL_subset_target : Set.Ioo (ep - δ) ep ⊆ e.target := by
    intro y hy
    exact htarget ⟨hy.1, by linarith [hy.2, hδpos]⟩
  have hR_subset_target : Set.Ioo ep (ep + δ) ⊆ e.target := by
    intro y hy
    exact htarget ⟨by linarith [hy.1, hδpos], hy.2⟩
  have hW_open : IsOpen W := by
    -- The inverse image of an open interval inside the target is open in the zero fiber.
    have hW_open_raw : IsOpen (e.symm '' (e.target ∩ Set.Ioo (ep - δ) (ep + δ))) := by
      simpa using e.symm.isOpen_image_source_inter isOpen_Ioo
    have htarget_eq : e.target ∩ Set.Ioo (ep - δ) (ep + δ) = Set.Ioo (ep - δ) (ep + δ) :=
      Set.inter_eq_right.mpr htarget
    simpa [W, htarget_eq] using hW_open_raw
  have hpW : p ∈ W := by
    -- The chart center itself lies in the bounded interval.
    refine ⟨ep, ?_, ?_⟩
    · constructor <;> linarith
    · simpa [ep, e] using e.left_inv (mem_chart_source ℝ p)
  have hL_preconnected : IsPreconnected L := by
    -- The left half comes from the preconnected interval `(ep - δ, ep)`.
    simpa [L] using isPreconnected_Ioo.image _ (e.continuousOn_symm.mono hL_subset_target)
  have hR_preconnected : IsPreconnected R := by
    -- The right half comes from the preconnected interval `(ep, ep + δ)`.
    simpa [R] using isPreconnected_Ioo.image _ (e.continuousOn_symm.mono hR_subset_target)
  have hpunctured_cover : L ∪ R = W \ ({p} : Set S) := by
    -- Removing the midpoint from the bounded interval leaves exactly its left and right halves.
    ext q
    constructor
    · intro hq
      rcases hq with hqL | hqR
      · rcases hqL with ⟨y, hy, rfl⟩
        refine ⟨?_, ?_⟩
        · refine ⟨y, ⟨hy.1, by linarith [hy.2, hδpos]⟩, rfl⟩
        · intro hqp
          have hy_target : y ∈ e.target := hL_subset_target hy
          have : y = ep := by
            calc
              y = e (e.symm y) := by symm; exact e.right_inv hy_target
              _ = e p := congrArg e hqp
              _ = ep := rfl
          have : ep < ep := by simpa [this] using hy.2
          exact lt_irrefl _ this
      · rcases hqR with ⟨y, hy, rfl⟩
        refine ⟨?_, ?_⟩
        · refine ⟨y, ⟨by linarith [hy.1, hδpos], hy.2⟩, rfl⟩
        · intro hqp
          have hy_target : y ∈ e.target := hR_subset_target hy
          have : y = ep := by
            calc
              y = e (e.symm y) := by symm; exact e.right_inv hy_target
              _ = e p := congrArg e hqp
              _ = ep := rfl
          have : ep < ep := by simpa [this] using hy.1
          exact lt_irrefl _ this
    · intro hq
      rcases hq.1 with ⟨y, hy, rfl⟩
      have hy_ne : y ≠ ep := by
        intro hy_eq
        apply hq.2
        simpa [ep, hy_eq, e] using e.left_inv (mem_chart_source ℝ p)
      rcases lt_or_gt_of_ne hy_ne with hy_lt | hy_gt
      · left
        exact ⟨y, ⟨hy.1, hy_lt⟩, rfl⟩
      · right
        exact ⟨y, ⟨hy_gt, hy.2⟩, rfl⟩
  -- Re-express the goal using the named neighborhood sets.
  dsimp [W, L, R]
  exact ⟨hW_open, hpW, hL_preconnected, hR_preconnected, hpunctured_cover⟩

/-- Helper for Problem 5-7: the zero fiber cannot be an embedded `1`-submanifold because every
punctured neighborhood of the origin meets three local branches, while a chart neighborhood splits
into only two preconnected sides. -/
theorem problem_5_7_level_zero_not_embedded_submanifold :
    ¬ ∃ (_ : ChartedSpace ℝ (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)))
        (_ : IsManifold 𝓘(ℝ) ⊤ (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ))),
        IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ)
          (problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)) := by
  intro hEmbedded
  rcases hEmbedded with ⟨cs, hs, _⟩
  let S : Set R2 := problem_5_7_F ⁻¹' ({(0 : ℝ)} : Set ℝ)
  let _ : ChartedSpace ℝ S := cs
  let _ : IsManifold 𝓘(ℝ) ⊤ S := hs
  let p : S := ⟨0, problem_5_7_zero_fiber_origin_mem⟩
  let e := chartAt ℝ p
  rcases problem_5_7_zero_chart_interval_two_side_cover with
    ⟨δ, hW_open, hpW, hL_preconnected, hR_preconnected, hpunctured_cover⟩
  let W : Set S := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p + (δ : ℝ))
  let L : Set S := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p)
  let R : Set S := e.symm '' Set.Ioo (e p) (e p + (δ : ℝ))
  have hW_open' : IsOpen W := by
    simpa [W, e, p] using hW_open
  have hpW' : p ∈ W := by
    simpa [W, e, p] using hpW
  have hL_preconnected' : IsPreconnected L := by
    simpa [L, e, p] using hL_preconnected
  have hR_preconnected' : IsPreconnected R := by
    simpa [R, e, p] using hR_preconnected
  have hpunctured_cover' : L ∪ R = W \ ({p} : Set S) := by
    simpa [W, L, R, e, p] using hpunctured_cover
  rcases problem_5_7_zero_level_sector_points_in_subtype_open W hW_open' hpW' with
    ⟨⟨q1, hq1W, hq1x_pos, hq1y_neg⟩,
      ⟨⟨q2, hq2W, hq2x_neg, hq2y_pos⟩,
        ⟨q3, hq3W, hq3x_neg, hq3y_neg⟩⟩⟩
  have hq1_ne_p : q1 ≠ p := by
    -- The first witness has positive `x`, so it cannot be the origin point `p`.
    intro hq1p
    have : 0 < (p : R2) 0 := by simpa [hq1p] using hq1x_pos
    simpa [p] using this
  have hq2_ne_p : q2 ≠ p := by
    -- The second witness has positive `y`, so it cannot be the origin point `p`.
    intro hq2p
    have : 0 < (p : R2) 1 := by simpa [hq2p] using hq2y_pos
    simpa [p] using this
  have hq3_ne_p : q3 ≠ p := by
    -- The third witness has negative `x`, so it cannot be the origin point `p`.
    intro hq3p
    have : (p : R2) 0 < 0 := by simpa [hq3p] using hq3x_neg
    simpa [p] using this
  have hq1_punctured : q1 ∈ W \ ({p} : Set S) := by
    exact ⟨hq1W, by simpa [Set.mem_singleton_iff] using hq1_ne_p⟩
  have hq2_punctured : q2 ∈ W \ ({p} : Set S) := by
    exact ⟨hq2W, by simpa [Set.mem_singleton_iff] using hq2_ne_p⟩
  have hq3_punctured : q3 ∈ W \ ({p} : Set S) := by
    exact ⟨hq3W, by simpa [Set.mem_singleton_iff] using hq3_ne_p⟩
  have hq1_side : q1 ∈ L ∪ R := by
    simpa [hpunctured_cover'] using hq1_punctured
  have hq2_side : q2 ∈ L ∪ R := by
    simpa [hpunctured_cover'] using hq2_punctured
  have hq3_side : q3 ∈ L ∪ R := by
    simpa [hpunctured_cover'] using hq3_punctured
  have hL_nonzero : ∀ q ∈ L, (q : R2) ≠ 0 := by
    intro q hqL hq0
    have hq_ne_p : q ≠ p := by
      have hq_punctured : q ∈ W \ ({p} : Set S) := by
        exact hpunctured_cover' ▸ Or.inl hqL
      simpa [Set.mem_singleton_iff] using hq_punctured.2
    apply hq_ne_p
    apply Subtype.ext
    simpa [p] using hq0
  have hR_nonzero : ∀ q ∈ R, (q : R2) ≠ 0 := by
    intro q hqR hq0
    have hq_ne_p : q ≠ p := by
      have hq_punctured : q ∈ W \ ({p} : Set S) := by
        exact hpunctured_cover' ▸ Or.inr hqR
      simpa [Set.mem_singleton_iff] using hq_punctured.2
    apply hq_ne_p
    apply Subtype.ext
    simpa [p] using hq0
  have hL_no_mixed_x :
      ¬ ((∃ q ∈ L, 0 < (q : R2) 0) ∧ ∃ q ∈ L, (q : R2) 0 < 0) :=
    problem_5_7_preconnected_zero_fiber_no_mixed_x_sign hL_preconnected' hL_nonzero
  have hR_no_mixed_x :
      ¬ ((∃ q ∈ R, 0 < (q : R2) 0) ∧ ∃ q ∈ R, (q : R2) 0 < 0) :=
    problem_5_7_preconnected_zero_fiber_no_mixed_x_sign hR_preconnected' hR_nonzero
  have hL_no_mixed_y :
      ¬ ((∃ q ∈ L, 0 < (q : R2) 1) ∧ ∃ q ∈ L, (q : R2) 1 < 0) :=
    problem_5_7_preconnected_zero_fiber_no_mixed_y_sign hL_preconnected' hL_nonzero
  have hR_no_mixed_y :
      ¬ ((∃ q ∈ R, 0 < (q : R2) 1) ∧ ∃ q ∈ R, (q : R2) 1 < 0) :=
    problem_5_7_preconnected_zero_fiber_no_mixed_y_sign hR_preconnected' hR_nonzero
  -- Route correction: keep the source proof's two-side-versus-three-branch contradiction inside
  -- the zero-fiber subtype, and only use sign-based preconnectedness obstructions on one side.
  rcases hq1_side with hq1L | hq1R <;>
    rcases hq2_side with hq2L | hq2R <;>
    rcases hq3_side with hq3L | hq3R
  · exact hL_no_mixed_x ⟨⟨q1, hq1L, hq1x_pos⟩, q3, hq3L, hq3x_neg⟩
  · exact hL_no_mixed_x ⟨⟨q1, hq1L, hq1x_pos⟩, q2, hq2L, hq2x_neg⟩
  · exact hL_no_mixed_x ⟨⟨q1, hq1L, hq1x_pos⟩, q3, hq3L, hq3x_neg⟩
  · exact hR_no_mixed_y ⟨⟨q2, hq2R, hq2y_pos⟩, q3, hq3R, hq3y_neg⟩
  · exact hL_no_mixed_y ⟨⟨q2, hq2L, hq2y_pos⟩, q3, hq3L, hq3y_neg⟩
  · exact hR_no_mixed_x ⟨⟨q1, hq1R, hq1x_pos⟩, q3, hq3R, hq3x_neg⟩
  · exact hR_no_mixed_x ⟨⟨q1, hq1R, hq1x_pos⟩, q2, hq2R, hq2x_neg⟩
  · exact hR_no_mixed_x ⟨⟨q1, hq1R, hq1x_pos⟩, q3, hq3R, hq3x_neg⟩

/-- Helper for Problem 5-7: conjugating an `ℝ¹` chart transition by the fixed linear
identification `ℝ ≃ ℝ¹` produces an `ℝ`-smooth chart transition. -/
theorem r1_transition_mem_contDiffGroupoid_real
    {e :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))}
    (he : e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1)) :
    let eModel :
        OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
      problem_5_7_real_to_r1_equiv.toHomeomorph.symm.toOpenPartialHomeomorph
    (eModel.symm.trans e).trans eModel ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
  let eModel :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
    problem_5_7_real_to_r1_equiv.toHomeomorph.symm.toOpenPartialHomeomorph
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (e : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) e.source := by
    simpa using he.1
  have he_right :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (e.symm : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) e.target := by
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel : EuclideanSpace ℝ (Fin 1) → ℝ) := by
    -- The model change is the fixed inverse linear equivalence `ℝ¹ → ℝ`.
    simpa [eModel] using problem_5_7_real_to_r1_equiv.symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel.symm : ℝ → EuclideanSpace ℝ (Fin 1)) := by
    -- Its inverse is the original linear equivalence `ℝ → ℝ¹`.
    simpa [eModel] using problem_5_7_real_to_r1_equiv.toContinuousLinearMap.contDiff
  constructor
  · -- Compose the old `ℝ¹`-smooth transition with the two fixed linear coordinate changes.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : ℝ ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) := by
      refine he_left.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : ℝ ↦ eModel (e (eModel.symm x)))
          (eModel.symm ⁻¹' e.source) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source] using hfinal
  · -- The same conjugation argument applies to the inverse transition.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : ℝ ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) := by
      refine he_right.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : ℝ ↦ eModel (e.symm (eModel.symm x)))
          (eModel.symm ⁻¹' e.target) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Problem 5-7: a regular level set modeled on `ℝ¹` can be re-packaged as an
embedded `ℝ`-curve by transporting its source charts through the fixed linear identification
`ℝ ≃ ℝ¹`. -/
theorem transport_embedded_submanifold_r1_to_real {S : Set R2}
    (hS :
      ∃ tm : TopologicalManifold 1 S,
        let _ : TopologicalManifold 1 S := tm
        ∃ hs : IsManifold (𝓡 1) (⊤ : WithTop ℕ∞) S,
          let _ : IsManifold (𝓡 1) (⊤ : WithTop ℕ∞) S := hs
          IsEmbeddedSubmanifold (𝓡 2) (𝓡 1) S) :
    ∃ (_ : ChartedSpace ℝ S) (_ : IsManifold 𝓘(ℝ) ⊤ S),
      IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ) S := by
  rcases hS with ⟨tm, hs, hEmb⟩
  let _ : TopologicalManifold 1 S := tm
  let _ : IsManifold (𝓡 1) (⊤ : WithTop ℕ∞) S := hs
  let eModel :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
    problem_5_7_real_to_r1_equiv.toHomeomorph.symm.toOpenPartialHomeomorph
  have heModel_source : eModel.source = Set.univ := by
    -- The model change comes from a global homeomorphism, so its source is all of `ℝ¹`.
    ext x
    simp [eModel]
  let _ : ChartedSpace ℝ (EuclideanSpace ℝ (Fin 1)) := eModel.singletonChartedSpace heModel_source
  let instCharted : ChartedSpace ℝ S := ChartedSpace.comp ℝ (EuclideanSpace ℝ (Fin 1)) S
  let _ : ChartedSpace ℝ S := instCharted
  have instManifold : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
    have hGroupoid : HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) := by
      refine ⟨?_⟩
      rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
      have hcEq : c = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c hc
      have hc'Eq : c' = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c' hc'
      subst c
      subst c'
      -- The transported transition is the old `ℝ¹` transition conjugated by the fixed model map.
      have hcompat_old :
          f.symm.trans f' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) :=
        HasGroupoid.compatible hf hf'
      simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc, eModel] using
        r1_transition_mem_contDiffGroupoid_real hcompat_old
    let _ : HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) := hGroupoid
    exact IsManifold.mk' 𝓘(ℝ) (⊤ : WithTop ℕ∞) S
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  have hSubtypeImmersion :
      Manifold.IsImmersion 𝓘(ℝ) (𝓡 2) (⊤ : WithTop ℕ∞) (Subtype.val : S → R2) := by
    let hImm := hEmb.isSmoothEmbedding_subtype_val.isImmersion
    let hComp := hImm.complement
    let hCompImm := hImm.isImmersionOfComplement_complement
    refine ⟨hComp, inferInstance, inferInstance, ?_⟩
    intro x
    let hx := hCompImm x
    let equivReal :
        (ℝ × hComp) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (problem_5_7_real_to_r1_equiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ hComp)).trans hx.equiv
    have hdomChart :
        hx.domChart.trans eModel ∈ IsManifold.maximalAtlas 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
      rw [IsManifold.mem_maximalAtlas_iff]
      intro d hd
      rcases hd with ⟨f, hf, c, hc, rfl⟩
      have hcEq : c = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c hc
      subst c
      have hleft_old :
          hx.domChart.symm.trans f ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) := by
        exact (hx.domChart_mem_maximalAtlas f hf).1
      have hright_old :
          f.symm.trans hx.domChart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) := by
        exact (hx.domChart_mem_maximalAtlas f hf).2
      constructor
      · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc, eModel] using
          r1_transition_mem_contDiffGroupoid_real hleft_old
      · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc, eModel] using
          r1_transition_mem_contDiffGroupoid_real hright_old
    -- Route correction: reuse the old immersion witness pointwise and only change the source chart.
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      equivReal (hx.domChart.trans eModel) hx.codChart ?_ ?_ hdomChart hx.codChart_mem_maximalAtlas
      ?_ ?_
    · -- The transported source chart still contains the point `x`.
      simpa [OpenPartialHomeomorph.trans_source, eModel] using hx.mem_domChart_source
    · -- The codomain chart condition is unchanged.
      simpa using hx.mem_codChart_source
    · -- A point in the transported source chart is still in the old source chart.
      intro z hz
      have hz' : z ∈ hx.domChart.source := by
        simpa [OpenPartialHomeomorph.trans_source, eModel] using hz
      exact hx.source_subset_preimage_source hz'
    · -- In transported source coordinates, the inclusion has the same normal form as before.
      intro u hu
      have hu' :
          problem_5_7_real_to_r1_equiv u ∈ (hx.domChart.extend (𝓡 1)).target := by
        simpa [eModel, OpenPartialHomeomorph.extend_target,
          OpenPartialHomeomorph.trans_target] using hu
      simpa [equivReal, eModel, Function.comp, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm] using hx.writtenInCharts hu'
  have hSubtype :
      Manifold.IsSmoothEmbedding 𝓘(ℝ) (𝓡 2) (⊤ : WithTop ℕ∞) (Subtype.val : S → R2) :=
    ⟨hSubtypeImmersion, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨instCharted, instManifold, ?_⟩
  exact
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := hSubtype }

-- Proof sketch: if `c ≠ 0` and `c ≠ 1 / 27`, then `c` is a regular value of `F`, so the regular
-- level-set theorem gives a smooth embedded one-dimensional submanifold structure on
-- `F⁻¹' {c}`. For `c = 0`, the level set has a self-crossing at the origin. For `c = 1 / 27`,
-- the translated equation factors as a line together with the isolated point `(-1/3,-1/3)`, so
-- that fiber is not a manifold.
/-- Problem 5-7: the level set `F⁻¹' {c}` is an embedded submanifold of `ℝ²` exactly for
`c ≠ 0` and `c ≠ 1 / 27`. -/
theorem problem_5_7_levelSet_is_embedded_submanifold_iff (c : ℝ) :
    (∃ (_ : ChartedSpace ℝ (problem_5_7_F ⁻¹' {c}))
        (_ : IsManifold 𝓘(ℝ) ⊤ (problem_5_7_F ⁻¹' {c})),
        IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ) (problem_5_7_F ⁻¹' {c})) ↔
      c ≠ 0 ∧ c ≠ (1 / 27 : ℝ) := by
  constructor
  · intro hEmbedded
    constructor
    · -- Route correction: the remaining `c = 0` obstruction must compare the three local zero-fiber
      -- branches with the two-sided punctured interval model in a chart at the origin.
      intro hc0
      subst hc0
      exact problem_5_7_level_zero_not_embedded_submanifold hEmbedded
    · -- The `c = 1 / 27` obstruction is now closed by isolating the singular point.
      intro hc27
      subst hc27
      exact problem_5_7_level_one_over_twenty_seventh_not_embedded_submanifold hEmbedded
  · intro hc
    -- Route correction: the positive direction is reduced to `problem_5_7_regular_level_embedded_submanifold_r1`.
    -- The remaining step is exactly the file-local chart transport from `ℝ¹` to `ℝ`.
    exact
      transport_embedded_submanifold_r1_to_real
        (problem_5_7_regular_level_embedded_submanifold_r1 hc)
