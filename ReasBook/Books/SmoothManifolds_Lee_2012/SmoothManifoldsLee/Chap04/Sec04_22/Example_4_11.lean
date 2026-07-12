import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_9
import SmoothManifolds_Lee_2012.Chap01.Sec01_07.Problem_1_8
import SmoothManifolds_Lee_2012.Chap02.Sec02_08.Example_2_13
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Proposition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `IsLocalDiffeomorph` is the canonical owner predicate, and finite products use
-- `isLocalDiffeomorph_pi`.

open scoped ContDiff Manifold Torus

noncomputable section

/-- Helper for Example 4.11: shifting an angle function by an integer multiple of `2π` preserves
the angle-function identities. -/
theorem IsAngleFunction.sub_int_mul_two_pi {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}
    (hθ : IsAngleFunction θ) (m : ℤ) :
    IsAngleFunction (fun z ↦ θ z - m * (2 * Real.pi)) := by
  constructor
  · -- Subtracting a constant keeps the local branch continuous.
    exact hθ.1.sub continuous_const
  · intro z
    -- Integer shifts disappear after exponentiating because `Circle.exp` is `2π`-periodic.
    calc
      Circle.exp (θ z - m * (2 * Real.pi))
          = Circle.exp (θ z) / Circle.exp (m * (2 * Real.pi)) := by
            rw [Circle.exp_sub]
      _ = Circle.exp (θ z) / 1 := by
            rw [Circle.exp_int_mul_two_pi]
      _ = Circle.exp (θ z) := by simp
      _ = z := hθ.2 z

/-- Helper for Example 4.11: around `Circle.exp x`, one can choose an angle branch whose value at
that point is exactly `x`. -/
theorem exists_angleFunction_through_exp (x : ℝ) :
    ∃ (U : TopologicalSpace.Opens Circle) (hxU : Circle.exp x ∈ U) (θ : U → ℝ),
      IsAngleFunction θ ∧ θ ⟨Circle.exp x, hxU⟩ = x := by
  let U : TopologicalSpace.Opens Circle :=
    ⟨{z : Circle | z ≠ -Circle.exp x}, isOpen_compl_singleton⟩
  have hxU : Circle.exp x ∈ U := by
    -- The deleted point is the antipode of `Circle.exp x`, so the base point stays in the arc.
    change Circle.exp x ≠ -Circle.exp x
    simpa [eq_comm] using Circle.neg_ne_self (Circle.exp x)
  have hmissing : -Circle.exp x ∉ U := by
    -- By construction the antipode is the unique point omitted from `U`.
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
  -- The integer shift is chosen so that the branch hits the prescribed angle value exactly.
  have hshift : θ₀ z₀ - m * (2 * Real.pi) = x := by
    linarith
  simpa [θ] using hshift

/-- Helper for Example 4.11: extend an angle branch by `0` outside its domain so it can be used
as an ambient inverse map on `Circle`. -/
noncomputable def angleFunction_extension {U : TopologicalSpace.Opens Circle} (θ : U → ℝ) :
    Circle → ℝ :=
  let _ : DecidablePred fun z : Circle ↦ z ∈ U := Classical.decPred _
  fun z ↦ if hz : z ∈ U then θ ⟨z, hz⟩ else 0

/-- Helper for Example 4.11: on its domain, the ambient extension of an angle branch agrees with
the branch itself. -/
theorem angleFunction_extension_eq {U : TopologicalSpace.Opens Circle} (θ : U → ℝ)
    {z : Circle} (hz : z ∈ U) :
    angleFunction_extension θ z = θ ⟨z, hz⟩ := by
  simp [angleFunction_extension, hz]

/-- Helper for Example 4.11: a normalized angle branch produces a partial diffeomorphism for the
scaled Fourier map `t ↦ Circle.exp (2 * Real.pi * t)`. -/
noncomputable def fourierAngle_partialDiffeomorph {U : TopologicalSpace.Opens Circle}
    {θ : U → ℝ} (hθ : IsAngleFunction θ) :
    PartialDiffeomorph (𝓘(ℝ)) (𝓡 1) ℝ Circle (∞ : WithTop ℕ∞) where
  toPartialEquiv :=
    { toFun := fun t ↦ Circle.exp (2 * Real.pi * t)
      invFun := fun z ↦ angleFunction_extension θ z / (2 * Real.pi)
      source := (fun t : ℝ ↦ (2 * Real.pi) * t) ⁻¹' (hθ.openImage : Set ℝ)
      target := U
      map_source' := by
        intro y hy
        -- The source is chosen so that the scaled parameter lies in the branch image.
        simpa using hθ.mapsTo_circleExp_openImage hy
      map_target' := by
        intro z hz
        have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        -- On the target, dividing the chosen angle by `2π` lands back in the source interval.
        have hscale :
            (2 * Real.pi) * (angleFunction_extension θ z / (2 * Real.pi)) =
              θ ⟨z, hz⟩ := by
          calc
            (2 * Real.pi) * (angleFunction_extension θ z / (2 * Real.pi))
                = angleFunction_extension θ z := by
                    field_simp [htwo_pi]
            _ = θ ⟨z, hz⟩ := by
                  rw [angleFunction_extension_eq θ hz]
        exact
          (show (2 * Real.pi) * (angleFunction_extension θ z / (2 * Real.pi)) ∈ hθ.openImage from
            ⟨⟨z, hz⟩, hscale.symm⟩)
      left_inv' := by
        intro y hy
        have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        have hyU : Circle.exp ((2 * Real.pi) * y) ∈ U := by
          simpa using hθ.mapsTo_circleExp_openImage hy
        -- The chosen branch evaluates to the scaled angle on the branch image.
        have hbranch :=
          congrArg (fun f : hθ.openImage → ℝ ↦ f ⟨(2 * Real.pi) * y, hy⟩)
            hθ.theta_comp_circleExpOpenImage
        have hbranch_eval :
            angleFunction_extension θ (Circle.exp ((2 * Real.pi) * y)) = (2 * Real.pi) * y := by
          simpa [Function.comp, angleFunction_extension, IsAngleFunction.circleExpOpenImage, hyU]
            using hbranch
        -- Dividing the branch value by `2π` recovers the original parameter.
        apply (div_eq_iff htwo_pi).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hbranch_eval
      right_inv' := by
        intro z hz
        have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        -- On the target, the ambient extension reduces to the original branch, so exponentiating
        -- after dividing by `2π` returns the original circle point.
        calc
          Circle.exp (2 * Real.pi * (angleFunction_extension θ z / (2 * Real.pi)))
              = Circle.exp (angleFunction_extension θ z) := by
                  congr 1
                  field_simp [htwo_pi]
          _ = Circle.exp (θ ⟨z, hz⟩) := by
                rw [angleFunction_extension_eq θ hz]
          _ = z := hθ.2 ⟨z, hz⟩ }
  open_source := by
    -- The source is the preimage of the branch image under the smooth linear phase map.
    simpa using hθ.openImage.2.preimage (continuous_const.mul continuous_id)
  open_target := U.2
  contMDiffOn_toFun := by
    -- The forward map is exactly the smooth Fourier exponential restricted to the source.
    simpa using circle_fourier_exp_contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    -- Near a target point, the ambient inverse is the chosen smooth branch scaled by `1 / 2π`.
    have hθz :
        ContMDiffAt (I := 𝓡 1) (I' := 𝓘(ℝ)) (n := (∞ : WithTop ℕ∞))
          (angleFunction_extension θ) z := by
      rw [← contMDiffAt_subtype_iff
        (U := U)
        (f := angleFunction_extension θ)
        (x := ⟨z, hz⟩)]
      simpa [angleFunction_extension] using hθ.contMDiff ⟨z, hz⟩
    have hscaled :
        ContMDiffAt (I := 𝓡 1) (I' := 𝓘(ℝ)) (n := (∞ : WithTop ℕ∞))
          (fun w : Circle ↦ angleFunction_extension θ w / (2 * Real.pi)) z := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (contMDiffAt_const.mul hθz)
    exact hscaled.contMDiffWithinAt

/-- Example 4.11 (1) (Local Diffeomorphisms): the map `ε : ℝ → S¹` from Example 2.13, written as
`t ↦ Circle.exp (2 * Real.pi * t)`, is a local diffeomorphism. -/
theorem circle_fourier_exp_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ)) (𝓡 1) (∞ : WithTop ℕ∞)
      (fun t : ℝ ↦ Circle.exp (2 * Real.pi * t)) := by
  intro x
  -- Route correction: instead of introducing a separate scaling diffeomorphism on `ℝ`, build the
  -- local inverse directly by dividing the normalized angle branch by `2π`.
  obtain ⟨U, hxU, θ, hθ, hθx⟩ := exists_angleFunction_through_exp (2 * Real.pi * x)
  refine ⟨fourierAngle_partialDiffeomorph hθ, ?_, ?_⟩
  · simpa [fourierAngle_partialDiffeomorph] using
      (show (2 * Real.pi) * x ∈ hθ.openImage from
        ⟨⟨Circle.exp (2 * Real.pi * x), hxU⟩, hθx⟩)
  · intro y _hy
    change Circle.exp (2 * Real.pi * y) = Circle.exp (2 * Real.pi * y)
    rfl

/-- Helper for Example 4.11: on `Fin n → ℝ`, the product real model agrees with the ambient self
model. -/
theorem modelWithCornersSelf_fin_fun_eq_pi (n : ℕ) :
    (𝓘(ℝ, Fin n → ℝ)) = ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)) := by
  -- Both sides are assembled from the identity chart on each coordinate.
  ext x <;>
    simp [ModelWithCorners.pi, modelWithCornersSelf_partialEquiv, PartialEquiv.pi_refl]

/-- Helper for Example 4.11: the finite-product charted-space structure on `Fin n → ℝ` is the
same as the self-charted-space structure. -/
theorem chartedSpaceSelf_fin_fun_eq_pi (n : ℕ) :
    piChartedSpace (fun _ : Fin n ↦ ℝ) (fun _ : Fin n ↦ ℝ) =
      chartedSpaceSelf (Fin n → ℝ) := by
  have hpiRefl :
      OpenPartialHomeomorph.pi (fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ) =
        OpenPartialHomeomorph.refl (Fin n → ℝ) := by
    -- The product of identity charts is again the identity chart.
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

/-- Helper for Example 4.11: the `PiLp` coordinate-forgetting map is smooth for the finite product
real model on `Fin n → ℝ`. -/
theorem euclidean_pi_real_contMDiff_toFun_pi_model (n : ℕ) :
    ContMDiff (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ))) (∞ : WithTop ℕ∞)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)) := by
  -- Rewrite to the self model, where a continuous linear equivalence is automatically smooth.
  rw [chartedSpaceSelf_fin_fun_eq_pi n]
  rw [← modelWithCornersSelf_fin_fun_eq_pi n]
  simpa using
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).contDiff.contMDiff

/-- Helper for Example 4.11: the inverse `PiLp` identification is smooth for the finite product
real model on `Fin n → ℝ`. -/
theorem euclidean_pi_real_contMDiff_invFun_pi_model (n : ℕ) :
    ContMDiff (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ))) (𝓡 n) (∞ : WithTop ℕ∞)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm) := by
  -- The inverse continuous linear equivalence is smooth after the same model identification.
  rw [chartedSpaceSelf_fin_fun_eq_pi n]
  rw [← modelWithCornersSelf_fin_fun_eq_pi n]
  simpa using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm).contDiff.contMDiff

/-- Helper for Example 4.11: the canonical `PiLp` equivalence identifies Euclidean space with the
raw function model carrying the product smooth structure. -/
noncomputable def euclidean_pi_real_product_diffeomorph (n : ℕ) :
    Diffeomorph (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ) (∞ : WithTop ℕ∞) :=
  { toEquiv := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toLinearEquiv.toEquiv
    contMDiff_toFun := euclidean_pi_real_contMDiff_toFun_pi_model n
    contMDiff_invFun := euclidean_pi_real_contMDiff_invFun_pi_model n }

/-- Helper for Example 4.11: the Euclidean-model torus map is the raw coordinatewise Fourier map
precomposed with the canonical `PiLp` diffeomorphism. -/
theorem torus_coordinatewise_fourier_exp_eq_comp (n : ℕ) :
    (fun x : EuclideanSpace ℝ (Fin n) ↦
      (fun i ↦ Circle.exp (2 * Real.pi * x i) : 𝕋^{n})) =
      (fun y : (Fin n → ℝ) ↦ fun i ↦ Circle.exp (2 * Real.pi * y i)) ∘
        (euclidean_pi_real_product_diffeomorph n : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) := by
  -- Both sides evaluate the same coordinates after forgetting the `PiLp` wrapper.
  funext x i
  rfl

/-- Example 4.11 (2) (Local Diffeomorphisms): the map `εⁿ : ℝⁿ → 𝕋ⁿ` from Example 2.13, written
coordinatewise as `x ↦ (fun i ↦ Circle.exp (2 * Real.pi * x i) : 𝕋^{n})`, is a local
diffeomorphism. -/
theorem torus_coordinatewise_fourier_exp_isLocalDiffeomorph (n : ℕ) :
    IsLocalDiffeomorph
      (𝓡 n)
      (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1)
      (∞ : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        (fun i ↦ Circle.exp (2 * Real.pi * x i) : 𝕋^{n})) := by
  let g : (Fin n → ℝ) → 𝕋^{n} := fun y i ↦ Circle.exp (2 * Real.pi * y i)
  have hg :
      IsLocalDiffeomorph
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
        (∞ : WithTop ℕ∞) g := by
    -- The raw product map is a product of the one-dimensional Fourier local diffeomorphisms.
    simpa [g] using
      isLocalDiffeomorph_pi (f := fun _ : Fin n ↦ fun t : ℝ ↦ Circle.exp (2 * Real.pi * t))
        (fun _ : Fin n ↦ circle_fourier_exp_isLocalDiffeomorph)
  have he :
      IsLocalDiffeomorph (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        (∞ : WithTop ℕ∞) (euclidean_pi_real_product_diffeomorph n) :=
    (euclidean_pi_real_product_diffeomorph n).isLocalDiffeomorph
  -- Transport the coordinatewise local diffeomorphism once along the canonical `PiLp`
  -- identification back to `EuclideanSpace`.
  rw [torus_coordinatewise_fourier_exp_eq_comp]
  simpa [g] using isLocalDiffeomorph_comp hg he
