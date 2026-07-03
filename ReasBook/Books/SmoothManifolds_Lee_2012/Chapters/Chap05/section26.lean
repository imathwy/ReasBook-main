import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Immersion

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_5_26 (from Chap05/Sec05_31) -/
open Topology
open scoped ContDiff Manifold
open Manifold

local notation "Plane" => ℝ × ℝ

/-- The point `0` belongs to the parameter interval `(-π, π)` of the figure-eight curve. -/
theorem zero_mem_figureEightCurve_parameterInterval :
    (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
  -- Check the two inequalities in the definition of the open interval separately.
  constructor
  · simpa using neg_lt_zero.mpr Real.pi_pos
  · simpa using Real.pi_pos

/-- Helper for Example 5.26: a nonzero continuous linear map out of the one-dimensional source
`ℝ` is injective. -/
theorem continuousLinearMap_injective_of_ne_zero_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ →L[ℝ] E} (hL : L ≠ 0) :
    Function.Injective L := by
  -- Reduce to the linear-map statement for the simple `ℝ`-module `ℝ`.
  exact LinearMap.injective_of_ne_zero (f := L.toLinearMap) <| by
    intro hzero
    exact hL <| ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun hzero x

/-- The parameter interval `(-π, π)` is nonempty. -/
instance :
    Nonempty (Set.Ioo (-Real.pi) Real.pi) :=
  ⟨⟨0, zero_mem_figureEightCurve_parameterInterval⟩⟩

/-- The open interval `(-π, π)` carries the charted-space structure induced by its inclusion into
`ℝ`. -/
noncomputable instance :
    ChartedSpace ℝ (Set.Ioo (-Real.pi) Real.pi) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
    change ChartedSpace ℝ U
    infer_instance

/-- The open interval `(-π, π)` is a smooth `1`-manifold with the charted-space structure induced
by inclusion into `ℝ`. -/
instance :
    IsManifold (𝓘(ℝ)) ∞
      (Set.Ioo (-Real.pi) Real.pi) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
    change IsManifold (𝓘(ℝ)) ∞ U
    infer_instance

/-- The open interval `(-π, π)` is also a smooth `1`-manifold at the canonical top regularity
level used by `ImmersedSubmanifold`. -/
instance :
    IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞)
      (Set.Ioo (-Real.pi) Real.pi) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  change IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) U
  infer_instance

/-- Helper for Example 5.26: the inclusion of the parameter interval into `ℝ` is a smooth
immersion. -/
theorem figureEightCurve_parameterInterval_subtype_val_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞
      (Subtype.val : Set.Ioo (-Real.pi) Real.pi → ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- Re-express the interval subtype as the canonical open subtype used by `IsImmersion.of_opens`.
  change IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : U → ℝ)
  simpa [U] using Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := ∞) U

/-- Helper for Example 5.26: the inclusion of the parameter interval into `ℝ` is also a smooth
immersion at the canonical regularity level used by `ImmersedSubmanifold`. -/
theorem figureEightCurve_parameterInterval_subtype_val_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (Subtype.val : Set.Ioo (-Real.pi) Real.pi → ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- Re-express the interval subtype as the canonical open owner at the outer regularity level.
  change IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Subtype.val : U → ℝ)
  simpa [U] using
    Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) U

/-- Helper for Example 5.26: once `cos t = 0`, the double-angle identity forces
`cos (2t) = -1`. -/
theorem cos_two_mul_eq_neg_one_of_cos_eq_zero {t : ℝ} (hcos : Real.cos t = 0) :
    Real.cos (2 * t) = -1 := by
  -- First rewrite `sin² t + cos² t = 1` using the vanishing cosine.
  have hsin_sq : Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t, hcos]
  -- Then the double-angle identity collapses to `1 - 2 = -1`.
  rw [Real.cos_two_mul]
  nlinarith [hcos, hsin_sq]

/-- Helper for Example 5.26: the ambient figure-eight derivative never vanishes, so the
ambient parametrization is an immersion on all of `ℝ`. -/
theorem figureEightCurveMap_fderiv_ne_zero_real (t : ℝ) :
    fderiv ℝ figureEightCurveMap t ≠ 0 := by
  have hfderiv :
      fderiv ℝ figureEightCurveMap t =
        (1 : ℝ →L[ℝ] ℝ).smulRight (2 * Real.cos (2 * t), Real.cos t) := by
    -- Rewrite the Fréchet derivative using the explicit one-variable derivative formula.
    simpa using (figureEightCurveMap_hasDerivAt t).hasFDerivAt.fderiv
  intro hzero
  have hvec_zero : (2 * Real.cos (2 * t), Real.cos t) = (0, 0) := by
    -- Evaluating the derivative at `1` recovers the velocity vector.
    have happly : (fderiv ℝ figureEightCurveMap t) 1 = 0 := by
      simp [hzero]
    rw [hfderiv, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul] at happly
    simpa using happly
  have hcoord₁ : 2 * Real.cos (2 * t) = 0 := congrArg Prod.fst hvec_zero
  have hcoord₂ : Real.cos t = 0 := congrArg Prod.snd hvec_zero
  have hcos_two_zero : Real.cos (2 * t) = 0 := by
    nlinarith [hcoord₁]
  -- The double-angle identity contradicts the simultaneous vanishing of both coordinates.
  have hcos_two_neg : Real.cos (2 * t) = -1 :=
    cos_two_mul_eq_neg_one_of_cos_eq_zero hcoord₂
  linarith [hcos_two_zero, hcos_two_neg]

/-- Helper for Example 5.26: the manifold derivative of the ambient figure-eight map is injective
at every real parameter because its Fréchet derivative never vanishes. -/
theorem figureEightCurveMap_mfderiv_injective_real (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t) := by
  -- Reinterpret the manifold derivative on Euclidean space as the usual derivative.
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    exact figureEightCurveMap_fderiv_ne_zero_real t
  -- In one real dimension, every nonzero continuous linear map is injective.
  exact continuousLinearMap_injective_of_ne_zero_real (E := Plane) hNonzero

/-- Helper for Example 5.26: the ambient figure-eight map is smooth as a map of manifolds. -/
theorem figureEightCurveMap_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ figureEightCurveMap := by
  -- On Euclidean spaces, manifold smoothness is equivalent to the ordinary `ContDiff` notion.
  simpa [contMDiff_iff_contDiff] using figureEightCurveMap_contDiff

/-- Helper for Example 5.26: the ambient figure-eight map is also smooth at the outer `ω`
regularity level used by `ImmersedSubmanifold`. -/
theorem figureEightCurveMap_contMDiff_top :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurveMap := by
  -- On Euclidean spaces, the top-order manifold smoothness claim is the ordinary analytic
  -- smoothness statement for the two sine coordinates.
  rw [contMDiff_iff_contDiff]
  simpa [figureEightCurveMap] using
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).prodMk
      (Real.contDiff_sin : ContDiff ℝ (⊤ : WithTop ℕ∞) Real.sin))

/-- Helper for Example 5.26: the ambient figure-eight map is `ω`-smooth at every real
parameter. -/
theorem figureEightCurveMap_contMDiffAt_top (t : ℝ) :
    ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurveMap t := by
  -- The branch-local straightening proof only needs the pointwise smoothness extracted from the
  -- global `ω`-smooth ambient map.
  exact figureEightCurveMap_contMDiff_top.contMDiffAt

/-- Helper for Example 5.26: at every real parameter, at least one scalar coordinate derivative of
the ambient figure-eight map is nonzero. -/
theorem figureEightCurveMap_has_nondegenerate_coordinate (t : ℝ) :
    Real.cos t ≠ 0 ∨ 2 * Real.cos (2 * t) ≠ 0 := by
  -- The two derivative coordinates cannot vanish simultaneously, by the earlier nonvanishing
  -- derivative computation for the ambient curve.
  by_cases hcos : Real.cos t = 0
  · right
    intro hcosTwo
    have hderivZero : fderiv ℝ figureEightCurveMap t = 0 := by
      have hfderiv :
          fderiv ℝ figureEightCurveMap t =
            (1 : ℝ →L[ℝ] ℝ).smulRight (2 * Real.cos (2 * t), Real.cos t) := by
        simpa using (figureEightCurveMap_hasDerivAt t).hasFDerivAt.fderiv
      rw [hfderiv]
      ext
      · simpa [hcosTwo]
      · simpa [hcos]
    exact (figureEightCurveMap_fderiv_ne_zero_real t) hderivZero
  · exact Or.inl hcos

/-- Helper for Example 5.26: the standard inclusion of the real axis into the ambient plane. -/
noncomputable def realAxisInclusion : ℝ → Plane :=
  fun u ↦ (u, 0)

/-- Helper for Example 5.26: the real-axis inclusion is already in the normal-form coordinates for
an immersion. -/
theorem realAxisInclusion_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ realAxisInclusion := by
  -- In the identity charts, the map is exactly the standard inclusion `u ↦ (u, 0)`.
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro u
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (by simpa [realAxisInclusion] using
      ((continuous_id : Continuous fun x : ℝ ↦ x).prodMk continuous_const).continuousAt)
    (ContinuousLinearEquiv.refl ℝ Plane)
    (OpenPartialHomeomorph.refl ℝ)
    (OpenPartialHomeomorph.refl Plane)
  · simpa using Set.mem_univ u
  · simpa using Set.mem_univ (realAxisInclusion u)
  · simpa using (contDiffGroupoid ∞ 𝓘(ℝ)).id_mem_maximalAtlas
  · simpa using (contDiffGroupoid ∞ 𝓘(ℝ, Plane)).id_mem_maximalAtlas
  · intro x hx
    -- The written-in-charts formula is definitionally the standard inclusion.
    simpa [realAxisInclusion]

/-- Helper for Example 5.26: the real-axis inclusion is also an immersion at the canonical top
regularity level. -/
theorem realAxisInclusion_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) realAxisInclusion := by
  -- The same identity-chart argument works verbatim at top regularity.
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro u
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (by simpa [realAxisInclusion] using
      ((continuous_id : Continuous fun x : ℝ ↦ x).prodMk continuous_const).continuousAt)
    (ContinuousLinearEquiv.refl ℝ Plane)
    (OpenPartialHomeomorph.refl ℝ)
    (OpenPartialHomeomorph.refl Plane)
  · simpa using Set.mem_univ u
  · simpa using Set.mem_univ (realAxisInclusion u)
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)).id_mem_maximalAtlas
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, Plane)).id_mem_maximalAtlas
  · intro x hx
    -- The written-in-charts formula is again definitionally the standard inclusion.
    simpa [realAxisInclusion]

/-- Helper for Example 5.26: in the branch where `sin t` is the invertible coordinate, the
ambient figure-eight is the zero-slice of an explicit graph map on the plane. -/
noncomputable def figureEightSecondCoordinateGraph : Plane → Plane :=
  fun p ↦ (p.2 + Real.sin (2 * p.1), Real.sin p.1)

/-- Helper for Example 5.26: in the branch where `sin (2t)` is the invertible coordinate, the
ambient figure-eight is the zero-slice of a symmetric explicit graph map on the plane. -/
noncomputable def figureEightFirstCoordinateGraph : Plane → Plane :=
  fun p ↦ (Real.sin (2 * p.1), p.2 + Real.sin p.1)

/-- Helper for Example 5.26: the global shear that straightens the second-coordinate graph branch
after the scalar inverse chart has recovered the parameter in the second coordinate. -/
noncomputable def figureEightSecondCoordinateShear : Plane ≃ₜ Plane where
  toEquiv :=
    { toFun := fun p ↦ (p.2, p.1 - Real.sin (2 * p.2))
      invFun := fun p ↦ (p.2 + Real.sin (2 * p.1), p.1)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp }
  continuous_toFun := by
    -- The forward shear is assembled from continuous coordinate projections and the sine term.
    exact
      (continuous_snd.prodMk
        (continuous_fst.sub (Real.continuous_sin.comp (continuous_const.mul continuous_snd))))
  continuous_invFun := by
    -- The inverse shear uses the symmetric formula `(u, v) ↦ (v + sin (2u), u)`.
    exact
      ((continuous_snd.add (Real.continuous_sin.comp (continuous_const.mul continuous_fst))).prodMk
        continuous_fst)

/-- Helper for Example 5.26: the global shear that straightens the first-coordinate graph branch
once the scalar inverse chart has recovered the parameter in the first coordinate. -/
noncomputable def figureEightFirstCoordinateShear : Plane ≃ₜ Plane where
  toEquiv :=
    { toFun := fun p ↦ (p.1, p.2 - Real.sin p.1)
      invFun := fun p ↦ (p.1, p.2 + Real.sin p.1)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp }
  continuous_toFun := by
    -- This branch uses the simpler shear `(u, y) ↦ (u, y - sin u)`.
    exact (continuous_fst.prodMk (continuous_snd.sub (Real.continuous_sin.comp continuous_fst)))
  continuous_invFun := by
    -- Its inverse adds back the graph function `sin u` in the transverse coordinate.
    exact (continuous_fst.prodMk (continuous_snd.add (Real.continuous_sin.comp continuous_fst)))

/-- Helper for Example 5.26: the forward second-coordinate shear is `ω`-smooth. -/
theorem figureEightSecondCoordinateShear_contDiff_top :
    ContDiff ℝ (⊤ : WithTop ℕ∞) figureEightSecondCoordinateShear := by
  -- Each component is built from coordinate projections and the analytic map `u ↦ sin (2u)`.
  simpa [figureEightSecondCoordinateShear] using
    ((contDiff_snd : ContDiff ℝ (⊤ : WithTop ℕ∞) fun p : Plane ↦ p.2).prodMk
      (contDiff_fst.sub (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd))))

/-- Helper for Example 5.26: the inverse second-coordinate shear is `ω`-smooth. -/
theorem figureEightSecondCoordinateShear_symm_contDiff_top :
    ContDiff ℝ (⊤ : WithTop ℕ∞) figureEightSecondCoordinateShear.symm := by
  -- The inverse shear uses the symmetric formula `(u, v) ↦ (v + sin (2u), u)`.
  simpa [figureEightSecondCoordinateShear] using
    ((contDiff_snd.add (Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst))).prodMk
      (contDiff_fst : ContDiff ℝ (⊤ : WithTop ℕ∞) fun p : Plane ↦ p.1))

/-- Helper for Example 5.26: the forward first-coordinate shear is `ω`-smooth. -/
theorem figureEightFirstCoordinateShear_contDiff_top :
    ContDiff ℝ (⊤ : WithTop ℕ∞) figureEightFirstCoordinateShear := by
  -- This branch uses the simpler shear `(u, y) ↦ (u, y - sin u)`.
  simpa [figureEightFirstCoordinateShear] using
    ((contDiff_fst : ContDiff ℝ (⊤ : WithTop ℕ∞) fun p : Plane ↦ p.1).prodMk
      (contDiff_snd.sub (Real.contDiff_sin.comp contDiff_fst)))

/-- Helper for Example 5.26: the inverse first-coordinate shear is `ω`-smooth. -/
theorem figureEightFirstCoordinateShear_symm_contDiff_top :
    ContDiff ℝ (⊤ : WithTop ℕ∞) figureEightFirstCoordinateShear.symm := by
  -- Its inverse adds back the graph function `sin u` in the transverse coordinate.
  simpa [figureEightFirstCoordinateShear] using
    ((contDiff_fst : ContDiff ℝ (⊤ : WithTop ℕ∞) fun p : Plane ↦ p.1).prodMk
      (contDiff_snd.add (Real.contDiff_sin.comp contDiff_fst)))

/-- Helper for Example 5.26: the second-coordinate shear sends the normalized graph point
`(sin (2u), u)` to the standard inclusion point `(u, 0)`. -/
theorem figureEightSecondCoordinateShear_straightens (u : ℝ) :
    figureEightSecondCoordinateShear (Real.sin (2 * u), u) = realAxisInclusion u := by
  -- After the scalar inverse chart has recovered `u`, the global shear cancels the graph term.
  simp [figureEightSecondCoordinateShear, realAxisInclusion]

/-- Helper for Example 5.26: the first-coordinate shear sends the normalized graph point
`(u, sin u)` to the standard inclusion point `(u, 0)`. -/
theorem figureEightFirstCoordinateShear_straightens (u : ℝ) :
    figureEightFirstCoordinateShear (u, Real.sin u) = realAxisInclusion u := by
  -- This is the symmetric straightening identity for the other graph branch.
  simp [figureEightFirstCoordinateShear, realAxisInclusion]

/-- Helper for Example 5.26: the second-coordinate graph model is `ω`-smooth on the ambient
plane. -/
theorem figureEightSecondCoordinateGraph_contMDiff_top :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightSecondCoordinateGraph := by
  -- Each coordinate is a sum of analytic coordinate projections and analytic sine compositions.
  rw [contMDiff_iff_contDiff]
  simpa [figureEightSecondCoordinateGraph] using
    ((contDiff_snd.add (Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst))).prodMk
      (Real.contDiff_sin.comp contDiff_fst))

/-- Helper for Example 5.26: the second-coordinate graph model is `ω`-smooth at each ambient
point. -/
theorem figureEightSecondCoordinateGraph_contMDiffAt_top (p : Plane) :
    ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightSecondCoordinateGraph p := by
  -- Later local-chart witnesses use this pointwise form to invoke the inverse function theorem.
  exact figureEightSecondCoordinateGraph_contMDiff_top.contMDiffAt

/-- Helper for Example 5.26: the first-coordinate graph model is `ω`-smooth on the ambient
plane. -/
theorem figureEightFirstCoordinateGraph_contMDiff_top :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightFirstCoordinateGraph := by
  -- The symmetric graph model is built from the same analytic coordinate projections.
  rw [contMDiff_iff_contDiff]
  simpa [figureEightFirstCoordinateGraph] using
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)).prodMk
      (contDiff_snd.add (Real.contDiff_sin.comp contDiff_fst)))

/-- Helper for Example 5.26: the first-coordinate graph model is `ω`-smooth at each ambient
point. -/
theorem figureEightFirstCoordinateGraph_contMDiffAt_top (p : Plane) :
    ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightFirstCoordinateGraph p := by
  -- This is the symmetric pointwise regularity input for the other branch-local chart.
  exact figureEightFirstCoordinateGraph_contMDiff_top.contMDiffAt

/-- Helper for Example 5.26: the second-coordinate graph map recovers the ambient figure-eight on
the real-axis slice `v = 0`. -/
theorem figureEightSecondCoordinateGraph_on_realAxis (t : ℝ) :
    figureEightSecondCoordinateGraph (realAxisInclusion t) = figureEightCurveMap t := by
  -- Setting the transverse coordinate to `0` leaves exactly the figure-eight parametrization.
  simp [figureEightSecondCoordinateGraph, realAxisInclusion, figureEightCurveMap]

/-- Helper for Example 5.26: the first-coordinate graph map also recovers the ambient figure-eight
on the real-axis slice `v = 0`. -/
theorem figureEightFirstCoordinateGraph_on_realAxis (t : ℝ) :
    figureEightFirstCoordinateGraph (realAxisInclusion t) = figureEightCurveMap t := by
  -- The symmetric graph model has the same zero-slice.
  simp [figureEightFirstCoordinateGraph, realAxisInclusion, figureEightCurveMap]

open scoped Manifold in
/-- Helper for Example 5.26: lowering the differentiability index preserves immersions by keeping
the same local chart normal forms. -/
lemma isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {J : ModelWithCorners 𝕜 E' H'} [IsManifold J (⊤ : WithTop ℕ∞) N]
    {n m : WithTop ℕ∞} {f : M → N} (hmn : m ≤ n)
    (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Keep the same global complement and the same pointwise chart presentation.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := N) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Example 5.26: the ambient figure-eight map is a smooth immersion on `ℝ`. -/
theorem figureEightCurveMap_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ figureEightCurveMap := by
  -- The global immersion criterion reduces the claim to injectivity of the manifold derivative at
  -- every parameter value.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv figureEightCurveMap_contMDiff).2 ?_
  intro t
  exact figureEightCurveMap_mfderiv_injective_real t

/-- Helper for Example 5.26: on the ambient Euclidean spaces, the same figure-eight map is an
immersion at the canonical outer regularity level used by `ImmersedSubmanifold`. -/
theorem figureEightCurveMap_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurveMap := by
  -- Route correction: the tempting derivative-criterion proof does not typecheck here, because
  -- the available repo theorem `Manifold.is_immersion_iff_forall_injective_mfderiv` is still
  -- specialized to the lower `∞` regularity, while this target lives at the outer `ω` level.
  -- TODO: follow the branch-local straightening route at order `ω`: when `Real.cos t ≠ 0` or
  -- `2 * Real.cos (2 * t) ≠ 0`, build a restricted source chart and an explicit codomain chart
  -- from `ContDiffAt.toOpenPartialHomeomorph`, then apply
  -- `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt` pointwise and package globally.
  sorry

/-- Helper for Example 5.26: the restricted parametrization is the ambient figure-eight map
precomposed with the interval inclusion. -/
theorem figureEightCurve_eq_ambient_comp_subtype_val :
    figureEightCurve = figureEightCurveMap ∘
      (Subtype.val : Set.Ioo (-Real.pi) Real.pi → ℝ) := by
  -- Both sides evaluate the same ambient formula on the subtype parameter.
  rfl

/-- The figure-eight parametrization `β : (-π, π) → ℝ²` is a smooth immersion. -/
-- Proof sketch: view `figureEightCurve` as the restriction of the smooth ambient map
-- `figureEightCurveMap`; the derivative criterion from Example 4.19 shows that the differential is
-- injective at every parameter value, which yields `Manifold.IsImmersion`.
theorem figureEightCurve_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ figureEightCurve := by
  -- Compose the ambient immersion with the open-interval inclusion of the parameter domain.
  simpa [figureEightCurve, Function.comp] using
    Manifold.IsImmersion.comp figureEightCurveMap_isImmersion
      figureEightCurve_parameterInterval_subtype_val_isImmersion

/-- Helper for Example 5.26: the figure-eight immersion is also available at the canonical
top regularity level used by `ImmersedSubmanifold`. -/
theorem figureEightCurve_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) (⊤ : WithTop ℕ∞) figureEightCurve := by
  -- Route correction: the exact close-out line from the `∞` proof is blocked for the same reason:
  -- the imported immersion-composition theorem is only available at order `∞`.
  -- TODO: after the ambient `ω`-immersion is proved, either add the matching `ω`-level
  -- composition/restriction bridge for open inclusions or prove this restricted case directly by
  -- reusing the ambient chart witness and restricting its domain chart to `(-π, π)`.
  sorry

/-- Example 5.26: the figure-eight curve, equipped with the smooth structure coming from the
global parametrization `β : (-π, π) → ℝ²`, defines an immersed submanifold of `ℝ²`. -/
noncomputable def figureEightCurveImmersedSubmanifold :
    ImmersedSubmanifold 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) :=
  figureEightCurve_isImmersion_top.toImmersedSubmanifold figureEightCurve_injective

/-- The underlying subset of the immersed figure-eight is the image of the parametrization
`figureEightCurve`. -/
-- Proof sketch: unfold `ImmersedSubmanifold.carrier` and the definition of
-- `figureEightCurveImmersedSubmanifold`.
theorem figureEightCurveImmersedSubmanifold_carrier :
    figureEightCurveImmersedSubmanifold.carrier = Set.range figureEightCurve := by
  -- Unfold the owner: its carrier is definitionally the range of the chosen inclusion.
  rfl
