import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

local instance circleGroupLieAlgebraSeminormedAddCommGroup :
    SeminormedAddCommGroup (GroupLieAlgebra (𝓡 1) Circle) :=
  inferInstanceAs (SeminormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))

local instance circleGroupLieAlgebraNormedAddCommGroup :
    NormedAddCommGroup (GroupLieAlgebra (𝓡 1) Circle) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))

local instance circleGroupLieAlgebraNormedSpace :
    NormedSpace ℝ (GroupLieAlgebra (𝓡 1) Circle) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))

/-- Helper for Problem 3-4: the identity tangent fiber of `Circle` is finite-dimensional. -/
local instance circleGroupLieAlgebraFiniteDimensional :
    FiniteDimensional ℝ (GroupLieAlgebra (𝓡 1) Circle) :=
  inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1)))

/-- Helper for Problem 3-4: the identity tangent fiber carries the standard self-charted manifold
structure. -/
local instance circleIdentityFiberChartedSpace :
    ChartedSpace (TangentSpace (𝓡 1) (1 : Circle)) (WithLp 2 (Fin 1 → ℝ)) :=
  by
    change ChartedSpace (WithLp 2 (Fin 1 → ℝ)) (WithLp 2 (Fin 1 → ℝ))
    exact chartedSpaceSelf _

/- The primary domain here is the tangent bundle of the Lie group `Circle`. The canonical owner for
the identity fiber is `GroupLieAlgebra (𝓡 1) Circle = TangentSpace (𝓡 1) (1 : Circle)`, and the
left-translation trivialization should land in `Circle × GroupLieAlgebra (𝓡 1) Circle`. The
one-dimensional identification with `ℝ` is a downstream bridge, obtained by differentiating the
canonical chart at `1 : Circle` and then using the standard model-space equivalence
`EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ`.
-/

/-- The tangent fiber at the identity of `Circle` is canonically one-dimensional, hence
continuously linearly equivalent to `ℝ`. -/
def circleTangentFiberContinuousLinearEquiv :
    GroupLieAlgebra (𝓡 1) Circle ≃L[ℝ] ℝ :=
  ((((mdifferentiable_chart (1 : Circle)).mfderiv
        (mem_chart_source (EuclideanSpace ℝ (Fin 1)) (1 : Circle))).trans
      (NormedSpace.fromTangentSpace
        ((chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)) (1 : Circle)))).trans
    ((EuclideanSpace.equiv (Fin 1) ℝ).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)))

/-- The tangent fiber at the identity of `Circle` is canonically one-dimensional, hence
diffeomorphic to `ℝ`. -/
def circleTangentFiberDiffeomorph :
    GroupLieAlgebra (𝓡 1) Circle ≃ₘ[ℝ] ℝ :=
  circleTangentFiberContinuousLinearEquiv.toDiffeomorph

/-- Helper for Problem 3-4: translating a tangent vector to the identity and back by left
multiplication recovers the original tangent vector. -/
lemma tangentBundle_circle_prodLie_left_inv (p : TangentBundle (𝓡 1) Circle) :
    (⟨p.1, mulInvariantVectorField (mfderiv% (p.1⁻¹ * ·) p.1 p.2) p.1⟩ :
      TangentBundle (𝓡 1) Circle) = p := by
  rcases p with ⟨g, v⟩
  -- Differentiate the identity `(fun x ↦ g * (g⁻¹ * x)) = id` at `g`.
  simp [mulInvariantVectorField]
  have M : minSmoothness ℝ 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hcomp :
      mfderiv% ((fun x ↦ g * x) ∘ fun x ↦ g⁻¹ * x) g =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 1) g) := by
    have hId : ((fun x ↦ g * x) ∘ fun x ↦ g⁻¹ * x) = id := by
      ext x
      simp
    rw [hId, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := 𝓡 1) _
      (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
      (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at hcomp
  have hpoint : g⁻¹ * g = (1 : Circle) := by
    simp
  rw [hpoint] at hcomp
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg
      (fun f : TangentSpace (𝓡 1) g →L[ℝ] TangentSpace (𝓡 1) g ↦ f v)
      hcomp

/-- Helper for Problem 3-4: left-translating a Lie algebra vector and pulling it back again
returns the original Lie algebra vector. -/
lemma tangentBundle_circle_prodLie_right_inv (q : Circle × GroupLieAlgebra (𝓡 1) Circle) :
    (q.1, mfderiv% (q.1⁻¹ * ·) q.1 (mulInvariantVectorField q.2 q.1)) = q := by
  rcases q with ⟨g, v⟩
  -- Differentiate the identity `(fun x ↦ g⁻¹ * (g * x)) = id` at `1`.
  ext
  · rfl
  · simp [mulInvariantVectorField]
    have M : minSmoothness ℝ 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    have hcomp :
        mfderiv% ((fun x ↦ g⁻¹ * x) ∘ fun x ↦ g * x) (1 : Circle) =
          ContinuousLinearMap.id ℝ (TangentSpace (𝓡 1) (1 : Circle)) := by
      have hId : ((fun x ↦ g⁻¹ * x) ∘ fun x ↦ g * x) = id := by
        ext x
        simp
      rw [hId, id_eq, mfderiv_id]
    rw [mfderiv_comp (I' := 𝓡 1) _
        (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
        (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at hcomp
    have hpoint : g * (1 : Circle) = g := by
      simp
    rw [hpoint] at hcomp
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg
        (fun f : TangentSpace (𝓡 1) (1 : Circle) →L[ℝ] TangentSpace (𝓡 1) (1 : Circle) ↦
          f v)
        hcomp

/-- Helper for Problem 3-4: the left-translation trivialization map
`(g, w) ↦ d(L_g)_1 w` is smooth. -/
lemma contMDiff_tangentBundle_circle_prodLie_invFun :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle))) (𝓡 1).tangent ∞
      (fun q : Circle × GroupLieAlgebra (𝓡 1) Circle ↦
        (⟨q.1, mulInvariantVectorField q.2 q.1⟩ : TangentBundle (𝓡 1) Circle)) := by
  let fg : Circle × GroupLieAlgebra (𝓡 1) Circle → TangentBundle (𝓡 1) Circle :=
    fun q ↦ (⟨q.1, 0⟩ : TangentBundle (𝓡 1) Circle)
  -- The zero vector over the moving base point is the zero section pulled back along `Prod.fst`.
  have sfg :
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle))) (𝓡 1).tangent ∞ fg := by
    simpa [fg, Bundle.zeroSection] using
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 1))).comp contMDiff_fst)
  let fv : Circle × GroupLieAlgebra (𝓡 1) Circle → TangentBundle (𝓡 1) Circle :=
    fun q ↦ (⟨1, q.2⟩ : TangentBundle (𝓡 1) Circle)
  -- A vector in the identity fiber is smooth as a map into the total space because the base is
  -- constant and the chart at `1` identifies the fiber linearly with the model fiber.
  have sfv :
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle))) (𝓡 1).tangent ∞ fv := by
    intro q0
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_const, ?_⟩
    let e := trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (1 : Circle)
    let h1 : (1 : Circle) ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (1 : Circle)
    let L : TangentSpace (𝓡 1) (1 : Circle) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      (e.linearEquivAt ℝ (1 : Circle) h1).toContinuousLinearMap
    simpa [fv, e, L, h1] using (L.contMDiffAt.comp q0 contMDiffAt_snd)
  let F₁ : Circle × GroupLieAlgebra (𝓡 1) Circle →
      TangentBundle (𝓡 1) Circle × TangentBundle (𝓡 1) Circle := fun q ↦ (fg q, fv q)
  have S₁ :
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle)))
        ((𝓡 1).tangent.prod (𝓡 1).tangent) ∞ F₁ :=
    sfg.prodMk sfv
  let F₂ : TangentBundle (𝓡 1) Circle × TangentBundle (𝓡 1) Circle →
      TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle) :=
    (equivTangentBundleProd (𝓡 1) Circle (𝓡 1) Circle).symm
  have S₂ :
      ContMDiff ((𝓡 1).tangent.prod (𝓡 1).tangent) (((𝓡 1).prod (𝓡 1)).tangent) ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle) → TangentBundle (𝓡 1) Circle :=
    tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) (fun p : Circle × Circle ↦ p.1 * p.2)
  have S₃ : ContMDiff (((𝓡 1).prod (𝓡 1)).tangent) (𝓡 1).tangent ∞ F₃ := by
    -- This is the tangent map of circle multiplication.
    apply ContMDiff.contMDiff_tangentMap
    · simpa using contMDiff_mul (𝓡 1) ∞
    · simp
  let S := (S₃.comp S₂).comp S₁
  have hcomp :
      ((F₃ ∘ F₂) ∘ F₁) =
        (fun q : Circle × GroupLieAlgebra (𝓡 1) Circle ↦
          (⟨q.1, mulInvariantVectorField q.2 q.1⟩ : TangentBundle (𝓡 1) Circle)) := by
    funext q
    -- The tangent vector `(0, q.2)` at `(q.1, 1)` is exactly the tangent of the slice
    -- `y ↦ (q.1, y)`, so the tangent map of multiplication reduces to `d(L_q.1)_1 q.2`.
    calc
      ((F₃ ∘ F₂) ∘ F₁) q
          = tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) (fun p : Circle × Circle ↦ p.1 * p.2)
              (⟨(q.1, 1), (0, q.2)⟩ : TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) := by
            rfl
      _ = tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) (fun p : Circle × Circle ↦ p.1 * p.2)
            (tangentMap (𝓡 1) ((𝓡 1).prod (𝓡 1)) (fun y : Circle ↦ (q.1, y))
              (⟨1, q.2⟩ : TangentBundle (𝓡 1) Circle)) := by
            rw [tangentMap_prod_right]
      _ = tangentMap (𝓡 1) (𝓡 1)
            (((fun p : Circle × Circle ↦ p.1 * p.2) ∘ fun y : Circle ↦ (q.1, y)))
            (⟨1, q.2⟩ : TangentBundle (𝓡 1) Circle) := by
            simpa using
              (congrArg
                (fun h : TangentBundle (𝓡 1) Circle → TangentBundle (𝓡 1) Circle ↦
                  h (⟨1, q.2⟩ : TangentBundle (𝓡 1) Circle))
                (tangentMap_comp
                  (((contMDiff_mul (𝓡 1) ∞).mdifferentiable (by simp)))
                  (mdifferentiable_const.prodMk mdifferentiable_id))).symm
      _ = tangentMap (𝓡 1) (𝓡 1) (fun x : Circle ↦ q.1 * x)
            (⟨1, q.2⟩ : TangentBundle (𝓡 1) Circle) := by
            rfl
      _ = (⟨q.1, mulInvariantVectorField q.2 q.1⟩ : TangentBundle (𝓡 1) Circle) := by
            apply Bundle.TotalSpace.ext
            · simp [tangentMap]
            · exact HEq.rfl
  simpa [S, hcomp] using S

/-- Helper for Problem 3-4: the pullback of a tangent vector by
`(g, h) ↦ g⁻¹ * h` gives a smooth map from `TS¹` to `S¹ × T₁S¹`. -/
lemma contMDiff_tangentBundle_circle_prodLie_toFun :
    ContMDiff (𝓡 1).tangent ((𝓡 1).prod 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle))) ∞
      (fun p : TangentBundle (𝓡 1) Circle ↦
        ((p.1, mfderiv% (p.1⁻¹ * ·) p.1 p.2) : Circle × TangentSpace (𝓡 1) (1 : Circle))) := by
  let fg : TangentBundle (𝓡 1) Circle → TangentBundle (𝓡 1) Circle :=
    fun p ↦ (⟨p.1, 0⟩ : TangentBundle (𝓡 1) Circle)
  -- The zero vector over the bundle projection is the zero section pulled back along `proj`.
  have sfg : ContMDiff (𝓡 1).tangent (𝓡 1).tangent ∞ fg := by
    simpa [fg, Bundle.zeroSection] using
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 1))).comp
        (Bundle.contMDiff_proj (TangentSpace (𝓡 1))))
  let F₁ : TangentBundle (𝓡 1) Circle →
      TangentBundle (𝓡 1) Circle × TangentBundle (𝓡 1) Circle := fun p ↦ (fg p, p)
  have S₁ : ContMDiff (𝓡 1).tangent ((𝓡 1).tangent.prod (𝓡 1).tangent) ∞ F₁ :=
    sfg.prodMk contMDiff_id
  let F₂ : TangentBundle (𝓡 1) Circle × TangentBundle (𝓡 1) Circle →
      TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle) :=
    (equivTangentBundleProd (𝓡 1) Circle (𝓡 1) Circle).symm
  have S₂ :
      ContMDiff ((𝓡 1).tangent.prod (𝓡 1).tangent) (((𝓡 1).prod (𝓡 1)).tangent) ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let diffMap : Circle × Circle → Circle := fun z ↦ z.1⁻¹ * z.2
  have hdiff : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 1) ∞ diffMap := by
    -- The difference map is the product of inversion and multiplication.
    simpa [diffMap] using
      (contMDiff_mul (𝓡 1) ∞).comp
        (((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd)
  let F₃ : TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle) → TangentBundle (𝓡 1) Circle :=
    tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) diffMap
  have S₃ : ContMDiff (((𝓡 1).prod (𝓡 1)).tangent) (𝓡 1).tangent ∞ F₃ := by
    -- This is the tangent map of the smooth difference map.
    apply ContMDiff.contMDiff_tangentMap
    · exact hdiff
    · simp
  let S := (S₃.comp S₂).comp S₁
  have hcore :
      ((F₃ ∘ F₂) ∘ F₁) =
        (fun p : TangentBundle (𝓡 1) Circle ↦
          (⟨1, mfderiv% (p.1⁻¹ * ·) p.1 p.2⟩ : TangentBundle (𝓡 1) Circle)) := by
    funext p
    -- The tangent vector `(0, p.2)` along the second factor is the tangent of the slice
    -- `y ↦ (p.1, y)`, so differentiating the difference map yields `d(L_{p.1⁻¹})_p.1 p.2`.
    calc
      ((F₃ ∘ F₂) ∘ F₁) p
          = tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) diffMap
              (⟨(p.1, p.1), (0, p.2)⟩ : TangentBundle ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) := by
            rfl
      _ = tangentMap ((𝓡 1).prod (𝓡 1)) (𝓡 1) diffMap
            (tangentMap (𝓡 1) ((𝓡 1).prod (𝓡 1)) (fun y : Circle ↦ (p.1, y)) p) := by
            rw [tangentMap_prod_right]
      _ = tangentMap (𝓡 1) (𝓡 1) (diffMap ∘ fun y : Circle ↦ (p.1, y)) p := by
            simpa using
              (congrArg
                (fun h : TangentBundle (𝓡 1) Circle → TangentBundle (𝓡 1) Circle ↦ h p)
                (tangentMap_comp
                  (hdiff.mdifferentiable (by simp))
                  (mdifferentiable_const.prodMk mdifferentiable_id))).symm
      _ = tangentMap (𝓡 1) (𝓡 1) (fun y : Circle ↦ p.1⁻¹ * y) p := by
            rfl
      _ = (⟨1, mfderiv% (p.1⁻¹ * ·) p.1 p.2⟩ : TangentBundle (𝓡 1) Circle) := by
            apply Bundle.TotalSpace.ext
            · simp [tangentMap, diffMap]
            · exact HEq.rfl
  have hcoreSmooth :
      ContMDiff (𝓡 1).tangent (𝓡 1).tangent ∞
        (fun p : TangentBundle (𝓡 1) Circle ↦
          (⟨1, mfderiv% (p.1⁻¹ * ·) p.1 p.2⟩ : TangentBundle (𝓡 1) Circle)) := by
    simpa [S, hcore] using S
  have hfiber :
      ContMDiff (𝓡 1).tangent 𝓘(ℝ, TangentSpace (𝓡 1) (1 : Circle)) ∞
        (fun p : TangentBundle (𝓡 1) Circle ↦
          (mfderiv% (p.1⁻¹ * ·) p.1 p.2 : TangentSpace (𝓡 1) (1 : Circle))) := by
    intro p0
    have hG0 := hcoreSmooth p0
    rw [Bundle.contMDiffAt_totalSpace] at hG0
    -- The target tangent vectors all live over the constant base point `1`, so undoing the
    -- chart-linear identification at `1` recovers the fiber component smoothly.
    let e := trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (1 : Circle)
    let h1 : (1 : Circle) ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (1 : Circle)
    let Lsymm : EuclideanSpace ℝ (Fin 1) →L[ℝ] TangentSpace (𝓡 1) (1 : Circle) :=
      (e.linearEquivAt ℝ (1 : Circle) h1).symm.toContinuousLinearMap
    have hcoord :
        (fun x : TangentBundle (𝓡 1) Circle ↦
          Lsymm ((e (⟨1, mfderiv% (x.1⁻¹ * ·) x.1 x.2⟩ : TangentBundle (𝓡 1) Circle)).2)) =
          fun x : TangentBundle (𝓡 1) Circle ↦ mfderiv% (x.1⁻¹ * ·) x.1 x.2 := by
      funext x
      simpa [e, Lsymm, h1]
    convert (Lsymm.contMDiffAt.comp p0 hG0.2) using 1
    exact hcoord.symm
  -- Combine the smooth base projection with the smooth identity-fiber coordinate.
  exact (Bundle.contMDiff_proj (TangentSpace (𝓡 1))).prodMk hfiber

/-- The tangent bundle of the circle is canonically trivialized by left translation. -/
def tangentBundle_circle_diffeomorph_prodLie :
    TangentBundle (𝓡 1) Circle ≃ₘ⟮(𝓡 1).tangent,
      (𝓡 1).prod 𝓘(ℝ, GroupLieAlgebra (𝓡 1) Circle)⟯
      Circle × GroupLieAlgebra (𝓡 1) Circle where
  toEquiv :=
    { toFun := fun p ↦ (p.1, mfderiv% (p.1⁻¹ * ·) p.1 p.2)
      invFun := fun q ↦ ⟨q.1, mulInvariantVectorField q.2 q.1⟩
      left_inv := tangentBundle_circle_prodLie_left_inv
      right_inv := tangentBundle_circle_prodLie_right_inv }
  contMDiff_toFun := contMDiff_tangentBundle_circle_prodLie_toFun
  contMDiff_invFun := contMDiff_tangentBundle_circle_prodLie_invFun

-- Proof sketch: first use the Lie-group trivialization `TG ≃ G × T₁G` from
-- `tangentBundle_circle_diffeomorph_prodLie`, then identify the one-dimensional Lie algebra
-- `GroupLieAlgebra (𝓡 1) Circle = T₁S¹` with `ℝ` using `circleTangentFiberDiffeomorph`.
/-- Problem 3-4: the tangent bundle of the unit circle is diffeomorphic to `S¹ × ℝ`. -/
def tangentBundle_unitCircle_diffeomorph :
    TangentBundle (𝓡 1) Circle ≃ₘ⟮(𝓡 1).tangent, (𝓡 1).prod 𝓘(ℝ, ℝ)⟯ Circle × ℝ :=
  let e :
      GroupLieAlgebra (𝓡 1) Circle ≃ₘ⟮𝓘(ℝ, GroupLieAlgebra (𝓡 1) Circle), 𝓘(ℝ, ℝ)⟯ ℝ :=
    circleTangentFiberDiffeomorph
  let he := e.contMDiff
  let hsymm := e.symm.contMDiff
  tangentBundle_circle_diffeomorph_prodLie.trans <|
    { toEquiv := (Equiv.refl Circle).prodCongr e.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (he.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (hsymm.comp contMDiff_snd) }
