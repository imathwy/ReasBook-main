import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_12.Problem_2_6
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_14.Proposition_3_9
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_55.Definition_8_55_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_55.Definition_8_55_extra_2

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "P2" => puncturedEuclidean 1

-- Domain sampling pass:
-- * primary domain: local and orthonormal frames on Euclidean manifolds and open submanifolds;
-- * relevant owner declarations checked before refinement:
--   `NormedSpace.fromTangentSpace`, `IsLocalFrameOn`, `VectorField.OrthonormalOn`,
--   and `IsOrthonormalFrameOn`;
-- * source-facing layer: the intrinsic punctured-plane vector fields `example_8_12_E1` and
--   `example_8_12_E2`;
-- * core/canonical layer: `IsLocalFrameOn` on the punctured manifold itself;
-- * bridge/view layer: a private pushed-forward ambient frame on `P2 ⊆ ℝ²`, used only to connect
--   the intrinsic pair to the chapter's ambient-subset owner `IsOrthonormalFrameOn`.
--
-- Semantic recall note: `lean_leansearch` confirms the local frame owners
-- `IsLocalFrameOn`/`IsOrthonormalFrameOn`; this item uses the project-local owner
-- `puncturedEuclidean` for the punctured plane together with the canonical tangent-space
-- identification on `ℝ²`.

/-- The ambient coordinate vector for `E₁ = (x / r) ∂/∂x + (y / r) ∂/∂y` at a punctured-plane
point. -/
private def example_8_12_E1Ambient (p : P2) : TangentSpace (𝓡 2) (p : R2) :=
  (fromTangentSpace (p : R2)).symm !₂[(p : R2) 0 / ‖(p : R2)‖, (p : R2) 1 / ‖(p : R2)‖]

/-- The vector field `E₁ = (x / r) ∂/∂x + (y / r) ∂/∂y` on the punctured plane. -/
def example_8_12_E1 (p : P2) : TangentSpace (𝓡 2) p :=
  (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p).inverse (example_8_12_E1Ambient p)

/-- On the punctured plane, `example_8_12_E1` has the coordinate formula from equation (8.3)
after pushing forward along the inclusion `P2 ↪ ℝ²`. -/
theorem fromTangentSpace_example_8_12_E1 (p : P2) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E1 p)) =
      !₂[(p : R2) 0 / ‖(p : R2)‖, (p : R2) 1 / ‖(p : R2)‖] := by
  -- Push `example_8_12_E1` forward through the inclusion, then read off its Euclidean
  -- coordinates with `fromTangentSpace`.
  have hpush :
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E1 p) =
        example_8_12_E1Ambient p := by
    simpa [example_8_12_E1] using
      (mfderiv_open_subset_inclusion_isInvertible P2 p).self_apply_inverse
        (example_8_12_E1Ambient p)
  simpa [example_8_12_E1Ambient] using congrArg (fromTangentSpace (p : R2)) hpush

/-- The ambient coordinate vector for `E₂ = -(y / r) ∂/∂x + (x / r) ∂/∂y` at a punctured-plane
point. -/
private def example_8_12_E2Ambient (p : P2) : TangentSpace (𝓡 2) (p : R2) :=
  (fromTangentSpace (p : R2)).symm !₂[-((p : R2) 1 / ‖(p : R2)‖), (p : R2) 0 / ‖(p : R2)‖]

/-- The vector field `E₂ = -(y / r) ∂/∂x + (x / r) ∂/∂y` on the punctured plane. -/
def example_8_12_E2 (p : P2) : TangentSpace (𝓡 2) p :=
  (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p).inverse (example_8_12_E2Ambient p)

/-- On the punctured plane, `example_8_12_E2` has the coordinate formula from equation (8.3)
after pushing forward along the inclusion `P2 ↪ ℝ²`. -/
theorem fromTangentSpace_example_8_12_E2 (p : P2) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E2 p)) =
      !₂[-((p : R2) 1 / ‖(p : R2)‖), (p : R2) 0 / ‖(p : R2)‖] := by
  -- Push `example_8_12_E2` forward through the inclusion, then read off its Euclidean
  -- coordinates with `fromTangentSpace`.
  have hpush :
      mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E2 p) =
        example_8_12_E2Ambient p := by
    simpa [example_8_12_E2] using
      (mfderiv_open_subset_inclusion_isInvertible P2 p).self_apply_inverse
        (example_8_12_E2Ambient p)
  simpa [example_8_12_E2Ambient] using congrArg (fromTangentSpace (p : R2)) hpush

/-- Helper for the punctured-plane frame example: the radial ambient vector field with coordinates
`(x / ‖(x, y)‖, y / ‖(x, y)‖)`. -/
private def example_8_12_radialAmbientField (x : R2) : TangentSpace (𝓡 2) x :=
  (fromTangentSpace x).symm !₂[x 0 / ‖x‖, x 1 / ‖x‖]

/-- Helper for the punctured-plane frame example: the angular ambient vector field with coordinates
`(-(y / ‖(x, y)‖), x / ‖(x, y)‖)`. -/
private def example_8_12_angularAmbientField (x : R2) : TangentSpace (𝓡 2) x :=
  (fromTangentSpace x).symm !₂[-(x 1 / ‖x‖), x 0 / ‖x‖]

/-- Helper for the punctured-plane frame example: each coordinate ratio `x i / ‖x‖` is smooth
away from the origin. -/
private theorem example_8_12_coordinateRatio_contDiffOn (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : R2 ↦ x i / ‖x‖) (P2 : Set R2) := by
  -- Divide the smooth coordinate projection by the smooth norm, using that the norm never
  -- vanishes on the punctured plane.
  have hcoord : ContDiffOn ℝ ∞ (fun x : R2 ↦ x i) (P2 : Set R2) := by
    simpa using
      ((contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 2 ↦ ℝ) (i := i)) :
        ContDiff ℝ ∞ (fun x : R2 ↦ x i)).contDiffOn
  have hnorm : ContDiffOn ℝ ∞ (fun x : R2 ↦ ‖x‖) (P2 : Set R2) := by
    simpa using
      (contDiff_id.contDiffOn.norm (𝕜 := ℝ) fun x hx ↦ hx)
  exact hcoord.div hnorm fun x hx ↦ norm_ne_zero_iff.mpr hx

/-- Helper for the punctured-plane frame example: the radial ambient field is smooth on
`ℝ² \ {0}`. -/
private theorem example_8_12_radialAmbientField_contMDiffOn :
    ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞ (T% example_8_12_radialAmbientField) (P2 : Set R2) := by
  -- Reduce manifold smoothness to the coordinate map on the model vector space.
  rw [contMDiffOn_vectorSpace_iff_contDiffOn]
  refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
  intro i
  fin_cases i
  · simpa [example_8_12_radialAmbientField] using example_8_12_coordinateRatio_contDiffOn 0
  · simpa [example_8_12_radialAmbientField] using example_8_12_coordinateRatio_contDiffOn 1

/-- Helper for the punctured-plane frame example: the angular ambient field is smooth on
`ℝ² \ {0}`. -/
private theorem example_8_12_angularAmbientField_contMDiffOn :
    ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞ (T% example_8_12_angularAmbientField) (P2 : Set R2) := by
  -- Reduce manifold smoothness to the coordinate map on the model vector space.
  rw [contMDiffOn_vectorSpace_iff_contDiffOn]
  refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
  intro i
  fin_cases i
  · simpa [example_8_12_angularAmbientField] using (example_8_12_coordinateRatio_contDiffOn 1).neg
  · simpa [example_8_12_angularAmbientField] using example_8_12_coordinateRatio_contDiffOn 0

/-- Ambient representative of the pushed-forward intrinsic pair `(E₁, E₂)`, used to express
Example 8.12 through the subset owner `IsOrthonormalFrameOn` on `P2 ⊆ ℝ²`. -/
def example_8_12_pushforwardFrame (i : Fin 2) (x : R2) : TangentSpace (𝓡 2) x :=
  if hx : x ≠ 0 then
    let p : P2 := ⟨x, hx⟩
    mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p ((!₂[example_8_12_E1, example_8_12_E2] i) p)
  else
    0

/-- For Example 8.12, at each point of the punctured plane, the pushed-forward pair `(E₁, E₂)` is
orthonormal in ambient Euclidean coordinates. -/
theorem example_8_12_orthonormal (p : P2) :
    Orthonormal ℝ !₂[
      fromTangentSpace (p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E1 p)),
      fromTangentSpace (p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E2 p))
    ] := by
  -- Rewrite both fields into explicit Euclidean coordinates and check the `2 × 2` inner-product
  -- table directly.
  have hnorm : ‖(p : R2)‖ ≠ 0 := norm_ne_zero_iff.mpr p.property
  have hnormSq :
      ‖(p : R2)‖ ^ 2 = ((p : R2) 0) ^ 2 + ((p : R2) 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (p : R2)
  rw [fromTangentSpace_example_8_12_E1, fromTangentSpace_example_8_12_E2, orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [Real.inner_apply]
    field_simp [hnorm]
    have hsq0 : |(p : R2) 0| ^ 2 = ((p : R2) 0) ^ 2 := by rw [sq_abs]
    have hsq1 : |(p : R2) 1| ^ 2 = ((p : R2) 1) ^ 2 := by rw [sq_abs]
    nlinarith [hnormSq, hsq0, hsq1]
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [Real.inner_apply]
    field_simp [hnorm]
    ring
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [Real.inner_apply]
    field_simp [hnorm]
    ring
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [Real.inner_apply]
    field_simp [hnorm]
    have hsq0 : |(p : R2) 0| ^ 2 = ((p : R2) 0) ^ 2 := by rw [sq_abs]
    have hsq1 : |(p : R2) 1| ^ 2 = ((p : R2) 1) ^ 2 := by rw [sq_abs]
    nlinarith [hnormSq, hsq0, hsq1]

/-- Helper for the punctured-plane frame example: on the punctured plane, the pushed-forward
frame is the explicit
ambient radial/angular pair. -/
private theorem example_8_12_pushforwardFrame_eq_ambient
    (i : Fin 2) {x : R2} (hx : x ∈ (P2 : Set R2)) :
    example_8_12_pushforwardFrame i x =
      !₂[example_8_12_radialAmbientField, example_8_12_angularAmbientField] i x := by
  -- Compare the two ambient fields after reading both sides in Euclidean coordinates.
  let p : P2 := ⟨x, hx⟩
  have hx0 : x ≠ 0 := hx
  fin_cases i
  · apply (fromTangentSpace x).injective
    simpa [example_8_12_pushforwardFrame, example_8_12_radialAmbientField, p, hx0]
      using fromTangentSpace_example_8_12_E1 p
  · apply (fromTangentSpace x).injective
    simpa [example_8_12_pushforwardFrame, example_8_12_angularAmbientField, p, hx0]
      using fromTangentSpace_example_8_12_E2 p

/-- Helper for the punctured-plane frame example: each pushed-forward ambient field is smooth on
`ℝ² \ {0}`. -/
private theorem example_8_12_pushforwardFrame_contMDiffOn (i : Fin 2) :
    ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞ (T% (example_8_12_pushforwardFrame i)) (P2 : Set R2) := by
  -- Replace the pushed-forward field by the explicit ambient formula on the punctured set.
  fin_cases i
  · exact example_8_12_radialAmbientField_contMDiffOn.congr fun x hx ↦
      by simp [example_8_12_pushforwardFrame_eq_ambient 0 hx]
  · exact example_8_12_angularAmbientField_contMDiffOn.congr fun x hx ↦
      by simp [example_8_12_pushforwardFrame_eq_ambient 1 hx]

/-- Helper for Example 8.12: the pushed-forward ambient pair is pointwise orthonormal on the
punctured plane. -/
private theorem example_8_12_pushforwardFrame_pointwise_orthonormal
    {x : R2} (hx : x ∈ (P2 : Set R2)) :
    Orthonormal ℝ (fun i : Fin 2 ↦ fromTangentSpace x (example_8_12_pushforwardFrame i x)) := by
  -- Normalize the pushed-forward frame to the already-proved explicit ambient pair.
  let p : P2 := ⟨x, hx⟩
  have hpush :
      (fun i : Fin 2 ↦ fromTangentSpace x (example_8_12_pushforwardFrame i x)) =
        fun i : Fin 2 ↦
          !₂[
            !₂[x 0 / ‖x‖, x 1 / ‖x‖],
            !₂[-(x 1 / ‖x‖), x 0 / ‖x‖]
          ] i := by
    funext i
    rw [example_8_12_pushforwardFrame_eq_ambient (i := i) hx]
    fin_cases i <;> simp [example_8_12_radialAmbientField, example_8_12_angularAmbientField]
  rw [hpush]
  simpa [fromTangentSpace_example_8_12_E1, fromTangentSpace_example_8_12_E2]
    using example_8_12_orthonormal p

/-- Helper for Example 8.12: at each punctured-plane point, the pushed-forward ambient pair is
linearly independent. -/
private theorem example_8_12_pushforwardFrame_linearIndependent
    {x : R2} (hx : x ∈ (P2 : Set R2)) :
    LinearIndependent ℝ (example_8_12_pushforwardFrame · x) := by
  -- Transport linear independence back from Euclidean coordinates using `fromTangentSpace`.
  have hcoords :
      LinearIndependent ℝ
        (fun i : Fin 2 ↦ fromTangentSpace x (example_8_12_pushforwardFrame i x)) :=
    (example_8_12_pushforwardFrame_pointwise_orthonormal hx).linearIndependent
  simpa using
    hcoords.map' ((fromTangentSpace x).symm.toLinearMap) (by
      ext v
      simp)

/-- Helper for Example 8.12: the pushed-forward ambient pair is pointwise linearly independent on
the punctured plane. -/
private theorem example_8_12_pushforwardFrame_linearlyIndependentOn :
    VectorField.LinearlyIndependentOn (P2 : Set R2) example_8_12_pushforwardFrame := by
  intro x hx
  exact example_8_12_pushforwardFrame_linearIndependent hx

/-- Example 8.12: the vector fields `(E₁, E₂)` form an orthonormal frame on the punctured plane
`ℝ² \ {0}`, expressed through the ambient-subset owner `IsOrthonormalFrameOn`. -/
theorem example_8_12_isOrthonormalFrameOn :
    IsOrthonormalFrameOn (P2 : Set R2) example_8_12_pushforwardFrame := by
  -- Package orthonormality, pointwise independence, spanning, and smoothness into the owner.
  refine
    { linearIndependent := by
        intro x hx
        exact example_8_12_pushforwardFrame_linearIndependent hx
      generating := by
        intro x hx
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 2) x) := by
          change FiniteDimensional ℝ R2
          infer_instance
        have hcard :
            Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) x) := by
          change Fintype.card (Fin 2) = Module.finrank ℝ R2
          simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)).symm
        exact
          (example_8_12_pushforwardFrame_linearIndependent hx).span_eq_top_of_card_eq_finrank'
            hcard |>.ge
      contMDiffOn := by
        intro i
        exact example_8_12_pushforwardFrame_contMDiffOn i
      orthonormal := by
        intro x hx
        exact example_8_12_pushforwardFrame_pointwise_orthonormal hx }

/-- Helper for the punctured-plane frame example: the intrinsic pair `(E₁, E₂)` is pointwise
linearly independent on the punctured plane. -/
private theorem example_8_12_intrinsic_linearIndependent (p : P2) :
    LinearIndependent ℝ (fun i : Fin 2 ↦ (!₂[example_8_12_E1, example_8_12_E2] i p)) := by
  -- First prove linear independence after pushing forward to the ambient tangent space, then pull
  -- it back through the inclusion derivative.
  have hp0 : (p : R2) ≠ 0 := p.property
  refine
    LinearIndependent.of_comp
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p).toLinearMap ?_
  simpa [Function.comp, example_8_12_pushforwardFrame, hp0] using
    example_8_12_pushforwardFrame_linearIndependent p.property

/-- Helper for Example 8.12: pulling back the pushed-forward ambient frame along the open-subtype
inclusion recovers the intrinsic pair `(E₁, E₂)`. -/
private theorem example_8_12_mpullback_pushforwardFrame_eq (i : Fin 2) :
    VectorField.mpullback (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2)
      (example_8_12_pushforwardFrame i) =
      !₂[example_8_12_E1, example_8_12_E2] i := by
  -- Use the inverse-derivative characterization of `VectorField.mpullback`.
  funext p
  rw [VectorField.mpullback_apply]
  have hp0 : (p : R2) ≠ 0 := p.property
  exact
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      (mfderiv_open_subset_inclusion_isInvertible (I := 𝓡 2) P2 p)).2 <| by
        simpa [example_8_12_pushforwardFrame, hp0]

/-- Helper for the punctured-plane frame example: each intrinsic field is smooth because it is the
pullback of the corresponding smooth ambient field on `ℝ² \ {0}`. -/
private theorem example_8_12_intrinsic_fields_contMDiffOn (i : Fin 2) :
    ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞
      (T% ((!₂[example_8_12_E1, example_8_12_E2] i))) (Set.univ : Set P2) := by
  -- Pull the smooth ambient field back along the open-subset inclusion and normalize the result
  -- to the existing intrinsic field.
  have hpull :
      ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞
        (T%
          (VectorField.mpullback (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2)
            (example_8_12_pushforwardFrame i))) (Set.univ : Set P2) := by
    have hpullRaw :=
      (example_8_12_pushforwardFrame_contMDiffOn i).mpullback_vectorField_preimage
        (f := (Subtype.val : P2 → R2))
        (hf := (contMDiff_subtype_val : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : P2 → R2)))
        (hf' := by
          intro p hp
          simpa using mfderiv_open_subset_inclusion_isInvertible (I := 𝓡 2) P2 p)
        (hmn := by simp)
    convert hpullRaw using 1
    ext p
    simp
  simpa [example_8_12_mpullback_pushforwardFrame_eq (i := i)] using hpull

/-- Helper for Example 8.12: the intrinsic pair `(E₁, E₂)` is pointwise linearly independent on
the punctured plane. -/
private theorem example_8_12_intrinsic_linearlyIndependentOn :
    VectorField.LinearlyIndependentOn (Set.univ : Set P2) (!₂[example_8_12_E1, example_8_12_E2]) := by
  intro p hp
  simpa using example_8_12_intrinsic_linearIndependent p

/-- For Example 8.12, the intrinsic pair `(E₁, E₂)` is a smooth local frame on the punctured
plane. -/
theorem example_8_12_isLocalFrame :
    IsLocalFrameOn (𝓡 2) R2 ∞ (!₂[example_8_12_E1, example_8_12_E2]) (Set.univ : Set P2) := by
  -- Package the pointwise independence and smoothness of the intrinsic fields into the owner.
  refine
    { linearIndependent := by
        intro p hp
        exact example_8_12_intrinsic_linearIndependent p
      generating := by
        intro p hp
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 2) p) := by
          change FiniteDimensional ℝ R2
          infer_instance
        have hcard :
            Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) p) := by
          change Fintype.card (Fin 2) = Module.finrank ℝ R2
          simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)).symm
        exact
          (example_8_12_intrinsic_linearIndependent p).span_eq_top_of_card_eq_finrank' hcard |>.ge
      contMDiffOn := by
        intro i
        exact example_8_12_intrinsic_fields_contMDiffOn i }

/-- In Example 8.12, `E₁` is tangent to the radial line through the base point and points outward
along that line. -/
theorem example_8_12_E1_tangent_to_radial_lines (p : P2) :
    ∃ a : ℝ,
      0 < a ∧
        fromTangentSpace (p : R2)
          (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E1 p)) =
          a • (p : R2) := by
  -- The radial field is the position vector normalized to unit length.
  refine ⟨1 / ‖(p : R2)‖, one_div_pos.mpr (norm_pos_iff.mpr p.property), ?_⟩
  calc
    fromTangentSpace (p : R2)
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E1 p)) =
        !₂[(p : R2) 0 / ‖(p : R2)‖, (p : R2) 1 / ‖(p : R2)‖] :=
      fromTangentSpace_example_8_12_E1 p
    _ = (1 / ‖(p : R2)‖) • (p : R2) := by
      ext i
      fin_cases i <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- In Example 8.12, `E₂` is tangent to the circle centered at the origin through the base point. -/
theorem example_8_12_E2_tangent_to_centered_circles (p : P2) :
    fromTangentSpace (p : R2)
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : P2 → R2) p (example_8_12_E2 p)) ∈
      (ℝ ∙ (p : R2))ᗮ := by
  -- The angular field is orthogonal to the position vector, hence tangent to the centered circle.
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hnorm : ‖(p : R2)‖ ≠ 0 := norm_ne_zero_iff.mpr p.property
  rw [fromTangentSpace_example_8_12_E2]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [Real.inner_apply]
  field_simp [hnorm]
  ring
