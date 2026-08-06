import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Quaternion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Example_9_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat LinearAlgebra.Projectivization Quaternion

-- Semantic recall via `lean_leansearch`: mathlib exposes `Quaternion ℝ`, `ℙ`, and sphere models,
-- but no current octonion/Cayley-number owner packages the `S^15 → S^8` Hopf map, so this item
-- uses an explicit local Cayley-coordinate model for the source-facing statement.

noncomputable section

/-- The quaternionic projective line `ℍP¹`, modeled as the projectivization of `ℍ²`. -/
abbrev QuaternionProjectiveLine := ℙ ℍ (Fin 2 → ℍ)

/-- The projective-space model `ℍP¹` carries the quotient topology inherited from nonzero vectors
in `ℍ²`. -/
instance : TopologicalSpace QuaternionProjectiveLine :=
  instTopologicalSpaceQuotient

/-- Helper for Example 9.4.9: identify `ℍ²` written as functions `Fin 2 → ℍ` with quaternionic
pairs. -/
private abbrev quaternionFinTwoArrow : (Fin 2 → ℍ) →ₗ[ℍ] (ℍ × ℍ) :=
  (LinearEquiv.finTwoArrow ℍ ℍ : (Fin 2 → ℍ) ≃ₗ[ℍ] (ℍ × ℍ))

/-- Helper for Example 9.4.9: the `Fin 2 → ℍ` to `ℍ × ℍ` identification is injective. -/
private theorem quaternionFinTwoArrow_injective :
    Function.Injective quaternionFinTwoArrow :=
  ((LinearEquiv.finTwoArrow ℍ ℍ : (Fin 2 → ℍ) ≃ₗ[ℍ] (ℍ × ℍ))).injective

/-- Helper for Example 9.4.9: unpack a quaternionic pair as a `Fin 2 → ℍ` vector. -/
private abbrev quaternionFinTwoArrowSymm : (ℍ × ℍ) →ₗ[ℍ] (Fin 2 → ℍ) :=
  ((LinearEquiv.finTwoArrow ℍ ℍ).symm : (ℍ × ℍ) ≃ₗ[ℍ] (Fin 2 → ℍ))

/-- Helper for Example 9.4.9: unpacking quaternionic pairs is injective. -/
private theorem quaternionFinTwoArrowSymm_injective :
    Function.Injective quaternionFinTwoArrowSymm :=
  (((LinearEquiv.finTwoArrow ℍ ℍ).symm : (ℍ × ℍ) ≃ₗ[ℍ] (Fin 2 → ℍ))).injective

/-- Helper for Example 9.4.9: transporting `OnePoint ℍ` to `ℍP¹` and back recovers the original
affine-line point. -/
private theorem quaternionProjectiveLineEquivOnePointQuaternion_left_inv [DecidableEq ℍ]
    (z : OnePoint ℍ) :
    ((OnePoint.equivProjectivization ℍ).symm ∘
        Projectivization.map quaternionFinTwoArrow quaternionFinTwoArrow_injective)
      ((Projectivization.map quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective ∘
        OnePoint.equivProjectivization ℍ) z) = z := by
  -- Cancel the linear-equivalence transport on projective space, then return through the
  -- explicit `OnePoint ℍ ≃ ℙ(ℍ × ℍ)` equivalence.
  have h :
      Projectivization.map quaternionFinTwoArrow quaternionFinTwoArrow_injective
          (Projectivization.map quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
            ((OnePoint.equivProjectivization ℍ) z)) =
        (OnePoint.equivProjectivization ℍ) z := by
    simpa [quaternionFinTwoArrow, quaternionFinTwoArrowSymm] using
      congrFun
        (Projectivization.map_comp quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
          quaternionFinTwoArrow quaternionFinTwoArrow_injective
          (quaternionFinTwoArrow_injective.comp quaternionFinTwoArrowSymm_injective))
        ((OnePoint.equivProjectivization ℍ) z) |>.symm
  simpa [Function.comp] using congrArg (OnePoint.equivProjectivization ℍ).symm h

/-- Helper for Example 9.4.9: transporting `ℍP¹` to `OnePoint ℍ` and back recovers the original
projective point. -/
private theorem quaternionProjectiveLineEquivOnePointQuaternion_right_inv [DecidableEq ℍ]
    (x : QuaternionProjectiveLine) :
    (Projectivization.map quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective ∘
        OnePoint.equivProjectivization ℍ)
      (((OnePoint.equivProjectivization ℍ).symm ∘
          Projectivization.map quaternionFinTwoArrow quaternionFinTwoArrow_injective) x) = x := by
  -- The inverse transport cancels the forward transport because the two linear maps are mutual
  -- inverses on `ℍ²`.
  have h :
      x =
        Projectivization.map quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
          (Projectivization.map quaternionFinTwoArrow quaternionFinTwoArrow_injective x) := by
    simpa [quaternionFinTwoArrow, quaternionFinTwoArrowSymm] using
      congrFun
        (Projectivization.map_comp quaternionFinTwoArrow quaternionFinTwoArrow_injective
          quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
          (quaternionFinTwoArrowSymm_injective.comp quaternionFinTwoArrow_injective))
        x
  simpa [Function.comp] using h.symm

/-- Helper for Example 9.4.9: the affine-line model `OnePoint ℍ` and the projectivization model
`ℍP¹` agree as sets via `[z : 1]` and `[1 : 0]`. -/
noncomputable def quaternionProjectiveLineEquivOnePointQuaternion :
    OnePoint ℍ ≃ QuaternionProjectiveLine :=
  let _ : DecidableEq ℍ := Classical.decEq ℍ
  { toFun :=
      Projectivization.map quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective ∘
        OnePoint.equivProjectivization ℍ
    invFun :=
      (OnePoint.equivProjectivization ℍ).symm ∘
        Projectivization.map quaternionFinTwoArrow quaternionFinTwoArrow_injective
    left_inv := quaternionProjectiveLineEquivOnePointQuaternion_left_inv
    right_inv := quaternionProjectiveLineEquivOnePointQuaternion_right_inv }

/-- Helper for Example 9.4.9: the concrete `S⁴` model has ambient real dimension `5`. -/
private instance sphereFourModelFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
  ⟨by simp⟩

/-- Helper for Example 9.4.9: the north pole of the concrete `S⁴` model. -/
private theorem sphereFourNorthPoleModel_mem :
    EuclideanSpace.single 4 (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  -- The basis vector `e₄` has unit norm in the ambient Euclidean space.
  rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
  simp

/-- Helper for Example 9.4.9: the north pole of the concrete `S⁴` model. -/
private def sphereFourNorthPoleModel :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
  ⟨EuclideanSpace.single 4 (1 : ℝ), sphereFourNorthPoleModel_mem⟩

/-- Helper for Example 9.4.9: the corresponding point of `𝕊 4`. -/
private def sphereFourNorthPole : 𝕊 4 :=
  ULift.up sphereFourNorthPoleModel

/-- Helper for Example 9.4.9: identify a quaternion with its scaled real-coordinate vector in
`ℝ⁴`, matching the standard stereographic formula. -/
private def quaternionStereographicCoord (q : ℍ) : EuclideanSpace ℝ (Fin 4) :=
  (2 : ℝ) • Quaternion.linearIsometryEquivTuple q

/-- Helper for Example 9.4.9: recover a quaternion from its scaled `ℝ⁴` stereographic
coordinates. -/
private def stereographicCoordQuaternion (x : EuclideanSpace ℝ (Fin 4)) : ℍ :=
  Quaternion.linearIsometryEquivTuple.symm ((1 / 2 : ℝ) • x)

/-- Helper for Example 9.4.9: the scaled `ℝ⁴` stereographic coordinates recover the original
quaternion. -/
private theorem stereographicCoordQuaternion_left_inv (q : ℍ) :
    stereographicCoordQuaternion (quaternionStereographicCoord q) = q := by
  -- The two fixed real scalings cancel before applying the inverse linear isometry.
  calc
    stereographicCoordQuaternion (quaternionStereographicCoord q)
        = Quaternion.linearIsometryEquivTuple.symm
            (((1 / 2 : ℝ) * 2 : ℝ) • Quaternion.linearIsometryEquivTuple q) := by
              simp [stereographicCoordQuaternion, quaternionStereographicCoord, smul_smul]
    _ = q := by
          simp

/-- Helper for Example 9.4.9: reconstructing a quaternion from scaled `ℝ⁴` coordinates recovers
the original vector. -/
private theorem stereographicCoordQuaternion_right_inv
    (x : EuclideanSpace ℝ (Fin 4)) :
    quaternionStereographicCoord (stereographicCoordQuaternion x) = x := by
  -- The inverse linear isometry followed by the forward one leaves the `ℝ⁴` coordinates unchanged.
  calc
    quaternionStereographicCoord (stereographicCoordQuaternion x)
        = ((2 : ℝ) * (1 / 2 : ℝ)) • x := by
            ext i
            fin_cases i <;>
              simp [quaternionStereographicCoord, stereographicCoordQuaternion, smul_smul]
    _ = x := by
          simp

/-- Helper for Example 9.4.9: the scaled quaternionic stereographic coordinates are continuous. -/
private theorem quaternionStereographicCoord_continuous :
    Continuous quaternionStereographicCoord := by
  -- This is a fixed real scaling of the continuous quaternion-to-`ℝ⁴` linear isometry.
  simpa [quaternionStereographicCoord] using
    (continuous_const.smul Quaternion.linearIsometryEquivTuple.continuous)

/-- Helper for Example 9.4.9: reconstructing a quaternion from scaled `ℝ⁴` coordinates is
continuous. -/
private theorem stereographicCoordQuaternion_continuous :
    Continuous stereographicCoordQuaternion := by
  -- First undo the fixed scaling in `ℝ⁴`, then apply the inverse linear isometry.
  have hscale : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦ ((1 / 2 : ℝ) • x) :=
    continuous_const.smul continuous_id
  change Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦
      Quaternion.linearIsometryEquivTuple.symm (((1 / 2 : ℝ) • x))
  exact Quaternion.linearIsometryEquivTuple.symm.continuous.comp hscale

/-- Helper for Example 9.4.9: the scaled quaternionic stereographic coordinates give a
homeomorphism `ℍ ≃ₜ ℝ⁴`. -/
private def quaternionStereographicCoordHomeomorph :
    ℍ ≃ₜ EuclideanSpace ℝ (Fin 4) where
  toEquiv :=
    { toFun := quaternionStereographicCoord
      invFun := stereographicCoordQuaternion
      left_inv := stereographicCoordQuaternion_left_inv
      right_inv := stereographicCoordQuaternion_right_inv }
  continuous_toFun := quaternionStereographicCoord_continuous
  continuous_invFun := stereographicCoordQuaternion_continuous

/-- Helper for Example 9.4.9: insert an `ℝ⁴` point into the orthogonal complement of the north
pole by adding a zero fifth coordinate. -/
private theorem northPolePerpOfEuclidean_mem (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1) +
        EuclideanSpace.single 2 (x 2) + EuclideanSpace.single 3 (x 3) ∈
      (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ := by
  -- The inserted vector is orthogonal to the north pole because its fifth coordinate vanishes.
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [sphereFourNorthPoleModel, PiLp.inner_apply, Fin.sum_univ_five]

/-- Helper for Example 9.4.9: insert an `ℝ⁴` point into the orthogonal complement of the north
pole by adding a zero fifth coordinate. -/
private def northPolePerpOfEuclidean (x : EuclideanSpace ℝ (Fin 4)) :
    (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ :=
  ⟨EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1) +
      EuclideanSpace.single 2 (x 2) + EuclideanSpace.single 3 (x 3),
    northPolePerpOfEuclidean_mem x⟩

/-- Helper for Example 9.4.9: forget the forced zero fifth coordinate in the orthogonal
complement of the north pole. -/
private def euclideanOfNorthPolePerp
    (x : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
    EuclideanSpace ℝ (Fin 4) :=
  EuclideanSpace.single 0 (x.1 0) + EuclideanSpace.single 1 (x.1 1) +
    EuclideanSpace.single 2 (x.1 2) + EuclideanSpace.single 3 (x.1 3)

/-- Helper for Example 9.4.9: vectors orthogonal to the north pole have zero fifth coordinate. -/
private theorem northPolePerp_last_eq_zero
    (x : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
    x.1 4 = 0 := by
  -- Orthogonality to `e₄` is exactly the vanishing of the fifth coordinate.
  have horth := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.2
  have hcoord :
      inner ℝ (EuclideanSpace.single 4 (1 : ℝ)) x.1 = 0 := by
    simpa [sphereFourNorthPoleModel] using horth
  have hsingle :
      inner ℝ (EuclideanSpace.single 4 (1 : ℝ)) x.1 = x.1 4 := by
    simpa using (EuclideanSpace.inner_single_left 4 (1 : ℝ) x.1)
  rw [hsingle] at hcoord
  simpa using hcoord

/-- Helper for Example 9.4.9: inserting into the equatorial hyperplane and projecting back
recovers the original `ℝ⁴` coordinates. -/
private theorem euclideanOfNorthPolePerp_northPolePerpOfEuclidean
    (x : EuclideanSpace ℝ (Fin 4)) :
    euclideanOfNorthPolePerp (northPolePerpOfEuclidean x) = x := by
  -- The first four coordinates are unchanged by the insertion.
  ext i
  fin_cases i <;> simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean]

/-- Helper for Example 9.4.9: inserting the first four coordinates of an orthogonal vector gives
back the same vector. -/
private theorem northPolePerpOfEuclidean_euclideanOfNorthPolePerp
    (x : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
    northPolePerpOfEuclidean (euclideanOfNorthPolePerp x) = x := by
  -- The orthogonality condition forces the fifth coordinate to remain zero.
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean, northPolePerp_last_eq_zero x]

/-- Helper for Example 9.4.9: the orthogonal complement of the north pole is explicitly
homeomorphic to the equatorial hyperplane `ℝ⁴`. -/
private noncomputable def northPolePerpHomeomorph :
    EuclideanSpace ℝ (Fin 4) ≃ₜ
      (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ where
  toEquiv :=
    { toFun := northPolePerpOfEuclidean
      invFun := euclideanOfNorthPolePerp
      left_inv := euclideanOfNorthPolePerp_northPolePerpOfEuclidean
      right_inv := northPolePerpOfEuclidean_euclideanOfNorthPolePerp }
  continuous_toFun := by
    -- The first four ambient coordinates are the source coordinates, and the fifth is constantly
    -- zero.
    have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦ x 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 0).continuous
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 1).continuous
    have h2 : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦ x 2 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 2).continuous
    have h3 : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦ x 3 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 3).continuous
    have hambient : Continuous fun x : EuclideanSpace ℝ (Fin 4) ↦
        (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1) +
          EuclideanSpace.single 2 (x 2) + EuclideanSpace.single 3 (x 3) :
            EuclideanSpace ℝ (Fin 5)) := by
      refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 5 => ℝ)).comp ?_
      refine continuous_pi fun i : Fin 5 ↦ ?_
      fin_cases i
      · simpa [northPolePerpOfEuclidean] using h0
      · simpa [northPolePerpOfEuclidean] using h1
      · simpa [northPolePerpOfEuclidean] using h2
      · simpa [northPolePerpOfEuclidean] using h3
      · simpa [northPolePerpOfEuclidean] using continuous_const
    exact Continuous.subtype_mk hambient fun x ↦ (northPolePerpOfEuclidean x).2
  continuous_invFun := by
    -- Reading off the first four coordinates is continuous on the subtype as well.
    have h0 : Continuous fun x :
        (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ ↦ x.1 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 0).continuous.comp continuous_subtype_val
    have h1 : Continuous fun x :
        (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ ↦ x.1 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 1).continuous.comp continuous_subtype_val
    have h2 : Continuous fun x :
        (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ ↦ x.1 2 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 2).continuous.comp continuous_subtype_val
    have h3 : Continuous fun x :
        (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ ↦ x.1 3 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 3).continuous.comp continuous_subtype_val
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa [euclideanOfNorthPolePerp] using h0
    · simpa [euclideanOfNorthPolePerp] using h1
    · simpa [euclideanOfNorthPolePerp] using h2
    · simpa [euclideanOfNorthPolePerp] using h3

/-- Helper for Example 9.4.9: the finite stereographic branch `ℍ → S⁴ \\ {north}`. -/
private def onePointQuaternionFiniteToSphereFourModel (q : ℍ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
  stereoInvFun (norm_eq_of_mem_sphere sphereFourNorthPoleModel)
    (northPolePerpHomeomorph (quaternionStereographicCoordHomeomorph q))

/-- Helper for Example 9.4.9: the inserted quaternionic stereographic-plane vector has squared
norm `4 * ‖q‖²`. -/
private theorem northPolePerpOfEuclidean_quaternionStereographicCoord_normSq (q : ℍ) :
    ‖(((northPolePerpOfEuclidean (quaternionStereographicCoord q) :
        (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
        EuclideanSpace ℝ (Fin 5)))‖ ^ 2 =
      4 * Quaternion.normSq q := by
  -- Expanding the inserted equatorial vector leaves the four quaternionic coordinates scaled by
  -- the fixed factor `2`.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_five]
  simp [northPolePerpOfEuclidean, quaternionStereographicCoord, Quaternion.normSq_def']
  ring

/-- Helper for Example 9.4.9: the finite stereographic branch has the classical explicit
quaternionic Hopf coordinates. -/
private theorem onePointQuaternionFiniteToSphereFourModel_formula (q : ℍ) :
    ((onePointQuaternionFiniteToSphereFourModel q :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
        EuclideanSpace ℝ (Fin 5)) =
      EuclideanSpace.single 0 (2 * q.re / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 1 (2 * q.imI / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 2 (2 * q.imJ / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 3 (2 * q.imK / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 4 ((Quaternion.normSq q - 1) / (1 + Quaternion.normSq q)) := by
  -- Expand the inverse stereographic map in the concrete north-pole chart.
  rw [onePointQuaternionFiniteToSphereFourModel, stereoInvFun_apply]
  let w : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ :=
    northPolePerpOfEuclidean (quaternionStereographicCoord q)
  change
    (‖((w : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
          EuclideanSpace ℝ (Fin 5))‖ ^ 2 + 4)⁻¹ •
        ((4 : ℝ) •
            (((w : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
              EuclideanSpace ℝ (Fin 5))) +
          (‖((w : (ℝ ∙ (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5)))ᗮ) :
                EuclideanSpace ℝ (Fin 5))‖ ^ 2 - 4) •
            ((sphereFourNorthPoleModel :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
              EuclideanSpace ℝ (Fin 5))) =
      EuclideanSpace.single 0 (2 * q.re / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 1 (2 * q.imI / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 2 (2 * q.imJ / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 3 (2 * q.imK / (1 + Quaternion.normSq q)) +
        EuclideanSpace.single 4 ((Quaternion.normSq q - 1) / (1 + Quaternion.normSq q))
  rw [northPolePerpOfEuclidean_quaternionStereographicCoord_normSq]
  have hnormSq_nonneg : 0 ≤ Quaternion.normSq q := by
    simpa using (Quaternion.normSq_nonneg (a := q))
  have hden : (1 + Quaternion.normSq q : ℝ) ≠ 0 := by
    linarith
  have hden' : (4 * Quaternion.normSq q + 4 : ℝ) ≠ 0 := by
    linarith
  ext i
  fin_cases i
  · -- The first coordinate is the normalized real part.
    simp [w, northPolePerpOfEuclidean, quaternionStereographicCoord, sphereFourNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The second coordinate is the normalized `i`-component.
    simp [w, northPolePerpOfEuclidean, quaternionStereographicCoord, sphereFourNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The third coordinate is the normalized `j`-component.
    simp [w, northPolePerpOfEuclidean, quaternionStereographicCoord, sphereFourNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The fourth coordinate is the normalized `k`-component.
    simp [w, northPolePerpOfEuclidean, quaternionStereographicCoord, sphereFourNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The fifth coordinate records the usual stereographic height.
    simp [w, northPolePerpOfEuclidean, quaternionStereographicCoord, sphereFourNorthPoleModel,
      Quaternion.normSq_def', div_eq_mul_inv]
    field_simp [hden, hden']
    ring_nf

/-- Helper for Example 9.4.9: the finite quaternionic stereographic branch is an open embedding. -/
private theorem onePointQuaternionFiniteToSphereFourModel_isOpenEmbedding :
    Topology.IsOpenEmbedding onePointQuaternionFiniteToSphereFourModel := by
  -- Compose the quaternionic `ℍ ≃ₜ ℝ⁴` coordinates with the inverse stereographic chart.
  have hstereo :
      Topology.IsOpenEmbedding
        (stereoInvFun (norm_eq_of_mem_sphere sphereFourNorthPoleModel)) := by
    simpa using
      (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere sphereFourNorthPoleModel))
  exact hstereo.comp
    (northPolePerpHomeomorph.isOpenEmbedding.comp
      quaternionStereographicCoordHomeomorph.isOpenEmbedding)

/-- Helper for Example 9.4.9: the finite stereographic branch covers exactly the complement of the
north pole. -/
private theorem onePointQuaternionFiniteToSphereFourModel_range :
    Set.range onePointQuaternionFiniteToSphereFourModel =
      ({sphereFourNorthPoleModel} :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1))ᶜ := by
  -- The quaternionic coordinate homeomorphism is surjective, so the only missing point is the
  -- north pole.
  refine le_antisymm ?_ ?_
  · rintro x ⟨q, rfl⟩
    simpa [onePointQuaternionFiniteToSphereFourModel] using
      stereoInvFun_ne_north_pole (norm_eq_of_mem_sphere sphereFourNorthPoleModel)
        (northPolePerpHomeomorph (quaternionStereographicCoordHomeomorph q))
  · intro x hx
    refine
      ⟨quaternionStereographicCoordHomeomorph.symm
          (northPolePerpHomeomorph.symm
            ((stereographic (norm_eq_of_mem_sphere sphereFourNorthPoleModel)) x)), ?_⟩
    -- Apply the left-inverse relation for stereographic projection away from the north pole.
    simpa [onePointQuaternionFiniteToSphereFourModel] using
      stereo_left_inv (norm_eq_of_mem_sphere sphereFourNorthPoleModel)
        (show (x : EuclideanSpace ℝ (Fin 5)) ≠
            (sphereFourNorthPoleModel : EuclideanSpace ℝ (Fin 5))
          from fun h ↦ hx (Subtype.ext h))

/-- Helper for Example 9.4.9: `OnePoint ℍ` is the standard affine chart model of `S⁴`, written
with an explicit quaternionic stereographic finite branch and north-pole point. -/
noncomputable def onePointQuaternionStereographicHomeomorphSphereFour :
    OnePoint ℍ ≃ₜ 𝕊 4 :=
  (OnePoint.equivOfIsEmbeddingOfRangeEq sphereFourNorthPoleModel
      onePointQuaternionFiniteToSphereFourModel
      onePointQuaternionFiniteToSphereFourModel_isOpenEmbedding.toIsEmbedding
      onePointQuaternionFiniteToSphereFourModel_range).trans Homeomorph.ulift.symm

/-- Helper for Example 9.4.9: on finite points, the quaternionic stereographic homeomorphism
agrees with the explicit finite branch. -/
private theorem onePointQuaternionStereographicHomeomorphSphereFour_apply_coe (q : ℍ) :
    onePointQuaternionStereographicHomeomorphSphereFour q =
      ULift.up (onePointQuaternionFiniteToSphereFourModel q) := by
  -- This is the defining finite branch of `OnePoint.equivOfIsEmbeddingOfRangeEq`.
  rfl

/-- Helper for Example 9.4.9: the quaternionic stereographic homeomorphism sends `∞` to the north
pole of `S⁴`. -/
private theorem onePointQuaternionStereographicHomeomorphSphereFour_apply_infty :
    onePointQuaternionStereographicHomeomorphSphereFour (OnePoint.infty : OnePoint ℍ) =
      sphereFourNorthPole := by
  -- The unique point outside the finite image is the north pole.
  rfl

/-- The unit sphere in `ℍ²`, used as the concrete model of `S^7 ⊂ ℍ²`. -/
abbrev QuaternionSphereSeven := Metric.sphere (0 : Fin 2 → ℍ) 1

/-- A point of the unit sphere in `ℍ²` is nonzero as a vector. -/
theorem quaternionSphereSeven_nonzero (q : QuaternionSphereSeven) : q.1 ≠ 0 := by
  intro hq
  have hnorm : ‖q.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
  simp [hq] at hnorm

/-- The quotient map from the concrete sphere `S^7 ⊂ ℍ²` to `ℍP¹`. -/
def quaternionSphereSevenToProjectivization (q : QuaternionSphereSeven) :
    QuaternionProjectiveLine :=
  Projectivization.mk ℍ q.1 (quaternionSphereSeven_nonzero q)

/-- Helper for Example 9.4.9: scaling a nonzero real-normed vector by the inverse of its norm
lands on the unit sphere. -/
private theorem invNorm_smul_mem_unitSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) (hx : x ≠ 0) :
    ((‖x‖)⁻¹ : ℝ) • x ∈ Metric.sphere (0 : E) 1 := by
  -- The inverse norm rescales the source vector to have norm `1`.
  rw [mem_sphere_zero_iff_norm]
  have hnorm : ‖x‖ ≠ 0 := by
    intro hnorm
    exact hx (norm_eq_zero.mp hnorm)
  calc
    ‖((‖x‖)⁻¹ : ℝ) • x‖ = ‖x‖⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    _ = 1 := by
      exact inv_mul_cancel₀ hnorm

/-- Helper for Example 9.4.9: normalizing a positive real multiple of a unit vector recovers the
original unit vector. -/
private theorem invNorm_smul_eq_of_mem_unitSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (hx : x ∈ Metric.sphere (0 : E) 1) {a : ℝ} (ha : 0 < a) :
    ((‖a • x‖)⁻¹ : ℝ) • (a • x) = x := by
  -- The source vector already has norm `1`, so normalizing any positive rescaling of it collapses
  -- back to the original vector.
  have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hnorm : ‖a • x‖ = a := by
    rw [norm_smul, hxnorm, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  calc
    ((‖a • x‖)⁻¹ : ℝ) • (a • x) = ((‖a • x‖)⁻¹ * a : ℝ) • x := by
      rw [smul_smul]
    _ = x := by
      simp [hnorm, ha.ne']

/-- Helper for Example 9.4.9: the canonical quotient `QuaternionSphereSeven → ℍP¹` is
continuous. -/
private theorem quaternionSphereSevenToProjectivization_continuous :
    Continuous quaternionSphereSevenToProjectivization := by
  -- Lift a sphere point to the nonzero-vector subtype, then apply the continuous projectivization
  -- quotient map.
  let nonzeroVector : QuaternionSphereSeven → { v : Fin 2 → ℍ // v ≠ 0 } :=
    fun z ↦ ⟨z.1, quaternionSphereSeven_nonzero z⟩
  have hnonzeroVector : Continuous nonzeroVector :=
    Continuous.subtype_mk continuous_subtype_val fun z ↦ (nonzeroVector z).2
  simpa [quaternionSphereSevenToProjectivization, Projectivization.mk', nonzeroVector,
    Projectivization.mk'_eq_mk] using
    (continuous_quotient_mk'.comp hnonzeroVector)

/-- Helper for Example 9.4.9: every point of `ℍP¹` has a unit-norm representative in
`QuaternionSphereSeven`. -/
private theorem quaternionSphereSevenToProjectivization_surjective :
    Function.Surjective quaternionSphereSevenToProjectivization := by
  intro x
  induction x using Projectivization.ind with
  | h v hv =>
      let z : QuaternionSphereSeven :=
        ⟨((‖v‖)⁻¹ : ℝ) • v, invNorm_smul_mem_unitSphere v hv⟩
      refine ⟨z, ?_⟩
      -- The normalized representative spans the same quaternionic line as the original vector.
      apply (Projectivization.mk_eq_mk_iff' ℍ z.1 v (quaternionSphereSeven_nonzero z) hv).2
      refine ⟨((‖v‖)⁻¹ : ℍ), ?_⟩
      funext i
      apply Quaternion.ext <;> simp [z, Algebra.smul_def]

/-- Helper for Example 9.4.9: `QuaternionProjectiveLine` is compact because it is the continuous
image of the compact sphere `QuaternionSphereSeven`. -/
private theorem quaternionProjectiveLine_isCompact :
    IsCompact (Set.univ : Set QuaternionProjectiveLine) := by
  simpa [Set.image_univ, quaternionSphereSevenToProjectivization_surjective.range_eq] using
    CompactSpace.isCompact_univ.image quaternionSphereSevenToProjectivization_continuous

/-- Helper for Example 9.4.9: the quotient model `ℍP¹` inherits compactness from the sphere
model. -/
private noncomputable instance quaternionProjectiveLineCompactSpace :
    CompactSpace QuaternionProjectiveLine :=
  isCompact_univ_iff.mp quaternionProjectiveLine_isCompact

/-- Helper for Example 9.4.9: the finite affine chart `q ↦ [q : 1]` in `ℍP¹`. -/
private def quaternionProjectiveLineFinite (q : ℍ) : QuaternionProjectiveLine :=
  Projectivization.mk ℍ (quaternionFinTwoArrowSymm (q, 1)) <| by
    -- The affine representative `(q, 1)` is nonzero because its second coordinate is `1`.
    intro hq
    have hq' : quaternionFinTwoArrowSymm (q, 1) = quaternionFinTwoArrowSymm 0 := by
      simpa using hq
    have hpair : ((q, (1 : ℍ)) : ℍ × ℍ) = 0 := quaternionFinTwoArrowSymm_injective hq'
    simpa using congrArg Prod.snd hpair

/-- Helper for Example 9.4.9: the point at infinity `[1 : 0]` in `ℍP¹`. -/
private def quaternionProjectiveLineInfinity : QuaternionProjectiveLine :=
  Projectivization.mk ℍ (quaternionFinTwoArrowSymm (1, 0)) <| by
    -- The representative `(1, 0)` is nonzero because its first coordinate is `1`.
    intro hq
    have hq' : quaternionFinTwoArrowSymm (1, 0) = quaternionFinTwoArrowSymm 0 := by
      simpa using hq
    have hpair : (((1 : ℍ), 0) : ℍ × ℍ) = 0 := quaternionFinTwoArrowSymm_injective hq'
    simpa using congrArg Prod.fst hpair

/-- Helper for Example 9.4.9: the explicit affine chart agrees with the finite part of
`quaternionProjectiveLineEquivOnePointQuaternion`. -/
private theorem quaternionProjectiveLineFinite_eq_equiv (q : ℍ) :
    quaternionProjectiveLineFinite q = quaternionProjectiveLineEquivOnePointQuaternion q := by
  -- Unfolding both sides shows that they are the same projective class `[q : 1]`.
  simpa [quaternionProjectiveLineFinite, quaternionProjectiveLineEquivOnePointQuaternion,
    Function.comp, OnePoint.equivProjectivization_apply_coe] using
    (Projectivization.map_mk quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
      ((q, 1) : ℍ × ℍ) (by simp)).symm

/-- Helper for Example 9.4.9: the chosen point at infinity agrees with the infinite part of
`quaternionProjectiveLineEquivOnePointQuaternion`. -/
private theorem quaternionProjectiveLineInfinity_eq_equiv :
    quaternionProjectiveLineInfinity =
      quaternionProjectiveLineEquivOnePointQuaternion (OnePoint.infty : OnePoint ℍ) := by
  -- Unfolding both sides shows that they are the same projective class `[1 : 0]`.
  simpa [quaternionProjectiveLineInfinity, quaternionProjectiveLineEquivOnePointQuaternion,
    Function.comp, OnePoint.equivProjectivization_apply_infinity] using
    (Projectivization.map_mk quaternionFinTwoArrowSymm quaternionFinTwoArrowSymm_injective
      ((1, 0) : ℍ × ℍ) (by simp)).symm

/-- Helper for Example 9.4.9: the finite affine chart is continuous. -/
private theorem quaternionProjectiveLineFinite_continuous :
    Continuous quaternionProjectiveLineFinite := by
  let affineRep : ℍ → { v : Fin 2 → ℍ // v ≠ 0 } := fun q ↦
    ⟨quaternionFinTwoArrowSymm (q, 1), by
      intro hq
      have hq' : quaternionFinTwoArrowSymm (q, 1) = quaternionFinTwoArrowSymm 0 := by
        simpa using hq
      have hpair : ((q, (1 : ℍ)) : ℍ × ℍ) = 0 := quaternionFinTwoArrowSymm_injective hq'
      simpa using congrArg Prod.snd hpair⟩
  have hbase : Continuous fun q : ℍ ↦ quaternionFinTwoArrowSymm (q, 1) := by
    -- In coordinates this is the map `q ↦ ![q, 1]`, so continuity is coordinatewise.
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact continuous_id
    · simpa [quaternionFinTwoArrowSymm] using (continuous_const : Continuous fun _ : ℍ ↦ (1 : ℍ))
  have haffineRep : Continuous affineRep := by
    -- The affine representatives vary continuously with `q`.
    simpa [affineRep] using
      (Continuous.subtype_mk hbase fun q ↦ (affineRep q).2)
  -- The affine representatives are exactly the nonzero vectors used by `Projectivization.mk`.
  have hmk : Projectivization.mk' ℍ ∘ affineRep = quaternionProjectiveLineFinite := by
    funext q
    simp [affineRep, quaternionProjectiveLineFinite]
  -- The projective quotient map is continuous, so the affine chart inherits continuity.
  have hquot : Continuous (Projectivization.mk' ℍ ∘ affineRep) :=
    continuous_quotient_mk'.comp haffineRep
  simpa [hmk] using hquot

/-- Helper for Example 9.4.9: finite affine points never hit the point at infinity. -/
private theorem quaternionProjectiveLineFinite_ne_infinity (q : ℍ) :
    quaternionProjectiveLineFinite q ≠ quaternionProjectiveLineInfinity := by
  -- Passing through `quaternionProjectiveLineEquivOnePointQuaternion` would force `q = ∞`,
  -- impossible.
  intro hq
  have hfinite :
      (q : OnePoint ℍ) = (OnePoint.infty : OnePoint ℍ) := by
    apply quaternionProjectiveLineEquivOnePointQuaternion.injective
    simpa [quaternionProjectiveLineFinite_eq_equiv, quaternionProjectiveLineInfinity_eq_equiv]
      using hq
  exact OnePoint.coe_ne_infty q hfinite

/-- Helper for Example 9.4.9: the finite affine chart is injective. -/
private theorem quaternionProjectiveLineFinite_injective :
    Function.Injective quaternionProjectiveLineFinite := by
  intro q r hqr
  have hfinite :
      quaternionProjectiveLineEquivOnePointQuaternion (q : OnePoint ℍ) =
        quaternionProjectiveLineEquivOnePointQuaternion (r : OnePoint ℍ) := by
    simpa [quaternionProjectiveLineFinite_eq_equiv] using hqr
  simpa using quaternionProjectiveLineEquivOnePointQuaternion.injective hfinite

/-- Helper for Example 9.4.9: the image of the finite affine chart is exactly the complement of
the point at infinity. -/
private theorem mem_range_quaternionProjectiveLineFinite_iff_ne_infinity
    (x : QuaternionProjectiveLine) :
    x ∈ Set.range quaternionProjectiveLineFinite ↔ x ≠ quaternionProjectiveLineInfinity := by
  constructor
  · rintro ⟨q, rfl⟩
    -- A finite affine point cannot equal the point at infinity.
    exact quaternionProjectiveLineFinite_ne_infinity q
  · intro hx
    -- The inverse equivalence cannot land at `∞`, so it comes from some finite affine coordinate.
    have hfinite :
        quaternionProjectiveLineEquivOnePointQuaternion.symm x ≠
          (OnePoint.infty : OnePoint ℍ) := by
      intro hinfty
      apply hx
      simpa [quaternionProjectiveLineInfinity_eq_equiv] using
        congrArg quaternionProjectiveLineEquivOnePointQuaternion hinfty
    rcases OnePoint.ne_infty_iff_exists.mp hfinite with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      quaternionProjectiveLineFinite q
          = quaternionProjectiveLineEquivOnePointQuaternion (q : OnePoint ℍ) := by
              simpa [quaternionProjectiveLineFinite_eq_equiv]
      _ = quaternionProjectiveLineEquivOnePointQuaternion
            (quaternionProjectiveLineEquivOnePointQuaternion.symm x) := by
              simpa [hq]
      _ = x := quaternionProjectiveLineEquivOnePointQuaternion.apply_symm_apply x

/-- Helper for Example 9.4.9: in the affine chart `ℍP¹ ≃ OnePoint ℍ`, the quotient map is the
usual ratio `z₀ / z₁` with the point at infinity when `z₁ = 0`. -/
private def quaternionQuotientAffineChartValue (z : QuaternionSphereSeven) : OnePoint ℍ :=
  let _ : DecidableEq ℍ := Classical.decEq ℍ
  if _h : z.1 1 = 0 then
    OnePoint.infty
  else
    ((z.1 1)⁻¹ * z.1 0 : ℍ)

/-- Helper for Example 9.4.9: the affine chart on `ℍP¹` sends the quaternionic quotient map to the
expected ratio formula. -/
private theorem quaternionQuotientAffineChartFormula (z : QuaternionSphereSeven) :
    quaternionProjectiveLineEquivOnePointQuaternion.symm (quaternionSphereSevenToProjectivization z) =
      quaternionQuotientAffineChartValue z := by
  -- The projectivization chart on `ℍP¹` is defined by the same affine ratio formula as in the
  -- complex case, now written in quaternionic coordinates.
  let _ : DecidableEq ℍ := Classical.decEq ℍ
  simp [quaternionQuotientAffineChartValue, quaternionProjectiveLineEquivOnePointQuaternion,
    quaternionSphereSevenToProjectivization, Function.comp, Projectivization.map_mk,
    OnePoint.equivProjectivization_symm_apply_mk]

/-- Helper for Example 9.4.9: the quotient map written in the affine `OnePoint ℍ` chart. -/
private def qQuaternion : QuaternionSphereSeven → OnePoint ℍ :=
  quaternionProjectiveLineEquivOnePointQuaternion.symm ∘ quaternionSphereSevenToProjectivization

/-- Helper for Example 9.4.9: `qQuaternion` is the previously computed affine quotient chart. -/
private theorem qQuaternion_eq_quaternionQuotientAffineChartValue (z : QuaternionSphereSeven) :
    qQuaternion z = quaternionQuotientAffineChartValue z := by
  -- This is just the quotient affine chart formula written with the packaged notation `qQuaternion`.
  simp [qQuaternion, quaternionQuotientAffineChartFormula]

/-- A map `ν : 𝕊 7 → 𝕊 4` is quaternionic Hopf if, after identifying `𝕊 7` with the unit sphere
in `ℍ²`, it is induced from the quotient `S^7 ⊂ ℍ² → ℍP¹` followed by a homeomorphism
`ℍP¹ ≃ₜ S⁴`. -/
def IsQuaternionicHopfQuotientMap (ν : TopCat.sphere.{0} 7 → TopCat.sphere.{0} 4) : Prop :=
  ∃ (eS7 : TopCat.sphere.{0} 7 ≃ₜ QuaternionSphereSeven)
    (eHP1 : QuaternionProjectiveLine ≃ₜ TopCat.sphere.{0} 4),
    ν = eHP1 ∘ quaternionSphereSevenToProjectivization ∘ eS7

namespace IsQuaternionicHopfQuotientMap

/-- A quaternionic Hopf quotient map comes with the source-facing homeomorphisms identifying it
with the quotient `S^7 ⊂ ℍ² → ℍP¹ ≃ S⁴`. -/
theorem exists_homeomorphisms {ν : 𝕊 7 → 𝕊 4} (hν : IsQuaternionicHopfQuotientMap ν) :
    ∃ (eS7 : 𝕊 7 ≃ₜ QuaternionSphereSeven) (eHP1 : QuaternionProjectiveLine ≃ₜ 𝕊 4),
      ν = eHP1 ∘ quaternionSphereSevenToProjectivization ∘ eS7 :=
  hν

end IsQuaternionicHopfQuotientMap

/-- The first quaternion coordinate of a point of `S^7 ⊂ ℝ⁸`. -/
def quaternionicLeft (x : 𝕊 7) : ℍ :=
  ⟨x.down.1 0, x.down.1 1, x.down.1 2, x.down.1 3⟩

/-- The second quaternion coordinate of a point of `S^7 ⊂ ℝ⁸`. -/
def quaternionicRight (x : 𝕊 7) : ℍ :=
  ⟨x.down.1 4, x.down.1 5, x.down.1 6, x.down.1 7⟩

/-- The standard quaternionic coordinate formula underlying the Hopf map `S^7 → S^4`. -/
def quaternionicHopfMapVec (x : 𝕊 7) : EuclideanSpace ℝ (Fin 5) :=
  let u := quaternionicLeft x
  let v := quaternionicRight x
  let uv := u * star v
  EuclideanSpace.single 0 (2 * uv.re) +
    EuclideanSpace.single 1 (2 * uv.imI) +
    EuclideanSpace.single 2 (2 * uv.imJ) +
    EuclideanSpace.single 3 (2 * uv.imK) +
    EuclideanSpace.single 4 (Quaternion.normSq u - Quaternion.normSq v)

/-- Helper for Example 9.4.9: the two quaternionic coordinates of a point of `S^7` have squared
norms summing to `1`. -/
private theorem quaternionicLeftRight_normSq (x : 𝕊 7) :
    Quaternion.normSq (quaternionicLeft x) + Quaternion.normSq (quaternionicRight x) = 1 := by
  -- Rewrite the ambient `S^7` equation as the sum of the eight coordinate squares.
  have hxnorm : ‖x.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.down.2
  have hxnormsq : ‖x.down.1‖ ^ 2 = 1 := by
    nlinarith [hxnorm]
  rw [EuclideanSpace.real_norm_sq_eq] at hxnormsq
  simp [Fin.sum_univ_succ] at hxnormsq
  ring_nf at hxnormsq
  -- Group the first four and last four coordinates into the two quaternionic norms.
  calc
    Quaternion.normSq (quaternionicLeft x) + Quaternion.normSq (quaternionicRight x)
        = x.down.1 0 ^ 2 + x.down.1 1 ^ 2 + x.down.1 2 ^ 2 + x.down.1 3 ^ 2 +
            (x.down.1 4 ^ 2 + x.down.1 5 ^ 2 + x.down.1 6 ^ 2 + x.down.1 7 ^ 2) := by
              simp [quaternionicLeft, quaternionicRight, Quaternion.normSq_def']
    _ = 1 := by
          have hsum := hxnormsq
          abel_nf at hsum ⊢
          exact hsum

/-- The quaternionic Hopf coordinate formula lands on the unit sphere `S⁴`. -/
theorem quaternionicHopfMapVec_mem (x : 𝕊 7) :
    quaternionicHopfMapVec x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  let u := quaternionicLeft x
  let v := quaternionicRight x
  let uv := u * star v
  have huv :
      Quaternion.normSq uv = Quaternion.normSq u * Quaternion.normSq v := by
    -- The mixed quaternionic term has the expected multiplicative squared norm.
    simp [uv, Quaternion.normSq.map_mul, Quaternion.normSq_star]
  have hsplit : Quaternion.normSq u + Quaternion.normSq v = 1 := by
    simpa [u, v] using quaternionicLeftRight_normSq x
  have hsq : ‖quaternionicHopfMapVec x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    -- Expanding the five coordinates reduces the target to the standard Hopf polynomial identity.
    calc
      ∑ i, (quaternionicHopfMapVec x i) ^ 2
          = 4 * Quaternion.normSq uv + (Quaternion.normSq u - Quaternion.normSq v) ^ 2 := by
              simp [quaternionicHopfMapVec, u, v, uv, Quaternion.normSq_def', Quaternion.re_mul,
                Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Fin.sum_univ_succ]
              ring
      _ = 4 * (Quaternion.normSq u * Quaternion.normSq v) +
            (Quaternion.normSq u - Quaternion.normSq v) ^ 2 := by
              rw [huv]
      _ = 1 := by
            nlinarith [hsplit]
  rw [mem_sphere_zero_iff_norm]
  -- A nonnegative real with square `1` must equal `1`.
  apply le_antisymm
  · nlinarith [norm_nonneg (quaternionicHopfMapVec x), hsq]
  · nlinarith [norm_nonneg (quaternionicHopfMapVec x), hsq]

/-- The quaternionic Hopf map `ν : S^7 → S^4` given by the standard quaternionic formula. -/
def quaternionicHopfMap (x : 𝕊 7) : 𝕊 4 :=
  ULift.up ⟨quaternionicHopfMapVec x, quaternionicHopfMapVec_mem x⟩

/-- Helper for Example 9.4.9: multiplying the affine ratio `a / b` by `‖b‖²` recovers the
quaternionic numerator `star b * a`. -/
private theorem quaternionNormSq_mul_inv_mul_eq_star_mul (a b : ℍ) :
    (Quaternion.normSq b : ℝ) • (b⁻¹ * a) = star b * a := by
  -- Rewrite the inverse through quaternionic conjugation, then cancel the real norm factor.
  by_cases hb : b = 0
  · simp [hb]
  · have hbnorm : Quaternion.normSq b ≠ 0 := Quaternion.normSq_ne_zero.mpr hb
    rw [Quaternion.inv_def]
    simpa [smul_mul_assoc, smul_smul, hbnorm]

/-- Helper for Example 9.4.9: the stereographic denominator for the affine ratio `a / b`
normalizes to the common Hopf denominator. -/
private theorem quaternionRatioNormSq_addOne_eq_normSqSum_div_normSq
    (a b : ℍ) (hb : b ≠ 0) :
    1 + Quaternion.normSq (b⁻¹ * a) =
      (Quaternion.normSq a + Quaternion.normSq b) / Quaternion.normSq b := by
  -- Clear the nonzero denominator `‖b‖²` to compare both scalar expressions directly.
  have hbnorm : Quaternion.normSq b ≠ 0 := Quaternion.normSq_ne_zero.mpr hb
  rw [Quaternion.normSq.map_mul, Quaternion.normSq_inv, div_eq_mul_inv]
  field_simp [hbnorm]
  ring


/-- Helper for Example 9.4.9: record a point of `S⁷` as the quaternionic pair
`(star right, star left)`. -/
private def sphereSevenPack (x : 𝕊 7) : Fin 2 → ℍ
  | 0 => star (quaternionicRight x)
  | 1 => star (quaternionicLeft x)

/-- Helper for Example 9.4.9: pack an ambient `ℝ⁸` vector into the quaternionic coordinates
compatible with `sphereSevenPack`. -/
private def quaternionPack (x : EuclideanSpace ℝ (Fin 8)) : Fin 2 → ℍ
  | 0 => ⟨x 4, -x 5, -x 6, -x 7⟩
  | 1 => ⟨x 0, -x 1, -x 2, -x 3⟩

/-- Helper for Example 9.4.9: the ambient packer agrees with the sphere-level packaging. -/
private theorem sphereSevenPack_eq_quaternionPack (x : 𝕊 7) :
    sphereSevenPack x = quaternionPack x.down.1 := by
  -- Both packers use the same fixed `(star right, star left)` coordinate convention.
  funext i
  fin_cases i
  · apply Quaternion.ext <;> simp [sphereSevenPack, quaternionPack, quaternionicRight]
  · apply Quaternion.ext <;> simp [sphereSevenPack, quaternionPack, quaternionicLeft]

/-- Helper for Example 9.4.9: the packaged source point exposes the right quaternionic coordinate
as the zeroth `ℍ²` entry. -/
private theorem sphereSevenPack_apply_zero (x : 𝕊 7) :
    sphereSevenPack x 0 = star (quaternionicRight x) := by
  -- This is the zeroth branch of the explicit source packaging.
  rfl

/-- Helper for Example 9.4.9: the packaged source point exposes the left quaternionic coordinate
as the first `ℍ²` entry. -/
private theorem sphereSevenPack_apply_one (x : 𝕊 7) :
    sphereSevenPack x 1 = star (quaternionicLeft x) := by
  -- This is the first branch of the explicit source packaging.
  rfl

/-- Helper for Example 9.4.9: the source packaging has quaternionic squared norms summing to `1`.
-/
private theorem sphereSevenPack_normSq (x : 𝕊 7) :
    Quaternion.normSq (sphereSevenPack x 0) + Quaternion.normSq (sphereSevenPack x 1) = 1 := by
  -- The inserted `star` does not change quaternionic norm, so this is exactly the earlier
  -- `quaternionicLeftRight_normSq` identity with the two coordinates swapped.
  calc
    Quaternion.normSq (sphereSevenPack x 0) + Quaternion.normSq (sphereSevenPack x 1)
        = Quaternion.normSq (quaternionicRight x) + Quaternion.normSq (quaternionicLeft x) := by
            simp [sphereSevenPack_apply_zero, sphereSevenPack_apply_one, add_comm]
    _ = 1 := by
          simpa [add_comm] using quaternionicLeftRight_normSq x

/-- Helper for Example 9.4.9: unpack the quaternionic pair `(z₀, z₁)` back into the eight real
coordinates compatible with the fixed source convention of `sphereSevenPack`. -/
private def sphereSevenUnpack (z : Fin 2 → ℍ) : EuclideanSpace ℝ (Fin 8) :=
  !₂[(z 1).re, -(z 1).imI, -(z 1).imJ, -(z 1).imK,
    (z 0).re, -(z 0).imI, -(z 0).imJ, -(z 0).imK]

/-- Helper for Example 9.4.9: unpacking the packaged source point recovers the original ambient
real coordinates of `S⁷`. -/
private theorem sphereSevenUnpack_pack (x : 𝕊 7) :
    sphereSevenUnpack (sphereSevenPack x) = x.down.1 := by
  -- Each real coordinate is recovered by undoing the conjugation built into `sphereSevenPack`.
  ext i
  fin_cases i <;> simp [sphereSevenUnpack, sphereSevenPack, quaternionicLeft, quaternionicRight]

/-- Helper for Example 9.4.9: unpacking the ambient packed coordinates recovers the original
vector in `ℝ⁸`. -/
private theorem sphereSevenUnpack_quaternionPack (x : EuclideanSpace ℝ (Fin 8)) :
    sphereSevenUnpack (quaternionPack x) = x := by
  -- The ambient packer was chosen as the coordinatewise inverse of `sphereSevenUnpack`.
  ext i
  fin_cases i <;> simp [sphereSevenUnpack, quaternionPack]

/-- Helper for Example 9.4.9: packing the unpacked quaternionic coordinates recovers the original
point of `ℍ²`. -/
private theorem quaternionPack_sphereSevenUnpack (z : Fin 2 → ℍ) :
    quaternionPack (sphereSevenUnpack z) = z := by
  -- Each quaternion coordinate is recovered from its real and imaginary components.
  funext i
  fin_cases i <;> apply Quaternion.ext <;> simp [sphereSevenUnpack, quaternionPack]

/-- Helper for Example 9.4.9: unpacking sends the zero quaternionic pair to the zero vector in
`ℝ⁸`. -/
private theorem sphereSevenUnpack_zero :
    sphereSevenUnpack (0 : Fin 2 → ℍ) = 0 := by
  -- Every real coordinate of the unpacked zero pair is zero.
  ext i
  fin_cases i <;> simp [sphereSevenUnpack]

/-- Helper for Example 9.4.9: unpacking commutes with real scaling of the quaternionic pair. -/
private theorem sphereSevenUnpack_real_smul (a : ℝ) (z : Fin 2 → ℍ) :
    sphereSevenUnpack (a • z) = a • sphereSevenUnpack z := by
  -- Real scalars distribute through the real and imaginary quaternion coordinates.
  ext i
  fin_cases i <;> simp [sphereSevenUnpack]

/-- Helper for Example 9.4.9: packing commutes with real scaling of the ambient `ℝ⁸` vector. -/
private theorem quaternionPack_real_smul (a : ℝ) (x : EuclideanSpace ℝ (Fin 8)) :
    quaternionPack (a • x) = a • quaternionPack x := by
  -- Real scalars distribute through each quaternion coordinate of the ambient packer.
  funext i
  fin_cases i <;> apply Quaternion.ext <;> simp [quaternionPack]

/-- Helper for Example 9.4.9: unpacking the quaternionic coordinates varies continuously. -/
private theorem sphereSevenUnpack_continuous :
    Continuous sphereSevenUnpack := by
  -- Each real coordinate of `sphereSevenUnpack` is a real or imaginary quaternion coordinate.
  have h0 : Continuous fun z : Fin 2 → ℍ ↦ z 0 := continuous_apply 0
  have h1 : Continuous fun z : Fin 2 → ℍ ↦ z 1 := continuous_apply 1
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 8 => ℝ)).comp ?_
  refine continuous_pi fun i : Fin 8 ↦ ?_
  fin_cases i
  · simpa [sphereSevenUnpack] using Quaternion.continuous_re.comp h1
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imI.comp h1).neg
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imJ.comp h1).neg
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imK.comp h1).neg
  · simpa [sphereSevenUnpack] using Quaternion.continuous_re.comp h0
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imI.comp h0).neg
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imJ.comp h0).neg
  · simpa [sphereSevenUnpack] using (Quaternion.continuous_imK.comp h0).neg

/-- Helper for Example 9.4.9: packing the ambient real coordinates into `ℍ²` is continuous. -/
private theorem quaternionPack_continuous :
    Continuous quaternionPack := by
  -- Each packed quaternion coordinate is an explicit tuple of ambient real coordinates.
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 0).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 1).continuous
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 2).continuous
  have h3 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 3 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 3).continuous
  have h4 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 4 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 4).continuous
  have h5 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 5 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 5).continuous
  have h6 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 6 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 6).continuous
  have h7 : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦ x 7 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 7).continuous
  have hRightVec : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦
      (!₂[x 4, -x 5, -x 6, -x 7] : EuclideanSpace ℝ (Fin 4)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa using h4
    · simpa using h5.neg
    · simpa using h6.neg
    · simpa using h7.neg
  have hLeftVec : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦
      (!₂[x 0, -x 1, -x 2, -x 3] : EuclideanSpace ℝ (Fin 4)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa using h0
    · simpa using h1.neg
    · simpa using h2.neg
    · simpa using h3.neg
  have hRight : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦
      (Quaternion.linearIsometryEquivTuple.symm
        (!₂[x 4, -x 5, -x 6, -x 7] : EuclideanSpace ℝ (Fin 4)) : ℍ) :=
    Quaternion.linearIsometryEquivTuple.symm.continuous.comp hRightVec
  have hLeft : Continuous fun x : EuclideanSpace ℝ (Fin 8) ↦
      (Quaternion.linearIsometryEquivTuple.symm
        (!₂[x 0, -x 1, -x 2, -x 3] : EuclideanSpace ℝ (Fin 4)) : ℍ) :=
    Quaternion.linearIsometryEquivTuple.symm.continuous.comp hLeftVec
  refine continuous_pi fun i : Fin 2 ↦ ?_
  fin_cases i
  · simpa [quaternionPack] using hRight
  · simpa [quaternionPack] using hLeft

/-- Helper for Example 9.4.9: unpacking a quaternionic pair identifies the ambient Euclidean norm
square with the sum of the two quaternionic norm squares. -/
private theorem sphereSevenUnpack_normSq (z : Fin 2 → ℍ) :
    ‖sphereSevenUnpack z‖ ^ 2 = Quaternion.normSq (z 0) + Quaternion.normSq (z 1) := by
  -- Expanding the eight real coordinates groups them into the two quaternionic norm squares.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_eight]
  simp [sphereSevenUnpack, Quaternion.normSq_def']
  ring

/-- Helper for Example 9.4.9: the ambient quaternionic packer is injective. -/
private theorem quaternionPack_injective :
    Function.Injective quaternionPack := by
  intro x y hxy
  simpa [sphereSevenUnpack_quaternionPack] using congrArg sphereSevenUnpack hxy

/-- Helper for Example 9.4.9: the quaternionic unpacker is injective. -/
private theorem sphereSevenUnpack_injective :
    Function.Injective sphereSevenUnpack := by
  intro z w hzw
  simpa [quaternionPack_sphereSevenUnpack] using congrArg quaternionPack hzw

/-- Helper for Example 9.4.9: packing the zero ambient vector gives the zero quaternionic pair. -/
private theorem quaternionPack_zero :
    quaternionPack (0 : EuclideanSpace ℝ (Fin 8)) = 0 := by
  -- Every packed quaternion coordinate of the zero vector is zero.
  funext i
  fin_cases i <;> apply Quaternion.ext <;> simp [quaternionPack]

/-- Helper for Example 9.4.9: a point on the Euclidean `S⁷` packs to a nonzero quaternionic
vector. -/
private theorem quaternionPack_nonzero
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :
    quaternionPack x.1 ≠ 0 := by
  -- Otherwise unpacking would force the original Euclidean sphere point to be zero.
  intro hpack
  have hzero : quaternionPack x.1 = quaternionPack 0 := by
    exact hpack.trans quaternionPack_zero.symm
  have hx0 : x.1 = 0 := quaternionPack_injective hzero
  have hxnorm : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  simp [hx0] at hxnorm

/-- Helper for Example 9.4.9: a point on the quaternionic unit sphere unpacks to a nonzero vector
in `ℝ⁸`. -/
private theorem sphereSevenUnpack_nonzero (z : QuaternionSphereSeven) :
    sphereSevenUnpack z.1 ≠ 0 := by
  -- Otherwise packing back would contradict that the quaternionic point lies on the unit sphere.
  intro hunpack
  have hzero : sphereSevenUnpack z.1 = sphereSevenUnpack 0 := by
    exact hunpack.trans sphereSevenUnpack_zero.symm
  have hz0 : z.1 = 0 := sphereSevenUnpack_injective hzero
  have hznorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  simp [hz0] at hznorm

/-- Helper for Example 9.4.9: the packed Euclidean sphere point, normalized in `ℍ²`, is the
chosen representative on `QuaternionSphereSeven`. -/
private def packedSpherePoint (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :
    QuaternionSphereSeven :=
  ⟨((‖quaternionPack x.1‖)⁻¹ : ℝ) • quaternionPack x.1,
    invNorm_smul_mem_unitSphere _ (quaternionPack_nonzero x)⟩

/-- Helper for Example 9.4.9: the unpacked quaternionic sphere point, normalized in `ℝ⁸`, is the
corresponding point on the Euclidean `S⁷`. -/
private def unpackedSpherePoint (z : QuaternionSphereSeven) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 :=
  ⟨((‖sphereSevenUnpack z.1‖)⁻¹ : ℝ) • sphereSevenUnpack z.1,
    invNorm_smul_mem_unitSphere _ (sphereSevenUnpack_nonzero z)⟩

/-- Helper for Example 9.4.9: the radial normalization from the Euclidean `S⁷` to the packed
quaternionic sphere is continuous. -/
private theorem packedSpherePoint_continuous :
    Continuous packedSpherePoint := by
  -- The packed quaternionic vector never vanishes on the source sphere, so radial normalization
  -- is continuous on the whole subtype.
  have hpack : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 ↦
      quaternionPack x.1 :=
    quaternionPack_continuous.comp continuous_subtype_val
  have hnormInv : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 ↦
      ((‖quaternionPack x.1‖)⁻¹ : ℝ) :=
    (hpack.norm).inv₀ fun x ↦ norm_ne_zero_iff.mpr (quaternionPack_nonzero x)
  have hnormalized :
      Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 ↦
        ((‖quaternionPack x.1‖)⁻¹ : ℝ) • quaternionPack x.1 :=
    hnormInv.smul hpack
  exact Continuous.subtype_mk hnormalized fun x ↦ (packedSpherePoint x).2

/-- Helper for Example 9.4.9: the restricted unpacking map from the quaternionic unit sphere is
continuous. -/
private theorem unpackedSpherePoint_continuous :
    Continuous unpackedSpherePoint := by
  -- The same radial-normalization argument applies after unpacking back to `ℝ⁸`.
  have hunpack : Continuous fun z : QuaternionSphereSeven ↦ sphereSevenUnpack z.1 :=
    sphereSevenUnpack_continuous.comp continuous_subtype_val
  have hnormInv : Continuous fun z : QuaternionSphereSeven ↦
      ((‖sphereSevenUnpack z.1‖)⁻¹ : ℝ) :=
    (hunpack.norm).inv₀ fun z ↦ norm_ne_zero_iff.mpr (sphereSevenUnpack_nonzero z)
  have hnormalized : Continuous fun z : QuaternionSphereSeven ↦
      ((‖sphereSevenUnpack z.1‖)⁻¹ : ℝ) • sphereSevenUnpack z.1 :=
    hnormInv.smul hunpack
  exact Continuous.subtype_mk hnormalized fun z ↦ (unpackedSpherePoint z).2

/-- Helper for Example 9.4.9: unpacking the packed sphere point recovers the original point of the
Euclidean unit sphere. -/
private theorem unpackedSpherePoint_packedSpherePoint
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :
    unpackedSpherePoint (packedSpherePoint x) = x := by
  -- Unpacking the normalized packed vector gives the same positive real multiple of `x`, and the
  -- outer normalization returns the original Euclidean unit vector.
  apply Subtype.ext
  have hpos : 0 < ((‖quaternionPack x.1‖)⁻¹ : ℝ) := by
    exact inv_pos.mpr (norm_pos_iff.mpr (quaternionPack_nonzero x))
  simpa [packedSpherePoint, unpackedSpherePoint, sphereSevenUnpack_real_smul,
    sphereSevenUnpack_quaternionPack] using
    (invNorm_smul_eq_of_mem_unitSphere x.2 hpos)

/-- Helper for Example 9.4.9: packing the unpacked sphere point recovers the original point of the
quaternionic unit sphere. -/
private theorem packedSpherePoint_unpackedSpherePoint (z : QuaternionSphereSeven) :
    packedSpherePoint (unpackedSpherePoint z) = z := by
  -- Packing the normalized unpacked vector gives the same positive real multiple of `z`, and the
  -- outer normalization returns the original quaternionic unit vector.
  apply Subtype.ext
  have hpos : 0 < ((‖sphereSevenUnpack z.1‖)⁻¹ : ℝ) := by
    exact inv_pos.mpr (norm_pos_iff.mpr (sphereSevenUnpack_nonzero z))
  simpa [packedSpherePoint, unpackedSpherePoint, quaternionPack_real_smul,
    quaternionPack_sphereSevenUnpack] using
    (invNorm_smul_eq_of_mem_unitSphere z.2 hpos)

/-- Helper for Example 9.4.9: `𝕊 7` identifies with the unit sphere in `ℍ²` by packing the eight
real coordinates into two quaternion coordinates. -/
private def sphereSevenHomeomorphQuaternionSphereSeven :
    𝕊 7 ≃ₜ QuaternionSphereSeven := by
  -- The sphere model `𝕊 7` is the `ULift` of the Euclidean unit sphere, so we package the
  -- explicit packing/unpacking equivalence at the subtype level and transport it across `ULift`.
  let packedHomeomorph :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 ≃ₜ QuaternionSphereSeven :=
    { toEquiv :=
        { toFun := packedSpherePoint
          invFun := unpackedSpherePoint
          left_inv := unpackedSpherePoint_packedSpherePoint
          right_inv := packedSpherePoint_unpackedSpherePoint }
      continuous_toFun := packedSpherePoint_continuous
      continuous_invFun := unpackedSpherePoint_continuous }
  exact Homeomorph.ulift.trans packedHomeomorph

/-- Helper for Example 9.4.9: the inverse source homeomorphism is the normalized unpacking map on
`QuaternionSphereSeven`. -/
private theorem sphereSevenHomeomorphQuaternionSphereSeven_symm_eq_unpackedSpherePoint
    (z : QuaternionSphereSeven) :
    sphereSevenHomeomorphQuaternionSphereSeven.symm z = ULift.up (unpackedSpherePoint z) := by
  -- The explicit source homeomorphism was built by transporting `unpackedSpherePoint` across
  -- `ULift`, so its inverse is definitionally the normalized unpacking map.
  rfl

/-- Helper for Example 9.4.9: normalize a nonzero vector in `ℍ²` onto the unit sphere
`S^7 ⊂ ℍ²`. -/
private def normalizeNonzeroQuaternionVector
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) : QuaternionSphereSeven :=
  ⟨((‖v.1‖)⁻¹ : ℝ) • v.1, invNorm_smul_mem_unitSphere _ v.2⟩

/-- Helper for Example 9.4.9: normalizing a nonzero quaternionic vector does not change its
projective class. -/
private theorem quaternionSphereSevenToProjectivization_normalizeNonzeroQuaternionVector
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) :
    quaternionSphereSevenToProjectivization (normalizeNonzeroQuaternionVector v) =
      Projectivization.mk ℍ v.1 v.2 := by
  -- The normalized vector differs from `v` by a nonzero real scalar, so it spans the same
  -- quaternionic line.
  apply (Projectivization.mk_eq_mk_iff' ℍ
    ((normalizeNonzeroQuaternionVector v).1) v.1
    (quaternionSphereSeven_nonzero (normalizeNonzeroQuaternionVector v)) v.2).2
  refine ⟨((‖v.1‖)⁻¹ : ℍ), ?_⟩
  funext i
  apply Quaternion.ext <;> simp [normalizeNonzeroQuaternionVector, Algebra.smul_def]

/-- Helper for Example 9.4.9: the projective affine chart on a nonzero quaternionic vector is the
ratio `z₀ / z₁`, with `∞` when the denominator vanishes. -/
private def quaternionProjectiveAffineChart
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) : OnePoint ℍ :=
  let _ : DecidableEq ℍ := Classical.decEq ℍ
  if _hv1 : v.1 1 = 0 then
    OnePoint.infty
  else
    ((v.1 1)⁻¹ * v.1 0 : ℍ)

/-- Helper for Example 9.4.9: normalizing a nonzero quaternionic vector does not change its affine
chart. -/
private theorem quaternionQuotientAffineChartValue_normalizeNonzeroQuaternionVector
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) :
    quaternionQuotientAffineChartValue (normalizeNonzeroQuaternionVector v) =
      quaternionProjectiveAffineChart v := by
  -- The common positive real normalization factor neither changes whether the second coordinate
  -- vanishes nor the affine ratio `z₀ / z₁`.
  let _ : DecidableEq ℍ := Classical.decEq ℍ
  have hnorm_ne : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  by_cases hv1 : v.1 1 = 0
  · -- When `v₁ = 0`, both affine charts land at `∞`.
    have hnormCoord :
        (normalizeNonzeroQuaternionVector v).1 1 = 0 := by
      simp [normalizeNonzeroQuaternionVector, hv1]
    simp [quaternionQuotientAffineChartValue, quaternionProjectiveAffineChart, hv1, hnormCoord]
  · -- Away from `v₁ = 0`, the shared real scalar cancels from the quaternionic quotient ratio.
    have hnormCoord :
        (normalizeNonzeroQuaternionVector v).1 1 ≠ 0 := by
      simp [normalizeNonzeroQuaternionVector, hv1, hnorm_ne]
    have hratio :
        ((((normalizeNonzeroQuaternionVector v).1) 1)⁻¹ *
            ((normalizeNonzeroQuaternionVector v).1 0) : ℍ) =
          ((v.1 1)⁻¹ * v.1 0 : ℍ) := by
      let r : ℍ := ‖v.1‖
      have hr_ne : r ≠ 0 := by
        change (((‖v.1‖ : ℝ) : ℍ) ≠ 0)
        intro hr0
        have hrnorm : ‖(((‖v.1‖ : ℝ) : ℍ))‖ = 0 := by
          simpa [hr0]
        have hreal : ‖v.1‖ = 0 := by
          simpa using hrnorm
        exact hnorm_ne hreal
      have hscale : r * (r⁻¹ * v.1 0) = v.1 0 := by
        calc
          r * (r⁻¹ * v.1 0) = (r * r⁻¹) * v.1 0 := by
            rw [mul_assoc]
          _ = v.1 0 := by
            simp [hr_ne]
      simpa [r, normalizeNonzeroQuaternionVector, hv1, hnormCoord, Algebra.smul_def,
        mul_assoc, mul_inv_rev] using hscale
    simpa [quaternionQuotientAffineChartValue, quaternionProjectiveAffineChart, hv1,
      hnormCoord] using hratio

/-- Helper for Example 9.4.9: the normalized representative in `QuaternionSphereSeven` depends
continuously on the nonzero quaternionic vector. -/
private theorem normalizeNonzeroQuaternionVector_continuous :
    Continuous normalizeNonzeroQuaternionVector := by
  -- The normalization factor is continuous on the nonzero-vector subtype, so the normalized
  -- quaternionic representative varies continuously.
  have hval : Continuous fun v : { w : Fin 2 → ℍ // w ≠ 0 } ↦ (v : Fin 2 → ℍ) :=
    continuous_subtype_val
  have hnormInv : Continuous fun v : { w : Fin 2 → ℍ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℍ)‖)⁻¹ : ℝ) :=
    (hval.norm).inv₀ fun v ↦ norm_ne_zero_iff.mpr v.2
  have hnormalized : Continuous fun v : { w : Fin 2 → ℍ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℍ)‖)⁻¹ : ℝ) • (v : Fin 2 → ℍ) :=
    hnormInv.smul hval
  exact Continuous.subtype_mk hnormalized fun v ↦ (normalizeNonzeroQuaternionVector v).2

/-- Helper for Example 9.4.9: equality in `𝕊 4` can be checked on the ambient `ℝ⁵` vectors after
descending through `ULift`. -/
private theorem sphereFour_eq_of_down_val_eq {x y : 𝕊 4}
    (hxy : x.down.1 = y.down.1) : x = y := by
  -- Once the ambient vectors agree, the sphere points agree by subtype extensionality and then by
  -- `ULift.down_injective`.
  apply ULift.down_injective
  apply Subtype.ext
  simpa using hxy

/-- Helper for Example 9.4.9: reflect the ambient `ℝ⁵` model of `S⁴` by negating only the height
coordinate. -/
private def sphereFourHeightReflectionVec
    (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  EuclideanSpace.single 0 (x 0) +
    EuclideanSpace.single 1 (x 1) +
    EuclideanSpace.single 2 (x 2) +
    EuclideanSpace.single 3 (x 3) +
    EuclideanSpace.single 4 (-x 4)

/-- Helper for Example 9.4.9: height reflection preserves the ambient Euclidean norm square on the
`S⁴` model. -/
private theorem sphereFourHeightReflectionVec_normSq
    (x : EuclideanSpace ℝ (Fin 5)) :
    ‖sphereFourHeightReflectionVec x‖ ^ 2 = ‖x‖ ^ 2 := by
  -- Squaring removes the sign on the last coordinate, so the norm square is unchanged.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_five, sphereFourHeightReflectionVec]

/-- Helper for Example 9.4.9: the height reflection sends the concrete `S⁴` carrier to itself. -/
private theorem sphereFourHeightReflectionVec_mem
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
    sphereFourHeightReflectionVec x.1 ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  -- The reflection preserves norm, so it preserves the unit sphere.
  have hxnorm : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hsq : ‖sphereFourHeightReflectionVec x.1‖ ^ 2 = 1 := by
    rw [sphereFourHeightReflectionVec_normSq, hxnorm]
    norm_num
  rw [mem_sphere_zero_iff_norm]
  apply le_antisymm
  · nlinarith [norm_nonneg (sphereFourHeightReflectionVec x.1), hsq]
  · nlinarith [norm_nonneg (sphereFourHeightReflectionVec x.1), hsq]

/-- Helper for Example 9.4.9: reflecting the height coordinate twice is the identity. -/
private theorem sphereFourHeightReflectionVec_involutive
    (x : EuclideanSpace ℝ (Fin 5)) :
    sphereFourHeightReflectionVec (sphereFourHeightReflectionVec x) = x := by
  -- Negating the last coordinate twice and leaving the first four fixed recovers the source
  -- vector.
  ext i
  fin_cases i <;> simp [sphereFourHeightReflectionVec]

/-- Helper for Example 9.4.9: the height reflection on `S⁴` is continuous. -/
private theorem sphereFourHeightReflection_continuous :
    Continuous fun x : 𝕊 4 ↦
      (ULift.up
        (⟨sphereFourHeightReflectionVec x.down.1,
          sphereFourHeightReflectionVec_mem x.down⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) : 𝕊 4) := by
  -- The ambient coordinates are continuous on `𝕊 4`, and the reflected height coordinate is just
  -- a negation of the last one.
  have hdown : Continuous fun x : 𝕊 4 ↦
      (((x.down : Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
          EuclideanSpace ℝ (Fin 5))) :=
    continuous_subtype_val.comp continuous_uliftDown
  have h0 : Continuous fun x : 𝕊 4 ↦ x.down.1 0 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 0).continuous.comp hdown
  have h1 : Continuous fun x : 𝕊 4 ↦ x.down.1 1 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 1).continuous.comp hdown
  have h2 : Continuous fun x : 𝕊 4 ↦ x.down.1 2 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 2).continuous.comp hdown
  have h3 : Continuous fun x : 𝕊 4 ↦ x.down.1 3 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 3).continuous.comp hdown
  have h4 : Continuous fun x : 𝕊 4 ↦ x.down.1 4 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) 4).continuous.comp hdown
  have hVec : Continuous fun x : 𝕊 4 ↦ sphereFourHeightReflectionVec x.down.1 := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 5 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 5 ↦ ?_
    fin_cases i
    · simpa [sphereFourHeightReflectionVec] using h0
    · simpa [sphereFourHeightReflectionVec] using h1
    · simpa [sphereFourHeightReflectionVec] using h2
    · simpa [sphereFourHeightReflectionVec] using h3
    · simpa [sphereFourHeightReflectionVec] using h4.neg
  have hSphere : Continuous fun x : 𝕊 4 ↦
      (⟨sphereFourHeightReflectionVec x.down.1,
        sphereFourHeightReflectionVec_mem x.down⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
    Continuous.subtype_mk hVec fun x ↦ sphereFourHeightReflectionVec_mem x.down
  simpa using continuous_uliftUp.comp hSphere

/-- Helper for Example 9.4.9: the target-side height reflection on `S⁴`. -/
private noncomputable def sphereFourHeightReflection : 𝕊 4 ≃ₜ 𝕊 4 where
  toEquiv :=
    { toFun := fun x ↦
        ULift.up
          ⟨sphereFourHeightReflectionVec x.down.1,
            sphereFourHeightReflectionVec_mem x.down⟩
      invFun := fun x ↦
        ULift.up
          ⟨sphereFourHeightReflectionVec x.down.1,
            sphereFourHeightReflectionVec_mem x.down⟩
      left_inv := by
        intro x
        apply sphereFour_eq_of_down_val_eq
        simp [sphereFourHeightReflectionVec_involutive]
      right_inv := by
        intro x
        apply sphereFour_eq_of_down_val_eq
        simp [sphereFourHeightReflectionVec_involutive] }
  continuous_toFun := sphereFourHeightReflection_continuous
  continuous_invFun := sphereFourHeightReflection_continuous

/-- Helper for Example 9.4.9: applying the height reflection amounts to negating only the final
ambient coordinate. -/
private theorem sphereFourHeightReflection_apply_down_val (x : 𝕊 4) :
    (sphereFourHeightReflection x).down.1 = sphereFourHeightReflectionVec x.down.1 := by
  -- The reflection was defined directly on the ambient `ℝ⁵` model.
  rfl

/-- Helper for Example 9.4.9: the explicit quaternionic Hopf map varies continuously with the
source point on `S⁷`. -/
private theorem quaternionicHopfMap_continuous :
    Continuous quaternionicHopfMap := by
  -- Read the eight real source coordinates through the `ULift` sphere model.
  have hdown : Continuous fun x : 𝕊 7 ↦
      (((x.down : Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :
          EuclideanSpace ℝ (Fin 8))) :=
    continuous_subtype_val.comp continuous_uliftDown
  have h0 : Continuous fun x : 𝕊 7 ↦ x.down.1 0 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 0).continuous.comp hdown
  have h1 : Continuous fun x : 𝕊 7 ↦ x.down.1 1 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 1).continuous.comp hdown
  have h2 : Continuous fun x : 𝕊 7 ↦ x.down.1 2 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 2).continuous.comp hdown
  have h3 : Continuous fun x : 𝕊 7 ↦ x.down.1 3 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 3).continuous.comp hdown
  have h4 : Continuous fun x : 𝕊 7 ↦ x.down.1 4 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 4).continuous.comp hdown
  have h5 : Continuous fun x : 𝕊 7 ↦ x.down.1 5 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 5).continuous.comp hdown
  have h6 : Continuous fun x : 𝕊 7 ↦ x.down.1 6 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 6).continuous.comp hdown
  have h7 : Continuous fun x : 𝕊 7 ↦ x.down.1 7 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 8) 7).continuous.comp hdown
  have hLeftVec : Continuous fun x : 𝕊 7 ↦
      (!₂[x.down.1 0, x.down.1 1, x.down.1 2, x.down.1 3] : EuclideanSpace ℝ (Fin 4)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hRightVec : Continuous fun x : 𝕊 7 ↦
      (!₂[x.down.1 4, x.down.1 5, x.down.1 6, x.down.1 7] : EuclideanSpace ℝ (Fin 4)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa using h4
    · simpa using h5
    · simpa using h6
    · simpa using h7
  have hLeft : Continuous quaternionicLeft := by
    change Continuous fun x : 𝕊 7 ↦
      Quaternion.linearIsometryEquivTuple.symm
        (!₂[x.down.1 0, x.down.1 1, x.down.1 2, x.down.1 3] : EuclideanSpace ℝ (Fin 4))
    exact Quaternion.linearIsometryEquivTuple.symm.continuous.comp hLeftVec
  have hRight : Continuous quaternionicRight := by
    change Continuous fun x : 𝕊 7 ↦
      Quaternion.linearIsometryEquivTuple.symm
        (!₂[x.down.1 4, x.down.1 5, x.down.1 6, x.down.1 7] : EuclideanSpace ℝ (Fin 4))
    exact Quaternion.linearIsometryEquivTuple.symm.continuous.comp hRightVec
  have hMixed : Continuous fun x : 𝕊 7 ↦
      quaternionicLeft x * star (quaternionicRight x) :=
    hLeft.mul (continuous_star.comp hRight)
  have hLeftRe : Continuous fun x : 𝕊 7 ↦ (quaternionicLeft x).re :=
    Quaternion.continuous_re.comp hLeft
  have hLeftImI : Continuous fun x : 𝕊 7 ↦ (quaternionicLeft x).imI :=
    Quaternion.continuous_imI.comp hLeft
  have hLeftImJ : Continuous fun x : 𝕊 7 ↦ (quaternionicLeft x).imJ :=
    Quaternion.continuous_imJ.comp hLeft
  have hLeftImK : Continuous fun x : 𝕊 7 ↦ (quaternionicLeft x).imK :=
    Quaternion.continuous_imK.comp hLeft
  have hRightRe : Continuous fun x : 𝕊 7 ↦ (quaternionicRight x).re :=
    Quaternion.continuous_re.comp hRight
  have hRightImI : Continuous fun x : 𝕊 7 ↦ (quaternionicRight x).imI :=
    Quaternion.continuous_imI.comp hRight
  have hRightImJ : Continuous fun x : 𝕊 7 ↦ (quaternionicRight x).imJ :=
    Quaternion.continuous_imJ.comp hRight
  have hRightImK : Continuous fun x : 𝕊 7 ↦ (quaternionicRight x).imK :=
    Quaternion.continuous_imK.comp hRight
  have hVec : Continuous quaternionicHopfMapVec := by
    -- Each target coordinate is an explicit polynomial in the quaternionic coordinates.
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 5 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 5 ↦ ?_
    fin_cases i
    · simpa [quaternionicHopfMapVec, Quaternion.re_mul, mul_add, add_mul] using
        (((continuous_const.mul (hLeftRe.mul hRightRe)).add
          (continuous_const.mul (hLeftImI.mul hRightImI))).add
            (continuous_const.mul (hLeftImJ.mul hRightImJ))).add
              (continuous_const.mul (hLeftImK.mul hRightImK))
    · simpa [quaternionicHopfMapVec, Quaternion.imI_mul, mul_add, add_mul] using
        ((((continuous_const.mul (hLeftRe.mul hRightImI)).neg.add
          (continuous_const.mul (hLeftImI.mul hRightRe))).add
            (continuous_const.mul (hLeftImJ.mul hRightImK)).neg).add
              (continuous_const.mul (hLeftImK.mul hRightImJ)))
    · simpa [quaternionicHopfMapVec, Quaternion.imJ_mul, mul_add, add_mul] using
        ((((continuous_const.mul (hLeftRe.mul hRightImJ)).neg.add
          (continuous_const.mul (hLeftImI.mul hRightImK))).add
            (continuous_const.mul (hLeftImJ.mul hRightRe))).add
              (continuous_const.mul (hLeftImK.mul hRightImI)).neg)
    · simpa [quaternionicHopfMapVec, Quaternion.imK_mul, mul_add, add_mul] using
        ((((continuous_const.mul (hLeftRe.mul hRightImK)).neg.add
          (continuous_const.mul (hLeftImI.mul hRightImJ)).neg).add
            (continuous_const.mul (hLeftImJ.mul hRightImI))).add
              (continuous_const.mul (hLeftImK.mul hRightRe)))
    · simpa [quaternionicHopfMapVec] using
        (Quaternion.continuous_normSq.comp hLeft).sub
          (Quaternion.continuous_normSq.comp hRight)
  have hSphere : Continuous fun x : 𝕊 7 ↦
      (⟨quaternionicHopfMapVec x, quaternionicHopfMapVec_mem x⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
    Continuous.subtype_mk hVec fun x ↦ quaternionicHopfMapVec_mem x
  -- Then lift the subtype-valued map back to `𝕊 4`.
  simpa [quaternionicHopfMap] using continuous_uliftUp.comp hSphere

/-- Helper for Example 9.4.9: fix the target `S⁴` model at universe level `0` in the reflected
chart package. -/
private abbrev SphereFour := TopCat.sphere.{0} 4

/-- Helper for Example 9.4.9: fix the source `S⁷` model at universe level `0` in the reflected
chart package. -/
private abbrev SphereSeven := TopCat.sphere.{0} 7

/-- Helper for Example 9.4.9: the reflected target homeomorphism viewed as a fixed `S⁴ → S⁴`
function. -/
private noncomputable def reflectedSphereFourMap : SphereFour → SphereFour :=
  (sphereFourHeightReflection : SphereFour ≃ₜ SphereFour)

/-- Helper for Example 9.4.9: the quaternionic stereographic chart viewed as a fixed
`OnePoint ℍ → S⁴` function. -/
private noncomputable def onePointQuaternionToSphereFour : OnePoint ℍ → SphereFour :=
  (onePointQuaternionStereographicHomeomorphSphereFour : OnePoint ℍ ≃ₜ SphereFour)

/-- Helper for Example 9.4.9: the source homeomorphism inverse viewed as a fixed
`QuaternionSphereSeven → S⁷` function. -/
private noncomputable def quaternionSphereSevenToSphereSeven : QuaternionSphereSeven → SphereSeven :=
  (sphereSevenHomeomorphQuaternionSphereSeven : SphereSeven ≃ₜ QuaternionSphereSeven).symm

/-- Helper for Example 9.4.9: the reflected affine chart on `QuaternionSphereSeven` should agree
with the explicit quaternionic Hopf map. -/
private theorem reflectedQuaternionicHopfQuotientAffineChartComparison
    (z : QuaternionSphereSeven) :
    reflectedSphereFourMap (onePointQuaternionToSphereFour (qQuaternion z)) =
      (quaternionicHopfMap : SphereSeven → SphereFour) (quaternionSphereSevenToSphereSeven z) := by
  -- TODO: split on `z.1 1 = 0`; in the finite branch compare the reflected quaternionic
  -- stereographic coordinates with the normalized Hopf coordinates on `QuaternionSphereSeven`,
  -- and in the zero branch identify the reflected south pole.
  sorry

/-- Helper for Example 9.4.9: the affine ratio chart is unchanged by quaternionic rescaling of a
nonzero vector. -/
private theorem quaternionProjectiveAffineChart_scaleInvariant
    (a b : { w : Fin 2 → ℍ // w ≠ 0 }) (t : ℍ) (h : a = t • (b : Fin 2 → ℍ)) :
    quaternionProjectiveAffineChart a = quaternionProjectiveAffineChart b := by
  -- The affine ratio `(t • b)₀ / (t • b)₁` is the same as `b₀ / b₁`; the `t = 0` case is
  -- impossible because `a` is nonzero.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  have hEq :
      quaternionProjectiveAffineChart a = quaternionProjectiveAffineChart b := by
    by_cases hb1 : b.1 1 = 0
    · have ha1 : a.1 1 = 0 := by
        simpa [Pi.smul_apply, hb1] using congrArg (fun z : Fin 2 → ℍ ↦ z 1) h
      simp [quaternionProjectiveAffineChart, ha1, hb1]
    · have ha1 : a.1 1 ≠ 0 := by
        have ha1mul : a.1 1 = t * b.1 1 := by
          simpa [Pi.smul_apply] using congrArg (fun z : Fin 2 → ℍ ↦ z 1) h
        rw [ha1mul]
        exact mul_ne_zero ht hb1
      have hratio :
          ((a.1 1)⁻¹ * a.1 0 : ℍ) = ((b.1 1)⁻¹ * b.1 0 : ℍ) := by
        rw [h]
        simp [smul_eq_mul, ht, mul_assoc]
      simp [quaternionProjectiveAffineChart, ha1, hb1, hratio]
  exact hEq

/-- Helper for Example 9.4.9: the reflected sphere-valued affine chart on nonzero quaternionic
representatives. -/
private def reflectedProjectiveSphereChart
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) : SphereFour :=
  reflectedSphereFourMap (onePointQuaternionToSphereFour (quaternionProjectiveAffineChart v))

/-- Helper for Example 9.4.9: the reflected sphere chart rewritten through the normalized Hopf
comparison representative. -/
private def normalizedReflectedProjectiveSphereChart
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) : SphereFour :=
  (quaternionicHopfMap : SphereSeven → SphereFour)
    (quaternionSphereSevenToSphereSeven (normalizeNonzeroQuaternionVector v))

/-- Helper for Example 9.4.9: the reflected projective chart agrees with the normalized Hopf-side
representative. -/
private theorem reflectedProjectiveSphereChart_eq_normalizedHopf
    (v : { w : Fin 2 → ℍ // w ≠ 0 }) :
    reflectedProjectiveSphereChart v = normalizedReflectedProjectiveSphereChart v := by
  -- Route correction: compare the descended chart only after rewriting both sides to the same
  -- normalized representative in `QuaternionSphereSeven`.
  calc
    reflectedProjectiveSphereChart v
        = reflectedSphereFourMap
            (onePointQuaternionToSphereFour (quaternionProjectiveAffineChart v)) := by
              rfl
    _ = reflectedSphereFourMap
          (onePointQuaternionToSphereFour
            (quaternionQuotientAffineChartValue (normalizeNonzeroQuaternionVector v))) := by
              rw [quaternionQuotientAffineChartValue_normalizeNonzeroQuaternionVector]
    _ = reflectedSphereFourMap
          (onePointQuaternionToSphereFour
            (qQuaternion (normalizeNonzeroQuaternionVector v))) := by
              rw [qQuaternion_eq_quaternionQuotientAffineChartValue]
    _ = normalizedReflectedProjectiveSphereChart v := by
          simpa [normalizedReflectedProjectiveSphereChart] using
            reflectedQuaternionicHopfQuotientAffineChartComparison
              (normalizeNonzeroQuaternionVector v)

/-- Helper for Example 9.4.9: the sphere-valued reflected chart on nonzero quaternionic vectors is
continuous because it is the Hopf map on the normalized representative. -/
private theorem reflectedProjectiveSphereChart_continuous :
    Continuous reflectedProjectiveSphereChart := by
  -- Rewrite the chart through the normalized Hopf comparison, where all maps are already known to
  -- be continuous.
  have hHopf : Continuous normalizedReflectedProjectiveSphereChart :=
    quaternionicHopfMap_continuous.comp
      (sphereSevenHomeomorphQuaternionSphereSeven.continuous_symm.comp
        normalizeNonzeroQuaternionVector_continuous)
  have hEq : reflectedProjectiveSphereChart = normalizedReflectedProjectiveSphereChart := by
    funext v
    exact reflectedProjectiveSphereChart_eq_normalizedHopf v
  rw [hEq]
  exact hHopf

/-- Helper for Example 9.4.9: the reflected sphere-valued affine chart is unchanged by
quaternionic rescaling of a nonzero representative. -/
private theorem reflectedProjectiveSphereChart_scaleInvariant
    (a b : { w : Fin 2 → ℍ // w ≠ 0 }) (t : ℍ) (h : a = t • (b : Fin 2 → ℍ)) :
    reflectedProjectiveSphereChart a = reflectedProjectiveSphereChart b := by
  -- The reflected sphere chart depends only on the affine ratio, so it inherits the same
  -- scale-invariance as `quaternionProjectiveAffineChart`.
  rw [reflectedProjectiveSphereChart, reflectedProjectiveSphereChart]
  rw [quaternionProjectiveAffineChart_scaleInvariant a b t h]

/-- Helper for Example 9.4.9: the reflected sphere-valued projective chart descended to `ℍP¹`.
-/
private def descendedReflectedProjectiveSphereChart :
    QuaternionProjectiveLine → SphereFour :=
  Projectivization.lift reflectedProjectiveSphereChart reflectedProjectiveSphereChart_scaleInvariant

/-- Helper for Example 9.4.9: the affine `OnePoint ℍ` chart on `ℍP¹` composed with the reflected
stereographic identification to `S⁴`. -/
private def reflectedAffineSphereComparison (x : QuaternionProjectiveLine) : SphereFour :=
  reflectedSphereFourMap
    (onePointQuaternionToSphereFour
      (quaternionProjectiveLineEquivOnePointQuaternion.symm x))

/-- Helper for Example 9.4.9: the descended reflected sphere-valued chart agrees with the affine
`OnePoint ℍ` chart on `ℍP¹`. -/
private theorem reflectedProjectiveSphereChart_descends_toAffineChart
    (x : QuaternionProjectiveLine) :
    descendedReflectedProjectiveSphereChart x = reflectedAffineSphereComparison x := by
  -- Check the equality on a nonzero representative, where the normalized representative gives the
  -- same projective point and the same affine chart.
  induction x using Projectivization.ind with
  | h v hv =>
      calc
        descendedReflectedProjectiveSphereChart (Projectivization.mk ℍ v hv)
            = reflectedProjectiveSphereChart ⟨v, hv⟩ := by
                simp [descendedReflectedProjectiveSphereChart, Projectivization.lift_mk]
        _ = reflectedSphereFourMap
              (onePointQuaternionToSphereFour
                (quaternionProjectiveAffineChart ⟨v, hv⟩)) := by
                  rfl
        _ = reflectedSphereFourMap
              (onePointQuaternionToSphereFour
                (quaternionQuotientAffineChartValue
                  (normalizeNonzeroQuaternionVector ⟨v, hv⟩))) := by
                    rw [quaternionQuotientAffineChartValue_normalizeNonzeroQuaternionVector]
        _ = reflectedSphereFourMap
              (onePointQuaternionToSphereFour
                (quaternionProjectiveLineEquivOnePointQuaternion.symm
                  (quaternionSphereSevenToProjectivization
                    (normalizeNonzeroQuaternionVector ⟨v, hv⟩)))) := by
                      rw [quaternionQuotientAffineChartFormula]
        _ = reflectedAffineSphereComparison (Projectivization.mk ℍ v hv) := by
              rw [quaternionSphereSevenToProjectivization_normalizeNonzeroQuaternionVector]
              rfl

/-- Helper for Example 9.4.9: the affine-chart equivalence `ℍP¹ ≃ OnePoint ℍ` becomes continuous
once the reflected sphere-valued chart is descended through `Projectivization.lift`. -/
private theorem quaternionProjectiveLineEquivOnePointQuaternion_symm_continuous :
    Continuous quaternionProjectiveLineEquivOnePointQuaternion.symm := by
  -- Route correction: descend the reflected sphere-valued chart directly from nonzero vectors via
  -- `Projectivization.lift`, then recover the affine chart by composing with the inverse
  -- reflected stereographic homeomorphism.
  have hRel :
      ∀ a b : { w : Fin 2 → ℍ // w ≠ 0 },
        (projectivizationSetoid ℍ (Fin 2 → ℍ)).r a b →
          reflectedProjectiveSphereChart a = reflectedProjectiveSphereChart b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨u, rfl⟩
    let scaled : { w : Fin 2 → ℍ // w ≠ 0 } :=
      ⟨u • b, by
        intro hub
        apply ha
        simpa using hub⟩
    calc
      reflectedProjectiveSphereChart scaled
          = reflectedSphereFourMap
              (onePointQuaternionToSphereFour
                (quaternionProjectiveAffineChart scaled)) := by
                    rfl
      _ = reflectedSphereFourMap
            (onePointQuaternionToSphereFour
              (quaternionProjectiveAffineChart ⟨b, hb⟩)) := by
                rw [quaternionProjectiveAffineChart_scaleInvariant
                  (a := scaled) (b := ⟨b, hb⟩) (t := (u : ℍ)) rfl]
      _ = reflectedProjectiveSphereChart ⟨b, hb⟩ := by
            rfl
  have hDesc : Continuous descendedReflectedProjectiveSphereChart := by
    simpa [descendedReflectedProjectiveSphereChart, Projectivization.lift] using
      reflectedProjectiveSphereChart_continuous.quotient_lift hRel
  have hDescEq :
      descendedReflectedProjectiveSphereChart = reflectedAffineSphereComparison := by
    funext x
    exact reflectedProjectiveSphereChart_descends_toAffineChart x
  have hComp : Continuous reflectedAffineSphereComparison := by
    rw [← hDescEq]
    exact hDesc
  have hRecover :
      quaternionProjectiveLineEquivOnePointQuaternion.symm =
        ((onePointQuaternionStereographicHomeomorphSphereFour : OnePoint ℍ ≃ₜ SphereFour).symm) ∘
          ((sphereFourHeightReflection : SphereFour ≃ₜ SphereFour).symm) ∘
            reflectedAffineSphereComparison := by
    funext x
    simp [Function.comp, reflectedAffineSphereComparison, reflectedSphereFourMap,
      onePointQuaternionToSphereFour]
  -- Compose with the inverse reflected stereographic homeomorphism to recover the affine chart.
  rw [hRecover]
  exact
    ((onePointQuaternionStereographicHomeomorphSphereFour :
        OnePoint ℍ ≃ₜ SphereFour).continuous_symm).comp
      (((sphereFourHeightReflection : SphereFour ≃ₜ SphereFour).continuous_symm).comp hComp)

/-- Helper for Example 9.4.9: the quotient model `ℍP¹` is canonically homeomorphic to
`OnePoint ℍ` once the reflected affine chart is known to agree with the quaternionic Hopf
comparison. -/
private noncomputable def quaternionProjectiveLineHomeomorphOnePointQuaternion :
    QuaternionProjectiveLine ≃ₜ OnePoint ℍ :=
  Continuous.homeoOfEquivCompactToT2
    (f := quaternionProjectiveLineEquivOnePointQuaternion.symm)
    quaternionProjectiveLineEquivOnePointQuaternion_symm_continuous

/-- Helper for Example 9.4.9: the canonical `QuaternionProjectiveLine ≃ₜ OnePoint ℍ` sends a
projective point to its affine-chart value. -/
private theorem quaternionProjectiveLineHomeomorphOnePointQuaternion_apply
    (x : QuaternionProjectiveLine) :
    quaternionProjectiveLineHomeomorphOnePointQuaternion x =
      quaternionProjectiveLineEquivOnePointQuaternion.symm x := by
  -- The homeomorphism was packaged from the existing affine-chart equivalence without changing
  -- its underlying function.
  rfl

/-- Helper for Example 9.4.9: the corrected homeomorphism `ℍP¹ ≃ₜ S⁴` is the reflected
stereographic chart composed with the affine `OnePoint ℍ` model. -/
private noncomputable def quaternionProjectiveLineHomeomorphSphereFour :
    QuaternionProjectiveLine ≃ₜ 𝕊 4 :=
  show QuaternionProjectiveLine ≃ₜ SphereFour from
    quaternionProjectiveLineHomeomorphOnePointQuaternion.trans
      ((onePointQuaternionStereographicHomeomorphSphereFour : OnePoint ℍ ≃ₜ SphereFour).trans
        (sphereFourHeightReflection : SphereFour ≃ₜ SphereFour))

/-- Example 9.4.9 (1): the quaternionic Hopf map `ν : S^7 → S^4` arises from the quotient
`S^7 ⊂ ℍ² → ℍP¹ ≃ S⁴`. -/
theorem quaternionicHopfMap_isQuaternionicQuotient :
    IsQuaternionicHopfQuotientMap quaternionicHopfMap := by
  -- Route correction: the unreflected stereographic chart has the wrong pole orientation for the
  -- chosen quaternionic source packaging, so the witness must use the reflected target chart.
  refine ⟨sphereSevenHomeomorphQuaternionSphereSeven,
    (show QuaternionProjectiveLine ≃ₜ 𝕊 4 from quaternionProjectiveLineHomeomorphSphereFour), ?_⟩
  funext x
  calc
    quaternionicHopfMap x
        = quaternionicHopfMap (sphereSevenHomeomorphQuaternionSphereSeven.symm
            (sphereSevenHomeomorphQuaternionSphereSeven x)) := by
              rw [sphereSevenHomeomorphQuaternionSphereSeven.symm_apply_apply]
    _ = sphereFourHeightReflection
          (onePointQuaternionStereographicHomeomorphSphereFour
            (qQuaternion (sphereSevenHomeomorphQuaternionSphereSeven x))) := by
              simpa [reflectedSphereFourMap, onePointQuaternionToSphereFour,
                quaternionSphereSevenToSphereSeven] using
                (reflectedQuaternionicHopfQuotientAffineChartComparison
                  (sphereSevenHomeomorphQuaternionSphereSeven x)).symm
    _ = quaternionProjectiveLineHomeomorphSphereFour
          (quaternionSphereSevenToProjectivization
            (sphereSevenHomeomorphQuaternionSphereSeven x)) := by
              rw [quaternionProjectiveLineHomeomorphSphereFour, Homeomorph.trans_apply,
                Homeomorph.trans_apply, quaternionProjectiveLineHomeomorphOnePointQuaternion_apply,
                qQuaternion, Function.comp]

/-- Any quaternionic Hopf quotient map `ν : S^7 → S^4` is a bundle map with fiber `S³`. -/
theorem quaternionicHopfQuotientMap_isFiberBundle {ν : 𝕊 7 → 𝕊 4}
    (hν : IsQuaternionicHopfQuotientMap ν) : IsFiberBundleMap (𝕊 3) ν := by
  -- Route correction: the transport step is already available from Example 9.4.8 through
  -- `isFiberBundleMap_congrHomeomorph`. The remaining missing owner is the raw quaternionic
  -- affine-chart bundle theorem for `qQuaternion`, together with the continuity/homeomorphism
  -- upgrade that identifies `qQuaternion` with `quaternionSphereSevenToProjectivization`.
  -- TODO: prove a two-chart trivialization for `qQuaternion : QuaternionSphereSeven → OnePoint ℍ`,
  -- then transport it across the source and target homeomorphisms extracted from `hν`.
  sorry

/-- Example 9.4.9 (2): the quaternionic Hopf map `ν : S^7 → S^4` is a fiber bundle over `S⁴`
with fiber `S³`. -/
theorem quaternionicHopfMap_isFiberBundle :
    IsFiberBundleMap (TopCat.sphere.{0} 3)
      (quaternionicHopfMap : TopCat.sphere.{0} 7 → TopCat.sphere.{0} 4) :=
  quaternionicHopfQuotientMap_isFiberBundle quaternionicHopfMap_isQuaternionicQuotient

/-- The real eight-dimensional vector space used as a concrete model for Cayley numbers. -/
abbrev CayleyNumber := EuclideanSpace ℝ (Fin 8)

/-- Conjugation on the concrete Cayley-number model. -/
def cayleyConj (a : CayleyNumber) : CayleyNumber :=
  EuclideanSpace.single 0 (a 0) +
    EuclideanSpace.single 1 (-a 1) +
    EuclideanSpace.single 2 (-a 2) +
    EuclideanSpace.single 3 (-a 3) +
    EuclideanSpace.single 4 (-a 4) +
    EuclideanSpace.single 5 (-a 5) +
    EuclideanSpace.single 6 (-a 6) +
    EuclideanSpace.single 7 (-a 7)

/-- The standard Cayley-number multiplication in coordinates. -/
def cayleyMul (a b : CayleyNumber) : CayleyNumber :=
  EuclideanSpace.single 0
      (a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3 - a 4 * b 4 - a 5 * b 5 -
        a 6 * b 6 - a 7 * b 7) +
    EuclideanSpace.single 1
      (a 0 * b 1 + a 1 * b 0 + a 2 * b 3 - a 3 * b 2 + a 4 * b 5 - a 5 * b 4 -
        a 6 * b 7 + a 7 * b 6) +
    EuclideanSpace.single 2
      (a 0 * b 2 - a 1 * b 3 + a 2 * b 0 + a 3 * b 1 + a 4 * b 6 + a 5 * b 7 -
        a 6 * b 4 - a 7 * b 5) +
    EuclideanSpace.single 3
      (a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0 + a 4 * b 7 - a 5 * b 6 +
        a 6 * b 5 - a 7 * b 4) +
    EuclideanSpace.single 4
      (a 0 * b 4 - a 1 * b 5 - a 2 * b 6 - a 3 * b 7 + a 4 * b 0 + a 5 * b 1 +
        a 6 * b 2 + a 7 * b 3) +
    EuclideanSpace.single 5
      (a 0 * b 5 + a 1 * b 4 - a 2 * b 7 + a 3 * b 6 - a 4 * b 1 + a 5 * b 0 -
        a 6 * b 3 + a 7 * b 2) +
    EuclideanSpace.single 6
      (a 0 * b 6 + a 1 * b 7 + a 2 * b 4 - a 3 * b 5 - a 4 * b 2 + a 5 * b 3 +
        a 6 * b 0 - a 7 * b 1) +
    EuclideanSpace.single 7
      (a 0 * b 7 - a 1 * b 6 + a 2 * b 5 + a 3 * b 4 - a 4 * b 3 - a 5 * b 2 +
        a 6 * b 1 + a 7 * b 0)

/-- The squared norm on the concrete Cayley-number model. -/
def cayleyNormSq (a : CayleyNumber) : ℝ :=
  a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2

/-- The first Cayley-number coordinate of a point of `S^15 ⊂ ℝ¹⁶`. -/
def cayleyLeft (x : 𝕊 15) : CayleyNumber :=
  EuclideanSpace.single 0 (x.down.1 0) +
    EuclideanSpace.single 1 (x.down.1 1) +
    EuclideanSpace.single 2 (x.down.1 2) +
    EuclideanSpace.single 3 (x.down.1 3) +
    EuclideanSpace.single 4 (x.down.1 4) +
    EuclideanSpace.single 5 (x.down.1 5) +
    EuclideanSpace.single 6 (x.down.1 6) +
    EuclideanSpace.single 7 (x.down.1 7)

/-- The second Cayley-number coordinate of a point of `S^15 ⊂ ℝ¹⁶`. -/
def cayleyRight (x : 𝕊 15) : CayleyNumber :=
  EuclideanSpace.single 0 (x.down.1 8) +
    EuclideanSpace.single 1 (x.down.1 9) +
    EuclideanSpace.single 2 (x.down.1 10) +
    EuclideanSpace.single 3 (x.down.1 11) +
    EuclideanSpace.single 4 (x.down.1 12) +
    EuclideanSpace.single 5 (x.down.1 13) +
    EuclideanSpace.single 6 (x.down.1 14) +
    EuclideanSpace.single 7 (x.down.1 15)

/-- The standard Cayley-number coordinate formula underlying the Hopf map `S^15 → S^8`. -/
def cayleyHopfMapVec (x : 𝕊 15) : EuclideanSpace ℝ (Fin 9) :=
  let u := cayleyLeft x
  let v := cayleyRight x
  let uv := cayleyMul u (cayleyConj v)
  EuclideanSpace.single 0 (2 * uv 0) +
    EuclideanSpace.single 1 (2 * uv 1) +
    EuclideanSpace.single 2 (2 * uv 2) +
    EuclideanSpace.single 3 (2 * uv 3) +
    EuclideanSpace.single 4 (2 * uv 4) +
    EuclideanSpace.single 5 (2 * uv 5) +
    EuclideanSpace.single 6 (2 * uv 6) +
    EuclideanSpace.single 7 (2 * uv 7) +
    EuclideanSpace.single 8 (cayleyNormSq u - cayleyNormSq v)

/-- Helper for Example 9.4.9: Cayley conjugation preserves the multiplicative norm formula used by
the coordinate Hopf expression. -/
private theorem cayleyNormSq_mul_conj (u v : CayleyNumber) :
    cayleyNormSq (cayleyMul u (cayleyConj v)) = cayleyNormSq u * cayleyNormSq v := by
  -- Direct coordinate expansion gives the classical multiplicativity identity.
  simp [cayleyNormSq, cayleyMul, cayleyConj]
  ring

/-- Helper for Example 9.4.9: the two Cayley-number coordinates of a point of `S^15` have squared
norms summing to `1`. -/
private theorem cayleyLeftRight_normSq (x : 𝕊 15) :
    cayleyNormSq (cayleyLeft x) + cayleyNormSq (cayleyRight x) = 1 := by
  -- Rewrite the ambient `S^15` equation as the sum of the sixteen coordinate squares.
  have hxnorm : ‖x.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.down.2
  have hxnormsq : ‖x.down.1‖ ^ 2 = 1 := by
    nlinarith [hxnorm]
  rw [EuclideanSpace.real_norm_sq_eq] at hxnormsq
  simp [Fin.sum_univ_succ] at hxnormsq
  ring_nf at hxnormsq
  -- The first eight and last eight coordinates are exactly the two Cayley norms.
  calc
    cayleyNormSq (cayleyLeft x) + cayleyNormSq (cayleyRight x)
        = x.down.1 0 ^ 2 + x.down.1 1 ^ 2 + x.down.1 2 ^ 2 + x.down.1 3 ^ 2 + x.down.1 4 ^ 2 +
            x.down.1 5 ^ 2 + x.down.1 6 ^ 2 + x.down.1 7 ^ 2 +
            (x.down.1 8 ^ 2 + x.down.1 9 ^ 2 + x.down.1 10 ^ 2 + x.down.1 11 ^ 2 +
              x.down.1 12 ^ 2 + x.down.1 13 ^ 2 + x.down.1 14 ^ 2 + x.down.1 15 ^ 2) := by
              simp [cayleyNormSq, cayleyLeft, cayleyRight]
    _ = 1 := by
          have hsum := hxnormsq
          abel_nf at hsum ⊢
          exact hsum

/-- The standard Cayley-number coordinate formula lands on the unit sphere `S⁸`. -/
theorem cayleyHopfMapVec_mem (x : 𝕊 15) :
    cayleyHopfMapVec x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 9)) 1 := by
  let u := cayleyLeft x
  let v := cayleyRight x
  let uv := cayleyMul u (cayleyConj v)
  have huv : cayleyNormSq uv = cayleyNormSq u * cayleyNormSq v := by
    -- The Cayley mixed term contributes the product of the source norms.
    simpa [u, v, uv] using cayleyNormSq_mul_conj u v
  have hsplit : cayleyNormSq u + cayleyNormSq v = 1 := by
    simpa [u, v] using cayleyLeftRight_normSq x
  have hsq : ‖cayleyHopfMapVec x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    -- Expanding the nine coordinates reduces the target to the same Hopf polynomial identity.
    calc
      ∑ i, (cayleyHopfMapVec x i) ^ 2
          = 4 * cayleyNormSq uv + (cayleyNormSq u - cayleyNormSq v) ^ 2 := by
              simp [cayleyHopfMapVec, cayleyNormSq, u, v, uv, Fin.sum_univ_succ]
              ring
      _ = 4 * (cayleyNormSq u * cayleyNormSq v) + (cayleyNormSq u - cayleyNormSq v) ^ 2 := by
            rw [huv]
      _ = 1 := by
            nlinarith [hsplit]
  rw [mem_sphere_zero_iff_norm]
  -- A nonnegative real with square `1` must equal `1`.
  apply le_antisymm
  · nlinarith [norm_nonneg (cayleyHopfMapVec x), hsq]
  · nlinarith [norm_nonneg (cayleyHopfMapVec x), hsq]

/-- Example 9.4.9 (3): the Cayley Hopf map `σ : S^15 → S^8` is given by the standard
Cayley-number formula coming from the Cayley numbers. -/
def cayleyHopfMap (x : 𝕊 15) : 𝕊 8 :=
  ULift.up ⟨cayleyHopfMapVec x, cayleyHopfMapVec_mem x⟩

/-- Example 9.4.9 (4): the Cayley Hopf map `σ : S^15 → S^8`, given by the standard
Cayley-number formula, is a fiber bundle over `S⁸` with fiber `S⁷`. -/
theorem cayleyHopfMap_isFiberBundle :
    IsFiberBundleMap (𝕊 7) cayleyHopfMap := by
  -- Route correction: the current file has the explicit Cayley coordinate formula, but no
  -- admissible quotient-model owner. The remaining executable route is a direct `OnePoint
  -- CayleyNumber` two-chart trivialization built from the explicit finite and infinite charts.
  -- TODO: define the finite/infinite `OnePoint CayleyNumber` chart map, prove its reconstruction
  -- lemmas from `cayleyNormSq_mul_conj`, and package the resulting `S⁷`-fiber trivializations.
  sorry
