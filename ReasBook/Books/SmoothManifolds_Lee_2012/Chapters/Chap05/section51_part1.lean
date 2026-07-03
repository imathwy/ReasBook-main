import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_51 (from Chap05/Sec05_36) -/
-- The source-facing local-slice owner is `Set.SatisfiesLocalSliceConditionWithBoundary`, and the
-- canonical embedded conclusion is the smooth-embedding owner for the subtype inclusion.

open LocalNormalFormAPI Set ChartedSpace
open scoped Manifold

universe u

section

variable {n k : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Helper for Theorem 5.51: the empty subtype carries the canonical smooth
manifold-with-boundary structure, and its inclusion into the ambient manifold is a smooth
embedding. -/
theorem empty_subtype_smooth_manifold_with_boundary_structure :
    ∃ _ : SmoothManifoldWithBoundary k (∅ : Set M),
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : (∅ : Set M) → M) := by
  letI : IsEmpty (∅ : Set M) := inferInstance
  letI : ChartedSpace (ℍ^{k}) (∅ : Set M) := ChartedSpace.empty _ _
  let hTopological : IsManifold (leeBoundaryModelWithCorners k) (0 : WithTop ℕ∞) (∅ : Set M) := by
    -- The empty charted space has no chart overlaps, so the `C^0` compatibility condition is
    -- vacuous.
    refine isManifold_of_contDiffOn (I := leeBoundaryModelWithCorners k) (n := (0 : WithTop ℕ∞))
      (M := (∅ : Set M)) ?_
    intro e e' he he'
    have hFalse : False := by
      change e ∈ (∅ : Set (OpenPartialHomeomorph (∅ : Set M) (ℍ^{k}))) at he
      simp at he
    exact False.elim hFalse
  let hSmooth : IsManifold (leeBoundaryModelWithCorners k) (⊤ : WithTop ℕ∞) (∅ : Set M) := by
    -- The same empty-atlas argument gives smooth compatibility in every differentiability degree.
    refine isManifold_of_contDiffOn (I := leeBoundaryModelWithCorners k)
      (n := (⊤ : WithTop ℕ∞)) (M := (∅ : Set M)) ?_
    intro e e' he he'
    have hFalse : False := by
      change e ∈ (∅ : Set (OpenPartialHomeomorph (∅ : Set M) (ℍ^{k}))) at he
      simp at he
    exact False.elim hFalse
  let hBoundary : SmoothManifoldWithBoundary k (∅ : Set M) :=
    { toTopologicalManifoldWithBoundary :=
        { toT2Space := inferInstance
          toSecondCountableTopology := inferInstance
          toChartedSpace := inferInstance
          toIsManifold := hTopological }
      smooth := hSmooth }
  refine ⟨hBoundary, ?_⟩
  let _ : SmoothManifoldWithBoundary k (∅ : Set M) := hBoundary
  -- The empty subtype inclusion is the canonical empty smooth embedding.
  refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
  exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

/-- Helper for Theorem 5.51: the subtype patch cut out by an ambient chart source is homeomorphic
to the corresponding ambient intersection. -/
private noncomputable def subtype_patch_intersection_homeomorph
    (S T : Set M) :
    {y : S | y.1 ∈ T} ≃ₜ (S ∩ T : Set M) where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter (fun x : M ↦ x ∈ S) (fun x : M ↦ x ∈ T)
  -- The forward map forgets the nested subtype structure and records the intersection membership.
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun y ↦ by exact ⟨y.1.2, y.2⟩)
  -- The inverse repackages an intersection point as a point of `S` lying in `T`.
  continuous_invFun := by
    have hToS : Continuous fun y : (S ∩ T : Set M) ↦ (⟨y.1, y.2.1⟩ : S) :=
      Continuous.subtype_mk continuous_subtype_val (fun y ↦ y.2.1)
    exact Continuous.subtype_mk hToS (fun y ↦ y.2.2)

/-- Helper for Theorem 5.51: the canonical open patch of `S` cut out by the ambient chart
source. -/
private noncomputable def subtype_source_patch
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    TopologicalSpace.Opens S :=
  ⟨{y : S | y.1 ∈ e.source}, by
    -- The subtype patch is open because it is the preimage of the ambient chart source.
    simpa [Set.preimage, Function.comp] using e.open_source.preimage continuous_subtype_val⟩

/-- Helper for Theorem 5.51: the canonical open patch type is definitionally the raw subtype patch
cut out by the ambient chart source. -/
private noncomputable def subtype_source_patch_opens_homeomorph
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    subtype_source_patch (S := S) e ≃ₜ {y : S | y.1 ∈ e.source} := by
  -- Route correction: fix the source type first so later chart compositions can occur on the
  -- canonical `Opens S` carrier instead of repeatedly transporting between equivalent subtypes.
  change subtype_source_patch (S := S) e ≃ₜ subtype_source_patch (S := S) e
  exact Homeomorph.refl _

/-- Helper for Theorem 5.51: once an ambient chart identifies `S ∩ e.source` with a target subset
`T`, the corresponding subtype patch is homeomorphic to `T`. -/
private noncomputable def subtype_patch_target_homeomorph
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : e '' (S ∩ e.source) = T) :
    {y : S | y.1 ∈ e.source} ≃ₜ T :=
  -- First identify the subtype patch with the ambient intersection, then apply the ambient chart.
  (subtype_patch_intersection_homeomorph (S := S) (T := e.source)).trans
    (e.homeomorphOfImageSubsetSource
      (fun _ hx ↦ hx.2)
      hT)

/-- Helper for Theorem 5.51: shifting the distinguished boundary coordinate by `a` keeps all
other Euclidean coordinates fixed. -/
private def boundary_model_shift_vector (m : ℕ) (a : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 fun i ↦ if i = 0 then a else 0

/-- Helper for Theorem 5.51: the distinguished coordinate of the shift vector is exactly `a`. -/
private theorem boundary_model_shift_vector_zero (m : ℕ) (a : ℝ) :
    boundary_model_shift_vector m a 0 = a := by
  simp [boundary_model_shift_vector]

/-- Helper for Theorem 5.51: away from the distinguished boundary coordinate, the shift vector
vanishes. -/
private theorem boundary_model_shift_vector_eq_zero_of_ne_zero
    (m : ℕ) (a : ℝ) {i : Fin (m + 1)} (hi : i ≠ 0) :
    boundary_model_shift_vector m a i = 0 := by
  simp [boundary_model_shift_vector, hi]

/-- Helper for Theorem 5.51: the positive boundary-coordinate shift used to move a Euclidean chart
into the interior of Lee's half-space model. -/
private def boundary_model_shift_amount
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  |z0 0| + 1

/-- Helper for Theorem 5.51: the Euclidean source half-space on which the boundary-model interior
translation is defined. -/
private def boundary_model_source_set
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | -(boundary_model_shift_amount z0) < x 0}

/-- Helper for Theorem 5.51: the chosen center point lies in the Euclidean source half-space for
the boundary-model interior translation. -/
-- Route correction: keep the half-space source-membership arithmetic isolated while the
-- boundary-model translation package is rebuilt.
private theorem boundary_model_source_set_mem
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    z0 ∈ boundary_model_source_set z0 := by
  -- The chosen shift is strictly larger than `|z0 0|`, so the translated half-space contains `z0`.
  dsimp [boundary_model_source_set, boundary_model_shift_amount]
  have hnegabs : -|z0 0| ≤ z0 0 := by
    simpa using neg_abs_le (z0 0)
  linarith

/-- Helper for Theorem 5.51: the Euclidean source half-space is open. -/
private noncomputable def boundary_model_source_opens
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1))) :=
  ⟨boundary_model_source_set z0, by
    -- This is the strict half-space cut out by the distinguished coordinate inequality.
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (m + 1) => ℝ) 0)⟩

/-- Helper for Theorem 5.51: the positive-coordinate interior of the half-space model is open. -/
private noncomputable def boundary_model_target_opens (m : ℕ) :
    TopologicalSpace.Opens (EuclideanHalfSpace (m + 1)) :=
  ⟨{z | 0 < z.1 0}, by
    -- Inside the half-space model, the strict positivity region of the boundary coordinate is
    -- open.
    exact isOpen_lt continuous_const <|
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (m + 1) => ℝ) 0).comp
        continuous_subtype_val⟩

/-- Helper for Theorem 5.51: every point of the positive target patch is an interior point of
Lee's boundary model. -/
private theorem boundary_model_target_isInteriorPoint
    {m : ℕ} (x : boundary_model_target_opens m) :
    (𝓡∂ (m + 1)).IsInteriorPoint (x : EuclideanHalfSpace (m + 1)) := by
  -- Route correction: isolate the source-proof observation that the translated target patch lies
  -- in the positive interior of `ℍ^(m+1)` before rebuilding the full interior adapter.
  -- On the model space itself, `extChartAt` is the boundary-model chart `𝓡∂ (m + 1)`, so the
  -- interior criterion becomes exactly positivity of the distinguished coordinate.
  change
    extChartAt (𝓡∂ (m + 1)) (x : EuclideanHalfSpace (m + 1))
        (x : EuclideanHalfSpace (m + 1)) ∈
      interior (Set.range (𝓡∂ (m + 1)))
  simpa [extChartAt_self_eq, interior_range_modelWithCornersEuclideanHalfSpace (m + 1)] using
    (show 0 < x.1.1 0 from x.2)

/-- Helper for Theorem 5.51: the positive target patch is contained in the manifold interior of
Lee's boundary model. -/
private theorem boundary_model_target_subset_interior (m : ℕ) :
    ((boundary_model_target_opens m : TopologicalSpace.Opens (EuclideanHalfSpace (m + 1))) :
        Set (EuclideanHalfSpace (m + 1))) ⊆
      (𝓡∂ (m + 1)).interior (EuclideanHalfSpace (m + 1)) := by
  -- Repackage the pointwise interior statement as the subset condition needed for the boundaryless
  -- open-submanifold owner.
  intro x hx
  exact boundary_model_target_isInteriorPoint (m := m) ⟨x, hx⟩

/-- Helper for Theorem 5.51: the positive target patch of `ℍ^(m+1)` is boundaryless. -/
private instance boundary_model_target_boundaryless (m : ℕ) :
    BoundarylessManifold
      (𝓡∂ (m + 1))
      (boundary_model_target_opens m) :=
  open_subset_of_interior_boundaryless
    (I := 𝓡∂ (m + 1))
    (U := boundary_model_target_opens m)
    (boundary_model_target_subset_interior (m := m))

/-- Helper for Theorem 5.51: the same positive-coordinate patch can be viewed as an open subset of
the ambient Euclidean space, separating the target-subtype transport from the later smoothness
argument. -/
private noncomputable def boundary_model_positive_target_opens (m : ℕ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1))) :=
  ⟨{z | 0 < z 0}, by
    -- This is the strict positivity region of the distinguished coordinate in ambient Euclidean
    -- space.
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (m + 1) => ℝ) 0)⟩

/-- Helper for Theorem 5.51: forgetting the half-space proof identifies the positive interior
patch of `ℍ^(m+1)` with the corresponding Euclidean open half-space. -/
private noncomputable def boundary_model_target_to_positive_euclidean_homeomorph
    (m : ℕ) :
    boundary_model_target_opens m ≃ₜ boundary_model_positive_target_opens m where
  toFun := fun z ↦ ⟨z.1.1, z.2⟩
  invFun := fun z ↦
    ⟨⟨z.1, show 0 ≤ z.1 0 from le_of_lt (show 0 < z.1 0 from z.2)⟩, z.2⟩
  left_inv z := by
    -- Both descriptions keep the same ambient Euclidean point; only the subtype proofs change.
    apply Subtype.ext
    exact EuclideanHalfSpace.ext _ _ rfl
  right_inv z := by
    -- Repackaging a positive Euclidean point through the half-space proof is pointwise the
    -- identity.
    exact Subtype.ext rfl
  continuous_toFun := by
    -- Forget the half-space proof and retain only the ambient Euclidean point.
    simpa using
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun z : boundary_model_target_opens m ↦ z.2)
  continuous_invFun := by
    -- Reattach first the half-space proof `0 ≤ z 0`, then the target-open proof `0 < z 0`.
    have hHalf :
        Continuous fun z : boundary_model_positive_target_opens m ↦
          (⟨z.1, show 0 ≤ z.1 0 from le_of_lt (show 0 < z.1 0 from z.2)⟩ :
            EuclideanHalfSpace (m + 1)) := by
      simpa using
        ((continuous_subtype_val :
            Continuous fun z : boundary_model_positive_target_opens m ↦ z.1)).subtype_mk
          (fun z : boundary_model_positive_target_opens m ↦
            show 0 ≤ z.1 0 from le_of_lt (show 0 < z.1 0 from z.2))
    simpa using hHalf.subtype_mk (fun z : boundary_model_positive_target_opens m ↦ z.2)

/-- Helper for Theorem 5.51: the positive Euclidean target patch lies in the range of the
boundary-model-with-corners map. -/
private theorem boundary_model_positive_target_subset_model_range
    (m : ℕ) :
    ((boundary_model_positive_target_opens m :
        TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) ⊆
      Set.range (𝓡∂ (m + 1)) := by
  -- A point with strictly positive distinguished coordinate is in particular a half-space point,
  -- so it is literally the image of that half-space point under `𝓡∂ (m + 1)`.
  intro z hz
  refine ⟨⟨z, le_of_lt hz⟩, rfl⟩

/-- Helper for Theorem 5.51: translate the Euclidean source half-space into the positive interior
of the boundary model by shifting the distinguished coordinate. -/
private theorem boundary_model_translate_forward_nonneg
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_source_opens z0) :
    0 ≤ (x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0)) 0 := by
  -- The translated distinguished coordinate is strictly positive, hence in particular nonnegative.
  change 0 ≤ x.1 0 + boundary_model_shift_amount z0
  have hx0 : -(boundary_model_shift_amount z0) < x.1 0 := by
    exact x.2
  have hpos : 0 < x.1 0 + boundary_model_shift_amount z0 := by
    linarith
  exact le_of_lt hpos

/-- Helper for Theorem 5.51: the translated Euclidean source point lies in the positive interior
of the half-space model. -/
private theorem boundary_model_translate_forward_mem_target
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_source_opens z0) :
    (⟨x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0),
      boundary_model_translate_forward_nonneg z0 x⟩ :
        EuclideanHalfSpace (m + 1)) ∈ boundary_model_target_opens m := by
  -- The translation adds a positive amount to coordinate `0`, so the image lands in the target.
  change 0 <
    (⟨x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0),
      boundary_model_translate_forward_nonneg z0 x⟩ :
        EuclideanHalfSpace (m + 1)).1 0
  change 0 < x.1 0 + boundary_model_shift_amount z0
  have hx0 : -(boundary_model_shift_amount z0) < x.1 0 := by
    exact x.2
  linarith

-- Route correction: this affine map should be rebuilt together with the half-space adapter API,
-- rather than through brittle coordinate rewrites in the main file.
private def boundary_model_translate_forward
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_source_opens z0) :
    boundary_model_target_opens m :=
  ⟨⟨x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0),
      boundary_model_translate_forward_nonneg z0 x⟩,
    boundary_model_translate_forward_mem_target z0 x⟩

/-- Helper for Theorem 5.51: subtracting the same shift moves the positive interior of the
boundary model back to the Euclidean source half-space. -/
private theorem boundary_model_translate_inverse_mem_source
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_target_opens m) :
    x.1.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0) ∈
      boundary_model_source_opens z0 := by
  -- Positive distinguished coordinate in the half-space model translates back into the source
  -- half-space inequality.
  change -(boundary_model_shift_amount z0) <
    (x.1.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0)) 0
  change -(boundary_model_shift_amount z0) <
    x.1.1 0 - boundary_model_shift_amount z0
  have hx0 : 0 < x.1.1 0 := by
    exact x.2
  linarith

-- Route correction: keep the inverse affine map synchronized with the forward translation helper.
private def boundary_model_translate_inverse
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_target_opens m) :
    boundary_model_source_opens z0 :=
  ⟨x.1.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0),
    boundary_model_translate_inverse_mem_source z0 x⟩

/-- Helper for Theorem 5.51: the affine inverse cancels the forward translation on the Euclidean
source half-space. -/
private theorem boundary_model_translate_inverse_forward_val
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_source_opens z0) :
    (boundary_model_translate_inverse z0 (boundary_model_translate_forward z0 x)).1 = x.1 := by
  -- Coordinatewise, subtracting the shift after adding it returns the original Euclidean point.
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [boundary_model_translate_forward, boundary_model_translate_inverse,
      boundary_model_shift_vector]
  · simp [boundary_model_translate_forward, boundary_model_translate_inverse,
      boundary_model_shift_vector]

/-- Helper for Theorem 5.51: the affine forward map cancels the inverse translation on the
positive interior of the half-space model. -/
private theorem boundary_model_translate_forward_inverse_val
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_target_opens m) :
    (boundary_model_translate_forward z0 (boundary_model_translate_inverse z0 x)).1.1 = x.1.1 := by
  -- The same coordinatewise cancellation works on the half-space side as well.
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [boundary_model_translate_forward, boundary_model_translate_inverse,
      boundary_model_shift_vector]
  · simp [boundary_model_translate_forward, boundary_model_translate_inverse,
      boundary_model_shift_vector]

/-- Helper for Theorem 5.51: translation identifies the chosen Euclidean half-space with the
positive interior of Lee's half-space model. -/
-- Route correction: the homeomorphism should be reconstructed from the explicit forward and
-- inverse affine maps once those two helpers are stabilized.
private noncomputable def boundary_model_translation_homeomorph
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    boundary_model_source_opens z0 ≃ₜ boundary_model_target_opens m where
  toFun := boundary_model_translate_forward z0
  invFun := boundary_model_translate_inverse z0
  left_inv x := by
    -- Translating by the shift and then subtracting it recovers the original Euclidean point.
    exact Subtype.ext (boundary_model_translate_inverse_forward_val z0 x)
  right_inv x := by
    -- Subtracting the shift and then translating back recovers the original half-space point.
    apply Subtype.ext
    exact EuclideanHalfSpace.ext _ _ (boundary_model_translate_forward_inverse_val z0 x)
  continuous_toFun := by
    -- The forward translation is an affine map between the corresponding subtype domains.
    have hRaw :
        Continuous fun x : boundary_model_source_opens z0 ↦
          x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0) :=
      continuous_subtype_val.add continuous_const
    exact Continuous.subtype_mk
      (Continuous.subtype_mk hRaw (fun x ↦ boundary_model_translate_forward_nonneg z0 x))
      (fun x ↦ boundary_model_translate_forward_mem_target z0 x)
  continuous_invFun := by
    -- The inverse translation is the corresponding affine subtraction map on the half-space.
    have hRaw :
        Continuous fun x : boundary_model_target_opens m ↦
          x.1.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0) :=
      (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const
    exact Continuous.subtype_mk hRaw
      (fun x ↦ boundary_model_translate_inverse_mem_source z0 x)

/-- Helper for Theorem 5.51: the inverse of the boundary-model translation homeomorphism is
definitionally the affine subtraction map on underlying Euclidean coordinates. -/
private theorem boundary_model_translation_homeomorph_symm_apply_val
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_target_opens m) :
    (((boundary_model_translation_homeomorph z0).symm x :
        boundary_model_source_opens z0).1) =
      x.1.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0) := by
  -- The inverse homeomorphism was defined using `boundary_model_translate_inverse`, so this is
  -- exactly its underlying Euclidean formula.
  rfl

/-- Helper for Theorem 5.51: after forgetting the half-space proof on the target, the interior
translation is literally the ambient Euclidean translation on the positive-coordinate open set. -/
private noncomputable def boundary_model_translation_positive_target_homeomorph
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    boundary_model_source_opens z0 ≃ₜ boundary_model_positive_target_opens m :=
  (boundary_model_translation_homeomorph z0).trans
    (boundary_model_target_to_positive_euclidean_homeomorph m)

/-- Helper for Theorem 5.51: the Euclideanized target-side translation acts by adding the fixed
shift vector on underlying points. -/
private theorem boundary_model_translation_positive_target_homeomorph_apply
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_source_opens z0) :
    ((boundary_model_translation_positive_target_homeomorph z0 x :
        boundary_model_positive_target_opens m) : EuclideanSpace ℝ (Fin (m + 1))) =
      x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0) := by
  -- The extra Euclidean target subtype forgets only proofs, so the formula is the same affine
  -- translation as before.
  rfl

/-- Helper for Theorem 5.51: the inverse Euclideanized target-side translation acts by
subtracting the same fixed shift vector on underlying points. -/
private theorem boundary_model_translation_positive_target_homeomorph_symm_apply
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1)))
    (x : boundary_model_positive_target_opens m) :
    ((boundary_model_translation_positive_target_homeomorph z0).symm x :
        boundary_model_source_opens z0).1 =
      x.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0) := by
  -- Passing through the half-space proof-forgetting homeomorphism changes no coordinates.
  rfl

/-- Helper for Theorem 5.51: the Euclideanized translation between the chosen source half-space
and the positive target half-space is a diffeomorphism of open Euclidean patches. -/
private noncomputable def boundary_model_translation_positive_target_diffeomorph
    {m : ℕ} (z0 : EuclideanSpace ℝ (Fin (m + 1))) :
    boundary_model_source_opens z0 ≃ₘ^(((⊤ : ℕ∞) : WithTop ℕ∞))⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
      boundary_model_positive_target_opens m where
  toEquiv := (boundary_model_translation_positive_target_homeomorph z0).toEquiv
  contMDiff_toFun := by
    -- Reduce smoothness into the codomain open subtype to smoothness of the ambient translation.
    have hcomp :
        Subtype.val ∘ boundary_model_translation_positive_target_homeomorph z0 =
          fun x : boundary_model_source_opens z0 ↦
            x.1 + boundary_model_shift_vector m (boundary_model_shift_amount z0) := by
      funext x
      exact boundary_model_translation_positive_target_homeomorph_apply z0 x
    refine (ContMDiff.subtypeVal_comp_iff
      (boundary_model_positive_target_opens m)
      (boundary_model_translation_positive_target_homeomorph z0)).mp ?_
    rw [hcomp]
    simpa using
      ((contMDiff_subtype_val :
          ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) (⊤ : WithTop ℕ∞)
            (Subtype.val : boundary_model_source_opens z0 →
              EuclideanSpace ℝ (Fin (m + 1)))).add contMDiff_const).of_le (by simp)
  contMDiff_invFun := by
    -- The inverse is the ambient translation by the opposite shift, restricted to the source open
    -- half-space.
    have hcomp :
        Subtype.val ∘ (boundary_model_translation_positive_target_homeomorph z0).symm =
          fun x : boundary_model_positive_target_opens m ↦
            x.1 - boundary_model_shift_vector m (boundary_model_shift_amount z0) := by
      funext x
      exact boundary_model_translation_positive_target_homeomorph_symm_apply z0 x
    refine (ContMDiff.subtypeVal_comp_iff
      (boundary_model_source_opens z0)
      ((boundary_model_translation_positive_target_homeomorph z0).symm)).mp ?_
    rw [hcomp]
    simpa using
      ((contMDiff_subtype_val :
          ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) (⊤ : WithTop ℕ∞)
            (Subtype.val : boundary_model_positive_target_opens m →
              EuclideanSpace ℝ (Fin (m + 1)))).sub contMDiff_const).of_le (by simp)

/-- Helper for Theorem 5.51: the inverse of the canonical open-subtype inclusion preserves the
underlying point and only restores the proof of membership in the open set. -/
private theorem opens_subtype_inclusion_symm_eq_mk
    {X : Type*} [TopologicalSpace X]
    (s : TopologicalSpace.Opens X) (hs : Nonempty s) {x : X} (hx : x ∈ (s : Set X)) :
    ((s.openPartialHomeomorphSubtypeCoe hs).symm x : s) = ⟨x, hx⟩ := by
  -- The open-subtype inclusion is the identity on points, so its inverse only repackages the
  -- membership proof.
  apply Subtype.ext
  have hxTarget : x ∈ (s.openPartialHomeomorphSubtypeCoe hs).target := by
    simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hx
  simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
    (s.openPartialHomeomorphSubtypeCoe hs).right_inv hxTarget

/-- Helper for Theorem 5.51: Euclidean `k`-space admits a local chart valued in Lee's boundary
model `ℍ^k`, and in positive dimensions this chart lands in the interior of the half-space. -/
private noncomputable def euclidean_space_to_boundary_model_chart_at
    (z0 : EuclideanSpace ℝ (Fin k)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (ℍ^{k}) := by
  cases k with
  | zero =>
      -- In dimension `0`, Lee's boundary model is already Euclidean space.
      simpa [leeBoundaryModelWithCorners] using
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 0)))
  | succ k =>
      let sourceOpen := boundary_model_source_opens z0
      let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
      let targetOpen := boundary_model_target_opens k
      let targetNonempty : Nonempty targetOpen := by
        exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
      -- Route correction: follow the source proof literally by shrinking to an open Euclidean
      -- half-space around `z0`, translating it into the interior of `ℍ^{k+1}`, and then forgetting
      -- the target-open proof.
      exact
        (((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm).trans
          ((boundary_model_translation_homeomorph z0).toOpenPartialHomeomorph.trans
            (targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)))

/-- Helper for Theorem 5.51: the Euclidean-to-boundary-model chart is defined at its chosen
center point. -/
private theorem euclidean_space_to_boundary_model_chart_at_mem_source
    (z0 : EuclideanSpace ℝ (Fin k)) :
    z0 ∈ (euclidean_space_to_boundary_model_chart_at (k := k) z0).source := by
  cases k with
  | zero =>
      -- In dimension `0`, the chart is the identity chart on all of `ℝ^0`.
      simp [euclidean_space_to_boundary_model_chart_at]
  | succ k =>
      let sourceOpen := boundary_model_source_opens z0
      let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
      let targetOpen := boundary_model_target_opens k
      let targetNonempty : Nonempty targetOpen := by
        exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
      -- The outer source condition is the Euclidean source half-space, while the inner composed
      -- chart has source `univ` because both of its factors are total on their subtype domains.
      change z0 ∈
        (((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm).trans
          ((boundary_model_translation_homeomorph z0).toOpenPartialHomeomorph.trans
            (targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty))).source
      rw [OpenPartialHomeomorph.trans_source]
      constructor
      · simpa [sourceOpen, boundary_model_source_opens] using hz0
      · rw [OpenPartialHomeomorph.trans_source]
        simp

/-- Helper for Theorem 5.51: in positive dimension, the target of the Euclidean-to-boundary-model
chart at `0` is exactly the positive boundary-model target patch. -/
private theorem euclidean_space_to_boundary_model_chart_at_target_mem_boundary_model_target
    {m : ℕ} {z : EuclideanHalfSpace (m + 1)}
    (hz : z ∈ (euclidean_space_to_boundary_model_chart_at
      (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).target) :
    z ∈ boundary_model_target_opens m := by
  let z0 : EuclideanSpace ℝ (Fin (m + 1)) := 0
  let sourceOpen := boundary_model_source_opens z0
  let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
  let targetOpen := boundary_model_target_opens m
  let targetNonempty : Nonempty targetOpen := by
    exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
  -- Unfold the packaged chart target once: after the translation homeomorphism, only the final
  -- target-open inclusion contributes the positivity proof.
  simpa [euclidean_space_to_boundary_model_chart_at, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, sourceOpen, targetOpen, targetNonempty, z0, hz0]
    using hz

/-- Helper for Theorem 5.51: in positive dimension, the inverse of the Euclidean-to-boundary-model
chart at `0` is the explicit translated source point. -/
private theorem euclidean_space_to_boundary_model_chart_at_symm_eq_translate_inverse
    {m : ℕ} {z : EuclideanHalfSpace (m + 1)}
    (hz : z ∈ (euclidean_space_to_boundary_model_chart_at
      (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).target) :
    (euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm z =
      ((boundary_model_translate_inverse
          (m := m) (0 : EuclideanSpace ℝ (Fin (m + 1)))
          ⟨z, euclidean_space_to_boundary_model_chart_at_target_mem_boundary_model_target hz⟩ :
            boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))).1) := by
  let z0 : EuclideanSpace ℝ (Fin (m + 1)) := 0
  let sourceOpen := boundary_model_source_opens z0
  let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
  let targetOpen := boundary_model_target_opens m
  let targetNonempty : Nonempty targetOpen := by
    exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
  let zTarget : targetOpen :=
    ⟨z, euclidean_space_to_boundary_model_chart_at_target_mem_boundary_model_target hz⟩
  let xSource : sourceOpen := boundary_model_translate_inverse z0 zTarget
  have hxSource :
      (xSource : EuclideanSpace ℝ (Fin (m + 1))) ∈
        (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).source := by
    -- The packaged chart source is the chosen Euclidean source half-space.
    simpa [euclidean_space_to_boundary_model_chart_at, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, sourceOpen, targetOpen, targetNonempty, z0, hz0]
      using xSource.2
  have hxImage :
      (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0) xSource.1 = z := by
    -- Normalize the composed chart map: the source inclusion inverse restores `xSource`, the
    -- translation homeomorphism cancels its own inverse, and the target inclusion forgets only
    -- the positivity proof.
    change
      ((targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)
        ((boundary_model_translation_homeomorph z0)
          ((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm xSource.1))) = z
    have hxRestore :
        ((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm xSource.1 :
          sourceOpen) = xSource := by
      exact
        opens_subtype_inclusion_symm_eq_mk
          sourceOpen
          ⟨⟨z0, hz0⟩⟩
          xSource.2
    rw [hxRestore]
    have htranslate :
        boundary_model_translation_homeomorph z0 xSource = zTarget := by
      -- The translation homeomorphism is inverse to `boundary_model_translate_inverse`.
      exact (boundary_model_translation_homeomorph z0).right_inv zTarget
    rw [htranslate]
    rfl
  -- Apply the partial-homeomorphism left-inverse to the explicit source point and rewrite the
  -- forward image with the normalized formula above.
  have hsymm :
      (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).symm z = xSource.1 := by
    simpa [hxImage] using
      (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).left_inv hxSource
  simpa [xSource] using hsymm

/-- Helper for Theorem 5.51: after removing subtype proofs, the inverse of the Euclidean-to-
boundary-model chart at `0` is the explicit affine subtraction map. -/
private theorem euclidean_space_to_boundary_model_chart_at_symm_val
    {m : ℕ} {z : EuclideanHalfSpace (m + 1)}
    (hz : z ∈ (euclidean_space_to_boundary_model_chart_at
      (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).target) :
    (euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm z =
      z.1 - boundary_model_shift_vector m
        (boundary_model_shift_amount (0 : EuclideanSpace ℝ (Fin (m + 1)))) := by
  -- First rewrite the inverse chart as the explicit translated source point, then drop the final
  -- source-open proof using the translation-homeomorphism formula.
  have hsymm :
      (euclidean_space_to_boundary_model_chart_at
          (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm z =
        ((boundary_model_translate_inverse
            (m := m) (0 : EuclideanSpace ℝ (Fin (m + 1)))
            ⟨z, euclidean_space_to_boundary_model_chart_at_target_mem_boundary_model_target hz⟩ :
              boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))).1) := by
    exact euclidean_space_to_boundary_model_chart_at_symm_eq_translate_inverse hz
  simpa [boundary_model_translation_homeomorph_symm_apply_val] using hsymm

/-- Helper for Theorem 5.51: on the normalized source half-space, the chart-at-`0` map is exactly
the explicit translation into the positive boundary-model patch. -/
private theorem euclidean_space_to_boundary_model_chart_at_apply_eq_translation
    {m : ℕ}
    (z : boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))) :
    ((euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1))) z : ℍ^{(m + 1)})) =
      (((boundary_model_translation_homeomorph
          (0 : EuclideanSpace ℝ (Fin (m + 1))) z :
            boundary_model_target_opens m) : ℍ^{(m + 1)})) := by
  let z0 : EuclideanSpace ℝ (Fin (m + 1)) := 0
  let sourceOpen := boundary_model_source_opens z0
  let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
  let targetOpen := boundary_model_target_opens m
  let targetNonempty : Nonempty targetOpen := by
    exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
  -- Unfold the packaged chart once: the source-open inverse restores `z`, and the target-open
  -- inclusion forgets only the positivity proof.
  change
    ((targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)
      ((boundary_model_translation_homeomorph z0)
        ((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm z.1))) =
      (((boundary_model_translation_homeomorph z0 z : targetOpen) : ℍ^{(m + 1)}))
  have hzRestore :
      ((sourceOpen.openPartialHomeomorphSubtypeCoe ⟨⟨z0, hz0⟩⟩).symm z.1 :
          sourceOpen) = z := by
    exact opens_subtype_inclusion_symm_eq_mk sourceOpen ⟨⟨z0, hz0⟩⟩ z.2
  rw [hzRestore]
  rfl

/-- Helper for Theorem 5.51: every point of the positive boundary-model patch lies in the target
of the chart-at-`0` normalization. -/
private theorem boundary_model_target_mem_euclidean_space_to_boundary_model_chart_at_target
    {m : ℕ} (y : boundary_model_target_opens m) :
    ((y : boundary_model_target_opens m) : ℍ^{(m + 1)}) ∈
      (euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).target := by
  let z0 : EuclideanSpace ℝ (Fin (m + 1)) := 0
  let sourceOpen := boundary_model_source_opens z0
  let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
  let targetOpen := boundary_model_target_opens m
  let targetNonempty : Nonempty targetOpen := by
    exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
  -- After the source-open inclusion and the translation homeomorphism, the final target is
  -- literally the positive patch `targetOpen`.
  simpa [euclidean_space_to_boundary_model_chart_at, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, sourceOpen, targetOpen, targetNonempty, z0, hz0]
    using y.2

/-- Helper for Theorem 5.51: if a point lies in the target of the normalized chart-at-`0`, then
its inverse image lies in the distinguished Euclidean source half-space. -/
private theorem euclidean_space_to_boundary_model_chart_at_symm_mem_source_open
    {m : ℕ} {y : ℍ^{(m + 1)}}
    (hy : y ∈ (euclidean_space_to_boundary_model_chart_at
      (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).target) :
    (euclidean_space_to_boundary_model_chart_at
      (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm y ∈
      boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))) := by
  let z0 : EuclideanSpace ℝ (Fin (m + 1)) := 0
  let sourceOpen := boundary_model_source_opens z0
  let hz0 : z0 ∈ sourceOpen := boundary_model_source_set_mem z0
  let targetOpen := boundary_model_target_opens m
  let targetNonempty : Nonempty targetOpen := by
    exact ⟨boundary_model_translate_forward z0 ⟨z0, hz0⟩⟩
  have hySource :
      (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).symm y ∈
        (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).source := by
    exact (euclidean_space_to_boundary_model_chart_at (k := m + 1) z0).map_target hy
  -- Unfold the chart source once: the only nontrivial source condition is membership in the
  -- chosen Euclidean half-space `sourceOpen`.
  simpa [euclidean_space_to_boundary_model_chart_at, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, sourceOpen, targetOpen, targetNonempty, z0, hz0]
    using hySource

/-- Helper for Theorem 5.51: Euclideanizing the distinguished boundary-model chart at an interior
point of `S` gives a local chart valued in `ℝ^k`. -/
private noncomputable def interior_euclidean_chart_at
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (x : S) :
    OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
  -- Route correction: follow the source proof by first choosing the boundary-model chart at `x`
  -- and then postcomposing with the fixed interior chart from `ℍ^k` to `ℝ^k`.
  (chartAt (ℍ^{k}) x).trans
    (euclidean_space_to_boundary_model_chart_at
      (k := k) (0 : EuclideanSpace ℝ (Fin k))).symm

/-- Helper for Theorem 5.51: the Euclideanized interior chart is defined at an interior point. -/
private theorem interior_euclidean_chart_at_mem_source
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (x : S)
    (hxInt : (leeBoundaryModelWithCorners k).IsInteriorPoint x) :
    x ∈ (interior_euclidean_chart_at (k := k) S x).source := by
  cases k with
  | zero =>
      -- In dimension `0`, the auxiliary Euclidean-to-boundary chart is the identity, so the
      -- source condition reduces to the usual centered chart source membership.
      simpa [interior_euclidean_chart_at, euclidean_space_to_boundary_model_chart_at] using
        (mem_chart_source (ℍ^{0}) x)
  | succ k =>
      let targetOpen := boundary_model_target_opens k
      let targetNonempty : Nonempty targetOpen := by
        refine ⟨?_⟩
        let z0 : EuclideanSpace ℝ (Fin (k + 1)) := 0
        let hz0 : z0 ∈ boundary_model_source_opens z0 := boundary_model_source_set_mem z0
        exact boundary_model_translate_forward z0 ⟨z0, hz0⟩
      -- Unfold the trans-source condition for the Euclideanized chart. The first component is the
      -- centered boundary chart source, and the second is exactly the positive-coordinate target
      -- proved above.
      change x ∈
        ((chartAt (ℍ^{(k + 1)}) x).trans
          ((euclidean_space_to_boundary_model_chart_at
            (k := k + 1) (0 : EuclideanSpace ℝ (Fin (k + 1)))).symm)).source
      rw [OpenPartialHomeomorph.trans_source]
      constructor
      · exact mem_chart_source (ℍ^{(k + 1)}) x
      · change chartAt (ℍ^{(k + 1)}) x x ∈
          ((euclidean_space_to_boundary_model_chart_at
            (k := k + 1) (0 : EuclideanSpace ℝ (Fin (k + 1)))).symm).source
        have hxPos : 0 < extChartAt (𝓡∂ (k + 1)) x x 0 := by
          have hxInt' : (𝓡∂ (k + 1)).IsInteriorPoint x := by
            simpa [leeBoundaryModelWithCorners] using hxInt
          -- Rewrite the interior-point hypothesis in the canonical boundary-model chart at `x`.
          rw [(𝓡∂ (k + 1)).isInteriorPoint_iff] at hxInt'
          -- In Lee's positive-dimensional model, interior points are exactly the points with
          -- positive distinguished boundary coordinate.
          have hxIntCoord :
              0 < extChartAt (𝓡∂ (k + 1)) x x 0 ∧
                extChartAt (𝓡∂ (k + 1)) x x ∈
                  interior (((𝓡∂ (k + 1)).symm) ⁻¹' (chartAt (ℍ^{(k + 1)}) x).target) := by
            simpa [extChartAt, mem_chart_source,
              interior_range_modelWithCornersEuclideanHalfSpace (k + 1)] using hxInt'
          exact hxIntCoord.1
        simpa [euclidean_space_to_boundary_model_chart_at, targetOpen, targetNonempty] using
          hxPos

/-- Helper for Theorem 5.51: Euclideanizing the interior chart at `x` cuts out a literal ambient
patch `S ∩ W` together with a pointwise-identical parametrization by the chart target. -/
private theorem interior_chart_patch_homeomorph
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (x : S)
    (hxInt : (leeBoundaryModelWithCorners k).IsInteriorPoint x) :
    ∃ W : Set M, IsOpen W ∧ x.1 ∈ W ∧
      let χ := interior_euclidean_chart_at (k := k) S x
      let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) := ⟨χ.target, χ.open_target⟩
      χ.source = {y : S | y.1 ∈ W} ∧
      ∃ Φ : V ≃ₜ (((S : Set M) ∩ W : Set M)),
        ∀ z : V, ((Φ z : ((S : Set M) ∩ W : Set M)) : M) = ((χ.symm z : S) : M) := by
  let χ := interior_euclidean_chart_at (k := k) S x
  have hxχ : x ∈ χ.source :=
    interior_euclidean_chart_at_mem_source (k := k) S x hxInt
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp χ.open_source with ⟨W, hW_open, hW_eq'⟩
  let hW_eq : χ.source = {y : S | y.1 ∈ W} := hW_eq'.symm
  have hxW : x.1 ∈ W := by
    simpa [hW_eq] using hxχ
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) := ⟨χ.target, χ.open_target⟩
  let Φ : V ≃ₜ (((S : Set M) ∩ W : Set M)) :=
    (χ.toHomeomorphSourceTarget.symm.trans
      (Homeomorph.setCongr hW_eq)).trans
      (subtype_patch_intersection_homeomorph (S := S) (T := W))
  refine ⟨W, hW_open, hxW, ?_⟩
  dsimp [χ, V]
  refine ⟨hW_eq, Φ, ?_⟩
  intro z
  rfl

/-- Helper for Theorem 5.51: an ambient slice chart first induces a patch chart valued in
`ℍ^k` before it is extended back to the whole subtype. -/
private noncomputable def interior_slice_chart_induces_patch_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph (subtype_source_patch (S := S) e) (ℍ^{k}) := by
  classical
  let hk : k ≤ n := Classical.choose he.2
  have hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c := by
    simpa [hk] using (Classical.choose_spec he.2)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xSlice : Set.euclideanSlice e.target k hk c :=
    subtype_patch_target_homeomorph (S := S) (e := e) hSlice xPatch
  -- Route correction: mirror the patch-level construction from Theorem 5.8 first, then apply the
  -- explicit Euclidean-to-`ℍ^k` interior adapter at the projected distinguished point.
  change OpenPartialHomeomorph {y : S | y.1 ∈ e.source} (ℍ^{k})
  exact
    (OpenPartialHomeomorph.trans'
      ((subtype_patch_target_homeomorph (S := S) (e := e) hSlice).toOpenPartialHomeomorph)
      (euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c xSlice)
      rfl).trans
      (euclidean_space_to_boundary_model_chart_at
        (k := k) (euclidean_slice_projection hk xSlice.1))

/-- Helper for Theorem 5.51: the interior patch chart is defined at the distinguished patch point
used to build it. -/
-- Route correction: the remaining source computation should be reproved from the explicit patch
-- chart expression after the transport chain is normalized.
private theorem interior_slice_chart_induces_patch_chart_mem_source
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    (⟨x, hx⟩ : subtype_source_patch (S := S) e) ∈
      (interior_slice_chart_induces_patch_chart (S := S) (e := e) he x hx).source := by
  classical
  let hk : k ≤ n := Classical.choose he.2
  have hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c := by
    simpa [hk] using (Classical.choose_spec he.2)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xSlice : Set.euclideanSlice e.target k hk c :=
    subtype_patch_target_homeomorph (S := S) (e := e) hSlice xPatch
  -- The patch-to-slice comparison is total, so only the final boundary-model interior chart
  -- contributes a source condition at the distinguished patch point.
  change xPatch ∈
    ((OpenPartialHomeomorph.trans'
        ((subtype_patch_target_homeomorph (S := S) (e := e) hSlice).toOpenPartialHomeomorph)
        (euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c xSlice)
        rfl).trans
      (euclidean_space_to_boundary_model_chart_at
        (k := k) (euclidean_slice_projection hk xSlice.1))).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · exact mem_univ xPatch
  · simpa [xSlice, euclidean_slice_projection_partial_homeomorph_apply] using
      euclidean_space_to_boundary_model_chart_at_mem_source
        (k := k) (euclidean_slice_projection hk xSlice.1)

/-- Helper for Theorem 5.51: an ambient slice chart induces a pointed subtype chart valued in
`ℍ^k` by projecting to the free Euclidean coordinates and then using the interior boundary-model
chart. -/
private noncomputable def interior_slice_chart_induces_pointed_subtype_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph S (ℍ^{k}) := by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- Route correction: once the interior patch chart is explicit, extending it back to `S` is the
  -- same clean open-patch composition as in the boundaryless slice proof.
  exact ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (interior_slice_chart_induces_patch_chart (S := S) (e := e) he x hx)

/-- Helper for Theorem 5.51: the pointed subtype chart induced from an ambient slice chart is
defined at the point it was built around. -/
-- Route correction: once the patch-level source lemma is repaired, this pointed-source statement
-- should follow by the same open-patch source calculation used in the boundary branch.
private theorem interior_slice_chart_induces_pointed_subtype_chart_mem_source
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    x ∈ (interior_slice_chart_induces_pointed_subtype_chart (S := S) (e := e) he x hx).source :=
  by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- The pointed chart source is the intersection of the open-patch inclusion source and the
  -- interior patch-chart source; both contain the distinguished point by construction.
  change x ∈
    (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
      (interior_slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · simpa [P] using hx
  · have hxTarget : x ∈ (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).target := by
      simpa [P] using hx
    have hxPatch :
        (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm x) :
          {y : S | y.1 ∈ e.source}) = ⟨x, hx⟩ := by
      -- The inverse of the open-subtype inclusion just restores the proof that `x ∈ P`.
      apply Subtype.ext
      simpa [P, xP, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).right_inv hxTarget
    simpa [Set.preimage, hxPatch] using
      interior_slice_chart_induces_patch_chart_mem_source (S := S) (e := e) he x hx

/-- Helper for Theorem 5.51: an ambient boundary-slice chart induces a chart on the canonical
subtype patch by first identifying the patch with the Euclidean half-slice image and then using
the theorem-local half-slice chart. -/
private def projected_last_coordinate (hk : 0 < k) : Fin k :=
  ⟨k - 1, Nat.pred_lt (Nat.ne_of_gt hk)⟩

/-- Helper for Theorem 5.51: the distinguished nonnegative coordinate of a Euclidean half-slice,
viewed in ambient `ℝ^n`. -/
private def euclidean_half_slice_ambient_last_coordinate (hk : 0 < k) (hkn : k ≤ n) : Fin n :=
  ⟨k - 1, lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hk)) hkn⟩

/-- Helper for Theorem 5.51: projecting to the first `k` coordinates carries the last free
half-slice coordinate to the last coordinate of `ℝ^k`. -/
private theorem euclidean_slice_projection_last_coordinate
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    euclidean_slice_projection hkn x (projected_last_coordinate hk) =
      x (euclidean_half_slice_ambient_last_coordinate hk hkn) := by
  -- Both sides are the same ambient coordinate after unfolding the projection index cast.
  rfl

/-- Helper for Theorem 5.51: swap the last coordinate of `ℝ^k` into slot `0`, matching mathlib's
half-space convention. -/
private def half_slice_boundary_coordinate_swap [NeZero k] (hk : 0 < k) : Fin k ≃ Fin k :=
  Equiv.swap 0 (projected_last_coordinate hk)

/-- Helper for Theorem 5.51: Lee's “last coordinate nonnegative” convention is homeomorphic to the
standard Euclidean half-space by swapping coordinates `0` and `k - 1`. -/
private noncomputable def half_slice_last_coordinate_homeomorph
    [NeZero k]
    (hk : 0 < k) :
    {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)} ≃ₜ
      EuclideanHalfSpace k := by
  let e : EuclideanSpace ℝ (Fin k) ≃ₜ EuclideanSpace ℝ (Fin k) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (half_slice_boundary_coordinate_swap hk)).toHomeomorph
  -- Route correction: isolate the coordinate permutation once, then lift it to the source and
  -- target subtypes instead of repeating transport-heavy coordinate rewrites downstream.
  exact e.subtype fun u ↦ by
    -- Swapping coordinates moves the last free coordinate into slot `0`.
    simpa [e, half_slice_boundary_coordinate_swap, projected_last_coordinate]

/-- Helper for Theorem 5.51: projecting a Euclidean half-slice to its free coordinates and then
moving the constrained last coordinate into slot `0` identifies it with a subtype of `ℍ^k`. -/
private noncomputable def euclidean_half_slice_projection_homeomorph
    [NeZero k]
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ) :
    Set.euclideanHalfSlice U k hk hkn c ≃ₜ
      {z : EuclideanHalfSpace k |
        euclidean_slice_inclusion hkn c
          ((half_slice_last_coordinate_homeomorph (k := k) hk).symm z).1 ∈ U} := by
  let sourceAsSlice :
      Set.euclideanHalfSlice U k hk hkn c ≃ₜ
        {x : Set.euclideanSlice U k hkn c |
          0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn)} := by
    -- The Euclidean half-slice is exactly the corresponding slice together with the nonnegativity
    -- condition on the distinguished last free coordinate.
    simpa [Set.euclideanHalfSlice, euclidean_half_slice_ambient_last_coordinate] using
      (subtype_patch_intersection_homeomorph
        (S := Set.euclideanSlice U k hkn c)
        (T := {y : EuclideanSpace ℝ (Fin n) |
          0 ≤ y (euclidean_half_slice_ambient_last_coordinate hk hkn)})).symm
  let projectedAsNested :
      {x : Set.euclideanSlice U k hkn c |
          0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn)} ≃ₜ
        {u : {u : EuclideanSpace ℝ (Fin k) |
            euclidean_slice_inclusion hkn c u ∈ U} |
          0 ≤ u.1 (projected_last_coordinate hk)} :=
    (euclidean_slice_projection_homeomorph U hkn c).subtype fun x ↦ by
      -- After projection, the last free ambient coordinate becomes the last coordinate of `ℝ^k`.
      change
        0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn) ↔
          0 ≤ (euclidean_slice_projection hkn x.1) (projected_last_coordinate hk)
      rw [euclidean_slice_projection_last_coordinate (hk := hk) (hkn := hkn) x.1]
  let reorderTarget :
      {u : {u : EuclideanSpace ℝ (Fin k) |
            euclidean_slice_inclusion hkn c u ∈ U} |
          0 ≤ u.1 (projected_last_coordinate hk)} ≃ₜ
        {u : {u : EuclideanSpace ℝ (Fin k) |
            0 ≤ u (projected_last_coordinate hk)} |
          euclidean_slice_inclusion hkn c u.1 ∈ U} := by
    let leftFlatten :
        {u : {u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} |
            0 ≤ u.1 (projected_last_coordinate hk)} ≃ₜ
          ({u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} ∩
            {u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} : Set (EuclideanSpace ℝ (Fin k))) :=
      subtype_patch_intersection_homeomorph
        (S := {u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hkn c u ∈ U})
        (T := {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)})
    let rightFlatten :
        {u : {u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} |
            euclidean_slice_inclusion hkn c u.1 ∈ U} ≃ₜ
          ({u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} ∩
            {u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} : Set (EuclideanSpace ℝ (Fin k))) :=
      subtype_patch_intersection_homeomorph
        (S := {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)})
        (T := {u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hkn c u ∈ U})
    -- The two nested target descriptions only differ by the order of the conjunction.
    exact leftFlatten.trans <|
      (Homeomorph.setCongr <| by
        ext u
        constructor <;> intro hu
        · exact ⟨hu.2, hu.1⟩
        · exact ⟨hu.2, hu.1⟩).trans rightFlatten.symm
  let halfSpaceAsNested :
      {u : {u : EuclideanSpace ℝ (Fin k) |
            0 ≤ u (projected_last_coordinate hk)} |
          euclidean_slice_inclusion hkn c u.1 ∈ U} ≃ₜ
        {z : EuclideanHalfSpace k |
          euclidean_slice_inclusion hkn c
            ((half_slice_last_coordinate_homeomorph (k := k) hk).symm z).1 ∈ U} :=
    (half_slice_last_coordinate_homeomorph (k := k) hk).subtype fun u ↦ by
      -- The target condition is phrased by pulling back along the explicit permutation
      -- homeomorphism, so it is tautologically preserved.
      have hu :
          ((half_slice_last_coordinate_homeomorph (k := k) hk).symm
            ((half_slice_last_coordinate_homeomorph (k := k) hk) u)) = u :=
        (half_slice_last_coordinate_homeomorph (k := k) hk).left_inv u
      change
        euclidean_slice_inclusion hkn c u.1 ∈ U ↔
          euclidean_slice_inclusion hkn c
            (((half_slice_last_coordinate_homeomorph (k := k) hk).symm
              ((half_slice_last_coordinate_homeomorph (k := k) hk) u)).1) ∈ U
      exact hu.symm ▸ Iff.rfl
  -- The full half-slice chart is the composition of the source identification, slice projection,
  -- target reordering, and the final coordinate permutation into `ℍ^k`.
  exact sourceAsSlice.trans <| projectedAsNested.trans <| reorderTarget.trans halfSpaceAsNested

/-- Helper for Theorem 5.51: the target subset of `ℍ^k` cut out by the projected half-slice chart
is open. -/
private noncomputable def euclidean_half_slice_projection_partial_homeomorph
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ)
    (x : Set.euclideanHalfSlice U k hk hkn c) :
    OpenPartialHomeomorph (Set.euclideanHalfSlice U k hk hkn c) (ℍ^{k}) := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k =>
      let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 1)) :=
        ⟨{z : EuclideanHalfSpace (k + 1) |
            euclidean_slice_inclusion hkn c
              ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1 ∈ U}, by
          -- The projected target is an open subset of `ℍ^(k+1)` because it is the preimage of the
          -- ambient open set `U` under the explicit half-slice inclusion map.
          have hcoord :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1 :=
            continuous_subtype_val.comp
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm.continuous
          have hmap :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                euclidean_slice_inclusion hkn c
                  (((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1) :=
            (euclidean_slice_inclusion_continuous hkn c).comp hcoord
          simpa [Set.preimage, Function.comp] using hU.preimage hmap⟩
      let xProjected :
          {u : EuclideanSpace ℝ (Fin (k + 1)) |
            0 ≤ u (projected_last_coordinate (k := k + 1) hk)} :=
        ⟨euclidean_slice_projection hkn x.1, by
          -- The half-slice inequality becomes the last coordinate inequality after projection.
          simpa [euclidean_slice_projection_last_coordinate (k := k + 1) (hk := hk)
            (hkn := hkn) x.1] using x.2.2⟩
      let targetNonempty : Nonempty targetOpen := by
        refine ⟨⟨half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected, ?_⟩⟩
        -- The distinguished half-slice point projects to a point of the open target.
        have hxPerm :
            ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected)) = xProjected :=
          (half_slice_last_coordinate_homeomorph (k := k + 1) hk).left_inv xProjected
        have hxInU : euclidean_slice_inclusion hkn c xProjected.1 ∈ U := by
          simpa [xProjected, euclidean_slice_inclusion_projection hkn c x.2.1] using x.2.1.1
        change euclidean_slice_inclusion hkn c
          (((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected)).1) ∈ U
        exact hxPerm.symm ▸ hxInU
      -- In the positive-dimensional branch, `ℍ^(k+1)` is definitionally `EuclideanHalfSpace
      -- (k + 1)`, so no further transport is needed.
      exact
        OpenPartialHomeomorph.trans'
          ((euclidean_half_slice_projection_homeomorph
            (k := k + 1) (U := U) (hk := hk) (hkn := hkn) c).toOpenPartialHomeomorph)
          (targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)
          rfl

/-- Helper for Theorem 5.51: the distinguished center point used to build the Euclidean
half-slice chart lies in that chart's source. -/
private theorem euclidean_half_slice_projection_partial_homeomorph_center_mem_source
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ)
    (x : Set.euclideanHalfSlice U k hk hkn c) :
    x ∈ (euclidean_half_slice_projection_partial_homeomorph U hU hk hkn c x).source := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k =>
      let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 1)) :=
        ⟨{z : EuclideanHalfSpace (k + 1) |
            euclidean_slice_inclusion hkn c
              ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1 ∈ U}, by
          have hcoord :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1 :=
            continuous_subtype_val.comp
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm.continuous
          have hmap :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                euclidean_slice_inclusion hkn c
                  (((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm z).1) :=
            (euclidean_slice_inclusion_continuous hkn c).comp hcoord
          simpa [Set.preimage, Function.comp] using hU.preimage hmap⟩
      let xProjected :
          {u : EuclideanSpace ℝ (Fin (k + 1)) |
            0 ≤ u (projected_last_coordinate (k := k + 1) hk)} :=
        ⟨euclidean_slice_projection hkn x.1, by
          simpa [euclidean_slice_projection_last_coordinate (k := k + 1) (hk := hk)
            (hkn := hkn) x.1] using x.2.2⟩
      let targetNonempty : Nonempty targetOpen := by
        refine ⟨⟨half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected, ?_⟩⟩
        have hxPerm :
            ((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected)) = xProjected :=
          (half_slice_last_coordinate_homeomorph (k := k + 1) hk).left_inv xProjected
        have hxInU : euclidean_slice_inclusion hkn c xProjected.1 ∈ U := by
          simpa [xProjected, euclidean_slice_inclusion_projection hkn c x.2.1] using x.2.1.1
        change euclidean_slice_inclusion hkn c
          (((half_slice_last_coordinate_homeomorph (k := k + 1) hk).symm
              (half_slice_last_coordinate_homeomorph (k := k + 1) hk xProjected)).1) ∈ U
        exact hxPerm.symm ▸ hxInU
      -- In positive dimension the chart built in the definition is exactly this explicit
      -- `trans'` expression, whose source is all of the Euclidean half-slice.
      simpa [euclidean_half_slice_projection_partial_homeomorph, targetOpen, xProjected,
        targetNonempty]

/-- Helper for Theorem 5.51: an ambient boundary-slice chart induces a chart on the canonical
subtype patch by first identifying the patch with the Euclidean half-slice image and then using
the theorem-local half-slice chart. -/
private noncomputable def boundary_slice_chart_induces_patch_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsBoundarySliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph (subtype_source_patch (S := S) e) (ℍ^{k}) := by
  classical
  let hk : 0 < k := Classical.choose he.2
  have hhkn :
      ∃ hkn : k ≤ n, ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c := by
    simpa [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice, hk] using
      (Classical.choose_spec he.2)
  let hkn : k ≤ n := Classical.choose hhkn
  have hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c := by
    simpa [hkn] using (Classical.choose_spec hhkn)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hHalfSlice :
      e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xHalfSlice : Set.euclideanHalfSlice e.target k hk hkn c :=
    subtype_patch_target_homeomorph (S := S) (e := e) hHalfSlice xPatch
  -- Route correction: mirror Theorem 5.8 at the patch level first, so the only remaining
  -- boundary-model geometry is the isolated half-slice chart on the Euclidean target.
  change OpenPartialHomeomorph {y : S | y.1 ∈ e.source} (ℍ^{k})
  exact OpenPartialHomeomorph.trans
    ((subtype_patch_target_homeomorph (S := S) (e := e) hHalfSlice).toOpenPartialHomeomorph)
    (euclidean_half_slice_projection_partial_homeomorph e.target e.open_target hk hkn c xHalfSlice)

/-- Helper for Theorem 5.51: the half-slice patch chart is defined at the distinguished point of
the canonical subtype patch. -/
private theorem boundary_slice_chart_induces_patch_chart_mem_source
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsBoundarySliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    (⟨x, hx⟩ : subtype_source_patch (S := S) e) ∈
      (boundary_slice_chart_induces_patch_chart (S := S) (e := e) he x hx).source := by
  classical
  let hk : 0 < k := Classical.choose he.2
  have hhkn :
      ∃ hkn : k ≤ n, ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c := by
    simpa [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice, hk] using
      (Classical.choose_spec he.2)
  let hkn : k ≤ n := Classical.choose hhkn
  have hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c := by
    simpa [hkn] using (Classical.choose_spec hhkn)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hHalfSlice :
      e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target k hk hkn c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xHalfSlice : Set.euclideanHalfSlice e.target k hk hkn c :=
    subtype_patch_target_homeomorph (S := S) (e := e) hHalfSlice xPatch
  -- Route correction: reduce the patch-source computation to the single missing fact that the
  -- theorem-local half-slice chart is defined at its distinguished center point `xHalfSlice`.
  have hChart :
      boundary_slice_chart_induces_patch_chart (S := S) (e := e) he x hx =
        OpenPartialHomeomorph.trans
          ((subtype_patch_target_homeomorph (S := S) (e := e) hHalfSlice).toOpenPartialHomeomorph)
          (euclidean_half_slice_projection_partial_homeomorph
            e.target e.open_target hk hkn c xHalfSlice) := by
    -- Unfold the patch chart and keep the same witness choices used above.
    unfold boundary_slice_chart_induces_patch_chart
    simp [hk, hkn, c, hHalfSlice, xPatch, xHalfSlice]
  rw [hChart, OpenPartialHomeomorph.trans_source]
  constructor
  · -- The first factor is the whole patch because the comparison map is a genuine homeomorphism.
    exact mem_univ _
  · -- The remaining source condition is exactly the center-membership fact from the canonical
    -- theorem-local half-slice chart API.
    simpa using
      euclidean_half_slice_projection_partial_homeomorph_center_mem_source
        e.target e.open_target hk hkn c xHalfSlice

/-- Helper for Theorem 5.51: composing the boundary patch chart with the inclusion of the
canonical open patch into `S` gives the pointed subtype chart on `S` for the half-slice branch. -/
private noncomputable def boundary_slice_chart_induces_pointed_subtype_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsBoundarySliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph S (ℍ^{k}) := by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- Route correction: once the patch chart exists, the inclusion of the patch back into `S` is
  -- the same single clean composition as in the boundaryless proof.
  exact ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (boundary_slice_chart_induces_patch_chart (S := S) (e := e) he x hx)

/-- Helper for Theorem 5.51: the pointed subtype chart induced from an ambient boundary slice
chart is defined at the point it was built around. -/
-- Route correction: once the patch-level boundary source computation is stabilized, this pointed
-- version should be the routine open-patch source calculation.
private theorem boundary_slice_chart_induces_pointed_subtype_chart_mem_source
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsBoundarySliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    x ∈ (boundary_slice_chart_induces_pointed_subtype_chart (S := S) (e := e) he x hx).source :=
  by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- The boundary pointed chart has the same open-patch source calculation as the interior branch.
  change x ∈
    (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
      (boundary_slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · simpa [P] using hx
  · have hxTarget : x ∈ (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).target := by
      simpa [P] using hx
    have hxPatch :
        (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm x) :
          {y : S | y.1 ∈ e.source}) = ⟨x, hx⟩ := by
      -- The inverse of the open-subtype inclusion again only restores the patch-membership proof.
      apply Subtype.ext
      simpa [P, xP, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).right_inv hxTarget
    simpa [Set.preimage, hxPatch] using
      boundary_slice_chart_induces_patch_chart_mem_source (S := S) (e := e) he x hx

/-- Helper for Theorem 5.51: choose, for each `x : S`, the ambient chart promised by the local
slice-with-boundary condition. -/
private noncomputable def local_slice_condition_with_boundary_ambient_chart
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  Classical.choose (hS.exists_sliceChart x.1 x.2)

/-- Helper for Theorem 5.51: the chosen ambient chart for `x : S` contains `x` in its source. -/
private theorem local_slice_condition_with_boundary_ambient_chart_mem_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    x.1 ∈ (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).source :=
  (Classical.choose_spec (hS.exists_sliceChart x.1 x.2)).1

/-- Helper for Theorem 5.51: the chosen ambient chart for `x : S` is either a slice chart or a
boundary slice chart. -/
private theorem local_slice_condition_with_boundary_ambient_chart_isSlice_or_isBoundarySlice
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).IsSliceChart S k ∨
      (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).IsBoundarySliceChart S k :=
  (Classical.choose_spec (hS.exists_sliceChart x.1 x.2)).2

/-- Helper for Theorem 5.51: the ambient chart chosen from the local slice-with-boundary condition
always lies in the smooth maximal atlas. -/
private theorem local_slice_condition_with_boundary_ambient_chart_mem_maximalAtlas
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    local_slice_condition_with_boundary_ambient_chart (S := S) hS x ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
  -- Either branch of the local witness is already a smooth ambient chart.
  rcases
      local_slice_condition_with_boundary_ambient_chart_isSlice_or_isBoundarySlice
        (S := S) hS x with hSlice | hBoundary
  · exact hSlice.mem_maximalAtlas
  · exact hBoundary.mem_maximalAtlas

/-- Helper for Theorem 5.51: the forward transition between the chosen ambient charts at two
points of `S` is smooth because both charts lie in the ambient maximal atlas. -/
private theorem local_slice_condition_with_boundary_ambient_transition_mem_contDiffGroupoid
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x y : S) :
    (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).symm.trans
        (local_slice_condition_with_boundary_ambient_chart (S := S) hS y) ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
  have hx :
      local_slice_condition_with_boundary_ambient_chart (S := S) hS x ∈
        IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    local_slice_condition_with_boundary_ambient_chart_mem_maximalAtlas (S := S) hS x
  have hy :
      local_slice_condition_with_boundary_ambient_chart (S := S) hS y ∈
        IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    local_slice_condition_with_boundary_ambient_chart_mem_maximalAtlas (S := S) hS y
  -- Maximal-atlas compatibility gives the smooth forward transition directly.
  exact IsManifold.compatible_of_mem_maximalAtlas hx hy

/-- Helper for Theorem 5.51: the reverse transition between the chosen ambient charts at two
points of `S` is smooth for the same maximal-atlas reason. -/
private theorem local_slice_condition_with_boundary_ambient_transition_symm_mem_contDiffGroupoid
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x y : S) :
    (local_slice_condition_with_boundary_ambient_chart (S := S) hS y).symm.trans
        (local_slice_condition_with_boundary_ambient_chart (S := S) hS x) ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
  have hx :
      local_slice_condition_with_boundary_ambient_chart (S := S) hS x ∈
        IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    local_slice_condition_with_boundary_ambient_chart_mem_maximalAtlas (S := S) hS x
  have hy :
      local_slice_condition_with_boundary_ambient_chart (S := S) hS y ∈
        IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    local_slice_condition_with_boundary_ambient_chart_mem_maximalAtlas (S := S) hS y
  -- This is the reverse transition from the same maximal-atlas compatibility statement.
  exact IsManifold.compatible_of_mem_maximalAtlas hy hx

/-- Helper for Theorem 5.51: choose the subtype chart induced by the local slice-with-boundary
witness at `x`, using the boundary branch immediately and leaving the interior bridge isolated. -/
private noncomputable def local_slice_condition_with_boundary_chartAt
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    OpenPartialHomeomorph S (ℍ^{k}) := by
  classical
  let e := local_slice_condition_with_boundary_ambient_chart (S := S) hS x
  let hx : x.1 ∈ e.source :=
    local_slice_condition_with_boundary_ambient_chart_mem_source (S := S) hS x
  have hCases : e.IsSliceChart S k ∨ e.IsBoundarySliceChart S k := by
    simpa [e] using
      local_slice_condition_with_boundary_ambient_chart_isSlice_or_isBoundarySlice
        (S := S) hS x
  by_cases hSlice : e.IsSliceChart S k
  · -- Route correction: the remaining interior branch should compose the existing Euclidean slice
    -- patch chart with a local interior chart valued in `ℍ^k`, instead of rebuilding the whole
    -- forward atlas inside the theorem body.
    exact interior_slice_chart_induces_pointed_subtype_chart
      (S := S) e hSlice x hx
  · have hBoundary : e.IsBoundarySliceChart S k := by
      rcases hCases with hSlice' | hBoundary
      · exact False.elim (hSlice hSlice')
      · exact hBoundary
    -- The boundary branch already uses the patch-level half-slice chart built above.
    exact boundary_slice_chart_induces_pointed_subtype_chart
      (S := S) e hBoundary x hx

/-- Helper for Theorem 5.51: if the chosen ambient witness at `x` is a slice chart, then the
subtype chart `chartAt` is definitionally the interior branch built from that witness. -/
private theorem local_slice_condition_with_boundary_chartAt_eq_of_isSliceChart
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S)
    (hSlice :
      (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).IsSliceChart S k) :
    local_slice_condition_with_boundary_chartAt (S := S) hS x =
      interior_slice_chart_induces_pointed_subtype_chart
        (S := S)
        (local_slice_condition_with_boundary_ambient_chart (S := S) hS x)
        hSlice
        x
        (local_slice_condition_with_boundary_ambient_chart_mem_source (S := S) hS x) := by
  -- Unfold the chart choice once: in the slice branch it returns the interior pointed chart
  -- attached to the chosen ambient witness.
  unfold local_slice_condition_with_boundary_chartAt
  simp [hSlice]

/-- Helper for Theorem 5.51: if the chosen ambient witness at `x` is not a slice chart, then the
subtype chart `chartAt` is definitionally the boundary branch built from that witness. -/
private theorem local_slice_condition_with_boundary_chartAt_eq_of_isBoundarySliceChart
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S)
    (hNotSlice :
      ¬ (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).IsSliceChart S k)
    (hBoundary :
      (local_slice_condition_with_boundary_ambient_chart (S := S) hS x).IsBoundarySliceChart S k) :
    local_slice_condition_with_boundary_chartAt (S := S) hS x =
      boundary_slice_chart_induces_pointed_subtype_chart
        (S := S)
        (local_slice_condition_with_boundary_ambient_chart (S := S) hS x)
        hBoundary
        x
        (local_slice_condition_with_boundary_ambient_chart_mem_source (S := S) hS x) := by
  -- Unfold the chart choice once: after excluding the slice branch, it returns the boundary
  -- pointed chart attached to the chosen ambient witness.
  unfold local_slice_condition_with_boundary_chartAt
  simp [hNotSlice]

/-- Helper for Theorem 5.51: the chosen subtype chart is intended to be centered at the point it
was selected for. -/
private theorem local_slice_condition_with_boundary_chartAt_mem_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) (x : S) :
    x ∈ (local_slice_condition_with_boundary_chartAt (S := S) hS x).source := by
  classical
  let e := local_slice_condition_with_boundary_ambient_chart (S := S) hS x
  let hx : x.1 ∈ e.source :=
    local_slice_condition_with_boundary_ambient_chart_mem_source (S := S) hS x
  have hCases : e.IsSliceChart S k ∨ e.IsBoundarySliceChart S k := by
    simpa [e] using
      local_slice_condition_with_boundary_ambient_chart_isSlice_or_isBoundarySlice
        (S := S) hS x
  by_cases hSlice : e.IsSliceChart S k
  · -- Reduce the source calculation to the explicit interior pointed chart in the slice branch.
    rw [local_slice_condition_with_boundary_chartAt_eq_of_isSliceChart
      (S := S) hS x (hSlice := by simpa [e] using hSlice)]
    exact interior_slice_chart_induces_pointed_subtype_chart_mem_source
      (S := S) (e := e) hSlice x hx
  · have hBoundary : e.IsBoundarySliceChart S k := by
      rcases hCases with hSlice' | hBoundary
      · exact False.elim (hSlice hSlice')
      · exact hBoundary
    -- After excluding the slice branch, the same source calculation reduces to the boundary chart.
    rw [local_slice_condition_with_boundary_chartAt_eq_of_isBoundarySliceChart
      (S := S) hS x
      (hNotSlice := by simpa [e] using hSlice)
      (hBoundary := by simpa [e] using hBoundary)]
    exact boundary_slice_chart_induces_pointed_subtype_chart_mem_source
      (S := S) (e := e) hBoundary x hx

/-- Helper for Theorem 5.51: the local slice-with-boundary condition packages the induced subtype
charts into a charted-space structure on `S`. -/
private noncomputable abbrev local_slice_condition_with_boundary_chartedSpace
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) :
    ChartedSpace (ℍ^{k}) S where
  atlas := {e | ∃ x : S, e = local_slice_condition_with_boundary_chartAt (S := S) hS x}
  chartAt := local_slice_condition_with_boundary_chartAt (S := S) hS
  mem_chart_source := local_slice_condition_with_boundary_chartAt_mem_source (S := S) hS
  chart_mem_atlas x := by
    -- The chosen chart at `x` is, by construction, one of the distinguished subtype charts.
    exact ⟨x, rfl⟩

/-- Helper for Theorem 5.51: any nonempty subset satisfying the local slice-with-boundary
condition has dimension at most that of the ambient manifold. -/
private theorem satisfies_local_slice_condition_with_boundary_dimension_le
    (S : Set M) (hS_nonempty : S.Nonempty)
    (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) :
    k ≤ n := by
  rcases hS_nonempty with ⟨x, hx⟩
  rcases hS.exists_sliceChart x hx with ⟨e, _, hChart⟩
  rcases hChart with hSlice | hBoundary
  · -- Interior slice witnesses already record the required inequality `k ≤ n`.
    rcases hSlice.2 with ⟨hk, _, _⟩
    exact hk
  · -- Boundary half-slice witnesses record both `0 < k` and the same ambient inequality.
    rcases hBoundary.2 with ⟨_, hk, _, _⟩
    exact hk

/-- Helper for Theorem 5.51: the zero-dimensional boundary model has no boundary points. -/
private theorem zero_dimensional_boundary_model_not_isBoundaryPoint
    (S : Set M) [SmoothManifoldWithBoundary 0 S] (x : S) :
    ¬ (leeBoundaryModelWithCorners 0).IsBoundaryPoint x := by
  -- In dimension `0`, Lee's boundary model is the boundaryless Euclidean owner `𝓡 0`, so every
  -- point is interior.
  have hxInt : (leeBoundaryModelWithCorners 0).IsInteriorPoint x := by
    simpa [leeBoundaryModelWithCorners] using
      (BoundarylessManifold.isInteriorPoint (I := 𝓡 0) (M := S) (x := x))
  exact ((leeBoundaryModelWithCorners 0).isInteriorPoint_iff_not_isBoundaryPoint x).1 hxInt

/-- Helper for Theorem 5.51: every `0`-dimensional topological manifold is discrete. -/
private theorem zero_dimensional_topological_manifold_discreteTopology
    {X : Type*} [TopologicalSpace X] [TopologicalManifold 0 X] :
    DiscreteTopology X := by
  infer_instance

/-- Helper for Theorem 5.51: an open subset of a subtype is cut out by an ambient open set. -/
private theorem subtype_open_eq_preimage_ambient_open
    {S : Set M} {U : Set S} (hU : IsOpen U) :
    ∃ W : Set M, IsOpen W ∧ U = {y : S | y.1 ∈ W} := by
  -- The subtype topology on `S` is induced by the ambient inclusion, so open subsets of `S`
  -- are exactly ambient-open preimages along `Subtype.val`.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hU with ⟨W, hW, hEq⟩
  exact ⟨W, hW, hEq.symm⟩

/-- Helper for Theorem 5.51: restricting the ambient subtype inclusion to an open patch preserves
the topological-embedding property. -/
private theorem open_subtype_patch_inclusion_isEmbedding
    {S : Set M} {U : TopologicalSpace.Opens S}
    (hEmb : Topology.IsEmbedding ((↑) : S → M)) :
    Topology.IsEmbedding ((↑) : U → M) := by
  -- The restricted inclusion factors through the open-subtype inclusion `U ↪ S`, followed by the
  -- ambient subtype inclusion `S ↪ M`.
  exact hEmb.comp Topology.IsEmbedding.subtypeVal

/-- Helper for Theorem 5.51: restricting a smooth subtype inclusion to an open subtype patch
preserves smooth embedding into the ambient manifold. -/
private theorem open_subtype_patch_inclusion_isSmoothEmbedding
    {S : Set M} [SmoothManifoldWithBoundary k S]
    (hEmb :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M))
    (U : TopologicalSpace.Opens S) :
    Manifold.IsSmoothEmbedding
      (leeBoundaryModelWithCorners k)
      (𝓡 n)
      (⊤ : WithTop ℕ∞)
      ((↑) : U → M) := by
  -- The restricted inclusion factors through the open inclusion `U ↪ S`, followed by the ambient
  -- subtype inclusion `S ↪ M`, so we compose the existing immersion data and keep the induced
  -- topological embedding.
  refine Manifold.IsSmoothEmbedding.mk ?_ <|
    open_subtype_patch_inclusion_isEmbedding (S := S) hEmb.2
  simpa [Function.comp] using
    Manifold.IsImmersion.ex416_comp hEmb.1 (Manifold.IsImmersion.of_opens U)

/-- Helper for Theorem 5.51: lowering the differentiability index preserves immersions by keeping
the same local chart normal forms. -/
private theorem isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) X]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
    {J : ModelWithCorners 𝕜 E' H'} [IsManifold J (⊤ : WithTop ℕ∞) Y]
    {m n : WithTop ℕ∞} {f : X → Y} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion I J n f) :
    Manifold.IsImmersion I J m f := by
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  -- Keep the same local chart presentation and only lower the maximal-atlas regularity bounds.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := X) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := Y) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 5.51: a top-order immersion can be lowered to the `↑⊤` smoothness level
used by the local normal-form API. -/
private theorem isImmersion_coe_top
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    {f : S → M}
    (hf : Manifold.IsImmersion (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) f) :
    Manifold.IsImmersion (𝓡 k) (𝓡 n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f := by
  -- This is the theorem-local specialization of the generic lowering lemma above.
  exact
    isImmersion_of_le
      (I := 𝓡 k)
      (J := 𝓡 n)
      (X := S)
      (Y := M)
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      (by simp)
      hf

/-- Helper for Theorem 5.51: a `0`-dimensional Euclidean slice is exactly the singleton cut out by
fixing all ambient coordinates. -/
-- Route correction: the zero-dimensional slice API should be restated in the canonical
-- `Set.tailCoordinate` language used by `Set.euclideanSlice`.
private theorem euclideanSlice_zero_eq_singleton
    {U : Set (EuclideanSpace ℝ (Fin n))} {c : Fin n → ℝ}
    {z0 : EuclideanSpace ℝ (Fin n)} (hz0 : z0 ∈ U) (hc : ∀ i, z0 i = c i) :
    Set.euclideanSlice U 0 (Nat.zero_le n) c = {z0} := by
  -- A `0`-slice fixes every ambient coordinate, so any point in it agrees with `z0`
  -- coordinatewise.
  ext x
  constructor
  · intro hx
    have hxcoords : ∀ i : Fin n, x i = c i := by
      intro i
      have hxi := hx.2 i
      -- In the zero-dimensional slice case, the tail-coordinate cast is the identity.
      change x (Fin.cast (Nat.add_sub_of_le (Nat.zero_le n)) (i.natAdd 0)) = c i at hxi
      simpa using hxi
    have hEq : x = z0 := by
      ext i
      calc
        x i = c i := hxcoords i
        _ = z0 i := (hc i).symm
    simpa [hEq]
  · intro hx
    rcases hx with rfl
    refine ⟨hz0, ?_⟩
    intro i
    -- The zero-dimensional tail-coordinate cast again simplifies to the identity index.
    change x (Fin.cast (Nat.add_sub_of_le (Nat.zero_le n)) (i.natAdd 0)) = c i
    simpa using hc i

/-- Helper for Theorem 5.51: once a local inclusion normal form is restricted to an ambient open
patch matching the domain-chart source, its source image is exactly the corresponding ambient
intersection patch. -/
private theorem local_normal_form_source_image_eq_restricted_patch
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S] {x : S}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt (Subtype.val : S → M) x
      (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W}) :
    Subtype.val '' hNF.domChart.source = S ∩ (hNF.codChart.restr W).source := by
  -- Normalize the restricted ambient source to `W`, and recover codomain-source membership from
  -- the local normal form instead of assuming a global inclusion `W ⊆ codChart.source`.
  apply Set.ext
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzW : z.1 ∈ W := by
      simpa [hW_eq] using hz
    have hzCod : z.1 ∈ hNF.codChart.source := by
      exact (LocalNormalFormAPI.LocalCoordinateNormalFormAt.mapsTo_source hNF) hz
    refine ⟨z.2, ?_⟩
    rw [hNF.codChart.restr_source' W hW_open]
    exact ⟨hzCod, hzW⟩
  · rintro ⟨hyS, hyRestr⟩
    rw [hNF.codChart.restr_source' W hW_open] at hyRestr
    let yS : S := ⟨y, hyS⟩
    have hyDom : yS ∈ hNF.domChart.source := by
      simpa [hW_eq] using hyRestr.2
    exact ⟨yS, hyDom, rfl⟩

/-- Helper for Theorem 5.51: in the same restricted local normal form, the distinguished center
point lies in the restricted codomain-chart source. -/
private theorem local_normal_form_center_mem_restricted_source
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S] {x : S}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt (Subtype.val : S → M) x
      (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W}) :
    x.1 ∈ (hNF.codChart.restr W).source := by
  -- The center point belongs to the domain chart source, hence to the matching ambient patch `W`,
  -- and `mapsTo_source` supplies the missing codomain-source membership after restriction.
  have hxDom : x ∈ hNF.domChart.source := hNF.domChart_centered.1
  have hxW : x.1 ∈ W := by
    simpa [hW_eq] using hxDom
  have hxCod : x.1 ∈ hNF.codChart.source := by
    exact (LocalNormalFormAPI.LocalCoordinateNormalFormAt.mapsTo_source hNF) hxDom
  -- After restricting the codomain chart to `W`, the source condition is exactly `x ∈ W`.
  rw [hNF.codChart.restr_source' W hW_open]
  exact ⟨hxCod, hxW⟩

/-- Helper for Theorem 5.51: a point of the zero-tail Euclidean slice is recovered by the
rank-`k` normal form after projecting to the first `k` coordinates. -/
private theorem rank_normal_form_self_eq_local_euclidean_slice_inclusion_zero
    (hk : k ≤ n) :
    LocalNormalFormAPI.rank_normal_form k n k =
      euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  exact rank_normal_form_self_eq_euclidean_slice_inclusion_zero hk

/-- Helper for Theorem 5.51: a point of the zero-tail Euclidean slice is recovered by the
rank-`k` normal form after projecting to the first `k` coordinates. -/
private theorem zero_slice_point_eq_rank_normal_form_projection
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hk : k ≤ n)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ Set.euclideanSlice U k hk (fun _ : Fin (n - k) ↦ (0 : ℝ))) :
    LocalNormalFormAPI.rank_normal_form k n k (euclidean_slice_projection hk z) = z := by
  -- Normalize the immersion normal form to the fixed-tail inclusion and then use the zero-slice
  -- equations to reconstruct `z` from its first `k` coordinates.
  rw [rank_normal_form_self_eq_local_euclidean_slice_inclusion_zero hk]
  exact euclidean_slice_inclusion_projection hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) hz

/-- Helper for Theorem 5.51: after restricting a local inclusion normal form to an ambient open
patch, the ambient image is the literal zero-tail Euclidean slice provided the slice projection
stays inside the source-chart target on that patch. -/
private theorem restricted_local_normal_form_image_subset_zero_slice
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S] {x : S}
    (hk : k ≤ n)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt (Subtype.val : S → M) x
      (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W}) :
    (hNF.codChart.restr W) '' (S ∩ (hNF.codChart.restr W).source) ⊆
      Set.euclideanSlice (hNF.codChart.restr W).target k hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  have hyImage :
      y ∈ Subtype.val '' hNF.domChart.source := by
    rw [local_normal_form_source_image_eq_restricted_patch
      (x := x) (hNF := hNF) (W := W)
      (hW_open := hW_open) (hW_eq := hW_eq)]
    exact hy
  rcases hyImage with ⟨yS, hyS, rfl⟩
  refine ⟨?_, ?_⟩
  · -- The restricted ambient chart already lands in its own target on source points.
    exact (hNF.codChart.restr W).map_source hy.2
  · -- The local normal form forces all tail coordinates to vanish on the image.
    intro i
    have hyTarget : hNF.domChart yS ∈ hNF.domChart.target :=
      hNF.domChart.map_source hyS
    have hyLeftInv : hNF.domChart.symm (hNF.domChart yS) = yS := by
      exact hNF.domChart.left_inv hyS
    have hcoord :
        (hNF.codChart.restr W) yS.1 =
          LocalNormalFormAPI.rank_normal_form k n k (hNF.domChart yS) := by
      simpa [hyLeftInv, Function.comp] using hNF.eqOn hyTarget
    simpa [hcoord, rank_normal_form_self_eq_local_euclidean_slice_inclusion_zero hk] using
      (euclidean_slice_inclusion_tail hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ))
        (hNF.domChart yS) i)

/-- Helper for Theorem 5.51: if points of the restricted zero-tail slice project back into the
domain-chart target, then each such point comes from the restricted ambient image of the subtype
patch. -/
private theorem restricted_local_normal_form_zero_slice_subset_image_of_projection_mem_target
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S] {x : S}
    (hk : k ≤ n)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt (Subtype.val : S → M) x
      (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W})
    (hproj :
      ∀ {z : EuclideanSpace ℝ (Fin n)},
        z ∈ Set.euclideanSlice (hNF.codChart.restr W).target k hk
            (fun _ : Fin (n - k) ↦ (0 : ℝ)) →
          euclidean_slice_projection hk z ∈ hNF.domChart.target) :
    Set.euclideanSlice (hNF.codChart.restr W).target k hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ)) ⊆
      (hNF.codChart.restr W) '' (S ∩ (hNF.codChart.restr W).source) := by
  intro z hz
  let yS : S := hNF.domChart.symm (euclidean_slice_projection hk z)
  have hyTarget : euclidean_slice_projection hk z ∈ hNF.domChart.target := hproj hz
  have hyDom : yS ∈ hNF.domChart.source := by
    simpa [yS] using hNF.domChart.symm.map_source hyTarget
  have hyCodSource : yS.1 ∈ hNF.codChart.source := by
    exact (LocalNormalFormAPI.LocalCoordinateNormalFormAt.mapsTo_source hNF) hyDom
  have hyW : yS.1 ∈ W := by
    simpa [hW_eq, yS] using hyDom
  have hyRestr : yS.1 ∈ (hNF.codChart.restr W).source := by
    -- Restricting the codomain chart only adds the ambient patch membership `yS.1 ∈ W`.
    rw [hNF.codChart.restr_source' W hW_open]
    exact ⟨hyCodSource, hyW⟩
  have hyCoord :
      (hNF.codChart.restr W) yS.1 = z := by
    -- Route correction: the reverse inclusion needs the source-proof projection hypothesis
    -- `hproj`, because the unrestricted normal form alone does not force the projected point to
    -- stay in `domChart.target`.
    calc
      (hNF.codChart.restr W) yS.1 =
          LocalNormalFormAPI.rank_normal_form k n k (euclidean_slice_projection hk z) := by
            simpa [yS, Function.comp] using hNF.eqOn hyTarget
      _ = z := zero_slice_point_eq_rank_normal_form_projection hk hz
  refine ⟨yS.1, ⟨yS.2, hyRestr⟩, ?_⟩
  exact hyCoord

/-- Helper for Theorem 5.51: after restricting a local inclusion normal form to an ambient open
patch, the ambient image is the literal zero-tail Euclidean slice provided the slice projection
stays inside the source-chart target on that patch. -/
private theorem restricted_local_normal_form_image_eq_zero_slice_of_projection_mem_target
    {S : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S] {x : S}
    (hk : k ≤ n)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt (Subtype.val : S → M) x
      (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W})
    (hproj :
      ∀ {z : EuclideanSpace ℝ (Fin n)},
        z ∈ Set.euclideanSlice (hNF.codChart.restr W).target k hk
            (fun _ : Fin (n - k) ↦ (0 : ℝ)) →
          euclidean_slice_projection hk z ∈ hNF.domChart.target) :
    (hNF.codChart.restr W) '' (S ∩ (hNF.codChart.restr W).source) =
      Set.euclideanSlice (hNF.codChart.restr W).target k hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- The forward inclusion is the restricted-image half of the local normal form.
    exact restricted_local_normal_form_image_subset_zero_slice
      (x := x) hk hNF (W := W) hW_open hW_eq
  · -- The reverse inclusion uses the supplied projection-stability hypothesis.
    exact restricted_local_normal_form_zero_slice_subset_image_of_projection_mem_target
      (x := x) hk hNF (W := W) hW_open hW_eq hproj

/-- Helper for Theorem 5.51: once the immersion normal form is restricted to `W ∩ W'`, points of
the restricted chart source automatically lie in the original ambient patch `W`, so the patch
subset `P = S ∩ W` and the original subset `S` agree on that source. -/
private theorem restricted_normal_form_source_eq_original_on_interior_patch
    {S W W' : Set M}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hWW'_open : IsOpen (W ∩ W')) :
    S ∩ (e.restr (W ∩ W')).source = (S ∩ W) ∩ (e.restr (W ∩ W')).source := by
  -- Expand the restricted source once; the `W`-membership needed on the right is already stored
  -- in the patch condition on the left.
  ext y
  rw [e.restr_source' (W ∩ W') hWW'_open]
  constructor
  · rintro ⟨hyS, hyRestr⟩
    exact ⟨⟨hyS, hyRestr.2.1⟩, hyRestr⟩
  · rintro ⟨hySW, hyRestr⟩
    exact ⟨hySW.1, hyRestr⟩

/-- Helper for Theorem 5.51: transport the Euclidean charted-space structure across a
homeomorphism onto a local ambient patch. -/
private noncomputable abbrev transported_patch_chartedSpace
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
    {P : Set M}
    (e : N ≃ₜ P) :
    ChartedSpace (EuclideanSpace ℝ (Fin k)) P := by
  let _ : ChartedSpace N P :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Use the explicit singleton-chart transport so the Euclidean owner stays visible to Lean.
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin k)) N P

/-- Helper for Theorem 5.51: a local patch homeomorphic to a Euclidean `k`-manifold inherits the
Euclidean smooth structure at the outer regularity `⊤`. -/
private theorem transported_patch_isManifold_top
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) N]
    {P : Set M}
    (e : N ≃ₜ P) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) P :=
      transported_patch_chartedSpace (M := M) (k := k) e
    IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) P := by
  let eP : OpenPartialHomeomorph P N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N P := eP.singletonChartedSpace (by
    ext x
    simp [eP])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) P :=
    transported_patch_chartedSpace (M := M) (k := k) e
  have hGroupoid : HasGroupoid P (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 k)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eP := by
      simpa [eP] using eP.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eP]) f hf
    have hf'Eq : f' = eP := by
      simpa [eP] using eP.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eP]) f' hf'
    subst f
    subst f'
    have hmid : eP.symm.trans eP = OpenPartialHomeomorph.refl N := by
      simpa [eP] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the already-known Euclidean compatibility on `N`.
    have hcompat :
        ((c.symm ≫ₕ (eP.symm ≫ₕ eP)) ≫ₕ c') ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 k) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 k)) hc hc'
    simpa [eP, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines a smooth Euclidean manifold structure.
  exact IsManifold.mk' (𝓡 k) (⊤ : WithTop ℕ∞) P

/-- Helper for Theorem 5.51: after transporting a Euclidean patch structure, the subtype
inclusion factors through the original local parametrization by composing with the inverse
homeomorphism. -/
private theorem transported_patch_subtype_val_eq_comp_homeomorph_symm
    {N : Type*} [TopologicalSpace N]
    {P : Set M}
    (e : N ≃ₜ P)
    (g : N → M)
    (he : ∀ x, ((e x : P) : M) = g x) :
    (Subtype.val : P → M) = g ∘ e.symm := by
  -- Evaluate the factorization at a point of the transported patch and rewrite with `e (e.symm y)`.
  funext y
  simpa using he (e.symm y)

/-- Helper for Theorem 5.51: transporting a Euclidean source patch along a homeomorphism preserves
the immersion statement for the induced subtype inclusion at the owner `↑⊤` used by the local
normal-form API. -/
private theorem transported_patch_subtype_val_isImmersion
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) N]
    {g : N → M}
    (hg : Manifold.IsImmersion
      (𝓡 k)
      (𝓡 n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      g)
    {P : Set M}
    (e : N ≃ₜ P)
    (he : ∀ x, ((e x : P) : M) = g x) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) P :=
      transported_patch_chartedSpace (M := M) (k := k) e
    let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) P :=
      transported_patch_isManifold_top (M := M) (k := k) e
    Manifold.IsImmersion
      (𝓡 k)
      (𝓡 n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Subtype.val : P → M) := by
  let instCharted : ChartedSpace (EuclideanSpace ℝ (Fin k)) P :=
    transported_patch_chartedSpace (M := M) (k := k) e
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) P := instCharted
  let instManifold : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) P :=
    transported_patch_isManifold_top (M := M) (k := k) e
  let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) P := instManifold
  let _ : IsManifold (𝓡 k) (↑(⊤ : ℕ∞) : WithTop ℕ∞) N :=
    IsManifold.of_le
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      (by simp)
  let _ : IsManifold (𝓡 k) (↑(⊤ : ℕ∞) : WithTop ℕ∞) P :=
    IsManifold.of_le
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      (by simp)
  let _ : IsManifold (𝓡 n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) M :=
    IsManifold.of_le
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      (by simp)
  let hCompImm := hg.isImmersionOfComplement_complement
  let eP : OpenPartialHomeomorph P N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N P := eP.singletonChartedSpace (by
    ext z
    simp [eP])
  -- Route correction: record the transported pointwise immersion witness first, so the ambient
  -- subtype inclusion on the local patch uses exactly the same charts as the original map `g`.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm (e.symm x)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the patch point `x`.
    simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is the same pointwise statement as for the original map `g`.
    have hxe : g (e.symm x) = (x : M) := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- The transported source chart stays in the maximal atlas after chart transport.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eP := by
      simpa [eP] using eP.singletonChartedSpace_mem_atlas_eq (h := by
        ext z
        simp [eP]) f hf
    subst f
    have hmid : eP.symm.trans eP = OpenPartialHomeomorph.refl N := by
      simpa [eP] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eP.symm ≫ₕ eP)) ≫ₕ c') ∈
            contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 k) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eP, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eP.symm ≫ₕ eP)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 k) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eP, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `Subtype.val ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = (z : M) := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- In the transported source chart, the patch inclusion has the same written-in-charts form
    -- as the original parametrization `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend (𝓡 k)).target := by
      simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ((e (hx.domChart.symm u) : P) : M) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Theorem 5.51: once a point-centered ambient patch is identified with an open
Euclidean neighborhood, that patch carries the Euclidean `k`-manifold owner. -/
private theorem interior_chart_patch_isManifold_euclidean
    {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k))}
    {P : Set M}
    (e : V ≃ₜ P) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) P :=
      transported_patch_chartedSpace (M := M) (k := k) e
    IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) P := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) V := inferInstance
  let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) V := inferInstance
  -- The source of the local patch is literally an open Euclidean subset, so the generic
  -- transport package applies without any further compatibility work.
  simpa using transported_patch_isManifold_top (M := M) (k := k) e

-- Helper for Theorem 5.51: the interior-branch local-slice proof starts here.
-- Route correction: the positive-dimensional interior normal form should come from
-- `smooth_immersion_local_inclusion_form`; keep the entire local-slice theorem as a single
-- structural blocker until that chart-comparison route is rebuilt.
-- The following helper begins the explicit Euclidean chart bookkeeping used in that route.
/-- Helper for Theorem 5.51: the Euclidean target of the interior chart is viewed as the canonical
open subset of `ℝ^k`. -/
private noncomputable def interior_chart_target_opens
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (x : S) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) :=
  ⟨(interior_euclidean_chart_at (k := k) S x).target,
    (interior_euclidean_chart_at (k := k) S x).open_target⟩

/-- Helper for Theorem 5.51: in positive dimension, the Euclideanized interior-chart target is
exactly the source patch of the fixed Euclidean-to-boundary-model chart cut down by the ambient
boundary chart target. -/
private theorem interior_chart_target_opens_eq_source_restriction
    {m : ℕ} (S : Set M) [SmoothManifoldWithBoundary (m + 1) S]
    (x : S) :
    ((interior_chart_target_opens (k := m + 1) S x :
        TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) =
      {z | z ∈ boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))) ∧
          euclidean_space_to_boundary_model_chart_at
              (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1))) z ∈
            (chartAt (ℍ^{(m + 1)}) x).target} := by
  -- Route correction: unfold exactly one `trans_target` so the target becomes the restricted
  -- source patch dictated by the source proof, instead of an opaque nested `trans`.
  ext z
  change
      z ∈ (euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))).source ∧
        euclidean_space_to_boundary_model_chart_at
          (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1))) z ∈
            (chartAt (ℍ^{(m + 1)}) x).target ↔
      z ∈ boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))) ∧
        euclidean_space_to_boundary_model_chart_at
          (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1))) z ∈
            (chartAt (ℍ^{(m + 1)}) x).target
  simpa [interior_chart_target_opens, interior_euclidean_chart_at,
    euclidean_space_to_boundary_model_chart_at, OpenPartialHomeomorph.trans_target]

/-- Helper for Theorem 5.51: the normalized interior-chart target can be viewed as the
corresponding open subset of the chart-at-`0` source open, so the later `restrictOpen`
construction only has to transport between equivalent subtype presentations. -/
private noncomputable def interior_chart_target_source_restriction_opens
    {m : ℕ} (S : Set M) [SmoothManifoldWithBoundary (m + 1) S]
    (x : S) :
    TopologicalSpace.Opens
      (boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))) :=
  ⟨{z | (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
      ((interior_chart_target_opens (k := m + 1) S x :
          TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _)}, by
    -- This is the ambient-target patch pulled back along the canonical source-open inclusion.
    simpa [Set.preimage, Function.comp] using
      (interior_chart_target_opens (k := m + 1) S x).2.preimage continuous_subtype_val⟩

/-- Helper for Theorem 5.51: after the target normalization, the source-side restriction inside
`boundary_model_source_opens 0` is exactly cut out by the ambient boundary-chart target
constraint. -/
private theorem interior_chart_target_source_restriction_opens_eq_preimage
    {m : ℕ} (S : Set M) [SmoothManifoldWithBoundary (m + 1) S]
    (x : S) :
    ((interior_chart_target_source_restriction_opens (m := m) (S := S) x :
        TopologicalSpace.Opens
          (boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))))) : Set _) =
      {z : boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))) |
        euclidean_space_to_boundary_model_chart_at
            (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))
            (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
          ((⟨(chartAt (ℍ^{(m + 1)}) x).target, (chartAt (ℍ^{(m + 1)}) x).open_target⟩ :
              TopologicalSpace.Opens (ℍ^{(m + 1)})) : Set (ℍ^{(m + 1)}))} := by
  ext z
  -- Route correction: record the source-open transport once, so the later `restrictOpen` image
  -- computation works on a genuine `Opens` of `boundary_model_source_opens 0`.
  change
      (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
        ((interior_chart_target_opens (k := m + 1) S x :
            TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) ↔
      euclidean_space_to_boundary_model_chart_at
          (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))
          (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
        ((⟨(chartAt (ℍ^{(m + 1)}) x).target, (chartAt (ℍ^{(m + 1)}) x).open_target⟩ :
            TopologicalSpace.Opens (ℍ^{(m + 1)})) : Set (ℍ^{(m + 1)}))
  rw [interior_chart_target_opens_eq_source_restriction (m := m) (S := S) (x := x)]
  exact and_iff_right z.2

/-- Helper for Theorem 5.51: membership in the normalized source-side restriction is already the
target-membership statement needed before transporting the interior local normal form back to the
boundary-model chart at `x`. -/
private theorem interior_chart_target_source_restriction_mem_chart_target
    {m : ℕ} (S : Set M) [SmoothManifoldWithBoundary (m + 1) S]
    (x : S)
    {z : boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))}
    (hz : z ∈ interior_chart_target_source_restriction_opens (m := m) (S := S) x) :
    euclidean_space_to_boundary_model_chart_at
        (k := m + 1) (0 : EuclideanSpace ℝ (Fin (m + 1)))
        (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
      (chartAt (ℍ^{(m + 1)}) x).target := by
  -- Route correction: isolate the normalized-target seam first, instead of trying to jump
  -- directly from slice-target membership to the final projection-into-`domChart.target` claim.
  change
      z ∈ ((interior_chart_target_source_restriction_opens
        (m := m) (S := S) x :
          TopologicalSpace.Opens
            (boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1))))) : Set _) at hz
  rw [interior_chart_target_source_restriction_opens_eq_preimage
    (m := m) (S := S) (x := x)] at hz
  exact hz

/-- Helper for Theorem 5.51: the normalized target patch and the corresponding open subset of the
chart-at-`0` source open carry the same underlying Euclidean points. This is the source-side
transport needed before applying `Diffeomorph.restrictOpen`. -/
private noncomputable def interior_chart_target_source_restriction_homeomorph
    {m : ℕ} (S : Set M) [SmoothManifoldWithBoundary (m + 1) S]
    (x : S) :
    interior_chart_target_source_restriction_opens (m := m) (S := S) x ≃ₜ
      interior_chart_target_opens (k := m + 1) S x where
  toFun := fun z ↦ ⟨z.1.1, z.2⟩
  invFun := fun z ↦
    ⟨⟨z.1, by
        have hz :
            (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
              ((interior_chart_target_opens (k := m + 1) S x :
                  TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) :=
          z.2
        rw [interior_chart_target_opens_eq_source_restriction (m := m) (S := S) (x := x)] at hz
        exact hz.1⟩, z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    exact Subtype.ext rfl
  continuous_toFun := by
    -- The forward map forgets only the extra source-open proof.
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z ↦ z.2)
  continuous_invFun := by
    -- The inverse reinstates the source-open proof provided by the normalized target description.
    have hInner :
        Continuous fun z : interior_chart_target_opens (k := m + 1) S x ↦
          (⟨(z : EuclideanSpace ℝ (Fin (m + 1))), by
              have hz :
                  (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
                    ((interior_chart_target_opens (k := m + 1) S x :
                        TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) :=
                z.2
              rw [interior_chart_target_opens_eq_source_restriction (m := m) (S := S) (x := x)] at hz
              exact hz.1⟩ :
            boundary_model_source_opens (0 : EuclideanSpace ℝ (Fin (m + 1)))) := by
      exact Continuous.subtype_mk continuous_subtype_val (fun z ↦ by
        have hz :
            (z : EuclideanSpace ℝ (Fin (m + 1))) ∈
              ((interior_chart_target_opens (k := m + 1) S x :
                  TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) : Set _) :=
          z.2
        rw [interior_chart_target_opens_eq_source_restriction (m := m) (S := S) (x := x)] at hz
        exact hz.1)
    exact Continuous.subtype_mk hInner (fun z ↦ z.2)

/-- Helper for Theorem 5.51: an interior point of a smoothly embedded subtype admits an ambient
slice chart. The detailed proof goes through the centered Euclidean chart on the subtype and the
ordinary local normal form for immersions; the previous expanded seam proof is intentionally
collapsed here because its private owner-transport scaffolding was tied to brittle open-subtype
instances. -/
theorem smooth_embedding_subtype_val_has_local_slice_at_of_isInteriorPoint
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (hS :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M))
    (x : S)
    (hxInt : (leeBoundaryModelWithCorners k).IsInteriorPoint x) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x.1 ∈ e.source ∧ e.IsSliceChart S k := by
  sorry

/-- Helper for Theorem 5.51: a boundary point of the source boundary model admits an ambient
half-slice chart for the subtype inclusion. -/
-- Route correction: keep the boundary branch as a single blocker until the Euclidean
-- half-slice-to-`ℍ^k` adapter is proved in local coordinates.
theorem smooth_embedding_subtype_val_has_local_half_slice_at_of_isBoundaryPoint
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (hS :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M))
    (x : S)
    (hxBd : (leeBoundaryModelWithCorners k).IsBoundaryPoint x) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x.1 ∈ e.source ∧ e.IsBoundarySliceChart S k := by
  by_cases hk0 : k = 0
  · -- The zero-dimensional boundary model is boundaryless, so no boundary-point branch remains.
    subst hk0
    exact False.elim (zero_dimensional_boundary_model_not_isBoundaryPoint (S := S) x hxBd)
  -- TODO: first exclude the `k = 0` case via
  -- `zero_dimensional_boundary_model_not_isBoundaryPoint`, then express the local inclusion form
  -- on a half-space source patch and use the same restricted-chart bookkeeping lemmas to show the
  -- restricted codomain chart has Euclidean half-slice image. The interior zero-slice bridge is
  -- now isolated behind
  -- `restricted_local_normal_form_image_eq_zero_slice_of_projection_mem_target`; the boundary
  -- branch still needs the half-slice analogue that additionally records the distinguished
  -- nonnegative coordinate.
  sorry

/-- Helper for Theorem 5.51: a point of a smoothly embedded subtype admits an ambient chart whose
local image is either a Euclidean slice or a Euclidean half-slice. -/
theorem smooth_embedding_subtype_val_has_local_slice_or_half_slice_at
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (hS :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M))
    (x : S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x.1 ∈ e.source ∧ (e.IsSliceChart S k ∨ e.IsBoundarySliceChart S k) := by
  classical
  by_cases hxInt : (leeBoundaryModelWithCorners k).IsInteriorPoint x
  · -- The interior branch is the ordinary slice normal form for the smooth embedding.
    rcases smooth_embedding_subtype_val_has_local_slice_at_of_isInteriorPoint
        (S := S) hS x hxInt with ⟨e, hxsource, heSlice⟩
    exact ⟨e, hxsource, Or.inl heSlice⟩
  · -- Non-interior points of the boundary model are boundary points.
    have hxBd : (leeBoundaryModelWithCorners k).IsBoundaryPoint x := by
      by_contra hxNotBd
      exact hxInt <|
        ((leeBoundaryModelWithCorners k).isInteriorPoint_iff_not_isBoundaryPoint x).2 hxNotBd
    rcases smooth_embedding_subtype_val_has_local_half_slice_at_of_isBoundaryPoint
        (S := S) hS x hxBd with ⟨e, hxsource, heHalfSlice⟩
    exact ⟨e, hxsource, Or.inr heHalfSlice⟩

/-- A local `k`-slice structure with boundary on `S ⊆ M` yields a smooth
`k`-manifold-with-boundary structure on the subtype `S` for which the inclusion into `M` is a
smooth embedding. -/
-- Proof sketch: build charts on `S` by restricting each interior or boundary slice chart to the
-- corresponding standard slice or half-slice, use the ambient chart transitions to verify the
-- induced smooth compatibility conditions, and then check that the subtype inclusion is a smooth
-- embedding in those coordinates.
theorem
    satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure
    (S : Set M) (hS : Set.SatisfiesLocalSliceConditionWithBoundary n S k) :
    ∃ _ : SmoothManifoldWithBoundary k S,
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M) := by
  by_cases hEmpty : S = ∅
  · cases hEmpty
    -- The empty subset already has the canonical trivial boundary structure.
    simpa using empty_subtype_smooth_manifold_with_boundary_structure (n := n) (k := k) (M := M)
  · -- The nonempty case is the genuine atlas-construction step from slice and half-slice charts.
    -- Route correction: the forward proof no longer blocks on the whole theorem. The induced
    -- subtype charts are now packaged by `local_slice_condition_with_boundary_chartAt` and
    -- `local_slice_condition_with_boundary_chartedSpace`; the remaining work is the interior
    -- slice-to-`ℍ^k` bridge and the usual smooth-atlas packaging.
    classical
    let _hNonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hk : k ≤ n :=
      satisfies_local_slice_condition_with_boundary_dimension_le
        (S := S) _hNonempty hS
    let _ : ChartedSpace (ℍ^{k}) S :=
      local_slice_condition_with_boundary_chartedSpace (S := S) hS
    -- The dimension bound is now fixed globally, so the only remaining tasks are the source-faithful
    -- chart-transition proof and the local normal-form statement for `Subtype.val`.
    -- TODO: prove `local_slice_condition_with_boundary_chartAt_transition_contDiffOn` using the
    -- fixed `hk`, with four overlap branches (slice/slice, slice/half-slice, half-slice/slice,
    -- half-slice/half-slice), then mirror Theorem 5.8 to obtain
    -- `IsManifold (leeBoundaryModelWithCorners k) 0 S`,
    -- `IsManifold (leeBoundaryModelWithCorners k) ⊤ S`,
    -- and the smooth-embedding coordinate formula for `Subtype.val`.
    sorry

/-- Helper for Theorem 5.51: a smooth manifold-with-boundary structure on the subtype together
with a smooth-embedding subtype inclusion yields the local `k`-slice condition with boundary on
the underlying subset. -/
-- Route correction: isolate the converse into the local normal-form problem for the subtype
-- inclusion, rather than leaving the backward implication entangled with the final `↔` wrapper.
theorem smooth_embedding_subtype_val_satisfiesLocalSliceConditionWithBoundary
    (S : Set M) [SmoothManifoldWithBoundary k S]
    (hS :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        (𝓡 n)
        (⊤ : WithTop ℕ∞)
        ((↑) : S → M)) :
    Set.SatisfiesLocalSliceConditionWithBoundary n S k := by
  by_cases hEmpty : S = ∅
  · cases hEmpty
    -- The empty subset satisfies the local slice condition with boundary vacuously.
    infer_instance
  · -- The nonempty case is the local normal-form argument for the smooth embedding `Subtype.val`.
    refine ⟨?_⟩
    intro x hx
    let xS : S := ⟨x, hx⟩
    -- The pointwise local normal form is isolated in
    -- `smooth_embedding_subtype_val_has_local_slice_or_half_slice_at`.
    simpa [xS] using
      smooth_embedding_subtype_val_has_local_slice_or_half_slice_at
        (S := S)
        hS
        xS

/-- Theorem 5.51: a subset of a smooth boundaryless `n`-manifold satisfies the local `k`-slice
condition for submanifolds with boundary exactly when the subtype `S` admits a smooth
`k`-manifold-with-boundary structure for which its inclusion into `M` is a smooth embedding. -/
-- Proof sketch: if `S` is already an embedded submanifold with boundary, use local normal-form
-- coordinates for the smooth embedding to obtain interior or boundary slice charts. Conversely,
-- build the manifold-with-boundary structure on `S` from those slice charts and check that the
-- subtype inclusion is a smooth embedding in the resulting coordinates.
theorem local_slice_criterion_for_embedded_submanifold_with_boundary
    (S : Set M) :
    Set.SatisfiesLocalSliceConditionWithBoundary n S k ↔
      ∃ _ : SmoothManifoldWithBoundary k S,
        Manifold.IsSmoothEmbedding
          (leeBoundaryModelWithCorners k)
          (𝓡 n)
          (⊤ : WithTop ℕ∞)
          ((↑) : S → M) := by
  constructor
  · intro hS
    -- The forward implication is the induced manifold-with-boundary construction from slice data.
    exact satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure S hS
  · intro hS
    -- The backward implication is the local normal-form statement for the subtype inclusion.
    rcases hS with ⟨hBoundary, hEmbedding⟩
    let _ : SmoothManifoldWithBoundary k S := hBoundary
    exact
      smooth_embedding_subtype_val_satisfiesLocalSliceConditionWithBoundary
        S
        hEmbedding

end
