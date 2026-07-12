import Mathlib
import DifferentialForms_Cartan_1970.VI.section25.«0008_Proposition_4_I»
import DifferentialForms_Cartan_1970.VI.section26.«0002_Definition_VI_5_extra_2»
import DifferentialForms_Cartan_1970.VI.section26.«0008_Problem_VI_5_extra_8».Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped Manifold

/-- Helper for Problem VI.5-extra-8: the lifted continuation chart still carries its ambient
complex coordinate after lowering through the `ULift` chart homeomorphism. -/
noncomputable def continuationLiftedCoordinate
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r → ℂ :=
  fun z ↦
    ((show continuation_chart r from
        (continuation_chart_space r).uliftFunctorObjHomeo.symm z) : ℂ)

/-- Helper for Problem VI.5-extra-8: the lowered ambient coordinate on a lifted continuation chart
is continuous. -/
lemma continuationLiftedCoordinate_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Continuous (continuationLiftedCoordinate (U := U) (f := f) r) := by
  -- Lower the lifted chart point and then forget the subtype coordinate.
  simpa [continuationLiftedCoordinate] using
    (continuous_subtype_val.comp
      (continuation_chart_space r).uliftFunctorObjHomeo.symm.continuous_toFun)

/-- Helper for Problem VI.5-extra-8: on a lifted continuation chart, the lowered ambient
coordinate is an open embedding into `ℂ`. This is the chart-level local-homeomorphism input for
the descended glued projection. -/
lemma continuationLiftedCoordinate_isOpenEmbedding
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Topology.IsOpenEmbedding (continuationLiftedCoordinate (U := U) (f := f) r) := by
  -- The lowered coordinate is just the lifted-chart homeomorphism followed by the inclusion of
  -- the open continuation chart into the ambient plane.
  simpa [continuationLiftedCoordinate, Function.comp] using
    ((continuation_chart r).2.isOpenEmbedding_subtypeVal.comp
      (continuation_chart_space r).uliftFunctorObjHomeo.symm.isOpenEmbedding)

/-- Helper for Problem VI.5-extra-8: the lifted continuation coordinate, repackaged in the common
universe used by the glued quotient. -/
noncomputable def continuationLiftedCoordinateUp
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r → ULift ℂ :=
  fun z ↦ ULift.up (continuationLiftedCoordinate (U := U) (f := f) r z)

/-- Helper for Problem VI.5-extra-8: the universe-lifted continuation coordinate is continuous. -/
lemma continuationLiftedCoordinateUp_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Continuous (continuationLiftedCoordinateUp (U := U) (f := f) r) := by
  -- The only new step is the continuous universe lift from `ℂ` to `ULift ℂ`.
  let hup : Continuous (fun x : ℂ ↦ (ULift.up x : ULift ℂ)) := by
    fun_prop
  simpa [continuationLiftedCoordinateUp] using
    hup.comp (continuationLiftedCoordinate_continuous (U := U) (f := f) r)

/-- Helper for Problem VI.5-extra-8: the lifted continuation coordinate as a chart morphism into
the universe-aligned copy of `ℂ`. -/
noncomputable def continuationLiftedCoordinateHom
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r ⟶ TopCat.of (ULift ℂ) :=
  TopCat.ofHom
    ⟨continuationLiftedCoordinateUp (U := U) (f := f) r,
      continuationLiftedCoordinateUp_continuous (U := U) (f := f) r⟩

/-- Helper for Problem VI.5-extra-8: the lowered ambient coordinate is unchanged across a lifted
overlap transition, so it descends through the glued quotient. -/
lemma continuationLiftedCoordinate_compat
    {U : Set ℂ} {f : ℂ → ℂ}
    (a : ContinuationRepresentative U f × ContinuationRepresentative U f) :
    CategoryTheory.CategoryStruct.comp
        ((continuation_glueData (U := U) (f := f)).diagram.fst a)
        (continuationLiftedCoordinateHom (U := U) (f := f) a.1) =
      CategoryTheory.CategoryStruct.comp
        ((continuation_glueData (U := U) (f := f)).diagram.snd a)
        (continuationLiftedCoordinateHom (U := U) (f := f) a.2) := by
  rcases a with ⟨r, s⟩
  -- Compare both composites pointwise and lower the lifted transition back to the original chart.
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply congrArg ULift.up
  simpa [continuationLiftedCoordinateUp, continuationLiftedCoordinate,
      continuation_lifted_overlap_down, continuation_overlap_swap_val,
      continuation_glueData, continuation_glueData_core,
      continuation_lifted_overlap_transition] using
    congrArg (fun y : continuation_overlap_open s r ↦ ((y : continuation_chart s) : ℂ))
      (continuation_lifted_transition_lower_eq (r := r) (s := s) x)

/-- Helper for Problem VI.5-extra-8: the base projection on the glued continuation quotient,
defined by descending the chart coordinates. -/
noncomputable def continuationGluedProjectionUpHom
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued ⟶ TopCat.of (ULift ℂ) :=
  CategoryTheory.Limits.Multicoequalizer.desc
    ((continuation_glueData (U := U) (f := f)).diagram)
    (TopCat.of (ULift ℂ))
    (continuationLiftedCoordinateHom (U := U) (f := f))
    (continuationLiftedCoordinate_compat (U := U) (f := f))

/-- Helper for Problem VI.5-extra-8: the descended base projection on the glued continuation
quotient, still valued in the universe-aligned copy of `ℂ`. -/
noncomputable def continuationGluedProjectionUp
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued → ULift ℂ :=
  continuationGluedProjectionUpHom (U := U) (f := f)

/-- Helper for Problem VI.5-extra-8: the descended base projection on the glued continuation
quotient. -/
noncomputable def continuationGluedProjection
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued → ℂ :=
  fun x ↦ (continuationGluedProjectionUp (U := U) (f := f) x).down

/-- Helper for Problem VI.5-extra-8: on each glued chart inclusion, the descended base projection
recovers the original chart coordinate before forgetting the auxiliary universe lift. -/
lemma continuationGluedProjectionUp_apply_ι
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_lifted_chart_space r) :
    continuationGluedProjectionUp (U := U) (f := f)
        ((continuation_glueData (U := U) (f := f)).ι r z) =
      continuationLiftedCoordinateUp (U := U) (f := f) r z := by
  -- Apply the multicoequalizer computation rule directly in the universe-aligned target.
  have h := CategoryTheory.Limits.Multicoequalizer.π_desc
    ((continuation_glueData (U := U) (f := f)).diagram)
    (TopCat.of (ULift ℂ))
    (continuationLiftedCoordinateHom (U := U) (f := f))
    (continuationLiftedCoordinate_compat (U := U) (f := f)) r
  simpa [continuationGluedProjectionUpHom, continuationGluedProjectionUp,
      continuationLiftedCoordinateHom, continuation_glueData] using
    congrArg (fun g ↦ g z) h

/-- Helper for Problem VI.5-extra-8: on each glued chart inclusion, the descended base projection
recovers the original chart coordinate. -/
lemma continuationGluedProjection_apply_ι
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_lifted_chart_space r) :
    continuationGluedProjection (U := U) (f := f)
        ((continuation_glueData (U := U) (f := f)).ι r z) =
      continuationLiftedCoordinate (U := U) (f := f) r z := by
  -- Forget the auxiliary universe lift after the direct `ULift` computation.
  simpa [continuationGluedProjection, continuationLiftedCoordinateUp] using
    congrArg ULift.down
      (continuationGluedProjectionUp_apply_ι (U := U) (f := f) r z)

/-- Helper for Problem VI.5-extra-8: the lifted continuation branch is the branch value of the
representative after lowering through the lifted chart homeomorphism. -/
noncomputable def continuationLiftedBranch
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r → ℂ :=
  fun z ↦
    continuation_branch r
      (show continuation_chart r from
        (continuation_chart_space r).uliftFunctorObjHomeo.symm z)

/-- Helper for Problem VI.5-extra-8: the lifted continuation branch is continuous because the
local branch is holomorphic on its chart. -/
lemma continuationLiftedBranch_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Continuous (continuationLiftedBranch (U := U) (f := f) r) := by
  -- Compose the holomorphic branch with the inverse lifted-chart homeomorphism.
  simpa [continuationLiftedBranch] using
    (continuation_branch_mdifferentiable (U := U) (f := f) r).continuous.comp
      (continuation_chart_space r).uliftFunctorObjHomeo.symm.continuous_toFun

/-- Helper for Problem VI.5-extra-8: the lifted continuation branch, repackaged in the common
universe used by the glued quotient. -/
noncomputable def continuationLiftedBranchUp
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r → ULift ℂ :=
  fun z ↦ ULift.up (continuationLiftedBranch (U := U) (f := f) r z)

/-- Helper for Problem VI.5-extra-8: the universe-lifted continuation branch is continuous. -/
lemma continuationLiftedBranchUp_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Continuous (continuationLiftedBranchUp (U := U) (f := f) r) := by
  -- As for the coordinate map, the only extra step is the continuous universe lift.
  let hup : Continuous (fun x : ℂ ↦ (ULift.up x : ULift ℂ)) := by
    fun_prop
  simpa [continuationLiftedBranchUp] using
    hup.comp (continuationLiftedBranch_continuous (U := U) (f := f) r)

/-- Helper for Problem VI.5-extra-8: the lifted continuation branch as a chart morphism into the
universe-aligned copy of `ℂ`. -/
noncomputable def continuationLiftedBranchHom
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r ⟶ TopCat.of (ULift ℂ) :=
  TopCat.ofHom
    ⟨continuationLiftedBranchUp (U := U) (f := f) r,
      continuationLiftedBranchUp_continuous (U := U) (f := f) r⟩

/-- Helper for Problem VI.5-extra-8: equality of continuation branches on lifted overlaps lets the
branch-value map descend through the glued quotient. -/
lemma continuationLiftedBranch_compat
    {U : Set ℂ} {f : ℂ → ℂ}
    (a : ContinuationRepresentative U f × ContinuationRepresentative U f) :
    CategoryTheory.CategoryStruct.comp
        ((continuation_glueData (U := U) (f := f)).diagram.fst a)
        (continuationLiftedBranchHom (U := U) (f := f) a.1) =
      CategoryTheory.CategoryStruct.comp
        ((continuation_glueData (U := U) (f := f)).diagram.snd a)
        (continuationLiftedBranchHom (U := U) (f := f) a.2) := by
  rcases a with ⟨r, s⟩
  -- Lower the lifted overlap point and use the already proved branch-coincidence theorem.
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply congrArg ULift.up
  simpa [continuationLiftedBranchUp, continuationLiftedBranch, continuation_lifted_overlap_down,
      continuation_glueData, continuation_glueData_core,
      continuation_lifted_overlap_transition] using
    continuation_branch_eq_of_overlap (U := U) (f := f)
      (continuation_lifted_overlap_down (r := r) (s := s) x)

/-- Helper for Problem VI.5-extra-8: the descended extension-value map on the glued continuation
quotient, defined by descending the local continuation branches. -/
noncomputable def continuationGluedExtensionUpHom
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued ⟶ TopCat.of (ULift ℂ) :=
  CategoryTheory.Limits.Multicoequalizer.desc
    ((continuation_glueData (U := U) (f := f)).diagram)
    (TopCat.of (ULift ℂ))
    (continuationLiftedBranchHom (U := U) (f := f))
    (continuationLiftedBranch_compat (U := U) (f := f))

/-- Helper for Problem VI.5-extra-8: the descended extension-value map on the glued continuation
quotient, still valued in the universe-aligned copy of `ℂ`. -/
noncomputable def continuationGluedExtensionUp
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued → ULift ℂ :=
  continuationGluedExtensionUpHom (U := U) (f := f)

/-- Helper for Problem VI.5-extra-8: the descended extension-value map on the glued continuation
quotient. -/
noncomputable def continuationGluedExtension
    {U : Set ℂ} {f : ℂ → ℂ} :
    (continuation_glueData (U := U) (f := f)).glued → ℂ :=
  fun x ↦ (continuationGluedExtensionUp (U := U) (f := f) x).down

/-- Helper for Problem VI.5-extra-8: on each glued chart inclusion, the descended extension-value
map recovers the original continuation branch before forgetting the auxiliary universe lift. -/
lemma continuationGluedExtensionUp_apply_ι
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_lifted_chart_space r) :
    continuationGluedExtensionUp (U := U) (f := f)
        ((continuation_glueData (U := U) (f := f)).ι r z) =
      continuationLiftedBranchUp (U := U) (f := f) r z := by
  -- Apply the multicoequalizer computation rule directly in the universe-aligned target.
  have h := CategoryTheory.Limits.Multicoequalizer.π_desc
    ((continuation_glueData (U := U) (f := f)).diagram)
    (TopCat.of (ULift ℂ))
    (continuationLiftedBranchHom (U := U) (f := f))
    (continuationLiftedBranch_compat (U := U) (f := f)) r
  simpa [continuationGluedExtensionUpHom, continuationGluedExtensionUp,
      continuationLiftedBranchHom, continuation_glueData] using
    congrArg (fun g ↦ g z) h

/-- Helper for Problem VI.5-extra-8: on each glued chart inclusion, the descended extension-value
map recovers the original continuation branch. -/
lemma continuationGluedExtension_apply_ι
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_lifted_chart_space r) :
    continuationGluedExtension (U := U) (f := f)
        ((continuation_glueData (U := U) (f := f)).ι r z) =
      continuationLiftedBranch (U := U) (f := f) r z := by
  -- Forget the auxiliary universe lift after the direct `ULift` computation.
  simpa [continuationGluedExtension, continuationLiftedBranchUp] using
    congrArg ULift.down
      (continuationGluedExtensionUp_apply_ι (U := U) (f := f) r z)

/-- Helper for Problem VI.5-extra-8: the distinguished center point of a continuation
representative, viewed in the lifted chart family used for gluing. -/
noncomputable def continuationRepresentativeCenter
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_chart_space r :=
  (continuation_chart_space r).uliftFunctorObjHomeo
    ⟨r.1.surface.projection r.2, continuation_projection_mem_chart (U := U) (f := f) r⟩

/-- Helper for Problem VI.5-extra-8: lowering the distinguished lifted center point recovers the
projection coordinate of the representative. -/
lemma continuationRepresentativeCenter_coordinate
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuationLiftedCoordinate (U := U) (f := f) r
        (continuationRepresentativeCenter (U := U) (f := f) r) =
      r.1.surface.projection r.2 := by
  -- The lifted center point was defined by applying the forward chart homeomorphism.
  rfl

/-- Helper for Problem VI.5-extra-8: every extension surface maps pointwise into the glued
continuation quotient by the class of its distinguished chart center. -/
noncomputable def continuationComparisonPoint
    {U : Set ℂ} {f : ℂ → ℂ} (E : PlaneHolomorphicExtension U f) :
    E.surface → (continuation_glueData (U := U) (f := f)).glued :=
  fun x ↦
    (continuation_glueData (U := U) (f := f)).ι ⟨E, x⟩
      (continuationRepresentativeCenter (U := U) (f := f) ⟨E, x⟩)

/-- Helper for Problem VI.5-extra-8: the canonical pointwise comparison into the glued quotient
preserves the base projection to `ℂ`. -/
lemma continuationComparisonPoint_projection
    {U : Set ℂ} {f : ℂ → ℂ} (E : PlaneHolomorphicExtension U f) (x : E.surface) :
    continuationGluedProjection (U := U) (f := f)
        (continuationComparisonPoint (U := U) (f := f) E x) =
      E.surface.projection x := by
  -- Compute on the glued chart inclusion and identify the chosen center coordinate.
  simpa [continuationComparisonPoint, continuationRepresentativeCenter_coordinate] using
    continuationGluedProjection_apply_ι (U := U) (f := f) ⟨E, x⟩
      (continuationRepresentativeCenter (U := U) (f := f) ⟨E, x⟩)

/-- Helper for Problem VI.5-extra-8: the canonical pointwise comparison into the glued quotient
preserves the extended holomorphic value. -/
lemma continuationComparisonPoint_extension
    {U : Set ℂ} {f : ℂ → ℂ} (E : PlaneHolomorphicExtension U f) (x : E.surface) :
    continuationGluedExtension (U := U) (f := f)
        (continuationComparisonPoint (U := U) (f := f) E x) =
      E.extension x := by
  -- Compute on the glued chart inclusion and evaluate the continuation branch at the center.
  simpa [continuationComparisonPoint, continuationRepresentativeCenter,
      continuationLiftedBranch] using
    (continuationGluedExtension_apply_ι (U := U) (f := f) ⟨E, x⟩
      (continuationRepresentativeCenter (U := U) (f := f) ⟨E, x⟩)).trans
      (continuation_branch_at_projection (U := U) (f := f) ⟨E, x⟩)

/-- Helper for Problem VI.5-extra-8: near an embedded base point `z : U`, the continuation branch
chosen from any extension agrees with the original germ `f`. This is the common-base bridge used
to compare different representatives above the same point of `U`. -/
lemma continuation_branch_eventually_eq_original
    {U : Set ℂ} (hU_open : IsOpen U) {f : ℂ → ℂ}
    (E : PlaneHolomorphicExtension U f) (z : U) :
    continuation_branch ⟨E, E.embedding z⟩ =ᶠ[
        nhds ⟨(z : ℂ),
          by
            simpa [E.projection_comp_embedding z] using
              continuation_projection_mem_chart (U := U) (f := f) ⟨E, E.embedding z⟩⟩]
      fun w ↦ f (w : ℂ) := by
  let r : ContinuationRepresentative U f := ⟨E, E.embedding z⟩
  let z₀ : continuation_chart r :=
    ⟨(z : ℂ), by
      simpa [r, E.projection_comp_embedding z] using
        continuation_projection_mem_chart (U := U) (f := f) r⟩
  obtain ⟨W, hW_nhds, hW_emb⟩ :=
    isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp E.surface.isLocalHomeomorph (E.embedding z)
  have hchart_eq :
      nhdsWithin (z : ℂ) (continuation_chart r) = nhds (z : ℂ) := by
    -- The continuation chart is open around the chosen base coordinate.
    exact (continuation_chart_isOpen (U := U) (f := f) r).nhdsWithin_eq z₀.2
  change ∀ᶠ w : continuation_chart r in nhds z₀, continuation_branch r w = f (w : ℂ)
  have hlocal :
      ∀ᶠ w : continuation_chart r in nhds z₀,
        (E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w ∈ W := by
    have hcontLocal :
        Continuous (fun w : continuation_chart r ↦
          (E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w) :=
      (continuation_local_inverse_mdifferentiable (U := U) (f := f) r).continuous
    have hz₀_eq :
        z₀ =
          ⟨E.surface.projection (E.embedding z),
            continuation_projection_mem_chart (U := U) (f := f) r⟩ := by
      apply Subtype.ext
      simpa [r] using (E.projection_comp_embedding z).symm
    have hlocalSelf :
        (E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) z₀ = E.embedding z := by
      rw [hz₀_eq]
      exact E.surface.isLocalHomeomorph.localInverseAt_apply_self (x := E.embedding z)
    have hW_local :
        W ∈ nhds ((E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) z₀) := by
      simpa [hlocalSelf] using hW_nhds
    simpa [r, z₀] using hcontLocal.continuousAt.preimage_mem_nhds
      hW_local
  have hEmbeddingOnU :
      ∀ᶠ u : U in nhds z, E.embedding u ∈ W := by
    -- The distinguished embedding is continuous at `z`, so nearby base points still land in
    -- the same injectivity neighborhood `W`.
    exact E.isOpenEmbedding_embedding.continuous.continuousAt.preimage_mem_nhds hW_nhds
  have hEmbeddingOnUExists :
      ∀ᶠ u : U in nhds z, ∃ hwU : (u : ℂ) ∈ U, E.embedding ⟨(u : ℂ), hwU⟩ ∈ W := by
    filter_upwards [hEmbeddingOnU] with u hu
    exact ⟨u.2, by simpa using hu⟩
  have hEmbeddingOnBase :
      ∀ᶠ w in nhds (z : ℂ), ∃ hwU : w ∈ U, E.embedding ⟨w, hwU⟩ ∈ W := by
    rw [← hU_open.nhdsWithin_eq z.2]
    exact (eventually_nhds_subtype_iff U z
      (fun w : ℂ ↦ ∃ hwU : w ∈ U, E.embedding ⟨w, hwU⟩ ∈ W)).1 hEmbeddingOnUExists
  have hembedding :
      ∀ᶠ w : continuation_chart r in nhds z₀,
        ∃ hwU : (w : ℂ) ∈ U, E.embedding ⟨(w : ℂ), hwU⟩ ∈ W := by
    have hEmbeddingOnChartBase :
        ∀ᶠ x in nhdsWithin (z : ℂ) (continuation_chart r),
          ∃ hwU : x ∈ U, E.embedding ⟨x, hwU⟩ ∈ W := by
      simpa [hchart_eq, z₀] using hEmbeddingOnBase
    exact (eventually_nhds_subtype_iff (continuation_chart r) z₀
      (fun w : ℂ ↦ ∃ hwU : w ∈ U, E.embedding ⟨w, hwU⟩ ∈ W)).2 <| by
        exact hEmbeddingOnChartBase
  -- Route correction: compare the chosen local inverse branch with the distinguished embedding
  -- on a single injective neighborhood of the projection, instead of trying to identify the two
  -- local branches definitionally.
  filter_upwards [hlocal, hembedding] with w hwLocal ⟨hwU, hwEmbedding⟩
  have hproj_eq :
      (W.restrict E.surface.projection) ⟨
          (E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w, hwLocal⟩ =
        (W.restrict E.surface.projection) ⟨E.embedding ⟨(w : ℂ), hwU⟩, hwEmbedding⟩ := by
    -- Both candidate points project to the same nearby base coordinate `w`.
    change
      E.surface.projection ((E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w) =
        E.surface.projection (E.embedding ⟨(w : ℂ), hwU⟩)
    calc
      E.surface.projection ((E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w) =
          (w : ℂ) := by
            simpa [r] using continuation_projection_localInverse (U := U) (f := f) r w
      _ = E.surface.projection (E.embedding ⟨(w : ℂ), hwU⟩) := by
            simpa using (E.projection_comp_embedding ⟨(w : ℂ), hwU⟩).symm
  have hpoints :
      (E.surface.isLocalHomeomorph.localInverseAt (E.embedding z)) w =
        E.embedding ⟨(w : ℂ), hwU⟩ := by
    -- Injectivity of the restricted projection on `W` forces the two lifts to coincide.
    exact congrArg Subtype.val (hW_emb.isEmbedding.injective hproj_eq)
  -- Replacing the lifted point by the embedded one turns the branch value into `f w`.
  calc
    continuation_branch r w = E.extension (E.embedding ⟨(w : ℂ), hwU⟩) := by
      simpa [continuation_branch, r] using congrArg E.extension hpoints
    _ = f (w : ℂ) := by
      simpa using E.extension_comp_embedding ⟨(w : ℂ), hwU⟩

/-- Helper for Problem VI.5-extra-8: all canonical comparison maps into the glued continuation
quotient agree on the embedded base copy of `U`. This supplies the common-base compatibility
needed both for the final embedding and for the universal comparison morphisms. -/
lemma continuationComparisonPoint_embedding_eq
    {U : Set ℂ} (hU_open : IsOpen U) {f : ℂ → ℂ}
    (E₁ E₂ : PlaneHolomorphicExtension U f) (z : U) :
    continuationComparisonPoint (U := U) (f := f) E₁ (E₁.embedding z) =
      continuationComparisonPoint (U := U) (f := f) E₂ (E₂.embedding z) := by
  let r₁ : ContinuationRepresentative U f := ⟨E₁, E₁.embedding z⟩
  let r₂ : ContinuationRepresentative U f := ⟨E₂, E₂.embedding z⟩
  have hz₁_chart : (z : ℂ) ∈ continuation_chart r₁ := by
    simpa [r₁, E₁.projection_comp_embedding z] using
      continuation_projection_mem_chart (U := U) (f := f) r₁
  have hz₂_chart : (z : ℂ) ∈ continuation_chart r₂ := by
    simpa [r₂, E₂.projection_comp_embedding z] using
      continuation_projection_mem_chart (U := U) (f := f) r₂
  let z₁ : continuation_chart r₁ := ⟨(z : ℂ), hz₁_chart⟩
  let z₂ : continuation_chart r₂ := ⟨(z : ℂ), hz₂_chart⟩
  let z₁₂ : continuation_common_chart r₁ r₂ := ⟨(z : ℂ), ⟨hz₁_chart, hz₂_chart⟩⟩
  have hcontLeft :
      Continuous
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r₁ r₂ ≤ continuation_chart r₁ from inf_le_left)) :=
    continuous_inclusion
      (show (continuation_common_chart r₁ r₂ : Set ℂ) ⊆ continuation_chart r₁ from inf_le_left)
  have hcontRight :
      Continuous
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r₁ r₂ ≤ continuation_chart r₂ from inf_le_right)) :=
    continuous_inclusion
      (show (continuation_common_chart r₁ r₂ : Set ℂ) ⊆ continuation_chart r₂ from inf_le_right)
  have htendstoLeft :
      Filter.Tendsto
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r₁ r₂ ≤ continuation_chart r₁ from inf_le_left))
        (nhds z₁₂) (nhds z₁) := by
    exact hcontLeft.continuousAt
  have htendstoRight :
      Filter.Tendsto
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r₁ r₂ ≤ continuation_chart r₂ from inf_le_right))
        (nhds z₁₂) (nhds z₂) := by
    exact hcontRight.continuousAt
  have hleft :
      continuation_left_branch r₁ r₂ =ᶠ[nhds z₁₂] fun w ↦ f (w : ℂ) := by
    -- Restrict the left continuation branch to the common chart and then replace it by the
    -- original germ on the embedded base neighborhood.
    simpa [continuation_left_branch] using
      (continuation_branch_eventually_eq_original (U := U) (f := f) hU_open E₁ z).comp_tendsto
        htendstoLeft
  have hright :
      continuation_right_branch r₁ r₂ =ᶠ[nhds z₁₂] fun w ↦ f (w : ℂ) := by
    -- The right restricted branch is handled symmetrically.
    simpa [continuation_right_branch] using
      (continuation_branch_eventually_eq_original (U := U) (f := f) hU_open E₂ z).comp_tendsto
        htendstoRight
  have hzOverlap : (z₁ : continuation_chart r₁) ∈ continuation_overlap_open r₁ r₂ := by
    -- The two restricted branches agree near the common base point because both equal `f` there.
    refine (mem_continuation_overlap_open_iff (r := r₁) (s := r₂)).2 ?_
    refine ⟨hz₂_chart, ?_⟩
    change continuation_left_branch r₁ r₂ =ᶠ[nhds z₁₂] continuation_right_branch r₁ r₂
    exact hleft.trans hright.symm
  have hcenter₁ :
      continuationRepresentativeCenter (U := U) (f := f) r₁ =
        (continuation_chart_space r₁).uliftFunctorObjHomeo z₁ := by
    apply (continuation_chart_space r₁).uliftFunctorObjHomeo.symm.injective
    simp [continuationRepresentativeCenter, r₁, z₁, E₁.projection_comp_embedding z]
  have hcenter₂ :
      continuationRepresentativeCenter (U := U) (f := f) r₂ =
        (continuation_chart_space r₂).uliftFunctorObjHomeo z₂ := by
    apply (continuation_chart_space r₂).uliftFunctorObjHomeo.symm.injective
    simp [continuationRepresentativeCenter, r₂, z₂, E₂.projection_comp_embedding z]
  let x : continuation_lifted_overlap_open r₁ r₂ :=
    ⟨continuationRepresentativeCenter (U := U) (f := f) r₁, by
      rw [hcenter₁]
      simpa [continuation_lifted_overlap_open, z₁] using hzOverlap⟩
  have hswap :
      ((continuation_overlap_swap (r := r₁) (s := r₂)
          ⟨z₁, hzOverlap⟩ : continuation_overlap_open r₂ r₁) : continuation_chart r₂) = z₂ := by
    apply Subtype.ext
    exact continuation_overlap_swap_val (r := r₁) (s := r₂)
      ⟨z₁, hzOverlap⟩
  have hrel :
      (continuation_glueData (U := U) (f := f)).Rel
        ⟨r₁, continuationRepresentativeCenter (U := U) (f := f) r₁⟩
        ⟨r₂, continuationRepresentativeCenter (U := U) (f := f) r₂⟩ := by
    refine ⟨x, ?_, ?_⟩
    · -- The witness `x` starts at the canonical center of the first representative.
      rfl
    · -- After transporting `x`, its lowered coordinate is unchanged, so it lands at the second
      -- canonical center.
      rw [hcenter₂]
      apply (continuation_chart_space r₂).uliftFunctorObjHomeo.symm.injective
      have hdown :
          (continuation_chart_space r₂).uliftFunctorObjHomeo.symm
              (((continuation_glueData (U := U) (f := f)).f r₂ r₁)
                (((continuation_glueData (U := U) (f := f)).t r₁ r₂) x)) =
            ((continuation_overlap_swap (r := r₁) (s := r₂)
                ⟨z₁, hzOverlap⟩ : continuation_overlap_open r₂ r₁) :
              continuation_chart r₂) := by
        simpa [continuation_glueData, continuation_glueData_core, x, hcenter₁, z₁,
          continuation_lifted_overlap_up, continuation_lifted_overlap_down_up,
          continuation_lifted_overlap_down] using
          congrArg (fun y : continuation_overlap_open r₂ r₁ ↦ (y : continuation_chart r₂))
            (continuation_lifted_transition_lower_eq (U := U) (f := f) (r := r₁) (s := r₂) x)
      simpa [hcenter₂, hswap] using hdown
  -- The gluing relation identifies the two canonical centers, so the comparison points coincide.
  exact (TopCat.GlueData.ι_eq_iff_rel (D := continuation_glueData (U := U) (f := f))
    r₁ r₂
    (continuationRepresentativeCenter (U := U) (f := f) r₁)
    (continuationRepresentativeCenter (U := U) (f := f) r₂)).2 hrel

/-- Helper for Problem VI.5-extra-8: on the image of one glued continuation chart, the descended
projection to `ℂ` is still an open embedding. This is the chart-image normal form used to package
the glued quotient as an unramified surface. -/
lemma continuationGluedProjection_chart_isOpenEmbedding
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    Topology.IsOpenEmbedding
      ((Set.range ((continuation_glueData (U := U) (f := f)).ι r)).restrict
        (continuationGluedProjection (U := U) (f := f))) := by
  let hι :
      Topology.IsOpenEmbedding ((continuation_glueData (U := U) (f := f)).ι r) :=
    TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) r
  let e :
      continuation_lifted_chart_space r ≃ₜ
        Set.range ((continuation_glueData (U := U) (f := f)).ι r) :=
    hι.isEmbedding.toHomeomorph
  have hrewrite :
      ((Set.range ((continuation_glueData (U := U) (f := f)).ι r)).restrict
          (continuationGluedProjection (U := U) (f := f))) =
        continuationLiftedCoordinate (U := U) (f := f) r ∘ e.symm := by
    funext y
    rcases y with ⟨y, ⟨z, rfl⟩⟩
    -- Move a point on the chart image back to its source chart coordinate, then compute the
    -- descended projection on that representative.
    have he :
        e.symm ⟨((continuation_glueData (U := U) (f := f)).ι r) z,
            Set.mem_range_self z⟩ = z := by
      exact hι.isEmbedding.toHomeomorph_symm_apply z
    simpa [Function.comp, he] using
      continuationGluedProjection_apply_ι (U := U) (f := f) r z
  -- Conjugating by the range homeomorphism reduces the restricted projection to the chart
  -- coordinate map proved above.
  rw [hrewrite]
  exact (continuationLiftedCoordinate_isOpenEmbedding (U := U) (f := f) r).comp
    e.symm.isOpenEmbedding

/-- Helper for Problem VI.5-extra-8: the descended projection on the glued continuation quotient
is a local homeomorphism, proved chartwise on the images of the glued chart inclusions. -/
lemma continuationGluedProjection_isLocalHomeomorph
    {U : Set ℂ} {f : ℂ → ℂ} :
    IsLocalHomeomorph (continuationGluedProjection (U := U) (f := f)) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  rcases TopCat.GlueData.ι_jointly_surjective
      (D := continuation_glueData (U := U) (f := f)) x with ⟨r, z, rfl⟩
  let hι :
      Topology.IsOpenEmbedding ((continuation_glueData (U := U) (f := f)).ι r) :=
    TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) r
  -- Use the open image of the chosen glued chart as the local neighborhood witnessing the local
  -- homeomorphism condition.
  refine ⟨Set.range ((continuation_glueData (U := U) (f := f)).ι r), ?_,
    continuationGluedProjection_chart_isOpenEmbedding (U := U) (f := f) r⟩
  simpa using hι.isOpen_range.mem_nhds (Set.mem_range_self z)

/-- Helper for Problem VI.5-extra-8: after moving from a continuation representative `r` to the
same extension evaluated at a nearby local-inverse point, the two local branches still coincide on
the common chart around that coordinate. -/
lemma sameExtensionBranchOverlapAtLocalInverse
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_chart r) :
    let x := (r.1.surface.isLocalHomeomorph.localInverseAt r.2) z
    let r' : ContinuationRepresentative U f := ⟨r.1, x⟩
    ∃ hz' : (z : ℂ) ∈ continuation_chart r',
      (⟨(z : ℂ), ⟨z.2, hz'⟩⟩ : continuation_common_chart r r') ∈
        continuation_branch_overlap r r' := by
  intro x r'
  let e := r.1.surface.isLocalHomeomorph.localInverseAt r.2
  let e' := r.1.surface.isLocalHomeomorph.localInverseAt x
  let S : Set ℂ := (e.trans e'.symm).source
  have hEqOn : Set.EqOn e e' S := by
    intro y hy
    have htrans :
        e.trans e'.symm ≈
          OpenPartialHomeomorph.ofSet S (e.trans e'.symm).open_source := by
      simpa [S, e, e'] using r.1.surface.localInverse_transition_eqOnSource_ofSet r.2 x
    have hyTarget : e y ∈ e'.target := by
      simpa [S, OpenPartialHomeomorph.trans_source] using hy.2
    have hyBack : e'.symm (e y) = y := by
      simpa [S] using htrans.eqOn hy
    -- On the transition source, both local inverses recover the same lift of the base point.
    calc
      e y = e' (e'.symm (e y)) := by rw [e'.right_inv hyTarget]
      _ = e' y := by rw [hyBack]
  have hzS : (z : ℂ) ∈ S := by
    refine ⟨z.2, ?_⟩
    -- The chosen point maps exactly to the new representative center, so it lies in the
    -- transition source between the two local inverses.
    have hxTarget : x ∈ e'.target := by
      exact r.1.surface.isLocalHomeomorph.self_mem_localInverseAt_target (x := x)
    simpa [x] using hxTarget
  have hz' : (z : ℂ) ∈ continuation_chart r' := by
    have hproj : r.1.surface.projection x = (z : ℂ) := by
      simpa [x] using continuation_projection_localInverse (U := U) (f := f) r z
    -- Re-express the new chart center by its base projection.
    simpa [r', hproj] using continuation_projection_mem_chart (U := U) (f := f) r'
  refine ⟨hz', ?_⟩
  let zc : continuation_common_chart r r' := ⟨(z : ℂ), ⟨z.2, hz'⟩⟩
  have hmem : {w : continuation_common_chart r r' | (w : ℂ) ∈ S} ∈ nhds zc := by
    -- The transition source is open and contains the common-chart point.
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((e.trans e'.symm).open_source.mem_nhds hzS)
  have hevent :
      continuation_left_branch r r' =ᶠ[nhds zc] continuation_right_branch r r' := by
    filter_upwards [hmem] with w hw
    -- On that common neighborhood, both branches are the same extension evaluated on the same
    -- lifted point.
    simpa [continuation_left_branch, continuation_right_branch, continuation_branch, e, e', r', x]
      using congrArg r.1.extension (hEqOn hw)
  simpa [continuation_branch_overlap, zc] using hevent

/-- Helper for Problem VI.5-extra-8: on a lifted continuation chart, the canonical comparison map
into the glued quotient is exactly the corresponding glued chart inclusion. -/
lemma continuationComparisonPoint_chartImage_eq
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_lifted_chart_space r) :
    continuationComparisonPoint (U := U) (f := f) r.1
        ((r.1.surface.isLocalHomeomorph.localInverseAt r.2)
          (show continuation_chart r from
            (continuation_chart_space r).uliftFunctorObjHomeo.symm z)) =
      ((continuation_glueData (U := U) (f := f)).ι r) z := by
  let w : continuation_chart r :=
    show continuation_chart r from (continuation_chart_space r).uliftFunctorObjHomeo.symm z
  let x := (r.1.surface.isLocalHomeomorph.localInverseAt r.2) w
  let r' : ContinuationRepresentative U f := ⟨r.1, x⟩
  obtain ⟨hw', hwOverlapRaw⟩ :=
    sameExtensionBranchOverlapAtLocalInverse (U := U) (f := f) r w
  have hwOverlap : (w : continuation_chart r) ∈ continuation_overlap_open r r' := by
    exact (mem_continuation_overlap_open_iff (r := r) (s := r')).2 ⟨hw', hwOverlapRaw⟩
  have hcenter' :
      continuationRepresentativeCenter (U := U) (f := f) r' =
        (continuation_chart_space r').uliftFunctorObjHomeo ⟨(w : ℂ), hw'⟩ := by
    apply (continuation_chart_space r').uliftFunctorObjHomeo.symm.injective
    have hproj : r.1.surface.projection x = (w : ℂ) := by
      simpa [x] using continuation_projection_localInverse (U := U) (f := f) r w
    -- The new representative center is the lifted chart point with the same base coordinate.
    simp [continuationRepresentativeCenter, r', hproj]
  have hrel :
      (continuation_glueData (U := U) (f := f)).Rel
        ⟨r', continuationRepresentativeCenter (U := U) (f := f) r'⟩
        ⟨r, z⟩ := by
    let y : continuation_lifted_overlap_open r' r :=
      ⟨continuationRepresentativeCenter (U := U) (f := f) r', by
        rw [hcenter']
        have hwOverlapSymm :=
          (continuation_overlap_open_symm (r := r) (s := r') hwOverlap).choose_spec
        simpa [continuation_lifted_overlap_open] using hwOverlapSymm⟩
    refine ⟨y, ?_, ?_⟩
    · -- The witness starts from the center of the moved representative.
      rfl
    · apply (continuation_chart_space r).uliftFunctorObjHomeo.symm.injective
      have hwOverlapSymm :=
        (continuation_overlap_open_symm (r := r) (s := r') hwOverlap).choose_spec
      have hswap :
          ((continuation_overlap_swap (r := r') (s := r)
              ⟨⟨(w : ℂ), hw'⟩, hwOverlapSymm⟩ : continuation_overlap_open r r') :
            continuation_chart r) = w := by
        apply Subtype.ext
        simp [continuation_overlap_swap_val]
      have hdown :
          (continuation_chart_space r).uliftFunctorObjHomeo.symm
              (((continuation_glueData (U := U) (f := f)).f r r')
                (((continuation_glueData (U := U) (f := f)).t r' r) y)) = w := by
        -- Lowering the gluing transport lands back at the original chart coordinate.
        simpa [continuation_glueData, continuation_glueData_core, y, hcenter',
          continuation_lifted_overlap_up, continuation_lifted_overlap_down_up,
          continuation_lifted_overlap_down, hswap] using
          congrArg (fun u : continuation_overlap_open r r' ↦ (u : continuation_chart r))
            (continuation_lifted_transition_lower_eq (U := U) (f := f) (r := r') (s := r) y)
      simpa [w] using hdown
  -- Route correction: instead of trying to rewrite the moving representative definitionally, we
  -- compare it to `r` through the same-extension overlap witness above.
  exact (TopCat.GlueData.ι_eq_iff_rel (D := continuation_glueData (U := U) (f := f))
    r' r
    (continuationRepresentativeCenter (U := U) (f := f) r') z).2 hrel

/-- Helper for Problem VI.5-extra-8: on the unlifted continuation chart source, the canonical
comparison map agrees with the glued chart inclusion after the fixed `ULift` transport. -/
lemma continuationComparisonPoint_chart_eq
    {U : Set ℂ} {f : ℂ → ℂ}
    (r : ContinuationRepresentative U f) (z : continuation_chart r) :
    continuationComparisonPoint (U := U) (f := f) r.1
        ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) z) =
      ((continuation_glueData (U := U) (f := f)).ι r)
        ((continuation_chart_space r).uliftFunctorObjHomeo z) := by
  -- Specialize the lifted chart-image identity to the chosen unlifted chart point.
  simpa using
    continuationComparisonPoint_chartImage_eq (U := U) (f := f) r
      ((continuation_chart_space r).uliftFunctorObjHomeo z)

/-- Helper for Problem VI.5-extra-8: every canonical comparison map into the glued quotient is
continuous, because in source charts it is literally a glued chart inclusion. -/
lemma continuationComparisonPoint_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (E : PlaneHolomorphicExtension U f) :
    Continuous (continuationComparisonPoint (U := U) (f := f) E) := by
  rw [continuous_iff_continuousAt]
  intro x
  let r : ContinuationRepresentative U f := ⟨E, x⟩
  let e := E.surface.isLocalHomeomorph.localInverseAt x
  have hsource : E.surface.projection x ∈ continuation_chart r :=
    continuation_projection_mem_chart (U := U) (f := f) r
  have hchartContinuous :
      Continuous (fun y : continuation_chart r ↦
        ((continuation_glueData (U := U) (f := f)).ι r)
          ((continuation_chart_space r).uliftFunctorObjHomeo y)) := by
    let hι : Topology.IsOpenEmbedding ((continuation_glueData (U := U) (f := f)).ι r) :=
      TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) r
    -- In a fixed source chart, the comparison map is just the chart inclusion.
    exact hι.continuous.comp (continuation_chart_space r).uliftFunctorObjHomeo.continuous_toFun
  have hrestrict :
      (continuation_chart r : Set ℂ).restrict
          (fun y : ℂ ↦ continuationComparisonPoint (U := U) (f := f) E (e y)) =
        fun y : continuation_chart r ↦
          ((continuation_glueData (U := U) (f := f)).ι r)
            ((continuation_chart_space r).uliftFunctorObjHomeo y) := by
    funext y
    simpa [r, e] using continuationComparisonPoint_chart_eq (U := U) (f := f) r y
  have hcompWithin :
      ContinuousWithinAt
        (fun y : ℂ ↦ continuationComparisonPoint (U := U) (f := f) E (e y))
        (continuation_chart r) (E.surface.projection x) := by
    rw [continuousWithinAt_iff_continuousAt_restrict _ hsource]
    rw [hrestrict]
    simpa [r] using hchartContinuous.continuousAt
  have hcomp :
      ContinuousAt
        (fun y : ℂ ↦ continuationComparisonPoint (U := U) (f := f) E (e y))
        (E.surface.projection x) :=
    hcompWithin.continuousAt ((continuation_chart_isOpen r).mem_nhds hsource)
  -- Read continuity through the local inverse chart at `x`.
  exact
    ((e.continuousAt_iff_continuousAt_comp_right
      (f := continuationComparisonPoint (U := U) (f := f) E)
      (x := x)
      (E.surface.isLocalHomeomorph.self_mem_localInverseAt_target (x := x))).2 <| by
        simpa [e, r, Function.comp] using hcomp)

/-- Helper for Problem VI.5-extra-8: local inverse branches on unramified surfaces over `ℂ` are
holomorphic because they are inverse preferred charts. -/
lemma unramifiedSurfaceLocalInverseAt_mdifferentiable
    (X : UnramifiedSurfaceOver ℂ) (x : X) :
    (X.isLocalHomeomorph.localInverseAt x).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  -- Replace the raw local inverse by the inverse preferred chart at `x`.
  have hchart :
      chartAt ℂ x = (X.isLocalHomeomorph.localInverseAt x).symm := by
    change
      (X.isLocalHomeomorph.localInverseAt x).symm.trans (chartAt ℂ (X.projection x)) =
        (X.isLocalHomeomorph.localInverseAt x).symm
    simp
  simpa [hchart] using (mdifferentiable_chart (I := 𝓘(ℂ)) (x := x)).symm

/-- Helper for Problem VI.5-extra-8: a continuous map between unramified surfaces over `ℂ` that
commutes with the base projections is holomorphic. In local inverse charts, such a map is
literally the identity on the ambient complex coordinate. -/
lemma mdifferentiable_of_projection_commutes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (SX : UnramifiedSurfaceOver ℂ) (SY : UnramifiedSurfaceOver ℂ)
    (h : SX → SY) (hcont : Continuous h)
    (hcomm : ∀ x : SX, SY.projection (h x) = SX.projection x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
  intro x
  let ey := SY.isLocalHomeomorph.localInverseAt (h x)
  have hsource :
      SX.projection x ∈ ey.source := by
    simpa [ey, hcomm x, SY.isLocalHomeomorph.localInverseAt_symm (x := h x)] using
      SY.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := h x)
  have hmodel :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x' : SX ↦ ey (SX.projection x')) x := by
    -- In a fixed target chart, the comparison map is `localInverseAt (h x) ∘ projection`.
    exact
      ((unramifiedSurfaceLocalInverseAt_mdifferentiable SY (h x)).mdifferentiableAt hsource).comp
        x (UnramifiedSurfaceOver.mdifferentiable_projection SX x)
  have hevent :
      h =ᶠ[nhds x] fun x' : SX ↦ ey (SX.projection x') := by
    -- Near `x`, continuity keeps `h x'` inside the target chart of `localInverseAt (h x)`, where
    -- the projection-commuting hypothesis identifies `h x'` with that local inverse branch.
    have htarget :
        ey.target ∈ nhds (h x) := ey.open_target.mem_nhds <|
          SY.isLocalHomeomorph.self_mem_localInverseAt_target (x := h x)
    filter_upwards [hcont.continuousAt.preimage_mem_nhds htarget] with x' hx'
    calc
      h x' = ey (SY.projection (h x')) := by
        simpa
          [ey, SY.isLocalHomeomorph.localInverseAt_symm (x := h x)]
          using (ey.right_inv hx').symm
      _ = ey (SX.projection x') := by rw [hcomm x']
  -- Read `h` through the fixed local target chart and use the eventual equality above.
  exact hmodel.congr_of_eventuallyEq hevent

/-- Helper for Problem VI.5-extra-8: a morphism of unramified surfaces over `ℂ` is continuous
because holomorphic maps between manifolds are continuous. -/
lemma ConnectedHausdorffUnramifiedSurfaceOver.Hom.continuous_toFun
    {X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ}
    (h : ConnectedHausdorffUnramifiedSurfaceOver.Hom X Y) :
    Continuous h :=
  h.holomorphic_toFun.continuous

/-- Helper for Problem VI.5-extra-8: two continuous lifts of the same base projection into an
unramified surface must agree on a neighborhood of any common point. -/
lemma eventuallyEq_of_projection_commutes
    {X : Type*} [TopologicalSpace X]
    {Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ}
    (π : X → ℂ) (h₁ h₂ : X → Y)
    (h₁cont : Continuous h₁) (h₂cont : Continuous h₂)
    (h₁comm : ∀ x : X, Y.projection (h₁ x) = π x)
    (h₂comm : ∀ x : X, Y.projection (h₂ x) = π x)
    {x : X} (hx : h₁ x = h₂ x) :
    h₁ =ᶠ[nhds x] h₂ := by
  let y := h₁ x
  let ey := Y.isLocalHomeomorph.localInverseAt y
  have hyTarget : ey.target ∈ nhds y := by
    exact ey.open_target.mem_nhds <|
      Y.isLocalHomeomorph.self_mem_localInverseAt_target (x := y)
  have h₁near : ∀ᶠ x' in nhds x, h₁ x' ∈ ey.target := by
    exact h₁cont.continuousAt.preimage_mem_nhds hyTarget
  have h₂near : ∀ᶠ x' in nhds x, h₂ x' ∈ ey.target := by
    have hyTarget' : ey.target ∈ nhds (h₂ x) := by
      simpa [y, hx] using hyTarget
    exact h₂cont.continuousAt.preimage_mem_nhds hyTarget'
  filter_upwards [h₁near, h₂near] with x' hx₁ hx₂
  calc
    h₁ x' = ey (Y.projection (h₁ x')) := by
      simpa [ey, Y.isLocalHomeomorph.localInverseAt_symm (x := y)] using (ey.right_inv hx₁).symm
    _ = ey (π x') := by rw [h₁comm x']
    _ = Y.isLocalHomeomorph.localInverseAt y (Y.projection (h₂ x')) := by rw [h₂comm x']
    _ = h₂ x' := by
      simpa [ey, Y.isLocalHomeomorph.localInverseAt_symm (x := y)] using ey.right_inv hx₂

/-- Helper for Problem VI.5-extra-8: two morphisms of connected Hausdorff unramified surfaces over
`ℂ` that agree at one point agree everywhere. -/
lemma ConnectedHausdorffUnramifiedSurfaceOver.Hom.eq_of_eq_at_point
    {X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ}
    (h₁ h₂ : ConnectedHausdorffUnramifiedSurfaceOver.Hom X Y)
    {x : X} (hx : h₁ x = h₂ x) :
    h₁ = h₂ := by
  let s : Set X := {x | h₁ x = h₂ x}
  have hsOpen : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro x hx'
    simpa [s] using
      eventuallyEq_of_projection_commutes
        (π := X.projection) h₁ h₂ h₁.continuous_toFun h₂.continuous_toFun
        h₁.commutes h₂.commutes hx'
  have hsClosed : IsClosed s := by
    simpa [s] using isClosed_eq h₁.continuous_toFun h₂.continuous_toFun
  have hsUniv : s = Set.univ := by
    exact IsClopen.eq_univ ⟨hsClosed, hsOpen⟩ ⟨x, hx⟩
  have hpoint : ∀ x' : X, h₁ x' = h₂ x' := by
    intro x'
    have hx' : x' ∈ s := by simp [hsUniv]
    exact hx'
  cases h₁ with
  | mk f₁ hol₁ comm₁ =>
      cases h₂ with
      | mk f₂ hol₂ comm₂ =>
          simp only at hpoint
          have hfun : f₁ = f₂ := funext hpoint
          cases hfun
          have hhol : hol₁ = hol₂ := Subsingleton.elim _ _
          have hcomm : comm₁ = comm₂ := Subsingleton.elim _ _
          cases hhol
          cases hcomm
          rfl

/-- Helper for Problem VI.5-extra-8: equal ambient coordinates place the left chart point in the
right continuation chart as well. -/
lemma continuationCommonChartOfEq_mem_right
    {U : Set ℂ} {f : ℂ → ℂ}
    {r s : ContinuationRepresentative U f}
    (z : continuation_chart r) (w : continuation_chart s) (hzw : (z : ℂ) = (w : ℂ)) :
    (z : ℂ) ∈ continuation_chart s := by
  rw [hzw]
  exact w.2

/-- Helper for Problem VI.5-extra-8: the common-chart point determined by two chart points with
the same ambient coordinate. -/
def continuationCommonChartOfEq
    {U : Set ℂ} {f : ℂ → ℂ}
    {r s : ContinuationRepresentative U f}
    (z : continuation_chart r) (w : continuation_chart s) (hzw : (z : ℂ) = (w : ℂ)) :
    continuation_common_chart r s :=
  ⟨(z : ℂ), ⟨z.2, continuationCommonChartOfEq_mem_right z w hzw⟩⟩

/-- Helper for Problem VI.5-extra-8: two glued chart points with the same ambient coordinate are
identified exactly when the corresponding common-chart point lies in the branch-overlap locus. -/
lemma continuationGlued_eq_iff_branch_overlap
    {U : Set ℂ} {f : ℂ → ℂ}
    {r s : ContinuationRepresentative U f}
    (z : continuation_chart r) (w : continuation_chart s) (hzw : (z : ℂ) = (w : ℂ)) :
    ((continuation_glueData (U := U) (f := f)).ι r)
        ((continuation_chart_space r).uliftFunctorObjHomeo z) =
      ((continuation_glueData (U := U) (f := f)).ι s)
        ((continuation_chart_space s).uliftFunctorObjHomeo w) ↔
      continuationCommonChartOfEq z w hzw ∈
        continuation_branch_overlap r s := by
  constructor
  · intro hEq
    rw [TopCat.GlueData.ι_eq_iff_rel (D := continuation_glueData (U := U) (f := f))] at hEq
    rcases hEq with ⟨x, hxleft, _hxright⟩
    let hx : continuation_lifted_overlap_open (U := U) (f := f) r s := by
      simpa [continuation_glueData, continuation_glueData_core] using x
    have hxz :
        (hx : continuation_lifted_chart_space r) =
          (continuation_chart_space r).uliftFunctorObjHomeo z := by
      simpa [hx, continuation_glueData, continuation_glueData_core] using hxleft
    let hxdown : continuation_overlap_open r s :=
      continuation_lifted_overlap_down (r := r) (s := s) hx
    have hxdownz : (hxdown : continuation_chart r) = z := by
      simpa [hxdown, continuation_lifted_overlap_down] using
        congrArg (fun y : continuation_lifted_chart_space r ↦
          (continuation_chart_space r).uliftFunctorObjHomeo.symm y) hxz
    have hzOverlap : z ∈ continuation_overlap_open r s := by
      simpa [hxdownz] using hxdown.2
    rcases (mem_continuation_overlap_open_iff (r := r) (s := s) (z := z)).1 hzOverlap with
      ⟨hzs, hzbranch⟩
    have hcommon :
        (⟨(z : ℂ), ⟨z.2, hzs⟩⟩ : continuation_common_chart r s) =
          continuationCommonChartOfEq z w hzw := by
      apply Subtype.ext
      rfl
    simpa [hcommon] using hzbranch
  · intro hzbranch
    have hzOverlap : z ∈ continuation_overlap_open r s := by
      refine (mem_continuation_overlap_open_iff (r := r) (s := s) (z := z)).2 ?_
      exact ⟨continuationCommonChartOfEq_mem_right z w hzw, hzbranch⟩
    let x0 : continuation_overlap_open r s := ⟨z, hzOverlap⟩
    let x : continuation_lifted_overlap_open r s :=
      continuation_lifted_overlap_up (r := r) (s := s) x0
    rw [TopCat.GlueData.ι_eq_iff_rel (D := continuation_glueData (U := U) (f := f))]
    refine ⟨x, ?_, ?_⟩
    · -- The lifted witness starts at the chosen left chart point.
      rfl
    · -- Lower the lifted transition, then identify the transported right chart point by its
      -- ambient complex coordinate.
      apply (continuation_chart_space s).uliftFunctorObjHomeo.symm.injective
      have hdown :
          (continuation_chart_space s).uliftFunctorObjHomeo.symm
              (((continuation_glueData (U := U) (f := f)).f s r)
                (((continuation_glueData (U := U) (f := f)).t r s) x)) =
            ((continuation_overlap_swap (r := r) (s := s) x0 :
                continuation_overlap_open s r) : continuation_chart s) := by
        simpa [x, x0, continuation_glueData, continuation_glueData_core,
          continuation_lifted_overlap_up, continuation_lifted_overlap_down,
          continuation_lifted_overlap_down_up] using
          congrArg (fun y : continuation_overlap_open s r ↦ (y : continuation_chart s))
            (continuation_lifted_transition_lower_eq (r := r) (s := s) x)
      have hswap :
          ((continuation_overlap_swap (r := r) (s := s) x0 :
              continuation_overlap_open s r) : continuation_chart s) = w := by
        apply Subtype.ext
        simpa [x0, hzw] using continuation_overlap_swap_val (r := r) (s := s) x0
      simpa [hswap] using hdown

/-- Helper for Problem VI.5-extra-8: two glued chart points with the same ambient coordinate but
different glued images can be separated by open neighborhoods coming from the complement of the
branch-overlap locus in the common chart. -/
lemma continuationGluedSeparatedOfSameCoordinate
    {U : Set ℂ} {f : ℂ → ℂ}
    {r s : ContinuationRepresentative U f}
    (z : continuation_chart r) (w : continuation_chart s) (hzw : (z : ℂ) = (w : ℂ))
    (hneq :
      ((continuation_glueData (U := U) (f := f)).ι r)
          ((continuation_chart_space r).uliftFunctorObjHomeo z) ≠
        ((continuation_glueData (U := U) (f := f)).ι s)
          ((continuation_chart_space s).uliftFunctorObjHomeo w)) :
    ∃ u v : Set ((continuation_glueData (U := U) (f := f)).glued),
      IsOpen u ∧ IsOpen v ∧
        ((continuation_glueData (U := U) (f := f)).ι r)
            ((continuation_chart_space r).uliftFunctorObjHomeo z) ∈ u ∧
          ((continuation_glueData (U := U) (f := f)).ι s)
              ((continuation_chart_space s).uliftFunctorObjHomeo w) ∈ v ∧
            Disjoint u v := by
  let c : continuation_common_chart r s := continuationCommonChartOfEq z w hzw
  let leftInc :
      continuation_common_chart r s → continuation_chart r :=
    TopologicalSpace.Opens.inclusion
      (show continuation_common_chart r s ≤ continuation_chart r from inf_le_left)
  let rightInc :
      continuation_common_chart r s → continuation_chart s :=
    TopologicalSpace.Opens.inclusion
      (show continuation_common_chart r s ≤ continuation_chart s from inf_le_right)
  have hleftInc :
      Topology.IsOpenEmbedding leftInc :=
    continuation_common_chart_left_inclusion_isOpenEmbedding (r := r) (s := s)
  have hrightInc :
      Topology.IsOpenEmbedding rightInc := by
    refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
    · exact continuous_inclusion
        (show (continuation_common_chart r s : Set ℂ) ⊆ continuation_chart s from inf_le_right)
    · intro x y hxy
      exact Subtype.ext (congrArg (fun u : continuation_chart s ↦ (u : ℂ)) hxy)
    · exact IsOpen.isOpenMap_inclusion (continuation_common_chart r s).2
        (show (continuation_common_chart r s : Set ℂ) ⊆ continuation_chart s from inf_le_right)
  let leftMap : continuation_common_chart r s →
      (continuation_glueData (U := U) (f := f)).glued :=
    fun u ↦
      ((continuation_glueData (U := U) (f := f)).ι r)
        ((continuation_chart_space r).uliftFunctorObjHomeo (leftInc u))
  let rightMap : continuation_common_chart r s →
      (continuation_glueData (U := U) (f := f)).glued :=
    fun u ↦
      ((continuation_glueData (U := U) (f := f)).ι s)
        ((continuation_chart_space s).uliftFunctorObjHomeo (rightInc u))
  have hleftMap :
      Topology.IsOpenEmbedding leftMap := by
    exact
      (TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) r).comp
        ((continuation_chart_space r).uliftFunctorObjHomeo.isOpenEmbedding.comp hleftInc)
  have hrightMap :
      Topology.IsOpenEmbedding rightMap := by
    exact
      (TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) s).comp
        ((continuation_chart_space s).uliftFunctorObjHomeo.isOpenEmbedding.comp hrightInc)
  let o : Set (continuation_common_chart r s) := (continuation_branch_overlap r s)ᶜ
  have ho : IsOpen o := (continuation_branch_overlap_isClosed r s).isOpen_compl
  have hcnot : c ∉ continuation_branch_overlap r s := by
    intro hc
    exact hneq <| (continuationGlued_eq_iff_branch_overlap (U := U) (f := f) z w hzw).2 hc
  have hc : c ∈ o := hcnot
  let u : Set ((continuation_glueData (U := U) (f := f)).glued) := leftMap '' o
  let v : Set ((continuation_glueData (U := U) (f := f)).glued) := rightMap '' o
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · -- The left neighborhood is the open image of the complement of the overlap locus.
    simpa [u] using hleftMap.isOpenMap _ ho
  · -- The right neighborhood is constructed symmetrically.
    simpa [v] using hrightMap.isOpenMap _ ho
  · -- The chosen common-chart point lands at the left glued point.
    exact Set.mem_image_of_mem _ hc
  · -- The same common-chart point lands at the right glued point.
    have hrightc : rightInc c = w := by
      apply Subtype.ext
      exact hzw
    simpa [v, rightMap, c, hrightc] using (Set.mem_image_of_mem rightMap hc)
  · -- Any point in both images would force a common-chart point back into the overlap locus.
    refine Set.disjoint_left.2 ?_
    intro q hqu hqv
    rcases hqu with ⟨u0, hu0, rfl⟩
    rcases hqv with ⟨v0, hv0, hEq⟩
    have huProj :
        continuationGluedProjection (U := U) (f := f) (leftMap u0) = (u0 : ℂ) := by
      simp [leftMap, leftInc, continuationGluedProjection_apply_ι, continuationLiftedCoordinate]
    have hvProj :
        continuationGluedProjection (U := U) (f := f) (rightMap v0) = (v0 : ℂ) := by
      simp [rightMap, rightInc, continuationGluedProjection_apply_ι, continuationLiftedCoordinate]
    have huvCoord : (u0 : ℂ) = (v0 : ℂ) := by
      calc
        (u0 : ℂ) = continuationGluedProjection (U := U) (f := f) (leftMap u0) := huProj.symm
        _ = continuationGluedProjection (U := U) (f := f) (rightMap v0) := congrArg
          (continuationGluedProjection (U := U) (f := f)) hEq.symm
        _ = (v0 : ℂ) := hvProj
    have huv : u0 = v0 := by
      apply Subtype.ext
      exact huvCoord
    have hEq' : leftMap u0 = rightMap u0 := by
      simpa [huv] using hEq.symm
    have huBranch : u0 ∈ continuation_branch_overlap r s := by
      exact
        (continuationGlued_eq_iff_branch_overlap (U := U) (f := f)
          ⟨(u0 : ℂ), u0.2.1⟩ ⟨(u0 : ℂ), u0.2.2⟩ rfl).1 <| by
            simpa [leftMap, rightMap, leftInc, rightInc] using hEq'
    exact hu0 huBranch

/-- Helper for Problem VI.5-extra-8: the glued continuation quotient is Hausdorff. Distinct
points are either separated by the projection to `ℂ`, or, if they lie over the same base point,
by the open complement of the branch-overlap locus in a common chart. -/
lemma continuationGlued_t2Space
    {U : Set ℂ} {f : ℂ → ℂ} :
    T2Space ((continuation_glueData (U := U) (f := f)).glued) := by
  have hcont :
      Continuous (continuationGluedProjection (U := U) (f := f)) := by
    -- The descended `ULift`-valued projection is a `TopCat` morphism; forget the lift with the
    -- continuous map `ULift.down`.
    simpa [continuationGluedProjection, continuationGluedProjectionUp] using
      continuous_uliftDown.comp
        (continuationGluedProjectionUpHom (U := U) (f := f)).hom.continuous_toFun
  refine ⟨?_⟩
  intro x y hxy
  rcases TopCat.GlueData.ι_jointly_surjective
      (D := continuation_glueData (U := U) (f := f)) x with ⟨r, z, rfl⟩
  rcases TopCat.GlueData.ι_jointly_surjective
      (D := continuation_glueData (U := U) (f := f)) y with ⟨s, w, rfl⟩
  let zr : continuation_chart r := (continuation_chart_space r).uliftFunctorObjHomeo.symm z
  let ws : continuation_chart s := (continuation_chart_space s).uliftFunctorObjHomeo.symm w
  by_cases hproj :
      continuationGluedProjection (U := U) (f := f)
          (((continuation_glueData (U := U) (f := f)).ι r) z) =
        continuationGluedProjection (U := U) (f := f)
          (((continuation_glueData (U := U) (f := f)).ι s) w)
  · -- Over a fixed base coordinate, use the complement of the branch-overlap locus.
    have hzw : (zr : ℂ) = (ws : ℂ) := by
      simpa [zr, ws, continuationGluedProjection_apply_ι, continuationLiftedCoordinate] using hproj
    simpa [zr, ws] using
      continuationGluedSeparatedOfSameCoordinate (U := U) (f := f) zr ws hzw hxy
  · -- Different base coordinates are separated by the continuous descended projection.
    exact separated_by_continuous hcont hproj

/-- Helper for Problem VI.5-extra-8: the glued continuation quotient is connected because it is
the union of the connected ranges of the canonical comparison maps from all extensions, and these
ranges all meet the common embedded base point coming from `U`. -/
lemma continuationGlued_connectedSpace
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ConnectedSpace ((continuation_glueData (U := U) (f := f)).glued) := by
  letI : ConnectedSpace U := Subtype.connectedSpace ⟨hU_nonempty, hU_connected⟩
  let E₀ : PlaneHolomorphicExtension U f := tautological_extension hU_open hf
  let z0 : U := ⟨hU_nonempty.choose, hU_nonempty.choose_spec⟩
  let p0 := continuationComparisonPoint (U := U) (f := f) E₀ z0
  rw [connectedSpace_iff_univ]
  refine ⟨⟨p0, trivial⟩, ?_⟩
  have hinter :
      (⋂ E : PlaneHolomorphicExtension U f,
        Set.range (continuationComparisonPoint (U := U) (f := f) E)).Nonempty := by
    refine ⟨p0, ?_⟩
    simp only [Set.mem_iInter]
    intro E
    refine Set.mem_range.2 ⟨E.embedding z0, ?_⟩
    -- Every comparison-map range contains the same embedded base point from `U`.
    simpa [p0] using
      (continuationComparisonPoint_embedding_eq (U := U) (f := f) hU_open E₀ E z0).symm
  have hpre :
      ∀ E : PlaneHolomorphicExtension U f,
        IsPreconnected (Set.range (continuationComparisonPoint (U := U) (f := f) E)) := by
    intro E
    exact isPreconnected_range (continuationComparisonPoint_continuous (U := U) (f := f) E)
  have hunion :
      (⋃ E : PlaneHolomorphicExtension U f,
        Set.range (continuationComparisonPoint (U := U) (f := f) E)) = Set.univ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rcases TopCat.GlueData.ι_jointly_surjective
          (D := continuation_glueData (U := U) (f := f)) x with ⟨r, z, rfl⟩
      refine Set.mem_iUnion.2 ⟨r.1, ?_⟩
      refine Set.mem_range.2 ⟨(r.1.surface.isLocalHomeomorph.localInverseAt r.2)
        (show continuation_chart r from (continuation_chart_space r).uliftFunctorObjHomeo.symm z),
        ?_⟩
      -- Every glued point lies in the range of the comparison map from its chosen representative.
      exact continuationComparisonPoint_chartImage_eq (U := U) (f := f) r z
  simpa [hunion] using isPreconnected_iUnion hinter hpre

/-- Cartan section26 0008_Problem_VI_5_extra_8: Problem VI.5-extra-8 shows that every
holomorphic function on a nonempty connected open set `U ⊆ ℂ` admits a
maximal extension to an unramified surface over `ℂ`, in the sense of the universal property
described in (i), (ii), and (iii). -/
theorem exists_maximal_unramified_surface_extension
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ E : PlaneHolomorphicExtension.{1} U f, E.IsMaximal := by
  letI : ConnectedSpace U := Subtype.connectedSpace ⟨hU_nonempty, hU_connected⟩
  have hbase : Nonempty (PlaneHolomorphicExtension.{0} U f) :=
    plane_holomorphic_extension_nonempty hU_open hU_nonempty hU_connected hf
  let E₀ : PlaneHolomorphicExtension.{0} U f := tautological_extension hU_open hf
  -- The verified prefix is the tautological extension on `U`.
  -- Route correction: the raw chart-by-chart gluing work is now condensed into the descended
  -- projection/value maps on `continuation_glueData.glued`, together with the canonical pointwise
  -- comparison map from every extension into that quotient.
  have hprojectionOnU :
      ∀ z : U,
        continuationGluedProjection (U := U) (f := f)
            (continuationComparisonPoint (U := U) (f := f) E₀ z) = z := by
    -- The tautological comparison preserves the base projection exactly.
    intro z
    simpa [E₀, tautological_extension] using
      continuationComparisonPoint_projection (U := U) (f := f) E₀ z
  have hextensionOnU :
      ∀ z : U,
        continuationGluedExtension (U := U) (f := f)
            (continuationComparisonPoint (U := U) (f := f) E₀ z) = f z := by
    -- The tautological comparison also preserves the extended holomorphic value.
    intro z
    simpa [E₀, tautological_extension] using
      continuationComparisonPoint_extension (U := U) (f := f) E₀ z
  have hgluedProjectionLocalHomeomorph :
      IsLocalHomeomorph (continuationGluedProjection (U := U) (f := f)) :=
    continuationGluedProjection_isLocalHomeomorph (U := U) (f := f)
  have hgluedConnected :
      ConnectedSpace ((continuation_glueData (U := U) (f := f)).glued) :=
    continuationGlued_connectedSpace (U := U) hU_open hU_nonempty hU_connected hf
  have hgluedT2 :
      T2Space ((continuation_glueData (U := U) (f := f)).glued) :=
    continuationGlued_t2Space (U := U) (f := f)
  letI : ConnectedSpace ((continuation_glueData (U := U) (f := f)).glued) := hgluedConnected
  letI : T2Space ((continuation_glueData (U := U) (f := f)).glued) := hgluedT2
  let Xg : ConnectedHausdorffUnramifiedSurfaceOver ℂ :=
    ConnectedHausdorffUnramifiedSurfaceOver.ofIsLocalHomeomorph
      (X := ((continuation_glueData (U := U) (f := f)).glued))
      (continuationGluedProjection (U := U) (f := f))
      hgluedProjectionLocalHomeomorph
  letI : ChartedSpace ℂ Xg := inferInstance
  letI : IsManifold 𝓘(ℂ) 1 Xg := inferInstance
  have hgluedExtensionContinuous :
      Continuous (continuationGluedExtension (U := U) (f := f)) := by
    -- The descended extension-value map is a `TopCat` morphism; forget the `ULift` target as in
    -- the projection continuity proof above.
    simpa [continuationGluedExtension, continuationGluedExtensionUp] using
      continuous_uliftDown.comp
        (continuationGluedExtensionUpHom (U := U) (f := f)).hom.continuous_toFun
  have hcomparisonEmbedding :
      Topology.IsOpenEmbedding
        (continuationComparisonPoint (U := U) (f := f) E₀) := by
    -- The tautological comparison on `U` is a continuous local section of the glued projection.
    have hcomp :
        continuationGluedProjection (U := U) (f := f) ∘
            continuationComparisonPoint (U := U) (f := f) E₀ =
          Subtype.val := by
      funext z
      exact hprojectionOnU z
    refine IsLocalHomeomorph.isOpenEmbedding_of_comp hgluedProjectionLocalHomeomorph ?_
      (continuationComparisonPoint_continuous (U := U) (f := f) E₀)
    simpa [hcomp] using hU_open.isOpenEmbedding_subtypeVal
  have hmaximal :
      ∃ E : PlaneHolomorphicExtension.{1} U f, E.IsMaximal := by
    have hgluedExtension_mdifferentiableAt_chartImage :
        ∀ (r : ContinuationRepresentative U f) {x : Xg},
          x ∈ Set.range ((continuation_glueData (U := U) (f := f)).ι r) →
            MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
              (fun y : Xg ↦ continuationGluedExtension (U := U) (f := f) y) x := by
      intro r x hx
      rcases hx with ⟨z, rfl⟩
      let x0 : Xg := ((continuation_glueData (U := U) (f := f)).ι r) z
      let model : Xg → ℂ := fun y ↦
        r.1.extension ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) (Xg.projection y))
      have hmodel :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) model x0 := by
        let w : continuation_chart r :=
          show continuation_chart r from (continuation_chart_space r).uliftFunctorObjHomeo.symm z
        have hsource :
            Xg.projection x0 ∈
              (r.1.surface.isLocalHomeomorph.localInverseAt r.2).source := by
          -- The chosen glued chart image lies inside the source of the representative's local
          -- inverse branch.
          have hproj : Xg.projection x0 = (w : ℂ) := by
            simpa [Xg, w, continuationLiftedCoordinate] using
              continuationGluedProjection_apply_ι (U := U) (f := f) r z
          rw [hproj]
          exact w.2
        have hmodelLift :
            MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
              (fun y : Xg ↦
                (r.1.surface.isLocalHomeomorph.localInverseAt r.2) (Xg.projection y))
              x0 := by
          have hprojection :
              MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Xg.projection x0 :=
            ConnectedHausdorffUnramifiedSurfaceOver.mdifferentiable_projection Xg x0
          have hlocalInverse :
              MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
                (r.1.surface.isLocalHomeomorph.localInverseAt r.2)
                (Xg.projection x0) :=
            (continuation_localInverseAt_mdifferentiable (U := U) (f := f) r).mdifferentiableAt
              hsource
          -- In source coordinates, the model is just the representative's local inverse branch
          -- after the glued projection.
          exact hlocalInverse.comp x0 hprojection
        -- Postcompose the local lifted point with the already holomorphic extension on `r.1`.
        have hmodelValue :
            MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
              (r.1.extension ∘ fun y : Xg ↦
                (r.1.surface.isLocalHomeomorph.localInverseAt r.2) (Xg.projection y))
              x0 := by
          have hExtension :
              MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) r.1.extension
                ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) (Xg.projection x0)) :=
            r.1.holomorphic_extension
              ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) (Xg.projection x0))
          exact hExtension.comp x0 hmodelLift
        simpa [model, Function.comp] using hmodelValue
      have hchartNhds :
          Set.range ((continuation_glueData (U := U) (f := f)).ι r) ∈
            nhds x0 := by
        let hι :
            Topology.IsOpenEmbedding ((continuation_glueData (U := U) (f := f)).ι r) :=
          TopCat.GlueData.ι_isOpenEmbedding (D := continuation_glueData (U := U) (f := f)) r
        -- The glued chart image is an open neighborhood of the chosen point.
        simpa using hι.isOpen_range.mem_nhds (Set.mem_range_self z)
      have hevent :
          (fun y : Xg ↦ continuationGluedExtension (U := U) (f := f) y) =ᶠ[
              nhds x0]
            model := by
        filter_upwards [hchartNhds] with y hy
        rcases hy with ⟨w, rfl⟩
        let w0 : continuation_chart r :=
          show continuation_chart r from (continuation_chart_space r).uliftFunctorObjHomeo.symm w
        have hproj :
            Xg.projection (((continuation_glueData (U := U) (f := f)).ι r) w) =
              (w0 : ℂ) := by
          simpa [Xg, w0, continuationLiftedCoordinate] using
            continuationGluedProjection_apply_ι (U := U) (f := f) r w
        -- On one fixed glued chart image, the descended extension is exactly the original
        -- extension composed with the representative's local inverse branch.
        calc
          continuationGluedExtension (U := U) (f := f)
              (((continuation_glueData (U := U) (f := f)).ι r) w) =
            continuationLiftedBranch (U := U) (f := f) r w := by
              simpa using continuationGluedExtension_apply_ι (U := U) (f := f) r w
          _ =
              r.1.extension
                ((r.1.surface.isLocalHomeomorph.localInverseAt r.2)
                  (Xg.projection (((continuation_glueData (U := U) (f := f)).ι r) w))) := by
              simp [continuationLiftedBranch, continuation_branch, w0, hproj]
          _ = model (((continuation_glueData (U := U) (f := f)).ι r) w) := by
              rfl
      -- Replace the descended extension by the explicit local model on the chart image.
      exact hmodel.congr_of_eventuallyEq hevent
    have hgluedExtensionHolomorphic :
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
          (fun x : Xg ↦ continuationGluedExtension (U := U) (f := f) x) := by
      intro x
      rcases TopCat.GlueData.ι_jointly_surjective
          (D := continuation_glueData (U := U) (f := f)) x with ⟨r, z, rfl⟩
      -- The glued charts cover `Xg`, so the chart-image local holomorphicity lemma applies at
      -- every point.
      exact hgluedExtension_mdifferentiableAt_chartImage r (Set.mem_range_self z)
    let Eg : PlaneHolomorphicExtension.{1} U f := {
      surface := Xg
      embedding := continuationComparisonPoint (U := U) (f := f) E₀
      isOpenEmbedding_embedding := hcomparisonEmbedding
      projection_comp_embedding := hprojectionOnU
      extension := continuationGluedExtension (U := U) (f := f)
      holomorphic_extension := hgluedExtensionHolomorphic
      extension_comp_embedding := hextensionOnU
    }
    refine ⟨Eg, ?_⟩
    intro E'
    let hcomparison : ConnectedHausdorffUnramifiedSurfaceOver.Hom E'.surface Eg.surface := {
      toFun := continuationComparisonPoint (U := U) (f := f) E'
      holomorphic_toFun := by
        simpa using
          (@mdifferentiable_of_projection_commutes
            E'.surface Eg.surface inferInstance inferInstance
            E'.surface.toUnramifiedSurfaceOver Eg.surface.toUnramifiedSurfaceOver
            (continuationComparisonPoint (U := U) (f := f) E' :
              E'.surface.toUnramifiedSurfaceOver → Eg.surface.toUnramifiedSurfaceOver)
            (continuationComparisonPoint_continuous (U := U) (f := f) E' :
              Continuous (continuationComparisonPoint (U := U) (f := f) E'))
            (continuationComparisonPoint_projection (U := U) (f := f) E'))
      commutes := continuationComparisonPoint_projection (U := U) (f := f) E'
    }
    have hcompatible : PlaneHolomorphicExtension.Compatible E' Eg hcomparison := by
      constructor
      · intro z
        -- The canonical comparison maps all agree on the embedded base copy of `U`.
        simpa [Eg, E₀] using
          (continuationComparisonPoint_embedding_eq (U := U) (f := f) hU_open E₀ E' z).symm
      · intro x
        -- The comparison map also preserves the extended holomorphic value by construction.
        simpa [Eg] using continuationComparisonPoint_extension (U := U) (f := f) E' x
    refine ⟨hcomparison, hcompatible, ?_⟩
    intro h hh
    let z0 : U := ⟨hU_nonempty.choose, hU_nonempty.choose_spec⟩
    -- Any other compatible morphism agrees with the canonical one at the embedded base point, so
    -- the connectedness rigidity lemma upgrades that pointwise agreement to global equality.
    apply ConnectedHausdorffUnramifiedSurfaceOver.Hom.eq_of_eq_at_point h hcomparison
    calc
      h (E'.embedding z0) = Eg.embedding z0 := (hh.1 z0)
      _ = hcomparison (E'.embedding z0) := by
        simpa [Eg, E₀, hcomparison] using
          continuationComparisonPoint_embedding_eq (U := U) (f := f) hU_open E₀ E' z0
  exact hmaximal
