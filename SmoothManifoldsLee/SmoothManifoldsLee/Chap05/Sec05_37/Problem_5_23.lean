import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifoldsLee.Chap01.Sec01_05.Definition_1_5_extra_1
import SmoothManifoldsLee.Chap05.Sec05_30.Definition_5_30_extra_3
import SmoothManifoldsLee.Chap05.Sec05_30.Corollary_5_13
import SmoothManifoldsLee.Chap05.Sec05_35.Corollary_5_39
import SmoothManifoldsLee.Chap05.Sec05_36.Theorem_5_51
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_3
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_4
import SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold

noncomputable section

namespace Manifold

universe uE uE' uEB uH uH' uHB uM uN

section RegularValue

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}

/-- A point `c` is a regular value of the boundary restriction `F|_{∂M}` when the derivative of
`F` along the boundary subset is surjective at every boundary point of the fiber `F⁻¹({c})`. This
is the intrinsic boundary-restriction form of Lee's boundary regular-value hypothesis; a smooth
boundary structure on `↥(I.boundary M)` turns it into the usual regular-value statement for the
subtype restriction. -/
def IsBoundaryRegularValue (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (F : M → N) (c : N) : Prop :=
  ∀ x : M, x ∈ I.boundary M → F x = c →
    Function.Surjective (mfderivWithin I J F (I.boundary M) x)

/-- A boundary regular value is characterized by surjectivity of the derivative of `F` within the
boundary along the boundary fiber. -/
theorem isBoundaryRegularValue_iff (F : M → N) (c : N) :
    IsBoundaryRegularValue I J F c ↔
      ∀ x : M, x ∈ I.boundary M → F x = c →
        Function.Surjective (mfderivWithin I J F (I.boundary M) x) :=
  Iff.rfl

section BoundaryRestriction

variable {EB : Type uEB} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
variable {HB : Type uHB} [TopologicalSpace HB]
variable {IB : ModelWithCorners ℝ EB HB}
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [IsManifold J (⊤ : WithTop ℕ∞) N]
variable [ChartedSpace HB ↥(I.boundary M)]
variable [IsManifold IB (⊤ : WithTop ℕ∞) ↥(I.boundary M)]

/-- Helper for Problem 5-23: the chosen boundary inclusion is smooth in the supplied boundary
manifold structure because the immersion normal form writes it as the linear inclusion
`u ↦ (u, 0)` in suitable charts. -/
theorem contMDiff_boundary_inclusion
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M)) :
    ContMDiff IB I ∞ (Subtype.val : ↥(I.boundary M) → M) := by
  -- First establish `C^∞` smoothness at the top differentiability level using the immersion
  -- normal form, then lower back to the requested `∞` degree.
  have hBoundarySmoothTop :
      ContMDiff IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) := by
    -- Use the immersion charts supplied by the smooth embedding and replace the chart expression
    -- by the linear model map `u ↦ (u, 0)` on the boundary target neighborhood.
    intro x
    let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
      hBoundary.isImmersion.isImmersionAt x
    let x' := (hImm.domChart.extend IB) x
    let L : EB →L[ℝ] E :=
      hImm.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ EB hImm.complement)
    have hcont : Continuous (Subtype.val : ↥(I.boundary M) → M) := by
      simpa [Function.comp] using
        (Topology.IsEmbedding.continuous_iff hBoundary.isEmbedding).mp continuous_id
    have hx : x ∈ hImm.domChart.source := hImm.mem_domChart_source
    have hy : (Subtype.val : ↥(I.boundary M) → M) x ∈ hImm.codChart.source :=
      hImm.mem_codChart_source
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
      (e := hImm.domChart) (e' := hImm.codChart) hImm.domChart_mem_maximalAtlas
      hImm.codChart_mem_maximalAtlas hx hy, continuousWithinAt_univ, Set.preimage_univ,
      Set.univ_inter]
    refine ⟨hcont.continuousAt, ?_⟩
    have hmodel : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) L (Set.range IB) x' := by
      -- The linear model map is smooth on the whole model space, hence on the chart range.
      exact L.contDiff.contDiffWithinAt
    have htarget_mem : (hImm.domChart.extend IB).target ∈ nhdsWithin x' (Set.range IB) := by
      -- The extended chart target is the canonical neighborhood of `x'` inside `range IB`.
      simpa [x'] using hImm.domChart.extend_target_mem_nhdsWithin (I := IB) hx
    have hEq :
        ((hImm.codChart.extend I) ∘ (Subtype.val : ↥(I.boundary M) → M) ∘
            (hImm.domChart.extend IB).symm)
          =ᶠ[nhdsWithin x' (Set.range IB)] L := by
      -- On the chart target, the immersion normal form identifies the inclusion with `L`.
      refine Filter.eventuallyEq_of_mem htarget_mem ?_
      intro z hz
      simpa [Function.comp, L] using hImm.writtenInCharts hz
    have hx'_target : x' ∈ (hImm.domChart.extend IB).target :=
      (hImm.domChart.extend IB).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx
    have hx'_range : x' ∈ Set.range IB :=
      hImm.domChart.extend_target_subset_range hx'_target
    -- Replace the chart expression by the linear model on a neighborhood within `range IB`.
    exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range
  exact hBoundarySmoothTop.of_le le_top

/-- Helper for Problem 5-23: the boundary inclusion is manifold-differentiable at every point of
the chosen boundary subtype. -/
theorem mdifferentiableAt_boundary_inclusion
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    MDifferentiableAt IB I (Subtype.val : ↥(I.boundary M) → M) x := by
  -- Pointwise differentiability is the degree-`1` consequence of smoothness of the inclusion.
  exact
    (contMDiff_boundary_inclusion (I := I) (IB := IB) hBoundary).mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)

/-- Helper for Problem 5-23: in the immersion normal form for the boundary inclusion, forgetting
the complementary coordinates is a surjective linear projection onto the boundary model space. -/
theorem boundary_chart_projection_surjective
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
      hBoundary.isImmersion.isImmersionAt x
    let pi : E →L[ℝ] EB :=
      (ContinuousLinearMap.fst ℝ EB hImm.complement).comp hImm.equiv.symm.toContinuousLinearMap
    Function.Surjective pi := by
  -- Choose the chart vector with zero complementary coordinate and push it through the inverse
  -- immersion equivalence.
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let pi : E →L[ℝ] EB :=
    (ContinuousLinearMap.fst ℝ EB hImm.complement).comp hImm.equiv.symm.toContinuousLinearMap
  -- After unfolding the local definitions, every boundary coordinate has a preimage with zero
  -- complementary component.
  show Function.Surjective pi
  intro v
  refine Exists.intro (hImm.equiv (v, 0)) ?_
  simp [pi, ContinuousLinearMap.comp_apply]

/-- Helper for Problem 5-23: the restriction of a smooth ambient map to a smooth boundary subtype
is smooth. -/
theorem contMDiff_boundary_restriction
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (hF : ContMDiff I J ∞ F) :
    ContMDiff IB J ∞ (fun y : ↥(I.boundary M) ↦ F y) := by
  -- First make the chosen boundary inclusion smooth in the supplied boundary structure.
  have hBoundarySmooth : ContMDiff IB I ∞ (Subtype.val : ↥(I.boundary M) → M) :=
    contMDiff_boundary_inclusion (I := I) (IB := IB) hBoundary
  -- With the boundary inclusion now known to be smooth, the restriction is just a composition.
  simpa [Function.comp] using hF.comp hBoundarySmooth

/-- Helper for Problem 5-23: surjectivity of the derivative of the boundary restriction is the
same as surjectivity of the intrinsic within-derivative along the ambient boundary. -/
theorem surjective_comp_iff_of_surjective
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : Y →L[ℝ] Z) (B : X →L[ℝ] Y) (hB : Function.Surjective B) :
    Function.Surjective (A.comp B) ↔ Function.Surjective A := by
  constructor
  · intro hComp
    -- Read surjectivity of the outer map off the surjectivity of the composite.
    exact Function.Surjective.of_comp hComp
  · intro hA
    -- Once the comparison map onto the boundary coordinates is surjective, surjectivity pushes
    -- forward through the composition immediately.
    exact hA.comp hB

/-- Helper for Problem 5-23: the zero map onto a nontrivial target cannot be surjective. -/
theorem not_surjective_zero_map
    {X : Type*} [Zero X] {Y : Type*} [Zero Y] [Nontrivial Y] :
    ¬ Function.Surjective (fun _ : X ↦ (0 : Y)) := by
  intro hsurj
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  rcases hsurj y with ⟨x, hx⟩
  exact hy <| by simpa using hx.symm

/-- Helper for Problem 5-23: if the within-derivative is surjective onto a nontrivial target
tangent space, then the map is manifold-differentiable within the set. -/
theorem mdifferentiableWithinAt_of_surjective_mfderivWithin
    {f : M → N} {s : Set M} {x : M}
    [Nontrivial (TangentSpace J (f x))]
    (hsurj : Function.Surjective (mfderivWithin I J f s x)) :
    MDifferentiableWithinAt I J f s x := by
  by_contra hmdiff
  -- If the map were not differentiable within the set, `mfderivWithin` would be the zero map.
  have hzero : mfderivWithin I J f s x = 0 :=
    mfderivWithin_zero_of_not_mdifferentiableWithinAt hmdiff
  exact not_surjective_zero_map (X := TangentSpace I x)
    (Y := TangentSpace J (f x)) <| by simpa [hzero] using hsurj

/-- Helper for Problem 5-23: if the manifold derivative is surjective onto a nontrivial target
tangent space, then the map is manifold-differentiable at the point. -/
theorem mdifferentiableAt_of_surjective_mfderiv
    {f : M → N} {x : M}
    [Nontrivial (TangentSpace J (f x))]
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    MDifferentiableAt I J f x := by
  by_contra hmdiff
  -- If the map were not differentiable at the point, `mfderiv` would be the zero map.
  have hzero : mfderiv I J f x = 0 :=
    mfderiv_zero_of_not_mdifferentiableAt hmdiff
  exact not_surjective_zero_map (X := TangentSpace I x)
    (Y := TangentSpace J (f x)) <| by simpa [hzero] using hsurj

/-- Helper for Problem 5-23: the inverse of an extended maximal-atlas chart is
manifold-differentiable within the model range at the corresponding chart point. -/
theorem chart_extend_symm_mdifferentiableWithin_range
    {x : M} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I (⊤ : WithTop ℕ∞) M) (hx : x ∈ e.source) :
    MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I (e.extend I).symm (Set.range I)
      (e.extend I x) := by
  letI : IsManifold I 1 M :=
    IsManifold.of_le (m := 1) (n := (⊤ : WithTop ℕ∞)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (m := 1) (n := (⊤ : WithTop ℕ∞)) (by simp) he
  have hid : MDifferentiableWithinAt I I (id : M → M) Set.univ x := by
    -- The inverse-chart differentiability bridge starts from the trivial differentiability of
    -- the identity map on the manifold.
    simpa using
      (mdifferentiableWithinAt_id (I := I) (s := Set.univ) (x := x) :
        MDifferentiableWithinAt I I (id : M → M) Set.univ x)
  -- Re-express `id` in chart coordinates so the inverse extended chart appears as the local
  -- representative on `Set.range I`.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
      (I := I) (I' := I) (e := e) (f := id) (s := Set.univ) he_one hx).mp hid

/-- Helper for Problem 5-23: if a chart-written map agrees near the base point within `range I`
with a differentiable model-space map, then its within-derivative is the ordinary derivative of
that model-space map. -/
theorem fderivWithin_writtenInExtChartAt_eq_fderiv_of_eventuallyEq
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H'']
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H'' M']
    {I' : ModelWithCorners ℝ E'' H''}
    (p : M) {f : M → M'} {g : E → E''}
    (hg :
      g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)] writtenInExtChartAt I I' p f)
    (hg_diff : DifferentiableAt ℝ g (extChartAt I p p)) :
    fderivWithin ℝ (writtenInExtChartAt I I' p f) (Set.range I) (extChartAt I p p) =
      fderiv ℝ g (extChartAt I p p) := by
  let q : E := extChartAt I p p
  have hq_range : q ∈ Set.range I := by
    -- The preferred chart point always lies in the model range.
    exact extChartAt_target_subset_range (I := I) p (mem_extChartAt_target (I := I) p)
  have hq_uniqueDiff : UniqueDiffWithinAt ℝ (Set.range I) q := by
    -- The model range has the canonical unique-differentiability owner at chart points.
    simpa [q, extChartAt, mem_chart_source] using
      (I.uniqueDiffWithinAt_image (x := chartAt H p p))
  have hderivWithin :
      fderivWithin ℝ g (Set.range I) q =
        fderivWithin ℝ (writtenInExtChartAt I I' p f) (Set.range I) q :=
    Filter.EventuallyEq.fderivWithin_eq_of_mem (f₁ := g)
      (f := writtenInExtChartAt I I' p f) hg hq_range
  -- First replace the chart-written function by the ambient differentiable model map, then remove
  -- the `within` because the model range is uniquely differentiable there.
  calc
    fderivWithin ℝ (writtenInExtChartAt I I' p f) (Set.range I) q
      = fderivWithin ℝ g (Set.range I) q := by
          simpa using hderivWithin.symm
    _ = fderiv ℝ g q := by
          exact DifferentiableAt.fderivWithin hg_diff hq_uniqueDiff

/-- Helper for Problem 5-23: in boundary-immersion charts, dropping the complementary coordinates
and returning through the boundary chart gives the local retraction onto the boundary subtype used
to compare ambient and intrinsic derivatives. -/
noncomputable def boundary_chart_retraction
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    M → ↥(I.boundary M) :=
  fun y =>
    let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
      hBoundary.isImmersion.isImmersionAt x
    let pi : E →L[ℝ] EB :=
      (ContinuousLinearMap.fst ℝ EB hImm.complement).comp hImm.equiv.symm.toContinuousLinearMap
    (hImm.domChart.extend IB).symm (pi ((hImm.codChart.extend I) y))

/-- Helper for Problem 5-23: on the boundary chart source itself, the chart-level retraction is
literally the identity after the immersion normal form replaces the inclusion by `u ↦ (u, 0)`. -/
theorem boundary_chart_retraction_eq_of_mem_domChart_source
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x z : ↥(I.boundary M))
    (hz : z ∈ (hBoundary.isImmersion.isImmersionAt x).domChart.source) :
    boundary_chart_retraction (I := I) (IB := IB) hBoundary x z = z := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let pi : E →L[ℝ] EB :=
    (ContinuousLinearMap.fst ℝ EB hImm.complement).comp hImm.equiv.symm.toContinuousLinearMap
  have hz_target : (hImm.domChart.extend IB) z ∈ (hImm.domChart.extend IB).target := by
    -- Moving a source point through the extended chart lands in the chart target.
    exact (hImm.domChart.extend IB).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  have hchart :
      (hImm.codChart.extend I) (z : M) =
        hImm.equiv ((hImm.domChart.extend IB) z, (0 : hImm.complement)) := by
    -- The immersion normal form identifies the boundary inclusion with `u ↦ (u, 0)`.
    simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
      hImm.writtenInCharts hz_target
  have hchart_coe :
      I (hImm.codChart (z : M)) =
        hImm.equiv ((hImm.domChart.extend IB) z, (0 : hImm.complement)) := by
    -- After unfolding `extend` on a source point, the same chart identity appears in raw chart
    -- coordinates.
    simpa [OpenPartialHomeomorph.extend_coe] using hchart
  have hproj :
      pi ((hImm.codChart.extend I) (z : M)) = (hImm.domChart.extend IB) z := by
    -- Projecting away the complementary coordinate recovers the boundary chart coordinate.
    calc
      pi ((hImm.codChart.extend I) (z : M))
          = pi (hImm.equiv ((hImm.domChart.extend IB) z, (0 : hImm.complement))) := by
              rw [hchart]
      _ = (hImm.domChart.extend IB) z := by
            simp [pi, ContinuousLinearMap.comp_apply]
  -- Route correction: the retraction proof now isolates the chart cancellation step explicitly,
  -- so the remaining factorization can differentiate this concrete local identity.
  -- After unfolding the retraction, rewrite through the chart normal form and then project away
  -- the complementary coordinate explicitly before canceling the inverse chart.
  dsimp [boundary_chart_retraction, hImm, pi]
  rw [hchart_coe]
  simp
  exact hImm.domChart.left_inv hz

/-- Helper for Problem 5-23: after forgetting the subtype proof, the same chart-level retraction
fixes every ambient boundary point lying in the image of the distinguished boundary chart source. -/
theorem boundary_chart_retraction_val_eq_of_mem_image_domChart_source
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) {y : M}
    (hy : y ∈ Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source) :
    (boundary_chart_retraction (I := I) (IB := IB) hBoundary x y : M) = y := by
  rcases hy with ⟨z, hz, rfl⟩
  -- Restrict back to the boundary subtype source and use the chart-level identity there.
  exact congrArg Subtype.val
    (boundary_chart_retraction_eq_of_mem_domChart_source
      (I := I) (IB := IB) hBoundary x z hz)

/-- Helper for Problem 5-23: the image of the boundary immersion chart source is a neighborhood of
`x` within the ambient boundary subset. -/
theorem boundary_chart_source_image_mem_nhdsWithin
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source ∈
      nhdsWithin (x : M) (I.boundary M) := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  have hsource_mem : hImm.domChart.source ∈ nhds x := by
    -- In the boundary manifold, the domain chart source is an ordinary open neighborhood of `x`.
    exact hImm.domChart.open_source.mem_nhds hImm.mem_domChart_source
  have himage_mem :
      Subtype.val '' hImm.domChart.source ∈
        Filter.map (Subtype.val : ↥(I.boundary M) → M) (nhds x) := by
    -- Membership in the mapped neighborhood filter reduces to the obvious preimage inclusion.
    change Subtype.val ⁻¹' (Subtype.val '' hImm.domChart.source) ∈ nhds x
    refine Filter.mem_of_superset hsource_mem ?_
    intro z hz
    exact ⟨z, hz, rfl⟩
  rw [Topology.IsEmbedding.map_nhds_eq Topology.IsEmbedding.subtypeVal x, Subtype.range_coe] at himage_mem
  simpa [hImm] using himage_mem

/-- Helper for Problem 5-23: after forgetting the subtype proof, the boundary chart retraction is
the identity on a full neighborhood of `x` inside the ambient boundary. -/
theorem boundary_chart_retraction_val_eventuallyEq_id
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    (fun y : M ↦ ((boundary_chart_retraction (I := I) (IB := IB) hBoundary x y :
      ↥(I.boundary M)) : M)) =ᶠ[nhdsWithin (x : M) (I.boundary M)] fun y ↦ y := by
  have hmem :
      Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source ∈
        nhdsWithin (x : M) (I.boundary M) :=
    boundary_chart_source_image_mem_nhdsWithin (I := I) (IB := IB) hBoundary x
  -- On the image of the distinguished boundary chart source, the pointwise retraction formula is
  -- already established, so it upgrades to an eventual equality on `nhdsWithin`.
  refine Filter.eventuallyEq_of_mem hmem ?_
  intro y hy
  simpa using
    boundary_chart_retraction_val_eq_of_mem_image_domChart_source
      (I := I) (IB := IB) hBoundary x hy

/-- Helper for Problem 5-23: the canonical ambient within-derivative of the boundary retraction,
after forgetting the subtype proof, matches the canonical within-derivative of the identity on the
ambient boundary because the two maps agree on a neighborhood within `I.boundary M`. -/
theorem mfderivWithin_boundary_chart_retraction_val_eq_mfderivWithin_id
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    mfderivWithin I I
        (fun y : M ↦ ((boundary_chart_retraction (I := I) (IB := IB) hBoundary x y :
          ↥(I.boundary M)) : M))
        (I.boundary M) (x : M) =
      mfderivWithin I I (id : M → M) (I.boundary M) (x : M) := by
  -- Differentiate the concrete ambient-valued retraction identity on the actual boundary filter.
  exact
    Filter.EventuallyEq.mfderivWithin_eq_of_mem
      (boundary_chart_retraction_val_eventuallyEq_id (I := I) (IB := IB) hBoundary x) x.2

/-- Helper for Problem 5-23: the chart-level boundary retraction is manifold-differentiable on
the ambient image of the distinguished boundary chart source. -/
theorem boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    let s_x := Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source
    MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
      s_x (x : M) := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let s_x : Set M := Subtype.val '' hImm.domChart.source
  let pi : E →L[ℝ] EB :=
    (ContinuousLinearMap.fst ℝ EB hImm.complement).comp hImm.equiv.symm.toContinuousLinearMap
  have hx_dom : x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hcodChart_mem_maximalAtlas_one :
      hImm.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (m := 1) (n := (⊤ : WithTop ℕ∞)) (by simp) hImm.codChart_mem_maximalAtlas
  have hcod :
      MDifferentiableAt I (modelWithCornersSelf ℝ E) (hImm.codChart.extend I) (x : M) := by
    -- Maximal-atlas codomain charts are differentiable at the base boundary point.
    exact
      (contMDiffAt_extend (I := I) (e := hImm.codChart) hcodChart_mem_maximalAtlas_one
        hImm.mem_codChart_source).mdifferentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  have hpi :
      MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ EB) pi
        ((hImm.codChart.extend I) (x : M)) := by
    -- The chart-level coordinate projection is a continuous linear map between model spaces.
    exact pi.contMDiffAt.mdifferentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  have hsymm :
      MDifferentiableWithinAt (modelWithCornersSelf ℝ EB) IB (hImm.domChart.extend IB).symm
        (Set.range IB) ((hImm.domChart.extend IB) x) :=
    chart_extend_symm_mdifferentiableWithin_range
      (I := IB) hImm.domChart_mem_maximalAtlas hx_dom
  have hinner_mapsTo :
      s_x ⊆ (fun y : M ↦ pi ((hImm.codChart.extend I) y)) ⁻¹' Set.range IB := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    change pi ((hImm.codChart.extend I) (z : M)) ∈ Set.range IB
    have hz_target : (hImm.domChart.extend IB) z ∈ (hImm.domChart.extend IB).target := by
      -- Moving a source point through the boundary chart lands in the chart target.
      exact (hImm.domChart.extend IB).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    have hchart :
        (hImm.codChart.extend I) (z : M) =
          hImm.equiv ((hImm.domChart.extend IB) z, (0 : hImm.complement)) := by
      -- The immersion normal form writes the boundary inclusion as `u ↦ (u, 0)` in charts.
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
        hImm.writtenInCharts hz_target
    -- Projecting away the complementary coordinate returns to the boundary chart range.
    refine ⟨hImm.domChart z, ?_⟩
    symm
    calc
      pi ((hImm.codChart.extend I) (z : M))
          = pi (hImm.equiv ((hImm.domChart.extend IB) z, (0 : hImm.complement))) := by
              rw [hchart]
      _ = (hImm.domChart.extend IB) z := by
            simp [pi, ContinuousLinearMap.comp_apply]
      _ = IB (hImm.domChart z) := by
            rfl
  have hinner :
      MDifferentiableWithinAt I (modelWithCornersSelf ℝ EB)
        (fun y : M ↦ pi ((hImm.codChart.extend I) y)) s_x (x : M) := by
    -- First differentiate the codomain chart, then postcompose with the linear projection.
    exact hpi.comp_mdifferentiableWithinAt _ hcod.mdifferentiableWithinAt
  have hinner_eq :
      pi ((hImm.codChart.extend I) (x : M)) = (hImm.domChart.extend IB) x := by
    have hx_target : (hImm.domChart.extend IB) x ∈ (hImm.domChart.extend IB).target := by
      -- The base boundary point lies in the target of its own boundary chart.
      exact (hImm.domChart.extend IB).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx_dom
    have hchart :
        (hImm.codChart.extend I) (x : M) =
          hImm.equiv ((hImm.domChart.extend IB) x, (0 : hImm.complement)) := by
      -- At the base point, the same immersion normal form gives the chart identity.
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hx_dom] using
        hImm.writtenInCharts hx_target
    calc
      pi ((hImm.codChart.extend I) (x : M))
          = pi (hImm.equiv ((hImm.domChart.extend IB) x, (0 : hImm.complement))) := by
              rw [hchart]
      _ = (hImm.domChart.extend IB) x := by
            simp [pi, ContinuousLinearMap.comp_apply]
  -- Route correction: differentiate the concrete chart factorization of the retraction on the
  -- chart-source image itself, not yet on the whole ambient boundary.
  simpa [boundary_chart_retraction, hImm, pi, s_x, Function.comp] using
    hsymm.comp_of_eq _ hinner hinner_mapsTo hinner_eq

/-- Helper for Problem 5-23: differentiating the chart retraction on the chart-source image gives
a right inverse to the derivative of the boundary inclusion, so the retraction derivative is
surjective. -/
theorem boundary_chart_retraction_mfderivWithin_right_inverse
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    let s_x := Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source
    let pi_x := mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
      s_x (x : M)
    pi_x.comp (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) =
      ContinuousLinearMap.id ℝ (TangentSpace IB x) ∧
      Function.Surjective pi_x := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let s_x : Set M := Subtype.val '' hImm.domChart.source
  have hx_dom : x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hsx : (x : M) ∈ s_x := ⟨x, hx_dom, rfl⟩
  have hsource_unique : UniqueMDiffWithinAt IB hImm.domChart.source x :=
    hImm.domChart.open_source.uniqueMDiffWithinAt hx_dom
  have hsub :
      MDifferentiableAt IB I (Subtype.val : ↥(I.boundary M) → M) x :=
    mdifferentiableAt_boundary_inclusion (I := I) (IB := IB) hBoundary x
  have hsub_within :
      mfderivWithin IB I (Subtype.val : ↥(I.boundary M) → M) hImm.domChart.source x =
        mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x :=
    mfderivWithin_eq_mfderiv hsource_unique hsub
  have hretr :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        s_x (x : M) :=
    boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
      (I := I) (IB := IB) hBoundary x
  have hpre :
      (Subtype.val : ↥(I.boundary M) → M) ⁻¹' s_x ∈ nhdsWithin x hImm.domChart.source := by
    -- The boundary chart source maps entirely into its ambient image `s_x`.
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro z hz
    exact ⟨z, hz, rfl⟩
  have hcomp :
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x =
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
            s_x (x : M)).comp
          (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) := by
    -- Differentiate the composite on the actual boundary chart source, then replace the within
    -- derivative of the inclusion by the ordinary derivative on this open source set.
    calc
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x
          =
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
            s_x (x : M)).comp
          (mfderivWithin IB I (Subtype.val : ↥(I.boundary M) → M) hImm.domChart.source x) := by
            exact mfderivWithin_comp_of_preimage_mem_nhdsWithin x hretr hsub.mdifferentiableWithinAt
              hpre hsource_unique
      _ =
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
            s_x (x : M)).comp
          (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) := by
            rw [hsub_within]
  have hid_comp :
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x =
        ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
    have hcomp_eq_id :
        mfderivWithin IB IB
            (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
              (Subtype.val : ↥(I.boundary M) → M))
            hImm.domChart.source x =
          mfderivWithin IB IB (id : ↥(I.boundary M) → ↥(I.boundary M)) hImm.domChart.source x := by
      apply mfderivWithin_congr_of_mem
      · intro z hz
        simpa [Function.comp] using
          boundary_chart_retraction_eq_of_mem_domChart_source
            (I := I) (IB := IB) hBoundary x z hz
      · exact hx_dom
    have hid :
        mfderivWithin IB IB (id : ↥(I.boundary M) → ↥(I.boundary M)) hImm.domChart.source x =
          ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
      simpa using
        (mfderivWithin_id (I := IB) (s := hImm.domChart.source) (x := x)
          (M := ↥(I.boundary M)) hsource_unique)
    -- On the boundary chart source, the retraction really is the identity.
    exact hcomp_eq_id.trans hid
  have hright :
      (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x) s_x
          (x : M)).comp
        (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) =
      ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
    exact hcomp.symm.trans hid_comp
  have hsurj :
      Function.Surjective
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x) s_x
          (x : M)) := by
    intro v
    refine ⟨(mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) v, ?_⟩
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L v) hright
  simpa [s_x] using ⟨hright, hsurj⟩

/-- Helper for Problem 5-23: after transporting the chart-source-image differentiability of the
boundary retraction to the actual ambient boundary subset, its within-derivative there still
right-inverts the derivative of the boundary inclusion and is therefore surjective. -/
theorem boundary_chart_retraction_mfderivWithin_boundary_right_inverse
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    let pi := mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
      (I.boundary M) (x : M)
    pi.comp (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) =
      ContinuousLinearMap.id ℝ (TangentSpace IB x) ∧
      Function.Surjective pi := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let s_x : Set M := Subtype.val '' hImm.domChart.source
  have hx_dom : x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hsource_unique : UniqueMDiffWithinAt IB hImm.domChart.source x :=
    hImm.domChart.open_source.uniqueMDiffWithinAt hx_dom
  have hsub :
      MDifferentiableAt IB I (Subtype.val : ↥(I.boundary M) → M) x :=
    mdifferentiableAt_boundary_inclusion (I := I) (IB := IB) hBoundary x
  have hsub_within :
      mfderivWithin IB I (Subtype.val : ↥(I.boundary M) → M) hImm.domChart.source x =
        mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x :=
    mfderivWithin_eq_mfderiv hsource_unique hsub
  have hmem :
      s_x ∈ nhdsWithin (x : M) (I.boundary M) :=
    boundary_chart_source_image_mem_nhdsWithin (I := I) (IB := IB) hBoundary x
  have hretr_s :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        s_x (x : M) :=
    boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
      (I := I) (IB := IB) hBoundary x
  have hretr_boundary :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (I.boundary M) (x : M) :=
    hretr_s.mono_of_mem_nhdsWithin hmem
  let pi := mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
    (I.boundary M) (x : M)
  have hpre :
      (Subtype.val : ↥(I.boundary M) → M) ⁻¹' (I.boundary M) ∈
        nhdsWithin x hImm.domChart.source := by
    -- The boundary inclusion lands in the ambient boundary identically.
    simpa using
      (show (Set.univ : Set ↥(I.boundary M)) ∈ nhdsWithin x hImm.domChart.source from
        Filter.univ_mem)
  have hcomp :
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x
        =
      pi.comp (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) := by
    -- Differentiate the composite on the genuine boundary chart source, but keep the retraction
    -- derivative taken on the ambient boundary subset where the final factorization will live.
    calc
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x
          =
        pi.comp
          (mfderivWithin IB I (Subtype.val : ↥(I.boundary M) → M) hImm.domChart.source x) := by
            exact mfderivWithin_comp_of_preimage_mem_nhdsWithin x hretr_boundary
              hsub.mdifferentiableWithinAt hpre hsource_unique
      _ =
        pi.comp (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) := by
            rw [hsub_within]
  have hid_comp :
      mfderivWithin IB IB
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
            (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x =
        ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
    have hcomp_eq_id :
        mfderivWithin IB IB
            (boundary_chart_retraction (I := I) (IB := IB) hBoundary x ∘
              (Subtype.val : ↥(I.boundary M) → M))
            hImm.domChart.source x =
          mfderivWithin IB IB (id : ↥(I.boundary M) → ↥(I.boundary M)) hImm.domChart.source x := by
      apply mfderivWithin_congr_of_mem
      · intro z hz
        simpa [Function.comp] using
          boundary_chart_retraction_eq_of_mem_domChart_source
            (I := I) (IB := IB) hBoundary x z hz
      · exact hx_dom
    have hid :
        mfderivWithin IB IB (id : ↥(I.boundary M) → ↥(I.boundary M)) hImm.domChart.source x =
          ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
      simpa using
        (mfderivWithin_id (I := IB) (s := hImm.domChart.source) (x := x)
          (M := ↥(I.boundary M)) hsource_unique)
    -- On the boundary chart source, the retraction composed with the inclusion is literally `id`.
    exact hcomp_eq_id.trans hid
  have hright :
      pi.comp (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) =
        ContinuousLinearMap.id ℝ (TangentSpace IB x) := by
    exact hcomp.symm.trans hid_comp
  have hsurj : Function.Surjective pi := by
    intro v
    refine ⟨(mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) v, ?_⟩
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L v) hright
  exact ⟨hright, hsurj⟩

/-- Helper for Problem 5-23: differentiability of the intrinsic boundary restriction is
equivalent to differentiability of the ambient map within the ambient boundary subset. -/
theorem boundary_restriction_mdifferentiableAt_iff
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    MDifferentiableAt IB J (fun y : ↥(I.boundary M) ↦ F y) x ↔
      MDifferentiableWithinAt I J F (I.boundary M) (x : M) := by
  let hImm : IsImmersionAt IB I (⊤ : WithTop ℕ∞) (Subtype.val : ↥(I.boundary M) → M) x :=
    hBoundary.isImmersion.isImmersionAt x
  let G : M → N :=
    fun y ↦ F (boundary_chart_retraction (I := I) (IB := IB) hBoundary x y)
  have hx_dom : x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hsub :
      MDifferentiableAt IB I (Subtype.val : ↥(I.boundary M) → M) x :=
    mdifferentiableAt_boundary_inclusion (I := I) (IB := IB) hBoundary x
  have hretr_s :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (Subtype.val '' hImm.domChart.source) (x : M) :=
    boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
      (I := I) (IB := IB) hBoundary x
  have hmem :
      Subtype.val '' hImm.domChart.source ∈ nhdsWithin (x : M) (I.boundary M) :=
    boundary_chart_source_image_mem_nhdsWithin (I := I) (IB := IB) hBoundary x
  have hretr_boundary :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (I.boundary M) (x : M) :=
    hretr_s.mono_of_mem_nhdsWithin hmem
  have hbase :
      boundary_chart_retraction (I := I) (IB := IB) hBoundary x (x : M) = x := by
    exact boundary_chart_retraction_eq_of_mem_domChart_source
      (I := I) (IB := IB) hBoundary x x hx_dom
  have hGF :
      G =ᶠ[nhdsWithin (x : M) (I.boundary M)] F := by
    -- On a neighborhood within the boundary, the retraction is the identity after forgetting the
    -- subtype proof, so the ambient composite agrees with `F`.
    filter_upwards
      [boundary_chart_retraction_val_eventuallyEq_id (I := I) (IB := IB) hBoundary x] with y hy
    simpa [G, hy]
  constructor
  · intro hRestr
    have hG :
        MDifferentiableWithinAt I J G (I.boundary M) (x : M) :=
      hRestr.comp_mdifferentiableWithinAt_of_eq _ hretr_boundary hbase
    -- Replace the retract-then-restrict composite by `F` on the actual ambient boundary.
    exact hG.congr_of_eventuallyEq_of_mem hGF.symm x.2
  · intro hF
    have hG :
        MDifferentiableWithinAt I J G (I.boundary M) (x : M) :=
      hF.congr_of_eventuallyEq_of_mem hGF x.2
    have hpre :
        (Subtype.val : ↥(I.boundary M) → M) ⁻¹' (I.boundary M) ∈
          nhdsWithin x hImm.domChart.source := by
      -- The boundary inclusion always lands back in the ambient boundary.
      simpa using
        (show (Set.univ : Set ↥(I.boundary M)) ∈ nhdsWithin x hImm.domChart.source from
          Filter.univ_mem)
    have hGcomp :
        MDifferentiableWithinAt IB J (G ∘ (Subtype.val : ↥(I.boundary M) → M))
          hImm.domChart.source x :=
      hG.comp_of_preimage_mem_nhdsWithin _ hsub.mdifferentiableWithinAt hpre
    have hEq :
        (G ∘ (Subtype.val : ↥(I.boundary M) → M)) =ᶠ[nhdsWithin x hImm.domChart.source]
          fun y : ↥(I.boundary M) ↦ F y := by
      refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      -- On the boundary chart source, the chart retraction really is the identity.
      simpa [Function.comp, G] using
        congrArg (fun w : ↥(I.boundary M) ↦ F w)
          (boundary_chart_retraction_eq_of_mem_domChart_source
            (I := I) (IB := IB) hBoundary x z hz)
    have hRestrWithin :
        MDifferentiableWithinAt IB J (fun y : ↥(I.boundary M) ↦ F y)
          hImm.domChart.source x :=
      hGcomp.congr_of_eventuallyEq_of_mem hEq.symm hx_dom
    -- The chart source is an ordinary neighborhood in the boundary manifold, so within- and
    -- ordinary differentiability agree there.
    exact hRestrWithin.mdifferentiableAt (hImm.domChart.open_source.mem_nhds hx_dom)

/-- Helper for Problem 5-23: on the exact chart filter defining `mfderivWithin` along
`I.boundary M`, the ambient chart-written map agrees with the chart-written intrinsic boundary
restriction composed with the chart-written boundary retraction. -/
theorem boundary_restriction_writtenInExtChartAt_eventuallyEq_retract_comp
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    let q := extChartAt I (x : M) (x : M)
    let s := ((extChartAt I (x : M)).symm ⁻¹' (I.boundary M)) ∩ Set.range I
    writtenInExtChartAt I J (x : M) F =ᶠ[nhdsWithin q s]
      (writtenInExtChartAt IB J x (fun y : ↥(I.boundary M) ↦ F y) ∘
        writtenInExtChartAt I IB (x : M)
          (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)) := by
  let G : M → N := fun y ↦ F (boundary_chart_retraction (I := I) (IB := IB) hBoundary x y)
  have hmem :
      Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source ∈
        nhdsWithin (x : M) (I.boundary M) :=
    boundary_chart_source_image_mem_nhdsWithin (I := I) (IB := IB) hBoundary x
  have hretr_s :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source) (x : M) :=
    boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
      (I := I) (IB := IB) hBoundary x
  have hretr_boundary :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (I.boundary M) (x : M) :=
    hretr_s.mono_of_mem_nhdsWithin hmem
  have hbase_subtype :
      boundary_chart_retraction (I := I) (IB := IB) hBoundary x (x : M) = x := by
    -- The chart retraction fixes the base boundary point itself.
    exact boundary_chart_retraction_eq_of_mem_domChart_source
      (I := I) (IB := IB) hBoundary x x
      (hBoundary.isImmersion.isImmersionAt x).mem_domChart_source
  have hbase :
      (boundary_chart_retraction (I := I) (IB := IB) hBoundary x (x : M) : M) = x := by
    exact congrArg Subtype.val hbase_subtype
  have hGF :
      G =ᶠ[nhdsWithin (x : M) (I.boundary M)] F := by
    -- On a neighborhood within the ambient boundary, the retraction is the identity.
    filter_upwards
      [boundary_chart_retraction_val_eventuallyEq_id (I := I) (IB := IB) hBoundary x] with y hy
    simpa [G, hy]
  have hwritten_eq :
      writtenInExtChartAt I J (x : M) F =ᶠ[nhdsWithin (extChartAt I (x : M) (x : M))
          (((extChartAt I (x : M)).symm ⁻¹' (I.boundary M)) ∩ Set.range I)]
        writtenInExtChartAt I J (x : M) G := by
    have hpre :
        (extChartAt I (x : M)).symm ⁻¹' {y : M | G y = F y} ∈
          nhdsWithin (extChartAt I (x : M) (x : M))
            (((extChartAt I (x : M)).symm ⁻¹' (I.boundary M)) ∩ Set.range I) :=
      extChartAt_preimage_mem_nhdsWithin (I := I) hGF
    -- Pull the ambient eventual equality back through the preferred source chart.
    refine Filter.eventuallyEq_of_mem hpre ?_
    intro y hy
    simpa [writtenInExtChartAt, G, hbase, Function.comp] using
      congrArg (extChartAt J (F (x : M))) hy.symm
  have hcomp :
      writtenInExtChartAt I J (x : M) G =ᶠ[nhdsWithin (extChartAt I (x : M) (x : M))
          (((extChartAt I (x : M)).symm ⁻¹' (I.boundary M)) ∩ Set.range I)]
        (writtenInExtChartAt IB J x (fun y : ↥(I.boundary M) ↦ F y) ∘
          writtenInExtChartAt I IB (x : M)
            (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)) := by
    -- Apply the chart composition formula on the actual boundary within-filter.
    simpa [G, hbase, hbase_subtype, Function.comp] using
      (writtenInExtChartAt_comp (I := I) (I' := IB) (I'' := J)
        (x := (x : M)) (s := I.boundary M)
        (f := boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (g := fun y : ↥(I.boundary M) ↦ F y) hretr_boundary.continuousWithinAt)
  exact hwritten_eq.trans hcomp

/-- Helper for Problem 5-23: the ambient within-derivative along the boundary factors through the
intrinsic derivative of the boundary restriction by a surjective tangent-space projection. -/
theorem mfderiv_boundary_restriction_eq_mfderivWithin_comp_boundary_inclusion
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M)) :
    mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x =
      (mfderivWithin I J F (I.boundary M) (x : M)).comp
        (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) := by
  by_cases hRestr : MDifferentiableAt IB J (fun y : ↥(I.boundary M) ↦ F y) x
  · have hWithin :
        MDifferentiableWithinAt I J F (I.boundary M) (x : M) :=
      (boundary_restriction_mdifferentiableAt_iff (I := I) (J := J) (IB := IB)
        (F := F) hBoundary x).mp hRestr
    have hsub :
        MDifferentiableAt IB I (Subtype.val : ↥(I.boundary M) → M) x :=
      mdifferentiableAt_boundary_inclusion (I := I) (IB := IB) hBoundary x
    have hpre :
        (Subtype.val : ↥(I.boundary M) → M) ⁻¹' (I.boundary M) ∈
          nhdsWithin x (Set.univ : Set ↥(I.boundary M)) := by
      -- The boundary inclusion lands in `I.boundary M` identically.
      simpa using
        (show (Set.univ : Set ↥(I.boundary M)) ∈
            nhdsWithin x (Set.univ : Set ↥(I.boundary M)) from
          Filter.univ_mem)
    have hcomp :
        mfderivWithin IB J ((fun y : M ↦ F y) ∘ (Subtype.val : ↥(I.boundary M) → M))
            Set.univ x =
          (mfderivWithin I J F (I.boundary M) (x : M)).comp
            (mfderivWithin IB I (Subtype.val : ↥(I.boundary M) → M) Set.univ x) := by
      -- Differentiate the restriction as an honest composite `F ∘ Subtype.val`.
      exact mfderivWithin_comp_of_preimage_mem_nhdsWithin x hWithin
        hsub.mdifferentiableWithinAt hpre (uniqueMDiffWithinAt_univ IB)
    -- On the domain `univ`, within- and ordinary manifold derivatives coincide.
    simpa [Function.comp, mfderivWithin_univ] using hcomp
  · have hWithin :
        ¬ MDifferentiableWithinAt I J F (I.boundary M) (x : M) := by
      intro hWithin
      exact hRestr <|
        (boundary_restriction_mdifferentiableAt_iff (I := I) (J := J) (IB := IB)
          (F := F) hBoundary x).mpr hWithin
    have hRestr_zero :
        mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hRestr
    have hWithin_zero :
        mfderivWithin I J F (I.boundary M) (x : M) = 0 :=
      mfderivWithin_zero_of_not_mdifferentiableWithinAt hWithin
    -- When neither map is differentiable, both canonical derivatives are zero.
    simp [hRestr_zero, hWithin_zero]

/-- Helper for Problem 5-23: surjectivity of the intrinsic derivative of the boundary restriction
forces surjectivity of the ambient derivative taken within the boundary subset. -/
theorem surjective_mfderivWithin_of_boundary_restriction_surjective
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M))
    (hsurj : Function.Surjective (mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x)) :
    Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
  have hfactor :
      mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x =
        (mfderivWithin I J F (I.boundary M) x).comp
          (mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) :=
    mfderiv_boundary_restriction_eq_mfderivWithin_comp_boundary_inclusion
      (I := I) (J := J) (IB := IB) (F := F) hBoundary x
  -- The derivative of the restriction is the ambient within-derivative postcomposed with the
  -- derivative of the inclusion, so every target tangent vector already lies in the image of the
  -- ambient within-derivative.
  intro z
  rcases hsurj z with ⟨v, hv⟩
  refine ⟨(mfderiv IB I (Subtype.val : ↥(I.boundary M) → M) x) v, ?_⟩
  simpa [hfactor, ContinuousLinearMap.comp_apply] using hv

/-- Helper for Problem 5-23: boundary regularity forces manifold-differentiability along the
ambient boundary subset. -/
theorem mdifferentiableWithinAt_boundary_of_isBoundaryRegularValue
    {F : M → N} {c : N} {x : M}
    [Nontrivial (TangentSpace J c)]
    (hBoundary : IsBoundaryRegularValue I J F c)
    (hx : x ∈ I.boundary M) (hxc : F x = c) :
    MDifferentiableWithinAt I J F (I.boundary M) x := by
  -- Read differentiability off the surjective boundary within-derivative at the fiber point.
  letI : Nontrivial (TangentSpace J (F x)) := by
    simpa [hxc] using (inferInstance : Nontrivial (TangentSpace J c))
  exact mdifferentiableWithinAt_of_surjective_mfderivWithin (hBoundary x hx hxc)

/-- Helper for Problem 5-23: along the ambient boundary filter, the within-derivative of `F`
factors through the intrinsic derivative of the boundary restriction by postcomposing with the
derivative of the chart-level boundary retraction. -/
theorem mfderivWithin_boundary_eq_mfderiv_boundary_restriction_comp_retraction
    {F : M → N}
    (hBoundary : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (x : ↥(I.boundary M))
    (hRestr : MDifferentiableAt IB J (fun y : ↥(I.boundary M) ↦ F y) x) :
    mfderivWithin I J F (I.boundary M) (x : M) =
      (mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x).comp
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
          (I.boundary M) (x : M)) := by
  have hretr :
      MDifferentiableWithinAt I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
        (I.boundary M) (x : M) := by
    -- First promote the chart-source-image differentiability of the retraction to the actual
    -- ambient boundary filter.
    let s_x : Set M :=
      Subtype.val '' (hBoundary.isImmersion.isImmersionAt x).domChart.source
    have hsx_mem :
        s_x ∈ nhdsWithin (x : M) (I.boundary M) :=
      boundary_chart_source_image_mem_nhdsWithin (I := I) (IB := IB) hBoundary x
    exact
      (boundary_chart_retraction_mdifferentiableWithinAt_on_chart_source_image
        (I := I) (IB := IB) hBoundary x).mono_of_mem_nhdsWithin hsx_mem
  have hpre :
      (boundary_chart_retraction (I := I) (IB := IB) hBoundary x) ⁻¹'
          (Set.univ : Set ↥(I.boundary M)) ∈
        nhdsWithin (x : M) (I.boundary M) := by
    -- The retraction always lands in the intrinsic boundary subtype, so the preimage of `univ`
    -- is all of the ambient boundary filter.
    simpa using
      (show (Set.univ : Set M) ∈ nhdsWithin (x : M) (I.boundary M) from Filter.univ_mem)
  have hcomp :
      mfderivWithin I J
          ((fun y : ↥(I.boundary M) ↦ F y) ∘
            boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
          (I.boundary M) (x : M) =
        (mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x).comp
          (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
            (I.boundary M) (x : M)) := by
    -- Differentiate the retract-then-restrict composite on the actual ambient boundary.
    simpa [Function.comp, mfderivWithin_univ] using
      (mfderivWithin_comp_of_preimage_mem_nhdsWithin
        (x := (x : M))
        hRestr.mdifferentiableWithinAt
        hretr
        hpre
        (uniqueMDiffWithinAt_univ IB))
  have hEq :
      (fun y : M ↦ F y) =ᶠ[nhdsWithin (x : M) (I.boundary M)]
        fun y ↦
          F (boundary_chart_retraction (I := I) (IB := IB) hBoundary x y) := by
    -- On a neighborhood within `I.boundary M`, the boundary retraction is literally the identity
    -- after forgetting the subtype proof.
    filter_upwards
      [boundary_chart_retraction_val_eventuallyEq_id (I := I) (IB := IB) hBoundary x] with y hy
    simpa [hy]
  have hEqDeriv :
      mfderivWithin I J F (I.boundary M) (x : M) =
        mfderivWithin I J
          ((fun y : ↥(I.boundary M) ↦ F y) ∘
            boundary_chart_retraction (I := I) (IB := IB) hBoundary x)
          (I.boundary M) (x : M) :=
    Filter.EventuallyEq.mfderivWithin_eq_of_mem hEq x.2
  -- Replace `F` by the retract-then-restrict composite on the ambient boundary and then apply
  -- the chain-rule factorization above.
  exact hEqDeriv.trans hcomp

/-- Helper for Problem 5-23: once the boundary regular-value hypothesis is read through the
chart-level boundary retraction, the intrinsic boundary restriction becomes an ordinary regular
value problem on `↥(I.boundary M)`. -/
theorem boundary_restriction_isRegularValue
    {F : M → N} {c : N}
    (hBoundaryIncl : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (hBoundaryReg : IsBoundaryRegularValue I J F c) :
    IsRegularValue IB J (fun y : ↥(I.boundary M) ↦ F y) c := by
  intro x hx
  by_cases hSub : Subsingleton (TangentSpace J c)
  · -- If the target tangent space at `c` is trivial, every derivative onto it is automatically
    -- surjective.
    intro z
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · -- In the nontrivial case, the boundary-regular-value hypothesis gives differentiability and a
    -- surjective ambient within-derivative, which the retraction factorization converts into
    -- surjectivity of the intrinsic boundary derivative.
    letI : Nontrivial (TangentSpace J c) := not_subsingleton_iff_nontrivial.mp hSub
    have hWithin :
        MDifferentiableWithinAt I J F (I.boundary M) (x : M) :=
      mdifferentiableWithinAt_boundary_of_isBoundaryRegularValue
        (I := I) (J := J) (F := F) (c := c)
        hBoundaryReg x.2 hx
    have hRestr :
        MDifferentiableAt IB J (fun y : ↥(I.boundary M) ↦ F y) x :=
      (boundary_restriction_mdifferentiableAt_iff
        (I := I) (J := J) (IB := IB) (F := F) hBoundaryIncl x).2 hWithin
    have hWithinSurj :
        Function.Surjective (mfderivWithin I J F (I.boundary M) (x : M)) :=
      boundary_regular_value_surjective_mfderivWithin_at_subtype_point
        (I := I) (J := J) (F := F) (c := c) hBoundaryReg hx
    have hpiSurj :
        Function.Surjective
          (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundaryIncl x)
            (I.boundary M) (x : M)) := by
      -- The derivative of the boundary retraction is surjective because it right-inverts the
      -- derivative of the boundary inclusion.
      simpa using
        (boundary_chart_retraction_mfderivWithin_boundary_right_inverse
          (I := I) (IB := IB) hBoundaryIncl x).2
    have hfactor :
        mfderivWithin I J F (I.boundary M) (x : M) =
          (mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x).comp
            (mfderivWithin I IB
              (boundary_chart_retraction (I := I) (IB := IB) hBoundaryIncl x)
              (I.boundary M) (x : M)) :=
      mfderivWithin_boundary_eq_mfderiv_boundary_restriction_comp_retraction
        (I := I) (J := J) (IB := IB) (F := F) hBoundaryIncl x hRestr
    -- The ambient within-derivative is the composite of the intrinsic boundary derivative with a
    -- surjective retraction derivative, so surjectivity transfers to the intrinsic derivative.
    exact
      (surjective_comp_iff_of_surjective
        (mfderiv IB J (fun y : ↥(I.boundary M) ↦ F y) x)
        (mfderivWithin I IB (boundary_chart_retraction (I := I) (IB := IB) hBoundaryIncl x)
          (I.boundary M) (x : M))
        hpiSurj).1 <| by
          simpa [hfactor]

/-- Helper for Problem 5-23: once a concrete smooth boundary owner is fixed, Lee's intrinsic
boundary hypothesis is exactly the ordinary statement that the boundary restriction is smooth and
has `c` as a regular value. -/
theorem boundary_restriction_contMDiff_and_isRegularValue
    {F : M → N} {c : N}
    (hBoundaryIncl : IsSmoothEmbedding IB I (⊤ : WithTop ℕ∞)
      (Subtype.val : ↥(I.boundary M) → M))
    (hF : ContMDiff I J ∞ F)
    (hBoundaryReg : IsBoundaryRegularValue I J F c) :
    ContMDiff IB J ∞ (fun y : ↥(I.boundary M) ↦ F y) ∧
      IsRegularValue IB J (fun y : ↥(I.boundary M) ↦ F y) c := by
  refine ⟨?_, ?_⟩
  · -- The chosen smooth boundary inclusion turns the restricted map into a smooth composition.
    exact
      contMDiff_boundary_restriction
        (I := I) (J := J) (IB := IB) (F := F) hBoundaryIncl hF
  · -- The intrinsic boundary regular-value condition is already the regular-value statement for
    -- the restricted map once the retraction factorization is in place.
    exact
      boundary_restriction_isRegularValue
        (I := I) (J := J) (IB := IB) (F := F) hBoundaryIncl hBoundaryReg

end BoundaryRestriction

-- Proof sketch: unfold `Set.IsDefiningMap` for `F ⁻¹' {c}`; the chosen level can be taken to
-- be `c`, and conversely the surjectivity hypothesis is exactly the defining condition along the
-- fiber `F⁻¹({c})`.
/-- The canonical defining-map owner specializes on a level set to smoothness of `F` together with
the regular-value owner `IsRegularValue I J F c`. -/
theorem isDefiningMap_levelSet_iff (F : M → N) (c : N) :
    Nonempty (Set.IsDefiningMap I J (F ⁻¹' {c}) F) ↔
      ContMDiff I J ∞ F ∧ IsRegularValue I J F c := by
  constructor
  · intro h
    rcases (Set.isDefiningMap_iff I J (F ⁻¹' {c}) F).mp h with ⟨_, hF, _, hsurj⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact hsurj x <| by simp [hx]
  · rintro ⟨hF, hsurj⟩
    refine (Set.isDefiningMap_iff I J (F ⁻¹' {c}) F).mpr ?_
    refine ⟨c, hF, rfl, ?_⟩
    intro x hx
    exact hsurj x <| Set.mem_singleton_iff.mp hx

end RegularValue

section RegularPreimageWithBoundary

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J (⊤ : WithTop ℕ∞) N]
  [BoundarylessManifold J N]

local notation "levelDim" =>
  Module.finrank ℝ E - Module.finrank ℝ E'

/-- Helper for Problem 5-23: once the fiber has ordinary slice charts away from `I.boundary M`
and half-slice charts along `I.boundary M`, the whole fiber satisfies Lee's local slice condition
with boundary. -/
theorem regular_preimage_satisfiesLocalSliceConditionWithBoundary
    [ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M]
    [IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M]
    {F : M → N} {c : N}
    (hInterior :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∉ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim)
    (hBoundarySlice :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∈ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          x ∈ e.source ∧ e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim) :
    Set.SatisfiesLocalSliceConditionWithBoundary
      (Module.finrank ℝ E) (F ⁻¹' {c}) levelDim := by
  refine ⟨?_⟩
  intro x hx
  by_cases hxBoundary : x ∈ I.boundary M
  · -- Boundary fiber points use the supplied half-slice chart witnesses.
    rcases hBoundarySlice x hx hxBoundary with ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inr he⟩
  · -- Nonboundary fiber points use the supplied ordinary slice chart witnesses.
    rcases hInterior x hx hxBoundary with ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inl he⟩

/-- Helper for Problem 5-23: once the regular fiber has the source-faithful local slice and
half-slice charts in Euclidean ambient coordinates, Theorem 5.51 packages those local models into
the Euclidean-ambient smooth-manifold-with-boundary owner and smooth embedding of the subtype
inclusion. -/
theorem regular_preimage_has_euclidean_embedding_structure
    [ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M]
    [IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M]
    {F : M → N} {c : N}
    (hInterior :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∉ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim)
    (hBoundarySlice :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∈ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          x ∈ e.source ∧ e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim) :
    ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
      letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        (𝓡 (Module.finrank ℝ E))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M) := by
  -- First assemble Lee's local slice-with-boundary criterion from the two pointwise witness
  -- families.
  have hSlice :
      Set.SatisfiesLocalSliceConditionWithBoundary
        (Module.finrank ℝ E) (F ⁻¹' {c}) levelDim := by
    exact
      regular_preimage_satisfiesLocalSliceConditionWithBoundary
        (I := I) (F := F) (c := c) hInterior hBoundarySlice
  -- Then invoke Theorem 5.51 exactly in that Euclidean ambient model.
  rcases
      (local_slice_criterion_for_embedded_submanifold_with_boundary
        (n := Module.finrank ℝ E) (k := levelDim) (M := M) (S := F ⁻¹' {c})).1 hSlice with
    ⟨instSmooth, hEmbedding⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
  simpa using hEmbedding

/-- Helper for Problem 5-23: a pointwise identification of boundary points of the regular fiber
with the ambient boundary immediately yields the textbook boundary formula
`∂(F⁻¹({c})) = F⁻¹({c}) ∩ ∂M`. -/
theorem regular_preimage_boundary_image_eq_of_boundary_point_iff
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hBoundaryPoint :
      ∀ x : (F ⁻¹' {c}),
        (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M) :
    Subtype.val '' (leeBoundaryModelWithCorners levelDim).boundary (F ⁻¹' {c}) =
      (F ⁻¹' {c}) ∩ I.boundary M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- A boundary point of the fiber already lies in the fiber and, by hypothesis, on `∂M`.
    exact ⟨y.2, (hBoundaryPoint y).1 hy⟩
  · intro hx
    let y : F ⁻¹' {c} := ⟨x, hx.1⟩
    -- Repackage the ambient boundary point as the corresponding boundary point of the fiber.
    refine ⟨y, ?_, rfl⟩
    exact (hBoundaryPoint y).2 hx.2

/-- Helper for Problem 5-23: a point away from `I.boundary M` lies in the canonical open interior
submanifold used in Lee's boundaryless branch. -/
theorem mem_interiorOpens_of_not_mem_boundary
    {x : M} (hxBoundary : x ∉ I.boundary M) :
    x ∈ (I.interiorOpens M (show (⊤ : WithTop ℕ∞) ≠ 0 by simp) : Set M) := by
  -- Replace the boundary complement by the manifold interior using
  -- `ModelWithCorners.compl_boundary`.
  change x ∈ I.interior M
  simpa [Set.mem_compl_iff, ModelWithCorners.compl_boundary] using hxBoundary

/-- Helper for Problem 5-23: restricting `F` to an open subtype does not change the defining
level-set equation. -/
theorem open_subtype_mem_preimage_singleton_iff
    {U : TopologicalSpace.Opens M} {F : M → N} {c : N} {y : U} :
    y ∈ (fun z : U ↦ F z) ⁻¹' ({c} : Set N) ↔ (y : M) ∈ F ⁻¹' ({c} : Set N) := by
  -- Both sides say exactly that the ambient value `F y` equals the chosen level `c`.
  simp [Set.mem_preimage, Set.mem_singleton_iff]

/-- Helper for Problem 5-23: the derivative of the inclusion of an open subtype is an
isomorphism of tangent spaces. This is the open-subset ingredient needed in Lee's interior branch
when the regular-value theorem is applied on `I.interior M`. -/
theorem mfderiv_open_subset_inclusion_isInvertible
    (U : TopologicalSpace.Opens M) (p : U) :
    (mfderiv I I (Subtype.val : U → M) p).IsInvertible := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have hsymm : ContMDiffOn I I 1 e.symm (U : Set M) := by
    -- The inverse local inclusion is smooth because it is locally inverse to `Subtype.val`.
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
    -- The open inclusion itself is a local diffeomorphism at every point of the open subtype.
    exact ⟨Φ, hp, fun x _ ↦ rfl⟩
  have hinv : (mfderiv I I (Φ : U → M) p).IsInvertible := by
    -- Local diffeomorphisms have invertible derivatives.
    rw [← hlocal.mfderivToContinuousLinearEquiv_coe one_ne_zero]
    exact ContinuousLinearMap.isInvertible_equiv
  simpa [Φ, e] using hinv

/-- Helper for Problem 5-23: restricting a smooth ambient map to an open subtype preserves
smoothness because the open-subset inclusion is smooth. -/
theorem contMDiff_open_subtype_restriction
    {U : TopologicalSpace.Opens M} {F : M → N}
    (hF : ContMDiff I J ∞ F) :
    ContMDiff I J ∞ (fun y : U ↦ F y) := by
  -- The restricted map is just the ambient map composed with the smooth open-subtype inclusion.
  simpa [Function.comp] using
    hF.comp (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M))

/-- Helper for Problem 5-23: a regular value stays regular after restricting the map to an open
subtype, because the derivative of the open-subset inclusion is an isomorphism. -/
theorem open_subtype_restriction_isRegularValue
    {U : TopologicalSpace.Opens M} {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c) :
    IsRegularValue I J (fun y : U ↦ F y) c := by
  intro x hx
  have hInclDiff : MDifferentiableAt I I (Subtype.val : U → M) x := by
    -- The open-subtype inclusion is smooth, hence differentiable at every point.
    exact
      (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).mdifferentiableAt
        (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hFDiff : MDifferentiableAt I J F (x : M) := by
    -- Ambient smoothness supplies the differentiability side of the chain rule.
    exact hF.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hComp :
      mfderiv I J (fun y : U ↦ F y) x =
        (mfderiv I J F (x : M)).comp (mfderiv I I (Subtype.val : U → M) x) := by
    -- Differentiate the restriction as the literal composition `F ∘ Subtype.val`.
    simpa [Function.comp] using mfderiv_comp x hFDiff hInclDiff
  have hAmbientSurj : Function.Surjective (mfderiv I J F (x : M)) := by
    -- Read regularity of the restricted point back as ambient regularity of its value.
    exact hc (x : M) <| by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx
  have hInclSurj : Function.Surjective (mfderiv I I (Subtype.val : U → M) x) :=
    (mfderiv_open_subset_inclusion_isInvertible (I := I) U x).surjective
  -- Surjectivity survives postcomposition with the invertible derivative of the open inclusion.
  simpa [hComp] using hAmbientSurj.comp hInclSurj

/-- Helper for Problem 5-23: restricting `F` to the intrinsic boundary subtype does not change
the defining level-set equation. -/
theorem boundary_subtype_mem_preimage_singleton_iff
    {F : M → N} {c : N} {y : ↥(I.boundary M)} :
    y ∈ (fun z : ↥(I.boundary M) ↦ F z) ⁻¹' ({c} : Set N) ↔
      (y : M) ∈ F ⁻¹' ({c} : Set N) := by
  -- This is the same level-set equation, now read through the boundary-subtype coercion.
  simp [Set.mem_preimage, Set.mem_singleton_iff]

/-- Helper for Problem 5-23: the boundary regular-value hypothesis can be read directly at a
boundary subtype point. -/
theorem boundary_regular_value_surjective_mfderivWithin_at_subtype_point
    {F : M → N} {c : N} {x : ↥(I.boundary M)}
    (hBoundary : IsBoundaryRegularValue I J F c)
    (hx : (fun y : ↥(I.boundary M) ↦ F y) x = c) :
    Function.Surjective (mfderivWithin I J F (I.boundary M) (x : M)) := by
  -- Reinterpret the subtype equation as the ambient fiber equation and apply the definition.
  exact hBoundary x x.2 <| by simpa using hx

/-- Helper for Problem 5-23: every boundary slice chart comes with explicit half-slice data for
its image of the distinguished subset. -/
theorem exists_half_slice_description_of_isBoundarySliceChart
    {S : Set M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (he : e.IsBoundarySliceChart S levelDim) :
    ∃ hk : 0 < levelDim, ∃ hkn : levelDim ≤ Module.finrank ℝ E,
      ∃ c : Fin (Module.finrank ℝ E - levelDim) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target levelDim hk hkn c := by
  -- Unpack the definition of `IsBoundarySliceChart`; the needed half-slice data is exactly its
  -- second component.
  simpa [OpenPartialHomeomorph.IsBoundarySliceChart, Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice]
    using he.2

/-- Helper for Problem 5-23: if the chart image of `S` is a Euclidean half-slice and the chart
center lands on the frontier of that half-slice, then the ambient point already lies on the
frontier of `S`. -/
theorem mem_frontier_of_half_slice_chart_frontier
    {S : Set M} {x : M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    {hk : 0 < levelDim} {hkn : levelDim ≤ Module.finrank ℝ E}
    {cHalf : Fin (Module.finrank ℝ E - levelDim) → ℝ}
    (hx : x ∈ e.source)
    (hHalf :
      e '' (S ∩ e.source) =
        Set.euclideanHalfSlice e.target levelDim hk hkn cHalf)
    (hxFrontier :
      e x ∈ frontier (Set.euclideanHalfSlice e.target levelDim hk hkn cHalf)) :
    x ∈ frontier S := by
  have hxFrontierImage : e x ∈ frontier (e '' (S ∩ e.source)) := by
    -- First rewrite the half-slice frontier witness back to the actual chart image of `S`.
    simpa [hHalf] using hxFrontier
  have hxPreimageFrontier :
      x ∈ e.source ∩ frontier (e ⁻¹' (e '' (S ∩ e.source))) := by
    -- Pull the frontier witness back through the open partial homeomorphism on its source.
    rw [← e.preimage_frontier (e '' (S ∩ e.source))]
    exact ⟨hx, hxFrontierImage⟩
  have hPreimageImage :
      e.source ∩ e ⁻¹' (e '' (S ∩ e.source)) = S ∩ e.source := by
    ext y
    constructor
    · rintro ⟨hySource, hyImage⟩
      rcases hyImage with ⟨z, hz, hzEq⟩
      have hyz : y = z := by
        calc
          y = e.symm (e y) := by exact (e.left_inv hySource).symm
          _ = e.symm (e z) := by simpa [hzEq]
          _ = z := e.left_inv hz.2
      exact hyz.symm ▸ hz
    · intro hy
      exact ⟨hy.2, ⟨y, hy, rfl⟩⟩
  have hxLocalFrontier : x ∈ frontier (S ∩ e.source) := by
    -- Localize the frontier computation to the open source neighborhood of the chart.
    have hxInter :
        x ∈ frontier (e ⁻¹' (e '' (S ∩ e.source))) ∩ e.source := by
      exact ⟨hxPreimageFrontier.2, hxPreimageFrontier.1⟩
    have hLocalize :
        frontier (e ⁻¹' (e '' (S ∩ e.source))) ∩ e.source =
          frontier (S ∩ e.source) ∩ e.source := by
      rw [← frontier_inter_open_inter (s := e ⁻¹' (e '' (S ∩ e.source))) e.open_source]
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc, hPreimageImage]
    have hxInter' : x ∈ frontier (S ∩ e.source) ∩ e.source := by
      rwa [hLocalize] at hxInter
    exact hxInter'.1
  -- Finally forget the open source restriction: frontier in an open neighborhood is ambient
  -- frontier at points of that neighborhood.
  have hxInterSource : x ∈ frontier (S ∩ e.source) ∩ e.source := ⟨hxLocalFrontier, hx⟩
  have hAmbientize :
      frontier (S ∩ e.source) ∩ e.source = frontier S ∩ e.source := by
    rw [frontier_inter_open_inter (s := S) e.open_source]
  have hxAmbient : x ∈ frontier S ∩ e.source := by
    rwa [hAmbientize] at hxInterSource
  exact hxAmbient.1

/-- Helper for Problem 5-23: a boundary patch must remember not only an ambient half-slice chart,
but also that the distinguished point lands on the boundary frontier of that half-slice. -/
abbrev BoundaryCenteredHalfSliceChartData (S : Set M) (x : M) : Prop :=
  ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
    x ∈ e.source ∧ e.IsBoundarySliceChart S levelDim ∧
      ∃ hk : 0 < levelDim, ∃ hkn : levelDim ≤ Module.finrank ℝ E,
        ∃ c : Fin (Module.finrank ℝ E - levelDim) → ℝ,
          e '' (S ∩ e.source) = Set.euclideanHalfSlice e.target levelDim hk hkn c ∧
            e x ∈ frontier (Set.euclideanHalfSlice e.target levelDim hk hkn c)

/-- Helper for Problem 5-23: at an interior fiber point, the regular-value data restricts to the
canonical open interior subtype on which Lee's ordinary boundaryless argument should run. -/
theorem interior_open_subtype_regular_value_data
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    {x : M} (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∉ I.boundary M) :
    let U : TopologicalSpace.Opens M :=
      I.interiorOpens M (show (⊤ : WithTop ℕ∞) ≠ 0 by simp)
    ∃ xU : U,
      (fun y : U ↦ F y) xU = c ∧
        ContMDiff I J ∞ (fun y : U ↦ F y) ∧
        IsRegularValue I J (fun y : U ↦ F y) c := by
  let U : TopologicalSpace.Opens M :=
    I.interiorOpens M (show (⊤ : WithTop ℕ∞) ≠ 0 by simp)
  have hxU : x ∈ (U : Set M) :=
    mem_interiorOpens_of_not_mem_boundary (I := I) (M := M) hxBoundary
  let xU : U := ⟨x, hxU⟩
  have hxUPreimage : xU ∈ (fun y : U ↦ F y) ⁻¹' ({c} : Set N) :=
    (open_subtype_mem_preimage_singleton_iff (U := U) (F := F) (c := c) (y := xU)).2 hx
  have hxUFiber : (fun y : U ↦ F y) xU = c := by
    -- Rewrite the restricted fiber-membership statement as the actual equation `F x = c`.
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxUPreimage
  refine ⟨xU, hxUFiber, ?_, ?_⟩
  · -- Smoothness survives restriction to the canonical open interior subtype.
    exact contMDiff_open_subtype_restriction (I := I) (J := J) (F := F) hF
  · -- Regularity also survives restriction because the open-subtype inclusion has invertible
    -- derivative.
    exact
      open_subtype_restriction_isRegularValue
        (I := I) (J := J) (U := U) (F := F) (c := c) hF hc

/-- Helper for Problem 5-23: at a boundary fiber point, the boundary regular-value hypothesis
already gives the subtype fiber equation and the ambient within-derivative surjectivity that the
boundary branch must feed into its half-slice normal form. -/
theorem boundary_subtype_regular_value_data
    {F : M → N} {c : N}
    (hBoundary : IsBoundaryRegularValue I J F c)
    {x : M} (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∈ I.boundary M) :
    let xBoundary : ↥(I.boundary M) := ⟨x, hxBoundary⟩
    (fun y : ↥(I.boundary M) ↦ F y) xBoundary = c ∧
      Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
  let xBoundary : ↥(I.boundary M) := ⟨x, hxBoundary⟩
  have hxBoundaryPreimage :
      xBoundary ∈ (fun y : ↥(I.boundary M) ↦ F y) ⁻¹' ({c} : Set N) :=
    (boundary_subtype_mem_preimage_singleton_iff (I := I) (F := F) (c := c)
      (y := xBoundary)).2 hx
  have hxBoundaryFiber : (fun y : ↥(I.boundary M) ↦ F y) xBoundary = c := by
    -- Rewrite the boundary-subtype fiber membership statement as the actual equation `F x = c`.
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxBoundaryPreimage
  have hxWithinSurj :
      Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
    -- The boundary regular-value hypothesis already gives surjectivity at the chosen fiber point.
    simpa [xBoundary] using
      boundary_regular_value_surjective_mfderivWithin_at_subtype_point
        (I := I) (J := J) (F := F) (c := c) hBoundary hxBoundaryFiber
  exact ⟨hxBoundaryFiber, hxWithinSurj⟩

/-- Helper for Problem 5-23: an interior fiber point can be localized simultaneously to the
ambient interior and to a single target chart around `c`, while preserving the restricted
regular-value data needed for Lee's boundaryless branch. -/
theorem interior_open_subtype_target_chart_data
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    {x : M} (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∉ I.boundary M) :
    let chartSource : Opens N := ⟨(chartAt H' c).source, (chartAt H' c).open_source⟩
    let U : Opens M :=
      ⟨I.interior M ∩ F ⁻¹' (chartSource : Set N),
        I.isOpen_interior.inter (chartSource.2.preimage hF.continuous)⟩
    ∃ xU : U,
      (fun y : U ↦ F y) xU = c ∧
        ContMDiff I J ∞ (fun y : U ↦ F y) ∧
        IsRegularValue I J (fun y : U ↦ F y) c := by
  let chartSource : Opens N := ⟨(chartAt H' c).source, (chartAt H' c).open_source⟩
  let U : Opens M :=
    ⟨I.interior M ∩ F ⁻¹' (chartSource : Set N),
      I.isOpen_interior.inter (chartSource.2.preimage hF.continuous)⟩
  have hxU : x ∈ (U : Set M) := by
    -- The chosen fiber point lies both in the ambient interior and in the source of the target
    -- chart centered at `c`.
    refine ⟨mem_interiorOpens_of_not_mem_boundary (I := I) (M := M) hxBoundary, ?_⟩
    simpa [chartSource, hx, Set.mem_preimage] using (mem_chart_source H' c)
  let xU : U := ⟨x, hxU⟩
  have hxUFiber : (fun y : U ↦ F y) xU = c := by
    -- Restricting to the smaller open subtype does not change the level-set equation.
    simpa [xU] using hx
  refine ⟨xU, hxUFiber, ?_, ?_⟩
  · -- Smoothness survives restriction to the smaller open subset.
    exact contMDiff_open_subtype_restriction (I := I) (J := J) (F := F) hF
  · -- Open-subtype restriction also preserves the regular-value condition.
    exact
      open_subtype_restriction_isRegularValue
        (I := I) (J := J) (U := U) (F := F) (c := c) hF hc

/-- Helper for Problem 5-23: the inverse of the canonical open-subtype inclusion simply restores
the ambient point together with its proof of membership in the open subset. -/
theorem open_subtype_inclusion_symm_eq_mk
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) {x : M} (hx : x ∈ U) :
    (U.openPartialHomeomorphSubtypeCoe hU).symm x = ⟨x, hx⟩ := by
  -- The open-subtype inclusion is an open partial homeomorphism with target exactly `U`, so its
  -- inverse just repackages an ambient point of `U` as the corresponding subtype point.
  apply Subtype.ext
  have hxTarget : x ∈ (U.openPartialHomeomorphSubtypeCoe hU).target := by
    simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hx
  simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
    (U.openPartialHomeomorphSubtypeCoe hU).right_inv hxTarget

/-- Helper for Problem 5-23: a slice chart on an open ambient subtype transports back to a slice
chart on the original ambient manifold. This isolates the open-subtype chart bookkeeping from the
actual local-submersion argument in Lee's interior branch. -/
theorem open_subtype_sliceChart_to_ambient
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) {S : Set M}
    {eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (heU : eU.IsSliceChart {y : U | (y : M) ∈ S} levelDim) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      ((U.openPartialHomeomorphSubtypeCoe hU).symm).trans eU
    e.IsSliceChart S levelDim := by
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ((U.openPartialHomeomorphSubtypeCoe hU).symm).trans eU
  refine ⟨?_, ?_⟩
  · -- Test maximal-atlas compatibility against the ambient preferred charts, then restrict those
    -- charts to the open subtype so the known subtype chart can be used.
    rw [IsManifold.mem_maximalAtlas_iff]
    intro c hc
    have hcU :
        c.subtypeRestr hU ∈
          IsManifold.maximalAtlas (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) U := by
      simpa [IsManifold.maximalAtlas] using
        (StructureGroupoid.subtypeRestr_mem_maximalAtlas
          (G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (Module.finrank ℝ E))) hc hU)
    constructor
    · -- After transporting through the open inclusion, the left transition is exactly the subtype
      -- transition already controlled by `heU`.
      have hleftU :
          eU.symm.trans (c.subtypeRestr hU) ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (Module.finrank ℝ E)) := by
        exact IsManifold.compatible_of_mem_maximalAtlas heU.1 hcU
      simpa [e, OpenPartialHomeomorph.subtypeRestr_def,
        OpenPartialHomeomorph.trans_assoc,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using hleftU
    · -- The right transition is the same subtype transition, read in the opposite direction.
      have hrightU :
          (c.subtypeRestr hU).symm.trans eU ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (Module.finrank ℝ E)) := by
        exact IsManifold.compatible_of_mem_maximalAtlas hcU heU.1
      simpa [e, OpenPartialHomeomorph.subtypeRestr_def,
        OpenPartialHomeomorph.trans_assoc,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using hrightU
  · rcases heU.2 with ⟨hkn, cSlice, hSliceImage⟩
    refine ⟨hkn, cSlice, ?_⟩
    have hImage :
        e '' (S ∩ e.source) =
          eU '' ({y : U | (y : M) ∈ S} ∩ eU.source) := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyS, hySource⟩, rfl⟩
        rw [OpenPartialHomeomorph.trans_source] at hySource
        exact ⟨((U.openPartialHomeomorphSubtypeCoe hU).symm y),
          ⟨hyS, hySource.2⟩, rfl⟩
      · rintro ⟨y, ⟨hyS, hySource⟩, rfl⟩
        have hyU : (y : M) ∈ U := y.2
        have hyEq :
            (U.openPartialHomeomorphSubtypeCoe hU).symm (y : M) = y := by
          simpa using
            open_subtype_inclusion_symm_eq_mk
              (I := I) (U := U) hU (x := (y : M)) hyU
        have hyAmbientSource : (y : M) ∈ e.source := by
          rw [OpenPartialHomeomorph.trans_source]
          refine ⟨?_, ?_⟩
          · simpa using hyU
          · simpa [hyEq] using hySource
        exact ⟨(y : M), ⟨hyS, hyAmbientSource⟩, by simpa [e, hyEq]⟩
    -- The chart target is unchanged because the open inclusion inverse has full target `univ`.
    calc
      e '' (S ∩ e.source) = eU '' ({y : U | (y : M) ∈ S} ∩ eU.source) := hImage
      _ = Set.euclideanSlice eU.target levelDim hkn cSlice := hSliceImage
      _ = Set.euclideanSlice e.target levelDim hkn cSlice := by
        simp [e, OpenPartialHomeomorph.trans_target,
          TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]

/-- Helper for Problem 5-23: once Lee's interior branch has been localized to a boundaryless open
subtype on which the restricted map still has `c` as a regular value, the remaining task is to
extract the actual slice chart on that open subtype. -/
theorem embedded_regular_preimage_on_boundaryless_open_has_slice_chart
    {U : TopologicalSpace.Opens M} [BoundarylessManifold I U]
    {F : M → N} {c : N} {xU : U}
    (hxUFiber : (fun y : U ↦ F y) xU = c)
    (hEmbedded :
      ∃ tm : TopologicalManifold levelDim ((fun y : U ↦ F y) ⁻¹' {c}),
        let _ : TopologicalManifold levelDim ((fun y : U ↦ F y) ⁻¹' {c}) := tm
        ∃ hs : IsManifold (𝓡 levelDim) (⊤ : WithTop ℕ∞) ((fun y : U ↦ F y) ⁻¹' {c}),
          let _ : IsManifold (𝓡 levelDim) (⊤ : WithTop ℕ∞) ((fun y : U ↦ F y) ⁻¹' {c}) := hs
          IsEmbeddedSubmanifold
            (𝓡 (Module.finrank ℝ E))
            (𝓡 levelDim)
            ((fun y : U ↦ F y) ⁻¹' {c})) :
    ∃ eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      xU ∈ eU.source ∧ eU.IsSliceChart ((fun y : U ↦ F y) ⁻¹' {c}) levelDim := by
  let SU : Set U := (fun y : U ↦ F y) ⁻¹' {c}
  have hxUS : xU ∈ SU := by
    -- The chosen base point already lies in the restricted fiber, so it is a valid center for the
    -- slice chart extracted from the embedded-submanifold structure.
    simpa [SU, Set.mem_preimage, Set.mem_singleton_iff] using hxUFiber
  have hSliceCondition :
      Set.SatisfiesLocalSliceCondition
        (Module.finrank ℝ E) SU levelDim := by
    -- Theorem 5.8 turns the embedded-submanifold owner on the restricted fiber into Lee's local
    -- slice condition on the same open subtype.
    exact
      (local_slice_criterion_for_embedded_submanifold
        (n := Module.finrank ℝ E) (k := levelDim) (M := U) (S := SU)).2 hEmbedded
  -- Once the local slice condition is available, read off the centered ambient slice chart at the
  -- distinguished fiber point `xU`.
  simpa [SU] using hSliceCondition.exists_sliceChart xU hxUS

/-- Helper for Problem 5-23: once the restricted map lands inside a single target chart around
`c`, composing with that chart and a fixed Euclidean linear identification preserves smoothness. -/
theorem target_chart_coordinate_restriction_contMDiff
    {U : TopologicalSpace.Opens M} {F : M → N} {c : N}
    (hFRestricted : ContMDiff I J ∞ (fun y : U ↦ F y))
    (hSource : ∀ y : U, F y ∈ (chartAt H' c).source) :
    let b' : Module.Basis (Fin (Module.finrank ℝ E')) ℝ E' := FiniteDimensional.finBasis ℝ E'
    ContMDiff I (𝓡 (Module.finrank ℝ E')) ∞
      (fun y : U ↦
        ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y))) := by
  let b' : Module.Basis (Fin (Module.finrank ℝ E')) ℝ E' := FiniteDimensional.finBasis ℝ E'
  intro y
  -- Smoothness of the restricted map supplies the first leg of the coordinate expression.
  have hFAt : ContMDiffAt I J ∞ (fun z : U ↦ F z) y :=
    hFRestricted.contMDiffAt
  -- On the chosen chart-source neighborhood, the target extended chart is smooth.
  have hChartAt : ContMDiffAt J (𝓘(ℝ, E')) ∞ (extChartAt J c) (F y) :=
    contMDiffAt_extChartAt' (I := J) (x := c) (hSource y)
  -- The fixed basis-model change on `E'` is a global diffeomorphism, hence smooth.
  have hBasisAt :
      ContMDiffAt (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E')) ∞
        ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y)) := by
    simpa [b'] using
      (((basis_model_diffeomorph (E := E') b').symm).contMDiff.contMDiffAt :
        ContMDiffAt (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E')) ∞
          ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y)))
  -- Compose the three smooth pieces in the source-faithful target coordinates.
  exact hBasisAt.comp y (hChartAt.comp y hFAt)

/-- Helper for Problem 5-23: once the restricted map lands inside a single target chart around
`c`, the corresponding Euclidean target-coordinate expression has surjective manifold derivative
at the fiber point. -/
theorem target_chart_coordinate_restriction_surjective_mfderiv
    {U : TopologicalSpace.Opens M} {F : M → N} {c : N} {xU : U}
    (hxUFiber : (fun y : U ↦ F y) xU = c)
    (hFRestricted : ContMDiff I J ∞ (fun y : U ↦ F y))
    (hcRestricted : IsRegularValue I J (fun y : U ↦ F y) c)
    (hSource : ∀ y : U, F y ∈ (chartAt H' c).source) :
    let b' : Module.Basis (Fin (Module.finrank ℝ E')) ℝ E' := FiniteDimensional.finBasis ℝ E'
    Function.Surjective
      (mfderiv I (𝓡 (Module.finrank ℝ E'))
        (fun y : U ↦
          ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y))) xU) := by
  let b' : Module.Basis (Fin (Module.finrank ℝ E')) ℝ E' := FiniteDimensional.finBasis ℝ E'
  -- Start from the regular-value surjectivity for the restricted map itself.
  have hFSurj : Function.Surjective (mfderiv I J (fun y : U ↦ F y) xU) :=
    hcRestricted xU hxUFiber
  have hFDiff : MDifferentiableAt I J (fun y : U ↦ F y) xU := by
    -- The restricted map is smooth, hence differentiable at the chosen fiber point.
    exact hFRestricted.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  -- The target extended chart at `c` has invertible derivative at the center.
  have hChartDiff : MDifferentiableAt J (𝓘(ℝ, E')) (extChartAt J c) c := by
    exact mdifferentiableAt_extChartAt (I := J) (x := c) (y := c) (mem_extChartAt_source c)
  have hChartSurj : Function.Surjective (mfderiv J (𝓘(ℝ, E')) (extChartAt J c) c) := by
    simpa using
      (isInvertible_mfderiv_extChartAt (I := J) (x := c) (y := c)
        (mem_extChartAt_source c)).surjective
  -- The fixed basis-model diffeomorphism on `E'` also has invertible derivative everywhere.
  have hBasisDiff :
      MDifferentiableAt (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E'))
        ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c c) := by
    simpa [b'] using
      (((basis_model_diffeomorph (E := E') b').symm).contMDiff.mdifferentiableAt
        (show (∞ : WithTop ℕ∞) ≠ 0 by simp) :
        MDifferentiableAt (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E'))
          ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c c))
  have hBasisSurj :
      Function.Surjective
        (mfderiv (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E'))
          ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c c)) := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      ((basis_model_diffeomorph (E := E') b').symm) one_ne_zero (x := extChartAt J c c)]
    exact
      (((basis_model_diffeomorph (E := E') b').symm).mfderivToContinuousLinearEquiv one_ne_zero
        (extChartAt J c c)).surjective
  -- First compose with the target chart.
  have hCoordDiff :
      MDifferentiableAt I (𝓘(ℝ, E')) (fun y : U ↦ extChartAt J c (F y)) xU := by
    exact hChartDiff.comp xU hFDiff
  have hCoordEq :
      mfderiv I (𝓘(ℝ, E')) (fun y : U ↦ extChartAt J c (F y)) xU =
        (mfderiv J (𝓘(ℝ, E')) (extChartAt J c) c).comp
          (mfderiv I J (fun y : U ↦ F y) xU) := by
    simpa [hxUFiber, Function.comp] using mfderiv_comp xU hChartDiff hFDiff
  have hCoordSurj :
      Function.Surjective
        (mfderiv I (𝓘(ℝ, E')) (fun y : U ↦ extChartAt J c (F y)) xU) := by
    simpa [hCoordEq] using hChartSurj.comp hFSurj
  -- Then postcompose by the fixed Euclidean linear identification.
  have hBasisEq :
      mfderiv I (𝓡 (Module.finrank ℝ E'))
          (fun y : U ↦
            ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y))) xU =
        (mfderiv (𝓘(ℝ, E')) (𝓡 (Module.finrank ℝ E'))
            ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c c)).comp
          (mfderiv I (𝓘(ℝ, E')) (fun y : U ↦ extChartAt J c (F y)) xU) := by
    simpa [hxUFiber, Function.comp] using mfderiv_comp xU hBasisDiff hCoordDiff
  -- Surjectivity is preserved through both coordinate changes.
  simpa [hBasisEq] using hBasisSurj.comp hCoordSurj

/-- Helper for Problem 5-23: once Lee's interior branch has been localized to a boundaryless open
subtype on which the restricted map still has `c` as a regular value, the remaining task is to
extract the actual slice chart on that open subtype. -/
theorem interior_regular_preimage_local_submersion_patch
    {U : TopologicalSpace.Opens M} [BoundarylessManifold I U]
    {F : M → N} {c : N} {xU : U}
    (hxUFiber : (fun y : U ↦ F y) xU = c)
    (hFRestricted : ContMDiff I J ∞ (fun y : U ↦ F y))
    (hcRestricted : IsRegularValue I J (fun y : U ↦ F y) c) :
    ∃ V : TopologicalSpace.Opens U, ∃ xV : V,
      ∃ Φ : V → EuclideanSpace ℝ (Fin (Module.finrank ℝ E')),
        ∃ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E')),
          xV.1 = xU ∧
            Φ xV = z ∧
            Manifold.IsSmoothSubmersion I (𝓡 (Module.finrank ℝ E')) Φ ∧
            ((fun y : V ↦ Φ y) ⁻¹' ({z} : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E')))) =
              {y : V | (fun q : U ↦ F q) y = c}) := by
  -- Route correction: the interior proof should not try to build a global embedded owner on all
  -- of `U`. The source-faithful frontier is a smaller open patch `V` where fixed target
  -- coordinates turn the restricted map into a smooth submersion with the same local fiber.
  let chartSource : TopologicalSpace.Opens N := ⟨(chartAt H' c).source, (chartAt H' c).open_source⟩
  let W : TopologicalSpace.Opens U :=
    ⟨(fun y : U ↦ F y) ⁻¹' (chartSource : Set N),
      chartSource.2.preimage hFRestricted.continuous⟩
  have hxW : xU ∈ W := by
    -- The base fiber point lands in the chosen target chart because `F xU = c`.
    simpa [W, chartSource, hxUFiber, Set.mem_preimage] using (mem_chart_source H' c)
  let xW : W := ⟨xU, hxW⟩
  have hxWFiber : (fun y : W ↦ F y) xW = c := by
    -- Restricting from `U` to the chart-source patch `W` does not change the fiber equation.
    simpa [xW] using hxUFiber
  have hFW : ContMDiff I J ∞ (fun y : W ↦ F y) := by
    -- Smoothness survives the further restriction from `U` to the chart-source patch `W`.
    exact
      contMDiff_open_subtype_restriction
        (I := I) (J := J) (F := fun y : U ↦ F y) hFRestricted
  have hcW : IsRegularValue I J (fun y : W ↦ F y) c := by
    -- The regular-value condition also survives the further restriction to `W`.
    exact
      open_subtype_restriction_isRegularValue
        (I := I) (J := J) (U := W) (F := fun y : U ↦ F y) hFRestricted hcRestricted
  have hWSource : ∀ y : W, F y ∈ (chartAt H' c).source := by
    -- Membership in `W` is exactly the target-chart source condition.
    intro y
    exact y.2
  let b' : Module.Basis (Fin (Module.finrank ℝ E')) ℝ E' := FiniteDimensional.finBasis ℝ E'
  let Ψ : W → EuclideanSpace ℝ (Fin (Module.finrank ℝ E')) :=
    fun y ↦ ((basis_model_diffeomorph (E := E') b').symm) (extChartAt J c (F y))
  have hΨSmooth : ContMDiff I (𝓡 (Module.finrank ℝ E')) ∞ Ψ := by
    -- The Euclidean target-coordinate expression is smooth on the whole chart-source patch `W`.
    simpa [Ψ, b'] using
      target_chart_coordinate_restriction_contMDiff
        (I := I) (J := J) (F := F) (c := c) hFW hWSource
  have hΨSurj :
      Function.Surjective (mfderiv I (𝓡 (Module.finrank ℝ E')) Ψ xW) := by
    -- At the base fiber point, the target-coordinate expression still has surjective derivative.
    simpa [Ψ, b'] using
      target_chart_coordinate_restriction_surjective_mfderiv
        (I := I) (J := J) (F := F) (c := c) (xU := xW) hxWFiber hFW hcW hWSource
  rcases
      exists_open_neighborhood_surjective_mfderiv
        (I := I) (Φ := Ψ) (x := xW) hΨSmooth hΨSurj with
    ⟨Vw, hxVw, hVwSurj⟩
  have _ := Vw
  have _ := hxVw
  have _ := hVwSurj
  -- TODO: convert the smaller open `Vw : Opens W` back into an `Opens U` witness, transport the
  -- Euclidean coordinate map `Ψ` along that open inclusion, and then package the resulting
  -- restricted submersion together with the level-set equality on the transported ambient patch.
  sorry

/-- Helper for Problem 5-23: once Lee's interior branch has been reduced to a smaller open
submersion patch, Corollary 5.13 produces the embedded fiber there and the existing open-subtype
transport closes the ambient slice-chart statement on `U`. -/
theorem boundaryless_open_subtype_regular_preimage_has_slice_chart
    {U : TopologicalSpace.Opens M} [BoundarylessManifold I U]
    {F : M → N} {c : N} {xU : U}
    (hxUFiber : (fun y : U ↦ F y) xU = c)
    (hFRestricted : ContMDiff I J ∞ (fun y : U ↦ F y))
    (hcRestricted : IsRegularValue I J (fun y : U ↦ F y) c) :
    ∃ eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      xU ∈ eU.source ∧ eU.IsSliceChart ((fun y : U ↦ F y) ⁻¹' {c}) levelDim := by
  -- Route correction: the interior work is now isolated to a smaller open submersion patch `V`.
  -- Once that patch is provided, Corollary 5.13 plus the existing transport lemmas finish the
  -- ambient slice chart on `U`.
  rcases
      interior_regular_preimage_local_submersion_patch
        (I := I) (J := J) (F := F) (c := c) (xU := xU)
        hxUFiber hFRestricted hcRestricted with
    ⟨V, xV, Φ, z, hxV, hΦxV, hΦSubmersion, hLevel⟩
  letI : BoundarylessManifold I V := inferInstance
  have hEmbeddedV :
      ∃ tm : TopologicalManifold levelDim ((fun y : V ↦ Φ y) ⁻¹' {z}),
        let _ : TopologicalManifold levelDim ((fun y : V ↦ Φ y) ⁻¹' {z}) := tm
        ∃ hs : IsManifold (𝓡 levelDim) (⊤ : WithTop ℕ∞) ((fun y : V ↦ Φ y) ⁻¹' {z}),
          let _ : IsManifold (𝓡 levelDim) (⊤ : WithTop ℕ∞) ((fun y : V ↦ Φ y) ⁻¹' {z}) := hs
          IsEmbeddedSubmanifold
            (𝓡 (Module.finrank ℝ E))
            (𝓡 levelDim)
            ((fun y : V ↦ Φ y) ⁻¹' {z}) := by
    -- Corollary 5.13 gives the embedded structure on the localized zero fiber of the smooth
    -- submersion `Φ`.
    simpa [levelDim] using
      smooth_submersion_level_set_has_embedded_submanifold_structure
        (I := I) (J := 𝓡 (Module.finrank ℝ E')) (Φ := Φ) hΦSubmersion z
  rcases
      embedded_regular_preimage_on_boundaryless_open_has_slice_chart
        (I := I) (J := 𝓡 (Module.finrank ℝ E')) (F := Φ) (c := z) (xU := xV)
        hΦxV hEmbeddedV with
    ⟨eV, hxVSource, heV⟩
  have heVLevel :
      eV.IsSliceChart {y : V | (fun q : U ↦ F q) y = c} levelDim := by
    -- Rewrite the local fiber through the explicit equality provided by the submersion patch.
    simpa [hLevel] using heV
  let eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ((V.openPartialHomeomorphSubtypeCoe ⟨xV⟩).symm).trans eV
  have heU :
      eU.IsSliceChart ((fun y : U ↦ F y) ⁻¹' ({c} : Set N)) levelDim := by
    -- Transport the slice chart from `V` back to the original open subtype `U`.
    simpa [eU, Set.mem_preimage, Set.mem_singleton_iff] using
      (open_subtype_sliceChart_to_ambient
        (I := I) (U := V) (hU := ⟨xV⟩)
        (S := ((fun y : U ↦ F y) ⁻¹' ({c} : Set N))) heVLevel)
  refine ⟨eU, ?_, heU⟩
  have hxEq :
      (V.openPartialHomeomorphSubtypeCoe ⟨xV⟩).symm xU = xV := by
    -- The inverse of the open-subtype inclusion simply restores the distinguished point `xV`.
    simpa [hxV] using
      open_subtype_inclusion_symm_eq_mk
        (I := I) (U := V) ⟨xV⟩ (x := xU) xV.2
  -- The transported ambient chart is defined at `xU` because `xV` lies in the local source.
  rw [eU, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · simpa [hxV] using xV.2
  · simpa [hxEq] using hxVSource

/-- Helper for Problem 5-23: at a boundary fiber point, surjectivity of the ambient derivative
and of the boundary within-derivative should package directly into the frontier-centered ambient
half-slice chart used in Lee's boundary branch. -/
theorem regular_preimage_boundary_point_has_centered_half_slice_from_derivatives
    {F : M → N} {c : N} {x : M}
    (hF : ContMDiff I J ∞ F)
    (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∈ I.boundary M)
    (hxAmbientSurj : Function.Surjective (mfderiv I J F x))
    (hxWithinSurj : Function.Surjective (mfderivWithin I J F (I.boundary M) x)) :
    BoundaryCenteredHalfSliceChartData (F ⁻¹' {c}) x := by
  -- Route correction: the remaining boundary work is now isolated to one ambient half-space model
  -- theorem. The intended source-faithful closure is to straighten `F` in one boundary chart,
  -- use the two surjectivity hypotheses to obtain a centered half-slice normal form, and then
  -- conjugate that model chart back to `M`.
  -- TODO: choose one ambient boundary chart and one target chart, prove the half-space model
  -- normal form at `x`, and package the resulting ambient chart together with the frontier
  -- witness required by `BoundaryCenteredHalfSliceChartData`.
  have _ := hF
  have _ := hx
  have _ := hxBoundary
  have _ := hxAmbientSurj
  have _ := hxWithinSurj
  sorry

/-- Helper for Problem 5-23: Lee's local normal-form proof splits the regular fiber into two
branches. At an interior fiber point one gets an ordinary slice chart, while at a boundary fiber
point one gets a half-slice chart in the same ambient manifold. -/
theorem regular_preimage_interior_point_has_slice_chart
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c)
    {x : M} (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∉ I.boundary M) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim := by
  -- Route correction: keep Lee's interior branch separate. The remaining work is to shrink to an
  -- open neighborhood inside `I.interior M` and invoke the ordinary regular-value level-set
  -- theorem there, rather than mixing this branch with the boundary restriction argument.
  have hInteriorSlice :
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim := by
    let chartSource : Opens N := ⟨(chartAt H' c).source, (chartAt H' c).open_source⟩
    let U : Opens M :=
      ⟨I.interior M ∩ F ⁻¹' (chartSource : Set N),
        I.isOpen_interior.inter (chartSource.2.preimage hF.continuous)⟩
    have hLocalized :
        ∃ xU : U,
          (fun y : U ↦ F y) xU = c ∧
            ContMDiff I J ∞ (fun y : U ↦ F y) ∧
            IsRegularValue I J (fun y : U ↦ F y) c := by
      -- First isolate the boundaryless interior branch on an open set that also keeps the chosen
      -- target chart around `c` available.
      simpa [chartSource, U] using
        interior_open_subtype_target_chart_data
          (I := I) (J := J) (F := F) (c := c) hF hc hx hxBoundary
    rcases hLocalized with ⟨xU, hxUFiber, hFRestricted, hcRestricted⟩
    have hUInterior : (U : Set M) ⊆ I.interior M := by
      intro y hy
      exact hy.1
    letI : BoundarylessManifold I U :=
      open_subset_of_interior_boundaryless (I := I) U hUInterior
    have hTransport :
        (∃ eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          xU ∈ eU.source ∧ eU.IsSliceChart ((fun y : U ↦ F y) ⁻¹' {c}) levelDim) →
          ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
            x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim := by
      intro hLocalSlice
      rcases hLocalSlice with ⟨eU, hxUSource, heU⟩
      let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
        ((U.openPartialHomeomorphSubtypeCoe ⟨xU⟩).symm).trans eU
      refine ⟨e, ?_, ?_⟩
      · -- The transported ambient chart is defined at `x` because the open inclusion inverse sends
        -- `x` back to the distinguished subtype point `xU`.
        have hxEq :
            (U.openPartialHomeomorphSubtypeCoe ⟨xU⟩).symm x = xU := by
          simpa [xU] using
            open_subtype_inclusion_symm_eq_mk
              (I := I) (U := U) ⟨xU⟩ (x := x) xU.2
        rw [e, OpenPartialHomeomorph.trans_source]
        exact ⟨xU.2, by simpa [hxEq] using hxUSource⟩
      · -- Once the local slice chart exists on the open subtype, the previous transport lemma
        -- turns it into the desired ambient slice chart for the full fiber.
        simpa [e, open_subtype_mem_preimage_singleton_iff] using
          open_subtype_sliceChart_to_ambient
            (I := I) (U := U) ⟨xU⟩ (S := F ⁻¹' {c}) heU
    -- TODO: the remaining interior branch is now reduced to a sharper local problem on the
    -- boundaryless open subtype `U`: use the fixed target chart around `c` to turn the restricted
    -- map into a Euclidean-valued local submersion near `xU`, produce a slice chart on `U`, and
    -- then feed that chart into `hTransport`.
    have hLocalSliceOnU :
        ∃ eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          xU ∈ eU.source ∧ eU.IsSliceChart ((fun y : U ↦ F y) ⁻¹' {c}) levelDim := by
      -- The open-subtype transport is already isolated, so invoke the dedicated boundaryless
      -- local extraction helper for the remaining source-faithful interior step.
      exact
        boundaryless_open_subtype_regular_preimage_has_slice_chart
          (I := I) (J := J) (F := F) (c := c) (xU := xU)
          hxUFiber hFRestricted hcRestricted
    exact hTransport hLocalSliceOnU
  -- The interior branch is reduced to the boundaryless-open-subset slice extraction above.
  exact hInteriorSlice

/-- Helper for Problem 5-23: at a boundary point of the regular fiber, Lee's proof passes to the
boundary restriction and then lifts the resulting slice chart back to an ambient half-slice chart.
-/
theorem regular_preimage_boundary_point_has_boundary_slice_chart
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c)
    {x : M} (hx : x ∈ F ⁻¹' {c}) (hxBoundary : x ∈ I.boundary M) :
    BoundaryCenteredHalfSliceChartData (F ⁻¹' {c}) x := by
  -- Route correction: keep Lee's boundary branch separate. The open work is to use the canonical
  -- boundary manifold owner on `↥(I.boundary M)`, prove that `c` is a regular value of the
  -- boundary restriction, obtain a slice chart there, and lift it to an ambient half-slice chart
  -- centered on the boundary hyperplane.
  have hBoundaryHalfSlice :
      BoundaryCenteredHalfSliceChartData (F ⁻¹' {c}) x := by
    let xBoundary : ↥(I.boundary M) := ⟨x, hxBoundary⟩
    have hBoundaryData :
        (fun y : ↥(I.boundary M) ↦ F y) xBoundary = c ∧
          Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
      -- First isolate the exact boundary-fiber equation and ambient within-surjectivity data that
      -- any direct half-slice normal-form argument must consume.
      simpa [xBoundary] using
        boundary_subtype_regular_value_data
          (I := I) (J := J) (F := F) (c := c) hBoundary hx hxBoundary
    have hxBoundaryFiber : (fun y : ↥(I.boundary M) ↦ F y) xBoundary = c := hBoundaryData.1
    have hxWithinSurj :
        Function.Surjective (mfderivWithin I J F (I.boundary M) x) := hBoundaryData.2
    have hxAmbientSurj : Function.Surjective (mfderiv I J F x) := by
      -- The ambient regular-value hypothesis gives the full surjective derivative at the chosen
      -- fiber point.
      exact hc x <| by simpa using hx
    -- The intrinsic-boundary bookkeeping is now finished; invoke the dedicated ambient half-slice
    -- packaging helper for the remaining source-faithful boundary step.
    have _ := xBoundary
    have _ := hxBoundaryFiber
    exact
      regular_preimage_boundary_point_has_centered_half_slice_from_derivatives
        (I := I) (J := J) (F := F) (c := c) (x := x)
        hF hx hxBoundary hxAmbientSurj hxWithinSurj
  -- The boundary branch is reduced to the intrinsic-boundary slice lift above.
  exact hBoundaryHalfSlice

/-- Helper for Problem 5-23: Lee's local normal-form proof splits the regular fiber into two
branches. At an interior fiber point one gets an ordinary slice chart, while at a boundary fiber
point one gets a half-slice chart in the same ambient manifold. -/
theorem regular_preimage_has_local_slice_or_boundary_slice_chart
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c) :
    ∀ x : M, x ∈ F ⁻¹' {c} →
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        x ∈ e.source ∧
          (x ∉ I.boundary M ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim ∨
            x ∈ I.boundary M ∧ e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim) := by
  intro x hx
  -- Route correction: the source proof really has two separate branches, so package the wrapper
  -- theorem by a direct split on whether `x` lies in the ambient boundary.
  by_cases hxBoundary : x ∈ I.boundary M
  · rcases regular_preimage_boundary_point_has_boundary_slice_chart
      (I := I) (J := J) (F := F) (c := c) hF hc hBoundary hx hxBoundary with
      ⟨e, hxSource, he, hk, hkn, cHalf, hHalfSlice, hxHalfFrontier⟩
    have _ := hk
    have _ := hkn
    have _ := cHalf
    have _ := hHalfSlice
    have _ := hxHalfFrontier
    exact ⟨e, hxSource, Or.inr ⟨hxBoundary, he⟩⟩
  · rcases regular_preimage_interior_point_has_slice_chart
      (I := I) (J := J) (F := F) (c := c) hF hc hBoundary hx hxBoundary with
      ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inl ⟨hxBoundary, he⟩⟩

/-- Helper for Problem 5-23: source-faithful interior patch data for the regular fiber. Each
interior fiber point admits a single ambient slice chart for the whole regular fiber. -/
abbrev RegularPreimageInteriorPatchData (F : M → N) (c : N) : Prop :=
  ∀ x : M, x ∈ F ⁻¹' {c} → x ∉ I.boundary M →
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim

/-- Helper for Problem 5-23: source-faithful boundary patch data for the regular fiber. Each
boundary fiber point admits a single ambient half-slice chart for the whole regular fiber, with
the distinguished point placed on the half-slice frontier. -/
abbrev RegularPreimageBoundaryPatchData (F : M → N) (c : N) : Prop :=
  ∀ x : M, x ∈ F ⁻¹' {c} → x ∈ I.boundary M →
    BoundaryCenteredHalfSliceChartData (F ⁻¹' {c}) x

/-- Helper for Problem 5-23: once the regular fiber has source-faithful interior and boundary
patch data, any gluing theorem that assembles those patches into a global boundary structure
immediately yields the textbook conclusion. -/
theorem regular_preimage_has_embedded_submanifold_with_boundary_structure_of_local_models
    {F : M → N} {c : N}
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c)
    (hGlue :
      RegularPreimageInteriorPatchData (I := I) F c →
        RegularPreimageBoundaryPatchData (I := I) F c →
          ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
            letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
            IsSmoothEmbedding
              (leeBoundaryModelWithCorners levelDim)
              I
              (⊤ : WithTop ℕ∞)
              (Subtype.val : (F ⁻¹' {c}) → M) ∧
            ∀ x : (F ⁻¹' {c}),
              (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M) :
    ∃ _ : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
        IsSmoothEmbedding
            (leeBoundaryModelWithCorners levelDim)
            I
            (⊤ : WithTop ℕ∞)
            (Subtype.val : (F ⁻¹' {c}) → M) ∧
          Subtype.val '' (leeBoundaryModelWithCorners levelDim).boundary (F ⁻¹' {c}) =
            (F ⁻¹' {c}) ∩ I.boundary M := by
  -- Route correction: the old interface asked for a false global Euclidean ambient owner on all of
  -- `M`. The right frontier is a gluing theorem from local open-subtype patch data.
  rcases hGlue hInteriorPatch hBoundaryPatch with ⟨instSmooth, hEmbedding, hBoundaryPoint⟩
  letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
  refine ⟨instSmooth, hEmbedding, ?_⟩
  -- Finally translate the pointwise boundary identification into the set-theoretic boundary
  -- formula `∂(F⁻¹({c})) = F⁻¹({c}) ∩ ∂M`.
  exact
    regular_preimage_boundary_image_eq_of_boundary_point_iff
      (I := I) (F := F) (c := c) hBoundaryPoint

/-- Helper for Problem 5-23: the pointwise interior and boundary patch data already give the
Euclidean-ambient smooth-manifold-with-boundary package from Theorem 5.51 as soon as the ambient
manifold `M` is viewed in Euclidean coordinates. -/
theorem regular_preimage_patch_data_has_euclidean_embedding_structure
    [ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M]
    [IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M]
    {F : M → N} {c : N}
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c) :
    ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
      letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        (𝓡 (Module.finrank ℝ E))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M) := by
  have hBoundarySlice :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∈ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
          x ∈ e.source ∧ e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim := by
    intro x hx hxBoundary
    -- Forget only the extra frontier-centered bookkeeping before applying Theorem 5.51.
    rcases hBoundaryPatch x hx hxBoundary with ⟨e, hxSource, heHalfSlice, hk, hkn, cHalf, hEq, hxFrontier⟩
    have _ := hk
    have _ := hkn
    have _ := cHalf
    have _ := hEq
    have _ := hxFrontier
    exact ⟨e, hxSource, heHalfSlice⟩
  -- This is exactly the Euclidean ambient packaging theorem, now fed by the abstract patch-data
  -- owners used in the final gluing step.
  exact
    regular_preimage_has_euclidean_embedding_structure
      (I := I) (F := F) (c := c) hInteriorPatch hBoundarySlice

/-- Helper for Problem 5-23: the interior branch of Lee's proof should produce the interior patch
data directly on an ambient open subset of `I.interior M`, not a chart witness for a global
Euclidean ambient structure on all of `M`. -/
theorem regular_preimage_has_interior_embedded_patch
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c) :
    RegularPreimageInteriorPatchData (I := I) F c := by
  intro x hx hxBoundary
  -- First obtain the local two-branch normal form near `x`, then discard the impossible
  -- half-slice branch because `x` is assumed to lie away from `I.boundary M`.
  rcases regular_preimage_has_local_slice_or_boundary_slice_chart
      (I := I) (J := J) (F := F) (c := c) hF hc hBoundary x hx with
    ⟨e, hxSource, hLocal⟩
  rcases hLocal with ⟨_, heSlice⟩ | ⟨hxBoundary', _⟩
  · exact ⟨e, hxSource, heSlice⟩
  · exact False.elim (hxBoundary hxBoundary')

/-- Helper for Problem 5-23: the boundary branch of Lee's proof should produce the boundary patch
data directly on one ambient open neighborhood, using the intrinsic boundary restriction and a
single half-slice chart there. -/
theorem regular_preimage_has_boundary_half_slice_patch
    {F : M → N} {c : N}
    (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c) :
    RegularPreimageBoundaryPatchData (I := I) F c := by
  intro x hx hxBoundary
  -- The repaired boundary patch data now comes directly from the dedicated boundary branch,
  -- because the wrapper theorem intentionally forgets the centered half-slice witness.
  exact
    regular_preimage_boundary_point_has_boundary_slice_chart
      (I := I) (J := J) (F := F) (c := c) hF hc hBoundary hx hxBoundary

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
fixed basis-model coordinates package the regular fiber as a smoothly embedded manifold with
boundary in a Euclidean ambient model. -/
theorem regular_preimage_has_basis_model_embedding_structure
    {F : M → N} {c : N}
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c) :
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := FiniteDimensional.finBasis ℝ E
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
      letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        (𝓡 (Module.finrank ℝ E))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M) := by
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := FiniteDimensional.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  let _ : IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold (E := E) (M := M) b
  -- With the fixed basis-model instances installed, the Euclidean packaging theorem applies
  -- directly to the already prepared interior and boundary patch data.
  simpa [b] using
    regular_preimage_patch_data_has_euclidean_embedding_structure
      (I := I) (F := F) (c := c) hInteriorPatch hBoundaryPatch

/-- Helper for Problem 5-23: the Euclidean ambient embedding of the regular fiber transports back
to the original ambient model `I` via the fixed basis-model change of coordinates from
Problem 5-8. -/
theorem regular_preimage_embedding_transports_to_original_model
    {F : M → N} {c : N}
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c) :
    ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
      letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        I
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M) := by
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := FiniteDimensional.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  let _ : IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold (E := E) (M := M) b
  -- First obtain the Euclidean ambient embedding structure from the fixed basis model.
  rcases
      regular_preimage_has_basis_model_embedding_structure
        (I := I) (F := F) (c := c) hInteriorPatch hBoundaryPatch with
    ⟨instSmooth, hEmbeddingEuclid⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
  -- Then transport only the codomain model back from `𝓡 (finrank E)` to the original model `I`.
  simpa [b, Set.compl_compl] using
    (basis_model_codomain_transport_isSmoothEmbedding
      (E := E) (M := M) (B := (F ⁻¹' {c})ᶜ) b hEmbeddingEuclid)

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
open-subtype transport from Proposition 5.16 should glue them into the global
`SmoothManifoldWithBoundary` owner on the regular fiber, together with the smooth subtype
embedding and the pointwise boundary criterion. -/
theorem regular_preimage_boundary_point_iff_mem_ambient_boundary_of_chart_bridges
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c)
    (hSliceBridge :
      ∀ {x : (F ⁻¹' {c})}
        {e : OpenPartialHomeomorph M
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))},
        x.1 ∈ e.source →
          e.IsSliceChart (F ⁻¹' {c}) levelDim →
            ¬ (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x)
    (hBoundaryBridge :
      ∀ {x : (F ⁻¹' {c})}
        {e : OpenPartialHomeomorph M
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
        {hk : 0 < levelDim} {hkn : levelDim ≤ Module.finrank ℝ E}
        {cHalf : Fin (Module.finrank ℝ E - levelDim) → ℝ},
        x.1 ∈ e.source →
          e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim →
          e '' ((F ⁻¹' {c}) ∩ e.source) =
            Set.euclideanHalfSlice e.target levelDim hk hkn cHalf →
          e x.1 ∈ frontier (Set.euclideanHalfSlice e.target levelDim hk hkn cHalf) →
            (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x) :
    ∀ x : (F ⁻¹' {c}),
      (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M := by
  intro x
  constructor
  · intro hxBoundaryPoint
    by_contra hxNotBoundary
    -- An ambient interior patch at `x` would force `x` to be an interior point of the fiber.
    rcases hInteriorPatch x.1 x.2 hxNotBoundary with ⟨e, hxSource, heSlice⟩
    exact (hSliceBridge hxSource heSlice) hxBoundaryPoint
  · intro hxBoundary
    -- The boundary patch at `x` is exactly the local half-slice witness that yields a boundary
    -- point of the fiber, now strengthened to remember that `x` lands on the half-slice
    -- frontier in the chosen ambient chart.
    rcases hBoundaryPatch x.1 x.2 hxBoundary with
      ⟨e, hxSource, heHalfSlice, hk, hkn, cHalf, hHalfSlice, hxHalfFrontier⟩
    exact hBoundaryBridge hxSource heHalfSlice hHalfSlice hxHalfFrontier

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
open-subtype transport from Proposition 5.16 should glue them into the global
`SmoothManifoldWithBoundary` owner on the regular fiber, together with the smooth subtype
embedding and the pointwise boundary criterion. -/
theorem slice_chart_center_not_boundary_point
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hEmbeddingToI :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        I
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M))
    {x : (F ⁻¹' {c})}
    {e : OpenPartialHomeomorph M
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hx : x.1 ∈ e.source)
    (he : e.IsSliceChart (F ⁻¹' {c}) levelDim) :
    ¬ (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x := by
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := FiniteDimensional.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  let _ : IsManifold (𝓡 (Module.finrank ℝ E)) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold (E := E) (M := M) b
  -- Route correction: the full-slice center already gives ambient interior, so no pointed-chart
  -- reconstruction is needed here.
  have hxInteriorAmbient : x.1 ∈ interior (F ⁻¹' {c}) := by
    -- A full-dimensional slice chart fills the ambient chart source near the center point.
    exact mem_interior_of_full_sliceChart (S := F ⁻¹' {c}) (x := x.1) hx he
  have hxInterior :
      (leeBoundaryModelWithCorners levelDim).IsInteriorPoint x := by
    -- Convert ambient interior of the subtype value into interior in Lee's boundary model.
    exact
      (leeBoundaryModelWithCorners levelDim).isInteriorPoint_iff_isInteriorPoint_val.2
        hxInteriorAmbient
  -- Interior points of Lee's boundary model are exactly the non-boundary points.
  exact
    ((leeBoundaryModelWithCorners levelDim).isInteriorPoint_iff_not_isBoundaryPoint x).1
      hxInterior

/-- Helper for Problem 5-23: a frontier-centered ambient half-slice chart forces the
corresponding subtype point of the regular fiber to be a boundary point in the induced Lee
boundary model. -/
theorem boundary_centered_half_slice_chart_implies_boundary_point
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hEmbeddingToI :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        I
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M))
    {x : (F ⁻¹' {c})}
    {e : OpenPartialHomeomorph M
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    {hk : 0 < levelDim} {hkn : levelDim ≤ Module.finrank ℝ E}
    {cHalf : Fin (Module.finrank ℝ E - levelDim) → ℝ}
    (hx : x.1 ∈ e.source)
    (he : e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim)
    (hHalf :
      e '' ((F ⁻¹' {c}) ∩ e.source) =
        Set.euclideanHalfSlice e.target levelDim hk hkn cHalf)
    (hxFrontier :
      e x.1 ∈ frontier (Set.euclideanHalfSlice e.target levelDim hk hkn cHalf)) :
    (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x := by
  -- First convert the explicit half-slice frontier witness into the intrinsic ambient-frontier
  -- statement for the regular fiber.
  have hxAmbientFrontier : x.1 ∈ frontier (F ⁻¹' {c}) := by
    exact
      mem_frontier_of_half_slice_chart_frontier
        (I := I) (x := x.1) (e := e) hx hHalf hxFrontier
  -- Route correction: once the ambient frontier statement is known, the boundary-model
  -- conclusion follows by excluding the interior alternative.
  by_contra hxNotBoundary
  have hxInterior :
      (leeBoundaryModelWithCorners levelDim).IsInteriorPoint x := by
    -- In Lee's boundary model, non-boundary points are exactly the interior points.
    exact
      ((leeBoundaryModelWithCorners levelDim).isInteriorPoint_iff_not_isBoundaryPoint x).2
        hxNotBoundary
  have hxInteriorAmbient : x.1 ∈ interior (F ⁻¹' {c}) := by
    -- Transport abstract interior of the subtype point back to ambient interior of its value.
    exact
      (leeBoundaryModelWithCorners levelDim).isInteriorPoint_iff_isInteriorPoint_val.1
        hxInterior
  -- A frontier point of the level set cannot lie in its ambient interior.
  exact hxAmbientFrontier.2 hxInteriorAmbient

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
open-subtype transport from Proposition 5.16 should glue them into the global
`SmoothManifoldWithBoundary` owner on the regular fiber, together with the smooth subtype
embedding and the pointwise boundary criterion. -/
theorem regular_preimage_chart_center_boundary_bridges
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hEmbeddingToI :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        I
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M)) :
    (∀ {x : (F ⁻¹' {c})}
      {e : OpenPartialHomeomorph M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))},
      x.1 ∈ e.source →
        e.IsSliceChart (F ⁻¹' {c}) levelDim →
          ¬ (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x) ∧
    (∀ {x : (F ⁻¹' {c})}
      {e : OpenPartialHomeomorph M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
      {hk : 0 < levelDim} {hkn : levelDim ≤ Module.finrank ℝ E}
      {cHalf : Fin (Module.finrank ℝ E - levelDim) → ℝ},
      x.1 ∈ e.source →
        e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim →
        e '' ((F ⁻¹' {c}) ∩ e.source) =
          Set.euclideanHalfSlice e.target levelDim hk hkn cHalf →
        e x.1 ∈ frontier (Set.euclideanHalfSlice e.target levelDim hk hkn cHalf) →
          (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x) := by
  -- Route correction: the local-to-global argument is already finished. The only remaining
  -- source-faithful blocker is to export the chart-center consequences of Theorem 5.51 in a form
  -- strong enough for the chosen boundary patches. The slice branch is plausible, but the
  -- half-slice branch is not valid in the current statement: a point can lie in the source of a
  -- boundary-slice chart and still correspond to an interior point of the half-slice. The
  -- repaired statement now asks for the stronger frontier-centered witness that actually matches
  -- Lee's boundary-branch geometry.
  refine ⟨?_, ?_⟩
  · intro x e hx he
    -- The slice-center consequence is isolated in the dedicated local chart-center bridge.
    exact
      slice_chart_center_not_boundary_point
        (I := I) (F := F) (c := c) hEmbeddingToI hx he
  · intro x e hk hkn cHalf hx he hHalf hxFrontier
    -- The corrected half-slice consequence is isolated in the frontier-aware bridge.
    exact
      boundary_centered_half_slice_chart_implies_boundary_point
        (I := I) (F := F) (c := c) hEmbeddingToI hx he hHalf hxFrontier

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
open-subtype transport from Proposition 5.16 should glue them into the global
`SmoothManifoldWithBoundary` owner on the regular fiber, together with the smooth subtype
embedding and the pointwise boundary criterion. -/
theorem regular_preimage_boundary_point_iff_mem_ambient_boundary
    {F : M → N} {c : N}
    [SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})]
    (hInteriorPatch : RegularPreimageInteriorPatchData (I := I) F c)
    (hBoundaryPatch : RegularPreimageBoundaryPatchData (I := I) F c)
    (hEmbeddingToI :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners levelDim)
        I
        (⊤ : WithTop ℕ∞)
        (Subtype.val : (F ⁻¹' {c}) → M)) :
    ∀ x : (F ⁻¹' {c}),
      (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M := by
  -- Route correction: the local-to-global logic is now stabilized in
  -- `regular_preimage_boundary_point_iff_mem_ambient_boundary_of_chart_bridges`. The only
  -- remaining blocker is to import the two missing chart-center bridge lemmas from
  -- `Theorem_5_51`.
  have hBridges :=
    regular_preimage_chart_center_boundary_bridges
      (I := I) (F := F) (c := c) hEmbeddingToI
  rcases hBridges with ⟨hSliceBridge, hBoundaryBridge⟩
  -- With the chart bridges isolated, the pointwise boundary criterion is exactly the stabilized
  -- local-to-global theorem proved just above.
  exact
    regular_preimage_boundary_point_iff_mem_ambient_boundary_of_chart_bridges
      (I := I) (F := F) (c := c)
      hInteriorPatch
      hBoundaryPatch
      hSliceBridge
      hBoundaryBridge

/-- Helper for Problem 5-23: once the interior and boundary local patch data are available, the
open-subtype transport from Proposition 5.16 should glue them into the global
`SmoothManifoldWithBoundary` owner on the regular fiber, together with the smooth subtype
embedding and the pointwise boundary criterion. -/
theorem local_boundary_patch_data_glue
    {F : M → N} {c : N} :
    RegularPreimageInteriorPatchData (I := I) F c →
      RegularPreimageBoundaryPatchData (I := I) F c →
        ∃ instSmooth : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
          letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
          IsSmoothEmbedding
            (leeBoundaryModelWithCorners levelDim)
            I
            (⊤ : WithTop ℕ∞)
            (Subtype.val : (F ⁻¹' {c}) → M) ∧
          ∀ x : (F ⁻¹' {c}),
            (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M := by
  intro hInteriorPatch hBoundaryPatch
  -- Route correction: the global packaging no longer blocks here. The basis-model embedding is
  -- already available, so the only remaining blocker is the pointwise boundary criterion for the
  -- transported subtype structure.
  rcases
      regular_preimage_embedding_transports_to_original_model
        (I := I) (F := F) (c := c) hInteriorPatch hBoundaryPatch with
    ⟨instSmooth, hEmbeddingToI⟩
  letI : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}) := instSmooth
  have hBoundaryPoint :
      ∀ x : (F ⁻¹' {c}),
        (leeBoundaryModelWithCorners levelDim).IsBoundaryPoint x ↔ x.1 ∈ I.boundary M := by
    -- The remaining boundary identification is isolated in the dedicated pointwise bridge lemma.
    exact
      regular_preimage_boundary_point_iff_mem_ambient_boundary
        (I := I) (F := F) (c := c) hInteriorPatch hBoundaryPatch hEmbeddingToI
  exact ⟨instSmooth, hEmbeddingToI, hBoundaryPoint⟩

-- Proof sketch: use the regular-value theorem in the interior of `M` to obtain local interior
-- slices for the fiber, use the boundary-regular-value hypothesis to obtain local half-space
-- slices near points of `S ∩ ∂M`, and glue these local normal forms into the canonical
-- manifold-with-boundary structure on the level-set subtype.
/-- Problem 5-23: if `M` is a smooth manifold with boundary, `N` is a smooth boundaryless
manifold, `F` is smooth, `c` is a regular value of `F`, and the boundary restriction `F | ∂M`
has `c` as a regular value in the intrinsic boundary sense, then the level set `F⁻¹({c})` carries
the canonical owner
`SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})`, its subtype inclusion into `M` is a smooth
embedding, and its boundary maps onto `F⁻¹({c}) ∩ ∂M`. -/
theorem regular_preimage_has_embedded_submanifold_with_boundary_structure
    {F : M → N} {c : N} (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c) :
    ∃ _ : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
        IsSmoothEmbedding
            (leeBoundaryModelWithCorners levelDim)
            I
            (⊤ : WithTop ℕ∞)
            (Subtype.val : (F ⁻¹' {c}) → M) ∧
          Subtype.val '' (leeBoundaryModelWithCorners levelDim).boundary (F ⁻¹' {c}) =
            (F ⁻¹' {c}) ∩ I.boundary M := by
  -- Route correction: the old global-Euclidean ambient route was the wrong interface. The actual
  -- frontier is now: produce the interior and boundary patch data, then invoke a gluing theorem
  -- that assembles those open-subtype patches into the global fiber structure.
  have hInteriorPatch :
      RegularPreimageInteriorPatchData (I := I) F c :=
    regular_preimage_has_interior_embedded_patch (I := I) (J := J) (F := F) (c := c)
      hF hc hBoundary
  have hBoundaryPatch :
      RegularPreimageBoundaryPatchData (I := I) F c :=
    regular_preimage_has_boundary_half_slice_patch (I := I) (J := J) (F := F) (c := c)
      hF hc hBoundary
  -- With the two pointwise patch families isolated, the remaining global step is exactly the
  -- local-patch gluing theorem.
  exact
    regular_preimage_has_embedded_submanifold_with_boundary_structure_of_local_models
      (I := I) (F := F) (c := c)
      hInteriorPatch
      hBoundaryPatch
      (local_boundary_patch_data_glue (I := I) (F := F) (c := c))

end RegularPreimageWithBoundary

end Manifold
