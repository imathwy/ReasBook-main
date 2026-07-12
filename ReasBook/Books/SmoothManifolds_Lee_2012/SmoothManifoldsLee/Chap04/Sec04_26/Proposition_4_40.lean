import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Covering.Basic
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Exercise_4_37
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Proposition_4_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

universe u𝕜 uE uH uM uE'

noncomputable section

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ∞ M]
variable {M' : Type uE'} [TopologicalSpace M'] (π : M' → M)

/- Proposition 4.40 is a `source-facing` existence-and-uniqueness statement, but its canonical
owner is the transported `IsManifold I ∞` structure on the total space. Lee's boundaryless
`ℝ^n` formulation is the specialization `I = 𝓡 n`; the textbook connectedness hypothesis is
redundant for both existence and uniqueness. -/

/-- Helper for Proposition 4.40: the canonical lifted chart through `p` is obtained by pulling the
base chart at `π p` back along the local inverse branch of the covering projection through `p`. -/
noncomputable def lifted_covering_chart
    (hπ : IsCoveringMap π) (p : M') : OpenPartialHomeomorph M' H :=
  (hπ.isLocalHomeomorph.localInverseAt p).symm.trans (chartAt H (π p))

/-- Helper for Proposition 4.40: the canonical local branch of the covering projection through `p`
is obtained by composing the lifted chart with the inverse of the base chart at `π p`. -/
noncomputable def lifted_projection_branch
    (hπ : IsCoveringMap π) (p : M') : OpenPartialHomeomorph M' M :=
  (lifted_covering_chart (H := H) π hπ p).trans (chartAt H (π p)).symm

/-- Helper for Proposition 4.40: the canonical lifted chart contains its marked point. -/
theorem mem_lifted_covering_chart_source
    (hπ : IsCoveringMap π) (p : M') :
    p ∈ (lifted_covering_chart (H := H) π hπ p).source := by
  -- The local inverse branch is defined at `π p`, and every manifold chart contains its center.
  simp [lifted_covering_chart]

/-- Helper for Proposition 4.40: the canonical lifted charts form a charted-space structure on the
covering space. -/
@[implicit_reducible]
noncomputable def lifted_covering_chartedSpace
    (hπ : IsCoveringMap π) : ChartedSpace H M' where
  atlas := Set.range (lifted_covering_chart (H := H) π hπ)
  chartAt := lifted_covering_chart (H := H) π hπ
  mem_chart_source := mem_lifted_covering_chart_source (H := H) π hπ
  chart_mem_atlas p := ⟨p, rfl⟩

/-- Helper for Proposition 4.40: the source of a lifted-chart transition is contained in the
source of the corresponding base-chart transition. -/
theorem lifted_covering_chart_transition_source_subset
    (hπ : IsCoveringMap π) (p q : M') :
    ((lifted_covering_chart (H := H) π hπ p).symm.trans
      (lifted_covering_chart (H := H) π hπ q)).source ⊆
      ((chartAt H (π p)).symm.trans (chartAt H (π q))).source := by
  intro x hx
  -- Expanding the lifted charts shows that every source condition for the lifted transition
  -- is stronger than the corresponding source condition for the base transition.
  have hx' := hx
  simp only [lifted_covering_chart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
    PartialEquiv.symm_source, OpenPartialHomeomorph.coe_coe_symm, Set.mem_inter_iff,
    Set.mem_preimage] at hx'
  rcases hx' with ⟨⟨hx_chart, hx_lp_source⟩, -, hx_qsource⟩
  refine ⟨hx_chart, ?_⟩
  have h_apply :
      π ((hπ.isLocalHomeomorph.localInverseAt p) ((chartAt H (π p)).symm x)) =
        (chartAt H (π p)).symm x := by
    exact hπ.isLocalHomeomorph.apply_localInverseAt_of_mem (x := p) hx_lp_source
  simpa [h_apply] using hx_qsource

/-- Helper for Proposition 4.40: on the source of the transition between two lifted charts, the
transition map is exactly the corresponding base-chart transition map. -/
theorem lifted_covering_chart_transition_eqOn
    (hπ : IsCoveringMap π) (p q : M') :
    Set.EqOn
      (((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q)) :
          H → H)
      (((chartAt H (π p)).symm.trans (chartAt H (π q))) : H → H)
      ((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q)).source := by
  intro x hx
  -- Both lifted charts use inverse branches of the same covering map, so the middle
  -- `localInverseAt` maps cancel on the overlap.
  have hx' := hx
  simp only [lifted_covering_chart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
    PartialEquiv.symm_source, OpenPartialHomeomorph.coe_coe_symm, Set.mem_inter_iff,
    Set.mem_preimage] at hx'
  rcases hx' with ⟨⟨-, hx_lp_source⟩, -, -⟩
  have h_apply :
      π ((hπ.isLocalHomeomorph.localInverseAt p) ((chartAt H (π p)).symm x)) =
        (chartAt H (π p)).symm x := by
    exact hπ.isLocalHomeomorph.apply_localInverseAt_of_mem (x := p) hx_lp_source
  simpa [lifted_covering_chart, h_apply]

/-- Helper for Proposition 4.40: the transition between two lifted charts is equivalent on its
source to the restriction of the corresponding base-chart transition. -/
theorem lifted_covering_chart_transition_eqOnSource
    (hπ : IsCoveringMap π) (p q : M') :
    (OpenPartialHomeomorph.EqOnSource
      ((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q))
      (((chartAt H (π p)).symm.trans (chartAt H (π q))).restr
        ((lifted_covering_chart (H := H) π hπ p).symm.trans
          (lifted_covering_chart (H := H) π hπ q)).source)) := by
  constructor
  · -- Restricting the base transition to the lifted-transition source preserves that source.
    rw [(((chartAt H (π p)).symm.trans (chartAt H (π q))).restr_source'
      ((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q)).source
      ((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q)).open_source)]
    exact (Set.inter_eq_right.mpr
      (lifted_covering_chart_transition_source_subset (H := H) π hπ p q)).symm
  · -- The two transition maps agree pointwise on their common source.
    exact lifted_covering_chart_transition_eqOn π hπ p q

/-- Helper for Proposition 4.40: every lifted-chart transition belongs to the smooth structure
groupoid because it is the restriction of a smooth base-chart transition. -/
theorem lifted_covering_chart_transition_mem_groupoid
    (hπ : IsCoveringMap π) (p q : M') :
    (lifted_covering_chart (H := H) π hπ p).symm.trans
      (lifted_covering_chart (H := H) π hπ q) ∈ contDiffGroupoid ∞ I := by
  -- The lifted transition is just a restricted base transition, so smoothness is inherited from
  -- the base maximal atlas.
  have hbase :
      (chartAt H (π p)).symm.trans (chartAt H (π q)) ∈ contDiffGroupoid ∞ I := by
    exact IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π p))
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π q))
  have hrestr :
      ((chartAt H (π p)).symm.trans (chartAt H (π q))).restr
        ((lifted_covering_chart (H := H) π hπ p).symm.trans
          (lifted_covering_chart (H := H) π hπ q)).source ∈ contDiffGroupoid ∞ I := by
    exact closedUnderRestriction' hbase
      ((lifted_covering_chart (H := H) π hπ p).symm.trans
        (lifted_covering_chart (H := H) π hπ q)).open_source
  exact (contDiffGroupoid ∞ I).mem_of_eqOnSource hrestr
    (lifted_covering_chart_transition_eqOnSource (H := H) π hπ p q)

/-- Helper for Proposition 4.40: the canonical lifted charted-space structure is smooth, because
all of its chart transitions are inherited from smooth base transitions. -/
theorem lifted_covering_chartedSpace_isManifold
    (hπ : IsCoveringMap π) :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    IsManifold I ∞ M' := by
  -- The canonical lifted atlas is compatible with the `C^∞` groupoid by construction.
  let cs : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  let hgroupoid :
      @HasGroupoid H _ M' _ cs (contDiffGroupoid ∞ I) :=
    { compatible := by
        intro e e' he he'
        rcases he with ⟨p, rfl⟩
        rcases he' with ⟨q, rfl⟩
        exact lifted_covering_chart_transition_mem_groupoid (I := I) (H := H) (π := π) hπ p q }
  let _ : HasGroupoid M' (contDiffGroupoid ∞ I) := hgroupoid
  exact IsManifold.mk' I ∞ M'

/-- Helper for Proposition 4.40: on the source of the canonical local branch through `p`, the
covering projection agrees with that branch. -/
theorem lifted_projection_branch_eqOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    Set.EqOn π
      (lifted_projection_branch (H := H) π hπ p)
      (lifted_projection_branch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  change Set.EqOn π
    (lifted_projection_branch (H := H) π hπ p)
    (lifted_projection_branch (H := H) π hπ p).source
  intro x hx
  -- The branch is literally the chosen local inverse branch of `π`, followed by the inverse
  -- base chart, so it computes to `π` on its source.
  have hx_lifted : x ∈ (lifted_covering_chart (H := H) π hπ p).source := by
    simpa [lifted_projection_branch] using hx.1
  have hx_chart : π x ∈ (chartAt H (π p)).source := by
    have hx_lifted' := hx_lifted
    simp [lifted_covering_chart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hx_lifted'
    exact hx_lifted'.2
  simpa [lifted_projection_branch, lifted_covering_chart] using
    ((chartAt H (π p)).left_inv hx_chart).symm

/-- Helper for Proposition 4.40: the marked point lies in the source of its canonical local branch
to the base manifold. -/
theorem mem_lifted_projection_branch_source
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    p ∈ (lifted_projection_branch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  -- The lifted chart contains `p`, and it sends `p` to the center of the base chart.
  simp [lifted_projection_branch, lifted_covering_chart]

/-- Helper for Proposition 4.40: the canonical local branch of the covering projection is smooth in
the canonical lifted atlas because its coordinate representative is the identity. -/
theorem lifted_projection_branch_contMDiffOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
    ContMDiffOn I I ∞
      (lifted_projection_branch (H := H) π hπ p)
      (lifted_projection_branch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := lifted_projection_branch (H := H) π hπ p
  have hs : e.source ⊆ (chartAt H p).source := by
    intro x hx
    simpa [e, lifted_projection_branch]
      using hx.1
  have hmaps : Set.MapsTo e e.source (chartAt H (π p)).source := by
    intro x hx
    have hx_target : (lifted_covering_chart (H := H) π hπ p) x ∈ (chartAt H (π p)).target := by
      simpa [e, lifted_projection_branch] using hx.2
    exact (chartAt H (π p)).symm_mapsTo hx_target
  have hs_ext : e.source ⊆ (extChartAt I p).source := by
    simpa [extChartAt_source] using hs
  have hmaps_ext : Set.MapsTo e e.source (extChartAt I (π p)).source := by
    simpa [extChartAt_source] using hmaps
  have hsmooth_model :
      ContDiffOn 𝕜 ∞
        (extChartAt I (π p) ∘ e ∘ (extChartAt I p).symm)
        (extChartAt I p '' e.source) := by
    refine contDiffOn_id.congr ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_chart : x ∈ (chartAt H p).source := hs hx
    have hx_target : (chartAt H p) x ∈ (chartAt H (π p)).target := by
      simpa [e, lifted_projection_branch] using hx.2
    have hstep :
        e x = (chartAt H (π p)).symm ((chartAt H p) x) := by
      change (lifted_projection_branch (H := H) π hπ p) x =
        (chartAt H (π p)).symm ((lifted_covering_chart (H := H) π hπ p) x)
      rfl
    have hright :
        (chartAt H (π p)) ((chartAt H (π p)).symm ((chartAt H p) x)) = (chartAt H p) x := by
      exact (chartAt H (π p)).right_inv hx_target
    calc
      extChartAt I (π p) (e ((extChartAt I p).symm (extChartAt I p x)))
          = extChartAt I (π p) (e x) := by
              rw [PartialEquiv.left_inv (extChartAt I p) (by simpa [extChartAt_source] using hx_chart)]
      _ = extChartAt I (π p) ((chartAt H (π p)).symm ((chartAt H p) x)) := by rw [hstep]
      _ = I ((chartAt H p) x) := by
            simp [extChartAt_coe, extChartAt_coe_symm, hright]
      _ = extChartAt I p x := by simp [extChartAt_coe]
  exact (contMDiffOn_iff_of_subset_source'
    (I := I) (I' := I) (f := e) (s := e.source) (x := p) (y := π p) hs_ext hmaps_ext).2
    hsmooth_model

/-- Helper for Proposition 4.40: the inverse of the canonical local branch through `p` is smooth,
again because its coordinate representative is the identity. -/
theorem lifted_projection_branch_symm_contMDiffOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
    ContMDiffOn I I ∞
      (lifted_projection_branch (H := H) π hπ p).symm
      (lifted_projection_branch (H := H) π hπ p).target := by
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := lifted_projection_branch (H := H) π hπ p
  have hs : e.target ⊆ (chartAt H (π p)).source := by
    intro x hx
    simpa [e, lifted_projection_branch]
      using hx.1
  have hmaps : Set.MapsTo e.symm e.target (chartAt H p).source := by
    intro x hx
    have hx_target : (chartAt H (π p)) x ∈ (lifted_covering_chart (H := H) π hπ p).target := by
      simpa [e, lifted_projection_branch] using hx.2
    change (lifted_covering_chart (H := H) π hπ p).symm ((chartAt H (π p)) x) ∈
      (lifted_covering_chart (H := H) π hπ p).source
    exact (lifted_covering_chart (H := H) π hπ p).symm_mapsTo hx_target
  have hs_ext : e.target ⊆ (extChartAt I (π p)).source := by
    simpa [extChartAt_source] using hs
  have hmaps_ext : Set.MapsTo e.symm e.target (extChartAt I p).source := by
    simpa [extChartAt_source] using hmaps
  have hsmooth_model :
      ContDiffOn 𝕜 ∞
        (extChartAt I p ∘ e.symm ∘ (extChartAt I (π p)).symm)
        (extChartAt I (π p) '' e.target) := by
    refine contDiffOn_id.congr ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_chart : x ∈ (chartAt H (π p)).source := hs hx
    have hx_target : (chartAt H (π p)) x ∈ (chartAt H p).target := by
      change (chartAt H (π p)) x ∈ (lifted_covering_chart (H := H) π hπ p).target
      simpa [e, lifted_projection_branch] using hx.2
    have hstep :
        e.symm x = (chartAt H p).symm ((chartAt H (π p)) x) := by
      change (lifted_projection_branch (H := H) π hπ p).symm x =
        (lifted_covering_chart (H := H) π hπ p).symm ((chartAt H (π p)) x)
      rfl
    have hright :
        (chartAt H p) ((chartAt H p).symm ((chartAt H (π p)) x)) = (chartAt H (π p)) x := by
      exact (chartAt H p).right_inv hx_target
    calc
      extChartAt I p (e.symm ((extChartAt I (π p)).symm (extChartAt I (π p) x)))
          = extChartAt I p (e.symm x) := by
              rw [PartialEquiv.left_inv (extChartAt I (π p))
                (by simpa [extChartAt_source] using hx_chart)]
      _ = extChartAt I p ((chartAt H p).symm ((chartAt H (π p)) x)) := by rw [hstep]
      _ = I ((chartAt H (π p)) x) := by
            simp [extChartAt_coe, extChartAt_coe_symm, hright]
      _ = extChartAt I (π p) x := by simp [extChartAt_coe]
  exact (contMDiffOn_iff_of_subset_source'
    (I := I) (I' := I) (f := e.symm) (s := e.target) (x := π p) (y := p) hs_ext hmaps_ext).2
    hsmooth_model

/-- Helper for Proposition 4.40: the canonical local branch of the covering projection through `p`
packages to a manifold `PartialDiffeomorph`. -/
theorem lifted_projection_partial_diffeomorph
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
    ∃ Φ : PartialDiffeomorph I I M' M ∞,
      p ∈ Φ.source ∧
      Set.EqOn π Φ Φ.source ∧
      Φ.toOpenPartialHomeomorph = lifted_projection_branch (H := H) π hπ p := by
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := lifted_projection_branch (H := H) π hπ p
  let Φ : PartialDiffeomorph I I M' M ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := lifted_projection_branch_contMDiffOn (I := I) (H := H) π hπ p
      contMDiffOn_invFun := lifted_projection_branch_symm_contMDiffOn (I := I) (H := H) π hπ p }
  refine ⟨Φ, ?_, ?_, rfl⟩
  · -- The branch is centered at `p`.
    simpa [Φ, e] using mem_lifted_projection_branch_source (H := H) π hπ p
  · -- The partial diffeomorphism coincides with `π` on its source.
    simpa [Φ, e] using lifted_projection_branch_eqOn (H := H) π hπ p

/-- Helper for Proposition 4.40: in any smooth covering structure on `M'`, the canonical
topological branch through `p` is already a smooth local section of `π`. -/
theorem canonical_localInverse_contMDiffOn_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ContMDiffOn I I ∞
      (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p)
      (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p).source := by
  let _ : ChartedSpace H M' := cs
  let σ := hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p
  have hσ_cont : ContinuousOn σ σ.source := σ.continuousOn
  have hσ_sec : Set.RightInvOn σ π σ.source := by
    intro y hy
    exact hsm.2.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem (x := p) hy
  -- The topological inverse branch is a continuous local section, so Exercise 4.37 upgrades it
  -- to a smooth local section on the same source.
  simpa [σ] using hsm.2.localSection_contMDiffOn σ.open_source hσ_cont hσ_sec

/-- Helper for Proposition 4.40: in any smooth covering structure, the inverse of the canonical
topological branch is smooth because it is the covering projection `π` on its target. -/
theorem canonical_localInverse_symm_contMDiffOn_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ContMDiffOn I I ∞
      (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p).symm
      (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p).target := by
  let _ : ChartedSpace H M' := cs
  -- The inverse branch is literally `π`, so smoothness comes from the local diffeomorphism field.
  simpa using
    (hsm.2.isLocalDiffeomorph.contMDiff.contMDiffOn :
      ContMDiffOn I I ∞ π
        (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p).target)

/-- Helper for Proposition 4.40: in any smooth covering structure, the canonical topological
branch through `p` packages to a manifold `PartialDiffeomorph`. -/
theorem canonical_localInverse_partial_diffeomorph_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ∃ Φ : PartialDiffeomorph I I M M' ∞,
      Φ.toOpenPartialHomeomorph = hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p := by
  let _ : ChartedSpace H M' := cs
  let σ := hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p
  let Φ : PartialDiffeomorph I I M M' ∞ :=
    { toPartialEquiv := σ.toPartialEquiv
      open_source := σ.open_source
      open_target := σ.open_target
      contMDiffOn_toFun := canonical_localInverse_contMDiffOn_of_smooth_covering_structure
        (I := I) (H := H) (π := π) hsm p
      contMDiffOn_invFun := canonical_localInverse_symm_contMDiffOn_of_smooth_covering_structure
        (I := I) (H := H) (π := π) hsm p }
  -- Packaging the two smoothness directions gives the desired partial diffeomorphism witness.
  exact ⟨Φ, rfl⟩

/-- Helper for Proposition 4.40: a model-space partial homeomorphism belongs to the smooth
groupoid once it is locally represented by smooth structomorphisms on its whole source. -/
theorem mem_contDiffGroupoid_of_local_structomorphOn_source
    {f : OpenPartialHomeomorph H H}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ I := by
  refine (contDiffGroupoid ∞ I).locality ?_
  intro x hx
  -- The local structomorphism data gives a genuine groupoid element on a neighborhood of `x`.
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ I) (f := f)] at hfx_prop'
  obtain ⟨e, he, hsource, hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  -- Restricting `f` to the neighborhood where it agrees with `e` identifies the two
  -- open partial homeomorphisms.
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid ∞ I).mem_of_eqOnSource he hEqOnSource

/-- Helper for Proposition 4.40: writing a manifold partial diffeomorphism in maximal-atlas
charts produces a smooth transition map on the model space. -/
theorem writtenIn_partial_diffeomorph_mem_contDiffGroupoid
    [ChartedSpace H M'] [IsManifold I ∞ M']
    {Φ : PartialDiffeomorph I I M M' ∞} {e : OpenPartialHomeomorph M H}
    {c : OpenPartialHomeomorph M' H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hc : c ∈ IsManifold.maximalAtlas I ∞ M') :
    (e.symm.trans Φ.toOpenPartialHomeomorph).trans c ∈ contDiffGroupoid ∞ I := by
  let f : OpenPartialHomeomorph H H := (e.symm.trans Φ.toOpenPartialHomeomorph).trans c
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is smooth in both directions on its own source and target.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := I) (n := ∞) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  -- Writing `Φ` in maximal-atlas charts transports its local structomorphism property to the
  -- model space, where `mem_contDiffGroupoid_of_local_structomorphOn_source` can close.
  refine mem_contDiffGroupoid_of_local_structomorphOn_source (I := I) ?_
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Set.preimage_id_eq]
  refine ⟨f.continuousOn_toFun.continuousWithinAt hy, ?_⟩
  intro hyf
  have hy_chart :
      y ∈ e.target ∩ e.symm ⁻¹' (Φ.source ∩ Φ.toOpenPartialHomeomorph ⁻¹' c.source) := by
    have hyf' := hyf
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hyf'
    rcases hyf' with ⟨⟨hy_target, hy_source⟩, hy_csource⟩
    exact ⟨hy_target, hy_source, hy_csource⟩
  have htransport :
      (contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt
        (c ∘ Φ.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Φ.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ I))
      he hc hΦ hy_chart
  rcases htransport hy_chart.2.1 with ⟨φ, hφ, hEq, hyφ⟩
  refine ⟨φ, hφ, ?_, hyφ⟩
  -- The source of the written-in-chart map is the usual chart-transport source, so the witness
  -- from the bigger set `e.symm ⁻¹' Φ.source` also works on the actual composite source.
  intro z hz
  have hz_big : z ∈ (e.symm ⁻¹' Φ.source) ∩ φ.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

/-- Helper for Proposition 4.40: pulling a maximal-atlas chart back along a smooth partial
diffeomorphism yields a maximal-atlas chart on the target manifold. -/
theorem pullback_chart_mem_maximalAtlas_of_partial_diffeomorph
    [ChartedSpace H M'] [IsManifold I ∞ M']
    {Φ : PartialDiffeomorph I I M M' ∞}
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    Φ.symm.toOpenPartialHomeomorph.trans e ∈ IsManifold.maximalAtlas I ∞ M' := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  have hc_max : c ∈ IsManifold.maximalAtlas I ∞ M' := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  constructor
  · -- The forward transition is `Φ` written in the source chart `e` and target chart `c`.
    simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      writtenIn_partial_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ) (e := e) (c := c) he hc_max
  · -- The reverse transition is the same chart-written statement for `Φ.symm`.
    simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      writtenIn_partial_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ.symm) (e := c) (c := e) hc_max he

/-- Helper for Proposition 4.40: every canonical lifted covering chart belongs to any
smooth-covering maximal atlas on the total space. -/
theorem canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    let _ : IsManifold I ∞ M' := hsm.1
    lifted_covering_chart (H := H) π hsm.2.isCoveringMap p ∈ IsManifold.maximalAtlas I ∞ M' := by
  let _ : ChartedSpace H M' := cs
  let _ : IsManifold I ∞ M' := hsm.1
  rcases canonical_localInverse_partial_diffeomorph_of_smooth_covering_structure
      (I := I) (H := H) (π := π) hsm p with ⟨Φ, hΦ⟩
  have hΦsymm :
      Φ.symm.toOpenPartialHomeomorph =
        (hsm.2.isCoveringMap.isLocalHomeomorph.localInverseAt p).symm := by
    simpa using congrArg OpenPartialHomeomorph.symm hΦ
  -- The canonical lifted chart is precisely the pullback of the base chart along the canonical
  -- local inverse branch through `p`.
  simpa [lifted_covering_chart, hΦsymm] using
    pullback_chart_mem_maximalAtlas_of_partial_diffeomorph
      (I := I) (Φ := Φ)
      (e := chartAt H (π p))
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π p))

/-- Helper for Proposition 4.40: once both smooth-covering structures contain the canonical
lifted charts, every chart of one maximal atlas is locally compatible with the other. -/
theorem smooth_covering_maximalAtlas_subset_via_canonical
    {cs cs' : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (hsm' : let _ : ChartedSpace H M' := cs'
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π) :
    (let _ : ChartedSpace H M' := cs
     let _ : IsManifold I ∞ M' := hsm.1
     IsManifold.maximalAtlas I ∞ M') ⊆
      (let _ : ChartedSpace H M' := cs'
       let _ : IsManifold I ∞ M' := hsm'.1
       IsManifold.maximalAtlas I ∞ M') := by
  intro e he
  have hπ : IsCoveringMap π := by
    let _ : ChartedSpace H M' := cs
    exact hsm.2.isCoveringMap
  have hπ' : IsCoveringMap π := by
    let _ : ChartedSpace H M' := cs'
    exact hsm'.2.isCoveringMap
  let _ : ChartedSpace H M' := cs'
  let _ : IsManifold I ∞ M' := hsm'.1
  rw [IsManifold.mem_maximalAtlas_iff]
  intro d hd
  have hd_max : d ∈ IsManifold.maximalAtlas I ∞ M' := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have hforward : e.symm.trans d ∈ contDiffGroupoid ∞ I := by
    -- Route correction: follow `compatible_of_mem_maximalAtlas`, but insert the canonical lifted
    -- chart at `e.symm x`, which is known to belong to both smooth-covering maximal atlases.
    refine (contDiffGroupoid ∞ I).locality ?_
    intro x hx
    let p : M' := e.symm x
    let k : OpenPartialHomeomorph M' H :=
      lifted_covering_chart (H := H) π hπ p
    let s : Set H := e.target ∩ e.symm ⁻¹' k.source
    have hs : IsOpen s := by
      dsimp [s]
      exact e.symm.continuousOn_toFun.isOpen_inter_preimage e.open_target k.open_source
    have hxp : p ∈ k.source := by
      simpa [p, k] using
        mem_lifted_covering_chart_source (H := H) π hπ p
    have hxs : x ∈ s := by
      refine ⟨hx.1, ?_⟩
      simpa [p] using hxp
    have hk_source :
        let _ : ChartedSpace H M' := cs
        let _ : IsManifold I ∞ M' := hsm.1
        k ∈ IsManifold.maximalAtlas I ∞ M' := by
      let _ : ChartedSpace H M' := cs
      let _ : IsManifold I ∞ M' := hsm.1
      simpa [k] using
        canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
          (I := I) (H := H) (π := π) hsm p
    have hk_target : k ∈ IsManifold.maximalAtlas I ∞ M' := by
      have hcover : hπ' = hπ := Subsingleton.elim _ _
      simpa [k, hcover] using
        canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
          (I := I) (H := H) (π := π) hsm' p
    have hek : e.symm.trans k ∈ contDiffGroupoid ∞ I := by
      let _ : ChartedSpace H M' := cs
      let _ : IsManifold I ∞ M' := hsm.1
      exact IsManifold.compatible_of_mem_maximalAtlas he hk_source
    have hkd : k.symm.trans d ∈ contDiffGroupoid ∞ I :=
      IsManifold.compatible_of_mem_maximalAtlas hk_target hd_max
    have hcomp : (e.symm.trans k).trans (k.symm.trans d) ∈ contDiffGroupoid ∞ I :=
      (contDiffGroupoid ∞ I).trans hek hkd
    have hEq :
        (e.symm.trans k).trans (k.symm.trans d) ≈ (e.symm.trans d).restr s := by
      calc
        (e.symm ≫ₕ k) ≫ₕ k.symm ≫ₕ d = e.symm ≫ₕ (k ≫ₕ k.symm) ≫ₕ d := by
          simp only [OpenPartialHomeomorph.trans_assoc]
        _ ≈ e.symm ≫ₕ OpenPartialHomeomorph.ofSet k.source k.open_source ≫ₕ d :=
          OpenPartialHomeomorph.EqOnSource.trans'
            (_root_.refl _)
            (OpenPartialHomeomorph.EqOnSource.trans'
              (OpenPartialHomeomorph.self_trans_symm _) (_root_.refl _))
        _ ≈ (e.symm ≫ₕ OpenPartialHomeomorph.ofSet k.source k.open_source) ≫ₕ d := by
          rw [OpenPartialHomeomorph.trans_assoc]
        _ ≈ e.symm.restr s ≫ₕ d := by
          rw [OpenPartialHomeomorph.trans_of_set']
          exact _root_.refl _
        _ ≈ (e.symm ≫ₕ d).restr s := by
          rw [OpenPartialHomeomorph.restr_trans]
    exact ⟨s, hs, hxs, (contDiffGroupoid ∞ I).mem_of_eqOnSource hcomp (Setoid.symm hEq)⟩
  constructor
  · exact hforward
  · simpa using (contDiffGroupoid ∞ I).symm hforward

/-- Proposition 4.40 (1): if `π : M' → M` is a surjective topological covering map over a smooth
manifold `M`, then `M'` admits a smooth structure modelled on the same `I` for which `π` is a
smooth covering map. -/
theorem exists_smooth_covering_structure
    (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ cs : ChartedSpace H M',
      let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π := by
  -- Route correction: the proof uses the canonical lifted atlas from covering inverse branches,
  -- rather than Lee's separate Hausdorff and second-countable detour.
  refine ⟨lifted_covering_chartedSpace (H := H) π hπ, ?_⟩
  let _ : ChartedSpace H M' := lifted_covering_chartedSpace (H := H) π hπ
  refine ⟨lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hπ, ?_⟩
  refine ⟨hπ, h_surj, ?_⟩
  intro p
  -- The canonical lifted chart around `p` is built from one local inverse branch of the covering
  -- map, and in those coordinates the map `π` is the identity.
  rcases lifted_projection_partial_diffeomorph (I := I) (H := H) π hπ p with
    ⟨Φ, hp, hEq, -⟩
  exact ⟨Φ, hp, hEq⟩

/-- Proposition 4.40 (2): any two smooth structures on the total space that make the covering
projection a smooth covering map determine the same maximal smooth atlas. -/
theorem smooth_covering_same_smooth_structure
    {cs cs' : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (hsm' : let _ : ChartedSpace H M' := cs'
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π) :
    (let _ : ChartedSpace H M' := cs
     let _ : IsManifold I ∞ M' := hsm.1
     IsManifold.maximalAtlas I ∞ M') =
      (let _ : ChartedSpace H M' := cs'
       let _ : IsManifold I ∞ M' := hsm'.1
       IsManifold.maximalAtlas I ∞ M') := by
  -- Route correction: uniqueness is proved by inserting the canonical lifted chart at each overlap
  -- point, rather than by returning to a separate branch-comparison argument.
  apply Set.Subset.antisymm
  · exact smooth_covering_maximalAtlas_subset_via_canonical
      (I := I) (H := H) (π := π) hsm hsm'
  · exact smooth_covering_maximalAtlas_subset_via_canonical
      (I := I) (H := H) (π := π) hsm' hsm

/-- Proposition 4.40, reformulated as existence together with uniqueness up to the canonical owner
`IsManifold.maximalAtlas I ∞ M'`. -/
theorem exists_unique_smooth_covering_structure
    (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ cs : ChartedSpace H M',
      ∃ hsm : let _ : ChartedSpace H M' := cs
        IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π,
      ∀ {cs' : ChartedSpace H M'}
        (hsm' : let _ : ChartedSpace H M' := cs'
          IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π),
        (let _ : ChartedSpace H M' := cs
         let _ : IsManifold I ∞ M' := hsm.1
         IsManifold.maximalAtlas I ∞ M') =
          (let _ : ChartedSpace H M' := cs'
           let _ : IsManifold I ∞ M' := hsm'.1
           IsManifold.maximalAtlas I ∞ M') := by
  -- Once existence and uniqueness are available separately, the final statement is just packaging.
  rcases exists_smooth_covering_structure (I := I) (H := H) π hπ h_surj with ⟨cs, hcs⟩
  refine ⟨cs, hcs, ?_⟩
  intro cs' hsm'
  exact smooth_covering_same_smooth_structure (I := I) (H := H) (π := π) hcs hsm'

end
