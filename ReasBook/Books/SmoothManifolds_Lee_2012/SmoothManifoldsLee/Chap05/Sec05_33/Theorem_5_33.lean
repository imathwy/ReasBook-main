import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_32.Definition_5_32_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_33.Theorem_5_31
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Exercise_4_16
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Theorem_1_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Topology.IsInducing

universe u𝕜 uE uH uM uE' uH'

section WeaklyEmbeddedSubmanifoldUniqueness

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J (⊤ : WithTop ℕ∞) S]

-- Semantic recall note: `lean_leansearch` only returned general immersion/embedding APIs, so the
-- source-facing statement is organized around the local `IsWeaklyEmbeddedSubmanifold` owner and
-- the existing uniqueness theorem `immersed_submanifold_structure_unique_of_same_carrier`.

private noncomputable abbrev immersionProjection {p : S}
    (hImm : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) p) :
    E →L[𝕜] E' :=
  (ContinuousLinearMap.fst 𝕜 E' hImm.complement).comp
    (hImm.equiv.symm).toContinuousLinearMap

-- Helper: the inclusion of a weakly embedded submanifold into the ambient manifold is continuous.
lemma weaklyEmbedded_subtypeVal_continuous
    [IsWeaklyEmbeddedSubmanifold I J S] : Continuous (Subtype.val : S → M) := by
  -- Exercise 4.16 upgrades the pointwise immersion normal form to pointwise continuity.
  rw [continuous_iff_continuousAt]
  intro x
  let hImm : Manifold.IsImmersion J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
    IsWeaklyEmbeddedSubmanifold.isImmersion_subtype_val
  exact (hImm.isImmersionAt x).continuousAt

-- Helper: the given topology on a weakly embedded submanifold is bounded above by the ambient
-- induced topology.
lemma weaklyEmbedded_topology_le_induced
    [IsWeaklyEmbeddedSubmanifold I J S] :
    inferInstanceAs (TopologicalSpace S) ≤
      TopologicalSpace.induced (Subtype.val : S → M) inferInstance := by
  -- Continuity of the ambient inclusion is exactly the induced-topology inequality.
  rw [← continuous_iff_le_induced]
  rw [continuous_iff_continuousAt]
  intro x
  let hImm : Manifold.IsImmersion J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
    IsWeaklyEmbeddedSubmanifold.isImmersion_subtype_val
  exact (hImm.isImmersionAt x).continuousAt

-- Helper: projecting the ambient chart coordinates of an immersed inclusion back to the source
-- factor recovers the source chart coordinates.
lemma immersionProjectionEqDomainCoordinates
    {p q : S}
    (hImm : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] E' := immersionProjection hImm
    π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q := by
  -- Apply the linear projection to the immersion normal form and simplify the chart inverses.
  let π : E →L[𝕜] E' := immersionProjection hImm
  have hq_source : q ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source] using hq
  have hq_target : (hImm.domChart.extend J) q ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  simpa [π, Function.comp, ContinuousLinearMap.comp_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

-- Helper: a local ambient section near each point produces the ambient-open refinement criterion
-- needed to recover the intrinsic topology from the ambient manifold.
lemma weaklyEmbedded_localAmbientRefinements_of_localSection
    (hSection :
      ∀ p : S,
        ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧
          ∃ σ : {x : M // x ∈ V} → S,
            Continuous σ ∧
              ∀ x : S, ∀ hx : x.1 ∈ V, σ ⟨x.1, hx⟩ = x) :
    ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
      ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U := by
  intro p U hU hpU
  rcases hSection p with ⟨V, hV_open, hpV, σ, hσ_cont, hσ_id⟩
  let pV : {x : M // x ∈ V} := ⟨(p : M), hpV⟩
  have hpσ : σ pV = p := by
    simpa [pV] using hσ_id p hpV
  have hpre : σ ⁻¹' U ∈ nhds pV := by
    -- Continuity of the local section turns the intrinsic neighborhood `U` of `p` into a
    -- neighborhood of `p` inside the ambient open subtype `V`.
    have hU_nhds : U ∈ nhds (σ pV) := hpσ ▸ hU.mem_nhds hpU
    exact hσ_cont.continuousAt.preimage_mem_nhds hU_nhds
  rcases mem_nhds_iff.mp hpre with ⟨W, hW_sub, hW_open, hpW⟩
  rcases isOpen_induced_iff.mp hW_open with ⟨W₀, hW₀_open, hW_eq⟩
  have hpW₀ : (p : M) ∈ W₀ := by
    have hp_pre : pV ∈ Subtype.val ⁻¹' W₀ := by
      rw [hW_eq]
      exact hpW
    exact hp_pre
  refine ⟨V ∩ W₀, hV_open.inter hW₀_open, ⟨hpV, hpW₀⟩, ?_⟩
  intro x hxVW
  let xV : {x : M // x ∈ V} := ⟨x.1, hxVW.1⟩
  have hxW : xV ∈ W := by
    have hx_pre : xV ∈ Subtype.val ⁻¹' W₀ := by
      simpa [xV] using hxVW.2
    rw [hW_eq] at hx_pre
    exact hx_pre
  have hxσU : σ xV ∈ U := hW_sub hxW
  have hxσ : σ xV = x := by
    simpa [xV] using hσ_id x hxVW.1
  simpa [hxσ] using hxσU

-- Helper: the ambient-open refinement criterion upgrades the ambient induced topology to the given
-- weakly embedded topology on `S`.
lemma inducedTopology_le_weaklyEmbeddedTopology_of_localAmbientRefinements
    (hRefine :
      ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
        ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U) :
    TopologicalSpace.induced (Subtype.val : S → M) inferInstance ≤
      inferInstanceAs (TopologicalSpace S) := by
  intro U hU
  -- To show that `U` is open in the induced topology, refine each point of `U` by an ambient-open
  -- neighborhood that already lies inside `U`.
  rw [isOpen_iff_mem_nhds]
  intro x hxU
  rcases hRefine x U hU hxU with ⟨V, hV_open, hxV, hVU⟩
  refine mem_nhds_iff.mpr ⟨{y : S | y.1 ∈ V}, hVU, ?_, hxV⟩
  exact isOpen_induced_iff.mpr ⟨V, hV_open, by ext y; rfl⟩

-- Helper: once local ambient refinements are available, the subtype inclusion is already a
-- topological embedding.
lemma weaklyEmbedded_subtypeVal_isEmbedding_of_localAmbientRefinements
    [IsWeaklyEmbeddedSubmanifold I J S]
    (hRefine :
      ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
        ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U) :
    Topology.IsEmbedding (Subtype.val : S → M) := by
  -- Compare the given topology with the ambient induced topology in both directions.
  have hle :
      inferInstanceAs (TopologicalSpace S) ≤
        TopologicalSpace.induced (Subtype.val : S → M) inferInstance := by
    rw [← continuous_iff_le_induced]
    rw [continuous_iff_continuousAt]
    intro x
    let hImm : Manifold.IsImmersion J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
      IsWeaklyEmbeddedSubmanifold.isImmersion_subtype_val
    exact (hImm.isImmersionAt x).continuousAt
  refine ⟨?_, Subtype.val_injective⟩
  exact ⟨le_antisymm
    hle
    (inducedTopology_le_weaklyEmbeddedTopology_of_localAmbientRefinements hRefine)⟩

-- Helper: the weak restriction axiom should produce a local ambient section near each point by
-- retracting ambient immersion coordinates back to the source slice.
lemma immersionProjectedLocalSectionContinuous
    {p : S}
    (hImm : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) p)
    {V : Set M}
    (hV_cod : V ⊆ hImm.codChart.source)
    (hV_target :
      let π : E →L[𝕜] E' := immersionProjection hImm
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target) :
    Continuous (fun x : {y : M // y ∈ V} ↦
      let π : E →L[𝕜] E' := immersionProjection hImm
      (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x.1))) := by
  let π : E →L[𝕜] E' := immersionProjection hImm
  let σ₀ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  -- Rewrite the target chart inverse onto its natural target once, then compose it with the
  -- projected ambient coordinates on the chosen patch.
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(𝕜, E') J ∞ (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hcodChart_mem :
      hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.codChart_mem_maximalAtlas
  have hcodExt :
      ContMDiffOn I 𝓘(𝕜, E) ∞ (hImm.codChart.extend I) V := by
    exact (contMDiffOn_extend hcodChart_mem).mono hV_cod
  have hproj :
      ContMDiffOn I 𝓘(𝕜, E') ∞ (π ∘ (hImm.codChart.extend I)) V := by
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    exact hV_target x hx
  have hσOn : ContMDiffOn I J ∞ σ₀ V := by
    -- The direct chart inverse already lands in `S`, so no codomain-restriction transport is
    -- needed once the projected coordinates stay in the target chart.
    exact hdomChartSymm.comp hproj hmaps
  -- Restrict the ambient-on-`V` continuity statement to the open subtype used in the theorem.
  simpa [σ₀, π, Function.comp] using
    (continuousOn_iff_continuous_restrict).mp hσOn.continuousOn

-- Helper: on the source chart of an immersion normal form, the direct chart inverse section fixes
-- every point of the source slice.
lemma immersionProjectedLocalSectionEqSelf
    {p q : S}
    (hImm : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] E' := immersionProjection hImm
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q)) = q := by
  let π : E →L[𝕜] E' := immersionProjection hImm
  have hq_proj :
      π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
    immersionProjectionEqDomainCoordinates hImm hq
  -- Normalize the projected codomain coordinates back to the intrinsic source coordinates, then
  -- cancel the chart inverse on the source patch.
  calc
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q))
        = (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = q := by
      have hleft : (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) = q :=
        hImm.domChart.extend_left_inv hq
      simpa using hleft

-- Helper: the weak restriction axiom should produce a local ambient section near each point by
-- retracting ambient immersion coordinates back to the source slice.
lemma weaklyEmbedded_hasLocalAmbientSection
    [IsWeaklyEmbeddedSubmanifold I J S] (p : S) :
    ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧
      ∃ σ : {x : M // x ∈ V} → S,
        Continuous σ ∧
          ∀ x : S, ∀ hx : x.1 ∈ V, σ ⟨x.1, hx⟩ = x := by
  let hImm : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) p :=
    IsWeaklyEmbeddedSubmanifold.isImmersion_subtype_val |>.isImmersionAt p
  let π : E →L[𝕜] E' := immersionProjection hImm
  let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  -- Route correction: use the direct subtype-valued chart inverse section instead of an ambient
  -- retraction followed by `weakly_embedded_restriction_axiom`.
  rcases subtypeVal.isOpen_iff.mp hImm.domChart.open_source with
    ⟨W, hW_open, hW_eq⟩
  have hpW : (p : M) ∈ W := by
    have hp_pre : p ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hp_pre
  let T : Set E' := interior ((hImm.domChart.extend J).target)
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := interior_subset
  have hpT : (hImm.domChart.extend J) p ∈ T := by
    have hInteriorPoint :
        J.IsInteriorPoint p ↔
          (hImm.domChart.extend J) p ∈ interior ((hImm.domChart.extend J).target) :=
      J.isInteriorPoint_iff_of_mem_maximalAtlas (show (⊤ : ℕ∞ω) ≠ 0 by simp)
        hImm.domChart_mem_maximalAtlas hImm.mem_domChart_source
    exact hInteriorPoint.1 BoundarylessManifold.isInteriorPoint
  have hp_proj :
      π ((hImm.codChart.extend I) p) = (hImm.domChart.extend J) p :=
    immersionProjectionEqDomainCoordinates hImm hImm.mem_domChart_source
  have hp_projT : (π ∘ (hImm.codChart.extend I)) p ∈ T := by
    simpa [Function.comp] using hp_proj.symm ▸ hpT
  have hπ_cont :
      ContinuousAt (π ∘ (hImm.codChart.extend I)) p := by
    exact π.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend hImm.mem_codChart_source)
  have hpre :
      ((π ∘ (hImm.codChart.extend I)) ⁻¹' T) ∈ nhds (p : M) := by
    exact hπ_cont.preimage_mem_nhds (isOpen_interior.mem_nhds hp_projT)
  rcases mem_nhds_iff.mp hpre with ⟨V₀, hV₀_sub, hV₀_open, hpV₀⟩
  let V : Set M := hImm.codChart.source ∩ (W ∩ V₀)
  have hcod_open : IsOpen hImm.codChart.source := hImm.codChart.open_source
  have hV_open : IsOpen V := hcod_open.inter (hW_open.inter hV₀_open)
  have hpV : (p : M) ∈ V := ⟨hImm.mem_codChart_source, hpW, hpV₀⟩
  have hV_cod : V ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hV_target :
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target := by
    intro x hx
    exact hT_sub (hV₀_sub hx.2.2)
  refine ⟨V, hV_open, hpV, (fun x : {y : M // y ∈ V} ↦ σ x.1), ?_, ?_⟩
  · -- The projected-coordinate formula is continuous on the ambient patch, so it is continuous on
    -- the ambient-open subtype used for the local section.
    exact immersionProjectedLocalSectionContinuous hImm hV_cod hV_target
  · intro x hx
    have hx_dom : x ∈ hImm.domChart.source := by
      -- The ambient realization of the source chart domain turns the `W`-part of `V` back into
      -- an intrinsic source-chart membership statement.
      have hx_pre : x ∈ Subtype.val ⁻¹' W := hx.2.1
      rw [hW_eq] at hx_pre
      exact hx_pre
    -- On nearby points of `S`, the direct section reduces to the identity by the immersion normal
    -- form in coordinates.
    simpa [σ, π] using
      immersionProjectedLocalSectionEqSelf hImm hx_dom

-- Helper: a weakly embedded submanifold has the ambient-open neighborhood refinements required to
-- recover its intrinsic topology from the ambient manifold.
lemma weaklyEmbedded_localAmbientRefinements
    [IsWeaklyEmbeddedSubmanifold I J S] :
    ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
      ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U := by
  -- Reduce the topological refinement statement to the local ambient section interface.
  have hSection :
      ∀ p : S,
        ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧
          ∃ σ : {x : M // x ∈ V} → S,
            Continuous σ ∧ ∀ x : S, ∀ hx : x.1 ∈ V, σ ⟨x.1, hx⟩ = x :=
    (@weaklyEmbedded_hasLocalAmbientSection
      𝕜 _ E _ _ H _ M _ _ I _ E' _ _ H' _ J S _ _ _)
  exact weaklyEmbedded_localAmbientRefinements_of_localSection hSection

-- Helper: by Problem 5-16, every weakly embedded submanifold is an embedded submanifold with the
-- same topology and smooth structure.
instance instIsEmbeddedSubmanifoldOfIsWeaklyEmbeddedSubmanifold
    [IsWeaklyEmbeddedSubmanifold I J S] : IsEmbeddedSubmanifold I J S := by
  -- Package the already-given immersion with the recovered topological embedding of the subtype
  -- inclusion.
  refine
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := ?_ }
  refine ⟨?_, ?_⟩
  · exact IsWeaklyEmbeddedSubmanifold.isImmersion_subtype_val
  · have hRefine :
        ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
          ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U :=
      (@weaklyEmbedded_localAmbientRefinements
        𝕜 _ E _ _ H _ M _ _ I _ E' _ _ H' _ J S _ _ _)
    exact
      (@weaklyEmbedded_subtypeVal_isEmbedding_of_localAmbientRefinements
        𝕜 _ E _ _ H _ M _ _ I _ E' _ _ H' _ J S _ _ _) hRefine

/-- Theorem 5.33. If `M` is a smooth manifold and `S ⊆ M` is a weakly embedded submanifold, then
`S` has only one topology and smooth structure with respect to which it is an immersed
submanifold. -/
theorem weakly_embedded_submanifold_structure_unique
    [IsWeaklyEmbeddedSubmanifold I J S]
    (T : Manifold.ImmersedSubmanifold I M) (hT : T.carrier = S) :
    ∃ Φ : T ≃ₘ⟮modelWithCornersSelf 𝕜 T.ModelSpace, J⟯ S,
      ∀ x : T, (Φ x : M) = T.inclusion x := by
  -- Once the weakly embedded structure has been upgraded to an embedded one, Theorem 5.31 applies
  -- verbatim to the same carrier.
  letI : IsEmbeddedSubmanifold I J S :=
    instIsEmbeddedSubmanifoldOfIsWeaklyEmbeddedSubmanifold
  simpa using
    immersed_submanifold_structure_unique_of_same_carrier T hT

end WeaklyEmbeddedSubmanifoldUniqueness
