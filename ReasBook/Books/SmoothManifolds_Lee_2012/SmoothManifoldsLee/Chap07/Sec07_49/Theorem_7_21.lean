import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_33.Theorem_5_33
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Proposition_5_22
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_49
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_53.Problem_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped LieGroup Manifold ContDiff
open Topology
open Manifold

universe u𝕜 uE uH uG

-- Domain sampling pass:
-- * primary domain: smooth embeddings of Lie subgroup inclusions;
-- * source-facing owner: `LieSubgroup I`;
-- * core/canonical owner: `Manifold.IsSmoothEmbedding` for the subgroup inclusion;
-- * sampled owner declarations: `Manifold.IsSmoothEmbedding`,
--   `smooth_embedding_of_injective_isImmersion_isClosedMap`,
--   `IsClosed.isClosedMap_subtype_val`;
-- * primitive data already stored by `LieSubgroup`: subgroup carrier, chosen smooth structure,
--   Lie-group structure, and `subtype_val_isImmersion`;
-- * derived API here: closedness of the carrier upgrades that immersion to a smooth embedding.

section ClosedLieSubgroups

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H}
variable [LieGroup I (⊤ : WithTop ℕ∞) G]

namespace LieSubgroup

/-- Helper for Theorem 7.21: the immersion normal form for the subgroup inclusion carries a
continuous linear projection from ambient chart coordinates back to subgroup coordinates. -/
private noncomputable abbrev subtypeValImmersionProjection
    {S : LieSubgroup I} {p : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p) :
    E →L[𝕜] S.ModelSpace :=
  (ContinuousLinearMap.fst 𝕜 S.ModelSpace hImm.complement).comp
    hImm.equiv.symm.toContinuousLinearMap

/-- Helper for Theorem 7.21: projecting the ambient immersion normal form back to subgroup
coordinates recovers the intrinsic source chart coordinates. -/
lemma subtypeValImmersionProjection_eqDomainCoordinates
    {S : LieSubgroup I} {p q : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
    π ((hImm.codChart.extend I) q) =
      (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) q := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
  have hq_source : q ∈ (hImm.domChart.extend J).source := by
    simpa [J, hImm.domChart.extend_source] using hq
  have hq_target : (hImm.domChart.extend J) q ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  -- Simplify the immersion normal form after applying the coordinate projection.
  simpa [π, J, Function.comp, ContinuousLinearMap.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

/-- Helper for Theorem 7.21: on an ambient patch where the projected coordinates stay in the
source chart target, the direct chart-inverse section is continuous. -/
lemma subtypeValImmersionProjectedLocalSectionContinuous
    {S : LieSubgroup I} {p : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    {V : Set G}
    (hV_cod : V ⊆ hImm.codChart.source)
    (hV_target :
      let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈
        (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target) :
    Continuous (fun x : {y : G // y ∈ V} ↦
      let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
      (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm
        (π ((hImm.codChart.extend I) x.1))) := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
  let σ₀ : G → S.carrier := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S.carrier :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(𝕜, S.ModelSpace) J ∞ (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [J, Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hcodChart_mem :
      hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) G :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.codChart_mem_maximalAtlas
  have hcodExt :
      ContMDiffOn I 𝓘(𝕜, E) ∞ (hImm.codChart.extend I) V := by
    exact (contMDiffOn_extend hcodChart_mem).mono hV_cod
  have hproj :
      ContMDiffOn I 𝓘(𝕜, S.ModelSpace) ∞ (π ∘ (hImm.codChart.extend I)) V := by
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    exact hV_target x hx
  have hσOn : ContMDiffOn I J ∞ σ₀ V := by
    -- The direct chart inverse already lands in the subgroup once the projected coordinates stay
    -- inside the intrinsic chart target.
    exact hdomChartSymm.comp hproj hmaps
  simpa [σ₀, π, J, Function.comp] using
    (continuousOn_iff_continuous_restrict).mp hσOn.continuousOn

/-- Helper for Theorem 7.21: on the intrinsic source branch of the immersion normal form, the
projected ambient section fixes each subgroup point. -/
lemma subtypeValImmersionProjectedLocalSectionEqSelf
    {S : LieSubgroup I} {p q : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
    (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm
      (π ((hImm.codChart.extend I) q)) = q := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
  have hq_proj :
      π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
    subtypeValImmersionProjection_eqDomainCoordinates (I := I) hImm hq
  -- Rewrite the projected coordinates to the intrinsic chart coordinates, then cancel the chart
  -- inverse on the source branch.
  calc
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q))
        = (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = q := by
      have hleft : (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) = q :=
        hImm.domChart.extend_left_inv hq
      simpa using hleft

/-- Helper for Theorem 7.21: lowering the differentiability order from `⊤` to `∞` preserves the
subgroup inclusion immersion. -/
lemma subtypeVal_isImmersion_infty (S : LieSubgroup I) :
    IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) := by
  -- Keep the same complement and the same chart normal form while lowering the atlas order.
  let hComp := S.subtype_val_isImmersion.complement
  let hCompImm := S.subtype_val_isImmersion.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact
      (IsManifold.maximalAtlas_subset_of_le
        (I := modelWithCornersSelf 𝕜 S.ModelSpace)
        (M := S.carrier)
        (m := (∞ : ℕ∞ω))
        (n := (⊤ : WithTop ℕ∞))
        (by simp)) hx.domChart_mem_maximalAtlas
  · exact
      (IsManifold.maximalAtlas_subset_of_le
        (I := I)
        (M := G)
        (m := (∞ : ℕ∞ω))
        (n := (⊤ : WithTop ℕ∞))
        (by simp)) hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 7.21: the subgroup inclusion is already a smooth embedding on some
open neighborhood of the identity in the chosen Lie-subgroup topology. -/
lemma subtypeVal_identityNeighborhood_isSmoothEmbedding (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (⊤ : WithTop ℕ∞)
        (fun x : U ↦ (show G from x.1.1)) := by
  -- Route correction: Proposition 5.22 already applies to the canonical immersed-submanifold
  -- owner `S.toImmersedSubmanifold`, so no literal-subtype transport through Proposition 5.49 is
  -- needed here.
  rcases
      Manifold.ImmersedSubmanifold.exists_open_neighborhood_isSmoothEmbedding
        (S := S.toImmersedSubmanifold) (p := (1 : S.carrier)) with
    ⟨U, h1U, hUemb⟩
  -- Normalize the owner-specific inclusion back to the local subgroup spelling used in this file.
  exact ⟨U, h1U, by
    simpa [LieSubgroup.toImmersedSubmanifold, Function.comp] using hUemb⟩

/-- Helper for Theorem 7.21: the subgroup inclusion is already a topological embedding on some
open neighborhood of the identity in the chosen Lie-subgroup topology. -/
lemma subtypeVal_identityNeighborhood_isEmbedding (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      Topology.IsEmbedding (fun x : U ↦ (show G from x.1.1)) := by
  rcases subtypeVal_identityNeighborhood_isSmoothEmbedding (𝕜 := 𝕜) (I := I) S with
    ⟨U, h1U, hUsmoothEmb⟩
  -- Forget smoothness and retain only the embedding component needed in the later topology step.
  exact ⟨U, h1U, hUsmoothEmb.isEmbedding⟩

/-- Helper for Theorem 7.21: the immersion chart at the identity provides an ambient-open patch
with a subgroup-valued projected local section back into the identity branch. -/
lemma subtypeVal_identityNeighborhood_localSection (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
        ∃ σ : {x : G // x ∈ V} → U,
          Continuous σ ∧
            ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
              σ ⟨(x : S.carrier).1, hx⟩ = x := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let hImm :
      Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G)
        (1 : S.carrier) :=
    S.subtype_val_isImmersion.isImmersionAt (1 : S.carrier)
  let U : TopologicalSpace.Opens S.carrier :=
    ⟨(hImm.domChart.extend J).source, hImm.domChart.isOpen_extend_source (I := J)⟩
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection (I := I) hImm
  let T : Set S.ModelSpace := (hImm.domChart.extend J).target
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := fun _ hx ↦ hx
  have h1T : (hImm.domChart.extend J) (1 : S.carrier) ∈ T := by
    exact (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  have h1_proj :
      π ((hImm.codChart.extend I) (1 : G)) = (hImm.domChart.extend J) (1 : S.carrier) := by
    -- The projection removes the complement coordinates from the immersion normal form.
    simpa [π, J] using
      subtypeValImmersionProjection_eqDomainCoordinates (I := I) hImm hImm.mem_domChart_source
  have h1_projT : (π ∘ (hImm.codChart.extend I)) (1 : G) ∈ T := by
    simpa [Function.comp] using h1_proj.symm ▸ h1T
  have hπ_cont : ContinuousAt (π ∘ (hImm.codChart.extend I)) (1 : G) := by
    exact π.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend hImm.mem_codChart_source)
  have hpre : ((π ∘ (hImm.codChart.extend I)) ⁻¹' T) ∈ nhds (1 : G) := by
    exact hπ_cont.preimage_mem_nhds ((hImm.domChart.isOpen_extend_target (I := J)).mem_nhds h1_projT)
  rcases mem_nhds_iff.mp hpre with ⟨V₀, hV₀_sub, hV₀_open, h1V₀⟩
  let V : Set G := hImm.codChart.source ∩ V₀
  have hV_open : IsOpen V := hImm.codChart.open_source.inter hV₀_open
  have h1V : (1 : G) ∈ V := ⟨hImm.mem_codChart_source, h1V₀⟩
  have hV_cod : V ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hV_target :
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target := by
    intro x hx
    exact hT_sub (hV₀_sub hx.2)
  let σ₀ : {x : G // x ∈ V} → S.carrier := fun x ↦
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x.1))
  have hσ₀_mem :
      ∀ x : {x : G // x ∈ V}, σ₀ x ∈ U := by
    intro x
    have hx_target : π ((hImm.codChart.extend I) x.1) ∈ (hImm.domChart.extend J).target :=
      hV_target x.1 x.2
    simpa [σ₀, U, OpenPartialHomeomorph.extend_source] using
      (hImm.domChart.extend J).map_target hx_target
  let σ : {x : G // x ∈ V} → U := fun x ↦ ⟨σ₀ x, hσ₀_mem x⟩
  have hσ_cont : Continuous σ := by
    -- The projected ambient chart inverse is continuous on the chosen ambient patch.
    have hσ₀_cont : Continuous σ₀ := by
      simpa [σ₀, π, J] using
        subtypeValImmersionProjectedLocalSectionContinuous (I := I) hImm hV_cod hV_target
    exact hσ₀_cont.subtype_mk hσ₀_mem
  have hσ_id :
      ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
        σ ⟨(x : S.carrier).1, hx⟩ = x := by
    intro x hx
    apply Subtype.ext
    have hx_dom : ((x : U) : S.carrier) ∈ hImm.domChart.source := by
      simpa [U, OpenPartialHomeomorph.extend_source] using x.2
    -- On the chosen identity branch, the projected section cancels back to the original point.
    simpa [σ, σ₀, π, J] using
      subtypeValImmersionProjectedLocalSectionEqSelf (I := I) hImm hx_dom
  have h1U : (1 : S.carrier) ∈ U := by
    simpa [U, OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  exact ⟨U, h1U, V, hV_open, h1V, σ, hσ_cont, hσ_id⟩

/-- Helper for Theorem 7.21: once the identity neighborhood filter on `S.carrier` agrees with the
ambient pullback filter, the subgroup inclusion is a topological embedding. -/
lemma subtypeVal_isEmbedding_of_nhdsOneEqComap (S : LieSubgroup I)
    (hnhds :
      𝓝 (1 : S.carrier) =
        Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G))) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
  -- For a group homomorphism, equality of the neighborhood filter at the identity is exactly the
  -- `IsInducing` criterion; injectivity then upgrades it to an embedding.
  refine Topology.IsEmbedding.mk ?_ Subtype.val_injective
  simpa using
    (IsTopologicalGroup.isInducing_iff_nhds_one (f := S.carrier.subtype)).2 hnhds

/-- Helper for Theorem 7.21: if the carrier of `S` is closed in `G`, then the identity
neighborhood filter on `S.carrier` agrees with the ambient pullback filter. -/
lemma subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isClosed (S : LieSubgroup I)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      Topology.IsEmbedding (fun x : U ↦ (show G from x.1.1)) ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U := by
  -- Route correction: Proposition 5.49 only gives the intrinsic embedding patch `U`; the real
  -- closed-subgroup step is to find an ambient neighborhood whose intersection with `S` lies in
  -- that patch.
  rcases subtypeVal_identityNeighborhood_isEmbedding (𝕜 := 𝕜) (I := I) S with
    ⟨U, h1U, hUemb⟩
  refine ⟨U, h1U, hUemb, ?_⟩
  -- TODO: prove the precise missing bridge for this file:
  -- from the intrinsic embedding patch `U` around `1`, upgrade the chart-level local section from
  -- `subtypeVal_identityNeighborhood_localSection` to an ambient trace statement by spending
  -- `hS_closed` together with `exists_nhds_one_subset_mul_inv_mem` to exclude extra nearby sheets
  -- of the immersed subgroup.
  -- The current frontier is precise: we now have an explicit ambient-open patch and a projected
  -- local section onto the identity branch, but still need the closed-subgroup argument showing
  -- every subgroup point in a smaller ambient neighborhood actually lies on that branch.
  sorry

/-- Helper for Theorem 7.21: once the identity branch admits one ambient trace neighborhood,
right translation transports it to arbitrary points and arbitrary intrinsic neighborhoods. -/
lemma subtypeVal_localAmbientRefinements_of_isClosed (S : LieSubgroup I)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    ∀ p : S.carrier, ∀ U : Set S.carrier, IsOpen U → p ∈ U →
      ∃ V : Set G, IsOpen V ∧ p.1 ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
  rcases subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isClosed
      (𝕜 := 𝕜) (I := I) S hS_closed with
    ⟨U₀, h1U₀, hU₀emb, V₀, hV₀_open, h1V₀, hV₀_sub⟩
  intro p U hU hpU
  let τS : S.carrier ≃ₜ S.carrier := Homeomorph.mulRight p
  let oneU₀ : U₀ := ⟨(1 : S.carrier), h1U₀⟩
  let AU : Set U₀ := Subtype.val ⁻¹' (τS ⁻¹' U)
  have hτS_pre_open : IsOpen (τS ⁻¹' U) := τS.continuous.isOpen_preimage _ hU
  have hAU_open : IsOpen AU := by
    -- Pull the translated intrinsic neighborhood back to the identity patch `U₀`.
    exact (TopologicalSpace.Opens.isOpenEmbedding' U₀).continuous.isOpen_preimage _ hτS_pre_open
  obtain ⟨W, hW_open, hW_pre⟩ := (hU₀emb.toIsInducing.isOpen_iff).1 hAU_open
  have h1W : (1 : G) ∈ W := by
    have honeAU : oneU₀ ∈ AU := by
      -- Translating the identity by `p` lands at the target point `p`.
      simpa [AU, τS, oneU₀] using hpU
    have hone_pre : oneU₀ ∈ (fun x : U₀ ↦ (show G from x.1.1)) ⁻¹' W := by
      rw [hW_pre]
      exact honeAU
    simpa using hone_pre
  let τGinv : G ≃ₜ G := Homeomorph.mulRight (p.1)⁻¹
  refine ⟨τGinv ⁻¹' (W ∩ V₀), ?_, ?_, ?_⟩
  · -- Translate the identity ambient neighborhood back to a neighborhood of `p`.
    exact τGinv.continuous.isOpen_preimage _ (hW_open.inter hV₀_open)
  · simpa [τGinv] using show p.1 * p.1⁻¹ ∈ W ∩ V₀ by simp [h1W, h1V₀]
  · intro x hx
    let xShift : S.carrier := x * p⁻¹
    have hxShiftW : xShift.1 ∈ W := by
      simpa [τGinv, xShift] using hx.1
    have hxShiftV₀ : xShift.1 ∈ V₀ := by
      simpa [τGinv, xShift] using hx.2
    have hxShiftU₀ : xShift ∈ U₀ := hV₀_sub hxShiftV₀
    have hxShiftAU : (⟨xShift, hxShiftU₀⟩ : U₀) ∈ AU := by
      have hxShiftPre : (⟨xShift, hxShiftU₀⟩ : U₀) ∈
          (fun y : U₀ ↦ (show G from y.1.1)) ⁻¹' W := by
        simpa [xShift] using hxShiftW
      rw [hW_pre] at hxShiftPre
      exact hxShiftPre
    have hxShiftU : xShift ∈ τS ⁻¹' U := by
      simpa [AU] using hxShiftAU
    -- Translating the refined identity-branch point back by `p` returns the original subgroup
    -- point, so the ambient neighborhood already lies in the target intrinsic neighborhood.
    simpa [τS, xShift, mul_assoc] using hxShiftU

/-- Helper for Theorem 7.21: local ambient neighborhood refinements force the chosen Lie-subgroup
topology to coincide with the ambient induced topology, hence the inclusion is an embedding. -/
lemma subtypeVal_isEmbedding_of_localAmbientRefinements (S : LieSubgroup I)
    (hRefine :
      ∀ p : S.carrier, ∀ U : Set S.carrier, IsOpen U → p ∈ U →
        ∃ V : Set G, IsOpen V ∧ p.1 ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  have hcontSub : Continuous (Subtype.val : S.carrier → G) := by
    -- Every immersion witness for the subgroup inclusion already packages continuity.
    rw [continuous_iff_continuousAt]
    intro x
    exact (S.subtype_val_isImmersion.isImmersionAt x).continuousAt
  have hnhds :
      𝓝 (1 : S.carrier) =
        Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) := by
    apply le_antisymm
    · exact Filter.Tendsto.le_comap <|
        (hcontSub.continuousAt : ContinuousAt (Subtype.val : S.carrier → G) 1)
    · rw [Filter.le_def]
      intro A hA
      rcases mem_nhds_iff.mp hA with ⟨A₀, hA₀_sub, hA₀_open, h1A₀⟩
      rcases hRefine (1 : S.carrier) A₀ hA₀_open h1A₀ with ⟨V, hV_open, h1V, hVA₀⟩
      have hpre_mem :
          (Subtype.val : S.carrier → G) ⁻¹' V ∈
            Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) :=
        Filter.preimage_mem_comap (hV_open.mem_nhds h1V)
      refine Filter.mem_of_superset hpre_mem ?_
      intro x hx
      exact hA₀_sub (hVA₀ hx)
  -- The local ambient refinements at the identity give the reverse neighborhood inequality, so the
  -- general topological-group embedding criterion applies.
  exact subtypeVal_isEmbedding_of_nhdsOneEqComap (𝕜 := 𝕜) (I := I) S hnhds

/-- Helper for Theorem 7.21: if the carrier of `S` is closed in `G`, then the identity
neighborhood filter on `S.carrier` agrees with the ambient pullback filter. -/
lemma subtypeVal_nhdsOneEqComap_of_isClosed (S : LieSubgroup I)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    𝓝 (1 : S.carrier) =
      Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) := by
  rcases subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isClosed
      (𝕜 := 𝕜) (I := I) S hS_closed with
    ⟨U, h1U, hUemb, V, hV_open, h1V, hV_sub⟩
  let oneU : U := ⟨(1 : S.carrier), h1U⟩
  let j : U → G := fun x : U ↦ (x : S.carrier).1
  have hcontSub : Continuous (Subtype.val : S.carrier → G) := by
    -- Every pointwise immersion witness for the subgroup inclusion already contains continuity.
    rw [continuous_iff_continuousAt]
    intro x
    exact (S.subtype_val_isImmersion.isImmersionAt x).continuousAt
  apply le_antisymm
  · -- Continuity of the subgroup inclusion gives the easy filter inequality.
    exact Filter.Tendsto.le_comap <|
      (hcontSub.continuousAt : ContinuousAt (Subtype.val : S.carrier → G) 1)
  · -- The only remaining input is the ambient-open refinement into the intrinsic embedding patch.
    rw [Filter.le_def]
    intro A hA
    rcases mem_nhds_iff.mp hA with ⟨A₀, hA₀_sub, hA₀_open, h1A₀⟩
    let AU : Set U := Subtype.val ⁻¹' A₀
    have hAU_open : IsOpen AU := by
      exact (TopologicalSpace.Opens.isOpenEmbedding' U).continuous.isOpen_preimage _ hA₀_open
    obtain ⟨W, hW_open, hW_pre⟩ := (hUemb.toIsInducing.isOpen_iff).1 hAU_open
    have h1W : (1 : G) ∈ W := by
      have honeU_mem : oneU ∈ AU := by
        simpa [AU, oneU] using h1A₀
      have honeU_pre : oneU ∈ j ⁻¹' W := by
        rw [hW_pre]
        exact honeU_mem
      simpa [j, Function.comp, oneU] using honeU_pre
    have hWV_mem : W ∩ V ∈ 𝓝 (1 : G) := by
      exact (hW_open.inter hV_open).mem_nhds ⟨h1W, h1V⟩
    have hpre_mem :
        (Subtype.val : S.carrier → G) ⁻¹' (W ∩ V) ∈
          Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) :=
      Filter.preimage_mem_comap hWV_mem
    refine Filter.mem_of_superset hpre_mem ?_
    intro x hx
    have hxU : x ∈ U := hV_sub hx.2
    have hx_preW : (⟨x, hxU⟩ : U) ∈ j ⁻¹' W := by
      simpa [j, Function.comp] using hx.1
    have hxAU : (⟨x, hxU⟩ : U) ∈ AU := by
      rw [hW_pre] at hx_preW
      exact hx_preW
    have hxA₀ : x ∈ A₀ := by
      simpa [AU] using hxAU
    exact hA₀_sub hxA₀

/-- Theorem 7.21: if a Lie subgroup `S ≤ G` is closed in `G`, then its inclusion `S ↪ G` is a
smooth embedding. -/
theorem isSmoothEmbedding_of_isClosed (S : LieSubgroup I)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) := by
  -- Route correction: finish through the Chapter 5 ambient-refinement criterion instead of the
  -- older neighborhood-filter detour.
  refine Manifold.IsSmoothEmbedding.mk (subtypeVal_isImmersion_infty (𝕜 := 𝕜) (I := I) S) ?_
  exact subtypeVal_isEmbedding_of_localAmbientRefinements (𝕜 := 𝕜) (I := I) S
    (subtypeVal_localAmbientRefinements_of_isClosed (𝕜 := 𝕜) (I := I) S hS_closed)

end LieSubgroup

end ClosedLieSubgroups
