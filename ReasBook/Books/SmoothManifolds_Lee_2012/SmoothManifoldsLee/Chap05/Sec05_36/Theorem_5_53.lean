import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_32.Corollary_5_30
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_32.Theorem_5_27

open scoped Manifold
open Manifold

section RestrictingMapsToSubmanifoldsWithBoundary

universe u𝕜 uE uH uM uE' uH' uS uE'' uH'' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {S : Set M}
variable [ChartedSpace H' S]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ⊤ S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

-- Layer triage:
-- * source-facing bridge: Theorem 5.53 (1), a specialization of `contMDiff_restrict_subtype`
--   to a manifold-with-boundary subtype whose inclusion is given by the owner object
--   `IsSmoothEmbedding`.
-- * core/canonical recall: Theorem 5.53 (2), namely
--   `Manifold.IsSmoothEmbedding.contMDiff_toSubtype`.

/-- Helper for Theorem 5.53: the subtype inclusion of a manifold-with-boundary submanifold is
globally smooth when its smooth structure is supplied by an ambient `IsSmoothEmbedding`. -/
lemma subtype_val_contMDiff_of_isSmoothEmbedding
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M)) :
    ContMDiff J I ⊤ (Subtype.val : S → M) := by
  -- Smoothness is verified pointwise from the immersion normal form carried by `hS`.
  have hSmoothTop : ContMDiff J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) := by
    intro x
    let hImmAt : IsImmersionAt J I ⊤ (Subtype.val : S → M) x :=
      hS.isImmersion.isImmersionAt x
    let x' : E' := (hImmAt.domChart.extend J) x
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    -- The inclusion is the canonical continuous map from the subtype into the ambient manifold.
    have hcont : ContinuousAt (Subtype.val : S → M) x :=
      continuous_subtype_val.continuousAt
    have hx : x ∈ hImmAt.domChart.source :=
      hImmAt.mem_domChart_source
    have hy : (Subtype.val : S → M) x ∈ hImmAt.codChart.source :=
      hImmAt.mem_codChart_source
    -- In immersion charts, the subtype inclusion is the linear map `u ↦ (u, 0)`.
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
      (e := hImmAt.domChart) (e' := hImmAt.codChart) hImmAt.domChart_mem_maximalAtlas
      hImmAt.codChart_mem_maximalAtlas hx hy, continuousWithinAt_univ, Set.preimage_univ,
      Set.univ_inter]
    refine ⟨hcont, ?_⟩
    have hmodel : ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞) L (Set.range J) x' := by
      exact L.contDiff.contDiffWithinAt
    have htarget_mem : (hImmAt.domChart.extend J).target ∈ nhdsWithin x' (Set.range J) := by
      simpa [x'] using hImmAt.domChart.extend_target_mem_nhdsWithin (I := J) hx
    have hEq :
        ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hImmAt.domChart.extend J).symm)
          =ᶠ[nhdsWithin x' (Set.range J)] L := by
      refine Filter.eventuallyEq_of_mem htarget_mem ?_
      intro z hz
      simpa [Function.comp, L] using hImmAt.writtenInCharts hz
    have hx'_target : x' ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx
    have hx'_range : x' ∈ Set.range J :=
      hImmAt.domChart.extend_target_subset_range hx'_target
    exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range
  exact hSmoothTop

/-- Theorem 5.53 (1): if `S ⊆ M` is an embedded submanifold with boundary and `F : M → N` is
smooth, then the restriction `S → N` is smooth. -/
theorem contMDiff_restrict_subtype_of_isEmbeddedSubmanifoldWithBoundary
    {F : M → N} (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    (hF : ContMDiff I K ⊤ F) :
    ContMDiff J K ⊤ (fun x : S ↦ F x.1) := by
  -- The inclusion `Subtype.val : S → M` is the governing object, and restriction is its
  -- composition with the ambient smooth map `F`.
  have hsub : ContMDiff J I ⊤ (Subtype.val : S → M) :=
    subtype_val_contMDiff_of_isSmoothEmbedding (I := I) (J := J) (S := S) hS
  simpa using contMDiff_restrict_subtype hsub F hF

/- Theorem 5.53 (2): this is exactly the canonical owner theorem
`Manifold.IsSmoothEmbedding.contMDiff_toSubtype`; no additional boundaryless hypothesis on the
ambient manifold belongs in the statement. -/
recall Manifold.IsSmoothEmbedding.contMDiff_toSubtype

end RestrictingMapsToSubmanifoldsWithBoundary
