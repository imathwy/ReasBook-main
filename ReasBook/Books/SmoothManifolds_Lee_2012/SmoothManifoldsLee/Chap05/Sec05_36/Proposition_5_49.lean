import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Proposition_5_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Exercise_4_16
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- Declarations for this item will be appended below by the statement pipeline.
-- `lean_leansearch` was unavailable in this environment; the statement surface reuses the Chapter 5
-- owner predicates for immersed and embedded submanifolds with boundary.

open TopologicalSpace
open scoped Manifold

universe u𝕜 uE uH uM uE' uH' uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' (⊤ : WithTop ℕ∞) N]

/- Proposition 5.49 (1): this is the canonical mathlib owner theorem
`Manifold.IsSmoothEmbedding.of_opens`, specialized to the manifold-with-boundary setting. -/
#check Manifold.IsSmoothEmbedding.of_opens

omit [IsManifold I (⊤ : WithTop ℕ∞) M] [IsManifold I' (⊤ : WithTop ℕ∞) N] in
/-- Helper for Proposition 5.49: lowering the differentiability index preserves smooth
embeddings. -/
lemma isSmoothEmbedding_of_le {n m : WithTop ℕ∞} {f : N → M} (hmn : m ≤ n)
    (hf : Manifold.IsSmoothEmbedding I' I n f) :
    Manifold.IsSmoothEmbedding I' I m f := by
  -- Keep the same global complement and local chart presentation for the immersion field.
  let hImm := hf.isImmersion
  let hComp := hImm.complement
  let hCompImm := hImm.isImmersionOfComplement_complement
  refine ⟨?_, hf.isEmbedding⟩
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I') (M := N) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Proposition 5.49: a top-order smooth embedding is in particular a `C^∞`
smooth embedding. -/
lemma isSmoothEmbedding_to_infty {f : N → M}
    (hf : Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) f) :
    Manifold.IsSmoothEmbedding I' I (((⊤ : ℕ∞) : WithTop ℕ∞)) f := by
  -- Lower the differentiability order from the ambient `⊤` statement to the owner theorem's `∞`.
  exact
    isSmoothEmbedding_of_le (I := I) (I' := I') (M := M) (N := N)
      (m := (((⊤ : ℕ∞) : WithTop ℕ∞))) (n := (⊤ : WithTop ℕ∞)) (by simp) hf

/-- Helper for Proposition 5.49: the image inclusion factors through the inverse diffeomorphism
onto the image returned by Proposition 5.2. -/
lemma subtype_val_eq_comp_image_diffeomorph_symm {F : N → M}
    [ChartedSpace H' (Set.range F)]
    [IsManifold I' (((⊤ : ℕ∞) : WithTop ℕ∞)) (Set.range F)]
    {Φ : N ≃ₘ^(((⊤ : ℕ∞) : WithTop ℕ∞))⟮I', I'⟯ Set.range F}
    (hΦ : ∀ x, (Φ x : M) = F x) :
    (Subtype.val : Set.range F → M) = F ∘ Φ.symm := by
  -- Evaluate the factorization at a point of the image and rewrite it using `Φ (Φ.symm y) = y`.
  funext y
  simpa using hΦ (Φ.symm y)

/-- Helper for Proposition 5.49: transport the source atlas of `N` to `Set.range F` through the
embedding homeomorphism. -/
noncomputable abbrev transported_range_chartedSpace {F : N → M}
    (e : N ≃ₜ Set.range F) : ChartedSpace H' (Set.range F) := by
  let _ : ChartedSpace N (Set.range F) :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Route correction: use the explicit homeomorphism-to-singleton-chart route, not the opaque
  -- owner image charted space, so later chart transport is visible to Lean.
  exact ChartedSpace.comp H' N (Set.range F)

/-- Helper for Proposition 5.49: the transported range charted space is a smooth manifold at the
outer regularity `⊤`. -/
lemma transported_range_isManifold_top {F : N → M}
    (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) := by
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  have hGroupoid :
      HasGroupoid (Set.range F) (contDiffGroupoid (⊤ : WithTop ℕ∞) I') := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- Both transported charts differ only by their source charts on `N`, so compatibility
    -- reduces to the already-known compatibility of `N`.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) I' := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid (⊤ : WithTop ℕ∞) I') hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The transported smooth atlas now packages directly into an `IsManifold` instance.
  exact IsManifold.mk' I' (⊤ : WithTop ℕ∞) (Set.range F)

/-- Proposition 5.49 (2): the image of a smooth embedding carries the subspace topology and admits
an induced smooth manifold-with-boundary structure for which the inclusion into the ambient
manifold is a smooth embedding. -/
-- This is a bridge/view item: extract the source-facing existence statement from the stronger
-- Chapter 5 owner theorem `smooth_embedding_range_has_induced_manifold_structure`.
theorem smooth_embedding_range_has_manifold_with_boundary {F : N → M}
    (hF : Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) F) :
    ∃ instCharted : ChartedSpace H' (Set.range F),
      ∃ instManifold : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F),
        let _ : ChartedSpace H' (Set.range F) := instCharted
        let _ : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
        Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) (Subtype.val : Set.range F → M) := by
  let e : N ≃ₜ Set.range F := hF.isEmbedding.toHomeomorph
  let instCharted : ChartedSpace H' (Set.range F) :=
    transported_range_chartedSpace e
  let _ : ChartedSpace H' (Set.range F) := instCharted
  have instManifold : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) :=
    transported_range_isManifold_top e
  let _ : IsManifold I' (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
  have hSubtypeImmersion : Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞)
      (Subtype.val : Set.range F → M) := by
    let hImm := hF.isImmersion
    let hComp := hImm.complement
    let hCompImm := hImm.isImmersionOfComplement_complement
    let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
    let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
      ext z
      simp [eS])
    refine ⟨hComp, inferInstance, inferInstance, ?_⟩
    intro x
    let hx := hCompImm (e.symm x)
    -- Transport the source chart of `F` through the homeomorphism onto the image.
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
    · -- The transported source chart still contains the image point `x`.
      simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
    · -- The codomain chart condition is the same pointwise statement as for `F`.
      have hxe : F (e.symm x) = (x : M) := by
        exact congrArg Subtype.val (e.apply_symm_apply x)
      simpa [hxe] using hx.mem_codChart_source
    · -- The transported source chart stays in the maximal atlas after chart transport.
      intro d hd
      rcases hd with ⟨f, hf, c', hc', rfl⟩
      have hfEq : f = eS := by
        simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
          ext z
          simp [eS]) f hf
      subst f
      have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
        simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
      constructor
      · have hleft :
            ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) I' := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').1
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hleft
      · have hright :
            ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) I' := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').2
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hright
    · exact hx.codChart_mem_maximalAtlas
    · -- Source points in the transported chart map into the codomain chart source because
      -- `Subtype.val ∘ e = F`.
      intro z hz
      have hz' : e.symm z ∈ hx.domChart.source := by
        simpa [OpenPartialHomeomorph.trans_source] using hz
      have hze : F (e.symm z) = (z : M) := by
        exact congrArg Subtype.val (e.apply_symm_apply z)
      simpa [hze] using hx.source_subset_preimage_source hz'
    · -- In the transported source chart, the inclusion `Set.range F ↪ M` has exactly the same
      -- written-in-extended-charts form as `F`.
      intro u hu
      have hu' : u ∈ (hx.domChart.extend I').target := by
        simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.extend_coe] using hx.writtenInCharts hu'
  -- The topology on `Set.range F` is still the subspace topology, so immersion plus embedding
  -- gives the desired smooth embedding of the subtype inclusion.
  have hSubtype : Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞)
      (Subtype.val : Set.range F → M) := ⟨hSubtypeImmersion, Topology.IsEmbedding.subtypeVal⟩
  exact ⟨instCharted, instManifold, hSubtype⟩

omit [IsManifold I (⊤ : WithTop ℕ∞) M] in
/-- Helper for Proposition 5.49: once the restricted subtype inclusion is a topological embedding,
the open-subset immersion structure upgrades it to a smooth embedding. -/
lemma subtype_val_isSmoothEmbedding_of_open_embedding {S : Set M}
    [ChartedSpace H' S] [IsManifold I' (⊤ : WithTop ℕ∞) S]
    (hS : Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞) (Subtype.val : S → M))
    (U : Opens S) (hUemb : Topology.IsEmbedding ((↑) : U → M)) :
    Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) ((↑) : U → M) := by
  -- The restricted inclusion factors through the open inclusion `U ↪ S` followed by `S ↪ M`.
  refine Manifold.IsSmoothEmbedding.mk ?_ hUemb
  -- Compose the canonical open immersion of `U` into `S` with the ambient immersed inclusion.
  simpa [Function.comp] using
    Manifold.IsImmersion.ex416_comp hS (Manifold.IsImmersion.of_opens U)

/-- Helper for Proposition 5.49: a partial equivalence with continuous forward and inverse maps
induces a homeomorphism between its source and target subtypes. -/
noncomputable def partialEquiv_sourceTargetHomeomorph {α : Type*} {β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (e : PartialEquiv α β)
    (he : ContinuousOn e e.source) (he_symm : ContinuousOn e.symm e.target) :
    e.source ≃ₜ e.target where
  toFun := Set.MapsTo.restrict e e.source e.target e.mapsTo
  invFun := Set.MapsTo.restrict e.symm e.target e.source e.symm.mapsTo
  left_inv x := Subtype.ext <| e.left_inv x.2
  right_inv y := Subtype.ext <| e.right_inv y.2
  continuous_toFun := he.mapsToRestrict e.mapsTo
  continuous_invFun := he_symm.mapsToRestrict e.symm.mapsTo

omit [IsManifold I (⊤ : WithTop ℕ∞) M] in
/-- Helper for Proposition 5.49: the immersion normal form yields an open neighborhood on which the
subtype inclusion is already a topological embedding. -/
lemma immersion_neighborhood_isEmbedding {S : Set M}
    [ChartedSpace H' S] [IsManifold I' (⊤ : WithTop ℕ∞) S]
    (hS : Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞) (Subtype.val : S → M)) (p : S) :
    ∃ U : Opens S, p ∈ U ∧ Topology.IsEmbedding ((↑) : U → M) := by
  let hp := hS.isImmersionAt p
  let U : Opens S := ⟨(hp.domChart.extend I').source, hp.domChart.isOpen_extend_source (I := I')⟩
  let j : U → (hp.codChart.extend I).source :=
    Set.codRestrict ((↑) : U → M) (hp.codChart.extend I).source fun x ↦ by
      -- The immersion source condition puts the restricted inclusion in the codomain chart source.
      simpa [OpenPartialHomeomorph.extend_source] using
        hp.source_subset_preimage_source (by
          simpa [U, OpenPartialHomeomorph.extend_source] using x.2)
  let modelSuper : (hp.domChart.extend I').target → E :=
    fun u ↦ hp.equiv (((u : E'), (0 : hp.complement)) : E' × hp.complement)
  let model : (hp.domChart.extend I').target → (hp.codChart.extend I).target :=
    Set.codRestrict modelSuper (hp.codChart.extend I).target fun u ↦
      hp.target_subset_preimage_target u.2
  let eDom :=
    partialEquiv_sourceTargetHomeomorph (hp.domChart.extend I')
      (hp.domChart.continuousOn_extend (I := I'))
      (hp.domChart.continuousOn_extend_symm (I := I'))
  let eCod :=
    partialEquiv_sourceTargetHomeomorph (hp.codChart.extend I)
      (hp.codChart.continuousOn_extend (I := I))
      (hp.codChart.continuousOn_extend_symm (I := I))
  have hmodelSuper_emb : Topology.IsEmbedding modelSuper := by
    -- The model map is the standard inclusion `u ↦ (u, 0)` followed by the chosen linear
    -- equivalence from the immersion normal form.
    refine hp.equiv.toHomeomorph.isEmbedding.comp ?_
    exact (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).comp
      (isEmbedding_prodMkLeft (0 : hp.complement))
  have hmodel_emb : Topology.IsEmbedding model := by
    -- Restrict the model map to the codomain chart target supplied by the immersion witness.
    exact hmodelSuper_emb.codRestrict (hp.codChart.extend I).target fun u ↦
      hp.target_subset_preimage_target u.2
  have hchartEq : eCod ∘ j = model ∘ eDom := by
    -- Writing the restricted inclusion in the chosen charts gives exactly the standard model
    -- embedding `u ↦ hp.equiv (u, 0)`.
    funext x
    apply Subtype.ext
    have hx_source : (x : S) ∈ hp.domChart.source := by
      simpa [U, OpenPartialHomeomorph.extend_source] using x.2
    have hx_cod_source : ((x : S) : M) ∈ hp.codChart.source := by
      simpa [OpenPartialHomeomorph.extend_source] using hp.source_subset_preimage_source hx_source
    have hx_target : hp.domChart.extend I' x ∈ (hp.domChart.extend I').target :=
      (hp.domChart.extend I').map_source x.2
    simpa [U, j, model, modelSuper, eDom, eCod, partialEquiv_sourceTargetHomeomorph,
      Function.comp, OpenPartialHomeomorph.extend_coe, hx_source, hx_cod_source,
      hp.domChart.left_inv hx_source] using hp.writtenInCharts hx_target
  have hj_emb : Topology.IsEmbedding j := by
    -- Conjugate the restricted inclusion by the source and codomain chart homeomorphisms.
    have hcomp : Topology.IsEmbedding (eCod ∘ j) := by
      rw [hchartEq]
      exact hmodel_emb.comp eDom.isEmbedding
    exact (Topology.IsEmbedding.of_comp_iff eCod.isEmbedding).mp hcomp
  refine ⟨U, ?_, ?_⟩
  · -- The chosen point lies in the source of the local immersion chart.
    simpa [U, OpenPartialHomeomorph.extend_source] using hp.mem_domChart_source
  · -- Forget the codomain restriction from the chart source back to the ambient manifold.
    simpa [U, j, Function.comp] using Topology.IsEmbedding.subtypeVal.comp hj_emb

/- Proposition 5.49 (3) is the same owner theorem as Proposition 5.5: proper embedding of a
subtype is a topological statement, so the manifold-with-boundary structure does not change the
owner abstraction. -/
#check Set.isProperlyEmbedded_iff_isClosed

/-- Proposition 5.49 (4): every point of an immersed submanifold with boundary has an open
neighborhood whose inclusion into the ambient manifold is a smooth embedding. -/
-- Proof sketch: use the local normal form in the definition of `Manifold.IsImmersion` to choose,
-- around `p`, an open neighborhood `U : Opens S` on which the immersed inclusion
-- `((↑) : U → M)` becomes a smooth embedding.
theorem immersed_submanifold_has_embedded_neighborhood {S : Set M}
    [ChartedSpace H' S] [IsManifold I' (⊤ : WithTop ℕ∞) S]
    (hS : Manifold.IsImmersion I' I (⊤ : WithTop ℕ∞) (Subtype.val : S → M)) (p : S) :
    ∃ U : Opens S, p ∈ U ∧
      Manifold.IsSmoothEmbedding I' I (⊤ : WithTop ℕ∞) ((↑) : U → M) := by
  -- Route correction: the proof follows the source local normal form for immersions, rather than
  -- trying to prove local embeddedness by a direct topological recursion on neighborhoods.
  obtain ⟨U, hpU, hUemb⟩ := immersion_neighborhood_isEmbedding hS p
  -- Upgrade the local topological embedding to a smooth embedding using the restricted immersion.
  refine ⟨U, hpU, ?_⟩
  exact subtype_val_isSmoothEmbedding_of_open_embedding hS U hUemb

end
