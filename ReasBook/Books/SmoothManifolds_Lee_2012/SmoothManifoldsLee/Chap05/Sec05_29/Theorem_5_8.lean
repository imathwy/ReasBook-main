import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Definition_5_29_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Theorem_5_8.Index
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Theorem_5_8.LocalNormalFormAPI

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u

open LocalNormalFormAPI Set ChartedSpace

section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Helper for Theorem 5.8: an open subset of the subtype `S` is the preimage of an ambient open
set in `M`. -/
private theorem subtype_open_eq_preimage_ambient_open
    {S : Set M} {U : Set S} (hU : IsOpen U) :
    ∃ W : Set M, IsOpen W ∧ U = {y : S | y.1 ∈ W} := by
  -- Open sets in the subtype topology are exactly preimages of ambient open sets along the
  -- inclusion `S ↪ M`.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hU with ⟨W, hW, hEq⟩
  exact ⟨W, hW, hEq.symm⟩

/-- Helper for Theorem 5.8: restricting the subtype inclusion to an ambient open patch preserves
the topological-embedding property. -/
private theorem subtype_patch_inclusion_isEmbedding
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S)
    {W : Set M} :
    Topology.IsEmbedding ((↑) : {y : S | y.1 ∈ W} → M) := by
  -- The patch inclusion is the canonical subtype embedding into `S`, followed by the global
  -- subtype inclusion `S ↪ M`, which is a topological embedding for embedded submanifolds.
  exact hEmb.isSmoothEmbedding_subtype_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal

/-- Helper for Theorem 5.8: a `C^∞` immersion is also an immersion at the smoothness level
`(↑⊤ : WithTop ℕ∞)` used by the local normal-form API. -/
private theorem isImmersion_coe_top
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    {f : S → M}
    (hf : Manifold.IsImmersion (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) f) :
    Manifold.IsImmersion (𝓡 k) (𝓡 n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f := by
  rcases hf with ⟨F, _, _, hF⟩
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hF x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      hx.equiv hx.domChart hx.codChart
      hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
      hx.source_subset_preimage_source hx.writtenInCharts
  · exact IsManifold.maximalAtlas_subset_of_le
      (I := 𝓡 k)
      (M := S)
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      le_top
      hx.domChart_mem_maximalAtlas
  · exact IsManifold.maximalAtlas_subset_of_le
      (I := 𝓡 n)
      (M := M)
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      le_top
      hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 5.8: the domain chart source from the local immersion normal form is
exactly the ambient subtype patch cut out by the restricted codomain chart. -/
private theorem local_normal_form_source_image_eq_restricted_patch
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (x : S)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : S → M) x (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_sub : W ⊆ hNF.codChart.source)
    (hW_eq : hNF.domChart.source = {y : S | y.1 ∈ W}) :
    Subtype.val '' hNF.domChart.source = S ∩ (hNF.codChart.restr W).source := by
  -- Normalize the restricted ambient source to `W`, then both sides become the same subtype patch
  -- `S ∩ W`.
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzW : z.1 ∈ W := by
      simpa [hW_eq] using hz
    refine ⟨z.2, ?_⟩
    rw [hNF.codChart.restr_source' W hW_open]
    exact ⟨hW_sub hzW, hzW⟩
  · rintro ⟨hyS, hyRestr⟩
    rw [hNF.codChart.restr_source' W hW_open] at hyRestr
    let yS : S := ⟨y, hyS⟩
    have hyDom : yS ∈ hNF.domChart.source := by
      simpa [hW_eq] using hyRestr.2
    exact ⟨yS, hyDom, rfl⟩

/-- Helper for Theorem 5.8: every point of the restricted ambient image coming from `S` satisfies
the zero-tail slice equations forced by the immersion normal form. -/
private theorem restricted_local_normal_form_image_subset_zero_slice
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (x : S) (hk : k ≤ n)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : S → M) x (LocalNormalFormAPI.rank_normal_form k n k))
    {W : Set M} (hW_open : IsOpen W)
    (hW_sub : W ⊆ hNF.codChart.source)
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
      (hW_open := hW_open) (hW_sub := hW_sub) (hW_eq := hW_eq)]
    exact hy
  rcases hyImage with ⟨yS, hyS, rfl⟩
  refine ⟨?_, ?_⟩
  · -- The restricted chart value automatically lands in its own target.
    exact (hNF.codChart.restr W).map_source hy.2
  · -- On the source patch, the local normal form identifies the coordinate image with the
    -- zero-tail Euclidean slice.
    intro i
    have hyTarget : hNF.domChart yS ∈ hNF.domChart.target :=
      hNF.domChart.map_source hyS
    have hyLeftInv : hNF.domChart.symm (hNF.domChart yS) = yS := by
      exact hNF.domChart.left_inv hyS
    have hcoord :
        (hNF.codChart.restr W) yS.1 =
          LocalNormalFormAPI.rank_normal_form k n k (hNF.domChart yS) := by
      simpa [hyLeftInv, Function.comp] using hNF.eqOn hyTarget
    simpa [hcoord, rank_normal_form_self_eq_euclidean_slice_inclusion_zero hk] using
      (euclidean_slice_inclusion_tail hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ))
        (hNF.domChart yS) i)

/-- Helper for Theorem 5.8: a point already lying in the zero-tail Euclidean slice is recovered by
the rank normal form after projecting to the first `k` coordinates. -/
private theorem zero_slice_point_eq_rank_normal_form_projection
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hk : k ≤ n)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ Set.euclideanSlice U k hk (fun _ : Fin (n - k) ↦ (0 : ℝ))) :
    LocalNormalFormAPI.rank_normal_form k n k (euclidean_slice_projection hk z) = z := by
  -- Normalize the rank normal form to the zero-tail inclusion, then use the slice equations to
  -- identify the point with the reinsertion of its projected free coordinates.
  rw [rank_normal_form_self_eq_euclidean_slice_inclusion_zero hk]
  exact euclidean_slice_inclusion_projection hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) hz

/-- Helper for Theorem 5.8: on the zero-tail slice inside an ambient Euclidean ball, projecting to
the first `k` coordinates stays inside the corresponding `k`-dimensional ball. -/
private theorem zero_tail_projection_mem_ball
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hk : k ≤ n) {ε : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hzBall : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
    (hz : z ∈ Set.euclideanSlice U k hk (fun _ : Fin (n - k) ↦ (0 : ℝ))) :
    euclidean_slice_projection hk z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε := by
  rw [Metric.mem_ball, dist_eq_norm] at hzBall ⊢
  have hnorm_sq :
      ‖euclidean_slice_projection hk z‖ ^ 2 = ‖z‖ ^ 2 := by
    have hslice :
        euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ))
            (euclidean_slice_projection hk z) = z :=
      euclidean_slice_inclusion_projection hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) hz
    let zProj := euclidean_slice_projection hk z
    let a : Fin n → ℝ := fun i ↦
      (euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) zProj).ofLp i ^ 2
    let f : Fin (k + (n - k)) → ℝ := fun i ↦ a ((finCongr (Nat.add_sub_of_le hk)) i)
    have hinclude_sq :
        ‖euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ))
            zProj‖ ^ 2 =
          ‖zProj‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      calc
        ∑ i : Fin n, a i
            = ∑ i : Fin (k + (n - k)), f i := by
              simpa [a, f] using
                (Equiv.sum_comp (finCongr (Nat.add_sub_of_le hk)) (g := a)).symm
        _ =
              (∑ i : Fin k,
                (euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) zProj).ofLp
                  (Fin.castLE hk i) ^ 2) +
                ∑ i : Fin (n - k),
                  (euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) zProj).ofLp
                    (euclidean_slice_tail_coordinate hk i) ^ 2 := by
              simpa [a, f, cast_first_coordinates, euclidean_slice_tail_coordinate] using
                (Fin.sum_univ_add (f := f))
        _ =
              (∑ i : Fin k, zProj.ofLp i ^ 2) +
                ∑ i : Fin (n - k), (0 : ℝ) ^ 2 := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro i hi
                simp [zProj, euclidean_slice_inclusion_first]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                simp [euclidean_slice_inclusion_tail]
        _ = ∑ i : Fin k, zProj.ofLp i ^ 2 := by simp
    calc
      ‖euclidean_slice_projection hk z‖ ^ 2 =
          ‖euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) zProj‖ ^ 2 := by
            simpa [zProj] using hinclude_sq.symm
      _ = ‖z‖ ^ 2 := by
            simp [zProj, hslice]
  have hnorm :
      ‖euclidean_slice_projection hk z‖ = ‖z‖ := by
    nlinarith [hnorm_sq, norm_nonneg (euclidean_slice_projection hk z), norm_nonneg z]
  simpa [hnorm] using hzBall

/-- Helper for Theorem 5.8: a Euclidean linear automorphism defines a smooth chart change in the
top regularity groupoid. -/
private theorem euclidean_linear_equiv_mem_contDiffGroupoid
    {m : ℕ}
    {L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)} :
    L.toHomeomorph.toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
  -- Linear equivalences on Euclidean space are smooth together with their inverses.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using L.contDiff.contDiffOn
  · simpa [modelWithCornersSelf_coe] using L.symm.contDiff.contDiffOn

/-- Helper for Theorem 5.8: an embedded submanifold point admits centered top-atlas charts in
which the subtype inclusion has Lee's literal zero-tail coordinate form. -/
private theorem embedded_submanifold_point_has_centered_zero_slice_charts
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S)
    (x : S) (hk : k ≤ n) :
    ∃ domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)),
      ∃ codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
        x ∈ domChart.source ∧
        domChart x = 0 ∧
        x.1 ∈ codChart.source ∧
        codChart x.1 = 0 ∧
        domChart ∈ IsManifold.maximalAtlas (𝓡 k) (⊤ : WithTop ℕ∞) S ∧
        codChart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧
        domChart.source ⊆ Subtype.val ⁻¹' codChart.source ∧
        Set.EqOn (((codChart.extend (𝓡 n)) ∘ Subtype.val ∘
            (domChart.extend (𝓡 k)).symm))
          (fun z ↦ euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z)
          domChart.target := by
  let hImm :
      Manifold.IsImmersion (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
    by simpa using hEmb.isSmoothEmbedding_subtype_val.isImmersion
  let hComp := hImm.complement
  let hImmTop :
      Manifold.IsImmersionOfComplement hComp (𝓡 k) (𝓡 n)
        (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
    hImm.isImmersionOfComplement_complement
  let hAt := hImmTop x
  haveI : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin k) × hComp) :=
    FiniteDimensional.of_injective hAt.equiv.toLinearMap hAt.equiv.injective
  haveI : FiniteDimensional ℝ hComp :=
    FiniteDimensional.of_injective
      (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) hComp)
      LinearMap.inr_injective
  have hfin_prod :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hComp) = n := by
    calc
      Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hComp)
          = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
            exact hAt.equiv.toLinearEquiv.finrank_eq
      _ = n := by
            simpa using finrank_euclideanSpace_fin (α := ℝ) (ι := Fin n)
  have hfin_comp :
      Module.finrank ℝ hComp = n - k := by
    have hsum : k + Module.finrank ℝ hComp = n := by
      calc
        k + Module.finrank ℝ hComp =
            Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × hComp) := by
              simpa using
                (Module.finrank_prod ℝ (EuclideanSpace ℝ (Fin k)) hComp).symm
        _ = n := hfin_prod
    have hsum' : k + Module.finrank ℝ hComp = k + (n - k) := by
      simpa [Nat.add_sub_of_le hk] using hsum
    exact Nat.add_left_cancel hsum'
  have hfin_comp_eq :
      Module.finrank ℝ hComp =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - k))) := by
    calc
      Module.finrank ℝ hComp = n - k := hfin_comp
      _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - k))) := by
            simpa using finrank_euclideanSpace_fin (α := ℝ) (ι := Fin (n - k))
  let compEquiv : hComp ≃L[ℝ] EuclideanSpace ℝ (Fin (n - k)) :=
    ContinuousLinearEquiv.ofFinrankEq hfin_comp_eq
  let rawDomChart := hAt.domChart
  let rawCodChart := hAt.codChart
  let domChart :=
    rawDomChart.centerAt ⟨x, hAt.mem_domChart_source⟩
  let centeredCodChart :=
    rawCodChart.centerAt ⟨x.1, hAt.mem_codChart_source⟩
  let straightening :
      EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    hAt.equiv.symm.trans
      (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin k))).prodCongr compEquiv).trans
        (euclidean_slice_product_equiv hk))
  let codChart :=
    centeredCodChart.trans straightening.toHomeomorph.toOpenPartialHomeomorph
  have hx_dom : x ∈ domChart.source := by
    -- Centering preserves the chart source and keeps the basepoint inside it.
    simpa [domChart, OpenPartialHomeomorph.centerAt_source] using hAt.mem_domChart_source
  have hdom_zero : domChart x = 0 := by
    -- Centering the source chart subtracts the basepoint coordinates.
    simp [domChart, centerAt_apply_eq_sub_basepoint]
  have hx_cod : x.1 ∈ codChart.source := by
    -- The codomain chart is centered first and then postcomposed by a global linear automorphism.
    simpa [codChart, centeredCodChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.centerAt_source] using hAt.mem_codChart_source
  have hcod_zero : codChart x.1 = 0 := by
    -- The centered ambient chart already vanishes at `x`; linear postcomposition fixes `0`.
    simp [codChart, centeredCodChart, centerAt_apply_eq_sub_basepoint]
  have hdom_max :
      domChart ∈ IsManifold.maximalAtlas (𝓡 k) (⊤ : WithTop ℕ∞) S := by
    -- Centering a source chart in the maximal atlas preserves maximal-atlas membership.
    exact centerAt_mem_maximalAtlas rawDomChart hAt.domChart_mem_maximalAtlas
      ⟨x, hAt.mem_domChart_source⟩
  have hcentered_cod_max :
      centeredCodChart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    -- The same centering argument applies to the ambient chart.
    exact centerAt_mem_maximalAtlas rawCodChart hAt.codChart_mem_maximalAtlas
      ⟨x.1, hAt.mem_codChart_source⟩
  have hcod_max :
      codChart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    -- The final codomain straightening is a smooth Euclidean chart change.
    exact trans_mem_maximalAtlas_of_mem_groupoid hcentered_cod_max
      (euclidean_linear_equiv_mem_contDiffGroupoid (L := straightening))
  have hsource_sub :
      domChart.source ⊆ Subtype.val ⁻¹' codChart.source := by
    intro y hy
    -- Undo the centering normalization and reuse the source-to-codomain inclusion from `hAt`.
    have hy_raw : y ∈ rawDomChart.source := by
      simpa [domChart, rawDomChart, OpenPartialHomeomorph.centerAt_source] using hy
    have hy_cod_raw : y.1 ∈ rawCodChart.source := hAt.source_subset_preimage_source hy_raw
    simpa [codChart, centeredCodChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.centerAt_source] using hy_cod_raw
  have hcoord :
      Set.EqOn (((codChart.extend (𝓡 n)) ∘ Subtype.val ∘
          (domChart.extend (𝓡 k)).symm))
        (fun z ↦ euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z)
        domChart.target := by
    intro z hz
    have hz_raw :
        z + rawDomChart x ∈ rawDomChart.target := by
      -- Undo the source centering to return to the original immersion chart target.
      simpa [domChart, rawDomChart] using
        centerAt_add_base_mem_target rawDomChart ⟨x, hAt.mem_domChart_source⟩ hz
    have hz_raw_ext :
        z + rawDomChart x ∈ (rawDomChart.extend (𝓡 k)).target := by
      -- The extended chart has the same target as the original chart in the self-model case.
      simpa [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hz_raw
    have hdom_symm :
        ((domChart.symm z : S)) = rawDomChart.symm (z + rawDomChart x) := by
      -- The centered inverse is the old inverse evaluated after adding back the basepoint.
      simpa [domChart, rawDomChart] using
        centerAt_symm_apply_eq_symm_add rawDomChart ⟨x, hAt.mem_domChart_source⟩ hz
    have hraw :
        rawCodChart (((domChart.symm z).1)) =
          hAt.equiv (z + rawDomChart x, (0 : hComp)) := by
      -- Rewrite the new source chart back to the original immersion witness and apply its
      -- written-in-charts formula.
      calc
        rawCodChart (((domChart.symm z).1)) =
            rawCodChart ((rawDomChart.symm (z + rawDomChart x)).1) := by
              rw [hdom_symm]
        _ = hAt.equiv (z + rawDomChart x, (0 : hComp)) := by
              simpa [Function.comp, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm] using hAt.writtenInCharts hz_raw_ext
    have hx_raw_target : rawDomChart x ∈ rawDomChart.target :=
      rawDomChart.map_source hAt.mem_domChart_source
    have hx_raw_target_ext :
        rawDomChart x ∈ (rawDomChart.extend (𝓡 k)).target := by
      -- The same target normalization is needed at the basepoint itself.
      simpa [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hx_raw_target
    have hbase :
        rawCodChart x.1 = hAt.equiv (rawDomChart x, (0 : hComp)) := by
      -- Evaluate the original immersion normal form at the basepoint itself.
      calc
        rawCodChart x.1 =
            rawCodChart ((rawDomChart.symm (rawDomChart x)).1) := by
              rw [rawDomChart.left_inv hAt.mem_domChart_source]
        _ = hAt.equiv (rawDomChart x, (0 : hComp)) := by
              simpa [Function.comp, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm] using hAt.writtenInCharts hx_raw_target_ext
    have hcentered :
        centeredCodChart (((domChart.symm z).1)) = hAt.equiv (z, (0 : hComp)) := by
      -- Centering both charts removes the basepoint offset and leaves only the linear inclusion.
      calc
        centeredCodChart (((domChart.symm z).1)) =
            rawCodChart (((domChart.symm z).1)) - rawCodChart x.1 := by
              simp [centeredCodChart, rawCodChart, centerAt_apply_eq_sub_basepoint]
        _ = hAt.equiv (z + rawDomChart x, (0 : hComp)) -
              hAt.equiv (rawDomChart x, (0 : hComp)) := by
              rw [hraw, hbase]
        _ = hAt.equiv ((z + rawDomChart x, (0 : hComp)) - (rawDomChart x, (0 : hComp))) := by
              rw [hAt.equiv.map_sub]
        _ = hAt.equiv (z, (0 : hComp)) := by
              simp
    -- Collapse the `extend` transports, then apply the codomain straightening automorphism.
    calc
      ((codChart.extend (𝓡 n)) ∘ Subtype.val ∘ (domChart.extend (𝓡 k)).symm) z =
          codChart (((domChart.symm z).1)) := by
            simp [codChart, domChart, Function.comp, OpenPartialHomeomorph.extend_coe,
              OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
              modelWithCornersSelf_coe_symm]
      _ = straightening (hAt.equiv (z, (0 : hComp))) := by
            simp [codChart, centeredCodChart, Function.comp, hcentered]
      _ = euclidean_slice_product_equiv hk (z, (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
            simp [straightening]
      _ = euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
            exact euclidean_slice_product_equiv_apply_zero hk z
  exact ⟨domChart, codChart, hx_dom, hdom_zero, hx_cod, hcod_zero,
    hdom_max, hcod_max, hsource_sub, hcoord⟩

/-- Helper for Theorem 5.8: the centered top-atlas charts used in the forward implication contain
a common Euclidean ball about the origin. -/
private theorem centered_zero_slice_common_ball_radius
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (x : S)
    {domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k))}
    {codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hx_dom : x ∈ domChart.source) (hdom_zero : domChart x = 0)
    (hx_cod : x.1 ∈ codChart.source) (hcod_zero : codChart x.1 = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε ⊆ domChart.target ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target := by
  have hdom_zero_mem : (0 : EuclideanSpace ℝ (Fin k)) ∈ domChart.target := by
    -- The centered source chart sends `x` to the origin.
    simpa [hdom_zero] using domChart.map_source hx_dom
  have hcod_zero_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ codChart.target := by
    -- The centered codomain chart sends `x` to the origin as well.
    simpa [hcod_zero] using codChart.map_source hx_cod
  obtain ⟨εdom, hεdom_pos, hεdom_sub⟩ :=
    Metric.mem_nhds_iff.mp (domChart.open_target.mem_nhds hdom_zero_mem)
  obtain ⟨εcod, hεcod_pos, hεcod_sub⟩ :=
    Metric.mem_nhds_iff.mp (codChart.open_target.mem_nhds hcod_zero_mem)
  refine ⟨min εdom εcod, lt_min hεdom_pos hεcod_pos, ?_, ?_⟩
  · -- The smaller common ball stays inside the source-chart target.
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans hεdom_sub
  · -- The same common radius works for the codomain chart.
    exact (Metric.ball_subset_ball (min_le_right _ _)).trans hεcod_sub

/-- Helper for Theorem 5.8: the source coordinate ball cut out by a centered chart is Lee's
`U₀` patch on the subtype. -/
private def centered_zero_slice_source_ball
    {S : Set M}
    (domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)))
    (ε : ℝ) : Set S :=
  domChart.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε

/-- Helper for Theorem 5.8: the target coordinate ball cut out by a centered chart is Lee's
`V₀` patch on the ambient manifold. -/
private def centered_zero_slice_target_ball
    (codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (ε : ℝ) : Set M :=
  codChart.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε

/-- Helper for Theorem 5.8: after intersecting the ambient patch `W₀` with the common target ball,
Lee's restricted ambient chart is the chart `e₁` used in the final slice argument. -/
private def centered_zero_slice_restricted_chart
    (codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (ε : ℝ) (W0 : Set M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  codChart.restr (W0 ∩ centered_zero_slice_target_ball codChart ε)

/-- Helper for Theorem 5.8: Lee's `V₀` patch is open for the centered ambient chart used in the
forward implication. -/
private theorem centered_zero_slice_target_ball_open
    (codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ}
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target) :
    IsOpen (centered_zero_slice_target_ball codChart ε) := by
  -- The inverse codomain chart is open on the chosen target ball.
  simpa [centered_zero_slice_target_ball, inter_eq_right.2 hεcod_ball] using
    codChart.symm.isOpen_image_source_inter
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε))

/-- Helper for Theorem 5.8: the restricted chart `e₁` has the expected source, namely the old
source intersected with the shrunken ambient patch `W₀ ∩ V₀`. -/
private theorem centered_zero_slice_restricted_chart_source
    (codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} {W0 : Set M} (hW0_open : IsOpen W0)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target) :
    (centered_zero_slice_restricted_chart codChart ε W0).source =
      codChart.source ∩ (W0 ∩ centered_zero_slice_target_ball codChart ε) := by
  have hV0_open : IsOpen (centered_zero_slice_target_ball codChart ε) :=
    centered_zero_slice_target_ball_open codChart hεcod_ball
  -- Unfolding the restriction once records the shrunken source formula needed later.
  simpa [centered_zero_slice_restricted_chart] using
    codChart.restr_source' (W0 ∩ centered_zero_slice_target_ball codChart ε)
      (hW0_open.inter hV0_open)

/-- Helper for Theorem 5.8: the restricted chart `e₁` has the expected target, namely the old
target together with the ambient source condition for `W₀ ∩ V₀`. -/
private theorem centered_zero_slice_restricted_chart_target
    (codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} {W0 : Set M} (hW0_open : IsOpen W0)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target) :
    (centered_zero_slice_restricted_chart codChart ε W0).target =
      codChart.target ∩
        codChart.symm ⁻¹' (W0 ∩ centered_zero_slice_target_ball codChart ε) := by
  have hV0_open : IsOpen (centered_zero_slice_target_ball codChart ε) :=
    centered_zero_slice_target_ball_open codChart hεcod_ball
  have hPatchOpen : IsOpen (W0 ∩ centered_zero_slice_target_ball codChart ε) :=
    hW0_open.inter hV0_open
  -- The restricted target is definitionally the old target plus the preimage of the restricted
  -- source set.
  simp [centered_zero_slice_restricted_chart, PartialEquiv.restr_target, hPatchOpen.interior_eq]

/-- Helper for Theorem 5.8: Lee's `U₀` patch is open in the subtype chart. -/
private theorem centered_zero_slice_source_ball_open
    {S : Set M}
    (domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)))
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε ⊆ domChart.target) :
    IsOpen (centered_zero_slice_source_ball domChart ε) := by
  -- The inverse chart is an open map on its source, and the chosen ball sits entirely inside it.
  simpa [centered_zero_slice_source_ball, inter_eq_right.2 hεdom_ball] using
    domChart.symm.isOpen_image_source_inter
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε))

/-- Helper for Theorem 5.8: after shrinking both centered charts to a common coordinate ball and
then intersecting with the ambient open set cutting out the subtype patch, the restricted codomain
chart has zero-tail image exactly equal to the Euclidean slice promised by Lee's argument. -/
private theorem centered_zero_slice_restricted_image_eq_zero_slice
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hk : k ≤ n)
    {domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k))}
    {codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hsource_sub : domChart.source ⊆ Subtype.val ⁻¹' codChart.source)
    (hcoord_eq :
      Set.EqOn (((codChart.extend (𝓡 n)) ∘ Subtype.val ∘
          (domChart.extend (𝓡 k)).symm))
        (fun z ↦ euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z)
        domChart.target)
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε ⊆ domChart.target)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target)
    {W0 : Set M} (hW0_open : IsOpen W0)
    (hW0_eq : centered_zero_slice_source_ball domChart ε = {y : S | y.1 ∈ W0}) :
    (centered_zero_slice_restricted_chart codChart ε W0) '' (S ∩
        (centered_zero_slice_restricted_chart codChart ε W0).source) =
      Set.euclideanSlice
        (centered_zero_slice_restricted_chart codChart ε W0).target
        k hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) := by
  let U0 : Set S := centered_zero_slice_source_ball domChart ε
  let V0 : Set M := centered_zero_slice_target_ball codChart ε
  let e1 := centered_zero_slice_restricted_chart codChart ε W0
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyS, hyRestr⟩
    have hyRestr_e1 : y ∈ e1.source := hyRestr
    rw [centered_zero_slice_restricted_chart_source codChart
      (ε := ε) (W0 := W0) hW0_open hεcod_ball] at hyRestr
    let yS : S := ⟨y, hyS⟩
    have hyU0 : yS ∈ U0 := by
      -- Points of `S` lying in the ambient patch `W0` are exactly the source-ball patch `U0`.
      simpa [U0, hW0_eq, yS] using hyRestr.2.1
    rcases hyU0 with ⟨u, huBall, huSymm⟩
    have huTarget : u ∈ domChart.target := hεdom_ball huBall
    have hyDom : yS ∈ domChart.source := by
      -- The inverse chart point of a target coordinate lies back in the source.
      simpa [yS, huSymm] using domChart.symm.map_source huTarget
    have hyCodSource : y ∈ codChart.source := hsource_sub hyDom
    have hcoord : codChart y = euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) u := by
      -- Collapse the `extend` transports and read off the zero-tail coordinate formula.
      simpa [Function.comp, yS, huSymm, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm] using hcoord_eq huTarget
    refine ⟨e1.map_source hyRestr_e1, ?_⟩
    -- The explicit zero-tail formula forces all tail coordinates to vanish.
    simpa [e1, centered_zero_slice_restricted_chart, hcoord] using
      (euclidean_slice_inclusion_tail hk
        (fun _ : Fin (n - k) ↦ (0 : ℝ)) u)
  · intro hz
    let y0 := codChart.symm z
    have hzRestrTarget : z ∈ e1.target := hz.1
    have hzTargetData :
        z ∈ codChart.target ∩ codChart.symm ⁻¹' (W0 ∩ V0) := by
      -- Rewrite the restricted target to the original target intersected with the restricted
      -- source condition.
      simpa [e1, V0] using
        (show z ∈
          codChart.target ∩
            codChart.symm ⁻¹' (W0 ∩ centered_zero_slice_target_ball codChart ε) from by
              rw [← centered_zero_slice_restricted_chart_target codChart
                (ε := ε) (W0 := W0) hW0_open hεcod_ball]
              exact hzRestrTarget)
    have hzCodTarget : z ∈ codChart.target := hzTargetData.1
    have hy0V1 : y0 ∈ W0 ∩ V0 := hzTargetData.2
    have hzBall : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
      -- Because `y0` lies in the shrunken source patch `V0`, the point `z` is one of the chosen
      -- codomain-ball coordinates.
      rcases hy0V1.2 with ⟨w, hwBall, hwSymm⟩
      have hwTarget : w ∈ codChart.target := hεcod_ball hwBall
      have hzw : z = w := by
        calc
          z = codChart y0 := by
                simpa [y0] using (codChart.right_inv hzCodTarget).symm
          _ = codChart (codChart.symm w) := by
                simpa [y0] using congrArg codChart hwSymm.symm
          _ = w := codChart.right_inv hwTarget
      simpa [hzw] using hwBall
    have huBall :
        euclidean_slice_projection hk z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε :=
      zero_tail_projection_mem_ball hk hzBall hz
    let yS : S := domChart.symm (euclidean_slice_projection hk z)
    have hyTarget : euclidean_slice_projection hk z ∈ domChart.target := hεdom_ball huBall
    have hyDom : yS ∈ domChart.source := by
      -- The projected point lies in the source chart target, so its inverse lies in the source.
      exact domChart.symm.map_source hyTarget
    have hyCodSource : yS.1 ∈ codChart.source := hsource_sub hyDom
    have hyW0 : yS.1 ∈ W0 := by
      have hyU0 : yS ∈ U0 := by
        refine ⟨euclidean_slice_projection hk z, huBall, rfl⟩
      -- The ambient open patch `W0` was chosen to cut out exactly the source ball `U0`.
      simpa [U0, hW0_eq, yS] using hyU0
    have hyCoord : codChart yS.1 = z := by
      -- Project the zero-tail point and reinsert it using the explicit slice formula.
      calc
        codChart yS.1 =
            euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ))
              (euclidean_slice_projection hk z) := by
              simpa [Function.comp, yS, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
                modelWithCornersSelf_coe_symm] using hcoord_eq hyTarget
        _ = z := euclidean_slice_inclusion_projection hk
              (fun _ : Fin (n - k) ↦ (0 : ℝ)) hz
    have hyV0 : yS.1 ∈ V0 := by
      -- The reconstructed subtype point has ambient coordinates `z`, which already lie in the
      -- codomain ball, so it belongs to the shrunken ambient source patch `V0`.
      refine ⟨z, hzBall, ?_⟩
      simpa [V0, hyCoord] using codChart.left_inv hyCodSource
    have hyRestr : yS.1 ∈ e1.source := by
      -- Membership in the restricted source is exactly membership in the original source together
      -- with membership in `W0 ∩ V0`.
      rw [centered_zero_slice_restricted_chart_source codChart
        (ε := ε) (W0 := W0) hW0_open hεcod_ball]
      exact ⟨hyCodSource, ⟨hyW0, hyV0⟩⟩
    refine ⟨yS.1, ⟨yS.2, hyRestr⟩, ?_⟩
    -- The witness `yS` maps to `z` under the restricted codomain chart.
    simpa using hyCoord

/-- Helper for Theorem 5.8: the restricted centered ambient chart is the smooth slice chart
promised by Lee's forward implication. -/
private theorem centered_zero_slice_restricted_chart_isSliceChart
    {S : Set M} [TopologicalManifold k S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hk : k ≤ n)
    {domChart : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k))}
    {codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hcod_max : codChart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M)
    (hsource_sub : domChart.source ⊆ Subtype.val ⁻¹' codChart.source)
    (hcoord_eq :
      Set.EqOn (((codChart.extend (𝓡 n)) ∘ Subtype.val ∘
          (domChart.extend (𝓡 k)).symm))
        (fun z ↦ euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z)
        domChart.target)
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε ⊆ domChart.target)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ codChart.target)
    {W0 : Set M} (hW0_open : IsOpen W0)
    (hW0_eq : centered_zero_slice_source_ball domChart ε = {y : S | y.1 ∈ W0}) :
    (centered_zero_slice_restricted_chart codChart ε W0).IsSliceChart S k := by
  have hV0_open : IsOpen (centered_zero_slice_target_ball codChart ε) :=
    centered_zero_slice_target_ball_open codChart hεcod_ball
  have hPatchOpen : IsOpen (W0 ∩ centered_zero_slice_target_ball codChart ε) :=
    hW0_open.inter hV0_open
  -- Route correction: the ambient chart is already top-regular, so restriction stays in the same
  -- top maximal atlas with no `∞ → ⊤` upgrade step.
  refine ⟨?_, ?_⟩
  · change codChart.restr (W0 ∩ centered_zero_slice_target_ball codChart ε) ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M
    exact restr_mem_maximalAtlas
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) hcod_max hPatchOpen
  · refine ⟨hk, fun _ : Fin (n - k) ↦ (0 : ℝ), ?_⟩
    -- Unfold the chart-slice definition and use the explicit zero-tail image computation.
    simpa [Set.IsSliceInChart] using
      centered_zero_slice_restricted_image_eq_zero_slice
        (hk := hk) (hsource_sub := hsource_sub) (hcoord_eq := hcoord_eq)
        (hεdom_ball := hεdom_ball) (hεcod_ball := hεcod_ball)
        (W0 := W0) hW0_open hW0_eq

/-- Theorem 5.8: a subset of a smooth `n`-manifold satisfies the local `k`-slice condition exactly
when the subtype `S` admits a topological `k`-manifold structure and a smooth boundaryless
`k`-manifold structure for which its inclusion into `M` is an embedded submanifold. -/
-- Proof sketch: for an embedded submanifold, use the top-order immersion witness of the subtype
-- inclusion, center the source and ambient charts, straighten the ambient Euclidean coordinates to
-- Lee's zero-tail slice model, and then run the common-radius restriction argument. Conversely,
-- the imported helper module already builds the subtype atlas by projecting slice coordinates and
-- proves the centered zero-tail immersion form.
theorem local_slice_criterion_for_embedded_submanifold
    (S : Set M) :
    Set.SatisfiesLocalSliceCondition n S k ↔
      ∃ tm : TopologicalManifold k S,
        let _ : TopologicalManifold k S := tm
        ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S,
          let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
          IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S := by
  constructor
  · intro hS
    -- The slice-induced atlas and the centered zero-tail immersion formula already produce the
    -- smooth embedded-submanifold structure on `S`.
    exact local_slice_condition_has_embedded_submanifold_structure (S := S) hS
  · intro hEmb
    classical
    by_cases hEmpty : S = ∅
    · subst hEmpty
      -- The empty subset satisfies the local slice condition by the dedicated vacuous instance.
      infer_instance
    · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      have hk : k ≤ n := by
        -- The immersed source dimension cannot exceed the ambient one.
        rcases hEmb with ⟨tm, hRest⟩
        let _ : TopologicalManifold k S := tm
        rcases hRest with ⟨hs, hEmbStruct⟩
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
        exact embedded_submanifold_dimension_le
          (S := S) hS_nonempty hEmbStruct
      refine ⟨?_⟩
      intro x hx
      let xS : S := ⟨x, hx⟩
      rcases hEmb with ⟨tm, hRest⟩
      let _ : TopologicalManifold k S := tm
      rcases hRest with ⟨hs, hEmbStruct⟩
      let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
      rcases embedded_submanifold_point_has_centered_zero_slice_charts
          (hEmb := hEmbStruct) (x := xS) hk with
        ⟨domChart, codChart, hxDom, hdom_zero, hxCod, hcod_zero,
          hdom_max, hcod_max, hsource_sub, hcoord_eq⟩
      obtain ⟨ε, hε_pos, hεdom_ball, hεcod_ball⟩ :=
        centered_zero_slice_common_ball_radius (x := xS)
          hxDom hdom_zero hxCod hcod_zero
      let U0 : Set S := centered_zero_slice_source_ball domChart ε
      have hU0_open : IsOpen U0 := by
        -- Lee's `U0` is the source coordinate ball inside the subtype chart domain.
        simpa [U0] using centered_zero_slice_source_ball_open domChart hεdom_ball
      rcases subtype_open_eq_preimage_ambient_open
          (hU := hU0_open) with ⟨W0, hW0_open, hW0_eq⟩
      let e1 := centered_zero_slice_restricted_chart codChart ε W0
      have hxU0 : xS ∈ U0 := by
        -- The centered source chart sends `xS` to `0`, so `xS` lies in the source coordinate ball.
        refine ⟨0, ?_, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm] using hε_pos
        · simpa [U0, centered_zero_slice_source_ball, hdom_zero] using domChart.left_inv hxDom
      have hxW0 : x ∈ W0 := by
        -- The ambient open set `W0` cuts out exactly `U0` on the subtype.
        simpa [hW0_eq] using hxU0
      have hxV0 : x ∈ centered_zero_slice_target_ball codChart ε := by
        -- The centered codomain chart sends `x` to `0`, so `x` lies in the ambient coordinate ball.
        refine ⟨0, ?_, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm] using hε_pos
        · simpa [centered_zero_slice_target_ball, hcod_zero] using codChart.left_inv hxCod
      have hxe1_source : x ∈ e1.source := by
        -- The witness chart `e1` is defined exactly on the ambient source intersected with
        -- the shrunken patch `W0 ∩ V0`.
        rw [centered_zero_slice_restricted_chart_source codChart
          (ε := ε) (W0 := W0) hW0_open hεcod_ball]
        exact ⟨hxCod, ⟨hxW0, hxV0⟩⟩
      -- Execute Lee's source route literally: form `U0`, extract `W0`, then restrict the ambient
      -- chart to `e1 = codChart|_(W0 ∩ V0)`.
      refine ⟨e1, hxe1_source, ?_⟩
      · exact centered_zero_slice_restricted_chart_isSliceChart
          (hk := hk) hcod_max hsource_sub hcoord_eq
          (hεdom_ball := hεdom_ball) (hεcod_ball := hεcod_ball)
          (hW0_open := hW0_open)
          (hW0_eq := by simpa [U0] using hW0_eq)

end
