import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Theorem_2_29
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_7
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold

-- Semantic search note: the expected proof route uses the closed-set smooth zero-set owner from
-- Chapter 2 together with the graph / proper-embedding APIs from Chapter 5, but the source-facing
-- public statement here keeps the textbook hypersurface conclusion as the main entry.

section

universe uN

variable {n : ℕ}

/-- The horizontal hyperplane `ℝ^n × {0}` inside `ℝ^n × ℝ`. -/
def horizontalHyperplane (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | p.2 = 0}

/-- Helper for Problem 6-14: pulling a closed subset of `ℝ^n × ℝ` back along the horizontal
inclusion `x ↦ (x, 0)` preserves closedness. -/
lemma horizontalBaseClosed
    {A : Set (EuclideanSpace ℝ (Fin n) × ℝ)} (hA_closed : IsClosed A) :
    IsClosed ((fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : ℝ))) ⁻¹' A) := by
  -- The horizontal inclusion is continuous, so closedness pulls back along it.
  simpa using hA_closed.preimage (continuous_id.prodMk continuous_const)

/-- Helper for Problem 6-14: transport the source charted-space structure across a homeomorphism
onto the range of a smooth embedding into `ℝ^n × ℝ`. -/
noncomputable abbrev transportedGraphRangeChartedSpace
    {N : Type uN} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    {F : N → EuclideanSpace ℝ (Fin n) × ℝ} (e : N ≃ₜ Set.range F) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) := by
  let _ : ChartedSpace N (Set.range F) :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Use the explicit singleton-chart route so the transported charts remain visible to Lean.
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) N (Set.range F)

/-- Helper for Problem 6-14: the transported graph range is again a smooth `n`-manifold at the
outer regularity `⊤`. -/
lemma transportedGraphRangeIsManifoldTop
    {N : Type uN} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N]
    {F : N → EuclideanSpace ℝ (Fin n) × ℝ} (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) :=
      transportedGraphRangeChartedSpace e
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F) := by
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) :=
    transportedGraphRangeChartedSpace e
  have hGroupoid :
      HasGroupoid (Set.range F) (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the already-known compatibility on the source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines a smooth manifold structure on the range.
  exact IsManifold.mk' (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F)

/-- Helper for Problem 6-14: the range of a top-regularity smooth embedding into `ℝ^n × ℝ`
inherits a transported smooth `n`-manifold structure for which the subtype inclusion is a
top-regularity smooth embedding. -/
theorem smoothEmbeddingRangeHasTopManifoldStructure
    {N : Type uN} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N]
    {F : N → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : Manifold.IsSmoothEmbedding (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ))
      (⊤ : WithTop ℕ∞) F) :
    ∃ instCharted : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F),
      ∃ instManifold : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) := instCharted
        let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
        Manifold.IsSmoothEmbedding (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ))
          (⊤ : WithTop ℕ∞)
          (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin n) × ℝ) := by
  let e : N ≃ₜ Set.range F := hF.isEmbedding.toHomeomorph
  let instCharted : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) :=
    transportedGraphRangeChartedSpace e
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) := instCharted
  have instManifold : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F) :=
    transportedGraphRangeIsManifoldTop e
  let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.range F) := instManifold
  have hSubtypeImmersion :
      Manifold.IsImmersion (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        (⊤ : WithTop ℕ∞) (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin n) × ℝ) := by
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
      hx.equiv (eS.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [eS, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
    · have hxe : F (e.symm x) = (x : EuclideanSpace ℝ (Fin n) × ℝ) := by
        exact congrArg Subtype.val (e.apply_symm_apply x)
      simpa [hxe] using hx.mem_codChart_source
    · intro d hd
      rcases hd with ⟨f, hf, c', hc', rfl⟩
      have hfEq : f = eS := by
        simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
          ext z
          simp [eS]) f hf
      subst f
      have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
        simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
      constructor
      · have hleft :
            ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').1
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hleft
      · have hright :
            ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').2
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hright
    · exact hx.codChart_mem_maximalAtlas
    · intro z hz
      have hz' : e.symm z ∈ hx.domChart.source := by
        simpa [eS, OpenPartialHomeomorph.trans_source] using hz
      have hze : F (e.symm z) = (z : EuclideanSpace ℝ (Fin n) × ℝ) := by
        exact congrArg Subtype.val (e.apply_symm_apply z)
      simpa [hze] using hx.source_subset_preimage_source hz'
    · intro u hu
      have hu' : u ∈ (hx.domChart.extend (𝓡 n)).target := by
        simpa [eS, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.extend_coe] using hx.writtenInCharts hu'
  -- The range still carries the subspace topology, so immersion plus the subtype embedding gives
  -- the desired smooth embedding of the inclusion.
  have hSubtype :
      Manifold.IsSmoothEmbedding (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin n) × ℝ) :=
    ⟨hSubtypeImmersion, Topology.IsEmbedding.subtypeVal⟩
  exact ⟨instCharted, instManifold, hSubtype⟩

/-- Helper for Problem 6-14: the global graph of a smooth map `ℝ^n → ℝ` carries the induced
`𝓡 n`-manifold structure, and its subtype inclusion into `ℝ^n × ℝ` is a smooth embedding. -/
lemma smoothGraphEmbeddedStructure
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ) (⊤ : WithTop ℕ∞) f) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.univ.graphOn f),
      ∃ hs : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.univ.graphOn f),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.univ.graphOn f) := cs
        let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.univ.graphOn f) := hs
        Manifold.IsSmoothEmbedding
          (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ))
          (⊤ : WithTop ℕ∞)
          (Subtype.val : Set.univ.graphOn f → EuclideanSpace ℝ (Fin n) × ℝ) := by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⊤
  have hEmbedding :=
    graphMap_isSmoothEmbedding U f hf.contMDiffOn
  obtain ⟨cs, hsTop, hSubtype⟩ :=
    smoothEmbeddingRangeHasTopManifoldStructure hEmbedding
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n))
      (Set.range (TopologicalSpace.Opens.graphMap U f)) := cs
  let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞)
      (Set.range (TopologicalSpace.Opens.graphMap U f)) := hsTop
  have hGraphEq :
      Set.range (TopologicalSpace.Opens.graphMap U f) = Set.univ.graphOn f := by
    simpa [U] using TopologicalSpace.Opens.range_graphMap_eq_graphOn U f
  rw [← hGraphEq]
  exact ⟨cs, hsTop, hSubtype⟩

/-- Helper for Problem 6-14: the immersed-submanifold carried by a smooth graph inclusion has the
expected finite-dimensional model space. -/
instance instFiniteDimensionalSmoothGraphImmersedModelSpace
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.univ.graphOn f)]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.univ.graphOn f)]
    (hGraph :
      Manifold.IsSmoothEmbedding
        (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : Set.univ.graphOn f → EuclideanSpace ℝ (Fin n) × ℝ)) :
    FiniteDimensional ℝ hGraph.toImmersedSubmanifold.ModelSpace := by
  simpa [Manifold.IsSmoothEmbedding.toImmersedSubmanifold] using
    (inferInstance : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))

/-- Helper for Problem 6-14: the global graph of a smooth map `ℝ^n → ℝ` is a hypersurface. -/
lemma smoothGraphIsHypersurface
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.univ.graphOn f)]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (Set.univ.graphOn f)]
    (hGraph :
      Manifold.IsSmoothEmbedding
        (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        (⊤ : WithTop ℕ∞)
        (Subtype.val : Set.univ.graphOn f → EuclideanSpace ℝ (Fin n) × ℝ)) :
    hGraph.toImmersedSubmanifold.IsHypersurface := by
  -- Compute the codimension of the graph as `(n + 1) - n = 1`.
  rw [Manifold.ImmersedSubmanifold.IsHypersurface,
    Manifold.ImmersedSubmanifold.codimension]
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) -
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 1
  simp [Module.finrank_prod]

/-- Helper for Problem 6-14: once the graph zero set agrees with the horizontal pullback of `A`,
the horizontal hyperplane meets the graph exactly in `A`. -/
lemma horizontalHyperplane_inter_graph_eq
    {A : Set (EuclideanSpace ℝ (Fin n) × ℝ)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hA_subset : A ⊆ horizontalHyperplane n)
    (hzero :
      f ⁻¹' ({0} : Set ℝ) = (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : ℝ))) ⁻¹' A) :
    horizontalHyperplane n ∩ Set.univ.graphOn f = A := by
  -- Compare the two sets pointwise using the graph equation and the zero-set identity.
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    simp only [horizontalHyperplane, Set.mem_inter_iff, Set.mem_graphOn, Set.mem_univ,
      true_and, Set.mem_setOf_eq] at hp
    rcases hp with ⟨hy_zero, hgraph⟩
    have hx_zero : f x = 0 := by
      simpa [hy_zero] using hgraph
    have hx_mem_preimage : x ∈ (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : ℝ))) ⁻¹' A := by
      rw [← hzero]
      simp [hx_zero]
    have hxA : (x, (0 : ℝ)) ∈ A := by
      simpa using hx_mem_preimage
    simpa [hy_zero] using hxA
  · intro hpA
    have hy_zero : y = 0 := by
      simpa [horizontalHyperplane] using hA_subset hpA
    have hxA : (x, (0 : ℝ)) ∈ A := by
      simpa [hy_zero] using hpA
    have hx_mem_preimage : x ∈ (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : ℝ))) ⁻¹' A := by
      simpa using hxA
    have hx_zero : f x = 0 := by
      have hx_zero_mem : x ∈ f ⁻¹' ({0} : Set ℝ) := by
        rw [hzero]
        exact hx_mem_preimage
      simpa using hx_zero_mem
    simp [horizontalHyperplane, Set.mem_graphOn, hy_zero, hx_zero]

/-- Helper for Problem 6-14: the global graph parametrization `x ↦ (x, f x)` is a `C^∞` smooth
embedding of `ℝ^n` into `ℝ^n × ℝ`. -/
lemma globalGraphParametrization_isSmoothEmbedding
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f) :
    Manifold.IsSmoothEmbedding
      (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ))
      (∞ : ℕ∞ω)
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, f x)) := by
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × ℝ := fun x ↦ (x, f x)
  have hFcont :
      ContMDiff
        (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        ∞
        F := by
    -- The graph parametrization is smooth because both coordinate functions are smooth.
    simpa [F] using contMDiff_id.prodMk hf
  have hFimm :
      Manifold.IsImmersion
        (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        ∞
        F := by
    -- The first coordinate of the derivative is the identity, so the differential is injective.
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv (𝓡 n) ((𝓡 n).prod 𝓘(ℝ)) F x =
          (mfderiv (𝓡 n) (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) ↦ y) x).prod
            (mfderiv (𝓡 n) 𝓘(ℝ) f x) := by
      simpa [F] using
        (mfderiv_prodMk
          (I := 𝓡 n)
          (I' := 𝓡 n)
          (I'' := 𝓘(ℝ))
          (f := fun y : EuclideanSpace ℝ (Fin n) ↦ y)
          (g := f)
          (x := x)
          (contMDiff_id.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hf.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv (𝓡 n) ((𝓡 n).prod 𝓘(ℝ)) F x) v).1 =
          ((mfderiv (𝓡 n) ((𝓡 n).prod 𝓘(ℝ)) F x) w).1 := by
      exact congrArg Prod.fst hvw
    simpa [hDeriv, mfderiv_id] using hFirst
  have hFemb : Topology.IsEmbedding F := by
    -- The graph map is a topological embedding because projection to the first coordinate is
    -- a continuous inverse on the image.
    simpa [F] using isEmbedding_graph hf.continuous
  exact ⟨hFimm, hFemb⟩

/-- Problem 6-14. If `A` is a closed subset of `S = ℝ^n × {0} ⊆ ℝ^n × ℝ`, then there exists a
properly embedded hypersurface `S' ⊆ ℝ^n × ℝ` such that `S ∩ S' = A`. -/
theorem exists_properlyEmbedded_hypersurface_inter_eq_closed_subset_of_horizontalHyperplane
    {A : Set (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hA_closed : IsClosed A)
    (hA_subset : A ⊆ horizontalHyperplane n) :
    ∃ S' : Set (EuclideanSpace ℝ (Fin n) × ℝ),
      ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) S',
        ∃ hs : IsManifold (𝓡 n) ∞ S',
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S' := cs
          let _ : IsManifold (𝓡 n) ∞ S' := hs
          Manifold.IsSmoothEmbedding
            (𝓡 n)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
            (∞ : ℕ∞ω)
            ((↑) : S' → EuclideanSpace ℝ (Fin n) × ℝ) ∧
            S'.IsProperlyEmbedded ∧
            horizontalHyperplane n ∩ S' = A := by
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : ℝ))) ⁻¹' A
  -- Pull the closed subset of the horizontal hyperplane back to the base `ℝ^n`.
  have hK_closed : IsClosed K := by
    simpa [K] using horizontalBaseClosed (n := n) hA_closed
  -- Realize that closed base set as the zero set of a smooth function on `ℝ^n`.
  obtain ⟨f, _, hzero⟩ :=
    exists_nonneg_smooth_zero_set_eq_of_isClosed (I := 𝓡 n) (K := K) hK_closed
  let g : EuclideanSpace ℝ (Fin n) → ℝ := f
  have hg_smooth : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ g := by
    simpa [g] using (f.contMDiff : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f)
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × ℝ := fun x ↦ (x, g x)
  let S' : Set (EuclideanSpace ℝ (Fin n) × ℝ) := Set.range F
  have hF_embedding :
      Manifold.IsSmoothEmbedding
        (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ))
        (∞ : ℕ∞ω)
        F :=
    globalGraphParametrization_isSmoothEmbedding (n := n) hg_smooth
  -- Give the range of the graph parametrization its induced `C^∞` manifold structure.
  rcases smooth_embedding_range_has_induced_manifold_structure
      (I := ((𝓡 n).prod 𝓘(ℝ)))
      (J := 𝓡 n)
      (F := F)
      hF_embedding with ⟨cs, hcs⟩
  have hRangeStructure :
      ∃ hs : IsManifold (𝓡 n) ∞ S',
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S' := cs
        let _ : IsManifold (𝓡 n) ∞ S' := hs
        Manifold.IsSmoothEmbedding
          (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ))
          (∞ : ℕ∞ω)
          (Subtype.val : S' → EuclideanSpace ℝ (Fin n) × ℝ) ∧
          ∃ Φ : EuclideanSpace ℝ (Fin n) ≃ₘ⟮𝓡 n, 𝓡 n⟯ S',
            ∀ x, (Φ x : EuclideanSpace ℝ (Fin n) × ℝ) = F x := by
    -- Proposition 5.2 packages exactly the range manifold data needed for the graph image.
    simpa [S', IsInducedImageManifoldStructure] using hcs
  rcases hRangeStructure with ⟨hs, hGraphEmbeddingProd, -, _⟩
  have hGraphEmbedding :
      Manifold.IsSmoothEmbedding
        (𝓡 n)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
        (∞ : ℕ∞ω)
        (Subtype.val : S' → EuclideanSpace ℝ (Fin n) × ℝ) := by
    -- Normalize the ambient model from the product model spelling to the self-model spelling.
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hGraphEmbeddingProd
  have hRangeEq : S' = Set.univ.graphOn g := by
    -- The range of the parametrization is exactly the global graph.
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      simp [F, Set.mem_graphOn]
    · intro hp
      rcases Set.mem_graphOn.1 hp with ⟨_, hpgraph⟩
      refine ⟨p.1, ?_⟩
      ext <;> simp [F, hpgraph]
  have hProper : S'.IsProperlyEmbedded := by
    rw [hRangeEq]
    simpa using
      (smooth_map_graph_isProperlyEmbedded
        (E := EuclideanSpace ℝ (Fin n))
        (F := ℝ)
        (G := ℝ)
        (J := 𝓘(ℝ))
        (M := EuclideanSpace ℝ (Fin n))
        (N := ℝ)
        (f := g)
        hg_smooth)
  -- The horizontal slice of the graph is exactly the prescribed closed subset `A`.
  have hInter : horizontalHyperplane n ∩ S' = A := by
    rw [hRangeEq]
    simpa [K] using horizontalHyperplane_inter_graph_eq (n := n) hA_subset hzero
  refine ⟨S', cs, hs, ?_⟩
  -- Route correction: use the `C^∞` induced range structure from Proposition 5.2, then compare
  -- that range to the literal graph only for the final set-theoretic statements.
  refine ⟨?_, hProper, hInter⟩
  exact hGraphEmbedding

end
