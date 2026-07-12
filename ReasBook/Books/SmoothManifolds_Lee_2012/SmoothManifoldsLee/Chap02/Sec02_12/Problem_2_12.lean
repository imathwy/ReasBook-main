import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import SmoothManifolds_Lee_2012.Chap01.Sec01_02.Proposition_1_17
import SmoothManifolds_Lee_2012.Chap01.Sec01_07.Problem_1_9
import SmoothManifolds_Lee_2012.Chap02.Sec02_12.Problem_2_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ChartedSpace OpenPartialHomeomorph
open scoped LinearAlgebra.Projectivization Manifold ContDiff

universe u

variable {m : ℕ}
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

local notation "Icp" => 𝓘(ℝ, EuclideanSpace ℂ (Fin m))

/-- Helper for Problem 2-12: precomposing two charts by the same partial homeomorphism cancels in
their transition map as soon as the middle inverse/forward composition is the identity. -/
private lemma transported_transition_eq
    {X Y H : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace H]
    (eS : OpenPartialHomeomorph X Y)
    {e c : OpenPartialHomeomorph Y H}
    (hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl Y) :
    (eS.trans e).symm.trans (eS.trans c) = e.symm.trans c := by
  -- Reassociate until the middle factor `eS.symm.trans eS` appears, then collapse it.
  calc
    (eS.trans e).symm.trans (eS.trans c)
        = ((e.symm.trans eS.symm).trans eS).trans c := by
            simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
              OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (eS.symm.trans eS)).trans c := by
          rw [← OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (OpenPartialHomeomorph.refl Y)).trans c := by
          rw [hmid]
    _ = e.symm.trans c := by
          simp [OpenPartialHomeomorph.trans_refl]

/-- Helper for Problem 2-12: a model-space partial homeomorphism belongs to the smooth groupoid
once its whole source is locally covered by smooth structomorph witnesses. -/
private theorem mem_contDiffGroupoid_of_local_structomorphOn_source
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {f : OpenPartialHomeomorph H H}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ I := by
  refine (contDiffGroupoid ∞ I).locality ?_
  intro x hx
  -- Read the local structomorphism witness in the model chart `chartAt H x = refl`.
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
  -- Restricting `f` to the neighborhood where it agrees with `e` lets `mem_of_eqOnSource` close.
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid ∞ I).mem_of_eqOnSource he hEqOnSource

/-- Helper for Problem 2-12: writing a diffeomorphism in maximal-atlas charts produces a smooth
transition map on the model space. -/
private theorem written_in_diffeomorph_mem_contDiffGroupoid
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (Φ : M ≃ₘ⟮I, I⟯ N)
    {e : OpenPartialHomeomorph M H}
    {c : OpenPartialHomeomorph N H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hc : c ∈ IsManifold.maximalAtlas I ∞ N) :
    (e.symm.trans Φ.toHomeomorph.toOpenPartialHomeomorph).trans c ∈ contDiffGroupoid ∞ I := by
  let f : OpenPartialHomeomorph H H :=
    (e.symm.trans Φ.toHomeomorph.toOpenPartialHomeomorph).trans c
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt)
        Φ.toHomeomorph.toOpenPartialHomeomorph
        Φ.toHomeomorph.toOpenPartialHomeomorph.source := by
    -- The diffeomorphism is smooth in both directions on its full source and target.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := I) (n := (∞ : ℕ∞ω)) (f := Φ.toHomeomorph.toOpenPartialHomeomorph)).2
      ⟨by
          simpa using Φ.contMDiff_toFun.contMDiffOn
       , by
          simpa using Φ.contMDiff_invFun.contMDiffOn⟩
  -- Transport the local structomorphism property through the chosen source and target charts.
  refine mem_contDiffGroupoid_of_local_structomorphOn_source (I := I) ?_
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Set.preimage_id_eq]
  refine ⟨f.continuousOn_toFun.continuousWithinAt hy, ?_⟩
  intro hyf
  have hy_chart :
      y ∈ e.target ∩ e.symm ⁻¹' (Φ.toHomeomorph.toOpenPartialHomeomorph.source ∩
        Φ.toHomeomorph.toOpenPartialHomeomorph ⁻¹' c.source) := by
    have hyf' := hyf
    simp only [f, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hyf'
    rcases hyf' with ⟨⟨hy_target, hy_source⟩, hy_csource⟩
    exact ⟨hy_target, hy_source, hy_csource⟩
  have htransport :
      (contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt
        (c ∘ Φ.toHomeomorph.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Φ.toHomeomorph.toOpenPartialHomeomorph.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ I))
      he hc hΦ hy_chart
  rcases htransport hy_chart.2.1 with ⟨φ, hφ, hEq, hyφ⟩
  refine ⟨φ, hφ, ?_, hyφ⟩
  -- The local witness on the larger source still agrees with the written-in-chart map
  -- on its actual composite source.
  intro z hz
  have hz_big : z ∈ (e.symm ⁻¹' Φ.toHomeomorph.toOpenPartialHomeomorph.source) ∩ φ.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

/-- Helper for Problem 2-12: pulling back an atlas chart along a diffeomorphism yields a chart in
the source maximal atlas. -/
theorem transported_chart_mem_maximalAtlas_of_diffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (Φ : M ≃ₘ⟮I, I⟯ N)
    {e : OpenPartialHomeomorph N H}
    (he : e ∈ atlas H N) :
    Φ.toHomeomorph.toOpenPartialHomeomorph.trans e ∈ IsManifold.maximalAtlas I ∞ M := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  have he_max : e ∈ IsManifold.maximalAtlas I ∞ N := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) he
  have hc_max : c ∈ IsManifold.maximalAtlas I ∞ M := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  constructor
  · -- The forward transition uses the inverse diffeomorphism written in the target chart `e`
    -- and source chart `c`.
    simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      written_in_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ.symm) (e := e) (c := c) he_max hc_max
  · -- The reverse transition writes `Φ` itself in the source chart `c` and target chart `e`.
    simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      written_in_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ) (e := c) (c := e) hc_max he_max

/-- Helper for Problem 2-12: in affine coordinates, a projectivized complex linear equivalence is
the usual quotient of transformed homogeneous coordinates. -/
private theorem Projectivization.linear_equiv_projective_chart_formula
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) (u : EuclideanSpace ℂ (Fin m))
    (h : e (complexProjectiveChartInvVector m i u) j ≠ 0) :
    complexProjectiveChart m j
      (Projectivization.map e.toLinearMap e.injective ((complexProjectiveChart m i).symm u)) =
        WithLp.toLp 2
          (fun k ↦
            e (complexProjectiveChartInvVector m i u) (j.succAbove k) /
              e (complexProjectiveChartInvVector m i u) j) := by
  have hv :
      e (complexProjectiveChartInvVector m i u) ≠ 0 := by
    -- The transformed representative cannot vanish because its `j`th coordinate is nonzero.
    intro hzero
    exact h (by simpa [hzero])
  -- Rewrite the source point as the inserted representative `[u,1]`.
  rw [complexProjectiveChart_symm_apply, Projectivization.map_mk]
  -- Evaluate the target chart on the transformed representative and use the denominator hypothesis.
  simpa [EuclideanSpace.equiv] using
    (complexProjectiveChart_mk m j
      (e (complexProjectiveChartInvVector m i u))
      hv)

/-- Helper for Problem 2-12: after applying a complex linear automorphism to the inserted
homogeneous representative `[u,1]`, membership in the `j`-chart domain is exactly the
nonvanishing of the transformed `j`th homogeneous coordinate. -/
private theorem Projectivization.linear_equiv_projective_image_mem_chartDomain_iff
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) (u : EuclideanSpace ℂ (Fin m)) :
    Projectivization.map e.toLinearMap e.injective ((complexProjectiveChart m i).symm u) ∈
        complexProjectiveChartDomain m j ↔
      e (complexProjectiveChartInvVector m i u) j ≠ 0 := by
  have hv :
      e (complexProjectiveChartInvVector m i u) ≠ 0 := by
    -- Injectivity of `e` preserves the nonzero inserted representative.
    intro hzero
    have hzero' : e (complexProjectiveChartInvVector m i u) = e 0 := by
      simpa using hzero
    exact complexProjectiveChartInvVector_ne_zero m i u (e.injective hzero')
  -- Rewrite the projective point as the class of the transformed representative and read the
  -- chart-domain condition on that representative.
  rw [complexProjectiveChart_symm_apply, Projectivization.map_mk]
  simpa using
    (complexProjectiveChartDomain_mk m j
      (e (complexProjectiveChartInvVector m i u)) hv)

/-- Helper for Problem 2-12: the inserted homogeneous representative depends smoothly on the
affine coordinates. -/
private theorem complexProjectiveChartInvVector_contDiff (n : ℕ) (i : Fin (n + 1)) :
    ContDiff ℝ ω (complexProjectiveChartInvVector n i) := by
  -- Keep the proof on the Pi-side: each homogeneous coordinate is either a fixed `1` or one of
  -- the affine coordinates, and `WithLp.toLp` repackages the coordinatewise smooth map.
  refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin (n + 1) ↦ ℂ)).comp ?_
  rw [contDiff_pi]
  intro j
  cases j using i.succAboveCases with
  | x =>
      simpa [complexProjectiveChartInvVector] using
        (contDiff_const :
          ContDiff ℝ ω (fun _ : EuclideanSpace ℂ (Fin n) => (1 : ℂ)))
  | p k =>
      simpa [complexProjectiveChartInvVector] using
        ((contDiff_piLp_apply (p := 2) (i := k)) :
          ContDiff ℝ ω (fun u : EuclideanSpace ℂ (Fin n) ↦ u k))

/-- Helper for Problem 2-12: each transformed homogeneous coordinate
`u ↦ e (complexProjectiveChartInvVector n i u) l` is smooth as a real map. -/
private theorem Projectivization.linear_equiv_projective_coordinate_contDiff
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i l : Fin (m + 1)) :
    ContDiff ℝ ω
      (fun u : EuclideanSpace ℂ (Fin m) ↦ e (complexProjectiveChartInvVector m i u) l) := by
  let eR : EuclideanSpace ℂ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℂ (Fin (m + 1)) :=
    (e.toContinuousLinearEquiv).restrictScalars ℝ
  have himage :
      ContDiff ℝ ω
        (fun u : EuclideanSpace ℂ (Fin m) ↦ eR (complexProjectiveChartInvVector m i u)) := by
    -- Restrict scalars to `ℝ` so the complex-linear automorphism becomes a smooth real-linear
    -- automorphism, then compose it with the inserted homogeneous vector.
    simpa [eR] using
      eR.contDiff.comp (complexProjectiveChartInvVector_contDiff m i)
  -- Finally project to the `l`th homogeneous coordinate.
  simpa [Function.comp] using
    ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := l)) : ContDiff ℝ ω
      (fun v : EuclideanSpace ℂ (Fin (m + 1)) ↦ v l)).comp himage

/-- Helper for Problem 2-12: in affine coordinates, the projectivized complex linear
automorphism is smooth on the nonvanishing denominator locus because every coordinate is a smooth
quotient of transformed homogeneous coordinates. -/
private theorem Projectivization.linear_equiv_projective_chart_contDiffOn
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) :
    ContDiffOn ℝ ω
      (fun u : EuclideanSpace ℂ (Fin m) ↦
        WithLp.toLp 2
          (fun k ↦
            e (complexProjectiveChartInvVector m i u) (j.succAbove k) /
              e (complexProjectiveChartInvVector m i u) j))
      {u | e (complexProjectiveChartInvVector m i u) j ≠ 0} := by
  let s : Set (EuclideanSpace ℂ (Fin m)) :=
    {u | e (complexProjectiveChartInvVector m i u) j ≠ 0}
  have hden :
      ContDiffOn ℝ ω
        (fun u : EuclideanSpace ℂ (Fin m) ↦ e (complexProjectiveChartInvVector m i u) j) s :=
    (Projectivization.linear_equiv_projective_coordinate_contDiff e i j).contDiffOn
  have hnum :
      ∀ k : Fin m,
        ContDiffOn ℝ ω
          (fun u : EuclideanSpace ℂ (Fin m) ↦
            e (complexProjectiveChartInvVector m i u) (j.succAbove k))
          s := fun k ↦
            (Projectivization.linear_equiv_projective_coordinate_contDiff
              e i (j.succAbove k)).contDiffOn
  have hcoord :
      ∀ k : Fin m,
        ContDiffOn ℝ ω
          (fun u : EuclideanSpace ℂ (Fin m) ↦
            e (complexProjectiveChartInvVector m i u) (j.succAbove k) /
              e (complexProjectiveChartInvVector m i u) j)
          s := by
    intro k
    -- Each affine coordinate is a numerator times the inverse of the chosen nonzero
    -- denominator coordinate.
    simpa [div_eq_mul_inv] using
      (hnum k).mul (hden.inv fun u hu ↦ hu)
  have htoLp :
      ContDiffOn ℝ ω
        (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m))
        Set.univ :=
    (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin m ↦ ℂ)).contDiffOn
  -- Package the coordinatewise quotient map back into Euclidean space.
  refine htoLp.comp ?_ fun _ _ ↦ by simp
  exact contDiffOn_pi.2 hcoord

/-- Helper for Problem 2-12: each standard affine chart of `ℂP[m]` already belongs to the smooth
maximal atlas. -/
private theorem complex_projective_chart_mem_maximalAtlas (i : Fin (m + 1)) :
    complexProjectiveChart m i ∈ IsManifold.maximalAtlas Icp ∞ (ℂP[m]) := by
  -- The charted-space atlas of `ℂP[m]` is generated by the standard affine charts.
  have hAtlas : complexProjectiveChart m i ∈ atlas (EuclideanSpace ℂ (Fin m)) (ℂP[m]) := by
    change complexProjectiveChart m i ∈ { e | ∃ j : Fin (m + 1), e = complexProjectiveChart m j }
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas (I := Icp) (n := ∞) hAtlas

/-- Helper for Problem 2-12: the chart-overlap image for a projectivized complex linear
automorphism is exactly the nonvanishing denominator set appearing in the affine formula. -/
private theorem Projectivization.linear_equiv_projective_overlap_image_eq
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) :
    ((complexProjectiveChart m i).extend Icp ''
        ((complexProjectiveChart m i).source ∩
          (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) ⁻¹'
            (complexProjectiveChart m j).source)) =
      {u : EuclideanSpace ℂ (Fin m) | e (complexProjectiveChartInvVector m i u) j ≠ 0} := by
  -- Route correction: rewrite the manifold overlap through the fixed `i`-chart before invoking
  -- the affine nonvanishing criterion for the transformed representative.
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx_source, hx_target⟩
    -- Replace the source point by its `i`-chart coordinates.
    have hx_eq :
        (complexProjectiveChart m i).symm ((complexProjectiveChart m i).extend Icp x) = x := by
      simpa [OpenPartialHomeomorph.extend_coe] using
        (OpenPartialHomeomorph.left_inv (complexProjectiveChart m i) hx_source)
    -- The target-chart membership is exactly the nonvanishing denominator condition.
    have hiff :=
      Projectivization.linear_equiv_projective_image_mem_chartDomain_iff
        e i j ((complexProjectiveChart m i).extend Icp x)
    have hx_target' :
        Projectivization.map e.toLinearMap e.injective
            ((complexProjectiveChart m i).symm ((complexProjectiveChart m i).extend Icp x)) ∈
          complexProjectiveChartDomain m j := by
      simpa [OpenPartialHomeomorph.extend_coe, hx_source, hx_eq] using hx_target
    simpa [OpenPartialHomeomorph.extend_coe, hx_source] using hiff.mp hx_target'
  · intro hu
    -- Start from affine coordinates `u`, move back to the `i`-chart inverse, and recover the
    -- overlap membership from the same nonvanishing criterion.
    refine ⟨(complexProjectiveChart m i).symm u, ?_, ?_⟩
    · constructor
      · exact complexProjectiveChart_symm_mem_domain m i u
      · exact
          (Projectivization.linear_equiv_projective_image_mem_chartDomain_iff e i j u).2 hu
    · simpa [OpenPartialHomeomorph.extend_coe] using
        (OpenPartialHomeomorph.right_inv (complexProjectiveChart m i) (by simp : u ∈ Set.univ))

/-- Helper for Problem 2-12: on a fixed chart overlap, the projectivized complex linear
automorphism is smooth as a manifold map. -/
private theorem Projectivization.complex_linear_equiv_projectivization_written_in_chart_eq
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) :
    Set.EqOn
      (((complexProjectiveChart m j).extend Icp) ∘
        (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) ∘
        ((complexProjectiveChart m i).extend Icp).symm)
      (fun u : EuclideanSpace ℂ (Fin m) ↦
        WithLp.toLp 2
          (fun k ↦
            e (complexProjectiveChartInvVector m i u) (j.succAbove k) /
              e (complexProjectiveChartInvVector m i u) j))
      {u : EuclideanSpace ℂ (Fin m) | e (complexProjectiveChartInvVector m i u) j ≠ 0} := by
  intro u hu
  -- Route correction: normalize the written map in extended charts back to the explicit affine
  -- quotient formula before invoking the already-proved `ContDiffOn` statement.
  have hu_target :
      Projectivization.map e.toLinearMap e.injective
          (((complexProjectiveChart m i).extend Icp).symm u) ∈
        (complexProjectiveChart m j).source := by
    simpa [OpenPartialHomeomorph.extend_coe_symm] using
      (Projectivization.linear_equiv_projective_image_mem_chartDomain_iff e i j u).2 hu
  -- Once the source and target extended charts are rewritten to the standard charts, the map is
  -- exactly the affine quotient formula from `linear_equiv_projective_chart_formula`.
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, hu_target] using
    Projectivization.linear_equiv_projective_chart_formula e i j u hu

/-- Helper for Problem 2-12: every preferred chart on `ℂP[m]` is literally one of the standard
affine charts. -/
private theorem Projectivization.exists_chartAt_eq_complexProjectiveChart (x : ℂP[m]) :
    ∃ i : Fin (m + 1), chartAt (EuclideanSpace ℂ (Fin m)) x = complexProjectiveChart m i := by
  -- The charted-space atlas on `ℂP[m]` was defined to be exactly the set of standard affine
  -- charts, so `chart_mem_atlas` immediately identifies the chosen chart.
  have hx := chart_mem_atlas (H := EuclideanSpace ℂ (Fin m)) x
  change ∃ i : Fin (m + 1), chartAt (EuclideanSpace ℂ (Fin m)) x = complexProjectiveChart m i at hx
  simpa using hx

/-- Helper for Problem 2-12: on a fixed chart overlap, the projectivized complex linear
automorphism is smooth as a manifold map. -/
private theorem Projectivization.complex_linear_equiv_projectivization_contMDiffOn_chart_overlap
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (i j : Fin (m + 1)) :
    ContMDiffOn Icp Icp ∞
      (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x)
      ((complexProjectiveChart m i).source ∩
        (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) ⁻¹'
          (complexProjectiveChart m j).source) := by
  let f : ℂP[m] → ℂP[m] := fun x ↦ Projectivization.map e.toLinearMap e.injective x
  let s : Set (ℂP[m]) :=
    (complexProjectiveChart m i).source ∩ f ⁻¹' (complexProjectiveChart m j).source
  have hs : s ⊆ (complexProjectiveChart m i).source := fun _ hx ↦ hx.1
  have hmaps : Set.MapsTo f s (complexProjectiveChart m j).source := fun _ hx ↦ hx.2
  -- Package the chartwise computation via the standard written-in-extend criterion.
  refine
    (OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
      (φ := complexProjectiveChart m i) (ψ := complexProjectiveChart m j)
      (I := Icp) (J := Icp) (n := (∞ : ℕ∞ω)) (f := f) (s := s)
      (complex_projective_chart_mem_maximalAtlas (m := m) i)
      (complex_projective_chart_mem_maximalAtlas (m := m) j)
      hs hmaps).1 ?_
  rw [contMDiffOn_iff_contDiffOn]
  rw [Projectivization.linear_equiv_projective_overlap_image_eq (m := m) e i j]
  -- The written map is exactly the affine quotient formula already known to be smooth.
  have hwritten :
      ContDiffOn ℝ ω
        (((complexProjectiveChart m j).extend Icp) ∘ f ∘
          ((complexProjectiveChart m i).extend Icp).symm)
        {u : EuclideanSpace ℂ (Fin m) | e (complexProjectiveChartInvVector m i u) j ≠ 0} := by
    refine (Projectivization.linear_equiv_projective_chart_contDiffOn (m := m) e i j).congr ?_
    intro u hu
    exact Projectivization.complex_linear_equiv_projectivization_written_in_chart_eq
      (m := m) e i j hu
  simpa [f] using hwritten.of_le le_top

/-- Helper for Problem 2-12: a complex linear automorphism of the homogeneous coordinates induces
an everywhere-smooth self-map of the standard complex projective space. -/
private theorem Projectivization.complex_linear_equiv_projectivization_contMDiff
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1))) :
    ContMDiff Icp Icp ∞
      (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  let P :
      {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0} →
        {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0} :=
    fun v ↦ ⟨e v, by
      intro hzero
      exact v.2 <| e.injective (by simpa using hzero)⟩
  let f : ℂP[m] → ℂP[m] := fun x ↦ Projectivization.map e.toLinearMap e.injective x
  have hP : Continuous P := by
    -- The representative-level linear equivalence is continuous and preserves nonzero vectors.
    exact (e.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk fun v ↦ by
      intro hzero
      exact v.2 <| e.injective (by simpa using hzero)
  have hcont : Continuous f := by
    let q : {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0} → ℂP[m] := Projectivization.mk' ℂ
    have hq : Continuous q := by
      simpa [q, Projectivization.mk'] using
        (continuous_quotient_mk' :
          Continuous
            (@Quotient.mk'
              {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0}
              (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin (m + 1))))))
    have hmk :
        Continuous
          (fun v : {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0} ↦
            Projectivization.mk ℂ (e v) (P v).2) := by
      simpa [q, P, Projectivization.mk'_eq_mk] using hq.comp hP
    -- Descend the continuous representative map through the projectivization quotient.
    simpa [f, Projectivization.map, Projectivization.lift, P] using
      hmk.quotient_lift fun a b hab ↦ by
        rcases (show ∃ c : ℂˣ,
            c • (b : EuclideanSpace ℂ (Fin (m + 1))) = (a : EuclideanSpace ℂ (Fin (m + 1))) from by
          simpa [projectivizationSetoid, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
            using hab) with ⟨c, hc⟩
        change Projectivization.mk ℂ (e a) (P a).2 = Projectivization.mk ℂ (e b) (P b).2
        exact
          (Projectivization.mk_eq_mk_iff ℂ (e a) (e b) (P a).2 (P b).2).2
            ⟨c, by
              have hsmul :
                  c • e (b : EuclideanSpace ℂ (Fin (m + 1))) =
                    e (c • (b : EuclideanSpace ℂ (Fin (m + 1)))) := by
                exact (e.map_smul c (b : EuclideanSpace ℂ (Fin (m + 1)))).symm
              calc
                c • e (b : EuclideanSpace ℂ (Fin (m + 1)))
                    = e (c • (b : EuclideanSpace ℂ (Fin (m + 1)))) := hsmul
                _ = e (a : EuclideanSpace ℂ (Fin (m + 1))) := by rw [hc]⟩
  intro x
  rcases complex_projective_space_has_standard_chart m x with ⟨i, hi⟩
  rcases complex_projective_space_has_standard_chart m (f x) with ⟨j, hj⟩
  let s : Set (ℂP[m]) :=
    (complexProjectiveChart m i).source ∩ f ⁻¹' (complexProjectiveChart m j).source
  have hs_nhds : s ∈ nhds x := by
    -- The chosen source and target charts remain valid on a neighborhood of `x` by continuity.
    have hi_nhds : (complexProjectiveChart m i).source ∈ nhds x :=
      (complexProjectiveChart m i).open_source.mem_nhds hi
    have hj_nhds : f ⁻¹' (complexProjectiveChart m j).source ∈ nhds x :=
      hcont.continuousAt.preimage_mem_nhds <|
        (complexProjectiveChart m j).open_source.mem_nhds hj
    simpa [s] using Filter.inter_mem hi_nhds hj_nhds
  have hlocal : ContMDiffOn Icp Icp ∞ f s := by
    simpa [f, s] using
      Projectivization.complex_linear_equiv_projectivization_contMDiffOn_chart_overlap
        (m := m) e i j
  -- The overlap theorem gives `C^∞` regularity on a neighborhood of `x`, hence at `x`.
  exact hlocal.contMDiffAt hs_nhds

namespace Projectivization

section ComplexBasisTransport

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Helper for Problem 2-12: the inverse basis map is induced by the inverse basis linear
equivalence. -/
private def complex_basisMapSymm (b : Module.Basis (Fin (m + 1)) ℂ V) :
    ℙ ℂ V → ℂP[m] :=
  Projectivization.map (Projectivization.basisLinearEquiv b).symm.toLinearMap
    (Projectivization.basisLinearEquiv b).symm.injective

/-- Helper for Problem 2-12: the basis-induced projectivization map is an equivalence of sets. -/
private def complex_basisEquiv (b : Module.Basis (Fin (m + 1)) ℂ V) :
    ℂP[m] ≃ ℙ ℂ V :=
  { toFun := Projectivization.basisMap b
    invFun := complex_basisMapSymm (m := m) b
    left_inv := fun x ↦ by
      let e := Projectivization.basisLinearEquiv b
      have hcomp :
          complex_basisMapSymm (m := m) b (Projectivization.basisMap b x) =
            Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective x := by
        -- Compose the forward and inverse basis maps to collapse to the identity linear
        -- equivalence on homogeneous coordinates.
        simpa [complex_basisMapSymm, Projectivization.basisMap, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.toLinearMap e.injective e.symm.toLinearMap e.symm.injective).symm
      have hid :
          Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective = id := by
        -- The projectivization of the identity linear map acts trivially on every line.
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.self_trans_symm]
      calc
        complex_basisMapSymm (m := m) b (Projectivization.basisMap b x)
            = Projectivization.map
                (e.trans e.symm).toLinearMap
                (e.trans e.symm).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid
    right_inv := fun x ↦ by
      let e := Projectivization.basisLinearEquiv b
      have hcomp :
          Projectivization.basisMap b (complex_basisMapSymm (m := m) b x) =
            Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective x := by
        -- The inverse-first composite similarly collapses to the identity linear equivalence.
        simpa [complex_basisMapSymm, Projectivization.basisMap, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.symm.toLinearMap e.symm.injective e.toLinearMap e.injective).symm
      have hid :
          Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective = id := by
        -- Again, the induced projective map of the identity is pointwise the identity.
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.symm_trans_self]
      calc
        Projectivization.basisMap b (complex_basisMapSymm (m := m) b x)
            = Projectivization.map
                (e.symm.trans e).toLinearMap
                (e.symm.trans e).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid }

/-- Helper for Problem 2-12: transport the standard topology on `ℂP[m]` across the basis
equivalence. -/
private abbrev complex_topologicalSpaceOfBasis (b : Module.Basis (Fin (m + 1)) ℂ V) :
    TopologicalSpace (ℙ ℂ V) :=
  (complex_basisEquiv (m := m) b).symm.topologicalSpace

/-- Helper for Problem 2-12: the transported basis homeomorphism is defined on all of `ℙ ℂ V`. -/
private theorem complex_basisHomeomorph_source_univ
    (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    (((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph).source =
      Set.univ := by
  simp [Homeomorph.toOpenPartialHomeomorph]

/-- Helper for Problem 2-12: transport a standard chart on `ℂP[m]` across the basis
homeomorphism. -/
private def complex_chartOfBasis (b : Module.Basis (Fin (m + 1)) ℂ V)
    (e : OpenPartialHomeomorph (ℂP[m]) (EuclideanSpace ℂ (Fin m))) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    OpenPartialHomeomorph (ℙ ℂ V) (EuclideanSpace ℂ (Fin m)) :=
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph.trans e

/-- Helper for Problem 2-12: the transported complex projective charts define the charted-space
structure on `ℙ ℂ V` associated with the chosen basis. -/
private abbrev complex_chartedSpaceOfBasis (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  let eS : OpenPartialHomeomorph (ℙ ℂ V) (ℂP[m]) :=
    ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℂP[m]) (ℙ ℂ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS)
      (complex_basisHomeomorph_source_univ (m := m) b)
  ChartedSpace.comp (EuclideanSpace ℂ (Fin m)) (ℂP[m]) (ℙ ℂ V)

/-- Helper for Problem 2-12: the transported charted-space structure from a chosen basis is a
smooth manifold because its chart transitions reduce to the standard ones on `ℂP[m]`. -/
private theorem complex_isManifoldOfBasis (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    let _ : @ChartedSpace (EuclideanSpace ℂ (Fin m)) _ (ℙ ℂ V)
      (complex_topologicalSpaceOfBasis (m := m) b) := complex_chartedSpaceOfBasis (m := m) b
    IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := by
  letI : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  let eS : OpenPartialHomeomorph (ℙ ℂ V) (ℂP[m]) :=
    ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph
  let hS : eS.source = Set.univ := complex_basisHomeomorph_source_univ (m := m) b
  letI : ChartedSpace (ℂP[m]) (ℙ ℂ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS) hS
  letI : @ChartedSpace (EuclideanSpace ℂ (Fin m)) _ (ℙ ℂ V)
      (complex_topologicalSpaceOfBasis (m := m) b) := complex_chartedSpaceOfBasis (m := m) b
  have hGroupoid : HasGroupoid (ℙ ℂ V) (contDiffGroupoid (⊤ : ℕ∞ω) Icp) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa using OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq (e := eS) hS f hf
    have hf'Eq : f' = eS := by
      simpa using OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq (e := eS) hS f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl (ℂP[m]) := by
      -- The transport chart is a global homeomorphism, so composing it with its inverse is `refl`.
      ext x <;> simp [eS]
    have hcMax :
        c ∈ IsManifold.maximalAtlas Icp (⊤ : ℕ∞ω) (ℂP[m]) := by
      exact IsManifold.subset_maximalAtlas (I := Icp) (n := (⊤ : ℕ∞ω)) hc
    have hc'Max :
        c' ∈ IsManifold.maximalAtlas Icp (⊤ : ℕ∞ω) (ℂP[m]) := by
      exact IsManifold.subset_maximalAtlas (I := Icp) (n := (⊤ : ℕ∞ω)) hc'
    -- After canceling the singleton transport chart, compatibility is exactly the standard
    -- complex projective compatibility already known on `ℂP[m]`.
    have hcompat :
        c.symm.trans c' ∈ contDiffGroupoid (⊤ : ℕ∞ω) Icp := by
      exact IsManifold.compatible_of_mem_maximalAtlas hcMax hc'Max
    have htransport :
        (eS.trans c).symm.trans (eS.trans c') = c.symm.trans c' := by
      simpa using
        transported_transition_eq (eS := eS) (e := c) (c := c') hmid
    rw [htransport]
    exact hcompat
  -- The transported atlas is the standard complex projective atlas pulled back through a global
  -- homeomorphism, so it carries the same smooth structure.
  exact IsManifold.mk' Icp (⊤ : ℕ∞ω) (ℙ ℂ V)

/-- Helper for Problem 2-12: in the singleton intermediate charted space used to transport the
standard atlas, the preferred chart at every point is the basis homeomorphism itself. -/
private theorem complexBasisIntermediateChartAt_eq
    (b : Module.Basis (Fin (m + 1)) ℂ V) (y : ℙ ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    let _ : ChartedSpace (ℂP[m]) (ℙ ℂ V) :=
      OpenPartialHomeomorph.singletonChartedSpace
        (e := ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph)
        (complex_basisHomeomorph_source_univ (m := m) b)
    chartAt (ℂP[m]) y =
      ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph := by
  -- The intermediate atlas is singleton, so `chartAt` is definitionally the chosen transport
  -- homeomorphism at every point.
  simp [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]

/-- Helper for Problem 2-12: the chosen-basis transport map is smooth from the standard model
into the transported manifold structure on `ℙ ℂ V`. -/
private theorem complex_basisMap_contMDiff
    (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
      complex_chartedSpaceOfBasis (m := m) b
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
    ContMDiff Icp Icp ∞ (Projectivization.basisMap b) := by
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  let eS : OpenPartialHomeomorph (ℙ ℂ V) (ℂP[m]) :=
    ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℂP[m]) (ℙ ℂ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS)
      (complex_basisHomeomorph_source_univ (m := m) b)
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
    complex_chartedSpaceOfBasis (m := m) b
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
  -- Normalize away the statement-level transport wrappers so the pointwise chart argument can
  -- work with the local instances directly.
  change ContMDiff Icp Icp ∞ (Projectivization.basisMap b)
  intro x
  rw [contMDiffAt_iff]
  constructor
  · -- Continuity is inherited from the transported homeomorphism before any chart computation.
    simpa [eS, complex_basisMapSymm] using
      (((complex_basisEquiv (m := m) b).symm.homeomorph).continuous_invFun.continuousAt :
        ContinuousAt (Projectivization.basisMap b) x)
  · -- Route correction: rewrite the intermediate target chart to `eS`, so the written map is the
    -- canonical `chartAt.symm` identity from `writtenInExtChartAt_chartAt_symm_comp`.
    have hchart :
        chartAt (ℂP[m]) (Projectivization.basisMap b x) = eS := by
      simpa [eS] using
        complexBasisIntermediateChartAt_eq (m := m) (V := V) b
          (Projectivization.basisMap b x)
    have hpoint : eS (Projectivization.basisMap b x) = x := by
      change complex_basisMapSymm (m := m) b (Projectivization.basisMap b x) = x
      exact (complex_basisEquiv (m := m) b).left_inv x
    have hcenter :
        letI := ChartedSpace.comp (EuclideanSpace ℂ (Fin m)) (ℂP[m]) (ℙ ℂ V)
        extChartAt Icp (Projectivization.basisMap b x) (Projectivization.basisMap b x) =
          extChartAt Icp x x := by
      simpa [extChartAt_comp, chartAt_comp, hchart, hpoint,
        OpenPartialHomeomorph.trans_apply]
    have hcenterChart :
        letI := ChartedSpace.comp (EuclideanSpace ℂ (Fin m)) (ℂP[m]) (ℙ ℂ V)
        chartAt (EuclideanSpace ℂ (Fin m)) (Projectivization.basisMap b x)
            (Projectivization.basisMap b x) =
          chartAt (EuclideanSpace ℂ (Fin m)) x x := by
      simpa [chartAt_comp, hchart, hpoint, OpenPartialHomeomorph.trans_apply]
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt ℝ ∞
          (id : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin m))
          (Set.range Icp) (extChartAt Icp x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · have htarget :
          letI := ChartedSpace.comp (EuclideanSpace ℂ (Fin m)) (ℂP[m]) (ℙ ℂ V)
          (extChartAt Icp (Projectivization.basisMap b x)).target ∈
            nhdsWithin (extChartAt Icp x x) (Set.range Icp) := by
        have htarget' :
            letI := ChartedSpace.comp (EuclideanSpace ℂ (Fin m)) (ℂP[m]) (ℙ ℂ V)
            (extChartAt Icp (Projectivization.basisMap b x)).target ∈
              nhdsWithin
                (extChartAt Icp (Projectivization.basisMap b x)
                  (Projectivization.basisMap b x))
                (Set.range Icp) := by
          exact extChartAt_target_mem_nhdsWithin (I := Icp)
            (Projectivization.basisMap b x)
        simpa [hcenter, hcenterChart] using htarget'
      filter_upwards [htarget] with y hy
      simpa [hchart, hpoint, eS, complex_basisMapSymm] using
        (writtenInExtChartAt_chartAt_symm_comp
          (I := Icp) (H := EuclideanSpace ℂ (Fin m)) (H' := ℂP[m])
          (x := Projectivization.basisMap b x) (y := y) hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (I := Icp) x)
        (mem_extChartAt_target (I := Icp) x)

/-- Helper for Problem 2-12: the inverse chosen-basis transport map is smooth back to the
standard model. -/
private theorem complex_basisMapSymm_contMDiff
    (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
      complex_chartedSpaceOfBasis (m := m) b
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
    ContMDiff Icp Icp ∞ (complex_basisMapSymm (m := m) b) := by
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  let eS : OpenPartialHomeomorph (ℙ ℂ V) (ℂP[m]) :=
    ((complex_basisEquiv (m := m) b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℂP[m]) (ℙ ℂ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS)
      (complex_basisHomeomorph_source_univ (m := m) b)
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
    complex_chartedSpaceOfBasis (m := m) b
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
  -- Normalize away the transported-instance wrappers before switching to the pointwise criterion.
  change ContMDiff Icp Icp ∞ (complex_basisMapSymm (m := m) b)
  intro x
  rw [contMDiffAt_iff]
  constructor
  · -- The inverse map is the forward direction of the transported homeomorphism.
    simpa [eS, complex_basisMapSymm] using
      (((complex_basisEquiv (m := m) b).symm.homeomorph).continuous_toFun.continuousAt :
        ContinuousAt (complex_basisMapSymm (m := m) b) x)
  · -- Rewriting the source chart to `eS` reduces the written map to the chart identity in the
    -- same stable normal form as the forward direction.
    have hchart : chartAt (ℂP[m]) x = eS := by
      simpa [eS] using complexBasisIntermediateChartAt_eq (m := m) (V := V) b x
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt ℝ ∞
          (id : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin m))
          (Set.range Icp) (extChartAt Icp x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin (I := Icp) x] with y hy
      simpa [hchart, eS, complex_basisMapSymm] using
        (writtenInExtChartAt_chartAt_comp
          (I := Icp) (H := EuclideanSpace ℂ (Fin m)) (H' := ℂP[m])
          (x := x) (y := y) hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (I := Icp) x)
        (mem_extChartAt_target (I := Icp) x)

/-- Helper for Problem 2-12: bundle the chosen-basis transport map into a diffeomorphism from the
standard complex projective space to the transported manifold structure on `ℙ ℂ V`. -/
private def complex_basis_transport_diffeomorph
    (b : Module.Basis (Fin (m + 1)) ℂ V) :
    let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
      complex_chartedSpaceOfBasis (m := m) b
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
    ℂP[m] ≃ₘ⟮Icp, Icp⟯ ℙ ℂ V :=
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
    complex_chartedSpaceOfBasis (m := m) b
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b
  { toEquiv := complex_basisEquiv (m := m) b
    contMDiff_toFun := complex_basisMap_contMDiff (m := m) b
    contMDiff_invFun := complex_basisMapSymm_contMDiff (m := m) b }

/-- Helper for Problem 2-12: the basis-change linear equivalence `A` intertwines the chosen base
basis map with any other basis map. -/
private theorem basis_map_eq_base_basis_comp_projectivization
    (b₀ b : Module.Basis (Fin (m + 1)) ℂ V) :
    let A :
        EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
      (Projectivization.basisLinearEquiv b).trans (Projectivization.basisLinearEquiv b₀).symm
    Projectivization.basisMap b =
      Projectivization.basisMap b₀ ∘ Projectivization.map A.toLinearMap A.injective := by
  let A :
      EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
    (Projectivization.basisLinearEquiv b).trans (Projectivization.basisLinearEquiv b₀).symm
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
      -- On representatives, applying `A` and then the base-basis map is the same as applying
      -- the target basis map directly.
      simp [Projectivization.basisMap, A, Projectivization.map_mk]

/-- Helper for Problem 2-12: the projectivized inverse linear equivalence is the inverse of the
projectivized forward linear equivalence. -/
private theorem complex_linear_equiv_projectivization_left_inv
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1))) :
    Function.LeftInverse
      (fun x : ℂP[m] ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x)
      (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  intro x
  have hcomp :
      Projectivization.map e.symm.toLinearMap e.symm.injective
          (Projectivization.map e.toLinearMap e.injective x) =
        Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective x := by
    -- Compose the projectivized maps before collapsing the linear equivalence to `id`.
    simpa [Function.comp] using
      congrArg (fun f ↦ f x) <|
        (Projectivization.map_comp
          e.toLinearMap e.injective e.symm.toLinearMap e.symm.injective).symm
  have hid :
      Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective = id := by
    -- The projectivization of the identity linear equivalence acts trivially on every line.
    ext y
    induction y using Projectivization.ind with
    | h v hv =>
        simp [Projectivization.map_mk, LinearEquiv.self_trans_symm]
  calc
    Projectivization.map e.symm.toLinearMap e.symm.injective
        (Projectivization.map e.toLinearMap e.injective x)
        = Projectivization.map
            (e.trans e.symm).toLinearMap
            (e.trans e.symm).injective x := hcomp
    _ = x := by
      simpa using congrArg (fun f ↦ f x) hid

/-- Helper for Problem 2-12: the projectivized forward linear equivalence is the inverse of the
projectivized inverse linear equivalence. -/
private theorem complex_linear_equiv_projectivization_right_inv
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1))) :
    Function.RightInverse
      (fun x : ℂP[m] ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x)
      (fun x : ℂP[m] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  intro x
  have hcomp :
      Projectivization.map e.toLinearMap e.injective
          (Projectivization.map e.symm.toLinearMap e.symm.injective x) =
        Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective x := by
    -- The inverse-first composite reduces to the identity linear equivalence in the same way.
    simpa [Function.comp] using
      congrArg (fun f ↦ f x) <|
        (Projectivization.map_comp
          e.symm.toLinearMap e.symm.injective e.toLinearMap e.injective).symm
  have hid :
      Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective = id := by
    -- Again the projectivization of the identity acts pointwise as `id`.
    ext y
    induction y using Projectivization.ind with
    | h v hv =>
        simp [Projectivization.map_mk, LinearEquiv.symm_trans_self]
  calc
    Projectivization.map e.toLinearMap e.injective
        (Projectivization.map e.symm.toLinearMap e.symm.injective x)
        = Projectivization.map
            (e.symm.trans e).toLinearMap
            (e.symm.trans e).injective x := hcomp
    _ = x := by
      simpa using congrArg (fun f ↦ f x) hid

private def complex_linear_equiv_projectivization_diffeomorph
    (e : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1))) :
    ℂP[m] ≃ₘ⟮Icp, Icp⟯ ℂP[m] :=
  { toEquiv :=
      { toFun := fun x ↦ Projectivization.map e.toLinearMap e.injective x
        invFun := fun x ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x
        left_inv := complex_linear_equiv_projectivization_left_inv (m := m) e
        right_inv := complex_linear_equiv_projectivization_right_inv (m := m) e }
    contMDiff_toFun := Projectivization.complex_linear_equiv_projectivization_contMDiff (m := m) e
    contMDiff_invFun :=
      Projectivization.complex_linear_equiv_projectivization_contMDiff (m := m) e.symm }

/-- Helper for Problem 2-12: transporting the standard complex projective manifold along one
chosen basis yields a basis-compatible smooth structure on `ℙ ℂ V`. -/
private theorem complex_basisCompatible_ofBasis
    (b₀ : Module.Basis (Fin (m + 1)) ℂ V) :
    Projectivization.BasisCompatible m V
      (complex_topologicalSpaceOfBasis (m := m) b₀)
      (complex_chartedSpaceOfBasis (m := m) b₀)
      (complex_isManifoldOfBasis (m := m) b₀) := by
  let _ : TopologicalSpace (ℙ ℂ V) := complex_topologicalSpaceOfBasis (m := m) b₀
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
    complex_chartedSpaceOfBasis (m := m) b₀
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := complex_isManifoldOfBasis (m := m) b₀
  refine ⟨b₀, ?_⟩
  intro b
  let A : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
    (Projectivization.basisLinearEquiv b).trans (Projectivization.basisLinearEquiv b₀).symm
  let Φ : ℂP[m] ≃ₘ⟮Icp, Icp⟯ ℙ ℂ V :=
    (complex_linear_equiv_projectivization_diffeomorph (m := m) A).trans
      (complex_basis_transport_diffeomorph (m := m) (V := V) b₀)
  refine ⟨Φ, ?_⟩
  intro x
  -- The composite first changes from the standard basis to `b₀`, then transports along `b₀`.
  simpa [Φ, A] using
    (congrArg (fun f : ℂP[m] → ℙ ℂ V ↦ f x)
      (basis_map_eq_base_basis_comp_projectivization (m := m) (V := V) b₀ b)).symm

end ComplexBasisTransport

end Projectivization

/-- Problem 2-12 existence: if `V` is a complex `(m + 1)`-dimensional vector space, then `ℙ ℂ V`
admits a basis-compatible smooth structure modeled on `ℂ^m`. This is the complex specialization
of the generic `RCLike` projectivization construction from Problem 2-11. -/
theorem complex_projectivization_exists_basisCompatible_smoothStructure
    (hm : Module.finrank ℂ V = m + 1) :
    ∃ (t : TopologicalSpace (ℙ ℂ V))
      (c : let _ : TopologicalSpace (ℙ ℂ V) := t
        ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
      (s : let _ : TopologicalSpace (ℙ ℂ V) := t
        let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
        IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V)),
      Projectivization.BasisCompatible m V t c s := by
  -- Route correction: the source-faithful proof first identifies the basis-change automorphism on
  -- the standard model in affine charts, then transports that model structure along one chosen
  -- basis of `V`.
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_finrank_eq_succ hm
  let b := Module.finBasisOfFinrankEq ℂ V hm
  let t : TopologicalSpace (ℙ ℂ V) :=
    Projectivization.complex_topologicalSpaceOfBasis (m := m) b
  let c :
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) :=
    Projectivization.complex_chartedSpaceOfBasis (m := m) b
  let s :
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) :=
    Projectivization.complex_isManifoldOfBasis (m := m) b
  refine ⟨t, c, s, ?_⟩
  let _ : TopologicalSpace (ℙ ℂ V) := t
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
  simpa [b, t, c, s] using
    Projectivization.complex_basisCompatible_ofBasis (m := m) (V := V) b

/-- Problem 2-12 uniqueness, topological part: any two basis-compatible smooth structures on
`ℙ ℂ V` induce the same topology. The source-facing owner remains
`Projectivization.BasisCompatible`; the proof can compare both structures with the same standard
projective-space model via the basis-induced diffeomorphisms from Problem 2-11. -/
theorem complex_projectivization_basisCompatible_unique_topology
    (t : TopologicalSpace (ℙ ℂ V))
    (c : let _ : TopologicalSpace (ℙ ℂ V) := t
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s : let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs : Projectivization.BasisCompatible m V t c s)
    (t' : TopologicalSpace (ℙ ℂ V))
    (c' : let _ : TopologicalSpace (ℙ ℂ V) := t'
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s' : let _ : TopologicalSpace (ℙ ℂ V) := t'
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs' : Projectivization.BasisCompatible m V t' c' s') :
    t = t' := by
  let _ : TopologicalSpace (ℙ ℂ V) := t
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
  rcases hs with ⟨b, hb⟩
  rcases hb b with ⟨Φ, hΦ⟩
  have hΦfun : (Φ : ℂP[m] → ℙ ℂ V) = Projectivization.basisMap b := funext hΦ
  have ht :
      TopologicalSpace.coinduced (Projectivization.basisMap b) inferInstance = t := by
    -- The topology on `ℙ ℂ V` is the coinduced topology from the standard model via `Φ`.
    simpa [hΦfun] using
      (Φ.toHomeomorph.coinduced_eq :
        TopologicalSpace.coinduced (Φ.toHomeomorph : ℂP[m] → ℙ ℂ V) inferInstance = t)
  let _ : TopologicalSpace (ℙ ℂ V) := t'
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s'
  rcases hs' with ⟨_, hb'⟩
  rcases hb' b with ⟨Φ', hΦ'⟩
  have ht' :
      TopologicalSpace.coinduced (Projectivization.basisMap b) inferInstance = t' := by
    -- The same argument for `Φ'` produces the same coinduced topology because the forward map agrees.
    have hΦ'fun : (Φ' : ℂP[m] → ℙ ℂ V) = Projectivization.basisMap b := funext hΦ'
    simpa [hΦ'fun] using
      (Φ'.toHomeomorph.coinduced_eq :
        TopologicalSpace.coinduced (Φ'.toHomeomorph : ℂP[m] → ℙ ℂ V) inferInstance = t')
  exact ht.symm.trans ht'

/-- Problem 2-12 uniqueness, smooth-atlas part: once the topology on `ℙ ℂ V` is fixed, any two
basis-compatible smooth structures determine a common smooth atlas. This is the source-facing
bridge theorem used to invoke Proposition 1.17's canonical comparison of maximal smooth atlases. -/
theorem complex_projectivization_basisCompatible_union_isSmoothAtlas
    (t : TopologicalSpace (ℙ ℂ V))
    (c : let _ : TopologicalSpace (ℙ ℂ V) := t
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s : let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs : Projectivization.BasisCompatible m V t c s)
    (c' : let _ : TopologicalSpace (ℙ ℂ V) := t
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s' : let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs' : Projectivization.BasisCompatible m V t c' s') :
    let _ : TopologicalSpace (ℙ ℂ V) := t
    IsSmoothAtlas Icp (c.atlas ∪ c'.atlas) := by
  let _ : TopologicalSpace (ℙ ℂ V) := t
  let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
  let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
  rcases hs with ⟨b, hb⟩
  rcases hb b with ⟨Φ, hΦ⟩
  let Φh : ℂP[m] ≃ₜ ℙ ℂ V := Φ.toHomeomorph
  have hcross :
      ∀ {e e' : OpenPartialHomeomorph (ℙ ℂ V) (EuclideanSpace ℂ (Fin m))},
        e ∈ c.atlas → e' ∈ c'.atlas → e.symm.trans e' ∈ contDiffGroupoid ∞ Icp := by
    intro e e' he he'
    let _ : TopologicalSpace (ℙ ℂ V) := t
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
    let eS : OpenPartialHomeomorph (ℂP[m]) (ℙ ℂ V) :=
      Φh.toOpenPartialHomeomorph
    have hleft : eS.trans e ∈ IsManifold.maximalAtlas Icp ∞ (ℂP[m]) := by
      -- Pull the `c`-chart back to the standard model using `Φ`.
      simpa [eS] using
        transported_chart_mem_maximalAtlas_of_diffeomorph (I := Icp) (Φ := Φ) he
    have hright : eS.trans e' ∈ IsManifold.maximalAtlas Icp ∞ (ℂP[m]) := by
      let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
      let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s'
      rcases hs' with ⟨_, hb'⟩
      rcases hb' b with ⟨Φ', hΦ'⟩
      let Φh' : ℂP[m] ≃ₜ ℙ ℂ V := Φ'.toHomeomorph
      have hhomeo : Φh = Φh' := by
        -- Both basis-compatible diffeomorphisms extend the same basis map, so their homeomorphs agree.
        ext x
        simpa [Φh, Φh'] using (show Φ x = Φ' x by rw [hΦ x, hΦ' x])
      have hright' :
          Φh'.toOpenPartialHomeomorph.trans e' ∈ IsManifold.maximalAtlas Icp ∞ (ℂP[m]) := by
        -- Pull the `c'`-chart back to the same standard model using `Φ'`.
        simpa using
          transported_chart_mem_maximalAtlas_of_diffeomorph (I := Icp) (Φ := Φ') he'
      simpa [eS] using
        hhomeo ▸ hright'
    have hcompat :
        (eS.trans e).symm.trans (eS.trans e') ∈ contDiffGroupoid ∞ Icp := by
      -- Once both pulled-back charts lie in the standard maximal atlas, they are compatible there.
      exact IsManifold.compatible_of_mem_maximalAtlas hleft hright
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl (ℙ ℂ V) := by
      -- The pulled-back chart family uses a genuine homeomorphism, so the middle factors cancel.
      calc
        eS.symm.trans eS = (Φh.symm.trans Φh).toOpenPartialHomeomorph := by
          simpa [eS] using
            (Homeomorph.trans_toOpenPartialHomeomorph Φh.symm Φh).symm
        _ = (Homeomorph.refl (ℙ ℂ V)).toOpenPartialHomeomorph := by
          rw [Homeomorph.symm_trans_self]
        _ = OpenPartialHomeomorph.refl (ℙ ℂ V) := by
          simp
    have hrewrite :
        (eS.trans e).symm.trans (eS.trans e') = e.symm.trans e' :=
      transported_transition_eq (eS := eS) (e := e) (c := e') hmid
    simpa [hrewrite] using hcompat
  refine ⟨?_, ?_⟩
  · intro x
    -- The original atlas `c.atlas` already covers `ℙ ℂ V`, so the union covers as well.
    exact ⟨chartAt (EuclideanSpace ℂ (Fin m)) x,
      Or.inl (chart_mem_atlas (H := EuclideanSpace ℂ (Fin m)) x),
      mem_chart_source (H := EuclideanSpace ℂ (Fin m)) x⟩
  · intro e e' he he'
    rcases he with he | he
    · rcases he' with he' | he'
      · -- Charts already in `c.atlas` are compatible because `c` is a smooth atlas.
        let _ : TopologicalSpace (ℙ ℂ V) := t
        let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
        let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
        exact HasGroupoid.compatible he he'
      · -- Mixed compatibility is reduced to the standard model via the common basis map.
        exact hcross he he'
    · rcases he' with he' | he'
      · -- Reverse the previously proved mixed case and use symmetry of the smooth groupoid.
        simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
          (contDiffGroupoid ∞ Icp).symm (hcross he' he)
      · -- Charts already in `c'.atlas` are compatible because `c'` is a smooth atlas.
        let _ : TopologicalSpace (ℙ ℂ V) := t
        let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
        let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s'
        exact HasGroupoid.compatible he he'

/-- Problem 2-12 uniqueness, smooth-structure part: once the common topology on `ℙ ℂ V` is fixed,
any two basis-compatible smooth structures determine the same maximal smooth atlas. Together with
`complex_projectivization_basisCompatible_unique_topology`, this gives the full uniqueness
conclusion of the problem in the canonical owner `IsManifold.maximalAtlas`. -/
theorem complex_projectivization_basisCompatible_same_smooth_structure
    (t : TopologicalSpace (ℙ ℂ V))
    (c : let _ : TopologicalSpace (ℙ ℂ V) := t
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s : let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs : Projectivization.BasisCompatible m V t c s)
    (c' : let _ : TopologicalSpace (ℙ ℂ V) := t
      ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V))
    (s' : let _ : TopologicalSpace (ℙ ℂ V) := t
      let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
      IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V))
    (hs' : Projectivization.BasisCompatible m V t c' s') :
    (let _ : TopologicalSpace (ℙ ℂ V) := t
     let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
     let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
     IsManifold.maximalAtlas Icp ∞ (ℙ ℂ V)) =
      (let _ : TopologicalSpace (ℙ ℂ V) := t
       let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
       let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s'
       IsManifold.maximalAtlas Icp ∞ (ℙ ℂ V)) := by
  have hc : IsSmoothAtlas Icp c.atlas := by
    let _ : TopologicalSpace (ℙ ℂ V) := t
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s
    infer_instance
  have hc' : IsSmoothAtlas Icp c'.atlas := by
    let _ : TopologicalSpace (ℙ ℂ V) := t
    let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
    let _ : IsManifold Icp (⊤ : ℕ∞ω) (ℙ ℂ V) := s'
    infer_instance
  have hunion : IsSmoothAtlas Icp (c.atlas ∪ c'.atlas) :=
    complex_projectivization_basisCompatible_union_isSmoothAtlas t c s hs c' s' hs'
  have hgroupoid :
      (let _ : TopologicalSpace (ℙ ℂ V) := t
       let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c
       (contDiffGroupoid (∞ : ℕ∞ω) Icp).maximalAtlas (ℙ ℂ V)) =
        (let _ : TopologicalSpace (ℙ ℂ V) := t
         let _ : ChartedSpace (EuclideanSpace ℂ (Fin m)) (ℙ ℂ V) := c'
         (contDiffGroupoid (∞ : ℕ∞ω) Icp).maximalAtlas (ℙ ℂ V)) :=
    (same_smooth_structure_iff_union_is_smooth_atlas c c' hc hc').2 hunion
  simpa [IsManifold.maximalAtlas] using hgroupoid
