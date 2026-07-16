import DifferentialForms_Cartan_1970.cartan.VI.section25.«0016_Theorem_VI_4_extra_13»
import DifferentialForms_Cartan_1970.cartan.VI.section23.«0001_Theorem_1»

universe u

open scoped Complex.UnitDisc Manifold

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment, so these
-- statements were aligned by direct inspection of the chapter owners
-- `BiholomorphicToRiemannSphere` and `Complex.UnitDisc` from `0016_Theorem_VI_4_extra_13`
-- together with mathlib's complex-manifold API.

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Helper for Corollary VI.4-extra-14: composing with the subtype inclusion into an open subset
does not change `C¹` regularity. -/
lemma contMDiff_subtypeVal_comp_iff {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {U : TopologicalSpace.Opens Y} {f : Z → U} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ f) ↔ ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f := by
  -- This is the finite-order version of the standard subtype-target smoothness bridge.
  simp only [ContMDiff, ContMDiffAt, ContMDiffWithinAt]
  constructor
  · intro h x
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℂ) 𝓘(ℂ) 1) (f := f) (s := Set.univ) (x := x)).mp
        (h x)
  · intro h x
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℂ) 𝓘(ℂ) 1) (f := f) (s := Set.univ) (x := x)).mpr
        (h x)

/-- Helper for Corollary VI.4-extra-14: a `C¹` open partial homeomorphism onto all of the target
manifold induces a `C¹` equivalence from its open source subtype to the whole target. -/
lemma open_partial_homeomorph.to_complex_manifold_equiv_of_target_eq_univ
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target)
    (ht : f.target = Set.univ) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) := by
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let g : Y → U := fun y ↦
    ⟨f.symm y, by
      have hy : y ∈ f.target := by simpa [ht]
      simpa using f.map_target hy⟩
  let h : U ≃ₜ Y :=
    (f.toHomeomorphSourceTarget.trans (Homeomorph.setCongr ht)).trans (Homeomorph.Set.univ Y)
  have h_to' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x) := by
    -- Restrict the forward branch to the source subtype and then use the global chart-free API.
    have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → X) :=
      contMDiff_subtype_val
    have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x.1) Set.univ := by
      simpa using h_to.comp hsub.contMDiffOn (by
        intro x hx
        exact x.2)
    simpa [contMDiffOn_univ, U, Function.comp] using hcomp
  have h_inv' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 g := by
    -- The inverse branch is smooth because its ambient composition with the subtype valuation is.
    have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ g) := by
      have hglobal : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm Set.univ := by
        simpa [ht] using h_inv
      simpa [contMDiffOn_univ, g, Function.comp] using hglobal
    exact (contMDiff_subtypeVal_comp_iff (Z := Y) (Y := X) (U := U) (f := g)).mp hambient
  refine ⟨{ toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · -- The underlying forward map is exactly the restricted forward branch.
    simpa [h, U, Function.comp]
      using h_to'
  · -- The inverse homeomorphism is the subtype-valued inverse branch defined above.
    simpa [h, g, U, ht, Function.comp]
      using h_inv'

/-- Helper for Corollary VI.4-extra-14: the affine chart identifies the punctured Riemann sphere
coming from `∞` with the complex plane. -/
lemma punctured_riemann_sphere_equiv_complex_plane
    (e : X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) :
    ∃ (p : X) (U : TopologicalSpace.Opens X),
      (↑U : Set X) = (Set.singleton p)ᶜ ∧ Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  let f : OpenPartialHomeomorph X ℂ :=
    e.toHomeomorph.toOpenPartialHomeomorph.trans RiemannSphere.affineOpenPartialHomeomorph
  let p : X := e.symm OnePoint.infty
  have h_e_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 e Set.univ := by
    simpa using e.contMDiff.contMDiffOn
  have h_e_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 e.symm Set.univ := by
    simpa using e.symm.contMDiff.contMDiffOn
  have h_affine_to :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph
        RiemannSphere.affineOpenPartialHomeomorph.source := by
    -- The affine chart is literally the preferred chart at any finite point of the sphere.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe, Function.comp]
      using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_affine_inv :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph.symm
        RiemannSphere.affineOpenPartialHomeomorph.target := by
    -- The inverse affine chart is the preferred chart inverse at the same finite point.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe_symm, Function.comp]
      using contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source := by
    -- Compose the global uniformization map with the affine chart on the sphere.
    simpa [f, OpenPartialHomeomorph.trans_apply, Function.comp_def,
      OpenPartialHomeomorph.trans_source, Set.preimage_inter, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm]
      using h_affine_to.comp' h_e_to
  have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target := by
    -- The inverse composition is smooth for the same reason.
    simpa [f, OpenPartialHomeomorph.trans_apply, Function.comp_def,
      OpenPartialHomeomorph.trans_target, Set.preimage_inter, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm]
      using h_e_inv.comp' h_affine_inv
  have htarget : f.target = Set.univ := by
    simp [f, RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart,
      OpenPartialHomeomorph.trans_target]
  refine ⟨p, ⟨f.source, f.open_source⟩, ?_, ?_⟩
  · -- The source is exactly the complement of the point mapping to `∞`.
    ext x
    change x ∈ f.source ↔ x ∈ (Set.singleton p)ᶜ
    have hxp : e x = OnePoint.infty ↔ x = p := by
      constructor
      · intro hx
        calc
          x = e.symm (e x) := by simpa using e.symm_apply_apply x
          _ = p := by simpa [p, hx]
      · intro hx
        calc
          e x = e p := by simpa [hx]
          _ = OnePoint.infty := by simpa [p] using e.apply_symm_apply OnePoint.infty
    have hsource :
        x ∈ f.source ↔ e x ∈ RiemannSphere.affineOpenPartialHomeomorph.source := by
      simp [f, OpenPartialHomeomorph.trans_source]
    rw [hsource]
    change e x ∈ RiemannSphere.affineOpenPartialHomeomorph.source ↔ x ≠ p
    simpa [RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart, hxp]
  · -- Package the smooth open partial homeomorphism as the required manifold equivalence.
    simpa using open_partial_homeomorph.to_complex_manifold_equiv_of_target_eq_univ
      (f := f) h_to h_inv htarget

/-- Helper for Corollary VI.4-extra-14: the unit-disc inclusion is a `C¹` open partial
homeomorphism into the complex plane. -/
lemma unit_disc_inclusion_mdifferentiable :
    (Complex.UnitDisc.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : 𝔻 → ℂ)).MDifferentiable
      𝓘(ℂ) 𝓘(ℂ) := by
  let ι : OpenPartialHomeomorph 𝔻 ℂ :=
    Complex.UnitDisc.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : 𝔻 → ℂ)
  have h_to : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 ((↑) : 𝔻 → ℂ) := by
    simpa using
      (contMDiff_isOpenEmbedding (I := 𝓘(ℂ)) (h := Complex.UnitDisc.isOpenEmbedding_coe)
        (n := 1) (e := ((↑) : 𝔻 → ℂ)))
  have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 ι.symm ι.target := by
    simpa [ι] using
      (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℂ)) (h := Complex.UnitDisc.isOpenEmbedding_coe)
        (n := 1) (e := ((↑) : 𝔻 → ℂ)))
  refine ⟨?_, ?_⟩
  · simpa [ι] using (h_to.mdifferentiable one_ne_zero).mdifferentiableOn
  · simpa [ι] using h_inv.mdifferentiableOn one_ne_zero

/-- Helper for Corollary VI.4-extra-14: any `C¹` equivalence from the plane to the unit disc would
induce the forbidden biholomorphic isomorphism from Theorem 1. -/
lemma complex_plane_not_manifold_equiv_unit_disc :
    ¬ Nonempty (ℂ ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻) := by
  rintro ⟨e⟩
  let ι : OpenPartialHomeomorph 𝔻 ℂ :=
    Complex.UnitDisc.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : 𝔻 → ℂ)
  let f : OpenPartialHomeomorph ℂ ℂ :=
    e.toHomeomorph.toOpenPartialHomeomorph.trans ι
  have hdiff : f.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    -- Compose the global `C¹` equivalence with the canonical inclusion of the disc into `ℂ`.
    exact OpenPartialHomeomorph.MDifferentiable.trans
      (e.toOpenPartialHomeomorph_mdifferentiable one_ne_zero)
      unit_disc_inclusion_mdifferentiable
  have hsource : f.source = Set.univ := by
    simp [f, ι, OpenPartialHomeomorph.trans_source]
  have hιtarget : ι.target = Metric.ball (0 : ℂ) 1 := by
    ext z
    have hrange : z ∈ Set.range ((↑) : 𝔻 → ℂ) ↔ z ∈ Metric.ball (0 : ℂ) 1 := by
      constructor
      · rintro ⟨w, rfl⟩
        simpa using Complex.UnitDisc.norm_lt_one w
      · intro hz
        exact ⟨⟨z, by simpa [Complex.UnitDisc] using hz⟩, rfl⟩
    simpa [ι, Complex.UnitDisc] using hrange
  have htarget : f.target = Metric.ball (0 : ℂ) 1 := by
    calc
      f.target = ι.target := by
        simp [f, OpenPartialHomeomorph.trans_target]
      _ = Metric.ball (0 : ℂ) 1 := hιtarget
  have hanalytic_to : AnalyticOnNhd ℂ f Set.univ := by
    -- On open subsets of `ℂ`, complex differentiability is equivalent to analyticity.
    simpa [hsource] using hdiff.1.differentiableOn.analyticOnNhd f.open_source
  have hanalytic_inv : AnalyticOnNhd ℂ f.symm (Metric.ball (0 : ℂ) 1) := by
    -- The inverse branch is analytic on the open ball target.
    simpa [htarget] using hdiff.2.differentiableOn.analyticOnNhd f.open_target
  have hprop : OpenPartialHomeomorph.IsHolomorphicIsoOn f Set.univ (Metric.ball (0 : ℂ) 1) := by
    exact ⟨hsource, htarget, hanalytic_to, hanalytic_inv⟩
  let hIso : HolomorphicIsomorph Set.univ (Metric.ball (0 : ℂ) 1) := ⟨f, hprop⟩
  exact complex_plane_not_biholomorphic_to_open_unit_disc ⟨hIso⟩

/-- Helper for Corollary VI.4-extra-14: the unit disc is noncompact. -/
lemma complex_unit_disc_noncompact : NoncompactSpace 𝔻 := by
  refine ⟨?_⟩
  intro hcompact
  haveI : CompactSpace 𝔻 := isCompact_univ_iff.mp hcompact
  haveI : CompactSpace ℂ := by
    let h : ℂ ≃ₜ 𝔻 := by
      simpa [Complex.UnitDisc] using (Homeomorph.unitBall (E := ℂ))
    exact h.symm.compactSpace
  exact (noncompact_univ ℂ) isCompact_univ

/-- Corollary VI.4-extra-14 (1): affine-chart form of the compact case. A compact
simply-connected Hausdorff complex manifold is the Riemann sphere, so there is a point whose
complement, as an open submanifold, is biholomorphic to `ℂ`. -/
theorem exists_punctured_biholomorph_complex_plane_of_compact_simplyConnected
    [SimplyConnectedSpace X] [CompactSpace X] :
    ∃ (p : X) (U : TopologicalSpace.Opens X),
      (↑U : Set X) = (Set.singleton p)ᶜ ∧ Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) :=
    by
  -- The source proof first classifies the manifold, then only the sphere branch survives
  -- compactness, and the affine chart identifies the punctured sphere with `ℂ`.
  rcases simply_connected_complex_manifold_uniformization
      (X := X) with hsphere | hplane | hdisc
  · rcases hsphere with ⟨e⟩
    exact punctured_riemann_sphere_equiv_complex_plane e
  · rcases hplane with ⟨e⟩
    -- A compact manifold cannot be equivalent to the noncompact plane.
    haveI : CompactSpace ℂ := e.toHomeomorph.compactSpace
    exact (noncompact_univ ℂ) isCompact_univ |> False.elim
  · rcases hdisc with ⟨e⟩
    -- A compact manifold cannot be equivalent to the noncompact unit disc.
    haveI : CompactSpace 𝔻 := e.toHomeomorph.compactSpace
    have hnc : NoncompactSpace 𝔻 := complex_unit_disc_noncompact
    exact hnc.noncompact_univ isCompact_univ |> False.elim

/-- Corollary VI.4-extra-14 (2): a noncompact simply-connected Hausdorff complex manifold is
biholomorphic to `ℂ` or to the open unit disc. -/
theorem nonempty_biholomorph_complex_plane_or_unit_disc_of_noncompact_simplyConnected
    [SimplyConnectedSpace X] [NoncompactSpace X] :
    Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻) := by
  -- The sphere case is excluded by noncompactness, so uniformization leaves only `ℂ` or `𝔻`.
  rcases simply_connected_complex_manifold_uniformization
      (X := X) with hsphere | hplane | hdisc
  · rcases hsphere with ⟨e⟩
    haveI : CompactSpace X := e.toHomeomorph.symm.compactSpace
    exact (noncompact_univ X) isCompact_univ |> False.elim
  · exact Or.inl hplane
  · exact Or.inr hdisc

/-- Corollary VI.4-extra-14 (3): the plane and the open unit disc cases are mutually
exclusive. -/
theorem not_both_biholomorph_complex_plane_and_unit_disc :
    ¬ (Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∧
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻)) := by
  rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
  -- Compose the two identifications to obtain a forbidden equivalence `ℂ ≃ₘ^1 𝔻`.
  exact complex_plane_not_manifold_equiv_unit_disc
    ⟨e₁.symm.trans e₂⟩
