import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uK uE uE' uH uH' uM uN

namespace Manifold

section

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

/-- Exercise 4.3 (1): the first projection from a product manifold is a smooth submersion. -/
-- Proof sketch: the first projection is smooth, and its manifold derivative is the tangent-space
-- projection `ContinuousLinearMap.fst`, hence surjective at every point.
theorem prod_fst_isSmoothSubmersion
    : IsSmoothSubmersion (I.prod J) I (Prod.fst : M × N → M) := by
  refine ⟨contMDiff_fst, ?_⟩
  intro x
  rw [mfderiv_fst]
  intro v
  exact ⟨(v, 0), rfl⟩

/-- Exercise 4.3 (2): the second projection from a product manifold is a smooth submersion. -/
-- Proof sketch: the second projection is smooth, and its manifold derivative is the tangent-space
-- projection `ContinuousLinearMap.snd`, hence surjective at every point.
theorem prod_snd_isSmoothSubmersion
    : IsSmoothSubmersion (I.prod J) J (Prod.snd : M × N → N) := by
  refine ⟨contMDiff_snd, ?_⟩
  intro x
  rw [mfderiv_snd]
  intro v
  exact ⟨(0, v), rfl⟩

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Helper for Exercise 4.3: postcomposing a maximal-atlas chart with a smooth self-chart change of
the model space stays in the same maximal atlas. -/
lemma trans_mem_maximalAtlas_of_mem_groupoid_infty
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N)
    {chi : OpenPartialHomeomorph H' H'}
    (hchi : chi ∈ contDiffGroupoid ∞ J) :
    e.trans chi ∈ IsManifold.maximalAtlas J ∞ N := by
  -- Membership in the maximal atlas is checked by compatibility with every original atlas chart.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas J ∞ N := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid ∞ J := by
    -- The old transition from `e` to `e'` is already smooth.
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid ∞ J := by
    -- The reverse transition is smooth for the same reason.
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- On the left, factor the new transition through `chi.symm`.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ J).trans ((contDiffGroupoid ∞ J).symm hchi) hleft
  · -- On the right, append the smooth model-space chart change `chi`.
    have hright' : (e'.symm.trans e).trans chi ∈ contDiffGroupoid ∞ J := by
      exact (contDiffGroupoid ∞ J).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Exercise 4.3: a model-space open partial homeomorphism belongs to the
`C^∞` structure groupoid once its whole source is locally covered by smooth structomorph charts. -/
theorem mem_contDiffGroupoid_of_local_structomorphOn_source
    {f : OpenPartialHomeomorph H' H'}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ J).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ J := by
  refine (contDiffGroupoid ∞ J).locality ?_
  intro x hx
  -- Read the local structomorphism witness in the model chart `chartAt H' x = refl`.
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid ∞ J).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ J) (f := f)] at hfx_prop'
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
  exact (contDiffGroupoid ∞ J).mem_of_eqOnSource he hEqOnSource

/-- Helper for Exercise 4.3: forgetting the inverse of a `J`-partial diffeomorphism of the model
space produces an element of the `C^∞` structure groupoid. -/
theorem model_partial_diffeomorph_mem_contDiffGroupoid
    {Φ : PartialDiffeomorph J J H' H' ∞} :
    Φ.toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ J := by
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ J).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is smooth on its source and inverse-target by definition.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := J) (n := (∞ : ℕ∞ω)) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  -- Promote the local structomorphism witness on the source to actual groupoid membership.
  exact mem_contDiffGroupoid_of_local_structomorphOn_source hΦ

/-- Helper for Exercise 4.3: in the naive product chart, the right slice `p ↦ (p, q)` becomes the
affine slice with fixed second coordinate. -/
lemma prod_mk_right_raw_in_product_chart
    (q : N) (x : M) :
    Set.EqOn
      ((((chartAt H x).prod (chartAt H' q)).extend (I.prod J)) ∘
        (fun p : M ↦ (p, q)) ∘
        ((chartAt H x).extend I).symm)
      (fun u : E ↦ (u, (chartAt H' q).extend J q))
      ((chartAt H x).extend I).target := by
  intro y hy
  -- The source chart inverse lands back in the source, so the first coordinate cancels.
  have hright : ((chartAt H x).extend I) (((chartAt H x).extend I).symm y) = y :=
    ((chartAt H x).extend I).right_inv hy
  simpa [Function.comp, OpenPartialHomeomorph.extend_prod, hright]

/-- Helper for Exercise 4.3: in the naive product chart, the left slice `q ↦ (p, q)` becomes the
affine slice with fixed first coordinate. -/
lemma prod_mk_left_raw_in_product_chart
    (p : M) (y : N) :
    Set.EqOn
      (((((chartAt H p).prod (chartAt H' y)).extend (I.prod J)) ∘
          (fun q : N ↦ (p, q)) ∘
          ((chartAt H' y).extend J).symm))
      (fun v : E' ↦ ((chartAt H p).extend I p, v))
      ((chartAt H' y).extend J).target := by
  intro z hz
  -- The target-side chart inverse cancels on its target, leaving the fixed first coordinate.
  have hright : ((chartAt H' y).extend J) (((chartAt H' y).extend J).symm z) = z :=
    ((chartAt H' y).extend J).right_inv hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_prod, hright]

/-- Helper for Exercise 4.3: if the fixed point `q` admits a maximal-atlas chart whose extended
coordinate is `0`, then the right slice `p ↦ (p, q)` is an immersion with complement `E'`. -/
lemma prod_mk_right_isImmersionOfComplement_of_zero_chart
    (q : N) (codChartq : OpenPartialHomeomorph N H')
    (hq : q ∈ codChartq.source)
    (hcodChartq : codChartq ∈ IsManifold.maximalAtlas J ∞ N)
    (hzero : (codChartq.extend J) q = 0) :
    IsImmersionOfComplement E' I (I.prod J) ∞ (fun p : M ↦ (p, q)) := by
  intro x
  let codChart : OpenPartialHomeomorph (M × N) (ModelProd H H') := (chartAt H x).prod codChartq
  -- Use the preferred chart on the moving factor and the zero-centered chart on the fixed factor.
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (f := fun p : M ↦ (p, q)) (x := x)
    (by simpa using (continuousAt_id.prodMk (continuousAt_const : ContinuousAt (fun _ : M ↦ q) x)))
    (ContinuousLinearEquiv.refl 𝕜 (E × E'))
    (chartAt H x)
    codChart
    (mem_chart_source H x) ⟨mem_chart_source H x, hq⟩
    (IsManifold.chart_mem_maximalAtlas x)
    (by
      simpa [codChart] using
        IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas x) hcodChartq) ?_
  · intro y hy
    -- In these product charts, the slice has the normal form `u ↦ (u, 0)`.
    have hright : ((chartAt H x).extend I) (((chartAt H x).extend I).symm y) = y :=
      ((chartAt H x).extend I).right_inv hy
    simpa [codChart, OpenPartialHomeomorph.extend_prod, hright, hzero]
      using And.intro hright hzero

/-- Helper for Exercise 4.3: if the fixed point `p` admits a maximal-atlas chart whose extended
coordinate is `0`, then the left slice `q ↦ (p, q)` is an immersion with complement `E`. -/
lemma prod_mk_left_isImmersionOfComplement_of_zero_chart
    (p : M) (codChartp : OpenPartialHomeomorph M H)
    (hp : p ∈ codChartp.source)
    (hcodChartp : codChartp ∈ IsManifold.maximalAtlas I ∞ M)
    (hzero : (codChartp.extend I) p = 0) :
    IsImmersionOfComplement E J (I.prod J) ∞ (fun q : N ↦ (p, q)) := by
  intro y
  let codChart : OpenPartialHomeomorph (M × N) (ModelProd H H') := codChartp.prod (chartAt H' y)
  -- Use the zero-centered chart on the fixed factor and the preferred chart on the moving factor.
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (f := fun q : N ↦ (p, q)) (x := y)
    (by simpa using
      ((continuousAt_const : ContinuousAt (fun _ : N ↦ p) y).prodMk continuousAt_id))
    (ContinuousLinearEquiv.prodComm 𝕜 E' E)
    (chartAt H' y)
    codChart
    (mem_chart_source H' y) ⟨hp, mem_chart_source H' y⟩
    (IsManifold.chart_mem_maximalAtlas y)
    (by
      simpa [codChart] using
        IsManifold.mem_maximalAtlas_prod hcodChartp (IsManifold.chart_mem_maximalAtlas y)) ?_
  · intro z hz
    -- The product chart expression is `v ↦ (0, v)`, then `prodComm` rewrites it as `(v, 0)`.
    have hright : ((chartAt H' y).extend J) (((chartAt H' y).extend J).symm z) = z :=
      ((chartAt H' y).extend J).right_inv hz
    simpa [codChart, OpenPartialHomeomorph.extend_prod, hright, hzero]
      using And.intro hzero hright

/-- Exercise 4.3 (3), in the chart-normalized form used by mathlib's general
`ModelWithCorners` API: if the fixed point `q` has a maximal-atlas chart whose extended
coordinate is `0`, then the left slice map `p ↦ (p, q)` is a smooth immersion. This is the
textbook product-slice claim after choosing product coordinates centered at the fixed factor. -/
theorem prod_mk_right_isImmersion
    (q : N) (codChartq : OpenPartialHomeomorph N H')
    (hq : q ∈ codChartq.source)
    (hcodChartq : codChartq ∈ IsManifold.maximalAtlas J ∞ N)
    (hzero : (codChartq.extend J) q = 0) :
    IsImmersion I (I.prod J) ∞ (fun p : M ↦ (p, q)) := by
  exact (prod_mk_right_isImmersionOfComplement_of_zero_chart
    (q := q) (codChartq := codChartq) hq hcodChartq hzero).isImmersion

/-- Exercise 4.3 (4), in the chart-normalized form used by mathlib's general
`ModelWithCorners` API: if the fixed point `p` has a maximal-atlas chart whose extended
coordinate is `0`, then the right slice map `q ↦ (p, q)` is a smooth immersion. -/
theorem prod_mk_left_isImmersion
    (p : M) (codChartp : OpenPartialHomeomorph M H)
    (hp : p ∈ codChartp.source)
    (hcodChartp : codChartp ∈ IsManifold.maximalAtlas I ∞ M)
    (hzero : (codChartp.extend I) p = 0) :
    IsImmersion J (I.prod J) ∞ (fun q : N ↦ (p, q)) := by
  exact (prod_mk_left_isImmersionOfComplement_of_zero_chart
    (p := p) (codChartp := codChartp) hp hcodChartp hzero).isImmersion

end

end Manifold
