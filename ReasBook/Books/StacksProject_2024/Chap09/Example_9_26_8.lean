import StacksProject_2024.Chap09.Example_9_3_6
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology
open CategoryTheory AlgebraicGeometry
open Set

noncomputable section

universe u v

section

set_option autoImplicit false

/-- A compact connected Riemann surface, modeled as a Hausdorff second-countable complex
one-manifold. The nontriviality needed for the category of nonconstant holomorphic maps is a
derived fact, not part of the object data. -/
structure CompactRiemannSurface where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) 1 carrier]
  [compactSpace : CompactSpace carrier]
  [connectedSpace : ConnectedSpace carrier]

attribute [instance] CompactRiemannSurface.topologicalSpace CompactRiemannSurface.t2Space
  CompactRiemannSurface.secondCountableTopology CompactRiemannSurface.chartedSpace
  CompactRiemannSurface.isManifold CompactRiemannSurface.compactSpace
  CompactRiemannSurface.connectedSpace

instance : CoeSort CompactRiemannSurface (Type u) := ⟨CompactRiemannSurface.carrier⟩

/-- Helper for Example 9.26.8: a compact Riemann surface has two distinct points. -/
lemma CompactRiemannSurface.exists_pair_ne (X : CompactRiemannSurface.{u}) :
    ∃ x y : X, x ≠ y := by
  letI : Nonempty X := inferInstance
  obtain ⟨x⟩ := ‹Nonempty X›
  let z : ℂ := extChartAt 𝓘(ℂ) x x
  -- Work in a chart around `x` and choose a second complex point in the punctured target.
  have hz_mem : z ∈ (extChartAt 𝓘(ℂ) x).target := by
    simpa [z] using mem_extChartAt_target (I := 𝓘(ℂ)) x
  have htarget : (extChartAt 𝓘(ℂ) x).target ∈ nhds z :=
    (isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hz_mem
  have hpunct : (nhdsWithin z ({z}ᶜ : Set ℂ)).NeBot := inferInstance
  have hdiff : ((extChartAt 𝓘(ℂ) x).target \ {z} : Set ℂ).Nonempty := by
    refine hpunct.nonempty_of_mem ?_
    simpa using diff_mem_nhdsWithin_compl htarget ({z} : Set ℂ)
  rcases hdiff with ⟨w, hw_target, hw_ne⟩
  refine ⟨x, (extChartAt 𝓘(ℂ) x).symm w, ?_⟩
  intro h_eq
  -- Apply the chart to the supposed equality to contradict `w ≠ z`.
  have hchart :
      extChartAt 𝓘(ℂ) x x = extChartAt 𝓘(ℂ) x ((extChartAt 𝓘(ℂ) x).symm w) :=
    congrArg (extChartAt 𝓘(ℂ) x) h_eq
  have hw_eq : z = w := by
    calc
      z = extChartAt 𝓘(ℂ) x x := by
        rfl
      _ = extChartAt 𝓘(ℂ) x ((extChartAt 𝓘(ℂ) x).symm w) := hchart
      _ = w := PartialEquiv.right_inv (extChartAt 𝓘(ℂ) x) hw_target
  exact hw_ne hw_eq.symm

instance (X : CompactRiemannSurface.{u}) : Nontrivial X := by
  -- The chart argument above supplies the two distinct points needed for `Nontrivial`.
  obtain ⟨x, y, hxy⟩ := CompactRiemannSurface.exists_pair_ne X
  exact ⟨x, y, hxy⟩

/-- A holomorphic map of compact Riemann surfaces, formalized as a complex
manifold-differentiable map. -/
structure CompactRiemannSurfaceHom (X Y : CompactRiemannSurface.{u}) where
  toFun : X → Y
  mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun

instance (X Y : CompactRiemannSurface.{u}) : FunLike (CompactRiemannSurfaceHom X Y) X Y where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

@[ext]
lemma CompactRiemannSurfaceHom.ext {X Y : CompactRiemannSurface.{u}}
    {f g : CompactRiemannSurfaceHom X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

instance : Category CompactRiemannSurface where
  Hom X Y := CompactRiemannSurfaceHom X Y
  id X :=
    { toFun := id
      mdifferentiable := by
        simpa using
          (mdifferentiable_id : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X ↦ x)) }
  comp f g :=
    { toFun := g ∘ f
      mdifferentiable := g.mdifferentiable.comp f.mdifferentiable }
  id_comp f := by
    ext x
    rfl
  comp_id f := by
    ext x
    rfl
  assoc f g h := by
    ext x
    rfl

/-- A holomorphic map of compact Riemann surfaces is nonconstant if it separates two points. -/
def CompactRiemannSurfaceHom.IsNonconstant {X Y : CompactRiemannSurface.{u}}
    (f : CompactRiemannSurfaceHom X Y) : Prop :=
  ∃ x y, f x ≠ f y

/-- The morphism property cutting out nonconstant holomorphic maps of compact Riemann surfaces. -/
def CompactRiemannSurface.nonconstantHom :
    MorphismProperty CompactRiemannSurface :=
  fun _ _ f ↦ f.IsNonconstant

/-- Helper for Example 9.26.8: the chart expression of a holomorphic map is analytic at the chart
base point. -/
lemma CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X) :
    AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) := by
  let s : Set X := (extChartAt 𝓘(ℂ) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source
  -- Work on the chart neighborhood where both the source chart and the target chart of `f x`
  -- are valid, so the manifold differentiability statement becomes ordinary differentiability.
  have hs_mem : s ∈ 𝓝 x := by
    refine Filter.inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x) ?_
    exact (f.mdifferentiable x).continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))
  have hs_subset : s ⊆ (extChartAt 𝓘(ℂ) x).source := Set.inter_subset_left
  have hs_maps : Set.MapsTo f s (extChartAt 𝓘(ℂ) (f x)).source := by
    intro y hy
    exact hy.2
  have hmdiffOn : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f s := by
    intro y hy
    exact (f.mdifferentiable y).mdifferentiableWithinAt
  have hdiffOn :
      DifferentiableOn ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x '' s) := by
    exact
      (mdifferentiableOn_iff_of_subset_source' (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (x := x) (y := f x) (s := s) (f := f) hs_subset hs_maps).1 hmdiffOn
  have himage_mem : extChartAt 𝓘(ℂ) x '' s ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    exact extChartAt_image_nhds_mem_nhds_of_boundaryless (I := 𝓘(ℂ)) hs_mem
  -- Complex differentiability on a chart neighborhood upgrades to analyticity at the base point.
  exact hdiffOn.analyticAt himage_mem

/-- Helper for Example 9.26.8: once a holomorphic map is known to be open, compactness and
connectedness force surjectivity. -/
lemma CompactRiemannSurfaceHom.surjective_of_isOpenMap {X Y : CompactRiemannSurface.{u}}
    (f : CompactRiemannSurfaceHom X Y) (hf_open : IsOpenMap f.toFun) :
    Function.Surjective f := by
  -- Compactness of the source makes the range closed in the Hausdorff target.
  have hcont : Continuous f := f.mdifferentiable.continuous
  have hclosed : IsClosed (Set.range f) := by
    have hclosedMap : IsClosedMap f := hcont.isClosedMap
    simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ
  -- Openness gives the complementary half of the clopen range argument.
  have hopen : IsOpen (Set.range f) := hf_open.isOpen_range
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  letI : Nonempty X := inferInstance
  have hnonempty : (Set.range f).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨f x, ⟨x, rfl⟩⟩
  -- Connectedness of the target rules out a nonempty proper clopen subset.
  have hconnected :=
    (connectedSpace_iff_clopen (α := Y)).1 (inferInstance : ConnectedSpace Y)
  have hrange : Set.range f = Set.univ := by
    exact (hconnected.2 (Set.range f) hclopen).resolve_left <| by
      intro hempty
      exact hnonempty.ne_empty hempty
  exact Set.range_eq_univ.mp hrange

/-- Helper for Example 9.26.8: surjectivity of the first map lets one pull back nonconstant
witnesses through composition. -/
lemma CompactRiemannSurfaceHom.nonconstantCompositeWitnesses
    {X Y Z : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (g : CompactRiemannSurfaceHom Y Z) (hf : Function.Surjective f) (hg : g.IsNonconstant) :
    ∃ x y : X, g (f x) ≠ g (f y) := by
  -- Pull the distinct witness pair for `g` back along the surjective `f`.
  rcases hg with ⟨y₁, y₂, hy⟩
  rcases hf y₁ with ⟨x₁, rfl⟩
  rcases hf y₂ with ⟨x₂, rfl⟩
  exact ⟨x₁, x₂, hy⟩

/-- Helper for Example 9.26.8: a complex-analytic function that is constant on a nonempty open
subset of a preconnected domain is constant on the whole domain. -/
lemma analytic_eq_const_of_eqOn_nonempty_open {V W : Set ℂ} {g : ℂ → ℂ} {c : ℂ}
    (hg : AnalyticOnNhd ℂ g V) (hV : IsPreconnected V) (hWV : W ⊆ V) (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) (hW_const : Set.EqOn g (fun _ ↦ c) W) :
    Set.EqOn g (fun _ ↦ c) V := by
  rcases hW_nonempty with ⟨z₀, hz₀W⟩
  have hz₀V : z₀ ∈ V := hWV hz₀W
  -- Use the open patch to upgrade pointwise constancy near `z₀` to eventual equality.
  have hEventually : g =ᶠ[𝓝 z₀] fun _ ↦ c := by
    filter_upwards [hW_open.mem_nhds hz₀W] with z hz
    exact hW_const hz
  exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hV hz₀V hEventually

/-- Helper for Example 9.26.8: near the base chart point, the chart representative of a
holomorphic map is defined on the actual source/target validity domain. -/
lemma CompactRiemannSurfaceHom.chartValidity_eventuallyEq
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X) :
    (Set.univ : Set ℂ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ) x x)]
      ((extChartAt 𝓘(ℂ) x).target ∩
        (extChartAt 𝓘(ℂ) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source) : Set ℂ) := by
  -- Normalize the ambient neighborhood to the exact chart-validity set from the ext-chart API.
  simpa using
    (ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
      (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (s := Set.univ) (f := f) (x := x)
      (f.mdifferentiable x).continuousWithinAt)

/-- Helper for Example 9.26.8: if the chart representative of `f` is eventually constant at `x`,
then `f` is constant on an open neighborhood of `x`. -/
lemma CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X)
    (hconst :
      ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ) x x),
        writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f z = extChartAt 𝓘(ℂ) (f x) (f x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.EqOn f (fun _ ↦ f x) U := by
  let validity : Set ℂ :=
    (extChartAt 𝓘(ℂ) x).target ∩
      (extChartAt 𝓘(ℂ) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source)
  have hvalid : validity ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    have hvalid' : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ) x x), z ∈ validity := by
      filter_upwards [CompactRiemannSurfaceHom.chartValidity_eventuallyEq f x] with z hz
      exact hz.mp trivial
    exact hvalid'
  let eqSet : Set ℂ :=
    {z | writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f z = extChartAt 𝓘(ℂ) (f x) (f x)}
  have hmem : validity ∩ eqSet ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    exact Filter.inter_mem hvalid (by simpa [eqSet] using hconst)
  rcases mem_nhds_iff.mp hmem with ⟨s, hs_sub, hs_open, hx_mem_s⟩
  let U : Set X := (chartAt ℂ x).source ∩ extChartAt 𝓘(ℂ) x ⁻¹' s
  refine ⟨U, ?_, ?_, ?_⟩
  · -- Pull the chart-open neighborhood back to the manifold.
    simpa [U] using isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x hs_open
  · -- The chart center belongs to the chosen neighborhood.
    exact ⟨mem_chart_source _ x, hx_mem_s⟩
  · intro y hy
    have hy_s : extChartAt 𝓘(ℂ) x y ∈ s := hy.2
    have hy_mem : extChartAt 𝓘(ℂ) x y ∈ validity ∩ eqSet := hs_sub hy_s
    have hy_targetSource :
        f ((extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y)) ∈
          (extChartAt 𝓘(ℂ) (f x)).source := hy_mem.1.2
    have hy_eqChart :
        writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f (extChartAt 𝓘(ℂ) x y) =
          extChartAt 𝓘(ℂ) (f x) (f x) := hy_mem.2
    have hy_source : y ∈ (extChartAt 𝓘(ℂ) x).source := by
      simpa [extChartAt_source] using hy.1
    have hy_symm :
        (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) = y :=
      PartialEquiv.left_inv (extChartAt 𝓘(ℂ) x) hy_source
    have hy_chart_symm :
        (chartAt ℂ x).symm ((chartAt ℂ x) y) = y := by
      simpa using hy_symm
    have hy_fx_source : f y ∈ (extChartAt 𝓘(ℂ) (f x)).source := by
      simpa [hy_chart_symm] using hy_targetSource
    have hchart_eq : extChartAt 𝓘(ℂ) (f x) (f y) = extChartAt 𝓘(ℂ) (f x) (f x) := by
      -- Rewrite the chart equality back to the actual target values.
      simpa [writtenInExtChartAt, Function.comp, hy_chart_symm] using hy_eqChart
    have hfy_eq : f y = f x := by
      have hfy_eq' := congrArg (fun z => (extChartAt 𝓘(ℂ) (f x)).symm z) hchart_eq
      calc
        f y = (extChartAt 𝓘(ℂ) (f x)).symm (extChartAt 𝓘(ℂ) (f x) (f y)) := by
          symm
          exact PartialEquiv.left_inv (extChartAt 𝓘(ℂ) (f x)) hy_fx_source
        _ = (extChartAt 𝓘(ℂ) (f x)).symm (extChartAt 𝓘(ℂ) (f x) (f x)) := hfy_eq'
        _ = f x := PartialEquiv.left_inv (extChartAt 𝓘(ℂ) (f x))
          (mem_extChartAt_source (I := 𝓘(ℂ)) (f x))
    simpa using hfy_eq

/-- Helper for Example 9.26.8: the local constancy locus of value `c` for `f`. -/
def CompactRiemannSurfaceHom.localConstancyLocus
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (c : Y) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.EqOn f (fun _ ↦ c) U}

/-- Helper for Example 9.26.8: a chart sends an open subset of its source to an open subset of the
model space. -/
lemma CompactRiemannSurface.isOpen_image_chartAt
    {X : CompactRiemannSurface.{u}} (x : X) {U : Set X} (hU : IsOpen U)
    (hU_source : U ⊆ (chartAt ℂ x).source) :
    IsOpen (chartAt ℂ x '' U) := by
  -- Use the local homeomorphism property of the chart pointwise on the image.
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro z ⟨y, hy, rfl⟩
  exact (chartAt ℂ x).image_mem_nhds (hU_source hy) (hU.mem_nhds hy)

/-- Helper for Example 9.26.8: the local constancy locus is stable under taking closure. -/
lemma CompactRiemannSurfaceHom.mem_localConstancyLocus_of_mem_closure
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) {c : Y} {x : X}
    (hx :
      x ∈ closure (CompactRiemannSurfaceHom.localConstancyLocus f c)) :
    x ∈ CompactRiemannSurfaceHom.localConstancyLocus f c := by
  let eX := extChartAt 𝓘(ℂ) x
  let eY := extChartAt 𝓘(ℂ) (f x)
  let z0 : ℂ := eX x
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  have hfiber_subset :
      CompactRiemannSurfaceHom.localConstancyLocus f c ⊆ f ⁻¹' ({c} : Set Y) := by
    intro y hy
    rcases hy with ⟨U, _, hyU, hUconst⟩
    simpa using hUconst hyU
  have hxFiber : x ∈ closure (f ⁻¹' ({c} : Set Y)) :=
    closure_mono hfiber_subset hx
  have hfx : f x = c := by
    -- First pin down the value at the closure point using continuity and the closed fiber.
    exact ContinuousWithinAt.eq_const_of_mem_closure
      (f.mdifferentiable.continuous.continuousAt.continuousWithinAt) hxFiber
      (by intro y hy; simpa using hy)
  have hanalytic := CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt f x
  obtain ⟨r, hr, hBallAnalytic⟩ := hanalytic.exists_ball_analyticOnNhd
  let chartBall : Set X := (chartAt ℂ x).source ∩ eX ⁻¹' (Metric.ball z0 r)
  have hchartBall_open : IsOpen chartBall := by
    -- Work inside one genuine chart ball around the closure point.
    simpa [chartBall, eX] using
      isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x Metric.isOpen_ball
  have hxChartBall : x ∈ chartBall := by
    refine ⟨mem_chart_source _ x, ?_⟩
    exact (show z0 ∈ Metric.ball z0 r from Metric.mem_ball_self hr)
  obtain ⟨y, hyChartBall, hyLocus⟩ :=
    (mem_closure_iff_nhds.mp hx) chartBall (hchartBall_open.mem_nhds hxChartBall)
  rcases hyLocus with ⟨U, hU_open, hyU, hUconst⟩
  let patch : Set X := (((chartAt ℂ x).source ∩ U) ∩ eX ⁻¹' (Metric.ball z0 r))
  have hpatch_open : IsOpen patch := by
    -- Intersect the constancy patch with the chosen chart ball.
    simpa [patch, eX, extChartAt_source, inter_assoc, inter_left_comm, inter_comm] using
      hU_open.inter (isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x Metric.isOpen_ball)
  have hyPatch : y ∈ patch := by
    exact ⟨⟨hyChartBall.1, hyU⟩, hyChartBall.2⟩
  let chartPatch : Set ℂ := chartAt ℂ x '' patch
  have hchartPatch_open : IsOpen chartPatch := by
    -- The chart sends the source patch to an open subset of the model space.
    exact CompactRiemannSurface.isOpen_image_chartAt x hpatch_open fun y hy ↦ hy.1.1
  have hchartPatch_nonempty : chartPatch.Nonempty := ⟨chartAt ℂ x y, ⟨y, hyPatch, rfl⟩⟩
  have hchartPatch_subset : chartPatch ⊆ Metric.ball z0 r := by
    rintro z ⟨w, hw, rfl⟩
    simpa [z0, eX, extChartAt_coe] using hw.2
  have hchartPatch_const :
      Set.EqOn g (fun _ ↦ eY (f x)) chartPatch := by
    -- On the transported open patch, the chart representative is literally constant.
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw_source : w ∈ (chartAt ℂ x).source := hw.1.1
    have hw_eq : f w = f x := by
      calc
        f w = c := hUconst hw.1.2
        _ = f x := hfx.symm
    have hw_chart_symm : (chartAt ℂ x).symm ((chartAt ℂ x) w) = w :=
      (chartAt ℂ x).left_inv hw_source
    simpa [g, eX, eY, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      Function.comp, hw_chart_symm, hw_eq]
  have hball_preconnected : IsPreconnected (Metric.ball z0 r) :=
    (convex_ball z0 r).isPreconnected
  rcases hBallAnalytic.is_constant_or_isOpen hball_preconnected with hconstBall | hopenBall
  · rcases hconstBall with ⟨w, hw⟩
    have hw0 : w = eY (f x) := by
      -- Normalize the constant by evaluating at the chart center.
      have hz0 : z0 ∈ Metric.ball z0 r := Metric.mem_ball_self hr
      have hz0_eval : g z0 = eY (f x) := by
        simp [g, z0, eX, eY, writtenInExtChartAt]
      exact (hw z0 hz0).symm.trans hz0_eval
    have hEventually :
        ∀ᶠ z in 𝓝 z0, g z = eY (f x) := by
      filter_upwards [Metric.ball_mem_nhds z0 hr] with z hz
      simpa [hw0] using hw z hz
    -- Turn chart constancy on a whole ball back into a manifold neighborhood of constancy.
    simpa [CompactRiemannSurfaceHom.localConstancyLocus, hfx, z0, g, eY] using
      CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt f x hEventually
  · have himage :
        g '' chartPatch = ({eY (f x)} : Set ℂ) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [hchartPatch_const hw]
      · intro hz
        rcases hchartPatch_nonempty with ⟨w, hw⟩
        have hz' : z = eY (f x) := by simpa using hz
        refine ⟨w, hw, ?_⟩
        have hw_const := hchartPatch_const hw
        simpa [hz'] using hw_const
    have hopenImage : IsOpen (g '' chartPatch) := by
      simpa [g, eX, eY, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
        Function.comp] using hopenBall chartPatch hchartPatch_subset hchartPatch_open
    have hsingletonOpen : IsOpen ({eY (f x)} : Set ℂ) := by
      simpa [himage] using hopenImage
    exact False.elim <| (not_isOpen_singleton (eY (f x))) hsingletonOpen

/-- Helper for Example 9.26.8: constancy on one nonempty open patch forces global constancy. -/
lemma CompactRiemannSurfaceHom.eq_const_of_eqOn_nonempty_open
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) {c : Y} {U : Set X}
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) (hUconst : Set.EqOn f (fun _ ↦ c) U) :
    ∀ z : X, f z = c := by
  let S := CompactRiemannSurfaceHom.localConstancyLocus f c
  have hS_open : IsOpen S := by
    -- Any witness neighborhood at one point witnesses openness of the whole locus nearby.
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    rcases hx with ⟨V, hV_open, hxV, hVconst⟩
    exact Filter.mem_of_superset (hV_open.mem_nhds hxV) fun y hyV ↦
      ⟨V, hV_open, hyV, hVconst⟩
  have hS_closed : IsClosed S := by
    -- Closure stability from the chart-ball argument makes the locus closed.
    rw [← closure_eq_iff_isClosed]
    exact Set.Subset.antisymm
      (fun x hx ↦ CompactRiemannSurfaceHom.mem_localConstancyLocus_of_mem_closure f hx)
      subset_closure
  have hS_nonempty : S.Nonempty := by
    rcases hU_nonempty with ⟨x, hxU⟩
    exact ⟨x, U, hU_open, hxU, hUconst⟩
  have hS_univ : S = Set.univ := by
    let hconnected :=
      (connectedSpace_iff_clopen (α := X)).1 (inferInstance : ConnectedSpace X)
    exact (hconnected.2 S ⟨hS_closed, hS_open⟩).resolve_left <| by
      intro hS_empty
      exact hS_nonempty.ne_empty hS_empty
  intro z
  have hzS : z ∈ S := by simpa [hS_univ]
  rcases hzS with ⟨V, _, hzV, hVconst⟩
  exact hVconst hzV

/-- Helper for Example 9.26.8: a nonconstant holomorphic map satisfies the neighborhood
criterion for openness at every point. -/
lemma CompactRiemannSurfaceHom.nhdsLeMapAt_of_isNonconstant
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (hf : f.IsNonconstant) (x : X) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  let eX := extChartAt 𝓘(ℂ) x
  let eY := extChartAt 𝓘(ℂ) (f x)
  let z0 : ℂ := eX x
  let w0 : ℂ := eY (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  rcases AnalyticAt.eventually_constant_or_nhds_le_map_nhds
      (CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt f x) with hconst | hmap
  · have hconst' :
        ∀ᶠ z in 𝓝 z0, g z = w0 := by
      have hz0_eval : g z0 = w0 := by
        simp [g, z0, w0, eX, eY, writtenInExtChartAt]
      filter_upwards [hconst] with z hz
      exact hz.trans hz0_eval
    rcases CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt f x hconst'
      with ⟨U, hU_open, hxU, hUconst⟩
    -- Route correction: once the chart branch is locally constant, the new rigidity lemma
    -- upgrades that to global constancy and contradicts `hf`.
    have hglobal : ∀ z : X, f z = f x :=
      CompactRiemannSurfaceHom.eq_const_of_eqOn_nonempty_open f hU_open ⟨x, hxU⟩ hUconst
    rcases hf with ⟨a, b, hab⟩
    exact (hab ((hglobal a).trans (hglobal b).symm)).elim
  · have hmap' :
        Filter.map eY.symm (𝓝 w0) ≤ Filter.map (eY.symm ∘ g) (𝓝 z0) :=
      by
        change Filter.map eY.symm (𝓝 w0) ≤ Filter.map eY.symm (Filter.map g (𝓝 z0))
        simpa [Filter.map_map] using Filter.map_mono (m := eY.symm) hmap
    have hleft : Filter.map eY.symm (𝓝 w0) = 𝓝 (f x) := by
      simpa [eY, w0, extChartAt_coe, extChartAt_coe_symm] using
        (chartAt ℂ (f x)).symm_map_nhds_eq (mem_chart_source _ (f x))
    have hcongr :
        (eY.symm ∘ g) =ᶠ[𝓝 z0] (f ∘ eX.symm) := by
      -- On the chart-validity neighborhood, the target chart inverse cancels back to `f`.
      filter_upwards [CompactRiemannSurfaceHom.chartValidity_eventuallyEq f x] with z hz
      have hz' :
          z ∈ (eX.target ∩ eX.symm ⁻¹' (f ⁻¹' eY.source) : Set ℂ) := hz.mp trivial
      have hz_source : f (eX.symm z) ∈ eY.source := hz'.2
      have hz_source' : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source := by
        simpa [eX, eY, extChartAt_source, extChartAt_coe_symm, Function.comp] using hz_source
      have hz_cancel :
          (chartAt ℂ (f x)).symm ((chartAt ℂ (f x)) (f ((chartAt ℂ x).symm z))) =
            f ((chartAt ℂ x).symm z) :=
        (chartAt ℂ (f x)).left_inv hz_source'
      simpa [eX, eY, g, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
        Function.comp, hz_cancel]
    have hright :
        Filter.map (eY.symm ∘ g) (𝓝 z0) = Filter.map (f ∘ eX.symm) (𝓝 z0) :=
      Filter.map_congr hcongr
    have hsource : Filter.map (f ∘ eX.symm) (𝓝 z0) = Filter.map f (𝓝 x) := by
      change Filter.map f (Filter.map eX.symm (𝓝 z0)) = Filter.map f (𝓝 x)
      congr 1
      simpa [eX, z0, extChartAt_coe, extChartAt_coe_symm] using
        (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source _ x)
    -- Transport the complex open-mapping neighborhood inequality back through the source and
    -- target charts.
    calc
      𝓝 (f x) = Filter.map eY.symm (𝓝 w0) := hleft.symm
      _ ≤ Filter.map (eY.symm ∘ g) (𝓝 z0) := hmap'
      _ = Filter.map (f ∘ eX.symm) (𝓝 z0) := hright
      _ = Filter.map f (𝓝 x) := hsource

/-- Example 9.26.8: a nonconstant holomorphic map of compact Riemann surfaces is open. -/
lemma CompactRiemannSurfaceHom.isOpenMap_of_isNonconstant
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (hf : f.IsNonconstant) : IsOpenMap f.toFun := by
  -- Route correction: the missing step was global rigidity from one open constancy patch.
  -- With that in place, the complex open-mapping dichotomy reduces pointwise to `nhds ≤ map nhds`.
  exact isOpenMap_iff_nhds_le.2 fun x ↦
    CompactRiemannSurfaceHom.nhdsLeMapAt_of_isNonconstant f hf x

instance : CompactRiemannSurface.nonconstantHom.IsMultiplicative where
  id_mem X := by
    -- The identity map is nonconstant because the object itself is nontrivial.
    obtain ⟨x, y, hxy⟩ := CompactRiemannSurface.exists_pair_ne X
    exact ⟨x, y, hxy⟩
  comp_mem f g hf hg := by
    -- Route correction: witness chasing is insufficient here, so first upgrade `f` to an open map.
    have hf_open : IsOpenMap f.toFun :=
      CompactRiemannSurfaceHom.isOpenMap_of_isNonconstant f hf
    -- Once `f` is open, compactness and connectedness force surjectivity, so the witness pair
    -- for `g` can be pulled back along `f`.
    simpa [CompactRiemannSurfaceHom.IsNonconstant] using
      CompactRiemannSurfaceHom.nonconstantCompositeWitnesses f g
        (CompactRiemannSurfaceHom.surjective_of_isOpenMap f hf_open) hg

/-- The category of compact Riemann surfaces with nonconstant holomorphic maps, realized as the
wide subcategory of holomorphic maps cut out by the nonconstancy property. -/
abbrev CompactRiemannSurfaceCat :=
  WideSubcategory CompactRiemannSurface.nonconstantHom

end
