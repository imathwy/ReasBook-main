import Mathlib

open scoped Manifold Topology

-- Declarations for this item will be appended below by the statement pipeline.

section Topological

variable {X : Type*} [TopologicalSpace X] {Y : Type*}

/-- Proposition 4.I (1): the set of points of `X` in a neighborhood of which two maps `f` and `g`
coincide is open. This is purely topological; no holomorphic hypotheses are needed. -/
theorem local_coincidence_set_isOpen {f g : X → Y} :
    IsOpen {x : X | f =ᶠ[𝓝 x] g} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases eventually_nhds_iff.mp hx with ⟨U, hU, hU_open, hxU⟩
  have hEq : Set.EqOn f g U := fun y hy ↦ hU y hy
  exact Filter.mem_of_superset (hU_open.mem_nhds hxU) fun y hyU ↦
    hEq.eventuallyEq_of_mem (hU_open.mem_nhds hyU)

end Topological

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ E' H'} [I'.Boundaryless]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X'] [IsManifold I' 1 X']

/-- Helper for Proposition 4.I: in a Hausdorff target, a closure point of the local coincidence
locus is already a pointwise coincidence point. -/
lemma closure_point_eq_of_mem_local_coincidence_closure [T2Space X'] {f g : X → X'}
    (hf : Continuous f) (hg : Continuous g)
    {a : X} (ha : a ∈ closure {x : X | f =ᶠ[𝓝 x] g}) :
    f a = g a := by
  -- A local coincidence at `x` specializes to an ordinary equality at `x`.
  have hsubset : {x : X | f =ᶠ[𝓝 x] g} ⊆ {x : X | f x = g x} := by
    intro x hx
    exact hx.eq_of_nhds
  -- The diagonal is closed in a Hausdorff target, so the closure still lies in that diagonal.
  have hclosure_subset :
      closure {x : X | f =ᶠ[𝓝 x] g} ⊆ {x : X | f x = g x} :=
    (isClosed_eq hf hg).closure_subset_iff.mpr hsubset
  exact hclosure_subset ha

/-- Helper for Proposition 4.I: if two complex-differentiable maps agree near one point of a ball
contained in the domain, then analytic continuation along complex affine lines makes them agree on
the whole ball. -/
lemma eqOn_ball_of_differentiableOn_of_eventuallyEq
    {U : Set E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ ψ : E → F} {x a : E} {r : ℝ}
    (hφ : DifferentiableOn ℂ φ U) (hψ : DifferentiableOn ℂ ψ U)
    (hballU : Metric.ball x r ⊆ U) (ha : a ∈ Metric.ball x r) (hEq : φ =ᶠ[𝓝 a] ψ) :
    Set.EqOn φ ψ (Metric.ball x r) := by
  intro w hw
  let ℓ : ℂ →ᵃ[ℂ] E := AffineMap.lineMap a w
  let V : Set ℂ := ℓ ⁻¹' Metric.ball x r
  let D : Set ℂ := connectedComponentIn V 0
  have hV_open : IsOpen V := by
    -- The affine line stays inside the ball on an open condition.
    simpa [V] using Metric.isOpen_ball.preimage ℓ.differentiable.continuous
  have hD_open : IsOpen D := hV_open.connectedComponentIn
  have hD_preconnected : IsPreconnected D := isPreconnected_connectedComponentIn
  have h0V : (0 : ℂ) ∈ V := by
    simpa [V, ℓ, AffineMap.lineMap_apply_zero] using ha
  have h0D : (0 : ℂ) ∈ D := mem_connectedComponentIn h0V
  have h1D : (1 : ℂ) ∈ D := by
    let I : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
    have hI_preconnected : IsPreconnected I := by
      simpa [I] using
        isPreconnected_Icc.image Complex.ofReal Complex.continuous_ofReal.continuousOn
    have hI_subset : I ⊆ D := by
      have hI_subset_V : I ⊆ V := by
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        have hline :
            ℓ (Complex.ofReal t) = (AffineMap.lineMap a w : ℝ →ᵃ[ℝ] E) t := by
          dsimp [ℓ]
          rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
          exact congrArg (fun v : E ↦ v + a) (Complex.coe_smul t (w - a))
        have hseg : (AffineMap.lineMap a w : ℝ →ᵃ[ℝ] E) t ∈ Metric.ball x r :=
          (convex_ball x r).lineMap_mem ha hw ht
        -- The real segment between `a` and `w` stays inside the convex ball.
        simpa [V, hline] using hseg
      have h0I : (0 : ℂ) ∈ I := by
        exact ⟨0, by simp, by simp⟩
      exact hI_preconnected.subset_connectedComponentIn h0I hI_subset_V
    have h1I : (1 : ℂ) ∈ I := by
      exact ⟨1, by simp, by simp⟩
    exact hI_subset h1I
  have hD_maps_U : Set.MapsTo ℓ D U := by
    intro z hz
    exact hballU <| by
      simpa [V] using connectedComponentIn_subset V 0 hz
  have hφD : DifferentiableOn ℂ (φ ∘ ℓ) D :=
    hφ.comp ℓ.differentiableOn hD_maps_U
  have hψD : DifferentiableOn ℂ (ψ ∘ ℓ) D :=
    hψ.comp ℓ.differentiableOn hD_maps_U
  have hEq_line : (φ ∘ ℓ) =ᶠ[𝓝 (0 : ℂ)] (ψ ∘ ℓ) := by
    -- Pull the given local coincidence at `a` back to the origin of the affine line.
    have hℓ_tendsto : Filter.Tendsto ℓ (𝓝 (0 : ℂ)) (𝓝 a) := by
      have hℓ_cont : ContinuousAt ℓ (0 : ℂ) := ℓ.differentiableAt.continuousAt
      simpa [ContinuousAt, ℓ, AffineMap.lineMap_apply_zero] using hℓ_cont
    simpa using hEq.comp_tendsto hℓ_tendsto
  have hdual :
      ∀ g : StrongDual ℂ F, g (φ w) = g (ψ w) := by
    intro g
    have hgφ : DifferentiableOn ℂ (g ∘ φ ∘ ℓ) D :=
      g.differentiable.comp_differentiableOn hφD
    have hgψ : DifferentiableOn ℂ (g ∘ ψ ∘ ℓ) D :=
      g.differentiable.comp_differentiableOn hψD
    have hEq_line_g : (g ∘ φ ∘ ℓ) =ᶠ[𝓝 (0 : ℂ)] (g ∘ ψ ∘ ℓ) :=
      hEq_line.fun_comp g
    have hEqOn_line_g : Set.EqOn (g ∘ φ ∘ ℓ) (g ∘ ψ ∘ ℓ) D := by
      -- Scalar-valued restrictions are analytic on the connected component, so the classical
      -- one-variable identity theorem applies.
      exact (hgφ.analyticOnNhd hD_open).eqOn_of_preconnected_of_eventuallyEq
        (hgψ.analyticOnNhd hD_open) hD_preconnected h0D hEq_line_g
    have h_at_one_g : (g ∘ φ ∘ ℓ) 1 = (g ∘ ψ ∘ ℓ) 1 := hEqOn_line_g h1D
    simpa [ℓ, AffineMap.lineMap_apply_one, Function.comp] using h_at_one_g
  exact (SeparatingDual.eq_iff_forall_dual_eq).2 hdual

/-- Helper for Proposition 4.I: on an open preconnected subset of a complex normed space, two
complex-differentiable maps that agree in a neighborhood of one point agree everywhere on that
subset. -/
lemma differentiableOn_eqOn_of_isOpen_of_preconnected_of_eventuallyEq
    {U : Set E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ ψ : E → F}
    (hφ : DifferentiableOn ℂ φ U) (hψ : DifferentiableOn ℂ ψ U)
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    {z₀ : E} (hz₀ : z₀ ∈ U) (hEq : φ =ᶠ[𝓝 z₀] ψ) :
    Set.EqOn φ ψ U := by
  -- Route correction: rather than searching for a nonexistent several-variable
  -- `DifferentiableOn ℂ -> AnalyticOnNhd` bridge, propagate equality on small balls by restricting
  -- to complex affine lines and then use a clopen argument on the subtype `U`.
  let A : Set U := {z | φ =ᶠ[𝓝 (z : E)] ψ}
  have hA_open : IsOpen A := by
    -- Local coincidence is an open condition, and the subtype `U` inherits it by pullback.
    simpa [A] using
      (local_coincidence_set_isOpen (f := φ) (g := ψ)).preimage continuous_subtype_val
  have hA_compl_open : IsOpen Aᶜ := by
    refine Metric.isOpen_iff.mpr ?_
    intro x hxA
    have hx_not : ¬ φ =ᶠ[𝓝 (x : E)] ψ := by
      simpa [A] using hxA
    rcases Metric.isOpen_iff.mp hU_open (x : E) x.property with ⟨r, hr, hballU⟩
    refine ⟨r / 2, by linarith, ?_⟩
    intro y hy
    have hy_small : (y : E) ∈ Metric.ball (x : E) (r / 2) := by
      simpa using hy
    have hy_big : (y : E) ∈ Metric.ball (x : E) r := by
      rw [Metric.mem_ball] at hy_small ⊢
      linarith
    have hy_not : ¬ φ =ᶠ[𝓝 (y : E)] ψ := by
      intro hyEq
      -- A local coincidence at `y` propagates across the whole ambient ball, in particular to `x`.
      have hEqOn_ball : Set.EqOn φ ψ (Metric.ball (x : E) r) :=
        eqOn_ball_of_differentiableOn_of_eventuallyEq hφ hψ hballU hy_big hyEq
      have hxEq : φ =ᶠ[𝓝 (x : E)] ψ :=
        hEqOn_ball.eventuallyEq_of_mem
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
      exact hx_not hxEq
    simpa [A] using hy_not
  have hA_clopen : IsClopen A := ⟨isOpen_compl_iff.mp hA_compl_open, hA_open⟩
  have hA_nonempty : A.Nonempty := ⟨⟨z₀, hz₀⟩, hEq⟩
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hU_preconnected
  have hA_univ : A = Set.univ := IsClopen.eq_univ hA_clopen hA_nonempty
  intro z hz
  have hzA : (⟨z, hz⟩ : U) ∈ A := by
    simp [hA_univ]
  exact hzA.eq_of_nhds

/-- Proposition 4.I (2): for holomorphic mappings `f` and `g` of a complex manifold `X` into a
Hausdorff complex manifold `X'`, the set of points of `X` in a neighborhood of which `f` and `g`
coincide is closed. The Hausdorff condition is part of the standard complex-manifold convention
used by the source text. -/
theorem holomorphic_local_coincidence_set_isClosed [T2Space X'] {f g : X → X'}
    (hf : MDiff f) (hg : MDiff g) :
    IsClosed {x : X | f =ᶠ[𝓝 x] g} := by
  -- Route correction: the textbook closure argument first shows `f a = g a` for
  -- `a ∈ closure {x | f =ᶠ[𝓝 x] g}` by continuity.
  -- The remaining step is local: move to one connected chart neighborhood around `a`,
  -- use the chart-level identity theorem there, and push the equality back to `X`.
  rw [← closure_subset_iff_isClosed]
  intro a ha
  have ha_eq : f a = g a :=
    closure_point_eq_of_mem_local_coincidence_closure hf.continuous hg.continuous ha
  haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace H X
  let y := f a
  have hy : g a = y := by
    simpa [y] using ha_eq.symm
  let e := extChartAt I a
  let φ := extChartAt I' y
  let V : Set X := (e.source ∩ f ⁻¹' φ.source) ∩ g ⁻¹' φ.source
  -- The chart neighborhood keeps both maps inside a single target chart.
  have hV_open : IsOpen V := by
    exact
      ((isOpen_extChartAt_source a).inter
          ((isOpen_extChartAt_source y).preimage hf.continuous)).inter
        ((isOpen_extChartAt_source y).preimage hg.continuous)
  have haV : a ∈ V := by
    refine ⟨⟨mem_extChartAt_source a, ?_⟩, ?_⟩
    · simp [φ, y]
    · simp [φ, hy, y]
  let C : Set X := connectedComponentIn V a
  have hC_open : IsOpen C := hV_open.connectedComponentIn
  have haC : a ∈ C := mem_connectedComponentIn haV
  have hC_subset : C ⊆ V := connectedComponentIn_subset V a
  have hC_preconnected : IsPreconnected C := isPreconnected_connectedComponentIn
  -- Since `a` lies in the closure of the local coincidence locus, this connected neighborhood
  -- contains a point where `f` and `g` already coincide on some open set.
  rcases (mem_closure_iff_nhds.1 ha) C (hC_open.mem_nhds haC) with ⟨z, hzC, hzA⟩
  rcases eventually_nhds_iff.mp hzA with ⟨U, hU, hU_open, hzU⟩
  have hU_eq : Set.EqOn f g U := fun x hx ↦ hU x hx
  have hC_subset_source : C ⊆ e.source := fun x hx ↦ (hC_subset hx).1.1
  have hfC_maps : Set.MapsTo f C φ.source := fun x hx ↦ (hC_subset hx).1.2
  have hgC_maps : Set.MapsTo g C φ.source := fun x hx ↦ (hC_subset hx).2
  -- Restrict the holomorphic maps to the connected component and pass to coordinates.
  have hF_diff : DifferentiableOn ℂ (φ ∘ f ∘ e.symm) (e '' C) := by
    have hmdiffC : MDiff[C] f := hf.mdifferentiableOn.mono hC_subset
    simpa [e, φ] using
      (mdifferentiableOn_iff_of_subset_source' hC_subset_source hfC_maps).1 hmdiffC
  have hG_diff : DifferentiableOn ℂ (φ ∘ g ∘ e.symm) (e '' C) := by
    have hmdiffC : MDiff[C] g := hg.mdifferentiableOn.mono hC_subset
    simpa [e, φ] using
      (mdifferentiableOn_iff_of_subset_source' hC_subset_source hgC_maps).1 hmdiffC
  have hChartC_open : IsOpen ((chartAt H a) '' C) :=
    (chartAt H a).isOpen_image_of_subset_source hC_open (by simpa [e] using hC_subset_source)
  have hEC_open : IsOpen (e '' C) := by
    simpa [e, extChartAt_coe, Function.comp, Set.image_image] using
      (I.toHomeomorph.isOpen_image).2 hChartC_open
  have hEC_preconnected : IsPreconnected (e '' C) :=
    hC_preconnected.image e ((continuousOn_extChartAt a).mono hC_subset_source)
  have hUC_open : IsOpen (U ∩ C) := hU_open.inter hC_open
  have hUC_subset_source : U ∩ C ⊆ e.source := fun x hx ↦ hC_subset_source hx.2
  have hChartUC_open : IsOpen ((chartAt H a) '' (U ∩ C)) :=
    (chartAt H a).isOpen_image_of_subset_source hUC_open
      (by simpa [e] using hUC_subset_source)
  have hEUC_open : IsOpen (e '' (U ∩ C)) := by
    simpa [e, extChartAt_coe, Function.comp, Set.image_image] using
      (I.toHomeomorph.isOpen_image).2 hChartUC_open
  have hEUC_nonempty : (e '' (U ∩ C)).Nonempty := ⟨e z, ⟨z, ⟨hzU, hzC⟩, rfl⟩⟩
  have hEqOn_image : Set.EqOn (φ ∘ f ∘ e.symm) (φ ∘ g ∘ e.symm) (e '' (U ∩ C)) := by
    intro w hw
    rcases hw with ⟨x, hx, rfl⟩
    have hx_source : x ∈ e.source := hC_subset_source hx.2
    have hxU : e.symm (e x) ∈ U := by
      simpa [e.left_inv hx_source] using hx.1
    exact congrArg φ (hU_eq hxU)
  rcases hEUC_nonempty with ⟨w₀, hw₀⟩
  have hw₀_mem : w₀ ∈ e '' C := by
    rcases hw₀ with ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩
  have h_event : (φ ∘ f ∘ e.symm) =ᶠ[𝓝 w₀] (φ ∘ g ∘ e.symm) := by
    exact hEqOn_image.eventuallyEq_of_mem (hEUC_open.mem_nhds hw₀)
  have hEqOn_chart : Set.EqOn (φ ∘ f ∘ e.symm) (φ ∘ g ∘ e.symm) (e '' C) :=
    differentiableOn_eqOn_of_isOpen_of_preconnected_of_eventuallyEq
      hF_diff hG_diff hEC_open hEC_preconnected hw₀_mem h_event
  have hEqOn_C : Set.EqOn f g C := by
    intro x hx
    have hx_chart : φ (f x) = φ (g x) := by
      have : (φ ∘ f ∘ e.symm) (e x) = (φ ∘ g ∘ e.symm) (e x) :=
        hEqOn_chart ⟨x, hx, rfl⟩
      simpa [Function.comp, e.left_inv (hC_subset_source hx)] using this
    have hfx : f x ∈ φ.source := hfC_maps hx
    have hgx : g x ∈ φ.source := hgC_maps hx
    rw [← φ.left_inv hfx, ← φ.left_inv hgx, hx_chart]
  -- Equality on the whole connected neighborhood gives the required eventual equality at `a`.
  exact hEqOn_C.eventuallyEq_of_mem (hC_open.mem_nhds haC)

end Holomorphic
