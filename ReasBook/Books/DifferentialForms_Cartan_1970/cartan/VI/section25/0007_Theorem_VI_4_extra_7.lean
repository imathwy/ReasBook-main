import Mathlib

open scoped Manifold
open scoped Topology
open Set

universe w w'

/- Domain sampling:
* primary domain: one-dimensional complex manifolds and holomorphic maps;
* source-facing item: uniqueness of analytic continuation from a nonempty open subset;
* core/canonical owner: `MDifferentiable`;
* bridge/view API used in the proof:
  - `MDifferentiableOn` in charts;
  - `DifferentiableOn.analyticOnNhd` on open subsets of `ℂ`;
  - `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

The source manifold in this chapter is canonically modeled on `ℂ`, so the public theorem should
live on the owner namespace `MDifferentiable` rather than as a parallel standalone wrapper.
-/

namespace MDifferentiable

/-- Theorem VI.4-extra-7. Let `D` be a nonempty open subset of a preconnected complex manifold
`X`. If two holomorphic maps `f, g : X → X'` into a complex manifold `X'` agree on `D`, then they
agree on all of `X`. -/
protected theorem eq_of_eqOn_nonempty_open
    {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
    {I : ModelWithCorners ℂ ℂ ℂ} [I.Boundaryless] [PreconnectedSpace X] [IsManifold I 1 X]
    {X' : Type w'} [TopologicalSpace X'] [T2Space X'] [ChartedSpace ℂ X']
    {I' : ModelWithCorners ℂ ℂ ℂ} [I'.Boundaryless] [IsManifold I' 1 X']
    {D : Set X} {f g : X → X'}
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I I' g)
    (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) (hfg : EqOn f g D) :
    f = g := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  let A : Set X := {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ EqOn f g U}
  have hf_cont : Continuous f := hf.continuous
  have hg_cont : Continuous g := hg.continuous
  have hA_open : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
    rcases hx with ⟨U, hU_open, hxU, hU_eq⟩
    exact Filter.mem_of_superset (hU_open.mem_nhds hxU) fun y hyU ↦ ⟨U, hU_open, hyU, hU_eq⟩
  have hA_nonempty : A.Nonempty := by
    rcases hD_nonempty with ⟨x, hx⟩
    exact ⟨x, D, hD_open, hx, hfg⟩
  have hA_subset_eq : A ⊆ {x | f x = g x} := by
    intro x hx
    rcases hx with ⟨U, _hU_open, hxU, hU_eq⟩
    exact hU_eq hxU
  have hA_closed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro x hx_closure
    have hx_eq : f x = g x := by
      have hclosure_subset_eq : closure A ⊆ {x | f x = g x} :=
        (isClosed_eq hf_cont hg_cont).closure_subset_iff.mpr hA_subset_eq
      exact hclosure_subset_eq hx_closure
    let y := f x
    have hy : g x = y := by simpa [y] using hx_eq.symm
    let e := extChartAt I x
    let φ := extChartAt I' y
    let V : Set X := (e.source ∩ f ⁻¹' φ.source) ∩ g ⁻¹' φ.source
    have hV_open : IsOpen V := by
      exact
        ((isOpen_extChartAt_source x).inter ((isOpen_extChartAt_source y).preimage hf_cont)).inter
          ((isOpen_extChartAt_source y).preimage hg_cont)
    have hxV : x ∈ V := by
      refine ⟨⟨mem_extChartAt_source x, ?_⟩, ?_⟩
      · simp [φ, y]
      · simp [φ, hy, y]
    have hV_nhds : V ∈ 𝓝 x := hV_open.mem_nhds hxV
    let C : Set X := connectedComponentIn V x
    have hC_open : IsOpen C := hV_open.connectedComponentIn
    have hxC : x ∈ C := mem_connectedComponentIn hxV
    have hC_subset : C ⊆ V := connectedComponentIn_subset V x
    have hC_preconnected : IsPreconnected C := isPreconnected_connectedComponentIn
    have hA_inter_C_nonempty : (A ∩ C).Nonempty := by
      rcases (mem_closure_iff_nhds.1 hx_closure) C (hC_open.mem_nhds hxC) with ⟨z, hzC, hzA⟩
      exact ⟨z, hzA, hzC⟩
    rcases hA_inter_C_nonempty with ⟨a, haA, haC⟩
    rcases haA with ⟨U, hU_open, haU, hU_eq⟩
    have hC_subset_source : C ⊆ e.source := fun z hz ↦ (hC_subset hz).1.1
    have hfC_maps : MapsTo f C φ.source := by
      intro z hz
      exact (hC_subset hz).1.2
    have hgC_maps : MapsTo g C φ.source := by
      intro z hz
      exact (hC_subset hz).2
    have hF_diff : DifferentiableOn ℂ (φ ∘ f ∘ e.symm) (e '' C) := by
      have hmdiffC : MDifferentiableOn I I' f C := hf.mdifferentiableOn.mono hC_subset
      simpa [e, φ] using
        (mdifferentiableOn_iff_of_subset_source' hC_subset_source hfC_maps).1 hmdiffC
    have hG_diff : DifferentiableOn ℂ (φ ∘ g ∘ e.symm) (e '' C) := by
      have hmdiffC : MDifferentiableOn I I' g C := hg.mdifferentiableOn.mono hC_subset
      simpa [e, φ] using
        (mdifferentiableOn_iff_of_subset_source' hC_subset_source hgC_maps).1 hmdiffC
    have hChartC_open : IsOpen ((chartAt ℂ x) '' C) :=
      (chartAt ℂ x).isOpen_image_of_subset_source hC_open (by simpa [e] using hC_subset_source)
    have hEC_open : IsOpen (e '' C) := by
      simpa [e, extChartAt_coe, Function.comp, Set.image_image] using
        (I.toHomeomorph.isOpen_image).2 hChartC_open
    have hEC_preconnected : IsPreconnected (e '' C) :=
      hC_preconnected.image e ((continuousOn_extChartAt x).mono hC_subset_source)
    have hUC_open : IsOpen (U ∩ C) := hU_open.inter hC_open
    have hUC_subset_source : U ∩ C ⊆ e.source := fun z hz ↦ hC_subset_source hz.2
    have hChartUC_open : IsOpen ((chartAt ℂ x) '' (U ∩ C)) :=
      (chartAt ℂ x).isOpen_image_of_subset_source hUC_open (by simpa [e] using hUC_subset_source)
    have hEUC_open : IsOpen (e '' (U ∩ C)) := by
      simpa [e, extChartAt_coe, Function.comp, Set.image_image] using
        (I.toHomeomorph.isOpen_image).2 hChartUC_open
    have hEUC_nonempty : (e '' (U ∩ C)).Nonempty := ⟨e a, ⟨a, ⟨haU, haC⟩, rfl⟩⟩
    have hEqOn_image : EqOn (φ ∘ f ∘ e.symm) (φ ∘ g ∘ e.symm) (e '' (U ∩ C)) := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      have hw_source : w ∈ e.source := hC_subset_source hw.2
      have hUw : e.symm (e w) ∈ U := by simpa [e.left_inv hw_source] using hw.1
      exact congrArg φ (hU_eq hUw)
    rcases hEUC_nonempty with ⟨z₀, hz₀⟩
    have hz₀_mem : z₀ ∈ e '' C := by
      rcases hz₀ with ⟨w, hw, rfl⟩
      exact ⟨w, hw.2, rfl⟩
    have h_event : (φ ∘ f ∘ e.symm) =ᶠ[𝓝 z₀] (φ ∘ g ∘ e.symm) := by
      exact hEqOn_image.eventuallyEq_of_mem (hEUC_open.mem_nhds hz₀)
    have hEqOn_chart :
        EqOn (φ ∘ f ∘ e.symm) (φ ∘ g ∘ e.symm) (e '' C) :=
      (hF_diff.analyticOnNhd hEC_open).eqOn_of_preconnected_of_eventuallyEq
        (hG_diff.analyticOnNhd hEC_open) hEC_preconnected hz₀_mem h_event
    have hEqOn_C : EqOn f g C := by
      intro z hz
      have hz_chart : φ (f z) = φ (g z) := by
        have : (φ ∘ f ∘ e.symm) (e z) = (φ ∘ g ∘ e.symm) (e z) :=
          hEqOn_chart ⟨z, hz, rfl⟩
        simpa [Function.comp, e.left_inv (hC_subset_source hz)] using this
      have hfz : f z ∈ φ.source := hfC_maps hz
      have hgz : g z ∈ φ.source := hgC_maps hz
      rw [← φ.left_inv hfz, ← φ.left_inv hgz, hz_chart]
    exact ⟨C, hC_open, hxC, hEqOn_C⟩
  have hA_univ : A = univ := IsClopen.eq_univ ⟨hA_closed, hA_open⟩ hA_nonempty
  ext x
  have hxA : x ∈ A := by
    simp [hA_univ]
  exact hA_subset_eq hxA

end MDifferentiable
