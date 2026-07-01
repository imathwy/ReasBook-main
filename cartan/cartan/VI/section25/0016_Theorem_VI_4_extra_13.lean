import Mathlib

universe u

open scoped Complex.UnitDisc Manifold

namespace Complex.UnitDisc

/-- The canonical coercion from the unit disc `𝔻` to `ℂ` is an open embedding. -/
theorem isOpenEmbedding_coe : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) := by
  simpa [Complex.UnitDisc] using
    ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal :
      Topology.IsOpenEmbedding ((↑) : Metric.ball (0 : ℂ) 1 → ℂ))

noncomputable instance : ChartedSpace ℂ 𝔻 :=
  isOpenEmbedding_coe.singletonChartedSpace

instance : IsManifold 𝓘(ℂ) 1 𝔻 :=
  isOpenEmbedding_coe.isManifold_singleton

end Complex.UnitDisc

/-
Domain sampling:
* primary domain: one-dimensional complex manifolds and their biholomorphic equivalences;
* source-facing layer: the theorem classifies simply connected Hausdorff complex manifolds by the
  canonical Riemann sphere, complex plane, and unit disc;
* core/canonical owner declarations inspected before this refinement:
  - the chapter-local Hausdorff owner `ComplexManifold` from
    `section25/0005_Definition_VI_4_extra_5.lean`;
  - mathlib's canonical one-point compactification carrier `OnePoint ℂ`;
  - mathlib's owner API `OnePoint.isOpenEmbedding_coe`,
    `OnePoint.continuousAt_infty'`, and `OnePoint.tendsto_coe_infty`.
* bridge/view layer: the local complex-manifold atlas on the canonical carrier `OnePoint ℂ`.

Primitive data here is only the standard affine chart and inversion chart. The topology is not
primitive data: it is the canonical `OnePoint ℂ` topology supplied upstream.
-/

/-- The canonical carrier of the Riemann sphere is the one-point compactification of `ℂ`. -/
abbrev RiemannSphere := OnePoint ℂ

namespace RiemannSphere

open Bornology Filter OnePoint Topology

/-- The affine chart on the finite part of the Riemann sphere. -/
def affineChart : PartialEquiv RiemannSphere ℂ where
  toFun
    | OnePoint.infty => 0
    | (z : ℂ) => z
  invFun z := (z : RiemannSphere)
  source := ({OnePoint.infty} : Set RiemannSphere)ᶜ
  target := Set.univ
  map_source' _ _ := by simp
  map_target' _ _ := by simp
  left_inv' z hz := by
    cases z using OnePoint.rec <;> simp at hz
    rfl
  right_inv' z _ := rfl

/-- The inverse affine coordinate on the Riemann sphere. -/
noncomputable def inftyInv : ℂ → RiemannSphere :=
  fun z ↦ if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : RiemannSphere)

/-- The chart centered at `∞`, given by the inversion coordinate `w = 1 / z`. -/
noncomputable def inftyChart : PartialEquiv RiemannSphere ℂ where
  toFun
    | OnePoint.infty => 0
    | (z : ℂ) => z⁻¹
  invFun := inftyInv
  source := ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ
  target := Set.univ
  map_source' _ _ := by simp
  map_target' z _ := by
    by_cases hz : z = 0
    · simp [inftyInv, hz]
    · simp [inftyInv, hz]
  left_inv' z hz := by
    cases z using OnePoint.rec with
    | infty =>
        simp [inftyInv]
    | coe w =>
        have hw : w ≠ 0 := by simpa using hz
        simp [inftyInv, hw]
  right_inv' z _ := by
    by_cases hz : z = 0
    · simp [inftyInv, hz]
    · simp [inftyInv, hz]

noncomputable def affineOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := affineChart
  open_source := by
    simp [affineChart]
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    rcases OnePoint.ne_infty_iff_exists.mp (by simpa using hx) with ⟨z, rfl⟩
    have hAffine :
        ContinuousAt affineChart z ↔ ContinuousAt (fun w : ℂ ↦ affineChart w) z :=
      OnePoint.continuousAt_coe
    exact
      (hAffine.2 <| by
        simpa [affineChart] using
          (continuousAt_id : ContinuousAt (fun w : ℂ ↦ w) z)).continuousWithinAt
  continuousOn_invFun := by
    intro z hz
    simpa [affineChart] using
      (OnePoint.continuous_coe : Continuous ((↑) : ℂ → RiemannSphere)).continuousWithinAt

noncomputable def inftyOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := inftyChart
  open_source := by
    have hclosed : IsClosed ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere) := by
      have himage :
          IsClosed (((↑) '' ({0} : Set ℂ) : Set RiemannSphere)) ↔
            IsClosed ({0} : Set ℂ) ∧ IsCompact ({0} : Set ℂ) :=
        OnePoint.isClosed_image_coe
      simpa [Set.image_singleton] using himage.2 ⟨isClosed_singleton, isCompact_singleton⟩
    simpa [inftyChart] using hclosed.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    cases x using OnePoint.rec with
    | infty =>
        have hInfty :
            ContinuousAt inftyChart OnePoint.infty ↔
              Tendsto (fun z : ℂ ↦ z⁻¹) (Filter.coclosedCompact ℂ) (𝓝 (0 : ℂ)) := by
          simpa [inftyChart] using
            (OnePoint.continuousAt_infty' :
              ContinuousAt inftyChart OnePoint.infty ↔
                Tendsto (fun z : ℂ ↦ inftyChart z) (Filter.coclosedCompact ℂ)
                  (𝓝 (inftyChart OnePoint.infty)))
        exact
          (hInfty.2 <| by
            simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
              (Filter.tendsto_inv₀_cobounded :
                Tendsto (Inv.inv : ℂ → ℂ) (cobounded ℂ) (𝓝 (0 : ℂ)))).continuousWithinAt
    | coe z =>
        have hz : z ≠ 0 := by simpa [inftyChart] using hx
        have hCoe :
            ContinuousAt inftyChart z ↔ ContinuousAt (fun w : ℂ ↦ inftyChart w) z :=
          OnePoint.continuousAt_coe
        exact
          (hCoe.2 <| by
            change ContinuousAt (fun w : ℂ ↦ w⁻¹) z
            simpa using (continuousAt_inv₀ hz)).continuousWithinAt
  continuousOn_invFun := by
    intro z _
    by_cases hz : z = 0
    · subst hz
      have hne :
          Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] (0 : ℂ)) (Filter.coclosedCompact ℂ) := by
        simpa [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (Filter.tendsto_inv₀_nhdsNE_zero :
            Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] (0 : ℂ)) (cobounded ℂ))
      have hpunct :
          Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝[≠] (0 : ℂ))
            (𝓝 (OnePoint.infty : RiemannSphere)) := by
        simpa [Function.comp_def] using
          (OnePoint.tendsto_coe_infty : Tendsto ((↑) : ℂ → RiemannSphere)
            (Filter.coclosedCompact ℂ) (𝓝 (OnePoint.infty : RiemannSphere))).comp
            hne
      have hpunct' : Tendsto inftyInv (𝓝[≠] (0 : ℂ)) (𝓝 (OnePoint.infty : RiemannSphere)) := by
        have hne0 : {w : ℂ | w ≠ 0} ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
        refine Tendsto.congr' ?_ hpunct
        filter_upwards [hne0] with w hw
        simp [inftyInv, hw]
      have h0 : ContinuousAt inftyInv (0 : ℂ) := by
        rw [ContinuousAt, show inftyInv 0 = (OnePoint.infty : RiemannSphere) by simp [inftyInv],
          ← nhdsNE_sup_pure (0 : ℂ)]
        refine hpunct'.sup ?_
        simpa [inftyInv] using tendsto_pure_nhds inftyInv (0 : ℂ)
      simpa [inftyChart] using (h0.continuousWithinAt : ContinuousWithinAt inftyInv Set.univ 0)
    · have hcont :
          Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝 z)
            (𝓝 ((z⁻¹ : ℂ) : RiemannSphere)) :=
        ((show Continuous ((↑) : ℂ → RiemannSphere) from OnePoint.continuous_coe).continuousAt.comp
          (continuousAt_inv₀ hz)).tendsto
      have hz' : ContinuousAt inftyInv z := by
        have hcont' :
            Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : RiemannSphere)) (𝓝 z) (𝓝 (inftyInv z)) := by
          simpa [inftyInv, hz] using hcont
        refine Tendsto.congr' ?_ hcont'
        filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton hz] with w hw
        have hw0 : w ≠ 0 := by simpa using hw
        simp [inftyInv, hw0]
      simpa [inftyChart] using (hz'.continuousWithinAt : ContinuousWithinAt inftyInv Set.univ z)

noncomputable instance : ChartedSpace ℂ RiemannSphere where
  atlas := {affineOpenPartialHomeomorph, inftyOpenPartialHomeomorph}
  chartAt
    | OnePoint.infty => inftyOpenPartialHomeomorph
    | (_ : ℂ) => affineOpenPartialHomeomorph
  mem_chart_source z := by
    cases z using OnePoint.rec <;>
      simp [affineOpenPartialHomeomorph, affineChart, inftyOpenPartialHomeomorph, inftyChart]
  chart_mem_atlas z := by
    cases z using OnePoint.rec <;> simp

@[simp] theorem chartAt_infty :
    chartAt ℂ (OnePoint.infty : RiemannSphere) = inftyOpenPartialHomeomorph :=
  rfl

@[simp] theorem chartAt_coe (z : ℂ) :
    chartAt ℂ (z : RiemannSphere) = affineOpenPartialHomeomorph :=
  rfl

theorem mem_atlas_iff {e : OpenPartialHomeomorph RiemannSphere ℂ} :
    e ∈ atlas ℂ RiemannSphere ↔
      e = affineOpenPartialHomeomorph ∨ e = inftyOpenPartialHomeomorph := by
  change e ∈ ({affineOpenPartialHomeomorph, inftyOpenPartialHomeomorph} :
    Set (OpenPartialHomeomorph RiemannSphere ℂ)) ↔
      e = affineOpenPartialHomeomorph ∨ e = inftyOpenPartialHomeomorph
  simp

instance : IsManifold 𝓘(ℂ) 1 RiemannSphere := by
  sorry

end RiemannSphere

section

/-- Theorem VI.4-extra-13. Fundamental theorem: any simply connected complex manifold `X` is
biholomorphic to the canonical Riemann sphere, the complex plane, or the unit disc `𝔻`. -/
theorem simply_connected_complex_manifold_uniformization
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    [SimplyConnectedSpace X] :
    Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) ∨
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻) := sorry

end
