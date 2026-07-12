import Mathlib

open scoped Manifold

/- 
Domain sampling:
* primary domain: the canonical Riemann sphere as a one-dimensional complex manifold;
* source-facing layer: the chapter-local owner `RiemannSphere` together with its two standard
  charts and their transition regularity;
* core/canonical owner declarations inspected before this extraction:
  - mathlib's canonical one-point compactification carrier `OnePoint ℂ`;
  - mathlib's owner API `OnePoint.isOpenEmbedding_coe`,
    `OnePoint.continuousAt_infty'`, and `OnePoint.tendsto_coe_infty`;
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

/-- The affine chart is an open partial homeomorphism from the finite sphere to `ℂ`. -/
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

/-- The inversion chart around `∞` is an open partial homeomorphism to `ℂ`. -/
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

/-- The canonical affine and inversion charts define the complex-manifold atlas on the sphere. -/
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

/-- The sphere atlas has exactly the affine and `∞` charts. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph RiemannSphere ℂ} :
    e ∈ atlas ℂ RiemannSphere ↔
      e = affineOpenPartialHomeomorph ∨ e = inftyOpenPartialHomeomorph := by
  change e ∈ ({affineOpenPartialHomeomorph, inftyOpenPartialHomeomorph} :
    Set (OpenPartialHomeomorph RiemannSphere ℂ)) ↔
      e = affineOpenPartialHomeomorph ∨ e = inftyOpenPartialHomeomorph
  simp

/-- The affine-to-infinity chart change is `C^1` on the punctured overlap. -/
lemma affineInftyTransition_contDiffOn :
    ContDiffOn ℂ 1
      ((𝓘(ℂ)) ∘
        ↑(affineOpenPartialHomeomorph.symm.trans inftyOpenPartialHomeomorph) ∘
        ↑(𝓘(ℂ)).symm)
      (↑(𝓘(ℂ)).symm ⁻¹'
          (affineOpenPartialHomeomorph.symm.trans inftyOpenPartialHomeomorph).source ∩
        Set.range ↑(𝓘(ℂ))) := by
  -- The mixed chart change is inversion, so the standard `C^1` theorem for `z ↦ z⁻¹` applies.
  refine
    (contDiffOn_inv (𝕜 := ℂ) (𝕜' := ℂ) (n := (1 : WithTop ℕ∞))).congr_mono ?_ ?_
  · intro z hz
    simp [affineOpenPartialHomeomorph, affineChart, inftyOpenPartialHomeomorph, inftyChart,
      Function.comp_def]
  · intro z hz
    simpa [affineOpenPartialHomeomorph, affineChart, inftyOpenPartialHomeomorph, inftyChart,
      OpenPartialHomeomorph.trans_source, Function.comp_def] using hz

/-- The infinity-to-affine chart change is `C^1` on the punctured overlap. -/
lemma inftyAffineTransition_contDiffOn :
    ContDiffOn ℂ 1
      ((𝓘(ℂ)) ∘
        ↑(inftyOpenPartialHomeomorph.symm.trans affineOpenPartialHomeomorph) ∘
        ↑(𝓘(ℂ)).symm)
      (↑(𝓘(ℂ)).symm ⁻¹'
          (inftyOpenPartialHomeomorph.symm.trans affineOpenPartialHomeomorph).source ∩
        Set.range ↑(𝓘(ℂ))) := by
  -- The reverse mixed change is the same inversion map, written through `inftyInv`.
  refine
    (contDiffOn_inv (𝕜 := ℂ) (𝕜' := ℂ) (n := (1 : WithTop ℕ∞))).congr_mono ?_ ?_
  · intro z hz
    have hz0 : z ≠ 0 := by
      simpa [inftyOpenPartialHomeomorph, inftyChart, inftyInv, affineOpenPartialHomeomorph,
        affineChart, OpenPartialHomeomorph.trans_source, Function.comp_def] using hz
    simp [inftyOpenPartialHomeomorph, inftyChart, inftyInv, affineOpenPartialHomeomorph,
      affineChart, Function.comp_def, hz0]
  · intro z hz
    simpa [inftyOpenPartialHomeomorph, inftyChart, inftyInv, affineOpenPartialHomeomorph,
      affineChart, OpenPartialHomeomorph.trans_source, Function.comp_def] using hz

/-- Every overlap of the two canonical sphere charts is `C^1`. -/
lemma chartTransition_contDiffOn {e e' : OpenPartialHomeomorph RiemannSphere ℂ}
    (he : e ∈ atlas ℂ RiemannSphere) (he' : e' ∈ atlas ℂ RiemannSphere) :
    ContDiffOn ℂ 1
      ((𝓘(ℂ)) ∘ ↑(e.symm.trans e') ∘ ↑(𝓘(ℂ)).symm)
      (↑(𝓘(ℂ)).symm ⁻¹' (e.symm.trans e').source ∩ Set.range ↑(𝓘(ℂ))) := by
  rcases mem_atlas_iff.mp he with rfl | rfl
  · rcases mem_atlas_iff.mp he' with rfl | rfl
    · -- The affine chart overlaps with itself by the identity map.
      refine
        (contDiff_id.contDiffOn : ContDiffOn ℂ 1 id (Set.univ : Set ℂ)).congr_mono ?_ ?_
      · intro z hz
        have hz' :
            z ∈ affineOpenPartialHomeomorph.target ∧
              affineOpenPartialHomeomorph.symm z ∈ affineOpenPartialHomeomorph.source := by
          simpa [OpenPartialHomeomorph.trans_source, Function.comp_def] using hz
        simpa [Function.comp_def] using affineOpenPartialHomeomorph.right_inv hz'.1
      · intro z hz
        simp
    · exact affineInftyTransition_contDiffOn
  · rcases mem_atlas_iff.mp he' with rfl | rfl
    · exact inftyAffineTransition_contDiffOn
    · -- The infinity chart overlaps with itself by the identity map.
      refine
        (contDiff_id.contDiffOn : ContDiffOn ℂ 1 id (Set.univ : Set ℂ)).congr_mono ?_ ?_
      · intro z hz
        have hz' :
            z ∈ inftyOpenPartialHomeomorph.target ∧
              inftyOpenPartialHomeomorph.symm z ∈ inftyOpenPartialHomeomorph.source := by
          simpa [OpenPartialHomeomorph.trans_source, Function.comp_def] using hz
        simpa [Function.comp_def] using inftyOpenPartialHomeomorph.right_inv hz'.1
      · intro z hz
        simp

/-- The canonical sphere atlas satisfies the manifold transition regularity condition. -/
instance : IsManifold 𝓘(ℂ) 1 RiemannSphere := by
  -- The atlas has only two charts, and every overlap is either identity or inversion.
  exact isManifold_of_contDiffOn 𝓘(ℂ) 1 RiemannSphere fun e e' he he' ↦
    chartTransition_contDiffOn he he'

end RiemannSphere
