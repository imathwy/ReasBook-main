import Mathlib
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology translate

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Proof sketch: translate the punctured-neighborhood analyticity condition from `z₀` to `0`
-- using the analytic invariance of translation, and transport the failure of meromorphicity
-- through the biholomorphic change of variables `z ↦ z + z₀`.
/-- Remark III.4-extra-8: translating the variable reduces the case of an essential singularity at
`z₀` to the case of an essential singularity at the origin. -/
theorem essential_singularity_at_iff_translate_to_zero {f : 𝕜 → E} {z₀ : 𝕜} :
    HasEssentialSingularityAt f z₀ ↔
      HasEssentialSingularityAt (τ (-z₀) f) 0 := by
  have htranslate :
      HasEssentialSingularityAt f z₀ ↔
        HasEssentialSingularityAt (fun z ↦ f (z + z₀)) 0 := by
    let g : 𝕜 → 𝕜 := fun z ↦ z + z₀
    let t : 𝕜 → 𝕜 := fun z ↦ z - z₀
    have hmap : Filter.map g (𝓝[≠] (0 : 𝕜)) = 𝓝[≠] z₀ := by
      convert
        (Filter.map_add_right_nhdsNE :
          Filter.map (fun z : 𝕜 ↦ z + z₀) (𝓝[≠] (0 : 𝕜)) = 𝓝[≠] ((0 : 𝕜) + z₀)) using 1
      simp
    have hg : AnalyticAt 𝕜 g 0 := by
      simpa [g] using (show AnalyticAt 𝕜 (fun z : 𝕜 ↦ z + z₀) 0 by fun_prop)
    have hsub : AnalyticAt 𝕜 t z₀ := by
      simpa [t] using (show AnalyticAt 𝕜 (fun z : 𝕜 ↦ z - z₀) z₀ by fun_prop)
    have hmero : MeromorphicAt (f ∘ g) 0 ↔ MeromorphicAt f z₀ := by
      constructor
      · intro hf
        have hzero : t z₀ = 0 := by simp [t]
        rw [← hzero] at hf
        refine (hf.comp_analyticAt hsub).congr ?_
        filter_upwards with z
        have hz' : (z - z₀) + z₀ = z := by
          abel
        exact by simp [Function.comp, g, t, hz']
      · intro hf
        have hg0 : g 0 = z₀ := by simp [g]
        rw [← hg0] at hf
        simpa [Function.comp, g] using hf.comp_analyticAt hg
    constructor
    · rintro ⟨ha, hm⟩
      refine ⟨?_, ?_⟩
      · have ha_map : ∀ᶠ z in Filter.map g (𝓝[≠] (0 : 𝕜)), AnalyticAt 𝕜 f z := by
          simpa [hmap] using ha
        have ha' : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), AnalyticAt 𝕜 f (z + z₀) := by
          simpa only [g, Filter.eventually_map] using ha_map
        exact ha'.mono fun z hz ↦ by
          simpa using hz.comp_sub (-z₀)
      · intro h
        exact hm <| hmero.mp <| by simpa [g] using h
    · rintro ⟨ha, hm⟩
      refine ⟨?_, ?_⟩
      · have ha0 : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), AnalyticAt 𝕜 f (z + z₀) := by
          exact ha.mono fun z hz ↦ by
            simpa [sub_eq_add_neg, add_assoc] using hz.comp_sub z₀
        have ha_map : ∀ᶠ z in Filter.map g (𝓝[≠] (0 : 𝕜)), AnalyticAt 𝕜 f z := by
          simpa only [g, Filter.eventually_map] using ha0
        simpa [hmap] using ha_map
      · intro h
        exact hm <| by simpa [g] using hmero.mpr h
  change HasEssentialSingularityAt f z₀ ↔
    HasEssentialSingularityAt (fun z ↦ f (z - (-z₀))) 0
  simpa [sub_eq_add_neg] using htranslate

end
