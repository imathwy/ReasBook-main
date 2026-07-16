import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_10

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {X : Type u} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.11 identifies the scalar `α`-sublevel set of the closure `cl(f)` with
  the intersection of the closures of the scalar `μ`-sublevel sets of `f` over all `μ > α`.
- `core/canonical`: the owner is still the Chapter 2 lower-semicontinuous hull
  `lowerSemicontinuousHull`, written `cl(·)`, together with ambient set closure and the canonical
  scalar sublevel sets as preimages `f ⁻¹' Set.Iic a`.
- `bridge/view`: this file first records the primitive bridge "if `cl(f)` is identified pointwise
  with neighborhood liminf, then the source set identity follows"; Text 7.0.10 then supplies that
  liminf bridge for the chapter owner.

Domain-style sampling used here:
- `lowerSemicontinuousHull` / `cl(·)` from `Text_7_0_4`;
- `lowerSemicontinuousHull_apply_eq_liminf_nhds` from `Text_7_0_10`;
- `Filter.liminf_le_iff` and `mem_closure_iff_frequently` from mathlib's filter/topology API.

Layer target: `source-facing`, with a primitive liminf-bridge lemma on canonical preimage owners
and a derived source theorem on textbook set-builder sublevel notation.
-/

-- Proof sketch: assume `g` is identified pointwise with neighborhood liminf of `f`. If
-- `g x ≤ α`, every `μ > α` has neighborhood liminf of `f` at `x` strictly below `μ`, so every
-- neighborhood of `x` meets the `μ`-sublevel set of `f`; hence `x` lies in the closure of that
-- sublevel set. Conversely, if `x` belongs to every such closure, then for each `μ > α` there
-- are points arbitrarily close to `x` with `f ≤ μ`, forcing `liminf f (nhds x) ≤ μ`; letting
-- `μ ↓ α` yields `g x ≤ α`.
/-- Primitive liminf bridge: if `g` is identified pointwise with the neighborhood liminf of `f`,
then the closed scalar `α`-sublevel preimage of `g` is the intersection of closures of higher
closed-sublevel preimages of `f`. -/
theorem sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f g : X → WithTopBot 𝕜) (α : 𝕜)
    (hliminf : g = fun x ↦ Filter.liminf f (nhds x)) :
    g ⁻¹' Set.Iic (α : WithTopBot 𝕜) =
      ⋂ μ : Set.Ioi (α : WithTopBot 𝕜), closure (f ⁻¹' Set.Iic (μ : WithTopBot 𝕜)) := by
  ext x
  have liminf_le_iff {β : WithTopBot 𝕜} :
      Filter.liminf f (nhds x) ≤ β ↔ ∀ y > β, ∃ᶠ z in nhds x, f z < y :=
    Filter.liminf_le_iff Filter.isCobounded_ge_of_top Filter.isBounded_ge_of_bot
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro μ
    have hx' : g x ≤ (α : WithTopBot 𝕜) := by
      simpa [Set.mem_preimage, Set.mem_Iic] using hx
    have hlim : Filter.liminf f (nhds x) ≤ (α : WithTopBot 𝕜) := by
      simpa [hliminf] using hx'
    have hαμ : (α : WithTopBot 𝕜) < (μ : WithTopBot 𝕜) := μ.2
    have hfreq_lt : ∃ᶠ y in nhds x, f y < (μ : WithTopBot 𝕜) :=
      (liminf_le_iff.1 hlim) (μ : WithTopBot 𝕜) hαμ
    have hfreq_le : ∃ᶠ y in nhds x, f y ≤ (μ : WithTopBot 𝕜) :=
      hfreq_lt.mono (fun _ hy ↦ le_of_lt hy)
    exact (mem_closure_iff_frequently).2 <| by
      simpa [Set.mem_preimage, Set.mem_Iic] using hfreq_le
  · intro hx
    have hfreq_le :
        ∀ μ : Set.Ioi (α : WithTopBot 𝕜), ∃ᶠ y in nhds x, f y ≤ (μ : WithTopBot 𝕜) := by
      intro μ
      have hμclosure : x ∈ closure (f ⁻¹' Set.Iic (μ : WithTopBot 𝕜)) :=
        (Set.mem_iInter.mp hx) μ
      exact (mem_closure_iff_frequently).1 hμclosure |>.mono <| by
        intro y hy
        simpa [Set.mem_preimage, Set.mem_Iic] using hy
    have hlim : Filter.liminf f (nhds x) ≤ (α : WithTopBot 𝕜) := by
      refine liminf_le_iff.2 ?_
      intro y hy
      by_cases hy_top : y = (⊤ : WithTopBot 𝕜)
      · obtain ⟨μ, hαμ⟩ := exists_gt α
        let μ' : Set.Ioi (α : WithTopBot 𝕜) := ⟨(μ : WithTopBot 𝕜),
          WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hαμ)⟩
        have hμfreq := hfreq_le μ'
        have hμlt_top : (μ' : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
          exact lt_top_iff_ne_top.mpr (by
            exact WithTop.coe_ne_top)
        exact hμfreq.mono (fun z hz ↦ lt_of_le_of_lt hz (hy_top ▸ hμlt_top))
      · have hy_bot : y ≠ (⊥ : WithTopBot 𝕜) := by
          intro hy_bot
          simp [hy_bot] at hy
        induction hν : y using WithTop.recTopCoe with
        | top => exact (hy_top hν).elim
        | coe y' =>
            induction y' using WithBot.recBotCoe with
            | bot => exact (hy_bot hν).elim
            | coe ν =>
                have hαν : α < ν := by
                  exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp (by simpa [hν] using hy))
                obtain ⟨μ, hαμ, hμν⟩ := exists_between hαν
                let μ' : Set.Ioi (α : WithTopBot 𝕜) :=
                  ⟨(μ : WithTopBot 𝕜),
                    WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hαμ)⟩
                have hμfreq := hfreq_le μ'
                have hμ'ν : (μ' : WithTopBot 𝕜) < (ν : WithTopBot 𝕜) := by
                  exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hμν)
                exact hμfreq.mono (fun z hz ↦ lt_of_le_of_lt hz (by simpa [hν] using hμ'ν))
    have hx' : g x ≤ (α : WithTopBot 𝕜) := by
      simpa [hliminf] using hlim
    simpa [Set.mem_preimage, Set.mem_Iic] using hx'

variable [TopologicalSpace 𝕜]

/-- Bridge-level specialization to Rockafellar's closure owner `cl(·)`. -/
theorem lowerSemicontinuousHull_sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f : X → WithTopBot 𝕜) (α : 𝕜)
    (hliminf : cl(f) = fun x ↦ Filter.liminf f (nhds x)) :
    (cl(f)) ⁻¹' Set.Iic (α : WithTopBot 𝕜) =
      ⋂ μ : Set.Ioi (α : WithTopBot 𝕜), closure (f ⁻¹' Set.Iic (μ : WithTopBot 𝕜)) := by
  simpa using sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f := f) (g := cl(f)) (α := α) (hliminf := hliminf)

variable [OrderTopology 𝕜]
variable [NoBotOrder 𝕜]

/-- Text 7.0.11: for each scalar `α`, the closed `α`-sublevel set of the closure `cl(f)` is the
intersection of the closures of the higher closed scalar sublevel sets of `f`. -/
theorem lowerSemicontinuousHull_sublevel_eq_iInter_closure_higher_sublevels
    (f : X → WithTopBot 𝕜) (α : 𝕜) :
    {x | cl(f) x ≤ α} =
      ⋂ μ : Set.Ioi (α : WithTopBot 𝕜), closure {x | f x ≤ (μ : WithTopBot 𝕜)} := by
  simpa [Set.ext_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic] using
    (lowerSemicontinuousHull_sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
      (f := f) (α := α)
      (hliminf := lowerSemicontinuousHull_eq_liminf_nhds (f := f)))

end
