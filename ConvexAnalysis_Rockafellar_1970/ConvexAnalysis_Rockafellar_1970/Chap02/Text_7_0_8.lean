import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_9
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "reciprocalIoiExtension" =>
  Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.8 is an existence remark asserting that closed proper convexity does
  not force the effective domain to be closed.
- `core/canonical`: the existing owner predicates are `IsClosedProperConvex[𝕜]`, the
  effective-domain notation `dom(·)`, and ambient closedness `IsClosed`.
- `bridge/view`: the canonical witness is the direct owner
  `Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))`, and the pure existence statement
  is a direct corollary.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `dom(·)` from `Chap01.Definition_4_4`, imported transitively there;
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn` and the reciprocal closedness
  theorem `lowerSemicontinuous_reciprocal_Ioi_extension` from `Text_7_0_9`;
- the convex-extension bridge `isConvex_toWithBotTopOn_iff` from `Chap01.Remark_4_4_5`.

Layer target: `source-facing`. The theorem records the textbook possibility statement directly,
while exposing the canonical reciprocal-on-`(0, ∞)` witness at the owner surface.
-/

-- Proof sketch: for
-- `f := Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))`, convexity comes from
-- `convexOn_zpow (-1)` plus `isConvex_toWithBotTopOn_iff`, closedness from Text 7.0.9, properness
-- from `f 1 = 1` and absence of `⊥`, and `dom(f) = Set.Ioi 0`, which is not closed in `𝕜`.
/-- Text 7.0.8 (canonical witness form): the reciprocal extension
`Function.toWithBotTopOn (fun x ↦ x⁻¹) (Set.Ioi 0)` is closed proper convex, while its effective
domain is not closed. -/
theorem reciprocal_Ioi_extension_isClosedProperConvex_and_nonclosed_domain :
    IsClosedProperConvex[𝕜] reciprocalIoiExtension ∧
      ¬ IsClosed (dom(reciprocalIoiExtension)) := by
  let f : 𝕜 → WithBotTop 𝕜 := reciprocalIoiExtension
  have hconvOn_inv : ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun x : 𝕜 ↦ x⁻¹) := by
    simpa [one_div, zpow_neg_one] using
      (convexOn_zpow (-1 : ℤ) :
        ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ t ^ (-1 : ℤ)))
  have hconv : f.IsConvex 𝕜 := by
    simpa [f, reciprocalIoiExtension] using
      (isConvex_toWithBotTopOn_iff
        (C := Set.Ioi (0 : 𝕜)) (f := fun x : 𝕜 ↦ x⁻¹)).2 hconvOn_inv
  have hproper : f.IsProper := by
    rw [Function.isProper_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · change (1 : 𝕜) ∈ dom(reciprocalIoiExtension)
      rw [effectiveDomain_reciprocal_Ioi_extension]
      simp
    · intro x
      simpa [f] using reciprocal_Ioi_extension_ne_bot x
  have hclosed : LowerSemicontinuous f := by
    simpa [f, reciprocalIoiExtension] using
      (lowerSemicontinuous_reciprocal_Ioi_extension :
        LowerSemicontinuous reciprocalIoiExtension)
  have hnonclosed_dom : ¬ IsClosed (dom(f)) := by
    intro hclosed_dom
    have hzero_closure : (0 : 𝕜) ∈ closure (dom(f)) := by
      simp [f, effectiveDomain_reciprocal_Ioi_extension, closure_Ioi]
    have hzero_dom : (0 : 𝕜) ∈ dom(f) := by
      simpa [hclosed_dom.closure_eq] using hzero_closure
    have hzero_pos : (0 : 𝕜) < 0 := by
      have hzero_Ioi := hzero_dom
      simp [f, effectiveDomain_reciprocal_Ioi_extension] at hzero_Ioi
    exact (lt_irrefl (0 : 𝕜)) hzero_pos
  refine ⟨?_, ?_⟩
  · have hf : IsClosedProperConvex[𝕜] f := ⟨hconv, hproper, hclosed⟩
    simpa [f] using hf
  · simpa [f] using hnonclosed_dom

/-- Text 7.0.8 (existence form): there exists a closed proper convex `WithBotTop 𝕜`-valued
function on `𝕜` whose effective domain is not closed. -/
theorem exists_closedProperConvex_with_nonclosed_domain :
    ∃ f : 𝕜 → WithBotTop 𝕜, IsClosedProperConvex[𝕜] f ∧ ¬ IsClosed (dom(f)) := by
  refine ⟨reciprocalIoiExtension, ?_⟩
  simpa using reciprocal_Ioi_extension_isClosedProperConvex_and_nonclosed_domain

end
