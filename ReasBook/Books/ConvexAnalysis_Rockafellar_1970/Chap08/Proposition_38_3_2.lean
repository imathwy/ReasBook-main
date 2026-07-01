import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_3_1

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.3.2 identifies the image of a function under the convex
  indicator bifunction of a linear map `A` with the ordinary Chapter 1 image of that function
  under `A`.
- `core/canonical`: the two existing owners are `Bifunction.image` for bifunction images and
  `Function.linearImage` for fiberwise infima along a linear map; the singleton-indicator
  bifunction attached to `A` is the graph owner `graphIndicator 𝕜 A`.
- `bridge/view`: this item is therefore a direct equality between existing owner-level
  constructions, not a place to introduce a new wrapper for “image under an indicator bifunction”.

Domain-style sampling used here:
- `Bifunction.image` from `Chap08.Definition_38_0_4`;
- `Bifunction.graphIndicator` from `Chap06.Definition_6_29_9`;
- `Function.linearImage` and `Function.linearImage_eq_sInf_image` from `Chap01.Theorem_5_7`.

Primitive data vs derived API:
- primitive source data: a linear map `A : U →ₗ[𝕜] X` and a function `f : U → WithBotTop 𝕜`;
- primitive owners reused directly: `image`, `graphIndicator`, and `Function.linearImage`;
- derived API here: only the bridge equality between the two source-facing image constructions.

Source-faithful assumption note: Rockafellar states the result for a function that does not take
the value `-∞`. In the project's `WithBotTop 𝕜` owner layer, that hypothesis is the non-bottom
condition `∀ u, f u ≠ ⊥`; convexity is unused in this identity.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: expand `image (graphIndicator 𝕜 A) f` pointwise using `image_apply`. For a
-- fixed `x`, the singleton-indicator term is `0` exactly on the fiber `A u = x` and `⊤`
-- otherwise, so the infimum reduces to the fiberwise infimum of `f`. That is exactly the Chapter
-- 1 owner `Function.linearImage A f`.
/-- Proposition 38.3.2: for the singleton-indicator bifunction of a linear map `A`, the Chapter 8
image of `f` agrees with the Chapter 1 linear image `A ◁ f`; equivalently, the infimum defining
`image (graphIndicator 𝕜 A) f` is taken over the fiber `A u = x` provided `f` never takes the
value `-∞`. -/
theorem image_graphIndicator_eq_linearImage
    (A : U →ₗ[𝕜] X) (f : U → WithBotTop 𝕜) (hf : ∀ u, f u ≠ ⊥) :
    image (graphIndicator 𝕜 A) f = A ◁ f := by
  classical
  funext x
  let fiber : Set U := {u : U | A u = x}
  calc
    image (graphIndicator 𝕜 A) f x
        = ⨅ u : U, if u ∈ fiber then f u else ⊤ := by
            rw [image_apply]
            apply iInf_congr
            intro u
            by_cases hu : u ∈ fiber
            · have hux : A u = x := by
                simpa [fiber] using hu
              have hxu : x = A u := hux.symm
              calc
                f u + graphIndicator 𝕜 A u x
                    = f u + (if x = A u then (0 : WithBotTop 𝕜) else ⊤) := by
                        rw [graphIndicator_cases]
                _ = f u := by simp [hxu]
                _ = if u ∈ fiber then f u else ⊤ := by simp [hu]
            · have hux : A u ≠ x := by
                simpa [fiber] using hu
              have hxu : x ≠ A u := by
                simpa [eq_comm] using hux
              calc
                f u + graphIndicator 𝕜 A u x
                    = f u + (if x = A u then (0 : WithBotTop 𝕜) else ⊤) := by
                        rw [graphIndicator_cases]
                _ = ⊤ := by
                      rw [if_neg hxu]
                      exact (WithBotTop.add_top_iff_ne_bot).2 (hf u)
                _ = if u ∈ fiber then f u else ⊤ := by simp [hu]
    _ = ⨅ u ∈ fiber, f u := by
          rw [iInf_ite]
          simp
    _ = (A ◁ f) x := by
          by_cases hfiber : fiber.Nonempty
          · letI : Nonempty U := ⟨hfiber.some⟩
            have hbelow : BddBelow (Set.range fun u : fiber ↦ f u) := by
              refine ⟨⊥, ?_⟩
              rintro _ ⟨u, rfl⟩
              exact bot_le
            have htop : ⨅ u : fiber, f u ≤ sInf (∅ : Set (WithBotTop 𝕜)) := by
              simp
            rw [Function.linearImage_eq_sInf_image]
            simpa [fiber] using (csInf_image hfiber hbelow htop).symm
          · rw [Function.linearImage_eq_sInf_image]
            have hempty : fiber = ∅ := Set.not_nonempty_iff_eq_empty.mp hfiber
            simp [fiber, hempty]

end

end Bifunction
