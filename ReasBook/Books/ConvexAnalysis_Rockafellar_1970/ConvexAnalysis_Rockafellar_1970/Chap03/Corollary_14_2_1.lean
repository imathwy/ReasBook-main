import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped PolarCone Rockafellar

variable {𝕜 E : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [ClosedIciTopology 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜] [FloorRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 14.2.1 states that for a nonempty closed convex set `C`, the polar of
  the barrier cone of `C` is exactly the recession cone of `C`.
- `core/canonical`: the owner abstractions already present in the project are the set-valued
  operators `barrierCone`, `polarCone`, and `recessionCone`, together with the chapter owner
  theorem
  `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate`.
- `bridge/view`: the source proof specializes that owner theorem to `supportFunction C`.
  `Text_13_0_4` identifies the effective domain of `supportFunction C` with `barrierCone C`,
  nonemptiness of `C` gives the owner-side properness of `supportFunction C`, Theorem 13.2
  rewrites the conjugate of `supportFunction C` as `indicatorFunction C`, and Theorem 8.7
  identifies the resulting function-side recession cone directly with the set-side recession cone
  `0⁺ C`.

Domain-style sampling used here:
- `barrierCone_eq_effectiveDomain_supportFunction` from `Text_13_0_4`;
- `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate`
  from `Theorem_14_2`;
- `supportFunction_def` from `Defintion_4_8_2`;
- `convexConjugate_supportFunction_eq_indicatorFunction` from `Theorem_13_2`;
- `functionRecessionCone_indicatorFunction_eq_recessionCone` from `Theorem_8_7`.

Primitive data vs derived API:
- primitive input: the subset `C : Set E`;
- owner hypotheses: nonemptiness, closedness, and convexity of `C`;
- derived output: the direct set equality `(barrierCone C)ᵒ = 0⁺ C`.

Layer target: `source-facing`, stated directly with the chapter owners for barrier cones, polars,
and recession cones, while deriving the result through the upstream owner theorem instead of
rebuilding a parallel local support-function wrapper.

Ambient refinement: the supporting owner theorems already live on arbitrary finite-dimensional
ordered-field pairing spaces with continuous symmetric pairing, so the corollary is stated at that
intrinsic layer rather than the concrete coordinate model `EuclideanSpace ℝ (Fin n)`.
-/

-- Proof sketch: apply the owner theorem
-- `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate` to
-- `supportFunction C`. The bridge `barrierCone_eq_effectiveDomain_supportFunction` identifies its
-- effective domain with `barrierCone C`, and the polar of a generated cone simplifies directly to
-- the polar of the underlying set in the source-facing polar owner. Nonemptiness of `C` gives the
-- properness of `supportFunction C` directly from `supportFunction_def`. Theorem 13.2 rewrites the
-- conjugate of `supportFunction C` as `indicatorFunction C`, and the Chapter 8 owner theorem
-- `functionRecessionCone_indicatorFunction_eq_recessionCone` finishes the source-facing set
-- identity.
/-- Corollary 14.2.1: the polar `(barrierCone C)ᵒ` of the barrier cone of a nonempty closed convex
set `C` is the recession cone of `C`. Specializing to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `R^n` statement. -/
theorem polarCone_barrierCone_eq_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    ((((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E)) = 0⁺[𝕜] C := by
  have hsupport_proper : (δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜).IsProper := by
    rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hC_nonempty with ⟨y, hy⟩
      refine ⟨(0 : E), ?_⟩
      rw [mem_effectiveDomain]
      have h_upper : δᵛ[WithBotTop 𝕜]((0 : E) | C) ≤ (0 : WithBotTop 𝕜) := by
        rw [supportFunction_def]
        refine iSup_le ?_
        intro z
        change ((⟪(0 : E), (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ 0
        simp
      have h_lower : (0 : WithBotTop 𝕜) ≤ δᵛ[WithBotTop 𝕜]((0 : E) | C) := by
        calc
          (0 : WithBotTop 𝕜) = ((⟪(0 : E), y⟫ₚ : 𝕜) : WithBotTop 𝕜) := by simp
          _ ≤ δᵛ[WithBotTop 𝕜]((0 : E) | C) := by
            rw [supportFunction_def]
            exact le_iSup (fun z : C ↦ ((⟪(0 : E), (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜)) ⟨y, hy⟩
      have h_eq : δᵛ[WithBotTop 𝕜]((0 : E) | C) = 0 := le_antisymm h_upper h_lower
      have htop : δᵛ[WithBotTop 𝕜]((0 : E) | C) < ⊤ := by
        rw [h_eq]
        exact WithBotTop.coe_lt_top 0
      exact htop
    · intro x
      rcases hC_nonempty with ⟨y, hy⟩
      have hbot : (⊥ : WithBotTop 𝕜) < δᵛ[WithBotTop 𝕜](x | C) := by
        rw [supportFunction_def]
        exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _) <|
          (le_iSup (fun z : C ↦ ((⟪x, (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜)) ⟨y, hy⟩)
      exact ne_of_gt hbot
  calc
    (((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
        Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := by
      let sDir : E → WithBotTop 𝕜 := fun x ↦
        @supportFunction E E (WithBotTop 𝕜) WithBot.instSupSet
          (@instHasPairingWithBotTop E E 𝕜 instHasPairingOfHasLinearPairing) C x
      let sSwp : E → WithBotTop 𝕜 := fun x ↦
        @supportFunction E E (WithBotTop 𝕜) WithBot.instSupSet
          (@instHasPairingWithBotTop E E 𝕜 instHasPairingYX) C x
      have hsupp_eq : sDir = sSwp := by
        funext x
        simp only [sDir, sSwp, supportFunction_def]
        refine iSup_congr ?_
        intro y
        have hpair : (⟪x, (y : E)⟫ₚ : 𝕜) = ⟪(y : E), x⟫ₚ := by
          simpa using (HasPairingSwap.pairing_swap (x := x) (y := (y : E)))
        exact congrArg (fun t : 𝕜 ↦ (t : WithBotTop 𝕜)) hpair
      have hdom_eq : dom(sDir) = dom(sSwp) := by
        simpa [hsupp_eq]
      have hbarrier : (barr[𝕜](C) : Set E) = dom(sSwp) := by
        simpa [sSwp] using
          (barrierCone_eq_effectiveDomain_supportFunction (R := 𝕜) (X := E) (Y := E) C)
      have hmain :
          (((dom(sDir))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
            Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := by
        simpa [sDir] using
          polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate
            (δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜) (Function.isConvex_supportFunction C)
            hsupport_proper
      calc
        (((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
            (((dom(sSwp))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) := by
          simpa [hbarrier]
        _ = (((dom(sDir))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) := by simpa [hdom_eq]
        _ = Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := hmain
    _ = Function.recessionCone (((δ[𝕜](· | C) : E → WithBotTop 𝕜))₀⁺) := by
      rw [convexConjugate_supportFunction_eq_indicatorFunction C hC_convex hC_closed]
    _ = 0⁺[𝕜] C := by
      simpa using
        (functionRecessionCone_indicatorFunction_eq_recessionCone
          (α := 𝕜) (C := C) hC_convex)

end
