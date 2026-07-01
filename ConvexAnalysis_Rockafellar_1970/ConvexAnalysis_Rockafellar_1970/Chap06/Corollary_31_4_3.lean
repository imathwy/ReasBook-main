import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_13_3_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Remark_31_4_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_4

noncomputable section

open scoped Pointwise PolarCone Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜] [HasContinuousPairing E EStar 𝕜]
variable {h : E → 𝕜} {K : Set E}

local notation "hStar" => (((h.toWithBotTop)⋆ : EStar → WithBotTop 𝕜))
local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.4.3 is the translated Fenchel-duality identity over a closed convex
  cone, together with attainment of the two translated infima.
- `core/canonical`: the existing owner theorem is
  `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` from `Theorem_31_4`,
  together with its two attainment companions, the Chapter 3 co-finiteness owner
  `Function.IsCofinite`, the paired-duality finiteness bridge
  `convexConjugate_finite_everywhere_iff_isCofinite`, the canonical Fenchel conjugate owner
  `hStar : EStar → WithBotTop 𝕜`.
- `bridge/view`: the source dual cone `K*` is rendered by the reusable Chapter 14 bridge
  `K∗[𝕜] : Set EStar`.

Domain-style sampling used here:

- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification`,
  `exists_mem_isMinOn_convexConjugate_on_dualCone_of_primal_qualification`, and
  `exists_mem_isMinOn_on_cone_of_dual_qualification` from `Theorem_31_4`;
- `convexConjugate_finite_everywhere_iff_isCofinite` from `Corollary_13_3_1`;
- the project owners `Function.IsCofinite`, `convexConjugate`, and the cone-polar notation `Kᵒ`.

Primitive data vs derived API:

- primitive inputs: the finite scalar-valued function `h`, the canonical Chapter 3 owner
  `h.toWithBotTop.IsCofinite` encoding the closed/proper/convex and recession data used
  downstream, a closed convex cone `K`, and translation data `z : E`, `zStar : EStar`;
- derived API: the translated zero-gap identity and the two attainment clauses. The source's
  printed right-hand side `⟨z, x*⟩` is treated as the evident bound-variable typo and rendered as
  `⟪z, zStar⟫ₚ`.

Layer target: `source-facing`, stated directly on the translated primal and dual objectives rather
than introducing a local wrapper around Theorem 31.4.
-/

-- Proof sketch: apply Theorem 31.4 to the translated-tilted closed proper convex function
-- `f x = h (z + x) - ⟪x, zStar⟫ₚ`, whose effective domain is all of `E` because `h` is finite.
-- Corollary 13.3.1 turns co-finiteness of `h` into finiteness of `hStar` everywhere on the paired
-- dual carrier `EStar`, so the translated cone problem satisfies the required qualification. The
-- translated conjugate is
-- then rewritten by the existing bridge `convexConjugate_translate_sub_pairing`, with the
-- constant term moved to the right-hand side.
/-- Corollary 31.4.3: for a finite convex function `h` on a finite-dimensional normed space over
`𝕜`,
paired with a dual carrier `EStar`, whose canonical Chapter 3 lift `h.toWithBotTop` is
co-finite, and a nonempty closed convex cone `K`, the translated primal infimum over `K` plus
the translated dual infimum over `K∗[𝕜]` equals `⟪z, zStar⟫ₚ`. This corrects the evident
bound-variable typo in the source display, whose right-hand side should read `⟨z, z*⟩`. -/
theorem iInf_translate_sub_pairing_on_cone_add_iInf_translate_sub_pairing_on_dualCone_eq_pairing
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    (⨅ x : K, (((h (z + x) - ⟪x, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜))) +
        (⨅ xStar : (K∗[𝕜] : Set EStar),
          hStar (zStar + xStar) - ⟪z, (xStar : EStar)⟫ₚ) =
      (⟪z, zStar⟫ₚ : WithBotTop 𝕜) := sorry

-- Proof sketch: the dual relative-interior qualification in Theorem 31.4 is automatic because the
-- translated conjugate is finite everywhere by the Chapter 3 co-finiteness bridge, so
-- `riDom(f⋆) = Set.univ`; since `0 ∈ K∗[𝕜]`, the source dual cone is a nonempty convex cone and
-- therefore has nonempty intrinsic interior. Rewriting the dual minimizer for the conjugate of
-- the translated-tilted function gives the stated minimizer of the translated dual objective, so
-- no separate `K.Nonempty` binder is part of the public API.
/-- The translated dual infimum in Corollary 31.4.3 is attained on `K∗[𝕜]`. -/
theorem exists_mem_isMinOn_convexConjugate_translate_sub_pairing_on_dualCone
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar),
      IsMinOn
        (fun xStar : EStar ↦ hStar (zStar + xStar) - ⟪z, xStar⟫ₚ)
        (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: co-finiteness of `h` makes `hStar` finite everywhere, so the dual
-- relative-interior qualification in Theorem 31.4 is automatic for the translated-tilted
-- function `x ↦ h (z + x) - ⟪x, zStar⟫ₚ`. The primal attainment conclusion of Theorem 31.4
-- therefore yields a minimizer of the translated primal objective on `K`.
/-- The translated primal infimum in Corollary 31.4.3 is attained on `K`. -/
theorem exists_mem_isMinOn_translate_sub_pairing_on_cone
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    ∃ x ∈ K,
      IsMinOn (fun x : E ↦ (((h (z + x) - ⟪x, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜))) K x := sorry

end
