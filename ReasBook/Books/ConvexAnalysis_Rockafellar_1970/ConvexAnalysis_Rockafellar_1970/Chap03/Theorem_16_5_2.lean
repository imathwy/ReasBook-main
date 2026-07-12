import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.2 identifies the conjugate of the pointwise supremum of the
  closures `cl fᵢ` with the closure of the convex hull of the conjugates `fᵢ*`.
- `core/canonical`: the project owner constructions are `convexConjugate`,
  `lowerSemicontinuousHull`, and the family convex-hull owner `conv(⨅ i, f i)`.
- `bridge/view`: Rockafellar's `sup {cl fᵢ | i ∈ I}` is rendered by the pointwise supremum
  `⨆ i, cl(f i)`, while `cl (conv {fᵢ* | i ∈ I})` is rendered by
  `cl(conv(⨅ i, (f i)⋆))`.

Domain-style sampling used here:
- `convexConjugate_conv_iInf_eq_iSup`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- `Function.isGreatest_conv_iInf_minorant`;
- `lowerSemicontinuousHull`;
- `conv`.

Primitive data vs derived API:
- primitive inputs: an indexed family `f : I → E → WithBotTop 𝕜`;
- source-essential hypothesis: each `f i` is convex, which is needed to identify `fᵢ**` with
  `cl fᵢ`;
- derived API: the conjugacy identity between the supremum of the closures and the closure of the
  convex hull of the conjugates.

Layer target: `source-facing`, stated directly through the existing owner constructions. The source
properness assumption is redundant for this identity, but convexity is not. The source's `R^n`
wording is rendered on the canonical finite-dimensional scalar-field owner layer with continuous
linear self-pairing. The codomain surface is the chapter's canonical `WithBotTop 𝕜` layer.
-/

-- Proof sketch: apply Theorem 16.5.1 to the family `fun i ↦ convexConjugate (f i)` to get
-- `(conv {fᵢ*})* = ⨆ i, fᵢ**`, rendered as `(conv(⨅ i, (f i)⋆))⋆ = ⨆ i, ((f i)⋆)⋆`.
-- Use Theorem 12.2 to rewrite each `fᵢ**` as
-- `lowerSemicontinuousHull (f i)` under the convexity hypothesis. Then apply Theorem 12.2 again
-- to the convex function `conv(⨅ i, (f i)⋆)`, whose
-- biconjugate is the lower-semicontinuous hull of `conv {fᵢ*}`.
/-- Theorem 16.5.2: for a family of convex functions on a finite-dimensional scalar-field space
equipped with a continuous linear self-pairing, the conjugate of the pointwise supremum of the
closures `cl f_i`, represented here by `⨆ i, cl(f i)`, is the closure of the convex hull of the
conjugates `f_i*`, represented here as `cl (conv(⨅ i, (f i)⋆))`. The source properness assumption
is redundant for this identity. -/
theorem
    convexConjugate_iSup_cl_eq_cl_conv_iInf_convexConjugate_of_convex
    (f : I → E → WithBotTop 𝕜) (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    ((⨆ i, cl(f i))⋆ : E → WithBotTop 𝕜) = cl(conv(⨅ i, (f i)⋆)) := by
  let g : I → E → WithBotTop 𝕜 := fun i ↦ (f i)⋆
  have hcl : ∀ i : I, cl(f i) = (f i)⋆⋆ := by
    intro i
    simpa using ((hf_convex i).biconjugate_eq_lowerSemicontinuousHull).symm
  have hconj :
      (conv(⨅ i : I, g i))⋆ = (⨆ i : I, (f i)⋆⋆) := by
    simpa [g] using
      (convexConjugate_conv_iInf_eq_iSup (f := g))
  have hiSup_cl :
      (⨆ i : I, cl(f i)) = (conv(⨅ i : I, g i))⋆ := by
    calc
      (⨆ i : I, cl(f i)) = (⨆ i : I, (f i)⋆⋆) := by
        simp [hcl]
      _ = (conv(⨅ i : I, g i))⋆ := by
        simpa using hconj.symm
  have hconvex : (conv(⨅ i : I, g i)).IsConvex 𝕜 :=
    (Function.isGreatest_conv_iInf_minorant g).1.1
  calc
    (⨆ i : I, cl(f i))⋆ = ((conv(⨅ i : I, g i))⋆)⋆ := by
      rw [hiSup_cl]
    _ = cl(conv(⨅ i : I, g i)) := by
      simpa using hconvex.biconjugate_eq_lowerSemicontinuousHull
    _ = cl(conv(⨅ i : I, (f i)⋆)) := by
      simp [g]

end
