import Mathlib.Tactic.Recall
import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_29

noncomputable section

universe u v

open Function
open scoped Rockafellar

namespace Bifunction

section SliceDomain

variable {U : Type u} {X : Type v} {α : Type*}
variable [Preorder α]

-- Proof sketch: unpack graph properness of `uncurry F` to get a point `(u, x)` where
-- `F u x` is finite, then read this directly as membership in `dom F`.
/-- The source domain `dom F` is nonempty under the graph-properness hypothesis of
Text 34.2.3. -/
theorem dom_nonempty_of_uncurry_isProper
    (F : U → X → WithBotTop α)
    (hF_proper : (uncurry F).IsProper) :
    (dom F).Nonempty := by
  rcases hF_proper.nonempty_dom with ⟨⟨u, x⟩, hx⟩
  refine ⟨u, (mem_dom_iff_exists).2 ?_⟩
  exact ⟨x, by simpa [uncurry] using hx⟩

end SliceDomain

section GraphProperness

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

local instance : Neg (WithBotTop ℝ) := WithBotTop.instNeg

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 34.2.3 says that if a closed convex bifunction `F` is proper, then its
  conjugate `F*` is proper, and consequently both source domains `dom F` and `dom F*` are
  nonempty.
- `core/canonical`: in Chapter 34, the properness notion used for this item is the graph-function
  owner `Function.IsProper (Function.uncurry F)`, while the source domains are the Chapter 6
  owner `dom F` and its adjoint-side specialization `dom (-adjoint X U F)`.
- `bridge/view`: the conjugate `F*` is rendered directly by the Chapter 6 adjoint owner
  `adjoint X U F`, and the nonemptiness of `dom F*` is rendered by
  `(dom (-adjoint X U F)).Nonempty`.

Primary mathematical domain:
- closed convex bifunctions, graph-function properness, and the corresponding source domain sets
  `dom F` and `dom (-adjoint X U F)`.

Domain-style sampling used here:
- `Bifunction.dom` and `Bifunction.mem_dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.adjoint` and `Bifunction.adjointFunction_isProper_iff`
  from `Chap06.Theorem_6_30_11`;
- `Function.IsProper.nonempty_dom` from `Chap01.Definition_4_6`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop ℝ`;
- primitive owner hypotheses: convexity of `Function.uncurry F` and graph properness
  `Function.IsProper (Function.uncurry F)`;
- derived API here: the source-domain nonemptiness consequences
  `dom F` and `dom (-adjoint X U F)`;
- the properness clause for the conjugate itself is already the Chapter 6 owner theorem
  `adjointFunction_isProper_iff`, so this file should recall that owner directly rather than keep
  a parallel weaker wrapper.

Layer target: `source-facing`, stated directly in the existing chapter owner language rather than
through a new wrapper around graph-function properness or source domains.
-/

/- Text 34.2.3, properness clause: the conjugate-properness statement is already the canonical
Chapter 6 owner theorem `adjointFunction_isProper_iff`. The source's closedness hypothesis is
redundant for this properness conclusion; only graph convexity and graph properness are used. -/
recall adjointFunction_isProper_iff

-- Proof sketch: rewrite the recalled properness clause for `F⋆` as properness of
-- `uncurry (-adjoint X U F)`, then apply the generic domain-nonempty owner theorem
-- `dom_nonempty_of_uncurry_isProper`.
/-- The source conjugate domain `dom F*`, rendered canonically as
`dom (-adjoint X U F)`, is nonempty under the graph-convexity and graph-properness
hypotheses of Text 34.2.3. -/
theorem dom_neg_adjointFunction_nonempty_of_uncurry_isConvex_of_uncurry_isProper
    (F : U → X → WithBotTop ℝ)
    (hF_convex : (uncurry F).IsConvex ℝ)
    (hF_proper : (uncurry F).IsProper) :
    (dom (-adjoint X U F)).Nonempty := by
  have hFStar_proper : (uncurry (-adjoint X U F)).IsProper := by
    change (-uncurry (adjoint X U F)).IsProper
    simpa using
      (adjointFunction_isProper_iff (XStar := X) (UStar := U) F hF_convex).2 hF_proper
  exact dom_nonempty_of_uncurry_isProper (-adjoint X U F) hFStar_proper

end GraphProperness

end Bifunction
