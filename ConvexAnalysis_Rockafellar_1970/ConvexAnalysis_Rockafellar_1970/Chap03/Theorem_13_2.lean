import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_4_7_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [ClosedIciTopology 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 13.2 states that for a closed convex set the indicator and support
  functions are mutual Fenchel conjugates, and it characterizes exactly which `WithBotTop 𝕜`-valued
  functions arise as support functions of nonempty closed convex sets.
- `core/canonical`: the owner declarations already present in the project are
  `indicatorFunction`, `supportFunction`, `convexConjugate`, `Function.IsConvex`,
  `Function.IsClosedProperConvex`, `Function.PositivelyHomogeneous`, together with the canonical
  set predicates `Set.Nonempty`, `IsClosed`, and `Convex`.
- `bridge/view`: the chapter notation layer `δ(· | C)`, `δᵛ(· | C)`, and `f⋆` is the
  source-facing surface for the owners `indicatorFunction`, `supportFunction`, and
  `convexConjugate`.
- Primitive data vs derived API: no new mathematical owner is needed beyond the existing
  `WithBotTop 𝕜` indicator/support owners and the canonical closed/proper/convex package
  `Function.IsClosedProperConvex`.

Domain-style sampling used here:
- `convexConjugate_indicatorFunction_eq_supportFunction`;
- `convexConjugate_supportFunction_eq_indicatorFunction_closure`;
- `Function.IsClosedProperConvex`;
- `Function.isClosedProperConvex_iff`;
- `Function.PositivelyHomogeneous`.

Layer target: `source-facing`, expressed directly in the canonical conjugacy and Chapter 13
notation surface, without introducing either a wrapper predicate for support functions or a
parallel bundle for closed/proper/convex data.
-/

/- Theorem 13.2 (1): the source-facing conjugacy `(δ(· | C))⋆ = δᵛ(· | C)` is exactly the owner
 theorem from Text 13.1.4. -/
recall convexConjugate_indicatorFunction_eq_supportFunction

-- Proof sketch: apply the support-function biconjugacy statement from Text 13.1.5 and use the
-- hypotheses `IsClosed C` and `Convex 𝕜 C` to identify `closure C` with `C`.
/-- Theorem 13.2 (2), in canonical ambient form: for a closed convex set `C` on a
finite-dimensional `𝕜`-vector space equipped with a continuous linear self-pairing, the support
function `δᵛ(· | C)` has Fenchel conjugate `δ(· | C)`. -/
theorem convexConjugate_supportFunction_eq_indicatorFunction
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    ((δᵛ(· | C) : E → WithBotTop 𝕜)⋆) = (δ[𝕜](· | C)) := by
  simpa [hC_closed.closure_eq] using
    (convexConjugate_supportFunction_eq_indicatorFunction_closure (E := E) (𝕜 := 𝕜) C hC_convex)

private theorem apply_zero_eq_zero_of_isClosedProperConvex_and_positivelyHomogeneous
    {f : E → WithBotTop 𝕜} (hf_closed : IsClosedProperConvex[𝕜] f)
    (hf_hom : f.PositivelyHomogeneous 𝕜) :
    f 0 = 0 := by
  sorry

private theorem supportFunction_positivelyHomogeneous (C : Set E) :
    (δᵛ(· | C) : E → WithBotTop 𝕜).PositivelyHomogeneous 𝕜 := by
  sorry

omit [FiniteDimensional 𝕜 E] in
private theorem nonpositiveSublevel_convexConjugate_eq_setOf_forall_pairing_le
    (f : E → WithBotTop 𝕜) :
    {xStar : E | f⋆ xStar ≤ (0 : WithBotTop 𝕜)} =
      {xStar : E | ∀ x : E, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f x} := by
  sorry

private theorem convexConjugate_eq_indicatorFunction_of_isClosedProperConvex_and_positivelyHomogeneous
    {f : E → WithBotTop 𝕜} (hf_closed : IsClosedProperConvex[𝕜] f)
    (hf_hom : f.PositivelyHomogeneous 𝕜) :
    f⋆ = (δ[𝕜](· | {xStar : E | ∀ x : E, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f x})) := by
  sorry

private theorem isClosedProperConvex_convexConjugate
    {f : E → WithBotTop 𝕜} (hf_closed : IsClosedProperConvex[𝕜] f) :
    IsClosedProperConvex[𝕜] (f⋆ : E → WithBotTop 𝕜) := by
  sorry

private theorem isClosedProperConvex_biconjugate_eq
    {f : E → WithBotTop 𝕜} (hf_closed : IsClosedProperConvex[𝕜] f) :
    (f⋆⋆ : E → WithBotTop 𝕜) = f := by
  sorry

-- Proof sketch: for the forward direction, replace `C` by `closure C` (which has the same support
-- function) and apply clause (1) plus Theorem 12.2 to obtain closed proper convexity; positive
-- homogeneity comes from the support-function scaling law. For the reverse direction, apply the
-- closed proper convex involutivity of conjugation to a positively homogeneous function `f`;
-- positive homogeneity forces its conjugate to be an indicator, and clause (1) then rewrites `f`
-- as the support function of a nonempty convex set.
omit [ClosedIciTopology 𝕜] in
/-- Theorem 13.2 (3), in canonical ambient form: a `WithBotTop 𝕜`-valued function on a
finite-dimensional `𝕜`-vector space equipped with a continuous linear self-pairing is of the
form `δᵛ(· | C)` for some nonempty convex set `C` if and only if it is closed proper convex and
positively homogeneous. -/
theorem
    exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous
    (f : E → WithBotTop 𝕜) :
    (∃ C : Set E, C.Nonempty ∧ Convex 𝕜 C ∧ f = (δᵛ(· | C) : E → WithBotTop 𝕜)) ↔
      IsClosedProperConvex[𝕜] f ∧ f.PositivelyHomogeneous 𝕜 := by
  sorry

end
