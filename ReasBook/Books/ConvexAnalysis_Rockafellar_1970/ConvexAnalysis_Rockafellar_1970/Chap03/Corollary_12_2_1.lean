import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.2.1 says that Fenchel conjugation `f ↦ f*` is a symmetric
  one-to-one correspondence on the class of closed proper convex functions on finite-dimensional
  paired spaces.
- `core/canonical`: the project owners already present are `convexConjugate` for Fenchel
  conjugation and the owner predicate `f.IsClosedProperConvex` for the admissible class, both on
  arbitrary finite-dimensional scalar spaces equipped with a continuous linear self-pairing.
- `bridge/view`: the textbook phrase "symmetric one-to-one correspondence" is rendered by the
  canonical set-level notion `Set.BijOn`, together with the companion involution statement
  `convexConjugate (convexConjugate f) = f` on that class.

Domain-style sampling used here:
- the project owner `convexConjugate`;
- the chapter owner predicate `Function.IsClosedProperConvex`;
- Theorem 12.2 declarations `Function.IsConvex.convexConjugate_isProper_iff`,
  `Function.isConvex_convexConjugate`, and
  `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- the closure owner theorem `lowerSemicontinuousHull_eq_self`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithBotTop 𝕜` together with the owner hypothesis
  `f.IsClosedProperConvex`;
- derived API: stability under conjugation and the induced bijection of the class with itself.

Codomain/scalar layer note:
- this item is stated directly on the scalar-generic chapter layer `WithBotTop 𝕜` and does not
  keep a parallel codomain-specialized surface.

Layer target:
- `core/canonical` for the companion owner lemmas
  `Function.IsClosedProperConvex.convexConjugate` and
  `Function.IsClosedProperConvex.biconjugate_eq`;
- `source-facing` for the correspondence theorem, stated directly as a theorem about the canonical
  conjugacy operator on the canonical class of closed proper convex functions, with no surrogate
  package or subtype wrapper.
-/

-- Proof sketch: Theorem 12.2 shows that the conjugate of any function is lower semicontinuous and
-- convex, and that properness is preserved on convex functions. Thus `convexConjugate` maps the
-- class of functions satisfying `Function.IsClosedProperConvex` to itself. Theorem 12.2 also gives
-- `f** = lowerSemicontinuousHull f` for convex `f`; applying this to `f` and then to `f⋆` yields
-- `cl(f⋆) = f⋆`, so closedness of the conjugate is recovered intrinsically from biconjugacy and
-- closure identities. Hence conjugation is its own inverse on that class and defines a bijection
-- of it with itself.
namespace Function.IsClosedProperConvex

section

variable [HasPairingSwap E E 𝕜]

/-- The class of closed proper convex functions on a finite-dimensional scalar space with a
continuous linear self-pairing is stable under Fenchel conjugation. -/
theorem convexConjugate {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosedProperConvex[𝕜] (f⋆ : E → WithBotTop 𝕜) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (Function.isConvex_convexConjugate (𝕜 := 𝕜) (f := f))
  · exact (Function.IsConvex.convexConjugate_isProper_iff (𝕜 := 𝕜) (f := f) hf.convex).2 hf.proper
  · simpa using (lowerSemicontinuous_convexConjugate (𝕜 := 𝕜) (f := f))

end

section

variable [OrderTopology 𝕜]

/-- Closed proper convex functions agree with their Fenchel biconjugates. -/
theorem biconjugate_eq {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    f⋆⋆ = f := by
  calc
    f⋆⋆ = cl(f) := Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull (𝕜 := 𝕜) hf.convex
    _ = f := lowerSemicontinuousHull_eq_self hf.closed

end

end Function.IsClosedProperConvex

variable [HasPairingSwap E E 𝕜] [OrderTopology 𝕜]

/-- Corollary 12.2.1: Fenchel conjugation induces a symmetric one-to-one correspondence on the
class of all closed proper convex functions on a finite-dimensional topological vector space with
continuous linear self-pairing, expressed here as a bijection of that class with itself. -/
theorem convexConjugate_bijOn_closedProperConvexFunctions :
    Set.BijOn
      (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
      {f : E → WithBotTop 𝕜 | IsClosedProperConvex[𝕜] f}
      {f : E → WithBotTop 𝕜 | IsClosedProperConvex[𝕜] f} := by
  let S : Set (E → WithBotTop 𝕜) := {f | IsClosedProperConvex[𝕜] f}
  have hmaps :
      Set.MapsTo
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        S S := by
    intro f hf
    exact hf.convexConjugate
  have hinv :
      Set.InvOn
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        S S := by
    constructor <;> intro f hf <;>
      exact Function.IsClosedProperConvex.biconjugate_eq hf
  simpa [S] using hinv.bijOn hmaps hmaps

end
