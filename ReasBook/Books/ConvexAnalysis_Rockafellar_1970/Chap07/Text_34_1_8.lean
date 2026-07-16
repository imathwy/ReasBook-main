import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v w z

open scoped Rockafellar
open SaddleFunction

namespace Bifunction

section

variable {R : Type z} {α : Type w} {U : Type u} {V : Type v}
variable [Semiring R] [PartialOrder R]
variable [AddCommMonoid U] [SMul R U] [TopologicalSpace U]
variable [AddCommMonoid V] [SMul R V] [TopologicalSpace V]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α] [SMul R α]

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.8 states that a finite saddle-function on a nonempty product
  domain `C × D` has equivalent lower and upper ambient extensions; the convexity of `C` and `D`
  is already encoded by the slice owners inside `IsSaddleOn` once the domains are nonempty.
- `core/canonical`: the theorem uses the Chapter 34 equivalence relation `K ∼ L` from
  `Defn_34_4`.
- `bridge/view`: the theorem surface uses the textbook Chapter 34 extension notation
  `K₁[J | C, D]` and `K₂[J | C, D]`, avoiding re-expansion of restricted kernel lambdas.

Domain-style sampling used here:
- `SaddleFunction.IsSaddleOn R C D J`;
- the primitive branch owners `SaddleFunction.IsConcaveConvexOn R C D J` and
  `SaddleFunction.IsConvexConcaveOn R C D J`;
- the source extension notation `K₁[· | ·, ·]` and `K₂[· | ·, ·]`;
- source notation `K ∼ L` for equality of Chapter 34 closure pairs.

Layer target: `source-facing`. The theorem keeps the textbook lower/upper extension semantics on
the short canonical bridge owners, avoiding theorem-surface lambda noise. The primitive branch
owners are surfaced directly, and the disjunctive saddle owner is kept as a thin wrapper.
-/

-- Proof sketch: compare the two canonical ambient bridge extensions of a finite saddle kernel on
-- `C × D` in the Chapter 34 equivalence relation.
/-- Text 34.1.8: if `J` is a finite saddle-function on a nonempty product domain `C × D` at
scalar layer `R`,
then its canonical lower and upper ambient bridge extensions are equivalent in the Chapter 34 sense
`∼`. -/
theorem saddleExtension_equivalent_upperBoundaryExtension_of_isSaddleOn
    {C : Set U} {D : Set V} {J : U → V → α}
    (hCD_nonempty : (C ×ˢ D).Nonempty)
    (hJ : IsSaddleOn R C D J) :
    K₁[J | C, D] ∼ K₂[J | C, D] := by
  sorry

end

end Bifunction
