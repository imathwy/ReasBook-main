import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section EffectiveDomain

variable {R : Type*} {α : Type*}
variable {U : Type u} {X : Type v}
variable [Semiring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [TopologicalSpace X]
variable [AddCommMonoid U] [SMul R U]
variable [AddCommMonoid X] [SMul R X]
variable [SMul R (WithBotTop α)]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 34.2.1 records two invariance consequences for equivalent closed
  concave-convex saddle-functions: the Chapter 34 effective domain is unchanged, and the two
  representatives agree pointwise whenever one coordinate lies in the relative interior of the
  corresponding coordinate-domain factor.
- `core/canonical`: the owner layer is Chapter 34's equivalence relation `K ∼ L` together with
  the canonical coordinate-domain owners `dom₁`, `dom₂`, `dom`, the closedness owner
  `IsClosed`, and the relative-interior notation `ri[R](·)`.
- `bridge/view`: this file keeps only the two source-facing corollary consequences on top of that
  owner layer. It does not introduce a second local equivalence wrapper, domain package, or
  kernel record.

Primary mathematical domain:
- Chapter 34 equivalence classes of closed concave-convex saddle-functions.

Domain-style sampling used here:
- `Bifunction.equivalence` and the notation `K ∼ L`;
- `Bifunction.equivalent_iff`;
- `SaddleFunction.dom`;
- `ri[R](·)`.

Primitive data vs derived API:
- primitive source data: `K`, `L`, the owner hypotheses `IsConcaveConvex R K`, `IsClosed K`, and
  `K ∼ L`;
- derived API: effective-domain invariance and the source-facing pointwise equality corollary.

Layer target: `bridge/view`, stated directly on the Chapter 34 owner layer.
-/

/-- Corollary 34.2.1 (1): equivalent representatives of a closed concave-convex saddle-function
share the same Chapter 34 effective domain `dom K`. -/
theorem dom_eq_of_equivalent_of_isConcaveConvex_of_isClosed
    {K L : U → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hLK : K ∼ L) :
    dom L = dom K := by
  sorry

end EffectiveDomain

section RelativeInterior

variable {R : Type*} {α : Type*}
variable {U : Type u} {X : Type v}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [TopologicalSpace X]
variable [AddCommGroup U] [Module R U]
variable [AddCommGroup X] [Module R X]
variable [SMul R (WithBotTop α)]

/-- Corollary 34.2.1 (2): if `K` is a closed concave-convex saddle-function and `L` is equivalent
to `K`, then `L` and `K` agree at `(u, v)` whenever `u ∈ ri(dom₁ K)` or `v ∈ ri(dom₂ K)`. -/
theorem eq_of_equivalent_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
    {K L : U → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hLK : K ∼ L)
    {u : U} {v : X}
    (hri : u ∈ ri[R](dom₁ K) ∨ v ∈ ri[R](dom₂ K)) :
    L u v = K u v := by
  sorry

end RelativeInterior

end SaddleFunction
