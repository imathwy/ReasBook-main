import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace Rockafellar

/-- Source-facing notation for Definition 6.30.8: a bifunction is concave exactly when its graph
function is concave. -/
scoped[Rockafellar] notation:70 "concᵇ[" 𝕜 "](" G ")" =>
  (Function.uncurry G).IsConcave 𝕜

end Rockafellar

namespace Bifunction

section

open scoped Rockafellar

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.8 introduces the phrase “concave bifunction” by requiring the
  graph function of a bifunction to be concave on the product space.
- `core/canonical`: the chapter concavity owner is already `Function.IsConcave` from
  Definition 6.30.2, and the graph function of a bifunction is canonically the uncurried map
  `Function.uncurry G`.
- `bridge/view`: no extra bifunction owner is needed; the source notion is exactly the canonical
  graph-function owner `(Function.uncurry G).IsConcave 𝕜`, with shorthand notation
  `concᵇ[𝕜](G)`.

Domain-style sampling used here:
- `Function.IsConcave` from `Definition_6_30_2`;
- the canonical product-view operators `Function.uncurry` and `Function.curry_uncurry`,
  recalled upstream in Definition 6.29.2.

Primitive data vs derived API:
- primitive data: a bifunction `G : U → X → WithTopBot α`;
- canonical owner expression: `(Function.uncurry G).IsConcave 𝕜`;
- source-facing notation surface: `concᵇ[𝕜](G)`.
- the ambient structure is the canonical componentwise product structure induced from `U` and `X`,
  so the owner assumptions are stated on the two variable spaces rather than on an arbitrary
  externally supplied structure on `U × X`.

Layer target: `source-facing` theorem surface on the canonical owner.
-/

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommGroup α] [SMul 𝕜 α] [LE α]

recall Function.IsConcave

/-- Definition 6.30.8, source-facing owner equation:
a bifunction is concave exactly when its graph function is concave. -/
@[simp] theorem conc_iff_uncurry_isConcave
    (G : U → X → WithTopBot α) :
    concᵇ[𝕜](G) ↔ (Function.uncurry G).IsConcave 𝕜 :=
  Iff.rfl

end

end Bifunction
