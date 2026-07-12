import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_36_3

noncomputable section

universe u v

open Set
open Bornology
open Bifunction

namespace SaddleFunction

section

variable {U : Type u} {X : Type v}
variable {β : Type*}
variable [CompleteLattice β]

/-- Ambient saddle-value existence follows from the domain-restricted Chapter 36 owner,
provided the canonical boundary-extension owner connecting `univ × univ` to
`dom₁ K × dom₂ K`, and the primitive nonemptiness datum needed for the minimax bridge. -/
theorem hasSaddleValue_of_hasSaddleValueOn_dom
    {K : U → X → β}
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hDom : HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact (hasSaddleValue_iff_hasSaddleValueOn_dom (K := K) hdom₁ hExt).2 hDom

/-- Ambient saddle-value existence follows from the domain-restricted Chapter 36 owner,
provided the canonical boundary-extension owner that connects `univ × univ` to
`dom₁ K × dom₂ K`. This convenience wrapper recovers the primitive nonemptiness datum
from `IsProper K`. -/
theorem hasSaddleValue_of_hasSaddleValueOn_dom_of_isProper
    {K : U → X → β}
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hDom : HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact (hasSaddleValue_iff_hasSaddleValueOn_dom_of_isProper (K := K) hK_proper hExt).2 hDom

/-- Corollary 37.3.1 in owner-bridge form: once boundedness is converted (by an upstream geometric
criterion) into domain-restricted saddle-value existence, the ambient saddle-value follows by the
canonical Chapter 36 domain bridge with the canonical boundary-extension owner. -/
theorem hasSaddleValue_of_isBounded_dom₁_or_dom₂
    {K : U → X → β}
    [Bornology U] [Bornology X]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom_bounded : IsBounded (dom₁ K) ∨ IsBounded (dom₂ K))
    (hDom_of_bounded :
      IsBounded (dom₁ K) ∨ IsBounded (dom₂ K) →
        HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_bounded hdom_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₁_or_dom₂` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₁_or_dom₂_of_isProper
    {K : U → X → β}
    [Bornology U] [Bornology X]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom_bounded : IsBounded (dom₁ K) ∨ IsBounded (dom₂ K))
    (hDom_of_bounded :
      IsBounded (dom₁ K) ∨ IsBounded (dom₂ K) →
        HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁_or_dom₂
    hK_proper.dom₁_nonempty hExt hdom_bounded hDom_of_bounded

/-- First one-sided bounded-domain entry point: if the first factor is bounded and an upstream
criterion yields the domain-restricted owner, then `K` has an ambient saddle-value. -/
theorem hasSaddleValue_of_isBounded_dom₁
    {K : U → X → β}
    [Bornology U]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₁_bounded : IsBounded (dom₁ K))
    (hDom_of_dom₁_bounded :
      IsBounded (dom₁ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_dom₁_bounded hdom₁_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₁` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₁_of_isProper
    {K : U → X → β}
    [Bornology U]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₁_bounded : IsBounded (dom₁ K))
    (hDom_of_dom₁_bounded :
      IsBounded (dom₁ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁
    hK_proper.dom₁_nonempty hExt hdom₁_bounded hDom_of_dom₁_bounded

/-- Second one-sided bounded-domain entry point: if the second factor is bounded and an upstream
criterion yields the domain-restricted owner, then `K` has an ambient saddle-value. -/
theorem hasSaddleValue_of_isBounded_dom₂
    {K : U → X → β}
    [Bornology X]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₂_bounded : IsBounded (dom₂ K))
    (hDom_of_dom₂_bounded :
      IsBounded (dom₂ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_dom₂_bounded hdom₂_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₂` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₂_of_isProper
    {K : U → X → β}
    [Bornology X]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₂_bounded : IsBounded (dom₂ K))
    (hDom_of_dom₂_bounded :
      IsBounded (dom₂ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₂
    hK_proper.dom₁_nonempty hExt hdom₂_bounded hDom_of_dom₂_bounded

end

end SaddleFunction
