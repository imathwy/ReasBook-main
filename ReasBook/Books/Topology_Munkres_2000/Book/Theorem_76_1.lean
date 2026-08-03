module

public import Topology_Munkres_2000.Book.Theorem_76_1.Presentation

public section

universe u w

namespace LabellingScheme

/--
Theorem 76.1. Suppose `X` is obtained by pasting polygonal regions according to the
joined scheme `y₀y₁, w₂, …, wₘ`. If `y₀` and `y₁` each have length at least two and
the label `c` does not occur in that scheme, then `X` is also obtained from the split
scheme `y₀c⁻¹, cy₁, w₂, …, wₘ`; conversely, a realization by the split scheme gives
one by the joined scheme.
-/
theorem presentsCut_iff {α : Type u} (y₀ y₁ : List (α × Bool)) (c : α)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c) {X : Type w} [TopologicalSpace X] :
    Presents (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) X ↔
      Presents
        (⟨y₀ ++ [(c, false)], PolygonWord.appendLetter_length y₀ (c, false) hy₀Length⟩ ::ₘ
          ⟨(c, true) :: y₁, PolygonWord.consLetter_length (c, true) y₁ hy₁Length⟩ ::ₘ rest) X :=
  by
    -- The canonical cut has exactly the joined and split schemes appearing above.
    exact
      presents_iff_of_cut
        (.ofNegativePositive y₀ y₁ c rest hy₀Length hy₁Length hy₀ hy₁ hrest)

end LabellingScheme

end
