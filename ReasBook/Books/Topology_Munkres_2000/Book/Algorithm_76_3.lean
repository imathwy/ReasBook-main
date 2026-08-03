module

public import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel

public section

universe u

namespace LabellingScheme.Cancel

/-- Algorithm 76.3: Cancel the adjacent pair `aa⁻¹` from `y₀aa⁻¹y₁`. -/
theorem ofPositiveNegative {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ a) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hrest : rest.AvoidsLabel a) :
    Cancel
      (⟨y₀ ++ [(a, true), (a, false)] ++ y₁,
        PolygonWord.insertCancelPair_length y₀ y₁ a true hy₀Length⟩ ::ₘ rest)
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) :=
  .of y₀ y₁ a true rest hy₀Length hy₁Length hy₀ hy₁ hrest

end LabellingScheme.Cancel
