module

public import Topology_Munkres_2000.Book.Algorithm_76_3

public section

universe u

namespace LabellingScheme

/-- An uncancel step is a cancel step with its source and target reversed. -/
def Uncancel {α : Type u} (before after : LabellingScheme α) : Prop :=
  Cancel after before

/-- An uncancel step is exactly a cancellation with its source and target reversed. -/
theorem uncancel_iff {α : Type u} {before after : LabellingScheme α} :
    Uncancel before after ↔ Cancel after before :=
  Iff.rfl

namespace Uncancel

/-- Insert a fresh adjacent oppositely signed pair between two sufficiently long fragments. -/
theorem of {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ a) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hrest : rest.AvoidsLabel a) :
    Uncancel
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
        PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩ ::ₘ rest) :=
  Cancel.of y₀ y₁ a b rest hy₀Length hy₁Length hy₀ hy₁ hrest

/-- Insert the source-prescribed adjacent pair `aa⁻¹` between `y₀` and `y₁`. -/
theorem ofPositiveNegative {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ a) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hrest : rest.AvoidsLabel a) :
    Uncancel
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ [(a, true), (a, false)] ++ y₁,
        PolygonWord.insertCancelPair_length y₀ y₁ a true hy₀Length⟩ ::ₘ rest) :=
  Cancel.ofPositiveNegative y₀ y₁ a rest hy₀Length hy₁Length hy₀ hy₁ hrest

end Uncancel

end LabellingScheme
