module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme

public section

universe u

namespace PolygonWord

/--
Inserting an adjacent oppositely signed pair after a fragment of length at least two gives a
polygon word.
-/
theorem insertCancelPair_length {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (hy₀Length : 2 ≤ y₀.length) :
    3 ≤ (y₀ ++ [(a, b), (a, !b)] ++ y₁).length := by
  -- Normalize the inserted pair to two additional letters, then use the prefix bound.
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end PolygonWord

namespace LabellingScheme

/--
One cancel step removes an adjacent oppositely signed pair carrying a label used nowhere else.
-/
inductive Cancel {α : Type u} : LabellingScheme α → LabellingScheme α → Prop
  | of (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool) (rest : LabellingScheme α)
      (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
      (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ a) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ a)
      (hrest : rest.AvoidsLabel a) :
      Cancel
        (⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
          PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩ ::ₘ rest)
        (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)

/-- A cancellation is characterized by its two fragments, inverse pair, and unchanged remainder. -/
theorem cancel_iff {α : Type u} {before after : LabellingScheme α} :
    Cancel before after ↔
      ∃ y₀ y₁ : List (α × Bool), ∃ a : α, ∃ b : Bool, ∃ rest : LabellingScheme α,
        ∃ hy₀Length : 2 ≤ y₀.length, ∃ hy₁Length : 2 ≤ y₁.length,
          before =
              (⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
                PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩ ::ₘ rest) ∧
            after =
              (⟨y₀ ++ y₁,
                PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) ∧
              (∀ letter ∈ y₀, letter.1 ≠ a) ∧
                (∀ letter ∈ y₁, letter.1 ≠ a) ∧ rest.AvoidsLabel a := by
  constructor
  · -- Expose the fragments, inverse pair, and freshness data stored by the constructor.
    rintro ⟨y₀, y₁, a, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
    exact ⟨y₀, y₁, a, b, rest, hy₀Length, hy₁Length, rfl, rfl, hy₀, hy₁, hrest⟩
  · -- Reconstruct the cancellation after the displayed source and target forms are substituted.
    rintro ⟨y₀, y₁, a, b, rest, hy₀Length, hy₁Length, rfl, rfl, hy₀, hy₁, hrest⟩
    exact .of y₀ y₁ a b rest hy₀Length hy₁Length hy₀ hy₁ hrest


end LabellingScheme
