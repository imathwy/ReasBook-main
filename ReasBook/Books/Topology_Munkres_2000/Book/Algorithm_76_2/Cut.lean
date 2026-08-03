module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme

public section

universe u

namespace LabellingScheme

/--
One cut step splits a polygon word into two sufficiently long fragments and inserts
oppositely signed occurrences of a label used nowhere else in the scheme.
-/
inductive Cut {α : Type u} : LabellingScheme α → LabellingScheme α → Prop
  | of (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool) (rest : LabellingScheme α)
      (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
      (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c)
      (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
      (hrest : rest.AvoidsLabel c) :
      Cut
        (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
        (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
          ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest)

/--
Algorithm 76.2. A cut step is specified by two fragments, a fresh label with opposite
orientations, and an unchanged remainder of the labelling scheme.
-/
theorem cut_iff {α : Type u} {before after : LabellingScheme α} :
    Cut before after ↔
      ∃ y₀ y₁ : List (α × Bool), ∃ c : α, ∃ b : Bool, ∃ rest : LabellingScheme α,
        ∃ hy₀Length : 2 ≤ y₀.length, ∃ hy₁Length : 2 ≤ y₁.length,
          before =
              (⟨y₀ ++ y₁,
                PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) ∧
            after =
              (⟨y₀ ++ [(c, !b)],
                  PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
                ⟨(c, b) :: y₁,
                  PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest) ∧
              (∀ letter ∈ y₀, letter.1 ≠ c) ∧
                (∀ letter ∈ y₁, letter.1 ≠ c) ∧ rest.AvoidsLabel c := by
  constructor
  · -- Expose the fragments and freshness data stored by the cut constructor.
    rintro ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
    exact ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, rfl, rfl, hy₀, hy₁, hrest⟩
  · -- Reassemble a cut directly from the displayed normal form and side conditions.
    rintro ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, rfl, rfl, hy₀, hy₁, hrest⟩
    exact .of y₀ y₁ c b rest hy₀Length hy₁Length hy₀ hy₁ hrest

namespace Cut

/-- Cut `y₀ ++ y₁` into the source-prescribed words `y₀c⁻¹` and `cy₁`. -/
theorem ofNegativePositive {α : Type u} (y₀ y₁ : List (α × Bool)) (c : α)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c) :
    Cut
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ [(c, false)],
          PolygonWord.appendLetter_length y₀ (c, false) hy₀Length⟩ ::ₘ
        ⟨(c, true) :: y₁,
          PolygonWord.consLetter_length (c, true) y₁ hy₁Length⟩ ::ₘ rest) :=
  .of y₀ y₁ c true rest hy₀Length hy₁Length hy₀ hy₁ hrest

end Cut


end LabellingScheme
