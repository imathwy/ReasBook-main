module

public import Topology_Munkres_2000.Book.Algorithm_76_2.Cut

public section

universe u

namespace LabellingScheme

/-- A paste step is a cut step read in the reverse direction. -/
def Paste {α : Type u} (before after : LabellingScheme α) : Prop :=
  Cut after before

namespace Paste

/-- Join two polygon words along oppositely signed occurrences of a fresh label. -/
theorem of {α : Type u} (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c) :
    Paste
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) :=
  Cut.of y₀ y₁ c b rest hy₀Length hy₁Length hy₀ hy₁ hrest

/-- Paste the source-prescribed words `y₀c⁻¹` and `cy₁` into `y₀y₁`. -/
theorem ofNegativePositive {α : Type u} (y₀ y₁ : List (α × Bool)) (c : α)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c) :
    Paste
      (⟨y₀ ++ [(c, false)],
          PolygonWord.appendLetter_length y₀ (c, false) hy₀Length⟩ ::ₘ
        ⟨(c, true) :: y₁,
          PolygonWord.consLetter_length (c, true) y₁ hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) :=
  of y₀ y₁ c true rest hy₀Length hy₁Length hy₀ hy₁ hrest

end Paste

/--
A specification of a paste step by its fragments, length bounds, fresh label, and remainder.
-/
theorem paste_iff {α : Type u} {before after : LabellingScheme α} :
    Paste before after ↔
      ∃ y₀ y₁ : List (α × Bool), ∃ c : α, ∃ b : Bool, ∃ rest : LabellingScheme α,
        ∃ hy₀Length : 2 ≤ y₀.length, ∃ hy₁Length : 2 ≤ y₁.length,
          before =
              (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
                ⟨(c, b) :: y₁,
                  PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest) ∧
            after =
              (⟨y₀ ++ y₁,
                PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest) ∧
              (∀ letter ∈ y₀, letter.1 ≠ c) ∧
              (∀ letter ∈ y₁, letter.1 ≠ c) ∧ rest.AvoidsLabel c := by
  constructor
  · intro h
    rcases cut_iff.mp h with
      ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hafter, hbefore, hy₀, hy₁, hrest⟩
    exact ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hbefore, hafter, hy₀, hy₁, hrest⟩
  · rintro ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hbefore, hafter, hy₀, hy₁, hrest⟩
    exact cut_iff.mpr
      ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hafter, hbefore, hy₀, hy₁, hrest⟩


end LabellingScheme
