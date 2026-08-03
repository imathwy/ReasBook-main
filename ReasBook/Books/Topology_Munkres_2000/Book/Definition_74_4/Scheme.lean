module

public import Topology_Munkres_2000.Book.Definition_74_4
public import Mathlib.Data.Multiset.MapFold

public section

universe u

namespace PolygonWord

/-- Appending one letter to a fragment of length at least two gives a polygon word. -/
theorem appendLetter_length {α : Type u} (y : List (α × Bool)) (letter : α × Bool)
    (hy : 2 ≤ y.length) : 3 ≤ (y ++ [letter]).length := by
  -- Normalize the appended singleton's length, then use the fragment bound.
  simp only [List.length_append, List.length_singleton]
  omega

/-- Prepending one letter to a fragment of length at least two gives a polygon word. -/
theorem consLetter_length {α : Type u} (letter : α × Bool) (y : List (α × Bool))
    (hy : 2 ≤ y.length) : 3 ≤ (letter :: y).length := by
  -- Normalize the cons length, then use the fragment bound.
  simp only [List.length_cons]
  omega

/-- Joining two fragments of length at least two gives a polygon word. -/
theorem append_length {α : Type u} (y₀ y₁ : List (α × Bool))
    (hy₀ : 2 ≤ y₀.length) (hy₁ : 2 ≤ y₁.length) : 3 ≤ (y₀ ++ y₁).length := by
  -- Express the joined length as a sum and combine the two lower bounds.
  simp only [List.length_append]
  omega

end PolygonWord

/-- A total labelling scheme is an unordered finite collection of polygon words. -/
abbrev LabellingScheme (α : Type u) := Multiset (PolygonWord α)

namespace LabellingScheme

/-- The underlying signed-label lists of a total labelling scheme. -/
def words {α : Type u} (scheme : LabellingScheme α) : Multiset (List (α × Bool)) :=
  Multiset.map (fun word ↦ word.1) scheme

/-- Mapping a scheme to its underlying words preserves multiset cons. -/
@[simp] theorem words_cons {α : Type u} (word : PolygonWord α)
    (scheme : LabellingScheme α) :
    words (word ::ₘ scheme) = word.1 ::ₘ scheme.words := by
  -- Compute the mapped head and retain the mapped tail.
  exact Multiset.map_cons (fun polygonWord ↦ polygonWord.1) word scheme

/-- The empty labelling scheme has no underlying words. -/
@[simp] theorem words_zero {α : Type u} :
    (0 : LabellingScheme α).words = 0 := by
  -- Mapping the empty multiset remains empty.
  exact Multiset.map_zero (fun polygonWord : PolygonWord α ↦ polygonWord.1)

/-- A raw word belongs to `scheme.words` exactly when it underlies a word in `scheme`. -/
theorem mem_words_iff {α : Type u} {scheme : LabellingScheme α}
    {word : List (α × Bool)} :
    word ∈ scheme.words ↔
      ∃ hword : 3 ≤ word.length, (⟨word, hword⟩ : PolygonWord α) ∈ scheme := by
  constructor
  · intro hword
    -- Extract the bundled polygon word whose underlying list is `word`.
    rw [words, Multiset.mem_map] at hword
    obtain ⟨polygonWord, hpolygonWord, rfl⟩ := hword
    exact ⟨polygonWord.property, hpolygonWord⟩
  · rintro ⟨hword, hmem⟩
    -- Map the reconstructed bundled word back to its underlying list.
    exact Multiset.mem_map_of_mem (fun polygonWord ↦ polygonWord.1) hmem

/-- A total labelling scheme avoids a label when none of its signed letters uses that label. -/
def AvoidsLabel {α : Type u} (scheme : LabellingScheme α) (c : α) : Prop :=
  ∀ word ∈ scheme, ∀ letter ∈ word.1, letter.1 ≠ c

/-- A quantified characterization of a total labelling scheme avoiding a label. -/
theorem avoidsLabel_iff {α : Type u} {scheme : LabellingScheme α} {c : α} :
    scheme.AvoidsLabel c ↔
      ∀ word ∈ scheme, ∀ letter ∈ word.1, letter.1 ≠ c := by
  -- The quantified statement is exactly the definition of label avoidance.
  rfl


end LabellingScheme
