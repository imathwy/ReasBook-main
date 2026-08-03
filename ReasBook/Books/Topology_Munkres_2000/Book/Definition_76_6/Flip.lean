module

public import Topology_Munkres_2000.Book.Definition_76_5.Scheme

public section

universe u

namespace PolygonWord

/-- Reversing a polygon word and negating every orientation preserves its minimum length. -/
theorem formalInverse_length {α : Type u} (word : PolygonWord α) :
    3 ≤ (word.1.reverse.map fun letter ↦ (letter.1, !letter.2)).length := by
  -- Reverse and map both preserve list length.
  simpa using word.2

/-- The formal inverse reverses the word and reverses every signed orientation. -/
def formalInverse {α : Type u} (word : PolygonWord α) : PolygonWord α :=
  ⟨word.1.reverse.map (fun letter ↦ (letter.1, !letter.2)), formalInverse_length word⟩

/-- The underlying list of a formal inverse is reverse followed by sign negation. -/
theorem formalInverse_val {α : Type u} (word : PolygonWord α) :
    word.formalInverse.1 = word.1.reverse.map (fun letter ↦ (letter.1, !letter.2)) := by
  -- This is the defining underlying list of the formal inverse.
  rfl

/-- Taking the formal inverse twice recovers the original polygon word. -/
theorem formalInverse_formalInverse {α : Type u} (word : PolygonWord α) :
    word.formalInverse.formalInverse = word := by
  -- Reverse-map commutation and double Boolean negation restore every letter.
  apply Subtype.ext
  simp only [formalInverse, List.map_reverse, List.reverse_reverse, List.map_map]
  calc
    List.map ((fun letter ↦ (letter.1, !letter.2)) ∘
        fun letter ↦ (letter.1, !letter.2)) word.1 = List.map id word.1 := by
      apply List.map_congr_left
      rintro ⟨label, sign⟩ _
      cases sign <;> rfl
    _ = word.1 := List.map_id word.1

end PolygonWord

namespace LabellingScheme

/-- One flip step replaces one polygon word by its formal inverse. -/
inductive Flip {α : Type u} : LabellingScheme α → LabellingScheme α → Prop
  | of (word : PolygonWord α) (rest : LabellingScheme α) :
      Flip (word ::ₘ rest) (word.formalInverse ::ₘ rest)

/-- A flip is exactly replacement of one selected polygon word by its formal inverse. -/
theorem flip_iff {α : Type u} {before after : LabellingScheme α} :
    Flip before after ↔
      ∃ word : PolygonWord α, ∃ rest : LabellingScheme α,
        before = word ::ₘ rest ∧ after = word.formalInverse ::ₘ rest := by
  constructor
  · intro h
    -- Extract the selected word and unchanged remainder from the constructor.
    cases h with
    | of word rest => exact ⟨word, rest, rfl, rfl⟩
  · rintro ⟨word, rest, rfl, rfl⟩
    -- Rebuild the corresponding flip step.
    exact Flip.of word rest


end LabellingScheme
