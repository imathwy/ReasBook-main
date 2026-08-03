module

public import Mathlib.Data.List.Basic

public section

universe u

/-- Definition 74.4. A polygon word is a sequence of signed edge labels with at least three
entries; the Boolean coordinate records the two possible orientations. -/
abbrev PolygonWord (α : Type u) := { word : List (α × Bool) // 3 ≤ word.length }

namespace PolygonWord

/-- Helper for Definition 74.4: the length of a polygon word is its number of signed labels. -/
def length {α : Type u} (word : PolygonWord α) : ℕ :=
  word.1.length

/-- Helper for Definition 74.4: every polygon word has at least three signed labels. -/
theorem three_le_length {α : Type u} (word : PolygonWord α) : 3 ≤ word.length :=
  word.property


end PolygonWord
