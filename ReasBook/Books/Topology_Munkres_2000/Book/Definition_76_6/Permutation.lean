module

public import Topology_Munkres_2000.Book.Definition_76_5.Scheme
public import Mathlib.Data.List.Rotate

public section

universe u

namespace PolygonWord

/-- The polygon word obtained by cyclically rotating its signed-label list. -/
@[expose]
def rotate {α : Type u} (word : PolygonWord α) (n : ℕ) : PolygonWord α :=
  ⟨word.val.rotate n, by simpa using word.property⟩

/-- The underlying list of `word.rotate n` is the corresponding list rotation. -/
theorem rotate_apply {α : Type u} (word : PolygonWord α) (n : ℕ) :
    (word.rotate n).val = word.val.rotate n := rfl

/-- A polygon word and any explicit rotation of it are cyclic permutations. -/
theorem isRotated_rotate {α : Type u} (word : PolygonWord α) (n : ℕ) :
    List.IsRotated word.val (word.rotate n).val :=
  ⟨n, rotate_apply word n |>.symm⟩

/-- Swapping two fragments preserves the polygon-word length condition. -/
theorem appendSwap_length {α : Type u} (y₀ y₁ : List (α × Bool))
    (hLength : 3 ≤ (y₀ ++ y₁).length) : 3 ≤ (y₁ ++ y₀).length := by
  -- Both concatenation orders have the same sum of fragment lengths.
  simpa [List.length_append, Nat.add_comm] using hLength

end PolygonWord

namespace LabellingScheme

/-- One permutation step replaces a selected polygon word by a cyclic permutation. -/
inductive Permute {α : Type u} : LabellingScheme α → LabellingScheme α → Prop
  | of (word rotated : PolygonWord α) (rest : LabellingScheme α)
      (hRotated : List.IsRotated word.val rotated.val) :
      Permute (word ::ₘ rest) (rotated ::ₘ rest)

/-- A permutation step is specified by one original word, one rotated word, and an
unchanged remainder of the scheme. -/
theorem permute_iff {α : Type u} {before after : LabellingScheme α} :
    Permute before after ↔
      ∃ word rotated : PolygonWord α, ∃ rest : LabellingScheme α,
        before = word ::ₘ rest ∧ after = rotated ::ₘ rest ∧
          List.IsRotated word.val rotated.val := by
  constructor
  · intro h
    -- Read the constructor data back as the existential specification.
    cases h with
    | of word rotated rest hRotated =>
        exact ⟨word, rotated, rest, rfl, rfl, hRotated⟩
  · rintro ⟨word, rotated, rest, rfl, rfl, hRotated⟩
    -- Reassemble the unique permutation constructor.
    exact Permute.of word rotated rest hRotated

namespace Permute

/-- Swapping `y₀ ++ y₁` to `y₁ ++ y₀` gives a permutation step. -/
theorem ofAppend {α : Type u} (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length) :
    Permute
      (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest)
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) := by
  -- The append swap is rotation by the length of the first fragment.
  refine Permute.of _ _ rest ?_
  exact ⟨y₀.length, by simp [List.rotate_eq_drop_append_take]⟩

end Permute


end LabellingScheme
