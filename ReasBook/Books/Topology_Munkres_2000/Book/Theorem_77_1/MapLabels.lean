module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme
public import Mathlib.Data.Fin.SuccPred

public section

namespace PolygonWord

/-- Helper for Theorem 77.1: mapping the labels of a polygon word preserves its
minimum boundary length. -/
theorem mapLabels_three_le (f : α → β) (word : PolygonWord α) :
    3 ≤ (word.val.map fun letter ↦ (f letter.1, letter.2)).length := by
  -- Label mapping changes no positions in the underlying boundary list.
  simpa only [List.length_map] using word.property

/-- Helper for Theorem 77.1: apply a function to every unsigned label of a
polygon word while retaining all orientation signs. -/
def mapLabels (f : α → β) (word : PolygonWord α) : PolygonWord β :=
  ⟨word.val.map fun letter ↦ (f letter.1, letter.2), mapLabels_three_le f word⟩

/-- Helper for Theorem 77.1: the value of `mapLabels` is the pointwise mapped
signed boundary list. -/
theorem mapLabels_val (f : α → β) (word : PolygonWord α) :
    (word.mapLabels f).val = word.val.map fun letter ↦ (f letter.1, letter.2) := by
  -- Expose the stable list projection of the mapped polygon word.
  rfl

/-- Helper for Theorem 77.1: mapping polygon-word labels preserves the exact
number of boundary positions. -/
theorem mapLabels_length (f : α → β) (word : PolygonWord α) :
    (word.mapLabels f).val.length = word.val.length := by
  -- Reduce to the standard length formula for `List.map`.
  simp only [mapLabels_val, List.length_map]

/-- Helper for Theorem 77.1: lookup in a mapped polygon word maps the label at
the corresponding original position and retains its sign. -/
theorem mapLabels_get (f : α → β) (word : PolygonWord α)
    (i : Fin word.val.length) :
    (word.mapLabels f).val.get (Fin.cast (mapLabels_length f word).symm i) =
      (f (word.val.get i).1, (word.val.get i).2) := by
  -- `List.get` commutes with the pointwise label map after the length cast.
  simp only [mapLabels_val, List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- Helper for Theorem 77.1: an injective label map preserves the property that
every position has a unique distinct position carrying the same unsigned label. -/
theorem mapLabelsPreservesLabelsPaired (f : α → β)
    (hf : Function.Injective f)
    (word : PolygonWord α)
    (hpaired : ∀ i : Fin word.val.length, ∃! j : Fin word.val.length,
      j ≠ i ∧ (word.val.get j).1 = (word.val.get i).1) :
    ∀ i : Fin (word.mapLabels f).val.length,
      ∃! j : Fin (word.mapLabels f).val.length,
        j ≠ i ∧
          ((word.mapLabels f).val.get j).1 =
            ((word.mapLabels f).val.get i).1 := by
  intro i
  let iOriginal := Fin.cast (mapLabels_length f word) i
  obtain ⟨jOriginal, hj, hj_unique⟩ := hpaired iOriginal
  let j := Fin.cast (mapLabels_length f word).symm jOriginal
  have hiLetter :
      (word.mapLabels f).val.get i =
        (f (word.val.get iOriginal).1, (word.val.get iOriginal).2) := by
    -- Move the mapped index to the original word and use the lookup formula.
    have hletter := mapLabels_get f word iOriginal
    rw [Fin.leftInverse_cast (mapLabels_length f word) i] at hletter
    exact hletter
  have hjLetter :
      (word.mapLabels f).val.get j =
        (f (word.val.get jOriginal).1, (word.val.get jOriginal).2) := by
    exact mapLabels_get f word jOriginal
  refine ⟨j, ⟨?_, ?_⟩, ?_⟩
  · -- Distinct original positions remain distinct after the length cast.
    intro hji
    apply hj.1
    apply Fin.cast_injective (mapLabels_length f word).symm
    calc
      Fin.cast (mapLabels_length f word).symm jOriginal = j := rfl
      _ = i := hji
      _ = Fin.cast (mapLabels_length f word).symm iOriginal :=
        (Fin.leftInverse_cast (mapLabels_length f word) i).symm
  · -- Injectivity transports the original mate's label equality forward.
    rw [hjLetter, hiLetter]
    exact congrArg f hj.2
  · intro k hk
    let kOriginal := Fin.cast (mapLabels_length f word) k
    have hkLetter :
        (word.mapLabels f).val.get k =
          (f (word.val.get kOriginal).1, (word.val.get kOriginal).2) := by
      have hletter := mapLabels_get f word kOriginal
      rw [Fin.leftInverse_cast (mapLabels_length f word) k] at hletter
      exact hletter
    have hkLabel :
        (word.val.get kOriginal).1 = (word.val.get iOriginal).1 := by
      apply hf
      calc
        f (word.val.get kOriginal).1 =
            ((word.mapLabels f).val.get k).1 :=
          (congrArg Prod.fst hkLetter).symm
        _ = ((word.mapLabels f).val.get i).1 := hk.2
        _ = f (word.val.get iOriginal).1 := congrArg Prod.fst hiLetter
    have hkOriginal : kOriginal = jOriginal := by
      apply hj_unique
      constructor
      · intro hki
        apply hk.1
        apply Fin.cast_injective (mapLabels_length f word)
        exact hki
      · exact hkLabel
    -- Return uniqueness to the mapped index type through the inverse cast.
    apply Fin.cast_injective (mapLabels_length f word)
    calc
      Fin.cast (mapLabels_length f word) k = jOriginal := hkOriginal
      _ = Fin.cast (mapLabels_length f word) j :=
        (Fin.rightInverse_cast (mapLabels_length f word) jOriginal).symm

end PolygonWord

namespace LabellingScheme

/-- Helper for Theorem 77.1: map every label in every polygon word of a
labelling scheme along a function. -/
abbrev mapLabels (f : α → β) (scheme : LabellingScheme α) :
    LabellingScheme β :=
  scheme.map (PolygonWord.mapLabels f)

/-- Helper for Theorem 77.1: mapping labels in a singleton scheme produces the
singleton containing the mapped polygon word. -/
theorem mapLabels_singleton (f : α → β) (word : PolygonWord α) :
    mapLabels f ({word} : LabellingScheme α) =
      ({word.mapLabels f} : LabellingScheme β) := by
  -- Compute the multiset map on a singleton scheme.
  exact Multiset.map_singleton (PolygonWord.mapLabels f) word

end LabellingScheme

end
