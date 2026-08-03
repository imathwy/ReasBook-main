module

public import Topology_Munkres_2000.Book.Definition_76_5.Scheme

public section

universe u v w

namespace PolygonWord

/-- The transposition exchanging two labels, using classical equality internally. -/
@[expose]
noncomputable def swapLabels {α : Type u} (a c : α) : α ≃ α :=
  @Equiv.swap α (Classical.decEq α) a c

/-- Replace label `a` by `c` in one signed letter, leaving every other letter fixed. -/
noncomputable def replaceLabelAt {α : Type u} (a c : α) (letter : α × Bool) : α × Bool :=
  @ite (α × Bool) (letter.1 = a) (Classical.propDecidable _)
    (c, letter.2) letter

/-- Relabelling a polygon word preserves its minimum length. -/
theorem relabel_length {α : Type u} {β : Type v} (e : α ≃ β) (word : PolygonWord α) :
    3 ≤ (word.1.map fun letter ↦ (e letter.1, letter.2)).length := by
  simpa using word.2

/-- Relabel every signed letter of a polygon word along a label equivalence. -/
@[expose]
def relabel {α : Type u} {β : Type v} (e : α ≃ β) (word : PolygonWord α) :
    PolygonWord β :=
  ⟨word.1.map fun letter ↦ (e letter.1, letter.2), relabel_length e word⟩

/-- The underlying list of a relabelled polygon word is obtained by letterwise mapping. -/
theorem relabel_val {α : Type u} {β : Type v} (e : α ≃ β) (word : PolygonWord α) :
    (word.relabel e).1 = word.1.map fun letter ↦ (e letter.1, letter.2) := rfl

/-- Relabelling by the identity equivalence leaves a polygon word unchanged. -/
theorem relabel_refl {α : Type u} (word : PolygonWord α) :
    word.relabel (Equiv.refl α) = word := by
  -- Compare the underlying signed-letter lists; identity relabelling is pointwise trivial.
  apply Subtype.ext
  simp [relabel]

/-- Successive polygon-word relabellings compose. -/
theorem relabel_trans {α : Type u} {β : Type v} {γ : Type w}
    (e : α ≃ β) (f : β ≃ γ) (word : PolygonWord α) :
    (word.relabel e).relabel f = word.relabel (e.trans f) := by
  -- Mapping twice is the same as mapping by the composite label equivalence.
  apply Subtype.ext
  simp [relabel]

/-- Reverse the sign of a signed letter when its label is `a`. -/
noncomputable def reverseSignAt {α : Type u} (a : α) (letter : α × Bool) : α × Bool :=
  @ite (α × Bool) (letter.1 = a) (Classical.propDecidable _)
    (letter.1, !letter.2) letter

/-- Reversing one label's signs preserves a polygon word's minimum length. -/
theorem reverseLabel_length {α : Type u} (a : α) (word : PolygonWord α) :
    3 ≤ (word.1.map (reverseSignAt a)).length := by
  simpa using word.2

/-- Reverse the sign of every occurrence of one label in a polygon word. -/
@[expose]
noncomputable def reverseLabel {α : Type u} (a : α) (word : PolygonWord α) :
    PolygonWord α :=
  ⟨word.1.map (reverseSignAt a), reverseLabel_length a word⟩

/-- The underlying list of a sign-reversed polygon word is mapped letterwise. -/
theorem reverseLabel_val {α : Type u} (a : α) (word : PolygonWord α) :
    (word.reverseLabel a).1 = word.1.map (reverseSignAt a) := rfl

/-- Reversing the signs belonging to one label twice restores the polygon word. -/
theorem reverseLabel_reverseLabel {α : Type u} (a : α) (word : PolygonWord α) :
    (word.reverseLabel a).reverseLabel a = word := by
  classical
  -- Each letter is fixed after the conditional Boolean negation is applied twice.
  apply Subtype.ext
  simp only [reverseLabel_val, List.map_map]
  calc
    List.map (reverseSignAt a ∘ reverseSignAt a) word.1 = List.map id word.1 := by
      apply List.map_congr_left
      rintro ⟨label, sign⟩ _
      by_cases hlabel : label = a
      · subst label
        simp [reverseSignAt]
      · simp [reverseSignAt, hlabel]
    _ = word.1 := List.map_id word.1

end PolygonWord

namespace LabellingScheme

/-- Relabel every polygon word in a labelling scheme along a label equivalence. -/
abbrev relabel {α : Type u} {β : Type v} (e : α ≃ β) (scheme : LabellingScheme α) :
    LabellingScheme β :=
  scheme.map (PolygonWord.relabel e)

/-- Membership in a relabelled scheme is characterized by a relabelled original word. -/
theorem mem_relabel_iff {α : Type u} {β : Type v} (e : α ≃ β)
    (scheme : LabellingScheme α) (word : PolygonWord β) :
    word ∈ scheme.relabel e ↔ ∃ original ∈ scheme, original.relabel e = word := by
  -- Membership in a mapped multiset records precisely an original preimage occurrence.
  exact Multiset.mem_map

/-- Relabelling a scheme by the identity equivalence leaves it unchanged. -/
theorem relabel_refl {α : Type u} (scheme : LabellingScheme α) :
    scheme.relabel (Equiv.refl α) = scheme := by
  -- The polygon-word identity law turns the multiset map into the identity map.
  change Multiset.map (PolygonWord.relabel (Equiv.refl α)) scheme = scheme
  calc
    Multiset.map (PolygonWord.relabel (Equiv.refl α)) scheme =
        Multiset.map id scheme := by
      apply Multiset.map_congr rfl
      intro word _
      exact PolygonWord.relabel_refl word
    _ = scheme := Multiset.map_id scheme

/-- Successive labelling-scheme relabellings compose. -/
theorem relabel_trans {α : Type u} {β : Type v} {γ : Type w}
    (e : α ≃ β) (f : β ≃ γ) (scheme : LabellingScheme α) :
    (scheme.relabel e).relabel f = scheme.relabel (e.trans f) := by
  -- Compose the two multiset maps using the polygon-word composition law.
  simpa only [Multiset.map_map, Function.comp_apply, PolygonWord.relabel_trans]

/-- Replace one label by another through the transposition of the two labels. -/
noncomputable abbrev renameLabel {α : Type u} (scheme : LabellingScheme α) (a c : α) :
    LabellingScheme α :=
  scheme.relabel (PolygonWord.swapLabels a c)

/-- Under the freshness hypotheses, `renameLabel` replaces `a` by `c` and fixes every
other signed letter occurring in the original scheme. -/
theorem renameLabel_spec {α : Type u} (scheme : LabellingScheme α) (a c : α)
    (h_ac : a ≠ c) (h_fresh : scheme.AvoidsLabel c) :
    ∀ word ∈ scheme, ∀ letter ∈ word.1,
      (PolygonWord.swapLabels a c letter.1, letter.2) =
        PolygonWord.replaceLabelAt a c letter := by
  classical
  intro word hword letter hletter
  -- Split at the replaced label; freshness rules out the other endpoint of the swap.
  rcases letter with ⟨label, sign⟩
  by_cases hlabel : label = a
  · subst label
    have hswap : PolygonWord.swapLabels a c a = c := Equiv.swap_apply_left a c
    simp [PolygonWord.replaceLabelAt, hswap]
  · have hfresh : label ≠ c :=
      (avoidsLabel_iff.mp h_fresh) word hword (label, sign) hletter
    have hswap : PolygonWord.swapLabels a c label = label :=
      Equiv.swap_apply_of_ne_of_ne hlabel hfresh
    simp [PolygonWord.replaceLabelAt, hlabel, hswap]

/-- Reverse the signs of every occurrence of one label throughout a labelling scheme. -/
noncomputable abbrev reverseLabel {α : Type u} (scheme : LabellingScheme α) (a : α) :
    LabellingScheme α :=
  scheme.map (PolygonWord.reverseLabel a)

/-- Reversing one label's signs twice restores the labelling scheme. -/
theorem reverseLabel_reverseLabel {α : Type u} (scheme : LabellingScheme α) (a : α) :
    (scheme.reverseLabel a).reverseLabel a = scheme := by
  -- The word-level involution reduces the iterated multiset map to the identity.
  change Multiset.map (PolygonWord.reverseLabel a)
      (Multiset.map (PolygonWord.reverseLabel a) scheme) = scheme
  rw [Multiset.map_map]
  calc
    Multiset.map (PolygonWord.reverseLabel a ∘ PolygonWord.reverseLabel a) scheme =
        Multiset.map id scheme := by
      apply Multiset.map_congr rfl
      intro word _
      exact PolygonWord.reverseLabel_reverseLabel a word
    _ = scheme := Multiset.map_id scheme


end LabellingScheme
