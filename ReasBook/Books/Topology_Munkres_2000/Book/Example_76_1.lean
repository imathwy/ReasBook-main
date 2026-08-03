module

public import Topology_Munkres_2000.Book.Definition_76_10.Equivalence
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel

@[expose] public section

namespace KleinBottleScheme

open LabellingScheme

-- The labels `0`, `1`, and `2` represent `a`, `b`, and `c`, respectively.

/-- The Klein-bottle polygon word `aba⁻¹b`. -/
def initialWord : PolygonWord (Fin 3) :=
  ⟨[(0, true), (1, true), (0, false), (1, true)], by decide⟩

/-- The initial singleton Klein-bottle labelling scheme. -/
def initial : LabellingScheme (Fin 3) :=
  initialWord ::ₘ 0

/-- The first word `abc⁻¹` produced by cutting. -/
def cutFirstWord : PolygonWord (Fin 3) :=
  ⟨[(0, true), (1, true), (2, false)], by decide⟩

/-- The second word `ca⁻¹b` produced by cutting. -/
def cutSecondWord : PolygonWord (Fin 3) :=
  ⟨[(2, true), (0, false), (1, true)], by decide⟩

/-- The two-word scheme `abc⁻¹`, `ca⁻¹b` produced by cutting. -/
def cutResult : LabellingScheme (Fin 3) :=
  cutFirstWord ::ₘ cutSecondWord ::ₘ 0

/-- The cyclically permuted first word `c⁻¹ab`. -/
def permutedFirstWord : PolygonWord (Fin 3) :=
  ⟨[(2, false), (0, true), (1, true)], by decide⟩

/-- The scheme after cyclically permuting the first cut word. -/
def firstPermuted : LabellingScheme (Fin 3) :=
  permutedFirstWord ::ₘ cutSecondWord ::ₘ 0

/-- The formal inverse `b⁻¹ac⁻¹` of the second cut word. -/
def flippedSecondWord : PolygonWord (Fin 3) :=
  ⟨[(1, false), (0, true), (2, false)], by decide⟩

/-- The scheme `c⁻¹ab`, `b⁻¹ac⁻¹` after flipping the second word. -/
def flipped : LabellingScheme (Fin 3) :=
  permutedFirstWord ::ₘ flippedSecondWord ::ₘ 0

/-- The polygon word `c⁻¹aac⁻¹` obtained by pasting along `b`. -/
def pastedWord : PolygonWord (Fin 3) :=
  ⟨[(2, false), (0, true), (0, true), (2, false)], by decide⟩

/-- The singleton scheme obtained by pasting along `b`. -/
def pasted : LabellingScheme (Fin 3) :=
  pastedWord ::ₘ 0

/-- The final cyclic permutation `aac⁻¹c⁻¹` before reversing the sign of `c`. -/
def secondPermutedWord : PolygonWord (Fin 3) :=
  ⟨[(0, true), (0, true), (2, false), (2, false)], by decide⟩

/-- The singleton scheme after the final cyclic permutation. -/
def secondPermuted : LabellingScheme (Fin 3) :=
  secondPermutedWord ::ₘ 0

/-- The standard two-fold projective-plane word `aacc`. -/
def projectiveWord : PolygonWord (Fin 3) :=
  ⟨[(0, true), (0, true), (2, true), (2, true)], by decide⟩

/-- The standard singleton scheme for the two-fold projective-plane word `aacc`. -/
def projective : LabellingScheme (Fin 3) :=
  projectiveWord ::ₘ 0

/-- Helper for Example 76.1: cutting `aba⁻¹b` produces the scheme `abc⁻¹`, `ca⁻¹b`. -/
theorem cut : LabellingScheme.Cut initial cutResult := by
  -- Split after `ab` and insert the fresh label `c` with opposite orientations.
  unfold initial cutResult initialWord cutFirstWord cutSecondWord
  apply Cut.ofNegativePositive
    [(0, true), (1, true)] [(0, false), (1, true)] 2 0
  · decide
  · decide
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- Helper for Example 76.1: cyclically permuting the first cut word gives `c⁻¹ab`. -/
theorem permuteFirst : LabellingScheme.Permute cutResult firstPermuted := by
  -- Move the final `c⁻¹` edge of the first word to its beginning.
  unfold cutResult firstPermuted cutFirstWord permutedFirstWord
  apply Permute.ofAppend [(0, true), (1, true)] [(2, false)]

/-- Helper for Example 76.1: flipping the second word `ca⁻¹b` gives `b⁻¹ac⁻¹`. -/
theorem flipSecond : LabellingScheme.Flip firstPermuted flipped := by
  -- Select the second multiset component and compute its formal inverse.
  rw [LabellingScheme.flip_iff]
  have hformalInverse : cutSecondWord.formalInverse = flippedSecondWord := by
    -- Equality of polygon words reduces to the explicit reversed signed-label lists.
    apply Subtype.ext
    rw [PolygonWord.formalInverse_val]
    rfl
  refine ⟨cutSecondWord, permutedFirstWord ::ₘ 0, ?_, ?_⟩
  · unfold firstPermuted
    exact Multiset.cons_swap _ _ 0
  · unfold flipped
    rw [hformalInverse]
    exact Multiset.cons_swap _ _ 0

/-- Helper for Example 76.1: pasting the two words along `b` produces `c⁻¹aac⁻¹`. -/
theorem paste : LabellingScheme.Paste flipped pasted := by
  -- Remove the opposite `b` edges and concatenate the two retained fragments.
  unfold flipped pasted permutedFirstWord flippedSecondWord pastedWord
  apply Paste.of [(2, false), (0, true)] [(0, true), (2, false)] 1 false 0
  · decide
  · decide
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- Helper for Example 76.1: cyclically permuting `c⁻¹aac⁻¹` gives `aac⁻¹c⁻¹`. -/
theorem permuteFinal : LabellingScheme.Permute pasted secondPermuted := by
  -- Move the initial `c⁻¹` edge to the end of the pasted word.
  unfold pasted secondPermuted pastedWord secondPermutedWord
  apply Permute.ofAppend [(2, false)] [(0, true), (0, true), (2, false)]

/-- Helper for Example 76.1: reversing label `c` in `aac⁻¹c⁻¹` gives `aacc`. -/
lemma reverseSecondPermutedWord :
    secondPermutedWord.reverseLabel 2 = projectiveWord := by
  -- Route correction: import the earlier owner module with implementation exposure, so the
  -- concrete signed-letter map can be normalized without duplicating its private definition.
  apply Subtype.ext
  rw [PolygonWord.reverseLabel_val]
  -- The two `a` letters are fixed, while both negatively signed `c` letters are toggled.
  have hzero_ne_two : (0 : Fin 3) ≠ 2 := by decide
  unfold secondPermutedWord projectiveWord
  simp only [List.map_cons, List.map_nil, PolygonWord.reverseSignAt, if_neg hzero_ne_two,
    if_true, Bool.not_false]

/-- Helper for Example 76.1: reversing the sign of `c` transforms `aac⁻¹c⁻¹` into `aacc`. -/
theorem reverseC : secondPermuted.reverseLabel 2 = projective := by
  -- Map the word-level sign computation across the singleton scheme.
  unfold secondPermuted projective LabellingScheme.reverseLabel
  rw [Multiset.map_cons, Multiset.map_zero, reverseSecondPermutedWord]

/-- Example 76.1: the Klein-bottle scheme `aba⁻¹b` is equivalent to the
two-fold projective-plane scheme `aacc`. -/
theorem equivalentProjective : LabellingScheme.Equivalent initial projective := by
  apply Equivalent.trans (Equivalent.ofElementary (.cut cut))
  apply Equivalent.trans (Equivalent.ofElementary (.permute permuteFirst))
  apply Equivalent.trans (Equivalent.ofElementary (.flip flipSecond))
  apply Equivalent.trans (Equivalent.ofElementary (.paste paste))
  apply Equivalent.trans (Equivalent.ofElementary (.permute permuteFinal))
  simpa only [reverseC] using Equivalent.ofElementary (.reverse secondPermuted 2)

end KleinBottleScheme
