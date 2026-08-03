module

public import Topology_Munkres_2000.Book.Definition_76_6.Flip
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation

@[expose] public section

namespace SurfacePastingExample

/-- The polygon word `acbc⁻¹`. -/
def firstWord : PolygonWord (Fin 4) :=
  ⟨[(0, true), (2, true), (1, true), (2, false)], by decide⟩

/-- The polygon word `cdba⁻¹d`. -/
def secondWord : PolygonWord (Fin 4) :=
  ⟨[(2, true), (3, true), (1, true), (0, false), (3, true)], by decide⟩

/-- The original two-word labelling scheme `acbc⁻¹`, `cdba⁻¹d`. -/
def originalScheme : LabellingScheme (Fin 4) :=
  firstWord ::ₘ secondWord ::ₘ 0

/-- The cyclic permutation `cbc⁻¹a` used before pasting along `a`. -/
def alongAFirstWord : PolygonWord (Fin 4) :=
  ⟨[(2, true), (1, true), (2, false), (0, true)], by decide⟩

/-- The scheme after cyclically permuting `acbc⁻¹` to `cbc⁻¹a`. -/
def alongAFirstPermutedScheme : LabellingScheme (Fin 4) :=
  alongAFirstWord ::ₘ secondWord ::ₘ 0

/-- The cyclic permutation `a⁻¹dcdb` used before pasting along `a`. -/
def alongASecondWord : PolygonWord (Fin 4) :=
  ⟨[(0, false), (3, true), (2, true), (3, true), (1, true)],
    by decide⟩

/-- The paste-ready two-word scheme for the paste along `a`. -/
def alongAReadyScheme : LabellingScheme (Fin 4) :=
  alongAFirstWord ::ₘ alongASecondWord ::ₘ 0

/-- The seven-letter polygon word `cbc⁻¹dcdb` obtained by pasting along `a`. -/
def alongAResultWord : PolygonWord (Fin 4) :=
  ⟨[(2, true), (1, true), (2, false), (3, true), (2, true), (3, true),
    (1, true)], by decide⟩

/-- The singleton scheme obtained by pasting along `a`. -/
def alongAResult : LabellingScheme (Fin 4) :=
  alongAResultWord ::ₘ 0

/-- The cyclic permutation `c⁻¹acb` used before pasting along `b`. -/
def alongBFirstWord : PolygonWord (Fin 4) :=
  ⟨[(2, false), (0, true), (2, true), (1, true)], by decide⟩

/-- The formal inverse `d⁻¹ab⁻¹d⁻¹c⁻¹` of the second polygon word. -/
def alongBFlippedSecondWord : PolygonWord (Fin 4) :=
  ⟨[(3, false), (0, true), (1, false), (3, false), (2, false)], by decide⟩

/-- The flipped and cyclically permuted word `b⁻¹d⁻¹c⁻¹d⁻¹a`. -/
def alongBSecondWord : PolygonWord (Fin 4) :=
  ⟨[(1, false), (3, false), (2, false), (3, false), (0, true)],
    by decide⟩

/-- The scheme after flipping the second polygon word. -/
def alongBFlippedScheme : LabellingScheme (Fin 4) :=
  firstWord ::ₘ alongBFlippedSecondWord ::ₘ 0

/-- The scheme after also cyclically permuting `acbc⁻¹` to `c⁻¹acb`. -/
def alongBFirstPermutedScheme : LabellingScheme (Fin 4) :=
  alongBFirstWord ::ₘ alongBFlippedSecondWord ::ₘ 0

/-- The paste-ready two-word scheme for the paste along `b`. -/
def alongBReadyScheme : LabellingScheme (Fin 4) :=
  alongBFirstWord ::ₘ alongBSecondWord ::ₘ 0

/-- The seven-letter polygon word `c⁻¹acd⁻¹c⁻¹d⁻¹a` obtained by pasting along `b`. -/
def alongBResultWord : PolygonWord (Fin 4) :=
  ⟨[(2, false), (0, true), (2, true), (3, false), (2, false), (3, false),
    (0, true)], by decide⟩

/-- The singleton scheme obtained by pasting along `b`. -/
def alongBResult : LabellingScheme (Fin 4) :=
  alongBResultWord ::ₘ 0

/-- The alleged seven-letter polygon word `acbdba⁻¹d` from an invalid paste along `c`. -/
def allegedAlongCResultWord : PolygonWord (Fin 4) :=
  ⟨[(0, true), (2, true), (1, true), (3, true), (1, true), (0, false),
    (3, true)], by decide⟩

/-- The singleton scheme alleged to result from pasting the original words along `c`. -/
def allegedAlongCResult : LabellingScheme (Fin 4) :=
  allegedAlongCResultWord ::ₘ 0

end SurfacePastingExample

/-- For Exercise 76.1 (a), first cyclically permute `acbc⁻¹` to `cbc⁻¹a`. -/
theorem permuteAlongAFirst :
    LabellingScheme.Permute SurfacePastingExample.originalScheme
      SurfacePastingExample.alongAFirstPermutedScheme := by
  -- Rotate the first polygon word and leave the second polygon word unchanged.
  unfold SurfacePastingExample.originalScheme
    SurfacePastingExample.alongAFirstPermutedScheme
  apply LabellingScheme.Permute.of
  decide

/-- For Exercise 76.1 (a), next cyclically permute `cdba⁻¹d` to `a⁻¹dcdb`. -/
theorem permuteAlongASecond :
    LabellingScheme.Permute SurfacePastingExample.alongAFirstPermutedScheme
      SurfacePastingExample.alongAReadyScheme := by
  -- Select the second multiset component and record its explicit cyclic rotation.
  rw [LabellingScheme.permute_iff]
  refine ⟨SurfacePastingExample.secondWord,
    SurfacePastingExample.alongASecondWord,
    SurfacePastingExample.alongAFirstWord ::ₘ 0, ?_, ?_, ?_⟩
  · unfold SurfacePastingExample.alongAFirstPermutedScheme
    exact Multiset.cons_swap _ _ 0
  · unfold SurfacePastingExample.alongAReadyScheme
    exact Multiset.cons_swap _ _ 0
  · decide

/-- For Exercise 76.1 (a), pasting along `a` produces `cbc⁻¹dcdb`. -/
theorem pasteAlongA :
    LabellingScheme.Paste SurfacePastingExample.alongAReadyScheme
      SurfacePastingExample.alongAResult := by
  -- Remove the opposite `a` edges and concatenate the two retained fragments.
  unfold SurfacePastingExample.alongAReadyScheme
    SurfacePastingExample.alongAFirstWord
    SurfacePastingExample.alongASecondWord
    SurfacePastingExample.alongAResult
    SurfacePastingExample.alongAResultWord
  rw [LabellingScheme.paste_iff]
  refine ⟨[(2, true), (1, true), (2, false)],
    [(3, true), (2, true), (3, true), (1, true)], 0, false, 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rfl
  · rfl
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- For Exercise 76.1 (b), first flip the second polygon word. -/
theorem flipAlongBSecond :
    LabellingScheme.Flip SurfacePastingExample.originalScheme
      SurfacePastingExample.alongBFlippedScheme := by
  -- Select the second polygon word and replace it by its formal inverse.
  rw [LabellingScheme.flip_iff]
  have hformalInverse :
      SurfacePastingExample.secondWord.formalInverse =
        SurfacePastingExample.alongBFlippedSecondWord := by
    -- Compute the formal inverse at the underlying signed-label list.
    apply Subtype.ext
    rw [PolygonWord.formalInverse_val]
    rfl
  refine ⟨SurfacePastingExample.secondWord,
    SurfacePastingExample.firstWord ::ₘ 0, ?_, ?_⟩
  · unfold SurfacePastingExample.originalScheme
    exact Multiset.cons_swap _ _ 0
  · unfold SurfacePastingExample.alongBFlippedScheme
    rw [hformalInverse]
    exact Multiset.cons_swap _ _ 0

/-- For Exercise 76.1 (b), next cyclically permute `acbc⁻¹` to `c⁻¹acb`. -/
theorem permuteAlongBFirst :
    LabellingScheme.Permute SurfacePastingExample.alongBFlippedScheme
      SurfacePastingExample.alongBFirstPermutedScheme := by
  -- Rotate the first polygon word and keep the flipped second word fixed.
  unfold SurfacePastingExample.alongBFlippedScheme
    SurfacePastingExample.alongBFirstPermutedScheme
  apply LabellingScheme.Permute.of
  decide

/-- For Exercise 76.1 (b), cyclically permute the flipped second word to
`b⁻¹d⁻¹c⁻¹d⁻¹a`. -/
theorem permuteAlongBSecond :
    LabellingScheme.Permute SurfacePastingExample.alongBFirstPermutedScheme
      SurfacePastingExample.alongBReadyScheme := by
  -- Select the flipped second component and rotate its leading `b⁻¹` into place.
  rw [LabellingScheme.permute_iff]
  refine ⟨SurfacePastingExample.alongBFlippedSecondWord,
    SurfacePastingExample.alongBSecondWord,
    SurfacePastingExample.alongBFirstWord ::ₘ 0, ?_, ?_, ?_⟩
  · unfold SurfacePastingExample.alongBFirstPermutedScheme
    exact Multiset.cons_swap _ _ 0
  · unfold SurfacePastingExample.alongBReadyScheme
    exact Multiset.cons_swap _ _ 0
  · decide

/-- For Exercise 76.1 (b), pasting along `b` produces `c⁻¹acd⁻¹c⁻¹d⁻¹a`. -/
theorem pasteAlongB :
    LabellingScheme.Paste SurfacePastingExample.alongBReadyScheme
      SurfacePastingExample.alongBResult := by
  -- Remove the opposite `b` edges and concatenate the two retained fragments.
  unfold SurfacePastingExample.alongBReadyScheme
    SurfacePastingExample.alongBFirstWord
    SurfacePastingExample.alongBSecondWord
    SurfacePastingExample.alongBResult
    SurfacePastingExample.alongBResultWord
  rw [LabellingScheme.paste_iff]
  refine ⟨[(2, false), (0, true), (2, true)],
    [(3, false), (2, false), (3, false), (0, true)], 1, false, 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rfl
  · rfl
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- Helper for Exercise 76.1: every paste result avoids the label used for the pasted edges. -/
lemma pasteResultAvoidsSomeLabel {α : Type*} {before after : LabellingScheme α}
    (hpaste : LabellingScheme.Paste before after) :
    ∃ c, after.AvoidsLabel c := by
  -- Expose the two retained fragments and their common freshness condition.
  rw [LabellingScheme.paste_iff] at hpaste
  rcases hpaste with
    ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hbefore, hafter,
      hy₀, hy₁, hrest⟩
  refine ⟨c, ?_⟩
  rw [hafter]
  rw [LabellingScheme.avoidsLabel_iff] at hrest ⊢
  intro word hword letter hletter
  rw [Multiset.mem_cons] at hword
  rcases hword with hword | hword
  · subst word
    -- A letter in the pasted word belongs to one of the two fresh fragments.
    rw [List.mem_append] at hletter
    rcases hletter with hletter | hletter
    · exact hy₀ letter hletter
    · exact hy₁ letter hletter
  · exact hrest word hword letter hletter

/-- Exercise 76.1 (c): the proposed paste along `c` cannot produce `acbdba⁻¹d`, because the
retained fragment `acb` still contains another occurrence of `c`.
-/
theorem cannotPasteAlongC :
    ¬LabellingScheme.Paste SurfacePastingExample.originalScheme
      SurfacePastingExample.allegedAlongCResult := by
  -- Any genuine paste omits its pasted label from the resulting scheme.
  intro hpaste
  obtain ⟨c, havoids⟩ := pasteResultAvoidsSomeLabel hpaste
  -- The alleged output contains each of the four available labels.
  rw [LabellingScheme.avoidsLabel_iff] at havoids
  have hword :
      SurfacePastingExample.allegedAlongCResultWord ∈
        SurfacePastingExample.allegedAlongCResult := by
    simp [SurfacePastingExample.allegedAlongCResult]
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree
  · subst c
    have hletter :
        ((0, true) : Fin 4 × Bool) ∈
          SurfacePastingExample.allegedAlongCResultWord.1 := by
      simp [SurfacePastingExample.allegedAlongCResultWord]
    exact havoids _ hword _ hletter rfl
  · subst c
    have hletter :
        ((1, true) : Fin 4 × Bool) ∈
          SurfacePastingExample.allegedAlongCResultWord.1 := by
      simp [SurfacePastingExample.allegedAlongCResultWord]
    exact havoids _ hword _ hletter rfl
  · subst c
    have hletter :
        ((2, true) : Fin 4 × Bool) ∈
          SurfacePastingExample.allegedAlongCResultWord.1 := by
      simp [SurfacePastingExample.allegedAlongCResultWord]
    exact havoids _ hword _ hletter rfl
  · subst c
    have hletter :
        ((3, true) : Fin 4 × Bool) ∈
          SurfacePastingExample.allegedAlongCResultWord.1 := by
      simp [SurfacePastingExample.allegedAlongCResultWord]
    exact havoids _ hword _ hletter rfl
