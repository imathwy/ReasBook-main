module

public import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel
public import Topology_Munkres_2000.Book.Definition_76_6.Flip
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation

@[expose] public section

namespace SurfaceReductionExample

/-- The polygon word `abcc`. -/
def abcc : PolygonWord (Fin 3) :=
  ⟨[(0, true), (1, true), (2, true), (2, true)], by decide⟩

/-- The polygon word `c⁻¹c⁻¹ab`. -/
def cInvCInvAB : PolygonWord (Fin 3) :=
  ⟨[(2, false), (2, false), (0, true), (1, true)], by decide⟩

/-- The polygon word `ccab`. -/
def ccab : PolygonWord (Fin 3) :=
  ⟨[(2, true), (2, true), (0, true), (1, true)], by decide⟩

/-- The polygon word `b⁻¹a⁻¹cc`. -/
def bInvAInvCC : PolygonWord (Fin 3) :=
  ⟨[(1, false), (0, false), (2, true), (2, true)], by decide⟩

/-- The polygon word `ccaa⁻¹cc`. -/
def ccaaInvcc : PolygonWord (Fin 3) :=
  ⟨[(2, true), (2, true), (0, true), (0, false), (2, true), (2, true)],
    by decide⟩

/-- The polygon word `cccc`. -/
def cccc : PolygonWord (Fin 3) :=
  ⟨[(2, true), (2, true), (2, true), (2, true)], by decide⟩

/-- The polygon word `abcc⁻¹ab`. -/
def abccInvab : PolygonWord (Fin 3) :=
  ⟨[(0, true), (1, true), (2, true), (2, false), (0, true), (1, true)],
    by decide⟩

/-- The original two-word labelling scheme. -/
def originalScheme : LabellingScheme (Fin 3) :=
  abcc ::ₘ cInvCInvAB ::ₘ 0

/-- The scheme obtained by cyclically permuting `abcc` to `ccab`. -/
def firstPermutedScheme : LabellingScheme (Fin 3) :=
  ccab ::ₘ cInvCInvAB ::ₘ 0

/-- The paste-ready scheme obtained by then flipping `c⁻¹c⁻¹ab` to `b⁻¹a⁻¹cc`. -/
def pasteReadyScheme : LabellingScheme (Fin 3) :=
  ccab ::ₘ bInvAInvCC ::ₘ 0

/-- The one-word scheme obtained by the valid paste along `b`. -/
def pastedScheme : LabellingScheme (Fin 3) :=
  ccaaInvcc ::ₘ 0

/-- The one-word scheme obtained by cancelling the isolated `aa⁻¹` pair. -/
def dunceCapScheme : LabellingScheme (Fin 3) :=
  cccc ::ₘ 0

/-- The one-word scheme alleged to result from pasting the original words along `c`. -/
def allegedProjectivePlaneScheme : LabellingScheme (Fin 3) :=
  abccInvab ::ₘ 0

end SurfaceReductionExample

/-- Helper for Exercise 76.2 (1): cyclically permute `abcc` to `ccab`. -/
theorem dunceCapReductionPermute :
    LabellingScheme.Permute SurfaceReductionExample.originalScheme
      SurfaceReductionExample.firstPermutedScheme := by
  -- Split `abcc` after `ab`; swapping the two fragments gives the displayed rotation.
  unfold SurfaceReductionExample.originalScheme
    SurfaceReductionExample.firstPermutedScheme
    SurfaceReductionExample.abcc SurfaceReductionExample.ccab
  apply LabellingScheme.Permute.ofAppend
    [(0, true), (1, true)] [(2, true), (2, true)]

/-- Helper for Exercise 76.2 (2): flip `c⁻¹c⁻¹ab` to `b⁻¹a⁻¹cc`. -/
theorem dunceCapReductionFlip :
    LabellingScheme.Flip SurfaceReductionExample.firstPermutedScheme
      SurfaceReductionExample.pasteReadyScheme := by
  -- Select the second multiset component and replace it by its formal inverse.
  rw [LabellingScheme.flip_iff]
  have hformalInverse :
      SurfaceReductionExample.cInvCInvAB.formalInverse =
        SurfaceReductionExample.bInvAInvCC := by
    -- Compute the reversed signed-label list underlying the formal inverse.
    apply Subtype.ext
    rw [PolygonWord.formalInverse_val]
    rfl
  refine ⟨SurfaceReductionExample.cInvCInvAB,
    SurfaceReductionExample.ccab ::ₘ 0, ?_, ?_⟩
  · unfold SurfaceReductionExample.firstPermutedScheme
    exact Multiset.cons_swap _ _ 0
  · unfold SurfaceReductionExample.pasteReadyScheme
    rw [hformalInverse]
    exact Multiset.cons_swap _ _ 0

/-- Helper for Exercise 76.2 (3): paste the two words along `b`, producing `ccaa⁻¹cc`. -/
theorem dunceCapReductionPaste :
    LabellingScheme.Paste SurfaceReductionExample.pasteReadyScheme
      SurfaceReductionExample.pastedScheme := by
  -- Remove the oppositely oriented `b` edges and concatenate the retained fragments.
  unfold SurfaceReductionExample.pasteReadyScheme
    SurfaceReductionExample.ccab SurfaceReductionExample.bInvAInvCC
    SurfaceReductionExample.pastedScheme SurfaceReductionExample.ccaaInvcc
  apply LabellingScheme.Paste.of
    [(2, true), (2, true), (0, true)]
    [(0, false), (2, true), (2, true)] 1 false 0
  · decide
  · decide
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- Helper for Exercise 76.2 (4): cancel the isolated adjacent pair `aa⁻¹`, producing `cccc`. -/
theorem dunceCapReductionCancel :
    LabellingScheme.Cancel SurfaceReductionExample.pastedScheme
      SurfaceReductionExample.dunceCapScheme := by
  -- Delete the adjacent opposite `a` edges, leaving the two `cc` fragments joined.
  unfold SurfaceReductionExample.pastedScheme SurfaceReductionExample.ccaaInvcc
    SurfaceReductionExample.dunceCapScheme SurfaceReductionExample.cccc
  apply LabellingScheme.Cancel.of
    [(2, true), (2, true)] [(2, true), (2, true)] 0 true 0
  · decide
  · decide
  · decide
  · decide
  · rw [LabellingScheme.avoidsLabel_iff]
    simp

/-- Helper for Exercise 76.2: every paste result avoids the label used for the pasted edges. -/
private lemma exists_avoidedLabel_of_paste {α : Type*}
    {before after : LabellingScheme α}
    (hpaste : LabellingScheme.Paste before after) :
    ∃ c, after.AvoidsLabel c := by
  -- Expose the retained fragments and their common freshness condition.
  rw [LabellingScheme.paste_iff] at hpaste
  rcases hpaste with
    ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, _hbefore, hafter,
      hy₀, hy₁, hrest⟩
  refine ⟨c, ?_⟩
  rw [hafter]
  rw [LabellingScheme.avoidsLabel_iff] at hrest ⊢
  intro word hword letter hletter
  rw [Multiset.mem_cons] at hword
  rcases hword with hword | hword
  · subst word
    -- Membership in the pasted word reduces to membership in one fresh fragment.
    rw [List.mem_append] at hletter
    rcases hletter with hletter | hletter
    · exact hy₀ letter hletter
    · exact hy₁ letter hletter
  · exact hrest word hword letter hletter

/-- Exercise 76.2 (5): the proposed paste along `c` is illegal because another `c` remains in
each retained fragment, so the alleged projective-plane reduction does not begin with a paste.
-/
theorem projectivePlaneReductionNotPaste :
    ¬LabellingScheme.Paste SurfaceReductionExample.originalScheme
      SurfaceReductionExample.allegedProjectivePlaneScheme := by
  -- Any genuine paste omits its pasted label from the resulting scheme.
  intro hpaste
  obtain ⟨c, havoids⟩ := exists_avoidedLabel_of_paste hpaste
  rw [LabellingScheme.avoidsLabel_iff] at havoids
  -- The alleged output contains each of the three available labels.
  have hword :
      SurfaceReductionExample.abccInvab ∈
        SurfaceReductionExample.allegedProjectivePlaneScheme := by
    simp [SurfaceReductionExample.allegedProjectivePlaneScheme]
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · subst c
    have hletter :
        ((0, true) : Fin 3 × Bool) ∈ SurfaceReductionExample.abccInvab.1 := by
      simp [SurfaceReductionExample.abccInvab]
    exact havoids _ hword _ hletter rfl
  · subst c
    have hletter :
        ((1, true) : Fin 3 × Bool) ∈ SurfaceReductionExample.abccInvab.1 := by
      simp [SurfaceReductionExample.abccInvab]
    exact havoids _ hword _ hletter rfl
  · subst c
    have hletter :
        ((2, true) : Fin 3 × Bool) ∈ SurfaceReductionExample.abccInvab.1 := by
      simp [SurfaceReductionExample.abccInvab]
    exact havoids _ hword _ hletter rfl
