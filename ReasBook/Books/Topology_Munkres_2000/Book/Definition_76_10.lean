module

public import Topology_Munkres_2000.Book.Definition_76_6.Flip
public import Topology_Munkres_2000.Book.Definition_76_6.Relabel
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation
public import Topology_Munkres_2000.Book.Definition_76_9.Uncancel
public import Mathlib.Logic.Relation

public section

universe u

/-- Helper for Definition 76.10: swapping two labels is independent of the order in which
the endpoints of the transposition are named. -/
theorem PolygonWord.swapLabels_comm {α : Type u} (a c : α) :
    swapLabels a c = swapLabels c a := by
  classical
  -- The wrapper uses the same classical equality instance on both sides.
  exact Equiv.swap_comm a c

/-- Helper for Definition 76.10: applying the label transposition to its right endpoint
returns its left endpoint. -/
theorem PolygonWord.swapLabels_apply_right {α : Type u} (a c : α) :
    swapLabels a c c = a := by
  classical
  -- This is the right-endpoint computation rule for the wrapped transposition.
  exact Equiv.swap_apply_right a c

/-- Helper for Definition 76.10: composing a label transposition with itself is the
identity equivalence. -/
theorem PolygonWord.swapLabels_self_trans {α : Type u} (a c : α) :
    (swapLabels a c).trans (swapLabels a c) = Equiv.refl α := by
  classical
  -- The wrapped transposition inherits the standard involution law for `Equiv.swap`.
  exact Equiv.swap_swap a c

namespace LabellingScheme

/-- Helper for Definition 76.10: an elementary step between labelling schemes is one of the
eight elementary scheme operations: cut, paste, flip, cyclic permutation, fresh relabelling,
sign reversal, cancellation, or uncancellation. -/
inductive ElementaryStep {α : Type u} :
    LabellingScheme α → LabellingScheme α → Prop
  | cut {before after} (step : Cut before after) : ElementaryStep before after
  | paste {before after} (step : Paste before after) : ElementaryStep before after
  | flip {before after} (step : Flip before after) : ElementaryStep before after
  | permute {before after} (step : Permute before after) : ElementaryStep before after
  | rename (before : LabellingScheme α) (a c : α) (h_ac : a ≠ c)
      (h_fresh : before.AvoidsLabel c) :
      ElementaryStep before (before.renameLabel a c)
  | reverse (before : LabellingScheme α) (a : α) :
      ElementaryStep before (before.reverseLabel a)
  | cancel {before after} (step : Cancel before after) : ElementaryStep before after
  | uncancel {before after} (step : Uncancel before after) : ElementaryStep before after

/-- Helper for Definition 76.10: an elementary step is exactly one of the eight elementary
scheme operations. -/
theorem elementaryStep_iff {α : Type u}
    {before after : LabellingScheme α} :
    ElementaryStep before after ↔
      Cut before after ∨ Paste before after ∨ Flip before after ∨
        Permute before after ∨
          (∃ a c : α, a ≠ c ∧ before.AvoidsLabel c ∧
            after = before.renameLabel a c) ∨
          (∃ a : α, after = before.reverseLabel a) ∨
          Cancel before after ∨ Uncancel before after := by
  constructor
  · intro step
    -- Read off which of the eight constructors produced the elementary step.
    cases step with
    | cut step => exact Or.inl step
    | paste step => exact Or.inr (Or.inl step)
    | flip step => exact Or.inr (Or.inr (Or.inl step))
    | permute step => exact Or.inr (Or.inr (Or.inr (Or.inl step)))
    | rename a c h_ac h_fresh =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨a, c, h_ac, h_fresh, rfl⟩))))
    | reverse a =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))))
    | cancel step =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl step))))))
    | uncancel step =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr step))))))
  · intro step
    -- Rebuild the corresponding constructor after substituting displayed targets.
    rcases step with step | step | step | step |
      ⟨a, c, h_ac, h_fresh, rfl⟩ | ⟨a, rfl⟩ | step | step
    · exact ElementaryStep.cut step
    · exact ElementaryStep.paste step
    · exact ElementaryStep.flip step
    · exact ElementaryStep.permute step
    · exact ElementaryStep.rename before a c h_ac h_fresh
    · exact ElementaryStep.reverse before a
    · exact ElementaryStep.cancel step
    · exact ElementaryStep.uncancel step

/-- Helper for Definition 76.10: avoiding a label is preserved when both the scheme and
the avoided label are transported through a label equivalence. -/
theorem AvoidsLabel.relabel {α : Type u} {β : Type*} {scheme : LabellingScheme α}
    {c : α} (h : scheme.AvoidsLabel c) (e : α ≃ β) :
    (scheme.relabel e).AvoidsLabel (e c) := by
  rw [avoidsLabel_iff]
  intro word hword letter hletter
  -- Pull the word and signed letter back through the two relabelling maps.
  obtain ⟨original, h_original, rfl⟩ := (mem_relabel_iff e scheme word).mp hword
  rw [PolygonWord.relabel_val, List.mem_map] at hletter
  obtain ⟨originalLetter, h_originalLetter, rfl⟩ := hletter
  -- Injectivity of the equivalence converts equality of transported labels back upstairs.
  exact fun h_eq ↦
    avoidsLabel_iff.mp h original h_original originalLetter h_originalLetter (e.injective h_eq)

/-- Helper for Definition 76.10: renaming a label and then swapping the two labels back
restores the original labelling scheme. -/
theorem renameLabel_renameLabel {α : Type u} (scheme : LabellingScheme α) (a c : α) :
    (scheme.renameLabel a c).renameLabel c a = scheme := by
  -- Compose the relabellings, identify the reverse swap, and use its involution law.
  calc
    (scheme.renameLabel a c).renameLabel c a =
        scheme.relabel ((PolygonWord.swapLabels a c).trans
          (PolygonWord.swapLabels c a)) :=
      relabel_trans (PolygonWord.swapLabels a c) (PolygonWord.swapLabels c a) scheme
    _ = scheme.relabel ((PolygonWord.swapLabels a c).trans
        (PolygonWord.swapLabels a c)) := by
      rw [PolygonWord.swapLabels_comm c a]
    _ = scheme.relabel (Equiv.refl α) := by
      rw [PolygonWord.swapLabels_self_trans]
    _ = scheme := relabel_refl scheme

/-- Helper for Definition 76.10: a paste is precisely a cut read in the opposite
direction. -/
theorem paste_iff_cut {α : Type u} {before after : LabellingScheme α} :
    Paste before after ↔ Cut after before := by
  constructor
  · intro step
    -- Exchange the displayed source and target in the public cut/paste specifications.
    obtain ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hbefore, hafter,
      hy₀, hy₁, hrest⟩ := paste_iff.mp step
    exact cut_iff.mpr
      ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hafter, hbefore,
        hy₀, hy₁, hrest⟩
  · intro step
    -- The same exchange reconstructs a paste from the reverse cut.
    obtain ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hafter, hbefore,
      hy₀, hy₁, hrest⟩ := cut_iff.mp step
    exact paste_iff.mpr
      ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hbefore, hafter,
        hy₀, hy₁, hrest⟩

/-- Helper for Definition 76.10: every elementary scheme operation can be reversed by an
elementary scheme operation. -/
theorem ElementaryStep.symm {α : Type u} {before after : LabellingScheme α}
    (step : ElementaryStep before after) : ElementaryStep after before := by
  cases step with
  | cut step =>
      -- Paste is definitionally a cut read in the reverse direction.
      exact ElementaryStep.paste (paste_iff_cut.mpr step)
  | paste step =>
      -- Conversely, the cut constructor reverses a paste.
      exact ElementaryStep.cut (paste_iff_cut.mp step)
  | flip step =>
      -- Formal inversion of a polygon word is involutive.
      cases step with
      | of word rest =>
          simpa only [PolygonWord.formalInverse_formalInverse] using
            ElementaryStep.flip (Flip.of word.formalInverse rest)
  | permute step =>
      -- Cyclic rotation is a symmetric relation on lists.
      cases step with
      | of word rotated rest hRotated =>
          exact ElementaryStep.permute (Permute.of rotated word rest hRotated.symm)
  | rename a c h_ac h_fresh =>
      -- The original fresh label is carried to the old label by the transposition.
      have h_reverseFresh : (before.renameLabel a c).AvoidsLabel a := by
        have h_transport := h_fresh.relabel (PolygonWord.swapLabels a c)
        rw [PolygonWord.swapLabels_apply_right] at h_transport
        exact h_transport
      -- Swapping back is an allowed fresh rename and returns the original scheme.
      simpa only [renameLabel_renameLabel] using
        ElementaryStep.rename (before.renameLabel a c) c a h_ac.symm h_reverseFresh
  | reverse a =>
      -- Reversing the same label's signs twice restores the scheme.
      simpa only [reverseLabel_reverseLabel] using
        ElementaryStep.reverse (before.reverseLabel a) a
  | cancel step =>
      -- Uncancellation is definitionally cancellation read backwards.
      exact ElementaryStep.uncancel (uncancel_iff.mpr step)
  | uncancel step =>
      -- Cancellation reverses an uncancellation.
      exact ElementaryStep.cancel (uncancel_iff.mp step)

/-- Definition 76.10: two labelling schemes are equivalent when one can be obtained from the
other by a finite sequence of elementary scheme operations. -/
def Equivalent {α : Type u}
    (before after : LabellingScheme α) : Prop :=
  Relation.ReflTransGen ElementaryStep before after

namespace Equivalent

/-- Helper for Definition 76.10: an elementary scheme operation gives an equivalence of
labelling schemes. -/
theorem ofElementary {α : Type u} {before after : LabellingScheme α}
    (step : ElementaryStep before after) : Equivalent before after :=
  Relation.ReflTransGen.single step

/-- Helper for Definition 76.10: every labelling scheme is equivalent to itself. -/
theorem refl {α : Type u} (scheme : LabellingScheme α) :
    Equivalent scheme scheme :=
  Relation.ReflTransGen.refl

/-- Helper for Definition 76.10: labelling-scheme equivalence is symmetric. -/
theorem symm {α : Type u} {before after : LabellingScheme α}
    (h : Equivalent before after) : Equivalent after before := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact (ofElementary step.symm).trans ih

/-- Helper for Definition 76.10: labelling-scheme equivalence is transitive. -/
theorem trans {α : Type u} {first second third : LabellingScheme α}
    (h₁ : Equivalent first second) (h₂ : Equivalent second third) :
    Equivalent first third :=
  Relation.ReflTransGen.trans h₁ h₂

end Equivalent

/-- Helper for Definition 76.10: labelling-scheme equivalence is an equivalence relation. -/
instance {α : Type u} : IsEquiv (LabellingScheme α) Equivalent where
  refl := Equivalent.refl
  symm _ _ := Equivalent.symm
  trans _ _ _ := Equivalent.trans

/-- Helper for Definition 76.10: the explicit setoid on labelling schemes generated by
elementary scheme operations. -/
def equivalentSetoid (α : Type u) : Setoid (LabellingScheme α) :=
  ⟨Equivalent, ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩⟩


end LabellingScheme
