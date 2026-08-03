module

public import Mathlib.Logic.Relation

public section

universe u

/-- Exercise 3.3: The proposed argument unjustifiably assumes `C a b`. For a symmetric
and transitive relation, reflexivity is equivalent to the missing condition that every
element is related to some element. -/
theorem reflexive_iff_leftTotal {α : Type u} {C : α → α → Prop}
    [Std.Symm C] [IsTrans α C] :
    Std.Refl C ↔ Relator.LeftTotal C := by
  constructor
  · intro h_reflexive
    exact Relator.LeftTotal.refl h_reflexive.refl
  · intro h_total
    exact ⟨fun a ↦ by
      obtain ⟨b, hab⟩ := h_total a
      exact IsTrans.trans a b a hab (Std.Symm.symm a b hab)⟩
