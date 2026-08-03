module

public import Mathlib.Topology.Covering.Basic

public section

universe u v w x

namespace CoveringMap

variable {E : Type u} {E' : Type v} {E'' : Type w} {B : Type x}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']

/-- A concrete equivalence of maps into the same base, given by a homeomorphism commuting with
the maps. For covering maps, this is an equivalence of covering spaces. -/
structure Equiv (p : E → B) (p' : E' → B) where
  toHomeomorph : E ≃ₜ E'
  commutes : p = p' ∘ toHomeomorph

namespace Equiv

/-- An equivalence of maps commutes with the maps to the base pointwise. -/
theorem commutes_apply {p : E → B} {p' : E' → B} (h : Equiv p p') (e : E) :
    p e = p' (h.toHomeomorph e) := congrFun h.commutes e

/-- The identity homeomorphism commutes with a map to the base. -/
theorem refl_commutes (p : E → B) : p = p ∘ Homeomorph.refl E := rfl

/-- The identity equivalence of a map into the base. -/
def refl (p : E → B) : Equiv p p where
  toHomeomorph := Homeomorph.refl E
  commutes := refl_commutes p

/-- The inverse homeomorphism of an equivalence commutes with the maps to the base. -/
theorem symm_commutes {p : E → B} {p' : E' → B} (h : Equiv p p') :
    p' = p ∘ h.toHomeomorph.symm := by
  funext e'
  simpa using (h.commutes_apply (h.toHomeomorph.symm e')).symm

/-- The inverse of an equivalence of maps into the base. -/
def symm {p : E → B} {p' : E' → B} (h : Equiv p p') : Equiv p' p where
  toHomeomorph := h.toHomeomorph.symm
  commutes := symm_commutes h

/-- The composite homeomorphism of two equivalences commutes with the maps to the base. -/
theorem trans_commutes {p : E → B} {p' : E' → B} {p'' : E'' → B}
    (h : Equiv p p') (k : Equiv p' p'') :
    p = p'' ∘ h.toHomeomorph.trans k.toHomeomorph := by
  funext e
  exact h.commutes_apply e |>.trans (k.commutes_apply (h.toHomeomorph e))

/-- The composite of two equivalences of maps into the base. -/
def trans {p : E → B} {p' : E' → B} {p'' : E'' → B}
    (h : Equiv p p') (k : Equiv p' p'') : Equiv p p'' where
  toHomeomorph := h.toHomeomorph.trans k.toHomeomorph
  commutes := trans_commutes h k

/-- Equivalences of maps into a base are determined by their underlying homeomorphisms. -/
@[ext]
theorem ext {p : E → B} {p' : E' → B} {h k : Equiv p p'}
    (h_homeomorph : h.toHomeomorph = k.toHomeomorph) : h = k := by
  cases h
  cases k
  cases h_homeomorph
  rfl

end Equiv

/-- Two maps into the same base are equivalent when there exists a homeomorphism commuting with
the maps. -/
def Equivalent (p : E → B) (p' : E' → B) : Prop :=
  Nonempty (Equiv p p')

/-- Equivalence of maps into a base is exactly existence of a commuting homeomorphism. -/
theorem equivalent_iff {p : E → B} {p' : E' → B} :
    Equivalent p p' ↔ ∃ h : E ≃ₜ E', p = p' ∘ h := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.toHomeomorph, h.commutes⟩
  · rintro ⟨h, h_commutes⟩
    exact ⟨⟨h, h_commutes⟩⟩

namespace Equivalent

/-- Equivalence of maps into a base is reflexive. -/
theorem refl (p : E → B) : Equivalent p p := ⟨Equiv.refl p⟩

/-- Equivalence of maps into a base is symmetric. -/
theorem symm {p : E → B} {p' : E' → B} (h : Equivalent p p') : Equivalent p' p := by
  obtain ⟨h⟩ := h
  exact ⟨h.symm⟩

/-- Equivalence of maps into a base is transitive. -/
theorem trans {p : E → B} {p' : E' → B} {p'' : E'' → B}
    (h : Equivalent p p') (k : Equivalent p' p'') : Equivalent p p'' := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨h.trans k⟩

end Equivalent


end CoveringMap

end
