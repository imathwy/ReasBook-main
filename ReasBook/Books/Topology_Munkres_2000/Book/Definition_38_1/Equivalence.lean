module

public import Topology_Munkres_2000.Book.Definition_38_1

@[expose] public section

universe u v w z

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- The identity homeomorphism of a compactification commutes with its embedding of `X`. -/
theorem Equiv.refl_commutes (C : Compactification.{u, v} X) (x : X) :
    Homeomorph.refl C (C x) = C x := by
  -- The identity homeomorphism fixes every point of the compactification.
  rfl

/-- The identity equivalence of a compactification. -/
def Equiv.refl (C : Compactification.{u, v} X) : Equiv C C where
  toHomeomorph := Homeomorph.refl C
  commutes := Equiv.refl_commutes C

/-- The inverse homeomorphism of an equivalence commutes with the embeddings of `X`. -/
theorem Equiv.symm_commutes {C : Compactification.{u, v} X}
    {D : Compactification.{u, w} X} (e : Equiv C D) (x : X) :
    e.toHomeomorph.symm (D x) = C x := by
  -- Replace the target embedding by its image under `e`, then cancel the inverse.
  rw [← e.commutes x]
  exact e.toHomeomorph.symm_apply_apply (C x)

/-- The inverse of an equivalence of compactifications. -/
def Equiv.symm {C : Compactification.{u, v} X} {D : Compactification.{u, w} X}
    (e : Equiv C D) : Equiv D C where
  toHomeomorph := e.toHomeomorph.symm
  commutes := Equiv.symm_commutes e

/-- The composite homeomorphism of two equivalences commutes with the embeddings of `X`. -/
theorem Equiv.trans_commutes {C : Compactification.{u, v} X}
    {D : Compactification.{u, w} X} {E : Compactification.{u, z} X}
    (e : Equiv C D) (f : Equiv D E) (x : X) :
    e.toHomeomorph.trans f.toHomeomorph (C x) = E x := by
  -- Evaluate the composite and successively use the two commuting equations.
  rw [Homeomorph.trans_apply, e.commutes x, f.commutes x]

/-- The composite of two equivalences of compactifications. -/
def Equiv.trans {C : Compactification.{u, v} X} {D : Compactification.{u, w} X}
    {E : Compactification.{u, z} X} (e : Equiv C D) (f : Equiv D E) : Equiv C E where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  commutes := Equiv.trans_commutes e f

/-- Equivalence of compactifications is exactly existence of a homeomorphism commuting with the
two embeddings of `X`. -/
theorem equivalent_iff (C : Compactification.{u, v} X) (D : Compactification.{u, w} X) :
    Equivalent C D ↔ ∃ e : C ≃ₜ D, ∀ x, e (C x) = D x := by
  -- Convert directly between a bundled equivalence witness and its two fields.
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toHomeomorph, e.commutes⟩
  · rintro ⟨e, h⟩
    exact ⟨⟨e, h⟩⟩

/-- Equivalence of compactifications is reflexive. -/
theorem Equivalent.refl (C : Compactification.{u, v} X) : Equivalent C C := by
  -- Package the canonical identity equivalence as a nonempty witness.
  exact ⟨Equiv.refl C⟩

/-- Equivalence of compactifications is symmetric. -/
theorem Equivalent.symm {C : Compactification.{u, v} X} {D : Compactification.{u, w} X}
    (h : Equivalent C D) : Equivalent D C := by
  -- Invert any bundled equivalence witnessing the hypothesis.
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/-- Equivalence of compactifications is transitive. -/
theorem Equivalent.trans {C : Compactification.{u, v} X} {D : Compactification.{u, w} X}
    {E : Compactification.{u, z} X} (hCD : Equivalent C D) (hDE : Equivalent D E) :
    Equivalent C E := by
  -- Compose representatives of the two nonempty equivalence types.
  rcases hCD with ⟨e⟩
  rcases hDE with ⟨f⟩
  exact ⟨e.trans f⟩


end Compactification

end
