module

public import Mathlib.Data.Sigma.Lex
public import Mathlib.Order.RelClasses

public section

namespace Sigma

universe u v

/-- The dependent lexicographic sum of a well-founded index and well-founded fibers is
well-founded. -/
instance instIsWellFoundedLex {ι : Type u} {α : ι → Type v} (r : ι → ι → Prop)
    (s : ∀ i, α i → α i → Prop) [IsWellFounded ι r]
    [∀ i, IsWellFounded (α i) (s i)] : IsWellFounded (Σ i, α i) (Lex r s) where
  wf := by
    let h : WellFounded (PSigma.Lex r s) :=
      WellFounded.psigma_lex IsWellFounded.wf fun _ ↦ IsWellFounded.wf
    let e := Equiv.psigmaEquivSigma α
    have hrel : InvImage (PSigma.Lex r s) e.symm = Lex r s := by
      funext a b
      apply propext
      constructor
      · intro hab
        obtain ⟨i, a⟩ := a
        obtain ⟨j, b⟩ := b
        cases hab with
        | left _ _ hij => exact Lex.left _ _ hij
        | right _ hab => exact Lex.right _ _ hab
      · intro hab
        obtain ⟨i, a⟩ := a
        obtain ⟨j, b⟩ := b
        cases hab with
        | left _ _ hij => exact PSigma.Lex.left _ _ hij
        | right _ _ hab => exact PSigma.Lex.right _ hab
    rw [← hrel]
    exact InvImage.wf e.symm h

/-- The dependent lexicographic sum of a well-ordered index and well-ordered fibers is
well-ordered. -/
instance instIsWellOrderLex {ι : Type u} {α : ι → Type v} (r : ι → ι → Prop)
    (s : ∀ i, α i → α i → Prop) [IsWellOrder ι r]
    [∀ i, IsWellOrder (α i) (s i)] : IsWellOrder (Σ i, α i) (Lex r s) where
  wf := IsWellFounded.wf

end Sigma
