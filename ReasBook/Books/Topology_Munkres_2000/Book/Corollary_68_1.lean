module

public import Mathlib.GroupTheory.Coprod.Basic

public section

universe u v w

open scoped Monoid.Coprod

/- Corollary 68.1. The two parenthesizations of the free product of three groups
are canonically multiplicatively equivalent. -/
#check fun (G₁ : Type u) (G₂ : Type v) (G₃ : Type w)
    [Group G₁] [Group G₂] [Group G₃] ↦
  (MulEquiv.coprodAssoc G₁ G₂ G₃ : (G₁ ∗ G₂) ∗ G₃ ≃* G₁ ∗ (G₂ ∗ G₃))
