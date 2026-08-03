module

public import Mathlib.GroupTheory.Coprod.Basic

public section

open scoped Monoid.Coprod

universe u v

/- Notation 70.1: In the free product `G₁ ∗ G₂`, we informally identify each factor with
its image under the canonical injective homomorphism. Thus the subgroups denoted by `G₁`
and `G₂` in the source are the ranges of `Monoid.Coprod.inl` and `Monoid.Coprod.inr`. -/
#check fun (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] ↦ G₁ ∗ G₂
#check fun (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] ↦
  (Monoid.Coprod.inl : G₁ →* G₁ ∗ G₂).range
#check fun (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] ↦
  (Monoid.Coprod.inr : G₂ →* G₁ ∗ G₂).range
#check Monoid.Coprod.inl_injective
#check Monoid.Coprod.inr_injective
