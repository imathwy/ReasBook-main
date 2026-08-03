module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic

public section

open scoped Monoid.Coprod

universe u v

namespace Abelianization

/-- Helper for Exercise 69.1: the canonical homomorphism from the abelianization of a
binary free product to the product of the abelianizations of its factors. -/
def coprodToProd (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    Abelianization (G₁ ∗ G₂) →* (Abelianization G₁ × Abelianization G₂) :=
  lift <| Monoid.Coprod.lift
    ((MonoidHom.inl (Abelianization G₁) (Abelianization G₂)).comp of)
    ((MonoidHom.inr (Abelianization G₁) (Abelianization G₂)).comp of)

/-- Helper for Exercise 69.1: the canonical homomorphism from the product of two
abelianizations to the abelianization of their binary free product. -/
def prodToCoprod (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (Abelianization G₁ × Abelianization G₂) →* Abelianization (G₁ ∗ G₂) :=
  (map (Monoid.Coprod.inl : G₁ →* G₁ ∗ G₂)).coprod
    (map (Monoid.Coprod.inr : G₂ →* G₁ ∗ G₂))

/-- Helper for Exercise 69.1: the canonical map to the product restricts on the first
abelianized factor to the first product inclusion. -/
lemma coprodToProd_comp_map_inl (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (coprodToProd G₁ G₂).comp (map (Monoid.Coprod.inl : G₁ →* G₁ ∗ G₂)) =
      MonoidHom.inl (Abelianization G₁) (Abelianization G₂) := by
  -- Reduce equality out of the abelianization to equality on the original generators.
  apply hom_ext
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, map_of, lift_apply_of, coprodToProd,
    Monoid.Coprod.lift_apply_inl, MonoidHom.inl_apply]

/-- Helper for Exercise 69.1: the canonical map to the product restricts on the second
abelianized factor to the second product inclusion. -/
lemma coprodToProd_comp_map_inr (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (coprodToProd G₁ G₂).comp (map (Monoid.Coprod.inr : G₂ →* G₁ ∗ G₂)) =
      MonoidHom.inr (Abelianization G₁) (Abelianization G₂) := by
  -- Reduce equality out of the abelianization to equality on the original generators.
  apply hom_ext
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, map_of, lift_apply_of, coprodToProd,
    Monoid.Coprod.lift_apply_inr, MonoidHom.inr_apply]

/-- Helper for Exercise 69.1: composing the canonical map to the product with the
canonical map back gives the identity on the abelianized free product. -/
lemma prodToCoprod_comp_coprodToProd (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (prodToCoprod G₁ G₂).comp (coprodToProd G₁ G₂) =
      MonoidHom.id (Abelianization (G₁ ∗ G₂)) := by
  -- It suffices to compare the maps on the free-product generators.
  apply hom_ext
  apply Monoid.Coprod.hom_ext
  · ext x
    simp only [MonoidHom.comp_apply, lift_apply_of, coprodToProd,
      Monoid.Coprod.lift_apply_inl, prodToCoprod, MonoidHom.coprod_apply,
      MonoidHom.inl_apply, map_of, map_one, mul_one, MonoidHom.id_apply]
  · ext x
    simp only [MonoidHom.comp_apply, lift_apply_of, coprodToProd,
      Monoid.Coprod.lift_apply_inr, prodToCoprod, MonoidHom.coprod_apply,
      MonoidHom.inr_apply, map_of, map_one, one_mul, MonoidHom.id_apply]

/-- Helper for Exercise 69.1: composing the canonical map to the abelianized free
product with the canonical map back gives the identity on the product. -/
lemma coprodToProd_comp_prodToCoprod (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (coprodToProd G₁ G₂).comp (prodToCoprod G₁ G₂) =
      MonoidHom.id (Abelianization G₁ × Abelianization G₂) := by
  -- Composition distributes over the product copairing, exposing both factor maps.
  rw [prodToCoprod, MonoidHom.comp_coprod, coprodToProd_comp_map_inl,
    coprodToProd_comp_map_inr, MonoidHom.coprod_inl_inr]

/-- Exercise 69.1: The abelianization of a binary free product is canonically
multiplicatively equivalent to the product of the abelianizations of its factors. -/
def coprodMulEquivProd (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    Abelianization (G₁ ∗ G₂) ≃* (Abelianization G₁ × Abelianization G₂) :=
  (coprodToProd G₁ G₂).toMulEquiv (prodToCoprod G₁ G₂)
    (prodToCoprod_comp_coprodToProd G₁ G₂)
    (coprodToProd_comp_prodToCoprod G₁ G₂)

end Abelianization
