module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

universe u v

namespace Monoid.Coprod

variable {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
variable (N₁ : Subgroup G₁) (N₂ : Subgroup G₂)

/-- The normal closure in `G₁ ∗ G₂` of the images of `N₁` and `N₂`. -/
def factorNormalClosure : Subgroup (G₁ ∗ G₂) :=
  Subgroup.normalClosure
    (N₁.map (inl : G₁ →* G₁ ∗ G₂) ⊔ N₂.map (inr : G₂ →* G₁ ∗ G₂))

/-- The factor normal closure is a normal subgroup of the binary coproduct. -/
instance factorNormalClosure_normal : (factorNormalClosure N₁ N₂).Normal :=
  Subgroup.normalClosure_normal

/-- The factor normal closure is the least normal subgroup containing both factor images. -/
theorem factorNormalClosure_le_iff (N : Subgroup (G₁ ∗ G₂)) [N.Normal] :
    factorNormalClosure N₁ N₂ ≤ N ↔
      N₁.map (inl : G₁ →* G₁ ∗ G₂) ≤ N ∧ N₂.map (inr : G₂ →* G₁ ∗ G₂) ≤ N := by
  rw [factorNormalClosure, ← Subgroup.normalClosure_subset_iff]
  exact sup_le_iff

variable [N₁.Normal] [N₂.Normal]

/-- The factor normal closure lies in the kernel of the coproduct of the quotient maps. -/
theorem factorNormalClosure_le_ker :
    factorNormalClosure N₁ N₂ ≤
      (map (QuotientGroup.mk' N₁) (QuotientGroup.mk' N₂)).ker := by
  -- Reduce to the two factor images, whose quotient classes are trivial.
  rw [factorNormalClosure_le_iff]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, map_apply_inl, QuotientGroup.mk'_apply]
    have hquotient : (x : G₁ ⧸ N₁) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hquotient, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, map_apply_inr, QuotientGroup.mk'_apply]
    have hquotient : (x : G₂ ⧸ N₂) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hquotient, map_one]

/-- The canonical homomorphism from the quotient of the coproduct to the coproduct of quotients. -/
def quotientToCoprodQuotient :
    (G₁ ∗ G₂) ⧸ factorNormalClosure N₁ N₂ →* (G₁ ⧸ N₁) ∗ (G₂ ⧸ N₂) :=
  QuotientGroup.lift (factorNormalClosure N₁ N₂)
    (map (QuotientGroup.mk' N₁) (QuotientGroup.mk' N₂))
    (factorNormalClosure_le_ker N₁ N₂)

omit [N₁.Normal] [N₂.Normal] in
/-- The left factor subgroup lies in the kernel of its inclusion into the quotient coproduct. -/
theorem leftFactor_le_ker :
    N₁ ≤ ((QuotientGroup.mk' (factorNormalClosure N₁ N₂)).comp
      (inl : G₁ →* G₁ ∗ G₂)).ker := by
  -- Insert each left-factor element into the defining supremum and then its normal closure.
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, factorNormalClosure]
  apply Subgroup.subset_normalClosure
  left
  exact Subgroup.mem_map_of_mem (inl : G₁ →* G₁ ∗ G₂) hx

omit [N₁.Normal] [N₂.Normal] in
/-- The right factor subgroup lies in the kernel of its inclusion into the quotient coproduct. -/
theorem rightFactor_le_ker :
    N₂ ≤ ((QuotientGroup.mk' (factorNormalClosure N₁ N₂)).comp
      (inr : G₂ →* G₁ ∗ G₂)).ker := by
  -- Insert each right-factor element into the defining supremum and then its normal closure.
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, factorNormalClosure]
  apply Subgroup.subset_normalClosure
  right
  exact Subgroup.mem_map_of_mem (inr : G₂ →* G₁ ∗ G₂) hx

/-- The canonical homomorphism from the coproduct of quotients to the quotient of the coproduct. -/
def coprodQuotientToQuotient :
    (G₁ ⧸ N₁) ∗ (G₂ ⧸ N₂) →* (G₁ ∗ G₂) ⧸ factorNormalClosure N₁ N₂ :=
  lift
    (QuotientGroup.lift N₁
      ((QuotientGroup.mk' (factorNormalClosure N₁ N₂)).comp
        (inl : G₁ →* G₁ ∗ G₂))
      (leftFactor_le_ker N₁ N₂))
    (QuotientGroup.lift N₂
      ((QuotientGroup.mk' (factorNormalClosure N₁ N₂)).comp
        (inr : G₂ →* G₁ ∗ G₂))
      (rightFactor_le_ker N₁ N₂))

/-- The two canonical quotient-coproduct homomorphisms are inverse in the quotient direction. -/
theorem coprodQuotientToQuotient_comp_quotientToCoprodQuotient :
    (coprodQuotientToQuotient N₁ N₂).comp (quotientToCoprodQuotient N₁ N₂) =
      MonoidHom.id ((G₁ ∗ G₂) ⧸ factorNormalClosure N₁ N₂) := by
  -- Descend to the original coproduct and compare the two factor generators.
  apply QuotientGroup.monoidHom_ext
  apply Monoid.Coprod.hom_ext
  · ext x
    simp only [MonoidHom.comp_apply, quotientToCoprodQuotient,
      coprodQuotientToQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_apply_inl,
      lift_apply_inl, MonoidHom.id_apply]
  · ext x
    simp only [MonoidHom.comp_apply, quotientToCoprodQuotient,
      coprodQuotientToQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_apply_inr,
      lift_apply_inr, MonoidHom.id_apply]

/-- The two canonical quotient-coproduct homomorphisms are inverse in the coproduct direction. -/
theorem quotientToCoprodQuotient_comp_coprodQuotientToQuotient :
    (quotientToCoprodQuotient N₁ N₂).comp (coprodQuotientToQuotient N₁ N₂) =
      MonoidHom.id ((G₁ ⧸ N₁) ∗ (G₂ ⧸ N₂)) := by
  -- Compare the coproduct factors, then evaluate each quotient homomorphism on representatives.
  apply Monoid.Coprod.hom_ext
  · apply QuotientGroup.monoidHom_ext
    ext x
    simp only [MonoidHom.comp_apply, quotientToCoprodQuotient,
      coprodQuotientToQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_apply_inl,
      lift_apply_inl, MonoidHom.id_apply]
  · apply QuotientGroup.monoidHom_ext
    ext x
    simp only [MonoidHom.comp_apply, quotientToCoprodQuotient,
      coprodQuotientToQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_apply_inr,
      lift_apply_inr, MonoidHom.id_apply]

/-- The quotient of a binary coproduct by the normal closure of the images of two normal
subgroups is multiplicatively equivalent to the coproduct of the factor quotients. -/
def quotientNormalClosureEquiv :
    (G₁ ∗ G₂) ⧸ factorNormalClosure N₁ N₂ ≃* (G₁ ⧸ N₁) ∗ (G₂ ⧸ N₂) :=
  (quotientToCoprodQuotient N₁ N₂).toMulEquiv (coprodQuotientToQuotient N₁ N₂)
    (coprodQuotientToQuotient_comp_quotientToCoprodQuotient N₁ N₂)
    (quotientToCoprodQuotient_comp_coprodQuotientToQuotient N₁ N₂)


end Monoid.Coprod
