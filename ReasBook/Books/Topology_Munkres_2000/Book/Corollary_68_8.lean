module

public import Topology_Munkres_2000.Book.Theorem_68_7.Quotient

public section

universe u v

open scoped Monoid.Coprod

namespace Monoid.Coprod

/-- The least normal subgroup of `G₁ ∗ G₂` containing the image of the left factor. -/
def leftFactorNormalClosure (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    Subgroup (G₁ ∗ G₂) :=
  factorNormalClosure (⊤ : Subgroup G₁) (⊥ : Subgroup G₂)

/-- `leftFactorNormalClosure G₁ G₂` is normal. -/
instance leftFactorNormalClosure_normal (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] : (leftFactorNormalClosure G₁ G₂).Normal :=
  factorNormalClosure_normal _ _

/-- Helper for Corollary 68.8: the left-factor normal closure lies in the kernel of
the projection onto the right factor. -/
private theorem leftFactorNormalClosure_le_ker_snd (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] :
    leftFactorNormalClosure G₁ G₂ ≤ (snd : G₁ ∗ G₂ →* G₂).ker := by
  -- Use the leastness API, then check the two factor images separately.
  rw [leftFactorNormalClosure, factorNormalClosure_le_iff]
  constructor
  · rintro _ ⟨g, _, rfl⟩
    simp only [MonoidHom.mem_ker, snd_apply_inl]
  · rintro _ ⟨g, hg, rfl⟩
    have hg_one : g = 1 := hg
    subst g
    simp only [map_one, MonoidHom.mem_ker]

/-- Helper for Corollary 68.8: the quotient by the left-factor normal closure maps
canonically to the right factor. -/
private def leftFactorQuotientToRight (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] :
    (G₁ ∗ G₂) ⧸ leftFactorNormalClosure G₁ G₂ →* G₂ :=
  QuotientGroup.lift (leftFactorNormalClosure G₁ G₂) (snd : G₁ ∗ G₂ →* G₂)
    (leftFactorNormalClosure_le_ker_snd G₁ G₂)

/-- Helper for Corollary 68.8: the right inclusion descends to the quotient by the
left-factor normal closure. -/
private def rightToLeftFactorQuotient (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] :
    G₂ →* (G₁ ∗ G₂) ⧸ leftFactorNormalClosure G₁ G₂ :=
  (QuotientGroup.mk' (leftFactorNormalClosure G₁ G₂)).comp (inr : G₂ →* G₁ ∗ G₂)

/-- Helper for Corollary 68.8: every left-factor generator belongs to the subgroup
being quotiented out. -/
private theorem inl_mem_leftFactorNormalClosure (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] (g : G₁) :
    inl g ∈ leftFactorNormalClosure G₁ G₂ := by
  -- Leastness of the factor normal closure contains the entire mapped left factor.
  rw [leftFactorNormalClosure]
  apply ((factorNormalClosure_le_iff (⊤ : Subgroup G₁) (⊥ : Subgroup G₂)
    (factorNormalClosure ⊤ ⊥)).mp (le_refl _)).1
  exact Subgroup.mem_map_of_mem (inl : G₁ →* G₁ ∗ G₂) (Subgroup.mem_top g)

/-- Helper for Corollary 68.8: inclusion of the right factor followed by projection
back to it is the identity. -/
private theorem leftFactorQuotientToRight_comp_rightToLeftFactorQuotient
    (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (leftFactorQuotientToRight G₁ G₂).comp (rightToLeftFactorQuotient G₁ G₂) =
      MonoidHom.id G₂ := by
  -- Evaluate both homomorphisms on a right-factor generator.
  ext g
  simp only [MonoidHom.comp_apply, leftFactorQuotientToRight,
    rightToLeftFactorQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk',
    snd_apply_inr, MonoidHom.id_apply]

/-- Helper for Corollary 68.8: projection to the right factor followed by its
quotient inclusion is the identity on the quotient. -/
private theorem rightToLeftFactorQuotient_comp_leftFactorQuotientToRight
    (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (rightToLeftFactorQuotient G₁ G₂).comp (leftFactorQuotientToRight G₁ G₂) =
      MonoidHom.id ((G₁ ∗ G₂) ⧸ leftFactorNormalClosure G₁ G₂) := by
  -- Descend to the coproduct, where the projection kills the left generators.
  apply QuotientGroup.monoidHom_ext
  apply Monoid.Coprod.hom_ext
  · ext g
    simp only [MonoidHom.comp_apply, leftFactorQuotientToRight,
      rightToLeftFactorQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk',
      snd_apply_inl, map_one, MonoidHom.id_apply]
    symm
    rw [QuotientGroup.eq_one_iff]
    exact inl_mem_leftFactorNormalClosure G₁ G₂ g
  · ext g
    simp only [MonoidHom.comp_apply, leftFactorQuotientToRight,
      rightToLeftFactorQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk',
      snd_apply_inr, MonoidHom.id_apply]

/-- Corollary 68.8. If `N` is the least normal subgroup of `G₁ ∗ G₂` containing
the image of the canonical left inclusion, then `(G₁ ∗ G₂) ⧸ N ≃* G₂`. -/
def quotientLeftFactorEquiv (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (G₁ ∗ G₂) ⧸ leftFactorNormalClosure G₁ G₂ ≃* G₂ :=
  -- Route correction: the imported Theorem 68.7 equivalence has no exposed computation
  -- theorem, so construct the same canonical equivalence directly from the right projection.
  (leftFactorQuotientToRight G₁ G₂).toMulEquiv (rightToLeftFactorQuotient G₁ G₂)
    (rightToLeftFactorQuotient_comp_leftFactorQuotientToRight G₁ G₂)
    (leftFactorQuotientToRight_comp_rightToLeftFactorQuotient G₁ G₂)

/-- Helper for Corollary 68.8: on coproduct representatives,
`quotientLeftFactorEquiv` is the canonical projection to the right factor. -/
private lemma quotientLeftFactorEquiv_mk (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] (x : G₁ ∗ G₂) :
    quotientLeftFactorEquiv G₁ G₂
        (QuotientGroup.mk' (leftFactorNormalClosure G₁ G₂) x) =
      (snd : G₁ ∗ G₂ →* G₂) x := by
  -- Compute the forward quotient lift on the chosen coproduct representative.
  simp only [quotientLeftFactorEquiv, MonoidHom.toMulEquiv_apply,
    leftFactorQuotientToRight, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

/-- `leftFactorNormalClosure G₁ G₂` is the least normal subgroup containing the
image of the left factor. -/
theorem leftFactorNormalClosure_le_iff (G₁ : Type u) (G₂ : Type v)
    [Group G₁] [Group G₂] (N : Subgroup (G₁ ∗ G₂)) [N.Normal] :
    leftFactorNormalClosure G₁ G₂ ≤ N ↔
      (⊤ : Subgroup G₁).map (inl : G₁ →* G₁ ∗ G₂) ≤ N := by
  rw [leftFactorNormalClosure, factorNormalClosure_le_iff]
  simp

/-- The quotient equivalence restricts to the identity on the right factor. -/
theorem quotientLeftFactorEquiv_mk_inr (G₁ : Type u) {G₂ : Type v}
    [Group G₁] [Group G₂] (g : G₂) :
    quotientLeftFactorEquiv G₁ G₂ (QuotientGroup.mk' (leftFactorNormalClosure G₁ G₂) (inr g)) =
      g := by
  -- Compute the quotient lift and then evaluate the right projection.
  rw [quotientLeftFactorEquiv_mk, snd_apply_inr]

/-- The quotient equivalence kills the left factor. -/
theorem quotientLeftFactorEquiv_mk_inl {G₁ : Type u} (G₂ : Type v)
    [Group G₁] [Group G₂] (g : G₁) :
    quotientLeftFactorEquiv G₁ G₂ (QuotientGroup.mk' (leftFactorNormalClosure G₁ G₂) (inl g)) =
      1 := by
  -- Compute the quotient lift and then use that the right projection kills the left factor.
  rw [quotientLeftFactorEquiv_mk, snd_apply_inl]


end Monoid.Coprod
