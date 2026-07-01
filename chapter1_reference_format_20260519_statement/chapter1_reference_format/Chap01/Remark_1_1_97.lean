import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} [Group G]

/- The finite abelian-group decomposition mentioned in the remark is already the canonical theorem
`CommGroup.equiv_prod_multiplicative_zmod_of_finite`. -/
recall CommGroup.equiv_prod_multiplicative_zmod_of_finite (G : Type u) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧ Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i))))

/-- Remark 1.1.97: for a fixed finite family of pairwise commuting subgroups, the canonical
ordered multiplication hom from their product is bijective exactly when every element admits a
unique ordered factorization by those subgroups. -/
-- Proof sketch: this is `Function.bijective_iff_existsUnique` applied directly to the canonical
-- hom `Subgroup.noncommPiCoprod hcomm`.
theorem bijective_noncommPiCoprod_iff_existsUnique_factorization {ι : Type v} [Fintype ι]
    (A : ι → Subgroup G)
    (hcomm : Pairwise fun i j ↦ ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y) :
    Function.Bijective (Subgroup.noncommPiCoprod hcomm) ↔
      ∀ g : G, ∃! a : ∀ i : ι, A i, Subgroup.noncommPiCoprod hcomm a = g := by
  simpa using Function.bijective_iff_existsUnique (Subgroup.noncommPiCoprod hcomm)

end
