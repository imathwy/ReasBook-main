import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open AlgEquiv
open IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [Normal K M]

/-- The canonical inclusion `Gal(L / M) → Gal(L / K)` is injective. -/
-- Proof sketch: two automorphisms over `M` are equal once their induced `K`-automorphisms of `L`
-- agree pointwise.
theorem galoisTowerRestriction_inl_injective [Normal K L] :
    Function.Injective (MulSemiringAction.toAlgAut Gal(L / M) K L) := sorry

/-- The image of the canonical inclusion `Gal(L / M) → Gal(L / K)` is the kernel of the
restriction map `Gal(L / K) → Gal(M / K)`. -/
-- Proof sketch: use the standard identification of the kernel of `restrictNormalHom M` with the
-- fixing subgroup of `M`, then identify that fixing subgroup with `Gal(L / M)`.
theorem galoisTowerRestriction_range_eq_ker [Normal K L] :
    (MulSemiringAction.toAlgAut Gal(L / M) K L).range = (restrictNormalHom M).ker := sorry

/-- The restriction map `Gal(L / K) → Gal(M / K)` is surjective. -/
-- Proof sketch: this is the standard normal-extension surjectivity theorem for restriction of
-- automorphisms.
theorem galoisTowerRestriction_rightHom_surjective [Normal K L] :
    Function.Surjective (restrictNormalHom M : Gal(L / K) →* Gal(M / K)) := sorry

/-- Lemma 9.21.8: for a tower of fields `L/M/K`, if `L/K` and `M/K` are finite Galois, then
`1 → Gal(L/M) → Gal(L/K) → Gal(M/K) → 1` is a short exact sequence. The canonical Lean owner is
the group extension `GroupExtension Gal(L/M) Gal(L/K) Gal(M/K)` built from the inclusion and
restriction homomorphisms. Its construction and exactness proof use only the primitive normality
data `[Normal K L]` and `[Normal K M]`; when `[FiniteDimensional K L]` is available, finiteness of
the three Galois groups is a separate downstream consequence of typeclass inference rather than a
primitive input to this exact-sequence object. -/
noncomputable def galoisTowerRestrictionShortExact [Normal K L] :
    GroupExtension Gal(L / M) Gal(L / K) Gal(M / K) where
  inl := MulSemiringAction.toAlgAut Gal(L / M) K L
  rightHom := restrictNormalHom M
  inl_injective := galoisTowerRestriction_inl_injective M
  range_inl_eq_ker_rightHom := galoisTowerRestriction_range_eq_ker M
  rightHom_surjective := galoisTowerRestriction_rightHom_surjective M

/-- The inclusion morphism in `galoisTowerRestrictionShortExact` lands in the kernel of the
restriction morphism. -/
-- Proof sketch: apply the general `GroupExtension.rightHom_comp_inl` theorem to the canonical
-- group extension defined above.
theorem galoisTowerRestrictionShortExact_rightHom_comp_inl [Normal K L] :
    (galoisTowerRestrictionShortExact M).rightHom.comp
      (galoisTowerRestrictionShortExact M).inl = 1 := sorry
