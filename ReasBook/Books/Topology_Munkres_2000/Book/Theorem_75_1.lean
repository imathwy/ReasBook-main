module

public import Mathlib.GroupTheory.Abelianization.Defs

public section

universe u

namespace Abelianization

/-- Helper for Theorem 75.1: the canonical homomorphism from the abelianization of `F ⧸ N`
to the quotient of the abelianization of `F` by the image of `N`. -/
def quotientComparison {F : Type u} [Group F] (N : Subgroup F) [N.Normal] :
    Abelianization (F ⧸ N) →* Abelianization F ⧸ N.map (of : F →* Abelianization F) :=
  lift (QuotientGroup.map N (N.map (of : F →* Abelianization F)) of
    (Subgroup.le_comap_map of N))

/-- Helper for Theorem 75.1: the comparison homomorphism sends the class represented by `x`
to the quotient class of its image in the abelianization of `F`. -/
theorem quotientComparison_apply_of {F : Type u} [Group F]
    (N : Subgroup F) [N.Normal] (x : F) :
    quotientComparison N (of (QuotientGroup.mk' N x)) =
      QuotientGroup.mk' (N.map (of : F →* Abelianization F)) (of x) := by
  -- Both quotient maps compute directly on the representative `x`.
  rfl

/-- Helper for Theorem 75.1: the image of `N` in `Abelianization F` is killed after mapping
to `Abelianization (F ⧸ N)`. -/
private lemma imageInAbelianization_le_ker_mapQuotient {F : Type u} [Group F]
    (N : Subgroup F) [N.Normal] :
    N.map (of : F →* Abelianization F) ≤ (map (QuotientGroup.mk' N)).ker := by
  -- Every element of the image has a representative in `N`, hence vanishes in `F ⧸ N`.
  rintro _ ⟨x, hx, rfl⟩
  rw [MonoidHom.mem_ker, map_of, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- Helper for Theorem 75.1: the canonical homomorphism from the quotient of `Abelianization F`
by the image of `N` to the abelianization of `F ⧸ N`. -/
def quotientComparisonInv {F : Type u} [Group F] (N : Subgroup F) [N.Normal] :
    Abelianization F ⧸ N.map (of : F →* Abelianization F) →* Abelianization (F ⧸ N) :=
  QuotientGroup.lift (N.map (of : F →* Abelianization F))
    (map (QuotientGroup.mk' N)) (imageInAbelianization_le_ker_mapQuotient N)

/-- Helper for Theorem 75.1: the inverse comparison homomorphism sends the quotient class
represented by `of x` to the class of the image of `x` in `F ⧸ N`. -/
theorem quotientComparisonInv_apply_mk_of {F : Type u} [Group F]
    (N : Subgroup F) [N.Normal] (x : F) :
    quotientComparisonInv N (QuotientGroup.mk' (N.map (of : F →* Abelianization F)) (of x)) =
      of (QuotientGroup.mk' N x) := by
  -- The quotient lift and abelianization map both compute on their generators.
  rfl

/-- Helper for Theorem 75.1: the reverse comparison is a left inverse of the
forward comparison. -/
private lemma quotientComparisonInv_leftInverse {F : Type u} [Group F]
    (N : Subgroup F) [N.Normal] :
    Function.LeftInverse (quotientComparisonInv N) (quotientComparison N) := by
  -- Extensionality exposes generators without unfolding either quotient construction.
  have comparisonComposite :
      (quotientComparisonInv N).comp (quotientComparison N) =
        MonoidHom.id (Abelianization (F ⧸ N)) := by
    apply hom_ext
    apply QuotientGroup.monoidHom_ext
    ext x
    -- The two computation formulas identify the composite on every generator.
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [quotientComparison_apply_of, quotientComparisonInv_apply_mk_of]
  -- Evaluate the resulting homomorphism equality at the requested element.
  exact DFunLike.congr_fun comparisonComposite

/-- Helper for Theorem 75.1: the reverse comparison is a right inverse of the
forward comparison. -/
private lemma quotientComparisonInv_rightInverse {F : Type u} [Group F]
    (N : Subgroup F) [N.Normal] :
    Function.RightInverse (quotientComparisonInv N) (quotientComparison N) := by
  -- Extensionality reduces first through the quotient, then through abelianization.
  have comparisonComposite :
      (quotientComparison N).comp (quotientComparisonInv N) =
        MonoidHom.id (Abelianization F ⧸ N.map (of : F →* Abelianization F)) := by
    apply QuotientGroup.monoidHom_ext
    apply hom_ext
    ext x
    -- Apply the generator formulas in reverse order to recover each quotient class.
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [quotientComparisonInv_apply_mk_of, quotientComparison_apply_of]
  -- Evaluate the resulting homomorphism equality at the requested element.
  exact DFunLike.congr_fun comparisonComposite

/-- Theorem 75.1. For a normal subgroup `N` of a group `F`, the canonical homomorphism from
the abelianization of `F ⧸ N` to the quotient of `Abelianization F` by the image of `N` is
an isomorphism. -/
def quotientComparisonEquiv {F : Type u} [Group F] (N : Subgroup F) [N.Normal] :
    Abelianization (F ⧸ N) ≃* Abelianization F ⧸ N.map (of : F →* Abelianization F) where
  -- Assemble the canonical maps using their generatorwise inverse laws.
  toFun := quotientComparison N
  invFun := quotientComparisonInv N
  left_inv := quotientComparisonInv_leftInverse N
  right_inv := quotientComparisonInv_rightInverse N
  map_mul' := map_mul (quotientComparison N)

/-- The canonical comparison homomorphism is bijective. -/
theorem quotientComparison_bijective {F : Type u} [Group F] (N : Subgroup F) [N.Normal] :
    Function.Bijective (quotientComparison N) :=
  (quotientComparisonEquiv N).bijective

end Abelianization

end
