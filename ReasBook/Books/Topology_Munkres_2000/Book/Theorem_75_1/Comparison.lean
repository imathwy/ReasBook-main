module

public import Mathlib.GroupTheory.Abelianization.Defs

public section

universe u

namespace Abelianization

variable {F : Type u} [Group F]

/-- The canonical homomorphism from the abelianization of `F ⧸ N` to the quotient of the
abelianization of `F` by the image of `N`. -/
def quotientComparison (N : Subgroup F) [N.Normal] :
    Abelianization (F ⧸ N) →* Abelianization F ⧸ N.map (of : F →* Abelianization F) :=
  lift (QuotientGroup.map N (N.map (of : F →* Abelianization F)) of
    (Subgroup.le_comap_map of N))

/-- The comparison homomorphism sends the class represented by `x` to the quotient class of
its image in the abelianization of `F`. -/
theorem quotientComparison_apply_of (N : Subgroup F) [N.Normal] (x : F) :
    quotientComparison N (of (QuotientGroup.mk' N x)) =
      QuotientGroup.mk' (N.map (of : F →* Abelianization F)) (of x) := by
  -- Both quotient maps compute directly on the representative `x`.
  rfl

/-- Helper for Theorem 75.1: the image of `N` in `Abelianization F` is killed after mapping
to `Abelianization (F ⧸ N)`. -/
private lemma imageInAbelianization_le_ker_mapQuotient (N : Subgroup F) [N.Normal] :
    N.map (of : F →* Abelianization F) ≤ (map (QuotientGroup.mk' N)).ker := by
  -- Every element of the image has a representative in `N`, hence vanishes in `F ⧸ N`.
  rintro _ ⟨x, hx, rfl⟩
  rw [MonoidHom.mem_ker, map_of, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- The canonical homomorphism from the quotient of `Abelianization F` by the image of `N`
to the abelianization of `F ⧸ N`. -/
def quotientComparisonInv (N : Subgroup F) [N.Normal] :
    Abelianization F ⧸ N.map (of : F →* Abelianization F) →* Abelianization (F ⧸ N) :=
  QuotientGroup.lift (N.map (of : F →* Abelianization F))
    (map (QuotientGroup.mk' N)) (imageInAbelianization_le_ker_mapQuotient N)

/-- The inverse comparison homomorphism sends the quotient class represented by `of x` to the
class of the image of `x` in `F ⧸ N`. -/
theorem quotientComparisonInv_apply_mk_of (N : Subgroup F) [N.Normal] (x : F) :
    quotientComparisonInv N (QuotientGroup.mk' (N.map (of : F →* Abelianization F)) (of x)) =
      of (QuotientGroup.mk' N x) := by
  -- The quotient lift and abelianization map both compute on their generators.
  rfl

end Abelianization

end
