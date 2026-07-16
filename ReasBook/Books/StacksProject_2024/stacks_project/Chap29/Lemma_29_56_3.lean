import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: the source-facing quasi-finite hypothesis from Definition 29.20.1 is
-- canonically the conjunction of quasi-compactness and local quasi-finiteness. The theorem below
-- keeps the same geometric content while using the reusable mathlib owners directly.

/-- Lemma 29.56.3: if `f : Y ⟶ X` is a quasi-finite morphism between affine schemes, then `f`
factors as an open immersion `j : Y ⟶ Z` followed by a finite morphism `π : Z ⟶ X` with `Z`
affine. -/
@[stacks 01TJ]
theorem exists_affine_openImmersion_finiteFactorization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y] [QuasiFinite f] :
    ∃ (Z : Scheme.{u}) (j : Y ⟶ Z) (π : Z ⟶ X),
      IsAffine Z ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f := sorry

end Scheme.Hom
end AlgebraicGeometry
