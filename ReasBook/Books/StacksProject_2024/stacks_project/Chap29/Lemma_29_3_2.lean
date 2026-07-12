import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Z : Scheme.{u}}

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced the exact scheme-side theorem
-- `IsImmersion.isImmersion_iff_exists_of_quasiCompact`, together with the canonical image
-- factorization through `Scheme.Hom.toImage` and `Scheme.Hom.imageι`. Nearby Section 29.3 precedent
-- uses the source-facing existential statement for the textbook wording, so this item is recorded
-- as that direct quasi-compact-immersion factorization theorem.

/-- Lemma 29.3.2: a quasi-compact immersion `h : Z ⟶ X` factors as an open immersion followed by a
closed immersion. -/
@[stacks 01QV]
theorem immersion_factors_open_then_closed_of_quasiCompact
    (h : Z ⟶ X) [QuasiCompact h] (hh : IsImmersion h) :
    ∃ (Zbar : Scheme.{u}) (j : Z ⟶ Zbar) (hj : IsOpenImmersion j)
      (i : Zbar ⟶ X) (hi : IsClosedImmersion i), j ≫ i = h := sorry

end

end AlgebraicGeometry
