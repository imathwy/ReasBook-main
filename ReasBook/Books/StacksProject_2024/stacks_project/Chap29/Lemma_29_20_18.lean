import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical owners `LocallyQuasiFinite`,
`LocallyOfFiniteType`, `Surjective`, and nearby composition lemmas, but no existing theorem with
the additional surjectivity descent hypothesis of Lemma 29.20.18. -/

/-- Lemma 29.20.18: let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. If `f` is
surjective, `g ∘ f` is locally quasi-finite, and `g` is locally of finite type, then
`g : Y ⟶ S` is locally quasi-finite. -/
@[stacks 0GWS]
theorem locallyQuasiFinite_of_surjective_of_comp_locallyQuasiFinite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [LocallyQuasiFinite (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyQuasiFinite g := sorry

end AlgebraicGeometry
