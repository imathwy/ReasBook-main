import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical scheme-theoretic owner
`LocallyQuasiFinite` and the existing composition-left theorem
`AlgebraicGeometry.LocallyQuasiFinite.of_comp`; the pointwise clause is recorded with the local
owner `Scheme.Hom.QuasiFiniteAt`. -/

/-- Lemma 29.20.17 (1): let `X ⟶ Y` be a morphism of schemes over a base scheme `S`.
If the composite `X ⟶ S` is quasi-finite at `x : X`, then `X ⟶ Y` is quasi-finite at `x`. -/
@[stacks 03WR]
theorem quasiFiniteAt_of_comp_quasiFiniteAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hfg : (f ≫ g).QuasiFiniteAt x) :
    f.QuasiFiniteAt x := sorry

/-- Lemma 29.20.17 (2): let `X ⟶ Y` be a morphism of schemes over a base scheme `S`.
If the composite `X ⟶ S` is locally quasi-finite, then `X ⟶ Y` is locally quasi-finite. -/
@[stacks 03WR]
theorem locallyQuasiFinite_of_comp_locallyQuasiFinite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyQuasiFinite (f ≫ g)] :
    LocallyQuasiFinite f := sorry

end AlgebraicGeometry
