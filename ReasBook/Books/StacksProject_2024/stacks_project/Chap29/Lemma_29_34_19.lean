import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owner `Smooth` and the smooth
  composition API;
- local Chapter 29 precedent (`Lemma_29_30_16`) fixes the commutative triangle convention as
  `hcomm : f ≫ q = p`.
- The provided Stacks tag evidence agrees on tag `02K5`.
-/

/-- Lemma 29.34.19: in a commutative diagram of morphisms of schemes
`X -f-> Y -q-> S` and `X -p-> S`, if `f` is surjective and smooth, `p` is smooth, and `q`
is locally of finite presentation, then `q` is smooth. -/
@[stacks 02K5]
theorem smooth_of_surjective_smooth_of_comp_smooth_of_locallyOfFinitePresentation
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] (hf : Smooth f) (hcomm : f ≫ q = p)
    (hp : Smooth p) (hq : LocallyOfFinitePresentation q) :
    Smooth q := sorry

end AlgebraicGeometry
