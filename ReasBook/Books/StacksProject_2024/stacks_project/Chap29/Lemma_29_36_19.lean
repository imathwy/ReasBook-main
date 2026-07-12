import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owners `Etale`,
  `Surjective`, and `LocallyOfFinitePresentation`;
- local Chapter 29 precedent (`Lemma_29_34_19` and `Lemma_29_30_16`) fixes the
  commutative triangle convention as `hcomm : f ≫ q = p`;
- the supplied Stacks tag evidence is consistent: Stacks tag `02K6` is the URL tag for
  `Lemma 29.36.19`.
-/

/-- Lemma 29.36.19: in a commutative diagram of morphisms of schemes
`X -f-> Y -q-> S` and `X -p-> S`, if `f` is surjective and étale, `p` is étale, and
`q` is locally of finite presentation, then `q` is étale. -/
@[stacks 02K6]
theorem etale_of_surjective_etale_of_comp_etale_of_locallyOfFinitePresentation
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] (hf : Etale f) (hcomm : f ≫ q = p)
    (hp : Etale p) (hq : LocallyOfFinitePresentation q) :
    Etale q := sorry

end AlgebraicGeometry
