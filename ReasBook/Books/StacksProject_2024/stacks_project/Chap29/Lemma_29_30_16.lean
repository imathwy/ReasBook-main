import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme-morphism owners `Surjective`,
  `LocallyOfFinitePresentation`, and descent-style morphism-property API;
- local Chapter 29 precedent fixes the triangle convention as `hcomm : f ≫ q = p`
  and the scheme-level syntomic owner as `Syntomic f := LocallyOfType RingHom.Syntomic f`.
-/

/-- Lemma 29.30.16: in a commutative triangle of morphisms of schemes
`X -f-> Y -q-> S` and `X -p-> S`, if `f` is surjective and syntomic, `p` is syntomic, and
`q` is locally of finite presentation, then `q` is syntomic. -/
@[stacks 02K3]
theorem syntomic_of_surjective_syntomic_of_comp_syntomic_of_locallyOfFinitePresentation
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] (hf : Syntomic f) (hcomm : f ≫ q = p)
    (hp : Syntomic p) (hq : LocallyOfFinitePresentation q) :
    Syntomic q := sorry

end AlgebraicGeometry
