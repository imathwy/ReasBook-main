import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (p : GrothendieckTopology.Point.{max u v} J)

/- Domain-style sampling:
- primary domain: points of a Grothendieck topology and their stalk functors on set-valued
  sheaves/presheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`,
  `ExactFunctor.of`,
  the canonical `PreservesColimits` instances on `p.sheafFiber` and `p.presheafFiber`;
- source/core/bridge triage:
  `source-facing`: the five clauses of Lemma 18.36.1 about stalks of set-valued
    sheaves/presheaves at a point;
  `core/canonical`: the owner point `p` together with the canonical stalk functors
    `p.sheafFiber`, `p.presheafFiber`, and the comparison
    `p.presheafToSheafCompSheafFiberIso`, plus the exact-functor and
    colimit-preservation owners built from them;
  `bridge/view`: none; this item is a direct owner recall rather than a second wrapper layer.
- primitive data: the point `p`, the presheaf/sheaf `ℱ`, and the ambient topology `J`;
- derived API: the sheafification comparison, exactness, and colimit-preservation facts. -/

section Sheafification

/-
Lemma 18.36.1 (1): for a set-valued presheaf `ℱ`, the canonical comparison from the stalk of the
sheafification to the original stalk is the component at `ℱ` of the owner natural isomorphism
`p.presheafToSheafCompSheafFiberIso (Type (max u v))`.
-/
variable [HasWeakSheafify J (Type (max u v))]

#check
  (p.presheafToSheafCompSheafFiberIso (Type (max u v)) :
    presheafToSheaf J (Type (max u v)) ⋙ p.sheafFiber ≅ p.presheafFiber)

end Sheafification

section Exactness

/- Lemma 18.36.1 (2): the stalk functor on sheaves of sets at a point of a site is exact. This
is the canonical bundled exact functor `ExactFunctor.of p.sheafFiber`. -/
#check
  (ExactFunctor.of p.sheafFiber :
    Sheaf J (Type (max u v)) ⥤ₑ Type (max u v))

end Exactness

/- Lemma 18.36.1 (3): the stalk functor on sheaves of sets at a point of a site commutes with
arbitrary colimits. This is the canonical `PreservesColimits` instance on `p.sheafFiber`. -/
#synth PreservesColimits (p.sheafFiber : Sheaf J (Type (max u v)) ⥤ Type (max u v))

section Exactness

/- Lemma 18.36.1 (4): the stalk functor on presheaves of sets at a point of a site is exact.
This is the canonical bundled exact functor `ExactFunctor.of p.presheafFiber`. -/
#check
  (ExactFunctor.of p.presheafFiber :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤ₑ Type (max u v))

end Exactness

/- Lemma 18.36.1 (5): the stalk functor on presheaves of sets at a point of a site commutes with
arbitrary colimits. This is the canonical `PreservesColimits` instance on `p.presheafFiber`. -/
#synth PreservesColimits (p.presheafFiber : (Cᵒᵖ ⥤ Type (max u v)) ⥤ Type (max u v))

end CategoryTheory
