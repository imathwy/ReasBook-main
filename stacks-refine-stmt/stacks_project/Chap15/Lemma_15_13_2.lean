import Mathlib
import stacks_project.Chap15.Lemma_15_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CommRingCat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: finite étale `A`-algebras and reduction modulo an ideal in a henselian pair;
- sampled owner declarations:
  `commAlgCatEquivUnder`,
  `etaleAlgebraProperty`,
  `quotientCommAlgFunctor`,
  `HenselianRing`;
- best owner abstraction: the ambient category of `A`-algebras is canonically `CommAlgCat A`,
  and Chapter 15 already packages the étale condition by `etaleAlgebraProperty` together with the
  quotient/base-change functor `quotientCommAlgFunctor`; this file should therefore add only the
  extra finiteness condition and restrict that existing functor, rather than rebuilding a parallel
  owner in `Under (CommRingCat.of A)`;
- primitive data: an object `B : CommAlgCat A`, together with `Module.Finite A B` and
  `etaleAlgebraProperty A B`;
- derived API: the full subcategory of finite étale objects, the quotient functor on that
  subcategory, and its henselian-pair equivalence.

Source/core/bridge triage:
- `source-facing`: the category of finite étale `A`-algebras and reduction modulo `I`;
- `core/canonical`: `CommAlgCat A`, `etaleAlgebraProperty`, `quotientCommAlgFunctor`, and
  `HenselianRing A I`;
- `bridge/view`: the restriction of `quotientCommAlgFunctor I` to the finite étale full
  subcategory.
-/

/-- The object property on `CommAlgCat A` selecting the finite étale `A`-algebras. -/
abbrev finiteEtaleAlgebraProperty (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat A) :=
  fun B : CommAlgCat A ↦ Module.Finite A B ∧ etaleAlgebraProperty A B

/-- The category of finite étale `A`-algebras, viewed as a full subcategory of `CommAlgCat A`. -/
abbrev finiteEtaleAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (finiteEtaleAlgebraProperty A).FullSubcategory

variable (I : Ideal A)

-- Proof sketch: reduction modulo `I` is base change along `A → A ⧸ I`, formalized by
-- `quotientCommAlgFunctor I`. Finite modules remain finite after tensoring with `A ⧸ I`, and the
-- étale condition is already handled by the Chapter 15 owner `quotientCommAlgFunctor`.
/-- Reduction modulo `I` preserves finite étale `A`-algebras. -/
private theorem quotientCommAlgFunctor_obj_mem_finiteEtaleAlgebraProperty :
    ∀ B : finiteEtaleAlgebras A,
      finiteEtaleAlgebraProperty (A ⧸ I) ((quotientCommAlgFunctor I).obj B.obj) := sorry

/-- The reduction functor `B ↦ B / I B`, formalized as base change along `A → A ⧸ I`, on the
category of finite étale `A`-algebras. -/
abbrev quotientFiniteEtaleAlgebraFunctor :
    finiteEtaleAlgebras A ⥤ finiteEtaleAlgebras (A ⧸ I) :=
  ObjectProperty.lift
    (finiteEtaleAlgebraProperty (A ⧸ I))
    ((finiteEtaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
    (quotientCommAlgFunctor_obj_mem_finiteEtaleAlgebraProperty I)

variable [HenselianRing A I]

-- Proof sketch: fullness and faithfulness follow by lifting morphisms between finite étale
-- quotients across the henselian pair, while essential surjectivity lifts a finite étale
-- `A ⧸ I`-algebra to a finite étale `A`-algebra. The finite condition is stable under the lifted
-- algebra and its reduction, so the restricted quotient functor is an equivalence.
/-- Lemma 15.13.2: if `(A, I)` is a henselian pair, then reduction modulo `I`, formalized by the
functor `B ↦ B / I B`, induces an equivalence between the category of finite étale `A`-algebras
and the category of finite étale `A ⧸ I`-algebras. -/
theorem quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing :
    Functor.IsEquivalence (quotientFiniteEtaleAlgebraFunctor I) := sorry

end
