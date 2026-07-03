import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CommRingCat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: étale `A`-algebras and reduction modulo an ideal;
- sampled owner declarations:
  `CommAlgCat`,
  `commAlgCatEquivUnder`,
  `CommRingCat.etale`,
  `ObjectProperty.lift`;
- best owner abstraction: the ambient category of `A`-algebras is canonically `CommAlgCat A`,
  equivalent to `Under (CommRingCat.of A)` via `commAlgCatEquivUnder`; the étale condition is
  therefore best expressed as an object property on `CommAlgCat A`, while the reduction functor is
  the base-change bridge to `CommAlgCat (A ⧸ I)`;
- primitive data: an object `B : CommAlgCat A`, equivalently an `A`-algebra with its structure
  morphism `A ⟶ B`;
- derived API: the étale object property on `CommAlgCat A`, the quotient/base-change functor
  `CommAlgCat A ⥤ CommAlgCat (A ⧸ I)`, its restriction to the étale full subcategory, its
  equivalence under a locally nilpotent ideal, and the induced henselian-ring instance.

Source/core/bridge triage:
- `source-facing`: reduction modulo `I` on the full subcategory of étale objects in
  `CommAlgCat A`;
- `core/canonical`: `CommAlgCat A`, `commAlgCatEquivUnder`, and `CommRingCat.etale`;
- `bridge/view`: the quotient/base-change functor on `CommAlgCat A`, obtained from the ordinary
  under-category base-change functor through `commAlgCatEquivUnder`.
-/

/-- The object property on `CommAlgCat A` selecting the étale `A`-algebras. -/
abbrev etaleAlgebraProperty (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat A) :=
  fun B : CommAlgCat A ↦
    CommRingCat.etale (((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom)

variable (I : Ideal A)

/-- Base change along `A → A ⧸ I`, formalizing the functor `B ↦ B / IB` on `A`-algebras, viewed
in the canonical owner category `CommAlgCat`. -/
abbrev quotientCommAlgFunctor : CommAlgCat A ⥤ CommAlgCat (A ⧸ I) :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    (CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I)) ⋙
      (commAlgCatEquivUnder (CommRingCat.of (A ⧸ I))).inverse

-- Proof sketch: an étale algebra stays étale after any base change, so applying the quotient
-- functor to an étale object of `CommAlgCat A` again lands in the étale full subcategory of
-- `CommAlgCat (A ⧸ I)`.
private theorem quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty :
    ∀ B : (etaleAlgebraProperty A).FullSubcategory,
      etaleAlgebraProperty (A ⧸ I) ((quotientCommAlgFunctor I).obj B.obj) := sorry

-- Proof sketch: essential surjectivity comes from lifting étale `A ⧸ I`-algebras across the
-- locally nilpotent quotient. Fullness comes from lifting morphisms by formal smoothness of étale
-- algebras. Faithfulness follows from the idempotent criterion for unramified morphisms together
-- with the fact that locally nilpotent ideals contain no nonzero idempotents.
/-- Lemma 15.11.2 (1): if `I` is locally nilpotent, then reduction modulo `I`, formalized by base
change along `A → A ⧸ I`, induces an equivalence between the full subcategories of étale objects
in `CommAlgCat A` and `CommAlgCat (A ⧸ I)`. -/
theorem quotientCommAlgFunctor_isEquivalence_on_etale_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) :
    Functor.IsEquivalence
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)) := sorry

-- Proof sketch: locally nilpotent ideals lie in the Jacobson radical, giving the Jacobson part of
-- henselianity. The factorization-lifting criterion is obtained by applying the étale
-- factorization lift of Lemma `15.9.5` and then using the equivalence from part `(1)` to descend
-- the resulting étale extension back to `A`.
/-- Lemma 15.11.2 (2): if `I` is locally nilpotent, then the pair `(A, I)` is henselian, i.e.
`A` is henselian at the ideal `I`. -/
instance henselianRing_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) : HenselianRing A I := sorry

end
