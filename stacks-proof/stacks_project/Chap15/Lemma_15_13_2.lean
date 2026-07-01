import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CommRingCat

universe u

section

variable {A : Type u} [CommRing A]

/-- The object property on `Under (CommRingCat.of A)` selecting finite étale `A`-algebras. -/
abbrev finiteEtaleAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (Under (CommRingCat.of A)) :=
  fun B : Under (CommRingCat.of A) ↦ (Hom.hom B.hom).Finite ∧ (Hom.hom B.hom).Etale

/-- The category of finite étale `A`-algebras, viewed as a full subcategory of
`Under (CommRingCat.of A)`. -/
abbrev finiteEtaleAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (finiteEtaleAlgebraProperty A).FullSubcategory

variable (I : Ideal A)

-- Proof sketch: reduction modulo `I` is base change along `A → A ⧸ I`. Finiteness of the
-- structural map descends under tensoring with the finite `A`-module `A ⧸ I`, and étaleness is
-- preserved by base change, so finite étale `A`-algebras remain finite étale after reduction.
/-- Reduction modulo `I` preserves finite étale `A`-algebras. -/
theorem quotientTensorProd_obj_mem_finiteEtaleAlgebras :
    ∀ B : finiteEtaleAlgebras A,
      finiteEtaleAlgebraProperty (A ⧸ I)
        (((CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I))).obj B.obj) := sorry

/-- The reduction functor `B ↦ B / I B`, formalized as base change along `A → A ⧸ I`, on the
category of finite étale `A`-algebras. -/
abbrev quotientFiniteEtaleAlgebraFunctor :
    finiteEtaleAlgebras A ⥤ finiteEtaleAlgebras (A ⧸ I) :=
  ObjectProperty.lift
    (finiteEtaleAlgebraProperty (A ⧸ I))
    ((finiteEtaleAlgebraProperty A).ι ⋙
      (CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I)))
    (quotientTensorProd_obj_mem_finiteEtaleAlgebras I)

variable [HenselianRing A I]

-- Proof sketch: full faithfulness is controlled by lifting idempotents and sections across the
-- henselian pair, using the finite-algebra idempotent lifting criterion from the henselian TFAE.
-- Essential surjectivity comes from lifting a finite étale `A ⧸ I`-algebra to an étale
-- `A`-algebra and then isolating the finite integral-closure summand whose reduction is the given
-- special fiber.
/-- Lemma 15.13.2: if `(A, I)` is a henselian pair, then reduction modulo `I`, formalized by the
functor `B ↦ B / I B`, induces an equivalence between the category of finite étale `A`-algebras
and the category of finite étale `A ⧸ I`-algebras. -/
theorem quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing :
    Functor.IsEquivalence (quotientFiniteEtaleAlgebraFunctor I) := sorry

end
