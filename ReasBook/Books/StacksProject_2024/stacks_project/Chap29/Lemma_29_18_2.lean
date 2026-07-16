import Mathlib
import StacksProject_2024.stacks_project.Chap10.Proposition_10_162_16
import StacksProject_2024.stacks_project.Chap29.Lemma_29_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical scheme-morphism owner `LocallyOfFiniteType`, and the
-- local Chapter 10 / 29 API already provides the ring-level Nagata examples together with the
-- scheme theorem `nagata_of_locallyOfFiniteType`. The source clauses are therefore best recorded
-- as direct specializations over `Spec`.

section

variable {k : Type u} [Field k]

/-- Lemma 29.18.2 (1): any scheme locally of finite type over a field is Nagata. -/
theorem nagata_of_locallyOfFiniteType_over_field
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] :
    Nagata X.left := sorry

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Lemma 29.18.2 (2): any scheme locally of finite type over a Noetherian complete local ring is
Nagata. -/
theorem nagata_of_locallyOfFiniteType_over_noetherian_completeLocalRing
    (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom] :
    Nagata X.left := sorry

end

section

/-- Lemma 29.18.2 (3): any scheme locally of finite type over `Spec ℤ` is Nagata. -/
theorem nagata_of_locallyOfFiniteType_over_integers
    (X : Over (Spec (CommRingCat.of ℤ))) [LocallyOfFiniteType X.hom] :
    Nagata X.left := sorry

end

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero R]

/-- Lemma 29.18.2 (4): any scheme locally of finite type over a Dedekind ring of characteristic
zero is Nagata. -/
theorem nagata_of_locallyOfFiniteType_over_dedekindDomain_charZero
    (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom] :
    Nagata X.left := sorry

end

end AlgebraicGeometry.Scheme
