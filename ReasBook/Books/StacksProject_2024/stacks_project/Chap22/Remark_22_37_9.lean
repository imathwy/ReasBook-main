import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import StacksProject_2024.Chap22.ModuleCatHasDerivedCategory
import StacksProject_2024.Chap22.RLinearTriangulatedEquivalence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {B : Type u} [Ring B] [Algebra R B]

local notation "DA" => DerivedCategory (ModuleCat A)
local notation "DB" => DerivedCategory (ModuleCat B)

variable [CategoryTheory.Linear R (DerivedCategory (ModuleCat A))]
variable [CategoryTheory.Linear R (DerivedCategory (ModuleCat B))]

-- Semantic recall note: the source-facing mathematical content is existential, so the refined
-- public API records `Nonempty` algebra equivalences rather than a fake chosen `def`.

/-- Remark 22.37.9 (1): if `D(A)` and `D(B)` are equivalent as `R`-linear triangulated
categories, then the centers of `A` and `B` are isomorphic as `R`-algebras. -/
@[stacks 09SD]
theorem nonempty_centerAlgEquiv_of_rLinearDerivedEquivalence
    (e : CategoryTheory.RLinearTriangulatedEquivalence R DA DB) :
    Nonempty (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B) := sorry

end

section

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- A center `R`-algebra equivalence between commutative `R`-algebras induces an `R`-algebra
equivalence of the algebras themselves. -/
theorem nonempty_algEquiv_of_nonempty_centerAlgEquiv
    (h : Nonempty (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B)) :
    Nonempty (A ≃ₐ[R] B) := sorry

local notation "DA" => DerivedCategory (ModuleCat A)
local notation "DB" => DerivedCategory (ModuleCat B)

/-- Remark 22.37.9 (2): if `A` and `B` are commutative and `D(A)` and `D(B)` are equivalent as
`R`-linear triangulated categories, then `A` and `B` are isomorphic as `R`-algebras. -/
@[stacks 09SD]
theorem nonempty_algEquiv_of_commutative_of_rLinearDerivedEquivalence
    [CategoryTheory.Linear R (DerivedCategory (ModuleCat A))]
    [CategoryTheory.Linear R (DerivedCategory (ModuleCat B))]
    (e : CategoryTheory.RLinearTriangulatedEquivalence R DA DB) :
    Nonempty (A ≃ₐ[R] B) := sorry

end
