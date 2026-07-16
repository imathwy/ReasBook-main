import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import StacksProject_2024.stacks_project.Chap13.Definition_13_36_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap22.RLinearTriangulatedEquivalence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

local notation "DMod(" A ")" => DerivedCategory (ModuleCat A)
local notation "Bimod(" R "," A "," B ")" => ModuleCat (TensorProduct R A Bᵐᵒᵖ)

/-- Source-facing Chapter `22` bridge: the forward functor of an `R`-linear triangulated
equivalence `e : D(A) ≌ D(B)` is realized by the chosen derived tensor functor attached to the
`(A, B)`-bimodule `N`. The concrete construction of `- ⊗ᴸ[A] N` is kept abstract here as the
owner `derivedTensorWithBimodule`, matching the surrounding Chapter `22` pattern of quantifying
over the chosen derived-tensor implementation surface rather than over an arbitrary predicate. -/
def CategoryTheory.RLinearTriangulatedEquivalence.IsDerivedTensorWithBimodule
    {R : Type u} [CommRing R]
    {A : Type u} [Ring A] [Algebra R A]
    {B : Type u} [Ring B] [Algebra R B]
    [CategoryTheory.Linear R (DMod(A))]
    [CategoryTheory.Linear R (DMod(B))]
    (e : RLinearTriangulatedEquivalence R (DMod(A)) (DMod(B)))
    (derivedTensorWithBimodule : Bimod(R,A,B) → DMod(A) ⥤ DMod(B))
    (N : Bimod(R,A,B)) : Prop :=
  Nonempty (e.functor ≅ derivedTensorWithBimodule N)

/-- The bridge `e.IsDerivedTensorWithBimodule derivedTensorWithBimodule N` says exactly that
`e.functor` is isomorphic to the chosen derived tensor functor of `N`. -/
theorem CategoryTheory.RLinearTriangulatedEquivalence.isDerivedTensorWithBimodule_iff
    {R : Type u} [CommRing R]
    {A : Type u} [Ring A] [Algebra R A]
    {B : Type u} [Ring B] [Algebra R B]
    [CategoryTheory.Linear R (DMod(A))]
    [CategoryTheory.Linear R (DMod(B))]
    (e : RLinearTriangulatedEquivalence R (DMod(A)) (DMod(B)))
    (derivedTensorWithBimodule : Bimod(R,A,B) → DMod(A) ⥤ DMod(B))
    (N : Bimod(R,A,B)) :
    e.IsDerivedTensorWithBimodule derivedTensorWithBimodule N ↔
      Nonempty (e.functor ≅ derivedTensorWithBimodule N) :=
  Iff.rfl

-- Stacks tag evidence is consistent for this item: both the item tag and source URL give `09SC`.
-- Semantic recall hits: `DerivedCategory.Q`, shifted Homs, `Functor.IsEquivalence`,
-- `Functor.IsTriangulated`, and `Module.Flat`; local Chapter 22 precedent uses an explicit
-- derived-tensor parameter when the concrete DG tensor construction is unavailable.

/-- Lemma 22.37.8 (1): for `R`-algebras `A` and `B`, an `R`-linear equivalence
`D(A) ≌ D(B)` of triangulated categories is equivalent to the existence of a perfect weak
generator `P : D(B)` whose shifted self-Homs vanish away from degree zero and whose degree-zero
endomorphism algebra is `A`. Here `P.IsPerfect` is the canonical Chapter `15` owner for being
represented by a bounded finite complex of finite projective `B`-modules. -/
@[stacks 09SC]
theorem exists_rLinearTriangulatedEquivalence_iff_exists_finiteProjective_generator_selfExt
    {R : Type u} [CommRing R]
    {A : Type u} [Ring A] [Algebra R A]
    {B : Type u} [Ring B] [Algebra R B]
    [CategoryTheory.Linear R (DMod(A))]
    [CategoryTheory.Linear R (DMod(B))] :
    Nonempty
      (RLinearTriangulatedEquivalence
        R (DMod(A)) (DMod(B))) ↔
      ∃ P : DMod(B),
        P.IsPerfect ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] A) := sorry

/-- Lemma 22.37.8 (2): if `B` is flat as an `R`-module, the same `R`-linear triangulated
equivalence condition is equivalent to the existence of an `(A, B)`-bimodule `N`, represented as a
module over `A ⊗[R] Bᵐᵒᵖ`, whose derived tensor functor is the forward functor of an
`R`-linear triangulated equivalence. In the current abstract interface, the chosen Chapter `22`
owner `derivedTensorWithBimodule` supplies the functor `- ⊗ᴸ[A] N`, and
`e.IsDerivedTensorWithBimodule derivedTensorWithBimodule N` records the comparison
`e.functor ≅ derivedTensorWithBimodule N`. -/
@[stacks 09SC]
theorem exists_rLinearTriangulatedEquivalence_iff_exists_bimodule_derivedTensor_equivalence_of_flat
    {R : Type u} [CommRing R]
    {A : Type u} [Ring A] [Algebra R A]
    {B : Type u} [Ring B] [Algebra R B]
    [Module.Flat R B]
    [CategoryTheory.Linear R (DMod(A))]
    [CategoryTheory.Linear R (DMod(B))]
    (derivedTensorWithBimodule : Bimod(R,A,B) → DMod(A) ⥤ DMod(B)) :
    Nonempty
      (RLinearTriangulatedEquivalence
        R (DMod(A)) (DMod(B))) ↔
      ∃ (N : Bimod(R, A, B)) (e : RLinearTriangulatedEquivalence R (DMod(A)) (DMod(B))),
        e.IsDerivedTensorWithBimodule derivedTensorWithBimodule N := sorry

end
