import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalCategory

universe u

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat R)}

/-- Tensoring `S` on the right with any finitely presented module preserves short exactness. -/
def TensorShortExactForFinitelyPresented (S : ShortComplex (ModuleCat R)) : Prop :=
  ∀ (Q : ModuleCat R) [Module.FinitePresentation R Q], (S.map (tensorRight Q)).ShortExact

/-- The equational lifting criterion for the first map of `S`. -/
def EquationalLiftingCriterion (S : ShortComplex (ModuleCat R)) : Prop :=
  ∀ {n m : ℕ} (x : Fin n → S.X₁) (y : Fin m → S.X₂) (a : Fin n → Fin m → R),
    (∀ i, S.f.hom (x i) = ∑ j, a i j • y j) →
      ∃ z : Fin m → S.X₁, ∀ i, x i = ∑ j, a i j • z j

/-- The finite free square lifting criterion for the first map of `S`. -/
def FiniteFreeSquareLiftingCriterion (S : ShortComplex (ModuleCat R)) : Prop :=
  ∀ {n m : ℕ}
    (u : ModuleCat.of R (Fin n →₀ R) ⟶ ModuleCat.of R (Fin m →₀ R)),
    HasLiftingProperty u S.f

/-- Postcomposition with `S.g` is surjective on maps from finitely presented modules. -/
def HomSurjectiveOnFinitelyPresented (S : ShortComplex (ModuleCat R)) : Prop :=
  ∀ (P : ModuleCat R) [Module.FinitePresentation R P],
    Function.Surjective fun φ : P ⟶ S.X₂ ↦ φ ≫ S.g

/-- `S` is a filtered colimit of split short exact sequences whose left term is constantly `S.X₁`
and whose cokernels are finitely presented. -/
def FilteredSplitColimitCriterion (S : ShortComplex (ModuleCat R)) : Prop :=
  ∃ (J : Type u) (_ : Category.{u} J) (_ : IsFiltered J)
    (F : J ⥤ ShortComplex (ModuleCat R))
    (_ : F ⋙ ShortComplex.π₁ ≅ (Functor.const J).obj S.X₁)
    (_ : ∀ j, Nonempty ((F.obj j).Splitting))
    (_ : ∀ j, Module.FinitePresentation R (F.obj j).X₃),
    ∃ e : colimit F ⟶ S, IsIso e

-- Proof sketch: identify universal exactness of the short exact sequence with flatness of the
-- cokernel module `S.X₃`, then combine the equational criterion for flatness, the finite
-- presentation lifting criterion, and Lazard-style filtered-colimit characterizations, translating
-- each flatness criterion back into the corresponding statement about the fixed short exact
-- sequence.
/-- Theorem 10.82.3: for a short exact sequence of `R`-modules, universal exactness is equivalent
to exactness after tensoring with every finitely presented module, to the equational lifting
criterion, to the finite free diagram lifting criterion, to surjectivity on `Hom` from finitely
presented modules, and to being a filtered colimit of split short exact sequences with constant
left term `S.X₁` and finitely presented cokernels. -/
theorem universallyExact_tfae (hS : S.ShortExact) :
    ([ S.UniversallyExact
     , TensorShortExactForFinitelyPresented S
     , EquationalLiftingCriterion S
     , FiniteFreeSquareLiftingCriterion S
     , HomSurjectiveOnFinitelyPresented S
     , FilteredSplitColimitCriterion S ] : List Prop).TFAE := sorry

end

end CategoryTheory.ShortComplex
