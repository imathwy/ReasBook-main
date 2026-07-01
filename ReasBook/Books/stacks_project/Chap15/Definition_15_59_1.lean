import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.RingTheory.Flat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace CochainComplex

section

variable {R : Type u} [Ring R]

/-- A cochain complex of `R`-modules is termwise free if each module `K^n` is free. -/
def IsTermwiseFree (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Free R (K.X n : Type u)

end

section

variable {R : Type u} [CommRing R]

/-- A cochain complex of `R`-modules is termwise flat if each module `K^n` is flat. -/
def IsTermwiseFlat (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n : Type u)

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- A cochain complex in a monoidal preadditive category is K-flat if totalized tensoring with it
preserves acyclic cochain complexes. Definition 15.59.1 is the specialization to complexes of
modules over a commutative ring. -/
def IsKFlat (K : CochainComplex C ℤ) : Prop :=
  ∀ ⦃M : CochainComplex C ℤ⦄ [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
    (HomologicalComplex.tensorObj M K).Acyclic

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

-- Proof sketch: unfold `CochainComplex.IsKFlat`; the right-hand side is exactly the defining
-- acyclicity condition for totalized tensoring with `K`.
/-- A cochain complex is K-flat exactly when totalized tensoring with it preserves acyclic
cochain complexes. -/
theorem isKFlat_iff (K : CochainComplex C ℤ) :
    K.IsKFlat ↔
      ∀ ⦃M : CochainComplex C ℤ⦄
        [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
        (HomologicalComplex.tensorObj M K).Acyclic :=
  Iff.rfl

end

end CochainComplex

namespace HomologicalComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- The K-flatness owner for cochain complexes, viewed through the canonical identification
`HomologicalComplex C (ComplexShape.up ℤ) = CochainComplex C ℤ`. This bridge lets homotopy-category
objects use the same postfix surface `K.IsKFlat` on their `.as` representatives. -/
abbrev IsKFlat (K : HomologicalComplex C (ComplexShape.up ℤ)) : Prop :=
  CochainComplex.IsKFlat K

end

end HomologicalComplex

namespace HomotopyCategory

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- The K-flatness owner for objects of the homotopy category of cochain complexes. This is the
canonical `K(C)`-level surface for the representative-level predicate on `K.as`. -/
abbrev IsKFlat (K : HomotopyCategory C (ComplexShape.up ℤ)) : Prop :=
  K.as.IsKFlat

end

end HomotopyCategory
