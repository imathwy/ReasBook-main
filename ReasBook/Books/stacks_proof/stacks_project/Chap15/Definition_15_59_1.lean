import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.StacksAttribute

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

/-- Definition 15.59.1: a cochain complex in a monoidal preadditive category is K-flat if
totalized tensoring with it preserves acyclic cochain complexes. This is the ambient categorical
form of the module-valued definition. -/
@[stacks 06XZ]
def IsKFlat (K : CochainComplex C ℤ) : Prop :=
  ∀ ⦃M : CochainComplex C ℤ⦄ [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
    (HomologicalComplex.tensorObj M K).Acyclic

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- Helper for Definition 15.59.1: a K-flat complex sends each acyclic input complex to an acyclic
tensor totalization. -/
lemma acyclic_tensorObj_of_isKFlat {K : CochainComplex C ℤ} (hK : K.IsKFlat)
    {M : CochainComplex C ℤ} [_h : HomologicalComplex.HasTensor M K] (hM : M.Acyclic) :
    (HomologicalComplex.tensorObj M K).Acyclic := by
  -- Unpack the defining preservation property of `IsKFlat` on the given acyclic complex `M`.
  exact hK hM

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

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

-- Proof sketch: the `HomologicalComplex` surface is definitionally the cochain-complex owner, so
-- the iff statement is just an explicit unfolding of that owner.
/-- A homological complex in cochain indexing is K-flat exactly when totalized tensoring with it
preserves acyclic complexes. -/
theorem isKFlat_iff (K : HomologicalComplex C (ComplexShape.up ℤ)) :
    K.IsKFlat ↔
      ∀ ⦃M : HomologicalComplex C (ComplexShape.up ℤ)⦄
        [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
        (HomologicalComplex.tensorObj M K).Acyclic := by
  -- Unfold both owner predicates so the statement becomes definitionally identical.
  simp [HomologicalComplex.IsKFlat, CochainComplex.IsKFlat]

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

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

-- Proof sketch: the homotopy-category owner is defined by evaluating `IsKFlat` on the chosen
-- representative complex `K.as`, so unfolding gives the claimed iff immediately.
/-- A homotopy-category object is K-flat exactly when its chosen representative complex is
K-flat. -/
theorem isKFlat_iff (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    K.IsKFlat ↔ K.as.IsKFlat := by
  -- Unfold the homotopy-category view to read K-flatness on the representative complex.
  rfl

end

end HomotopyCategory
