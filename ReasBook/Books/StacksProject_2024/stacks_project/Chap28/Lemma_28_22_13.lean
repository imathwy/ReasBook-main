import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_22_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [MonoidalCategory X.Modules] [BraidedCategory X.Modules]

-- Semantic recall: `lean_leansearch` found the scheme-module predicates
-- `SheafOfModules.IsQuasicoherent` and categorical finite-presentability, while nearby
-- Chapter 28 files use `CommMon X.Modules` for quasi-coherent `\mathcal O_X`-algebras and
-- `Subobject` families with supremum `⊤` for "directed colimit of subalgebras".

/-- The finite quasi-coherent subalgebras of a commutative `\mathcal O_X`-algebra, represented as
subobjects in `CommMon X.Modules`. "Finite" is imposed on the underlying module object. -/
def finiteQuasiCoherentSubalgebras (A : CommMon X.Modules) : Set (Subobject A) :=
  { B | ((B : CommMon X.Modules).X).IsQuasicoherent ∧
      ((B : CommMon X.Modules).X).IsFiniteType }

/-- Membership in the finite quasi-coherent subalgebra family. -/
theorem mem_finiteQuasiCoherentSubalgebras (A : CommMon X.Modules) (B : Subobject A) :
    B ∈ finiteQuasiCoherentSubalgebras A ↔
      ((B : CommMon X.Modules).X).IsQuasicoherent ∧
        ((B : CommMon X.Modules).X).IsFiniteType := sorry

/-- The chapter-local finite-subalgebra formulation of an integral commutative
`\mathcal O_X`-algebra object: finite type quasi-coherent subalgebras are finite over
`\mathcal O_X`. -/
def IsIntegralAlgebra (A : CommMon X.Modules) : Prop :=
  ∀ B : Subobject A, B ∈ finiteTypeQuasiCoherentSubalgebras A →
    ((B : CommMon X.Modules).X).IsFiniteType

/-- Integral algebra objects make every finite type quasi-coherent subalgebra finite. -/
theorem isIntegralAlgebra_iff_finiteTypeSubalgebrasFinite (A : CommMon X.Modules) :
    IsIntegralAlgebra A ↔
      ∀ B : Subobject A, B ∈ finiteTypeQuasiCoherentSubalgebras A →
        ((B : CommMon X.Modules).X).IsFiniteType := sorry

/-- Lemma 28.22.13 (1): if `X` is quasi-compact and quasi-separated and `A` is an
integral quasi-coherent `\mathcal O_X`-algebra, then `A` is the directed colimit of its finite
quasi-coherent `\mathcal O_X`-subalgebras. As in Lemma 28.22.11, the colimit assertion is
recorded by directedness of the corresponding subobject family and by its supremum being `⊤`. -/
@[stacks 0817]
theorem finiteQuasiCoherentSubalgebras_isDirectedColimit_of_isIntegralAlgebra
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) [A.X.IsQuasicoherent] (hA : IsIntegralAlgebra A) :
    DirectedOn (· ≤ ·) (finiteQuasiCoherentSubalgebras A) ∧
      IsLUB (finiteQuasiCoherentSubalgebras A) (⊤ : Subobject A) := sorry

/-- Lemma 28.22.13 (2): under the same hypotheses, the integral quasi-coherent
`\mathcal O_X`-algebra `A` is a filtered colimit of finite and finitely presented
quasi-coherent `\mathcal O_X`-algebras. The filtered category `I`, diagram `B`, and cocone legs
are the Lean counterparts of the direct system and its maps to `A`. -/
@[stacks 0817]
theorem exists_filteredSystem_finite_finitelyPresentable_algebra_colimit_of_isIntegralAlgebra
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) [A.X.IsQuasicoherent] (hA : IsIntegralAlgebra A) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (B : I ⥤ CommMon X.Modules) (φ : B ⟶ (Functor.const I).obj A),
        ∃ (_ : IsColimit (Cocone.mk A φ))
          (_ : ∀ i : I, (B.obj i).X.IsFiniteType)
          (_ : ∀ i : I, (B.obj i).X.IsQuasicoherent),
          ∀ i : I, IsFinitelyPresentable (B.obj i) := sorry

end AlgebraicGeometry.Scheme.Modules
