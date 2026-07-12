import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [MonoidalCategory X.Modules] [BraidedCategory X.Modules]

-- Semantic recall: `lean_leansearch` surfaced the scheme-module predicates
-- `SheafOfModules.IsQuasicoherent` and categorical finite-presentability. Nearby Chapter 28
-- algebra entries use `CommMon X.Modules` for `\mathcal O_X`-algebras, while Lemma 28.22.3
-- records "directed colimit of subobjects" as a directed subset of `Subobject` with supremum `⊤`.

/-- A commutative `\mathcal O_X`-algebra object is of finite type if it is a quotient of a
finitely presentable algebra object. This is the algebra-object analogue of finite generation
used to describe finite type subalgebras. -/
def IsFiniteTypeAlgebra (A : CommMon X.Modules) : Prop :=
  ∃ P : CommMon X.Modules, IsFinitelyPresentable.{u} P ∧ ∃ π : P ⟶ A, Epi π

/-- The finite type quasi-coherent subalgebras of a commutative `\mathcal O_X`-algebra, represented
as subobjects in `CommMon X.Modules`. -/
def finiteTypeQuasiCoherentSubalgebras (A : CommMon X.Modules) : Set (Subobject A) :=
  { B | ((B : CommMon X.Modules).X).IsQuasicoherent ∧
      IsFiniteTypeAlgebra (B : CommMon X.Modules) }

/-- Membership in the set of finite type quasi-coherent subalgebras. -/
theorem mem_finiteTypeQuasiCoherentSubalgebras (A : CommMon X.Modules) (B : Subobject A) :
    B ∈ finiteTypeQuasiCoherentSubalgebras A ↔
      ((B : CommMon X.Modules).X).IsQuasicoherent ∧
        IsFiniteTypeAlgebra (B : CommMon X.Modules) := sorry

/-- Lemma 28.22.11: let `X` be a quasi-compact and quasi-separated scheme, and let `A` be a
quasi-coherent `\mathcal O_X`-algebra. Then `A` is the directed colimit of its finite type
quasi-coherent `\mathcal O_X`-subalgebras. In `CommMon X.Modules`, these subalgebras are
subobjects of `A`; being a directed colimit is recorded by directedness of the corresponding
subset of `Subobject A` and by its supremum being `⊤`. -/
@[stacks 05JT]
theorem finiteTypeQuasiCoherentSubalgebras_isDirectedColimit
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) [A.X.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
      IsLUB (finiteTypeQuasiCoherentSubalgebras A) (⊤ : Subobject A) := sorry

end AlgebraicGeometry.Scheme.Modules
