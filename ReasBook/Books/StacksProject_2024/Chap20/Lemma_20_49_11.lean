import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The degree-`i` cohomology `\mathcal O_X`-module of a derived `\mathcal O_X`-module `E`. -/
abbrev derivedCohomologyModule (X : RingedSpace.{u}) (E : ModuleDerived X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj E

/-- The underlying type-valued presheaf of an `\mathcal O_X`-module. -/
abbrev underlyingPresheaf (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) :
    TopCat.Presheaf (Type u) X :=
  ℱ.val.presheaf ⋙ forget Ab

/-- The stalk of an `\mathcal O_X`-module, regarded as an underlying type. -/
abbrev stalkType (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) : Type u :=
  TopCat.Presheaf.stalk (underlyingPresheaf X ℱ) x

/-- The stalk of an `\mathcal O_X`-module inherits its additive group structure. -/
instance stalkAddCommGroup (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) :
    AddCommGroup (stalkType X ℱ x) := sorry

/-- The stalk of an `\mathcal O_X`-module carries its natural `\mathcal O_{X, x}`-module
structure. -/
instance stalkModule (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) :
    Module (X.presheaf.stalk x) (stalkType X ℱ x) := sorry

/-- The stalk of the degree-`i` cohomology module of `E` at `x`, viewed as a type over the stalk
ring `\mathcal O_{X, x}`. -/
abbrev derivedCohomologyStalk (E : ModuleDerived X) (i : ℤ) (x : X) : Type u :=
  stalkType X (derivedCohomologyModule X E i) x

/-- The degree-`i` cohomology stalk of `E` at `x` is finite free over `\mathcal O_{X, x}`. -/
def cohomologyStalkIsFiniteFree (E : ModuleDerived X) (i : ℤ) (x : X) : Prop :=
  Module.Free (X.presheaf.stalk x) (derivedCohomologyStalk E i x) ∧
    Module.Finite (X.presheaf.stalk x) (derivedCohomologyStalk E i x)

/-- The set of points where every cohomology stalk of `E` is finite free over the corresponding
stalk ring. -/
def finiteFreeCohomologyStalkLocus (E : ModuleDerived X) : Set X :=
  {x | ∀ i : ℤ, cohomologyStalkIsFiniteFree E i x}

/-- The restriction of every cohomology sheaf of `E` to the open subspace `U` is finite locally
free, expressed by local triviality inside `U`. -/
def cohomologyIsFiniteLocallyFreeOnOpen (E : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  ∀ i : ℤ, ∀ x : X, x ∈ U →
    ∃ V : Opens X.carrier, x ∈ V ∧ V ≤ U ∧
      ∃ I : Type u, Finite I ∧
        Nonempty ((derivedCohomologyModule X E i).over V ≅ SheafOfModules.free.{u} I)

-- Proof sketch: represent `E` locally by a strictly perfect complex. At a point whose cohomology
-- stalks are all finite free, apply Lemma `17.11.7` to make the top cohomology locally free and
-- Lemma `20.46.5` to split off the top term locally; then shorten the strict-perfect complex and
-- iterate on its length.
/-- Lemma 20.49.11: for a perfect derived `\mathcal O_X`-module on a ringed space whose stalk
rings are local, the locus where every cohomology stalk is a finite free `\mathcal O_{X, x}`-
module is open. -/
theorem isOpen_finiteFreeCohomologyStalkLocus
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsOpen (finiteFreeCohomologyStalkLocus E) := sorry

/-- The open subset where every cohomology stalk of `E` is finite free. -/
def finiteFreeCohomologyStalkOpen
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) : Opens X.carrier :=
  ⟨finiteFreeCohomologyStalkLocus E, isOpen_finiteFreeCohomologyStalkLocus E hperfect hlocal⟩

-- Proof sketch: every point of the locus admits, by the same local splitting argument as in the
-- source proof, a neighborhood on which the restricted cohomology sheaves are finite locally free
-- in all degrees; these neighborhoods lie inside the locus and cover the open subset above.
/-- On the finite-free cohomology-stalk locus of a perfect complex, all cohomology sheaves become
finite locally free after restriction. -/
theorem cohomologyIsFiniteLocallyFreeOnOpen_finiteFreeCohomologyStalkOpen
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    cohomologyIsFiniteLocallyFreeOnOpen E (finiteFreeCohomologyStalkOpen E hperfect hlocal) :=
  sorry

-- Proof sketch: a locally free trivialization on an open neighborhood inside `U` makes each
-- cohomology stalk finite free at points of that neighborhood. Applying this to every degree
-- shows that each point of `U` belongs to the locus by definition.
/-- Any open subset on which all cohomology sheaves of `E` are finite locally free is contained
in the finite-free cohomology-stalk locus. -/
theorem subset_finiteFreeCohomologyStalkLocus_of_cohomologyIsFiniteLocallyFreeOnOpen
    (E : ModuleDerived X) (U : Opens X.carrier)
    (hU : cohomologyIsFiniteLocallyFreeOnOpen E U) :
    (U : Set X) ⊆ finiteFreeCohomologyStalkLocus E := sorry

end

end AlgebraicGeometry.RingedSpace
