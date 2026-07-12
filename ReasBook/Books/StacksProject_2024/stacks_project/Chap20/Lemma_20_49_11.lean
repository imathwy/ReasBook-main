import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => DerivedCategory ModX
local notation "Mod[" U "]" => openSubspaceModuleCategory X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation:max "H^" q:max => DerivedCategory.homologyFunctor ModX q

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]

/- Domain-style sampling for Lemma 20.49.11:
- primary domain: perfect derived `𝒪_X`-modules, their cohomology sheaves, and the
  finite-free stalk locus on a ringed space with local stalk rings;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `openSubspaceModuleCategory`,
  `moduleRestrictionToOpenDerived`,
  `ModuleDerived.cohomologyStalk`,
  `ModuleDerived.cohomologyStalkIsFiniteFree`,
  `RingedSpace.stalkModuleCat`,
  `DerivedCategory.homologyFunctor`,
  `SheafOfModules.IsFiniteLocallyFree`,
  `DerivedCategory.IsPerfect`,
  `SheafOfModules.exists_open_neighborhood_free_over_of_stalk_free`;
- best owner abstraction:
  `source-facing`: the finite-free cohomology-stalk locus and its associated open subset;
  `core/canonical`: `derivedCategoryCohomologyInProperty`,
    `openSubspaceModuleCategory`, `moduleRestrictionToOpenDerived`,
    `ModuleDerived.cohomologyStalk`, `ModuleDerived.cohomologyStalkIsFiniteFree`,
    `RingedSpace.stalkModuleCat`, `DerivedCategory.homologyFunctor`,
    `SheafOfModules.IsFiniteLocallyFree`, `DerivedCategory.IsPerfect`;
  `bridge/view`: the comparison between the stalkwise finite-free locus and the canonical
    cohomology-in-property owner for the restricted derived object.

Primitive data are only the perfect derived object `E`, the cohomology sheaves `(H^i).obj E`,
and the canonical stalk-module owner `RingedSpace.stalkModuleCat`. The open-condition side should
therefore be expressed through the Chapter 13 owner
`derivedCategoryCohomologyInProperty` applied to `SheafOfModules.IsFiniteLocallyFree`, while the
stalk cohomology object stays bundled as a module over `𝒪_{X, x}` instead of being
unpacked to its underlying type in the public API. -/

namespace ModuleDerived

/-- The stalk of the degree-`i` cohomology module of `E` at `x`, bundled as a module over the
stalk ring `𝒪_{X, x}`. -/
abbrev cohomologyStalk (E : DModX) (i : ℤ) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat ((H^i).obj E) x

/-- The degree-`i` cohomology stalk of `E` at `x` is finite free over `𝒪_{X, x}`. -/
def cohomologyStalkIsFiniteFree (E : DModX) (i : ℤ) (x : X) : Prop :=
  Module.Free (X.presheaf.stalk x) (cohomologyStalk E i x) ∧
    Module.Finite (X.presheaf.stalk x) (cohomologyStalk E i x)

end ModuleDerived

open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived

namespace DerivedCategory

/-- The set of points where every cohomology stalk of `E` is finite free over the corresponding
stalk ring. -/
def finiteFreeCohomologyStalkLocus (E : DModX) : Set X :=
  {x | ∀ i : ℤ, cohomologyStalkIsFiniteFree E i x}

omit [CategoryWithHomology ModX]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
@[simp] theorem mem_finiteFreeCohomologyStalkLocus (E : DModX) (x : X) :
    x ∈ finiteFreeCohomologyStalkLocus E ↔ ∀ i : ℤ, cohomologyStalkIsFiniteFree E i x :=
  Iff.rfl

-- Proof sketch: represent `E` locally by a strictly perfect complex. At a point whose cohomology
-- stalks are all finite free, apply Lemma `17.11.7` to make the top cohomology locally free and
-- Lemma `20.46.5` to split off the top term locally; then shorten the strict-perfect complex and
-- iterate on its length.
/-- Lemma 20.49.11: for a perfect derived `𝒪_X`-module on a ringed space whose stalk
rings are local, the locus where every cohomology stalk is a finite free `𝒪_{X, x}`-
module is open. -/
@[stacks 0GT1]
theorem isOpen_finiteFreeCohomologyStalkLocus
    (E : DModX) (hperfect : IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsOpen (finiteFreeCohomologyStalkLocus E) := sorry

/-- The open subset cut out by the finite-free cohomology-stalk locus of a perfect derived
`𝒪_X`-module. -/
def finiteFreeCohomologyStalkOpen
    (E : DModX) (hperfect : IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    Opens X.carrier :=
  ⟨finiteFreeCohomologyStalkLocus E, isOpen_finiteFreeCohomologyStalkLocus E hperfect hlocal⟩

@[simp] theorem coe_finiteFreeCohomologyStalkOpen
    (E : DModX) (hperfect : IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    (finiteFreeCohomologyStalkOpen E hperfect hlocal : Set X) =
      finiteFreeCohomologyStalkLocus E :=
  rfl

@[simp] theorem mem_finiteFreeCohomologyStalkOpen
    (E : DModX) (hperfect : IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) (x : X) :
    x ∈ finiteFreeCohomologyStalkOpen E hperfect hlocal ↔
      ∀ i : ℤ, cohomologyStalkIsFiniteFree E i x :=
  Iff.rfl

-- Proof sketch: every point of the locus admits, by the same local splitting argument as in the
-- source proof, a neighborhood on which the restricted cohomology sheaves are finite locally free
-- in all degrees; these neighborhoods lie inside the locus and cover its induced open subset.
/-- On the open finite-free cohomology-stalk locus of a perfect complex, all cohomology sheaves
become finite locally free after restriction. -/
theorem cohomologyIsFiniteLocallyFreeOn_finiteFreeCohomologyStalkLocus
    (E : DModX) (hperfect : IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    derivedCategoryCohomologyInProperty
      (SheafOfModules.IsFiniteLocallyFree :
        ObjectProperty (Mod[finiteFreeCohomologyStalkOpen E hperfect hlocal]))
      ((DRes[finiteFreeCohomologyStalkOpen E hperfect hlocal]).obj E) := by
  sorry

-- Proof sketch: a locally free trivialization on an open neighborhood inside `U` makes each
-- cohomology stalk finite free at points of that neighborhood. Applying this to every degree
-- shows that each point of `U` belongs to the locus by definition.
/-- Any open subset on which all cohomology sheaves of `E` are finite locally free is contained
in the finite-free cohomology-stalk locus. -/
theorem subset_finiteFreeCohomologyStalkLocus_of_cohomologyIsFiniteLocallyFreeOnOpen
    (E : DModX) (U : Opens X.carrier)
    (hU :
      derivedCategoryCohomologyInProperty
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (Mod[U]))
        ((DRes[U]).obj E)) :
    (U : Set X) ⊆ finiteFreeCohomologyStalkLocus E := sorry

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace
