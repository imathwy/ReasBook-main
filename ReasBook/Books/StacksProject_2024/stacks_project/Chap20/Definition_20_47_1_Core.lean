import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Definition 20.47.1 core owners: the Chapter 20 pseudo-coherence predicates on complexes,
derived `𝒪_X`-modules, and degree-zero module sheaves. The open-cover criterion remains in
`Definition_20_47_1`. -/

local notation "ModX" => RingedSpace.Modules X
local notation "CpxOX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX
local notation "Mod[" U "]" => openSubspaceModuleCategory X U
local notation "Cpx[" U "]" => CochainComplex (Mod[U]) ℤ

open _root_.AlgebraicGeometry.RingedSpace.CochainComplex

namespace CochainComplex

/-- Definition 20.47.1 (complex `m`-version): a complex of `𝒪_X`-modules is
`m`-pseudo-coherent if there is an open covering of `X` such that on each member of the cover its
restriction admits a morphism from a strictly perfect complex inducing isomorphisms on cohomology
in degrees `> m` and an epimorphism in degree `m`. -/
@[stacks 08CB]
def IsMPseudoCoherent (E : CpxOX) (m : ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, ∃ Ei : Cpx[U i],
        ∃ α : Ei ⟶ restrictedComplexOnOpen X (U i) E,
          IsStrictlyPerfect Ei ∧
            (∀ j : ℤ, m < j →
              IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def IsPseudoCoherent (E : CpxOX) : Prop :=
  ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m

end CochainComplex

namespace ModuleDerived

/-- Definition 20.47.1 (derived `m`-version): a derived `𝒪_X`-module is
`m`-pseudo-coherent if it is represented by an `m`-pseudo-coherent complex. -/
@[stacks 08CB]
def IsMPseudoCoherent (E : DModX) (m : ℤ) : Prop :=
  ∃ K : CpxOX, ∃ _ : E ≅ DerivedCategory.Q.obj K, CochainComplex.IsMPseudoCoherent K m

/-- Definition 20.47.1 (derived version): an object of `D(𝒪_X)` is pseudo-coherent if
it is represented by a pseudo-coherent complex. -/
@[stacks 08CB]
def IsPseudoCoherent (E : DModX) : Prop :=
  ∃ K : CpxOX, ∃ _ : E ≅ DerivedCategory.Q.obj K, CochainComplex.IsPseudoCoherent K

/-- Unfolding `IsMPseudoCoherent` gives the representative-complex criterion from Definition
20.47.1. -/
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ K : CpxOX, ∃ _ : E ≅ DerivedCategory.Q.obj K,
        CochainComplex.IsMPseudoCoherent K m :=
  Iff.rfl

/-- Unfolding `IsPseudoCoherent` gives the pseudo-coherent representative criterion from
Definition 20.47.1. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (E : DModX) :
    IsPseudoCoherent E ↔
      ∃ K : CpxOX, ∃ _ : E ≅ DerivedCategory.Q.obj K,
        CochainComplex.IsPseudoCoherent K :=
  Iff.rfl

/-- A derived `𝒪_X`-module is pseudo-coherent exactly when it is `m`-pseudo-coherent
for every integer `m`. This is the degreewise companion characterization of the representative
owner. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent
    (E : DModX) :
    IsPseudoCoherent E ↔ ∀ m : ℤ, IsMPseudoCoherent E m :=
  sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules

variable {X : RingedSpace.{u}}

open AlgebraicGeometry.RingedSpace
local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => DerivedCategory ModX

/-- A sheaf of `𝒪_X`-modules is `m`-pseudo-coherent if its degree-zero realization in `D(𝒪_X)` is
`m`-pseudo-coherent. -/
abbrev IsMPseudoCoherent (ℱ : ModX) (m : ℤ) : Prop :=
  ModuleDerived.IsMPseudoCoherent
    ((DerivedCategory.singleFunctor ModX (0 : ℤ)).obj ℱ) m

/-- A sheaf of `𝒪_X`-modules is pseudo-coherent if its degree-zero realization in `D(𝒪_X)` is
pseudo-coherent. -/
abbrev IsPseudoCoherent (ℱ : ModX) : Prop :=
  ModuleDerived.IsPseudoCoherent
    ((DerivedCategory.singleFunctor ModX (0 : ℤ)).obj ℱ)

end SheafOfModules
