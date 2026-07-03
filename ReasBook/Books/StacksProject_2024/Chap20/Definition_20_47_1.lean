import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Definition_20_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- 
Domain-style sampling for Definition 20.47.1:
- primary domain: pseudo-coherence for derived `\mathcal O_X`-modules via local strictly perfect
  approximations after restriction to open subspaces and representative complexes in the derived
  category;
- inspected owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `CochainComplex.IsStrictlyPerfect`,
  `RingedSpace.IsMPseudoCoherent`,
  `DerivedCategory.Q.objPreimage`;
- best owner abstraction: the intrinsic derived owner family `IsMPseudoCoherent` from Lemma
  `20.47.9`, with derived pseudo-coherence owned intrinsically by the universal condition
  `∀ m, IsMPseudoCoherent E m`, and the canonical quotient functor owner `DerivedCategory.Q`;
  this file should keep the source-facing complex predicates while relegating representative-based
  derived criteria to bridge theorems rather than second owner definitions;
- primitive data: an open cover, local strictly perfect complexes, and comparison maps whose
  induced maps on homology are isomorphisms above degree `m` and epimorphisms in degree `m`, plus
  a representative complex of the derived object;
- derived API: the source-facing complex predicates, the intrinsic derived owners
  `IsMPseudoCoherent` and `IsPseudoCoherent`, the open-cover bridge theorem for
  `IsMPseudoCoherent`, and the representative bridge theorems relating the complex and derived
  notions.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`;
- `core/canonical`: `TopologicalSpace.IsOpenCover`, `RingedSpace.IsMPseudoCoherent`,
  `RingedSpace.IsPseudoCoherent`, and `DerivedCategory.Q`;
- `bridge/view`: `isMPseudoCoherent_iff_exists_openCover`,
  `isMPseudoCoherent_iff_exists_mPseudoCoherent_representative`, and
  `isPseudoCoherent_iff_exists_pseudoCoherent_representative`.
-/
namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The category of `\mathcal O_X`-modules on a ringed space carries its standard derived
category. -/
instance sheafModules_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

local notation "DModX" => ModuleDerived X
local notation "OpenComplex" U => CochainComplex (OpenSubsetSheafModules X U) ℤ

/-- Definition 20.47.1: a complex of `\mathcal O_X`-modules is `m`-pseudo-coherent if there is
an open covering of `X` such that on each member of the cover its restriction admits a morphism
from a strictly perfect complex inducing isomorphisms on cohomology in degrees `> m` and an
epimorphism in degree `m`. -/
def CochainComplex.IsMPseudoCoherent (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ α : Ei ⟶
            (((moduleSheafRestrictionToOpen (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E),
          CochainComplex.IsStrictlyPerfect Ei ∧
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α m)

-- Proof sketch: unfold `CochainComplex.IsMPseudoCoherent`; the statement is exactly the local
-- strictly-perfect approximation condition from the definition, expressed using restriction of
-- complexes to opens and the induced maps on homology.
/-- Unfolding `IsMPseudoCoherent` gives the local strictly-perfect approximation criterion on an
open covering. -/
theorem cochainComplex_isMPseudoCoherent_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) :
    CochainComplex.IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : Ei ⟶
                (((moduleSheafRestrictionToOpen (U i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E),
              CochainComplex.IsStrictlyPerfect Ei ∧
                (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                  Epi (HomologicalComplex.homologyMap α m) :=
  Iff.rfl

/-- A complex of `\mathcal O_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def CochainComplex.IsPseudoCoherent (E : CochainComplex (RingedSpace.Modules X) ℤ) : Prop :=
  ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m

-- Proof sketch: unfold `CochainComplex.IsPseudoCoherent`; it is definitionally the universal
-- quantification of `m`-pseudo-coherence over all integers.
/-- A complex is pseudo-coherent exactly when it is `m`-pseudo-coherent for all integers. -/
theorem cochainComplex_isPseudoCoherent_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) :
    CochainComplex.IsPseudoCoherent E ↔
      ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m :=
  Iff.rfl

/- Definition 20.47.1 (derived `m`-version): the intrinsic owner is the existing ringed-space
predicate `IsMPseudoCoherent`. -/
recall IsMPseudoCoherent

-- Proof sketch: convert between the pointwise neighborhoodwise approximation data from
-- `IsMPseudoCoherent` and a family indexed by an open cover, using `TopologicalSpace.IsOpenCover`
-- as the canonical cover owner.
/-- The owner predicate `IsMPseudoCoherent` is equivalently the existence of a strict-perfect
open-cover approximation of the restricted derived object. -/
theorem isMPseudoCoherent_iff_exists_openCover
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : DerivedCategory.Q.obj Ei ⟶ (moduleDerivedRestrictionToOpen (U i)).obj E,
              CochainComplex.IsStrictlyPerfect Ei ∧
                (∀ j : ℤ, m < j →
                  IsIso
                    ((DerivedCategory.homologyFunctor (OpenSubsetSheafModules X (U i)) j).map
                      α)) ∧
                  Epi
                    ((DerivedCategory.homologyFunctor (OpenSubsetSheafModules X (U i)) m).map
                      α) := by
  sorry

/-- Definition 20.47.1 (derived `m`-version): an object of `D(\mathcal O_X)` is
`m`-pseudo-coherent exactly when it is represented by an `m`-pseudo-coherent complex. This keeps
the source-facing representative criterion visible while using the intrinsic owner
`IsMPseudoCoherent` as the canonical core notion. -/
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅
            (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX).obj K,
          CochainComplex.IsMPseudoCoherent K m := by
  sorry

/-- Definition 20.47.1 (derived version): an object of `D(\mathcal O_X)` is pseudo-coherent if
it is `m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (E : DModX) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

-- Proof sketch: unfold `IsPseudoCoherent`; it is definitionally the universal quantification of
-- `m`-pseudo-coherence over all integers.
/-- A derived `\mathcal O_X`-module is pseudo-coherent exactly when it is `m`-pseudo-coherent for
all integers. -/
theorem isPseudoCoherent_iff
    (E : DModX) :
    IsPseudoCoherent E ↔ ∀ m : ℤ, IsMPseudoCoherent E m :=
  Iff.rfl

/-- A derived `\mathcal O_X`-module is pseudo-coherent exactly when it has a pseudo-coherent
representative complex. This is the companion bridge from the intrinsic owner to the source-facing
representative criterion. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (E : DModX) :
    IsPseudoCoherent E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsPseudoCoherent K := by
  sorry

end AlgebraicGeometry.RingedSpace
