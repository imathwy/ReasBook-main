import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap18.Definition_18_17_1
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- The pullback of the structure sheaf of `X` to the open subspace cut out by `U`. -/
abbrev openSubspaceRingCatSheaf (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)

/-- An `\mathcal O_U`-module is finite free if it is isomorphic to a finite free module sheaf on
the open subspace `U`. -/
def IsFiniteFreeOnOpenSubspace {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) : Prop :=
  ∃ I : Type u, Finite I ∧
    Nonempty (ℱ ≅ (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U))

-- Proof sketch: unfold `IsFiniteFreeOnOpenSubspace`.
/-- Unfolding `IsFiniteFreeOnOpenSubspace` gives the existence of a finite basis for the module
sheaf on the open subspace. -/
theorem isFiniteFreeOnOpenSubspace_iff {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) :
    IsFiniteFreeOnOpenSubspace ℱ ↔
      ∃ I : Type u, Finite I ∧
        Nonempty (ℱ ≅ (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U)) := sorry

/-- An `\mathcal O_U`-module is finite locally free if some open cover of `U` trivializes it by
finite free module sheaves. -/
def IsFiniteLocallyFreeOnOpenSubspace {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) : Prop :=
  ∃ (ι : Type u) (V : ι → Opens U),
    iSup V = ⊤ ∧
      ∀ i : ι, ∃ I : Type u, Finite I ∧
        Nonempty
          (ℱ.over (V i) ≅
            (SheafOfModules.free.{u} I :
              SheafOfModules ((openSubspaceRingCatSheaf X U).over (V i))))

-- Proof sketch: unfold `IsFiniteLocallyFreeOnOpenSubspace`.
/-- Unfolding `IsFiniteLocallyFreeOnOpenSubspace` gives a covering of the open subspace on which
the module becomes finite free. -/
theorem isFiniteLocallyFreeOnOpenSubspace_iff {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) :
    IsFiniteLocallyFreeOnOpenSubspace ℱ ↔
      ∃ (ι : Type u) (V : ι → Opens U),
        iSup V = ⊤ ∧
          ∀ i : ι, ∃ I : Type u, Finite I ∧
            Nonempty
              (ℱ.over (V i) ≅
                (SheafOfModules.free.{u} I :
                  SheafOfModules ((openSubspaceRingCatSheaf X U).over (V i)))) := sorry

namespace DerivedCategory

/-- An object of `D(\mathcal O_X)` admits a finite-locally-free representative on an open cover
if, after restricting to each member of some open cover, it is represented by a bounded complex
whose terms are finite locally free `\mathcal O`-modules on that open subspace. -/
def HasFiniteLocallyFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ _ : E ≅ DerivedCategory.Q.obj K,
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteLocallyFreeOnOpenSubspace (Ei.X j)

-- Proof sketch: unfold `HasFiniteLocallyFreeRepresentativeOnOpenCover`.
/-- Unfolding `HasFiniteLocallyFreeRepresentativeOnOpenCover` gives the open-cover criterion by
bounded complexes of finite locally free modules. -/
theorem hasFiniteLocallyFreeRepresentativeOnOpenCover_iff
    (E : DModX) :
    HasFiniteLocallyFreeRepresentativeOnOpenCover E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          ∃ (ι : Type u) (U : ι → Opens X.carrier),
            iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteLocallyFreeOnOpenSubspace (Ei.X j) := sorry

/-- An object of `D(\mathcal O_X)` admits a finite-free representative on an open cover if,
after restricting to each member of some open cover, it is represented by a bounded complex whose
terms are finite free `\mathcal O`-modules on that open subspace. -/
def HasFiniteFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ _ : E ≅ DerivedCategory.Q.obj K,
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteFreeOnOpenSubspace (Ei.X j)

-- Proof sketch: unfold `HasFiniteFreeRepresentativeOnOpenCover`.
/-- Unfolding `HasFiniteFreeRepresentativeOnOpenCover` gives the open-cover criterion by bounded
complexes of finite free modules. -/
theorem hasFiniteFreeRepresentativeOnOpenCover_iff
    (E : DModX) :
    HasFiniteFreeRepresentativeOnOpenCover E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          ∃ (ι : Type u) (U : ι → Opens X.carrier),
            iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteFreeOnOpenSubspace (Ei.X j) := sorry

-- Proof sketch: `(1) → (2)` uses Lemma `20.49.2` to choose a perfect representative and then
-- applies Lemma `17.14.6` termwise on the open subspaces, using the local-ring hypothesis on
-- stalks. `(2) → (3)` refines the cover so that each finite locally free term becomes finite free
-- on smaller opens. `(3) → (1)` applies Lemma `20.49.2` again, since a bounded complex of finite
-- free modules is in particular strictly perfect on each member of the chosen cover.
/-- Lemma 20.49.3: for an object `E` of `D(\mathcal O_X)` on a ringed space whose stalk rings are
local, the following are equivalent: `E` is perfect, `E` is locally represented by bounded
complexes of finite locally free modules, and `E` is locally represented by bounded complexes of
finite free modules. -/
theorem perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    ([ IsPerfect E
      , HasFiniteLocallyFreeRepresentativeOnOpenCover E
      , HasFiniteFreeRepresentativeOnOpenCover E
      ] : List Prop).TFAE := sorry

end DerivedCategory
end AlgebraicGeometry.RingedSpace
