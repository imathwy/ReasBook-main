import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.stacks_project.Chap17.TensorPowerSheaf
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme} [MonoidalCategory X.Modules]

/- Semantic recall: `lean_leansearch` pointed to the scheme affine-open and basic-open owners.
The intended local owner is `Scheme.Modules.IsAmple` from Definition 28.26.1, but importing that
file currently forces Lake to rebuild upstream Chapter 17 files that fail before this item
elaborates.  The theorem below therefore expands that owner: tensor powers are
`RingedSpace.tensorPowerSheaf`, and `X_s` is represented by the explicit stalkwise nonvanishing
set used by the Chapter 17 nonvanishing-open API. The current stalk-module helper is universe
monomorphic, so this item is stated in mathlib's default scheme universe. -/

/-- The monoidal structure on scheme modules, viewed as the corresponding monoidal structure on
modules over the underlying ringed space. -/
local instance instMonoidalCategoryRingedSpaceModules :
    MonoidalCategory (SheafOfModules X.toRingedSpace.ringCatSheaf) :=
  inferInstanceAs (MonoidalCategory X.Modules)

/-- The underlying set of the nonvanishing locus of a global section of a positive tensor power.
This is the explicit stalkwise formula used when the packaged Chapter 28 nonvanishing-open owner
is unavailable in item-file checking. -/
def tensorPowerSectionNonvanishingSet
    (L : X.Modules) (n : ℕ)
    (s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤)) :
    Set X :=
  {x | ((TopCat.Presheaf.Γgerm
      (RingedSpace.tensorPowerSheaf L n).val.presheaf x).hom s) ∉
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat
              (RingedSpace.tensorPowerSheaf L n) x)))}

/-- Membership in the explicit tensor-power nonvanishing set is the stalkwise nonvanishing
condition. -/
theorem mem_tensorPowerSectionNonvanishingSet
    {L : X.Modules} {n : ℕ}
    {s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤)} {x : X} :
    x ∈ tensorPowerSectionNonvanishingSet L n s ↔
      ((TopCat.Presheaf.Γgerm
        (RingedSpace.tensorPowerSheaf L n).val.presheaf x).hom s) ∉
          ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (RingedSpace.stalkModuleCat
                (RingedSpace.tensorPowerSheaf L n) x))) := sorry

/-- A positive tensor-power section cuts out an affine nonvanishing open containing a point. -/
structure TensorPowerSectionAffineNonvanishingAt
    (L : X.Modules) (n : ℕ+)
    (s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤)) (U : X.Opens) (x : X) :
    Prop where
  nonvanishing_eq : (U : Set X) = tensorPowerSectionNonvanishingSet L n s
  mem_open : x ∈ (U : Set X)
  isAffineOpen : IsAffineOpen U

/-- A positive tensor-power section cuts out an affine nonvanishing open between a finite set and
an ambient open. -/
structure TensorPowerSectionAffineNonvanishingOpenBetween
    (L : X.Modules) (n : ℕ+)
    (s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤)) (U : X.Opens) (E : Set X) (W : X.Opens) :
    Prop where
  nonvanishing_eq : (U : Set X) = tensorPowerSectionNonvanishingSet L n s
  isAffineOpen : IsAffineOpen U
  subset_open : E ⊆ (U : Set X)
  le_open : U ≤ W

/-- Lemma 28.29.6: for an ample invertible sheaf `L` on a scheme `X`, every finite subset
`E` contained in an open `W` is contained in an affine nonvanishing open `X_s`, for a global
section `s` of a positive tensor power of `L`, and this nonvanishing open is itself contained
in `W`. -/
@[stacks 09NV]
theorem exists_positive_tensorPower_section_affine_nonvanishingOpen_between_finiteSet_and_open
    (L : X.Modules) [Functor.IsEquivalence (tensorRight L)]
    (hX_compact : IsCompact (Set.univ : Set X))
    (hL_ample : ∀ x : X, ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
        ∃ U : X.Opens, TensorPowerSectionAffineNonvanishingAt L n s U x)
    (E : Set X) (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
        ∃ U : X.Opens, TensorPowerSectionAffineNonvanishingOpenBetween L n s U E W := sorry

end AlgebraicGeometry.Scheme.Modules
