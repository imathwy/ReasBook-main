import Mathlib
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [∀ U : Opens X.carrier, MonoidalCategory (openSubspaceModuleCategory X U)]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- Extension by zero from an open subspace back to the ambient ringed space, viewed at the module
level. -/
abbrev moduleExtensionByZeroFromOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ (RingedSpace.Modules X) :=
  moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)

-- Proof sketch: restriction to an open subspace is pullback of module sheaves along the open
-- immersion, hence it preserves the additive structure.
/-- Restriction of `\mathcal O_X`-modules to an open subspace is additive. -/
theorem moduleRestrictionToOpen_additive_forInvertible
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive := sorry

-- Proof sketch: restriction to an open subspace is exact on the underlying abelian sheaves, so it
-- preserves finite limits and finite colimits on module sheaves as well.
/-- Restriction of `\mathcal O_X`-modules to an open subspace is exact. -/
theorem moduleRestrictionToOpen_exact_forInvertible
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := sorry

/-- The derived restriction functor induced by exact restriction to an open subspace. -/
abbrev moduleRestrictionToOpenDerivedForInvertible
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (openSubspaceModuleCategory X U) :=
  let _ : (moduleRestrictionToOpen X U).Additive :=
    moduleRestrictionToOpen_additive_forInvertible X U
  let _ : PreservesFiniteLimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact_forInvertible X U)).1
  let _ : PreservesFiniteColimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact_forInvertible X U)).2
  (moduleRestrictionToOpen X U).mapDerivedCategory

/-- A source-facing encoding of the factor decomposition in Lemma `20.52.2`: the structure sheaf
is decomposed by a locally finite family of pairwise disjoint open factors `U_n`, each `U_n`
carries an invertible module `\mathcal H^n`, and `M` is represented by the zero-differential
complex whose term in degree `n` is the extension by zero of `\mathcal H^n` from `U_n`. -/
def HasInvertibleSheafFactorDecomposition (M : DMod) : Prop :=
  ∃ (U : ℤ → Opens X.carrier) (ℋ : ∀ n : ℤ, openSubspaceModuleCategory X (U n)),
    LocallyFinite (fun n : ℤ ↦ (U n : Set X.carrier)) ∧
      iSup U = ⊤ ∧
        (∀ m n : ℤ, m ≠ n → Disjoint (↑(U m) : Set X.carrier) (↑(U n) : Set X.carrier)) ∧
          (∀ n : ℤ, Functor.IsEquivalence (tensorLeft (ℋ n))) ∧
            ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
              (∀ n : ℤ, K.X n = (moduleExtensionByZeroFromOpen X (U n)).obj (ℋ n)) ∧
                (∀ n : ℤ, K.d n (n + 1) = 0) ∧
                  Nonempty (M ≅ DerivedCategory.Q.obj K)

/-- A source-facing encoding of the local normal form in Lemma `20.52.2`: after restricting to an
open cover, `M` becomes a single shift of an invertible module sheaf. -/
def LocallyIsomorphicToShiftedInvertibleModule (M : DMod) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ (n : ℤ) (ℒ : openSubspaceModuleCategory X (U i)),
        Functor.IsEquivalence (tensorLeft ℒ) ∧
          Nonempty
            (((moduleRestrictionToOpenDerivedForInvertible X (U i)).obj M) ≅
              ((DerivedCategory.singleFunctor (openSubspaceModuleCategory X (U i))
                (0 : ℤ)).obj ℒ)⟦(-n : ℤ)⟧)

-- Proof sketch: for `(1) → (2)`, the inverse object and Lemmas `20.50.8`, `20.52.1`, and
-- `15.127.4` identify the global-sections model of `M` with a locally finite family of shifted
-- invertible pieces, which are then sheafified back to `X`. For `(2) → (1)`, one checks locally
-- that the derived dual evaluates to the unit on each disjoint factor and then combines the
-- factors using the locally finite decomposition.
/-- Lemma 20.52.2: an object `M` of `D(\mathcal O_X)` is invertible if and only if the structure
sheaf admits a locally finite factor decomposition by pairwise disjoint open pieces on which `M`
is represented by invertible modules concentrated in the corresponding degrees. -/
theorem isInvertibleDerivedObject_iff_hasInvertibleSheafFactorDecomposition
    (M : DMod) :
    Functor.IsEquivalence (tensorLeft M) ↔ HasInvertibleSheafFactorDecomposition M := sorry

-- Proof sketch: an invertible object has a dual by definition. Lemma `20.50.8` says any object of
-- `D(\mathcal O_X)` with a left dual is perfect.
/-- An invertible object of `D(\mathcal O_X)` is perfect. -/
theorem isPerfect_of_isInvertibleDerivedObject
    {M : DMod} (hM : Functor.IsEquivalence (tensorLeft M)) :
    DerivedCategory.IsPerfect M := sorry

-- Proof sketch: if all stalk rings are local, an invertible module sheaf is locally free of rank
-- `1`, so the factor decomposition of the previous theorem can be refined to the stated open-cover
-- normal form. Conversely, the local normal form immediately yields a local inverse, which glues
-- because invertibility can be checked on an open cover.
/-- On a ringed space with local stalk rings, invertibility in `D(\mathcal O_X)` is equivalent to
being locally a single shift of an invertible module sheaf. -/
theorem isInvertibleDerivedObject_iff_locallyIsomorphicToShiftedInvertibleModule_of_stalk_isLocalRing
    (M : DMod) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    Functor.IsEquivalence (tensorLeft M) ↔
      LocallyIsomorphicToShiftedInvertibleModule M := sorry

end AlgebraicGeometry.RingedSpace
