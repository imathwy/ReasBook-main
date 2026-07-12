import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap17.Definition_17_20_1
import StacksProject_2024.Chap20.Lemma_20_27_1
import StacksProject_2024.Chap20.Definition_20_47_1
import StacksProject_2024.Chap20.Definition_20_49_1
import StacksProject_2024.Chap20.Remark_20_42_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace
open scoped RingedSpace.Hom
open scoped RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u

/- Domain-style sampling for Lemma 20.51.3:
- primary domain: pullback comparison for derived internal Hom on ringed spaces, with source
  hypotheses expressed by perfectness, pseudo-coherence, local bounded-below-ness, flatness, and
  finite tor dimension;
- sampled owner declarations:
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`,
  `modulePullbackDerivedTensorIso`,
  `ModuleDerived.IsLocallyBoundedAbove`,
  `DerivedCategory.IsPerfect`,
  `ModuleDerived.IsPseudoCoherent`,
  `ModuleHasFiniteTorDimension`;
- best owner abstraction: the comparison morphism itself is already canonically owned by
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`; the source-facing input data
  for that owner is a chosen pullback-tensor comparison family as in Remark `20.42.13`, and the
  canonical Chapter 20 owner for such a family is `modulePullbackDerivedTensorIso` evaluated
  objectwise as `fun A B ↦ (modulePullbackDerivedTensorIso f B).app A`. The two auxiliary
  predicates below are still source-facing local owners here,
  since this chapter/project does not already provide upstream owners for morphismwise finite tor
  dimension or locally bounded-below derived objects on ringed spaces. The morphism-side
  tor-dimension predicate should nevertheless follow the Chapter 17 owner pattern `pointwise view +
  owner class`, just as `RingedSpace.Hom.IsFlat` does, while the bounded-below predicate should
  mirror the Chapter 20 owner `ModuleDerived.IsLocallyBoundedAbove` instead of introducing a
  packaging wrapper;
- primitive data: a morphism `f : X ⟶ Y`, the derived objects `K` and `M`, and the stalk/local
  boundedness hypotheses appearing in the three source statements;
- derived API: only the three isomorphism theorems below, together with the minimal source-facing
  helper predicates needed to state part `(3)`.

Source/core/bridge triage:
- `source-facing`: `RingedSpace.Hom.FiniteTorDimensionAt`,
  `RingedSpace.Hom.HasFiniteTorDimension`, and `ModuleDerived.IsLocallyBoundedBelow`;
- `core/canonical`: `ModuleHasFiniteTorDimension`, `DerivedCategory.IsPerfect`,
  `ModuleDerived.IsPseudoCoherent`, and
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`;
- `bridge/view`: none beyond the ringed-space specialization already provided by
  `Remark_20_42_13`. -/

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The morphism `f` has finite tor dimension at `x` when the local ring `𝒪_{X, x}` has finite
tor dimension as a module over `𝒪_{Y, f(x)}`. -/
abbrev FiniteTorDimensionAt (x : X) : Prop :=
  let _ : Algebra ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  ModuleHasFiniteTorDimension
    (ModuleCat.of ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x))

/-- A morphism of ringed spaces has finite tor dimension when it has finite tor dimension at every
point of the source. -/
@[mk_iff]
class HasFiniteTorDimension : Prop where
  finiteTorDimensionAt (x : X) : FiniteTorDimensionAt f x

end RingedSpace.Hom

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

open SheafOfModules.RingedSite

/-- A derived `𝒪_X`-module is locally bounded below when every point has an open neighborhood on
which its restriction lies in the bounded-below derived category. -/
def ModuleDerived.IsLocallyBoundedBelow (E : ModuleDerived X) : Prop :=
  ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U) (n : ℤ),
    ((moduleRestrictionToOpenDerived X U).obj E).IsGE n

/-- A derived `𝒪_X`-module is locally bounded below exactly when each point admits an open
neighborhood on which the restriction lies in some `D^{≥ n}`. -/
theorem ModuleDerived.isLocallyBoundedBelow_iff (E : ModuleDerived X) :
    E.IsLocallyBoundedBelow ↔
      ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U) (n : ℤ),
        ((moduleRestrictionToOpenDerived X U).obj E).IsGE n :=
  Iff.rfl

section

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

variable [CategoryWithHomology ModX]
variable [CategoryWithHomology ModY]
variable [∀ U : Opens Y.carrier, CategoryWithHomology (openSubspaceModuleCategory Y U)]

-- Proof sketch: this is the first case of the Stacks Project proof. Replace `K` locally by a
-- strictly perfect complex, compute derived internal Hom by the explicit internal-Hom complex,
-- pull everything back termwise, and identify the pulled-back internal-Hom complex with the
-- internal Hom of the pulled-back representatives.
/-- Lemma 20.51.3 (1): for a morphism of ringed spaces `f : X ⟶ Y`, if `K` is a perfect object of
`D(𝒪_Y)`, then the canonical comparison map
`Lf^* RHom(K, M) ⟶ RHom(Lf^* K, Lf^* M)` from Remark `20.42.13`, formed using a chosen
pullback-tensor comparison for `L(f)^*`, is an isomorphism. -/
@[stacks 0GM7]
instance pullbackDerivedInternalHomComparison_isIso_of_isPerfect
    [MonoidalCategory DModX] [BraidedCategory DModX] [MonoidalClosed DModX]
    [MonoidalCategory DModY] [BraidedCategory DModY] [MonoidalClosed DModY]
    (f : X ⟶ Y) [(f^*).Additive]
    (pullbackTensorIso :
      ∀ A B : DModY, (L(f)^*).obj (A ⊗ B) ≅ ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    (K M : DModY) (hK : DerivedCategory.IsPerfect K) :
    IsIso (pullbackDerivedInternalHomComparison (L(f)^*) pullbackTensorIso K M) := sorry

-- Proof sketch: use flatness of `f` to compute `Lf^*` by ordinary pullback, then truncate the
-- pseudo-coherent source `K` high enough relative to the lower bound on `M`. The truncated source
-- is locally strictly perfect, so part `(1)` applies and gives the comparison isomorphism on all
-- sufficiently low cohomology; varying the truncation yields an isomorphism everywhere.
/-- Lemma 20.51.3 (2): for a flat morphism of ringed spaces `f : X ⟶ Y`, if `K` is
pseudo-coherent and `M` is locally bounded below, then the canonical map
`Lf^* RHom(K, M) ⟶ RHom(Lf^* K, Lf^* M)` from Remark `20.42.13`, formed using a chosen
pullback-tensor comparison for `L(f)^*`, is an isomorphism. -/
@[stacks 0GM7]
instance pullbackDerivedInternalHomComparison_isIso_of_isFlat_of_isPseudoCoherent_of_locallyBoundedBelow
    [MonoidalCategory DModX] [BraidedCategory DModX] [MonoidalClosed DModX]
    [MonoidalCategory DModY] [BraidedCategory DModY] [MonoidalClosed DModY]
    (f : X ⟶ Y) [(f^*).Additive]
    (pullbackTensorIso :
      ∀ A B : DModY, (L(f)^*).obj (A ⊗ B) ≅ ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    [RingedSpace.Hom.IsFlat f] (K M : DModY)
    (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (pullbackDerivedInternalHomComparison (L(f)^*) pullbackTensorIso K M) := sorry

-- Proof sketch: argue as in part `(2)`, but replace flatness by the finite-tor-dimension bound on
-- the stalk maps of `f`, which gives bounded cohomological amplitude for `Lf^*` on bounded-below
-- objects. After truncating `K`, reduce again to the perfect case `(1)`.
/-- Lemma 20.51.3 (3): for a morphism of ringed spaces `f : X ⟶ Y`, if `𝒪_X` has finite tor
dimension over `f⁻¹𝒪_Y`, `K` is pseudo-coherent, and `M` is locally bounded below, then the
canonical map `Lf^* RHom(K, M) ⟶ RHom(Lf^* K, Lf^* M)` from Remark `20.42.13`, formed using a chosen
pullback-tensor comparison for `L(f)^*`, is an isomorphism. -/
@[stacks 0GM7]
instance pullbackDerivedInternalHomComparison_isIso_of_hasFiniteTorDimension_of_isPseudoCoherent_of_locallyBoundedBelow
    [MonoidalCategory DModX] [BraidedCategory DModX] [MonoidalClosed DModX]
    [MonoidalCategory DModY] [BraidedCategory DModY] [MonoidalClosed DModY]
    (f : X ⟶ Y) [(f^*).Additive]
    (pullbackTensorIso :
      ∀ A B : DModY, (L(f)^*).obj (A ⊗ B) ≅ ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    [RingedSpace.Hom.HasFiniteTorDimension f] (K M : DModY)
    (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (pullbackDerivedInternalHomComparison (L(f)^*) pullbackTensorIso K M) := sorry

end

end AlgebraicGeometry.RingedSpace
