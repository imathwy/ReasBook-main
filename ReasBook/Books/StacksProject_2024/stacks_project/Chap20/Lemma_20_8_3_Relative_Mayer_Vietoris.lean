import StacksProject_2024.Chap20.«20_2_0_4»
import StacksProject_2024.Chap20.Open_subspace_module_pushforward_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

/- Domain-style sampling for relative Mayer-Vietoris on ringed spaces:
- primary domain: direct image of `𝒪_X`-modules along a morphism of ringed spaces,
  together with the canonical open-restriction/direct-image terms and first higher direct image in
  the initial relative Mayer-Vietoris segment;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `moduleRestrictionToOpen`,
  `modulePushforwardFromOpen`,
  `modulePushforwardFromOpenAlong`,
  `modulePushforwardFromOpenRestrictionMap`,
  `RingedSpace.Hom.higherDirectImageModule`,
  `ComposableArrows.mk₄`;
- best owner abstraction:
  `source-facing`: the canonical initial relative Mayer-Vietoris exact segment on `f_*` with
    boundary in `R^1 f_*`;
  `core/canonical`: `RingedSpace.Modules`, `f _*`, `moduleRestrictionToOpen`,
    `modulePushforwardFromOpen`, `modulePushforwardFromOpenAlong`, and
    `RingedSpace.Hom.higherDirectImageModule`, concretely `R^{1}_[f](ℱ)`;
  `bridge/view`: `modulePushforwardFromOpenAlongUnitNatTrans`,
    `modulePushforwardFromOpenAlongRestrictionNatTrans`, and the local exact-segment package
    below.
- primitive-vs-derived split:
  primitive data are the morphism `f : X ⟶ Y`, the opens `U,V ⊆ X`, and the module
  `ℱ : X.Modules`;
  the Mayer-Vietoris middle/intersection terms and the exact-segment maps are derived API built
  from those owners. -/

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y

/-- The first two canonical maps in the relative Mayer-Vietoris segment compose to zero. -/
private theorem ringedSpaceModule_relativeMayerVietoris_comp_eq_zero
    (U V : Opens X) (ℱ : RingedSpace.Modules X) :
    ((biprod.lift
        (modulePushforwardFromOpenAlongUnitNatTrans f U)
        (modulePushforwardFromOpenAlongUnitNatTrans f V)).app ℱ) ≫
      ((biprod.desc
          (modulePushforwardFromOpenAlongRestrictionNatTrans f
            (inf_le_left : U ⊓ V ≤ U))
          (-(modulePushforwardFromOpenAlongRestrictionNatTrans f
            (inf_le_right : U ⊓ V ≤ V)))).app ℱ) = 0 := by
  sorry

/-- The canonical underived relative Mayer-Vietoris short complex on `Y`. -/
abbrev ringedSpaceModuleRelativeMayerVietorisShortComplex
    (U V : Opens X) (ℱ : ModX) :
    ShortComplex ModY :=
  ShortComplex.mk
    ((biprod.lift
        (modulePushforwardFromOpenAlongUnitNatTrans f U)
        (modulePushforwardFromOpenAlongUnitNatTrans f V)).app ℱ)
    ((biprod.desc
        (modulePushforwardFromOpenAlongRestrictionNatTrans f
          (inf_le_left : U ⊓ V ≤ U))
        (-(modulePushforwardFromOpenAlongRestrictionNatTrans f
          (inf_le_right : U ⊓ V ≤ V)))).app ℱ)
    (ringedSpaceModule_relativeMayerVietoris_comp_eq_zero f U V ℱ)

/-- The left map in the underived relative Mayer-Vietoris short complex is monic. -/
theorem ringedSpaceModuleRelativeMayerVietorisShortComplex_left_mono
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) :
    Mono ((ringedSpaceModuleRelativeMayerVietorisShortComplex f U V ℱ).f) := by
  sorry

-- Proof sketch: the underived Mayer-Vietoris row on `X`
-- `0 ⟶ ℱ ⟶ j_{U,*}(ℱ|_U) ⊞ j_{V,*}(ℱ|_V) ⟶ j_{U ∩ V,*}(ℱ|_{U ∩ V}) ⟶ 0`
-- is short exact for a two-open cover. Applying `f_*` gives the concrete row below on `Y`, so the
-- first nontrivial exactness window is already available before introducing the boundary map into
-- `R^1 f_*`.
/-- Companion to Lemma 20.8.3: for a cover `X = U ∪ V`, the canonical underived relative
Mayer-Vietoris row on `Y`
`f_* ℱ ⟶ a_*(ℱ|_U) ⊞ b_*(ℱ|_V) ⟶ c_*(ℱ|_{U ∩ V})`
is exact at the middle term. -/
theorem ringedSpaceModule_relativeMayerVietoris_middle_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : RingedSpace.Modules X) :
    (ringedSpaceModuleRelativeMayerVietorisShortComplex f U V ℱ).Exact := by
  sorry

end

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [hAdd : (f _*).Additive]
variable [hRes : HasInjectiveResolutions (RingedSpace.Modules X)]

local notation "ModY" => RingedSpace.Modules Y
local macro:max "R^{" i:term "}_[" g:term "](" F:term ")" : term =>
  `(@higherDirectImageModule X Y $g hAdd hRes $F $i)

/-- The relative Mayer-Vietoris four-term segment determined by a boundary morphism
`δ : c_*(ℱ|_{U ∩ V}) ⟶ R^{1}_[f](ℱ)`. -/
abbrev ringedSpaceModuleRelativeMayerVietorisSequence
    (U V : Opens X) (ℱ : RingedSpace.Modules X)
    (δ : (modulePushforwardFromOpenAlong f (U ⊓ V)).obj ℱ ⟶
      R^{1}_[f](ℱ)) :
    ComposableArrows ModY 3 :=
  ComposableArrows.mk₃
    ((biprod.lift
        (modulePushforwardFromOpenAlongUnitNatTrans f U)
        (modulePushforwardFromOpenAlongUnitNatTrans f V)).app ℱ)
    ((biprod.desc
        (modulePushforwardFromOpenAlongRestrictionNatTrans f
          (inf_le_left : U ⊓ V ≤ U))
        (-(modulePushforwardFromOpenAlongRestrictionNatTrans f
          (inf_le_right : U ⊓ V ≤ V)))).app ℱ)
    δ

-- Proof sketch: start from the derived relative Mayer-Vietoris triangle for `Rf_*`, apply the
-- degree-`0` cohomology functor, identify the first three displayed terms with the underived
-- pushforward/restriction row above, and use the standard comparison
-- `H^1(Rf_* ℱ) ≅ R^{1}_[f](ℱ)` to obtain the boundary morphism.
/-- Lemma 20.8.3 (Relative Mayer-Vietoris), exactness companion: if `f : X ⟶ Y` is a morphism of
ringed spaces and `X = U ∪ V`, then for every `𝒪_X`-module `ℱ` there exists a boundary morphism
`c_*(ℱ|_{U ∩ V}) ⟶ R^{1}_[f](ℱ)` such that the relative Mayer-Vietoris sequence
`f_* ℱ ⟶ a_*(ℱ|_U) ⊞ b_*(ℱ|_V) ⟶ c_*(ℱ|_{U ∩ V}) ⟶ R^{1}_[f](ℱ)`
is exact. -/
@[stacks 01EC]
theorem ringedSpaceModule_relativeMayerVietoris_sequence_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : RingedSpace.Modules X) :
    ∃ δ : (modulePushforwardFromOpenAlong f (U ⊓ V)).obj ℱ ⟶
        R^{1}_[f](ℱ),
      (ringedSpaceModuleRelativeMayerVietorisSequence f U V ℱ δ).Exact := by
  sorry

-- Proof sketch: combine the boundary-sequence exactness above with the already available monicity
-- of `f_* ℱ ⟶ a_*(ℱ|_U) ⊞ b_*(ℱ|_V)` for a two-open cover. This restores the source-facing initial
-- exact segment beginning at `0`.
/-- Lemma 20.8.3 (Relative Mayer-Vietoris): if `f : X ⟶ Y` is a morphism of ringed spaces and
`X = U ∪ V`, then for every `𝒪_X`-module `ℱ` there exists a boundary morphism
`c_*(ℱ|_{U ∩ V}) ⟶ R^{1}_[f](ℱ)` such that the initial relative Mayer-Vietoris segment
`0 ⟶ f_* ℱ ⟶ a_*(ℱ|_U) ⊞ b_*(ℱ|_V) ⟶ c_*(ℱ|_{U ∩ V}) ⟶ R^{1}_[f](ℱ)`
is exact. -/
@[stacks 01EC]
theorem ringedSpaceModule_relativeMayerVietoris_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : RingedSpace.Modules X) :
    ∃ δ : (modulePushforwardFromOpenAlong f (U ⊓ V)).obj ℱ ⟶
        R^{1}_[f](ℱ),
      Mono ((ringedSpaceModuleRelativeMayerVietorisShortComplex f U V ℱ).f) ∧
        (ringedSpaceModuleRelativeMayerVietorisSequence f U V ℱ δ).Exact := by
  sorry

end

end RingedSpace

end AlgebraicGeometry
