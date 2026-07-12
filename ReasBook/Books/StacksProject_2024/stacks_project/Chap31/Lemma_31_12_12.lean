import Mathlib
import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Remark_31_12_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `ObjectProperty.FullSubcategory` and
-- `ObjectProperty.lift` as the canonical full-subcategory API for restricted functors. Local
-- Chapter 31 precedent fixes the category of coherent reflexive sheaves as `ReflexiveCoh`, and
-- Chapter 30 fixes the scheme-depth hypothesis via `moduleDepth` on stalks.

variable (Y : Scheme.{u}) [MonoidalCategory Y.Modules] [BraidedCategory Y.Modules]
  [MonoidalClosed Y.Modules]

/-- Forget coherent reflexive modules to all `\mathcal O_Y`-modules. -/
private abbrev reflexiveCohForgetToModules : ReflexiveCoh Y ⥤ Y.Modules :=
  reflexiveCohInclusion Y ⋙ (SheafOfModules.isCoherent Y.toRingedSpace).ι

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (U : X.Opens)
variable [MonoidalCategory (U : Scheme).Modules]
variable [BraidedCategory (U : Scheme).Modules]
variable [MonoidalClosed (U : Scheme).Modules]

/-- The restriction of the canonical open pullback `j^*` to coherent reflexive modules, assuming
the needed coherence and reflexivity preservation facts. -/
@[stacks 0EBJ]
abbrev coherentReflexiveOpenPullbackFunctor
    (hcoh : ∀ ℱ : ReflexiveCoh X,
      ((Scheme.Modules.pullback U.ι).obj ((reflexiveCohForgetToModules X).obj ℱ)).IsCoherent)
    (href : ∀ ℱ : ReflexiveCoh X,
      IsReflexive
        ((Scheme.Modules.pullback U.ι).obj ((reflexiveCohForgetToModules X).obj ℱ))) :
    ReflexiveCoh X ⥤ ReflexiveCoh (U : Scheme) :=
  ObjectProperty.lift (reflexiveCohProperty (U : Scheme))
    (ObjectProperty.lift (SheafOfModules.isCoherent (U : Scheme).toRingedSpace)
      (reflexiveCohForgetToModules X ⋙ Scheme.Modules.pullback U.ι) hcoh)
    href

/-- The restriction of the canonical open pushforward `j_*` to coherent reflexive modules,
assuming the needed coherence and reflexivity preservation facts. -/
@[stacks 0EBJ]
abbrev coherentReflexiveOpenPushforwardFunctor
    (hcoh : ∀ 𝒢 : ReflexiveCoh (U : Scheme),
      ((Scheme.Modules.pushforward U.ι).obj
        ((reflexiveCohForgetToModules (U : Scheme)).obj 𝒢)).IsCoherent)
    (href : ∀ 𝒢 : ReflexiveCoh (U : Scheme),
      IsReflexive
        ((Scheme.Modules.pushforward U.ι).obj
          ((reflexiveCohForgetToModules (U : Scheme)).obj 𝒢))) :
    ReflexiveCoh (U : Scheme) ⥤ ReflexiveCoh X :=
  ObjectProperty.lift (reflexiveCohProperty X)
    (ObjectProperty.lift (SheafOfModules.isCoherent X.toRingedSpace)
      (reflexiveCohForgetToModules (U : Scheme) ⋙ Scheme.Modules.pushforward U.ι) hcoh)
    href

/-- Lemma 31.12.12: let `X` be an integral locally Noetherian scheme, let `j : U ⟶ X` be an
open subscheme with complement `Z`, and assume `depth(\mathcal O_{X,z}) ≥ 2` for all
`z ∈ Z`. Then `j^*` and `j_*` define an equivalence between coherent reflexive
`\mathcal O_X`-modules and coherent reflexive `\mathcal O_U`-modules. -/
@[stacks 0EBJ]
theorem coherentReflexiveOpenRestrictionPushforward_equivalence
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    ∃ (hPullCoh : ∀ ℱ : ReflexiveCoh X,
        ((Scheme.Modules.pullback U.ι).obj
          ((reflexiveCohForgetToModules X).obj ℱ)).IsCoherent),
      ∃ (hPullReflexive : ∀ ℱ : ReflexiveCoh X,
        IsReflexive
          ((Scheme.Modules.pullback U.ι).obj ((reflexiveCohForgetToModules X).obj ℱ))),
      ∃ (hPushCoh : ∀ 𝒢 : ReflexiveCoh (U : Scheme),
        ((Scheme.Modules.pushforward U.ι).obj
          ((reflexiveCohForgetToModules (U : Scheme)).obj 𝒢)).IsCoherent),
      ∃ (hPushReflexive : ∀ 𝒢 : ReflexiveCoh (U : Scheme),
        IsReflexive
          ((Scheme.Modules.pushforward U.ι).obj
            ((reflexiveCohForgetToModules (U : Scheme)).obj 𝒢))),
      ∃ e : ReflexiveCoh X ≌ ReflexiveCoh (U : Scheme),
        e.functor = coherentReflexiveOpenPullbackFunctor U hPullCoh hPullReflexive ∧
          e.inverse = coherentReflexiveOpenPushforwardFunctor U hPushCoh hPushReflexive := sorry

end AlgebraicGeometry.Scheme.Modules
