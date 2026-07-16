import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap04.Lemma_4_33_14
import StacksProject_2024.stacks_project.Chap08.Lemma_8_10_3
import StacksProject_2024.stacks_project.Chap21.Example_21_39_1_Category_over_point
import StacksProject_2024.stacks_project.Chap21.Example_21_39_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_40_1
import StacksProject_2024.stacks_project.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FibredCategoryMor
open Opposite
open Functor.Fiber
open scoped CategoryTheory.CategoryHomology

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {D : RingedSite.{u, v}} {C C' : FibredCategoryOver D}
variable (u : C' ⟶ C)

local notation "JC'" => FibredCategoryOver.inheritedTopology D.siteTopology C'
local notation "JC" => FibredCategoryOver.inheritedTopology D.siteTopology C

/-
Domain-style sampling for Lemma 21.40.3:
- primary domain: fiberwise category homology for the comparison indexing categories attached to a
  morphism of fibred categories in Situation `21.38.3`;
- sampled owner declarations:
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.adjointFactorizationToTarget`,
  `fiberRestrictionPresheaf`,
  `fiberCategoryHomologyPresheaf`,
  `fiberCategoryHomologySheaf`,
  `Functor.leftDerived`;
- best owner abstraction: the comparison categories `𝓘_U` should be assembled into the
  fibred category over `C.S` whose projection is the canonical target functor in the adjoint
  factorization of `u`; the source-facing fibers and restricted presheaves should then feed the
  chapter owners `fiberCategoryHomologyPresheaf` and `fiberCategoryHomologySheaf`;
- primitive data: the comparison fibred category over `C.S`, the source projection from the
  adjoint factorization, and the source sheaf `ℱ'`;
- derived API: the fibers `𝓘_U`, the restricted presheaf `𝓕'_U`, and the
  source-facing homology presheaf and sheaf built from the Chapter `21.40.1` owners.

Source/core/bridge triage:
- `source-facing`: the comparison-index fibred category over `C.S`, its fibers
  `comparisonIndexCategory u U`, the restricted presheaves `comparisonIndexRestrictionPresheaf`,
  and the final derived lower-shriek theorem;
- `core/canonical`: `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.adjointFactorizationToTarget`,
  `fiberCategoryHomologyPresheaf`, `fiberCategoryHomologySheaf`, and `Functor.leftDerived`;
- `bridge/view`: the structured-arrow description of the fiber of
  `adjointFactorizationToTarget u` over `U`. -/

/-- The comparison-index categories of Lemma `21.40.3`, organized as a fibred category over the
target total category `𝒞`. The fiber over `U : C.S` is the comparison indexing category `𝓘_U`. -/
abbrev comparisonIndexFibredCategory (u : C' ⟶ C) :
    FibredCategoryOver C.S :=
  let p := toFunctor (adjointFactorizationToTarget u)
  letI : p.IsFibered := adjointFactorizationToTarget_isFibered u
  FibredCategoryOver.ofFunctor p

/-- The underlying presheaf on the comparison fibred category obtained by pulling `𝓕'`
back along the source projection in the adjoint factorization of `u`. -/
abbrev comparisonIndexSourcePresheaf
    (ℱ' : Sheaf JC' AddCommGrpCat) :
    (comparisonIndexFibredCategory u).Sᵒᵖ ⥤ AddCommGrpCat :=
  (toFunctor (adjointFactorizationToSource u)).op ⋙ ℱ'.1

/-- The indexing category `𝓘_U` of pairs `(U', φ)` with
`φ : U ⟶ u(U')`, realized canonically as the fiber over `U` of the comparison fibred
category. Lemma `4.33.14` identifies this fiber with the corresponding structured-arrow model. -/
abbrev comparisonIndexCategory (u : C' ⟶ C) (U : C.S) :=
  (comparisonIndexFibredCategory u).p.Fiber U

/-- The presheaf `𝓕'_U` on `𝓘_U`, obtained by restricting the pulled-back source
presheaf to the comparison fiber over `U`. -/
abbrev comparisonIndexRestrictionPresheaf
    (ℱ' : Sheaf JC' AddCommGrpCat) (U : C.S) :
    (comparisonIndexCategory u U)ᵒᵖ ⥤ AddCommGrpCat :=
  fiberRestrictionPresheaf (comparisonIndexFibredCategory u)
    (comparisonIndexSourcePresheaf u ℱ') U

variable [∀ U : C.S,
  HasProjectiveResolutions ((comparisonIndexCategory u U)ᵒᵖ ⥤ AddCommGrpCat)]
variable [∀ ⦃U V : C.S⦄ (f : V ⟶ U),
  ((comparisonIndexFibredCategory u).fiberPullbackPrecomp f).PreservesProjectiveObjects]

/-- The category homology `H_n(𝓘_U, 𝓕'_U)` attached to the comparison index
category over `U`. This is a thin source-facing bridge to the chapter owner `categoryHomology`.
-/
abbrev comparisonIndexHomology
    (ℱ' : Sheaf JC' AddCommGrpCat) (U : C.S) (n : ℕ) :
    AddCommGrpCat :=
  let _ :
      HasColimitsOfShape (comparisonIndexCategory u U)ᵒᵖ AddCommGrpCat := by
    infer_instance
  H_[n](comparisonIndexCategory u U, comparisonIndexRestrictionPresheaf u ℱ' U)

variable [HasWeakSheafify JC AddCommGrpCat]
variable [Functor.IsRightAdjoint
  ((toFunctor u).sheafPushforwardContinuous AddCommGrpCat JC' JC)]
variable [hLowerShriekAdditive :
  (Functor.leftAdjoint
    ((toFunctor u).sheafPushforwardContinuous AddCommGrpCat JC' JC)).Additive]
variable [Abelian (Sheaf JC' AddCommGrpCat)]
variable [Abelian (Sheaf JC AddCommGrpCat)]
variable [hSourceProjective : HasProjectiveResolutions (Sheaf JC' AddCommGrpCat)]
variable {ℱ' : Sheaf JC' AddCommGrpCat}

/-- The presheaf on `𝒞` sending `U` to `H_n(𝓘_U, 𝓕'_U)`. -/
def comparisonIndexHomologyPresheaf
    (ℱ' : Sheaf JC' AddCommGrpCat) (n : ℕ) :
    C.Sᵒᵖ ⥤ AddCommGrpCat :=
  fiberCategoryHomologyPresheaf (comparisonIndexFibredCategory u)
    (comparisonIndexSourcePresheaf u ℱ') n

/-- The sheaf associated to the source-facing presheaf `U ↦ H_n(𝓘_U, 𝓕'_U)`. -/
def comparisonIndexHomologySheaf
    (ℱ' : Sheaf JC' AddCommGrpCat) (n : ℕ) :
    Sheaf JC AddCommGrpCat :=
  fiberCategoryHomologySheaf JC (comparisonIndexFibredCategory u)
    (comparisonIndexSourcePresheaf u ℱ') n

-- Proof sketch: factor the comparison functor `u` through the fibred category `𝒞''`
-- of Categories, Lemma `4.33.14`, where the first stage has exact lower shriek and the second
-- stage is covered by Lemma `21.40.2`. The construction of `𝒞''` identifies each fiber `𝒞''_U`
-- with `𝓘_U`, and the restricted sheaf with `𝓕'_U`. The proof also supplies the restriction
-- maps on the objectwise rule `U ↦ H_n(𝓘_U, 𝓕'_U)`, producing the presheaf whose sheafification
-- computes `L_n g_!(𝓕')`.
/- Lemma 21.40.3: in Situation `21.38.3`, for an abelian sheaf `𝓕'` on `𝒞'` and `n ≥ 0`, the
`n`-th left derived lower shriek `L_n g_!(𝓕')` is canonically isomorphic to the source-facing
sheaf `comparisonIndexHomologySheaf u ℱ' n` attached to the presheaf sending `U` to
`H_n(𝓘_U, 𝓕'_U)`, where `𝓘_U` is the comparison indexing category and `𝓕'_U` is the induced
presheaf on `𝓘_U`. -/
@[stacks 08PK]
def abelian_lower_shriek_left_derived_isomorphic_comparison_index_homology_sheaf
    [(Functor.leftAdjoint
      ((toFunctor u).sheafPushforwardContinuous AddCommGrpCat JC' JC)).Additive]
    [HasProjectiveResolutions (Sheaf JC' AddCommGrpCat)]
    (ℱ' : Sheaf JC' AddCommGrpCat) (n : ℕ) :
    IsIsomorphic
      (((Functor.leftAdjoint
          ((toFunctor u).sheafPushforwardContinuous AddCommGrpCat JC' JC)).leftDerived n).obj ℱ')
      (comparisonIndexHomologySheaf u ℱ' n) := by
  exact ⟨by
    sorry⟩

end

end FibredCategoryOver
end CategoryTheory
