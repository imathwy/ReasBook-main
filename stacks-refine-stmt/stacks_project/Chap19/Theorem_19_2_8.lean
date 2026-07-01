import Mathlib
import stacks_project.Chap12.Definition_12_27_5
import stacks_project.Chap19.Lemma_19_2_7
import stacks_project.Chap19.Proposition_19_2_5

open CategoryTheory
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct

universe u

section

variable (R : Type u) [Ring R]

/-- The successor structure on `ModuleCat R ⥤ ModuleCat R` determined by the one-step Baer
construction `M ↦ 𝐌(M)`. -/
private noncomputable abbrev baerModuleTransfiniteSuccStruct :
    SuccStruct (ModuleCat R ⥤ ModuleCat R) :=
  SuccStruct.ofNatTrans (baerModuleStepInclusionNatTrans R)

/-- The zeroth object of the transfinite Baer successor structure is the identity functor on
`ModuleCat R`. -/
@[simp]
private theorem baerModuleTransfiniteSuccStruct_X₀ :
    (baerModuleTransfiniteSuccStruct R).X₀ = 𝟭 (ModuleCat R) :=
  rfl

/-- The transfinite Baer functor `N ↦ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteFunctor (α : Ordinal.{u}) :
    ModuleCat R ⥤ ModuleCat R :=
  if hα : α = 0 then
    𝟭 (ModuleCat R)
  else
    letI := Ordinal.toTypeOrderBot hα
    (baerModuleTransfiniteSuccStruct R).iteration α.ToType

notation:max "𝐌_[" α "](" N ")" => Functor.obj (baerModuleTransfiniteFunctor _ α) N

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α = 0`, the defining `if` chooses the
-- identity functor branch.
/-- At ordinal `0`, the transfinite Baer functor is the identity functor on `ModuleCat R`. -/
private theorem baerModuleTransfiniteFunctor_eq_id (α : Ordinal.{u}) (hα : α = 0) :
    baerModuleTransfiniteFunctor R α = 𝟭 (ModuleCat R) := sorry

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α ≠ 0`, the defining `if` chooses the
-- branch given by the transfinite iteration of the one-step Baer successor structure over
-- `α.ToType`.
/-- For `α ≠ 0`, the transfinite Baer functor is the standard transfinite iteration of the
one-step Baer successor structure over `α.ToType`. -/
private theorem baerModuleTransfiniteFunctor_eq_iteration (α : Ordinal.{u}) (hα : α ≠ 0) :
    baerModuleTransfiniteFunctor R α =
      letI := Ordinal.toTypeOrderBot hα
      (baerModuleTransfiniteSuccStruct R).iteration α.ToType := sorry

/-- The canonical natural transformation `N ⟶ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteInclusion (α : Ordinal.{u}) :
    𝟭 (ModuleCat R) ⟶ baerModuleTransfiniteFunctor R α :=
  if hα : α = 0 then
    eqToHom (baerModuleTransfiniteFunctor_eq_id R α hα).symm
  else
    letI := Ordinal.toTypeOrderBot hα
    eqToHom (baerModuleTransfiniteSuccStruct_X₀ R).symm ≫
      (baerModuleTransfiniteSuccStruct R).ιIteration α.ToType ≫
        eqToHom (baerModuleTransfiniteFunctor_eq_iteration R α hα).symm

notation:max "ι_𝐌[" α "](" N ")" => NatTrans.app (baerModuleTransfiniteInclusion _ α) N

private noncomputable def baerModuleTransfiniteArrowFunctor (α : Ordinal.{u}) :
    ModuleCat R ⥤ Arrow (ModuleCat R) :=
  (baerModuleTransfiniteInclusion R α).arrowFunctor

-- Proof sketch: each successor map `\mathbf{M}_β(N) ⟶ \mathbf{M}_{β + 1}(N)` is injective by
-- Lemma `19.2.7 (2)`, and the transfinite stage `N ⟶ \mathbf{M}_α(N)` is obtained by composing
-- these injections and taking the canonical maps into limit-stage colimits.
/-- For every `R`-module `N`, the canonical map `N ⟶ \mathbf{M}_α(N)` is injective. -/
theorem baerModuleTransfiniteInclusion_app_injective
    (α : Ordinal.{u}) (N : ModuleCat R) :
    Function.Injective (ι_𝐌[α](N)).hom := sorry

-- Proof sketch: use Baer's criterion. Given an ideal map `I ⟶ \mathbf{M}_α(N)`, apply
-- Proposition `19.2.5` to the module `I` to factor it through some earlier stage
-- `\mathbf{M}_β(N)` with `β < α`, then use Lemma `19.2.7 (3)` to extend it across
-- `I ↪ R` into `\mathbf{M}_{β + 1}(N) ⟶ \mathbf{M}_α(N)`.
/-- If the cofinality of `α` is larger than the cardinality of the set of ideals of `R`, then
`\mathbf{M}_α(N)` is an injective `R`-module. -/
theorem baerModuleTransfiniteFunctor_obj_injective
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) (N : ModuleCat R) :
    Injective (𝐌_[α](N)) := sorry

/-- Theorem 19.2.8: if the cofinality of `α` is strictly larger than the cardinality of the set of
ideals of `R`, then the transfinite Baer construction `N ↦ \mathbf{M}_α(N)` together with the
canonical maps `N ⟶ \mathbf{M}_α(N)` yields functorial injective embeddings of `R`-modules. -/
@[reducible]
noncomputable def baerModule_hasFunctorialInjectiveEmbeddings
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) :
    HasFunctorialInjectiveEmbeddings (ModuleCat R) where
  J := baerModuleTransfiniteArrowFunctor R α
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj N := (ModuleCat.mono_iff_injective _).mpr
    (baerModuleTransfiniteInclusion_app_injective R α N)
  injective_obj N := baerModuleTransfiniteFunctor_obj_injective R α hα N

end
