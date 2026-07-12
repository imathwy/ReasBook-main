import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap18.Lemma_18_27_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.27.5:
- primary domain: left exactness of internal Hom in the monoidal closed category of sheaves of
  modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `leftExactFunctor`,
  `functor_leftExact_iff_maps_shortExact_to_exact_mono`,
  `ihom`,
  `internalHom.flip.obj`,
  `ringedSiteModuleCategory_preservesLimitsOfShape_ihom`,
  `ringedSiteModuleCategory_preservesLimitsOfShape_internalHom_flip_obj`;
- best owner abstraction:
  `leftExactFunctor ModOJ ModOJ (ihom ℱ)` in the target variable and
  `leftExactFunctor ModOJ ModOJ (internalHom.flip.obj 𝒢)` in the source variable, where the
  source-variable owner uses the braided internal-Hom bridge from Lemma 18.27.4;
- primitive data:
  a fixed module in the remaining variable, together with the canonical limit-preservation owners
  from Lemma 18.27.4 and the braiding required by the source-variable owner;
- derived API:
  the mapped-short-complex exactness consequences for the source-facing `Exact ∧ Epi` and
  `Exact ∧ Mono` hypotheses.

Source/core/bridge triage:
- `source-facing`: the textbook exactness statements obtained by applying internal Hom to a short
  exact sequence of `𝒪`-modules;
- `core/canonical`: `leftExactFunctor` on `ihom ℱ` and `internalHom.flip.obj 𝒢`;
- `bridge/view`: `functor_leftExact_iff_maps_shortExact_to_exact_mono` and the local
  `PreservesZeroMorphisms` instances that allow the source-facing companions to use
  `ShortComplex.map` directly.

This file therefore treats left exactness of the two canonical internal-Hom owner functors as the
main API and keeps the `Exact ∧ Epi` / `Exact ∧ Mono` mapped-short-complex statements only as
thin companions. -/

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

/-- Helper for Lemma 18.27.5: the ambient category of modules over the ringed-site structure
sheaf, written in the underlying `SheafOfModules` owner so universe parameters stay fixed. -/
private abbrev ringedSiteModuleOwner
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules.{max u v, v, u, max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

local notation "ModOJ" => ringedSiteModuleOwner J 𝒪

/-- Helper for Lemma 18.27.5: the module category on a ringed site is abelian. -/
local instance ringedSiteModuleCategory_abelian :
    Abelian (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :=
  SheafOfModules.instAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

section Source

variable [BraidedCategory (ringedSiteModuleCategory J 𝒪)]

/-- Helper for Lemma 18.27.5: the opposite of the ringed-site module category is abelian. -/
local instance ringedSiteModuleCategory_op_abelian :
    Abelian (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))ᵒᵖ :=
  CategoryTheory.instAbelianOpposite
    (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))

-- Proof sketch: fix `𝒢` and regard `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` as the source-variable internal-Hom owner
-- `internalHom.flip.obj 𝒢`. Lemma 18.27.4 gives the relevant limit preservation, and Lemma
-- 12.7.2 packages that as the canonical owner predicate `leftExactFunctor`.
/-- Lemma 18.27.5 (1), owner form: for fixed `𝒢`, the source-variable internal-Hom functor
`ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is left exact. -/
@[stacks 0GMY]
theorem ringedSiteModuleInternalHom_leftExact_in_source
    (𝒢 : ModOJ) :
    leftExactFunctor ModOJᵒᵖ ModOJ ((MonoidalClosed.internalHom).flip.obj 𝒢) := by
  -- Route correction: instance search does not expose `PreservesFiniteLimits` for the alias
  -- `internalHom.flip.obj 𝒢` directly, so we first install the all-shapes preservation owner from
  -- Lemma 18.27.4 and then pass to finite limits.
  letI : PreservesLimits
      (((MonoidalClosed.internalHom).flip.obj 𝒢) : ModOJᵒᵖ ⥤ ModOJ) :=
    { preservesLimitsOfShape := fun {I} _ ↦ by
        exact ringedSiteModuleCategory_preservesLimitsOfShape_internalHom_flip_obj
          (I := I) (J := J) (𝒪 := 𝒪) 𝒢 }
  -- Proof comment: once the owner preserves all limits, left exactness is exactly the finite-limit
  -- part of that canonical owner property.
  simpa [leftExactFunctor_iff] using
    (PreservesLimits.preservesFiniteLimits
      (((MonoidalClosed.internalHom).flip.obj 𝒢) : ModOJᵒᵖ ⥤ ModOJ))

-- Proof sketch: once the source-variable owner is known to be left exact, Chapter 12 upgrades
-- that canonical owner property to additivity, and additive functors preserve zero morphisms.
local instance ringedSiteModuleInternalHom_source_preservesZeroMorphisms
    (𝒢 : ModOJ) :
    ((MonoidalClosed.internalHom).flip.obj 𝒢).PreservesZeroMorphisms := by
  -- Proof comment: Chapter 12 upgrades left exactness to additivity, and additive functors
  -- preserve zero morphisms.
  let hAb :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :=
    ringedSiteModuleCategory_abelian (J := J) (𝒪 := 𝒪)
  let hAbOp :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))ᵒᵖ :=
    ringedSiteModuleCategory_op_abelian (J := J) (𝒪 := 𝒪)
  letI : ((MonoidalClosed.internalHom).flip.obj 𝒢).Additive :=
    @CategoryTheory.functor_additive_of_leftExact_or_rightExact
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))ᵒᵖ
      _ hAbOp
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      ((MonoidalClosed.internalHom).flip.obj 𝒢)
      (.inl <| ringedSiteModuleInternalHom_leftExact_in_source (J := J) (𝒪 := 𝒪) 𝒢)
  exact Functor.preservesZeroMorphisms_of_additive
    ((MonoidalClosed.internalHom).flip.obj 𝒢)

/-- Lemma 18.27.5 (1), source-facing exactness form: if `ℱ₂ ⟶ ℱ₁ ⟶ ℱ ⟶ 0` is exact, then
`0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ₁, 𝒢) ⟶ ℋom_𝒪(ℱ₂, 𝒢)` is exact. -/
@[stacks 0GMY]
theorem ringedSiteModuleInternalHom_exact_in_source
    {S : ShortComplex ModOJ} (hS : S.Exact ∧ Epi S.g) (𝒢 : ModOJ) :
    (S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).Exact ∧
      Mono ((S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).f) := by
  -- Proof comment: apply the left-exact owner criterion to `S.op`, where `Epi S.g` becomes the
  -- required monomorphism on the first map of the opposite short complex.
  let hAb :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :=
    ringedSiteModuleCategory_abelian (J := J) (𝒪 := 𝒪)
  let hAbOp :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))ᵒᵖ :=
    ringedSiteModuleCategory_op_abelian (J := J) (𝒪 := 𝒪)
  let hF := ringedSiteModuleInternalHom_leftExact_in_source (J := J) (𝒪 := 𝒪) 𝒢
  let F : ModOJᵒᵖ ⥤ ModOJ :=
    ((MonoidalClosed.internalHom).flip.obj 𝒢 : ModOJᵒᵖ ⥤ ModOJ)
  letI : F.Additive :=
    @CategoryTheory.functor_additive_of_leftExact_or_rightExact
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))ᵒᵖ
      _ hAbOp
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      F (.inl hF)
  have hmap := ((Functor.preservesFiniteLimits_tfae F).out 3 1).1 <| by
    simpa [leftExactFunctor_iff] using hF
  simpa [F] using hmap S.op ⟨hS.1.op, by simpa using hS.2⟩

end Source

-- Proof sketch: for fixed `ℱ`, the functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` is the right adjoint `ihom ℱ`.
-- Lemma 18.27.4 supplies preservation of limits, and Lemma 12.7.2 packages that as the canonical
-- owner predicate `leftExactFunctor`.
/-- Lemma 18.27.5 (2), owner form: for fixed `ℱ`, the target-variable internal-Hom functor
`𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` is left exact. -/
@[stacks 0GMY]
theorem ringedSiteModuleInternalHom_leftExact_in_target
    (ℱ : ModOJ) :
    leftExactFunctor ModOJ ModOJ (ihom ℱ) := by
  letI := (ihom.adjunction ℱ).rightAdjoint_preservesLimits
  simpa [leftExactFunctor_iff] using
    (inferInstance : PreservesFiniteLimits (ihom ℱ))

-- Proof sketch: once the target-variable owner is known to be left exact, Chapter 12 upgrades
-- that canonical owner property to additivity, and additive functors preserve zero morphisms.
local instance ringedSiteModuleInternalHom_target_preservesZeroMorphisms
    (ℱ : ModOJ) :
    (ihom ℱ).PreservesZeroMorphisms := by
  -- Proof comment: the fixed-source internal-Hom owner is left exact, hence additive, so it
  -- preserves zero morphisms.
  let hAb :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :=
    ringedSiteModuleCategory_abelian (J := J) (𝒪 := 𝒪)
  letI : (ihom ℱ).Additive :=
    @CategoryTheory.functor_additive_of_leftExact_or_rightExact
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      (ihom ℱ)
      (.inl <| ringedSiteModuleInternalHom_leftExact_in_target (J := J) (𝒪 := 𝒪) ℱ)
  exact Functor.preservesZeroMorphisms_of_additive (ihom ℱ)

/-- Lemma 18.27.5 (2), source-facing exactness form: if `0 ⟶ 𝒢 ⟶ 𝒢₁ ⟶ 𝒢₂` is exact, then
`0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ, 𝒢₁) ⟶ ℋom_𝒪(ℱ, 𝒢₂)` is exact. -/
@[stacks 0GMY]
theorem ringedSiteModuleInternalHom_exact_in_target
    {S : ShortComplex ModOJ} (hS : S.Exact ∧ Mono S.f) (ℱ : ModOJ) :
    (S.map (ihom ℱ)).Exact ∧ Mono ((S.map (ihom ℱ)).f) := by
  -- Proof comment: the target-variable clause is the direct owner specialization of left
  -- exactness to a mapped short complex.
  let hAb :
      Abelian (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :=
    ringedSiteModuleCategory_abelian (J := J) (𝒪 := 𝒪)
  let hF := ringedSiteModuleInternalHom_leftExact_in_target (J := J) (𝒪 := 𝒪) ℱ
  let F : ModOJ ⥤ ModOJ := ihom ℱ
  letI : F.Additive :=
    @CategoryTheory.functor_additive_of_leftExact_or_rightExact
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
      _ hAb
      F (.inl hF)
  have hmap := ((Functor.preservesFiniteLimits_tfae F).out 3 1).1 <| by
    simpa [leftExactFunctor_iff] using hF
  simpa [F] using hmap S hS

end
