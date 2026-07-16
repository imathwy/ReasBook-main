import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import stacks_proof.stacks_project.Chap13.Lemma_13_20_1
import stacks_proof.stacks_project.Chap13.Lemma_13_32_2
import stacks_proof.stacks_project.Chap13.Lemma_13_16_4
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap15.Lemma_15_87_1
import stacks_proof.stacks_project.Chap15.Lemma_15_88_1_Base
import stacks_proof.stacks_project.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 15.88.1 in the sequential inverse-system / derived-limit domain:
- sampled project owner declarations:
  * `sequentialRingedModuleEvaluation`
  * `sequentialRingedModuleEvaluationStep`
  * `Functor.mapDerivedCategoryFactors`
  * `CategoryTheory.SequentialInverseSystem`
  * `CategoryTheory.IsDerivedLimit`
- source/core/bridge triage:
  * `source-facing`: the derived inverse-limit functor on
    `Mod(ℕ, (Aₙ)) = naturalNumbersRingedModules (sequentialRingSystem A ρ)` with target
    `Mod_{lim Aₙ}`
  * `core/canonical`: the chapter owners `sequentialRingSystem`,
    `naturalNumbersRingedModules`, `sequentialRingedModuleEvaluation`, and
    `CategoryTheory.IsDerivedLimit`
  * `bridge/view`: the fixed-base specialization to sequential inverse systems of `A`-modules

Primitive data for the source-facing owner are only the varying-ring module category
`naturalNumbersRingedModules (sequentialRingSystem A ρ)`, the limit ring `A = lim Aₙ`, and the
stagewise evaluation functors restricted along the canonical projections `A → Aₙ`. The fixed-base
`A`-module inverse-limit constructions are bridge API and should not replace the source-facing
varying-ring owner.
-/

section SourceFacing

/-
The public owner layer for the varying-ring category `Mod(ℕ, (A_n))` is already provided by
`Lemma_15_88_1_Base`; this file keeps only the fixed-limit-ring bridge from that owner to the
source-facing derived inverse-limit functor.
-/
variable (A : ℕ → Type u) [∀ n, CommRing (A n)]
variable (ρ : ∀ n, A (n + 1) →+* A n)
attribute [local instance] seqRingMod_abelian seqRingMod_categoryWithHomology

/-- Helper for Lemma 15.88.1: make the abelian structure on the varying-ring module category
available to later theorem statements. -/
local instance : Abelian (SeqRingMod.{u, u} A ρ) := by
  -- TODO: `SeqRingMod.{u,u} A ρ` is definitionally `ULiftHom (SeqRingMod A ρ)`, while the base
  -- owner `seqRingMod_abelian A ρ` lives on the canonical hom-universe `0` surface. The remaining
  -- blocker is a reusable transport of `Abelian` data across this `ULiftHom` presentation.
  sorry

/-- Helper for Lemma 15.88.1: the varying-ring module category is preadditive. -/
local instance : Preadditive (SeqRingMod.{u, u} A ρ) :=
  Abelian.toPreadditive

/-- Helper for Lemma 15.88.1: the varying-ring module category carries homology data. -/
local instance : CategoryWithHomology (SeqRingMod.{u, u} A ρ) := by
  -- The base-file owner is already registered on this exact surface.
  infer_instance

/-- Helper for Lemma 15.88.1: inverse limit on sequential inverse systems of modules is additive,
because two maps into a limit agree once they agree after every limit projection. -/
private theorem sequentialInverseSystemLimit_additive
    (S : Type u) [CommRing S] :
    Functor.Additive (lim : SequentialInverseSystem (ModuleCat S) ⥤ ModuleCat S) := by
  constructor
  intro X Y f g
  -- Compare the two candidate morphisms into the limit object stagewise.
  apply limit.hom_ext
  intro j
  -- On each projection, `lim` acts by the corresponding component map of the natural
  -- transformation between the two inverse systems.
  change limMap (f + g) ≫ limit.π Y j = (limMap f + limMap g) ≫ limit.π Y j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

/-- Helper for Lemma 15.88.1: the degree-zero object of `D(\mathrm{Mod}(\mathbf N,(A_n)))`
attached to `M`. This isolates the current universe mismatch in `singleFunctor`. -/
private abbrev ringedModuleDegreeZero (M : SeqRingMod.{u, u} A ρ) :
    DerivedCategory (SeqRingMod.{u, u} A ρ) :=
  (DerivedCategory.singleFunctor (SeqRingMod.{u, u} A ρ) (0 : ℤ)).obj M

private abbrev limRing : Type u :=
  ((limit (sequentialRingSystem A ρ) : CommRingCat.{u}) : Type u)

private abbrev limMod :=
  ModuleCat.{u} (limRing A ρ)

private abbrev dLim :=
  DerivedCategory (limMod A ρ)

private abbrev sequentialRingLimitProjection (n : ℕ) : limRing A ρ →+* A n :=
  (limit.π (sequentialRingSystem A ρ) (op n)).hom

local instance instAlgebraSequentialRingLimitStage (n : ℕ) : Algebra (limRing A ρ) (A n) :=
  RingHom.toAlgebra (sequentialRingLimitProjection A ρ n)

private theorem sequentialRingLimitProjection_comp (n : ℕ) :
    sequentialRingLimitProjection A ρ n =
      (ρ n).comp (sequentialRingLimitProjection A ρ (n + 1)) := by
  ext x
  simpa using congrArg
    (fun f : limit (sequentialRingSystem A ρ) ⟶ (sequentialRingSystem A ρ).obj (op n) ↦ f x)
    ((limit.w (sequentialRingSystem A ρ) ((homOfLE (Nat.le_succ n)).op)).symm)

/-- Evaluation at stage `n`, then restriction of scalars along `A = \varprojlim_n A_n → A_n`.
This is the source-facing `A`-module valued stage functor on `\mathrm{Mod}(\mathbf N, (A_n))`. -/
-- Route correction: use the canonical universe on `SeqRingMod A ρ`; the ad hoc `{u, 0}`
-- specialization mismatched the evaluation-owner universe and blocked elaboration before any
-- source-faithful fixed-base comparison could be stated.
private abbrev sequentialRingedModuleLimitEvaluation (n : ℕ) :
    SeqRingMod.{u, u} A ρ ⥤ limMod A ρ :=
  sequentialRingedModuleEvaluation A ρ n ⋙
    ModuleCat.restrictScalars (sequentialRingLimitProjection A ρ n)

/-- The transition morphism on the stagewise `A`-module tower attached to an object of
`\mathrm{Mod}(\mathbf N, (A_n))`. -/
private abbrev sequentialRingedModuleLimitEvaluationStep (n : ℕ) :
    sequentialRingedModuleLimitEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleLimitEvaluation A ρ n :=
  (Functor.whiskerRight
      (sequentialRingedModuleEvaluationStep A ρ n)
      (ModuleCat.restrictScalars (sequentialRingLimitProjection A ρ (n + 1)))) ≫
    Functor.whiskerLeft (sequentialRingedModuleEvaluation A ρ n)
      ((ModuleCat.restrictScalarsComp'
        (sequentialRingLimitProjection A ρ (n + 1))
        (ρ n)
        (sequentialRingLimitProjection A ρ n)
        (sequentialRingLimitProjection_comp A ρ n)).inv)

private theorem sequentialRingedModuleLimitTower_naturality
    {M N : SeqRingMod.{u, u} A ρ} (f : M ⟶ N) (n : ℕ) :
    (sequentialRingedModuleLimitEvaluationStep A ρ n).app M ≫
        (sequentialRingedModuleLimitEvaluation A ρ n).map f =
      (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
        (sequentialRingedModuleLimitEvaluationStep A ρ n).app N := by
  simpa using ((sequentialRingedModuleLimitEvaluationStep A ρ n).naturality f).symm

/-- The sequential inverse system of `A = \varprojlim_n A_n`-modules attached to
`M ∈ \mathrm{Mod}(\mathbf N, (A_n))`, obtained by stagewise restriction of scalars along the
canonical projections `A → A_n`. -/
abbrev ringedModuleLimitTower (M : SeqRingMod.{u, u} A ρ) :
    SequentialInverseSystem (limMod A ρ) :=
  @Functor.ofOpSequence (limMod A ρ) _
    (fun n ↦ (sequentialRingedModuleLimitEvaluation A ρ n).obj M)
    (fun n ↦ (sequentialRingedModuleLimitEvaluationStep A ρ n).app M)

private theorem ringedModuleLimitTower_naturality
    {M N : SeqRingMod.{u, u} A ρ} (f : M ⟶ N) (n : ℕ) :
    (ringedModuleLimitTower A ρ M).map (homOfLE (Nat.le_succ n)).op ≫
        (sequentialRingedModuleLimitEvaluation A ρ n).map f =
      (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
        (ringedModuleLimitTower A ρ N).map (homOfLE (Nat.le_succ n)).op := by
  have h :
      ∀ {M N : SeqRingMod.{u, u} A ρ} (f : M ⟶ N) (n : ℕ),
        (sequentialRingedModuleLimitEvaluationStep A ρ n).app M ≫
            (sequentialRingedModuleLimitEvaluation A ρ n).map f =
          (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
            (sequentialRingedModuleLimitEvaluationStep A ρ n).app N :=
    @sequentialRingedModuleLimitTower_naturality A _ ρ
  simpa [ringedModuleLimitTower] using
    h f n

private abbrev ringedModuleLimitTowerFunctor :
    SeqRingMod.{u, u} A ρ ⥤ SequentialInverseSystem (limMod A ρ) where
  obj := ringedModuleLimitTower A ρ
  map f :=
    show ringedModuleLimitTower A ρ _ ⟶ ringedModuleLimitTower A ρ _ from
      NatTrans.ofOpSequence
        (fun n ↦ (sequentialRingedModuleLimitEvaluation A ρ n).map f)
        (ringedModuleLimitTower_naturality A ρ f)
  map_id := by
    intro M
    ext n
    simp
  map_comp := by
    intro M N P f g
    ext n
    simp

/-- Helper for Lemma 15.88.1: the `n`th component of the tower-functor map is the stagewise
evaluation of the original morphism. This isolates the component formula needed for the eventual
componentwise additivity proof. -/
private theorem ringedModuleLimitTowerFunctor_map_app
    {M N : SeqRingMod.{u, u} A ρ} (f : M ⟶ N) (n : ℕ) :
    ((ringedModuleLimitTowerFunctor A ρ).map f).app (op n) =
      (sequentialRingedModuleLimitEvaluation A ρ n).map f := by
  -- Unfold the tower-functor map once so the `n`th component is exactly the evaluated morphism.
  rfl

/-- Helper for Lemma 15.88.1: after evaluating the `n`th tower-map component on an element, one
simply applies the stagewise restricted-scalars map of the original morphism. -/
private theorem ringedModuleLimitTowerFunctor_map_app_apply
    {M N : SeqRingMod.{u, u} A ρ} (f : M ⟶ N) (n : ℕ)
    (x : ((ringedModuleLimitTower A ρ M).obj (op n) : limMod A ρ)) :
    (ModuleCat.Hom.hom (((ringedModuleLimitTowerFunctor A ρ).map f).app (op n))) x =
      (ModuleCat.Hom.hom ((sequentialRingedModuleLimitEvaluation A ρ n).map f)) x := by
  -- Evaluating the component formula at an element does not change it.
  rfl

/-- Helper for Lemma 15.88.1: applying the sum of two tower-map components to an element is the
sum of the two stagewise values. -/
private theorem ringedModuleLimitTowerFunctor_sum_app_apply
    {M N : SeqRingMod.{u, u} A ρ} (f g : M ⟶ N) (n : ℕ)
    (x : ((ringedModuleLimitTower A ρ M).obj (op n) : limMod A ρ)) :
    (ModuleCat.Hom.hom
        ((((ringedModuleLimitTowerFunctor A ρ).map f +
            (ringedModuleLimitTowerFunctor A ρ).map g).app (op n)))) x =
      (ModuleCat.Hom.hom (((ringedModuleLimitTowerFunctor A ρ).map f).app (op n))) x +
        (ModuleCat.Hom.hom (((ringedModuleLimitTowerFunctor A ρ).map g).app (op n))) x := by
  -- Addition of natural transformations is pointwise, and addition in `ModuleCat` is pointwise.
  change
      (ModuleCat.Hom.hom
          ((((ringedModuleLimitTowerFunctor A ρ).map f).app (op n) +
              (((ringedModuleLimitTowerFunctor A ρ).map g).app (op n))))) x =
        (ModuleCat.Hom.hom (((ringedModuleLimitTowerFunctor A ρ).map f).app (op n))) x +
          (ModuleCat.Hom.hom (((ringedModuleLimitTowerFunctor A ρ).map g).app (op n))) x
  rw [ModuleCat.hom_add]
  rw [LinearMap.add_apply]

/-- Helper for Lemma 15.88.1: the stagewise restricted-scalars evaluation sends a sum of
morphisms to the sum of the evaluated maps on the explicit `SeqRingMod.{u,u}` surface. -/
private theorem sequentialRingedModuleLimitEvaluation_map_add_apply_surface
    {M N : SeqRingMod.{u, u} A ρ} (f g : M ⟶ N) (n : ℕ)
    (x : ((sequentialRingedModuleLimitEvaluation A ρ n).obj M : limMod A ρ)) :
    (ModuleCat.Hom.hom
        ((sequentialRingedModuleLimitEvaluation A ρ n).map (f + g))) x =
      (ModuleCat.Hom.hom ((sequentialRingedModuleLimitEvaluation A ρ n).map f)) x +
        (ModuleCat.Hom.hom ((sequentialRingedModuleLimitEvaluation A ρ n).map g)) x := by
  -- The stagewise functor sends `f + g` to the sum of the two mapped morphisms definitionally.
  have hmap :
      (sequentialRingedModuleLimitEvaluation A ρ n).map (f + g) =
        (sequentialRingedModuleLimitEvaluation A ρ n).map f +
          (sequentialRingedModuleLimitEvaluation A ρ n).map g := by
    rfl
  -- Evaluating that equality at an element turns it into the desired pointwise identity.
  simpa [ModuleCat.hom_add, LinearMap.add_apply] using
    congrArg (fun h ↦ (ModuleCat.Hom.hom h) x) hmap

/-- Helper for Lemma 15.88.1: the stagewise tower functor is additive because each evaluated
stage functor is additive. -/
private theorem ringedModuleLimitTowerFunctor_additive :
    Functor.Additive (ringedModuleLimitTowerFunctor A ρ) := by
  -- TODO: the stagewise pointwise identity is now isolated in
  -- `sequentialRingedModuleLimitEvaluation_map_add_apply_surface`, but the final `Functor.Additive`
  -- packaging still hits a coercion mismatch between the sheaf-level `AddCommGroup` on morphisms
  -- and the local `Preadditive.homGroup` used on the explicit `SeqRingMod.{u,u}` surface.
  sorry

/-- Helper for Lemma 15.88.1: the varying-ring module category is Grothendieck abelian on the
local `{u, u}` surface used in this file. -/
local instance seqRingMod_isGrothendieckAbelian_surface :
    IsGrothendieckAbelian.{u + 1} (SeqRingMod.{u, u} A ρ) := by
  -- TODO: transport the Grothendieck owner from the canonical sheaf-of-modules surface to this
  -- local `{u, u}` surface. The current blocker is the missing source-side owner itself.
  sorry

/-- The inverse-limit functor
`\mathrm{Mod}(\mathbf N, (A_n)) \to \mathrm{Mod}_A`, where `A = \varprojlim_n A_n`. -/
abbrev ringedModuleInverseLimitFunctor : SeqRingMod.{u, u} A ρ ⥤ limMod A ρ :=
  ringedModuleLimitTowerFunctor A ρ ⋙ lim

local notation "KtoD" => mapHomotopyCategoryToDerived (ringedModuleInverseLimitFunctor A ρ)
local notation "RightAcyclic" =>
  IsRightAcyclicForAdditiveFunctor (ringedModuleInverseLimitFunctor A ρ)

/-- Helper for Lemma 15.88.1: placeholder additive structure on the source-facing inverse-limit
functor while the `SeqRingMod` universe owner is being normalized. -/
local instance ringedModuleInverseLimitFunctor_additive :
    Functor.Additive (ringedModuleLimitTowerFunctor A ρ ⋙ lim) := by
  -- Compose the additive stagewise tower functor with the additive inverse-limit functor on the
  -- fixed-base module category.
  letI : Functor.Additive (ringedModuleLimitTowerFunctor A ρ) :=
    ringedModuleLimitTowerFunctor_additive (A := A) (ρ := ρ)
  letI : Functor.Additive (lim : SequentialInverseSystem (limMod A ρ) ⥤ limMod A ρ) :=
    sequentialInverseSystemLimit_additive (S := limRing A ρ)
  infer_instance

/-- Helper for Lemma 15.88.1: adapter instance rewriting the additive placeholder to the public
inverse-limit functor abbreviation. -/
local instance ringedModuleInverseLimitFunctor_additive_abbrev :
    Functor.Additive (ringedModuleInverseLimitFunctor A ρ) := by
  -- Unfold the public abbreviation once and reuse the additive composite instance above.
  simpa [ringedModuleInverseLimitFunctor] using
    (inferInstance : Functor.Additive (ringedModuleLimitTowerFunctor A ρ ⋙ lim))

/-- Helper for Lemma 15.88.1: placeholder injective-resolution owner on the normalized
source-facing category. -/
local instance :
    HasInjectiveResolutions (SeqRingMod.{u, u} A ρ) := by
  -- TODO: once the source-side Grothendieck owner is available on this surface, this should be
  -- discharged by instance search.
  sorry

/-- Helper for Lemma 15.88.1: placeholder Grothendieck-abelian owner on the normalized
source-facing category. -/
local instance :
    IsGrothendieckAbelian.{u + 1} (SeqRingMod.{u, u} A ρ) := by
  -- Reuse the named surface-normalization helper introduced above.
  infer_instance

/-- Lemma 15.88.1 source-facing owner: for a varying ring system
`A₀ ← A₁ ← A₂ ← ⋯` with inverse limit ring `A = \varprojlim_n A_n`, the inverse-limit functor
`\varprojlim : \mathrm{Mod}(\mathbf N, (A_n)) \to \mathrm{Mod}_A` admits a right derived functor
`R\!\varprojlim : D(\mathrm{Mod}(\mathbf N, (A_n))) \to D(A)`. -/
@[stacks 091D]
abbrev ringedModuleDerivedInverseLimitFunctor :
    DerivedCategory (SeqRingMod.{u, u} A ρ) ⥤ dLim A ρ :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (ringedModuleInverseLimitFunctor A ρ)

/-- Helper for Lemma 15.88.1: the cochain-level inverse-limit functor has a total right derived
functor because `SeqRingMod A ρ` is Grothendieck abelian. -/
local instance :
    ((ringedModuleInverseLimitFunctor A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ)) :=
  _root_.CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor.{u + 1, u + 1, u + 1, u, u}
    (ringedModuleInverseLimitFunctor A ρ)

/-- Helper for Lemma 15.88.1: right-acyclic objects for the source-facing inverse-limit functor
have monomorphic envelopes, because every object admits an injective presentation and injectives
are right acyclic for additive functors. -/
local instance ringedModuleLimit_rightAcyclic_hasMonoEmbedding :
    HasMonoEmbedding RightAcyclic where
  exists_mono M := by
    -- Use an injective presentation of `M` and then apply the general injective-acyclicity
    -- theorem for additive functors.
    let p := (EnoughInjectives.presentation M).some
    refine ⟨p.J, ?_, p.f, inferInstance⟩
    exact injective_isRightAcyclicForAdditiveFunctor
      (F := ringedModuleInverseLimitFunctor A ρ) p.J

/-- Helper for Lemma 15.88.1: the homotopy-to-derived inverse-limit functor still needs the
source-facing unbounded right-derived owner, obtained from Chapter `13` once right-acyclic
objects have mono envelopes. -/
local instance :
    Functor.HasRightDerivedFunctor KtoD
      (HomotopyCategory.quasiIso (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ)) := by
  -- Route correction: use the canonical Chapter `13` existence theorem for the homotopy-level
  -- right derived functor, rather than building a bespoke comparison with the cochain-level
  -- total right derived functor.
  exact
    has_unbounded_rightDerivedFunctor_of_mono_into_higherRightDerivedVanishes
      (F := ringedModuleInverseLimitFunctor A ρ)

namespace CategoryTheory

/- Textbook notation for the varying-ring derived inverse-limit object `R lim(K)` in
`D(\varprojlim_n A_n)`. -/
scoped notation:max "R" " lim(" K ")" =>
  Functor.obj (ringedModuleDerivedInverseLimitFunctor _ _) K

/- Textbook notation for the cohomology object `R^p lim(K) = H^p(R lim(K))` in
`\operatorname{Mod}_{\varprojlim_n A_n}`. -/
scoped notation:max "R^" p:max " lim(" K ")" =>
  Functor.obj (DerivedCategory.homologyFunctor _ p)
    (Functor.obj (ringedModuleDerivedInverseLimitFunctor _ _) K)

end CategoryTheory

-- Proof sketch: after viewing `M ∈ \mathrm{Mod}(\mathbf N, (A_n))` as the sequential system of
-- `A`-modules obtained by stagewise restriction of scalars along `A = \varprojlim_n A_n → A_n`,
-- the Milnor distinguished triangle identifies `R \!\varprojlim(M[0])` with a derived limit of
-- that stagewise tower in `D(A)`.
/-- Applying `R \!\varprojlim` to an object of `\mathrm{Mod}(\mathbf N, (A_n))` viewed in degree
`0` yields the standard derived-limit object in `D(A)`, where `A = \varprojlim_n A_n`. -/
theorem ringedModuleDerivedInverseLimit_isDerivedLimit_of_inverseSystem
    (M : SeqRingMod.{u, u} A ρ) :
    IsDerivedLimit
      ((ringedModuleLimitTower A ρ M) ⋙
        DerivedCategory.singleFunctor (limMod A ρ) 0)
      (R lim(ringedModuleDegreeZero A ρ M)) := by
  -- TODO: identify `R lim(M[0])` with the fixed-base `A`-module derived limit of
  -- `ringedModuleLimitTower A ρ M`; the missing Grothendieck/injective-resolution bridge above
  -- prevents this source-facing comparison from being stated in a usable form.
  sorry

-- Proof sketch: apply the classical Mittag-Leffler acyclicity criterion to the sequential system
-- of `A`-modules obtained from `M ∈ \mathrm{Mod}(\mathbf N, (A_n))` by stagewise restriction of
-- scalars along `A = \varprojlim_n A_n → A_n`.
/-- A Mittag-Leffler object of `\mathrm{Mod}(\mathbf N, (A_n))`, viewed as a sequential inverse
system of `A`-modules with `A = \varprojlim_n A_n`, is right acyclic for inverse limit. -/
theorem ringedModuleLimit_rightAcyclic_of_isMittagLeffler
    (M : SeqRingMod.{u, u} A ρ)
    (hM : SequentialInverseSystem.IsMittagLeffler (ringedModuleLimitTower A ρ M)) :
    RightAcyclic M := by
  -- TODO: reduce to the fixed-base module Mittag-Leffler acyclicity theorem for
  -- `ringedModuleLimitTower A ρ M`; that fixed-base theorem is the first missing owner-level
  -- input once the source category infrastructure above is repaired.
  sorry

-- Proof sketch: combine the right-acyclicity statement above with the Chapter 13 companion
-- characterization of right acyclicity by vanishing of the positive right derived functors.
/-- Companion to `ringedModuleLimit_rightAcyclic_of_isMittagLeffler`: a Mittag-Leffler object of
`\mathrm{Mod}(\mathbf N, (A_n))` has vanishing positive right derived functors for inverse
limit. -/
theorem ringedModuleInverseLimit_higherRightDerivedVanishes_of_isMittagLeffler
    (M : SeqRingMod.{u, u} A ρ)
    (hM : SequentialInverseSystem.IsMittagLeffler (ringedModuleLimitTower A ρ M)) :
    ∀ n : ℕ, IsZero (((ringedModuleInverseLimitFunctor A ρ).rightDerived (n + 1)).obj M) := by
  -- First upgrade the Mittag-Leffler hypothesis to right acyclicity for inverse limit.
  have hacyclic : RightAcyclic M :=
    ringedModuleLimit_rightAcyclic_of_isMittagLeffler A ρ M hM
  -- Then read off the vanishing of all positive right derived functors from the Chapter 13
  -- characterization of right acyclicity.
  exact
    (isRightAcyclicForAdditiveFunctor_iff_isIso_toRightDerivedZero_app_and_higherRightDerivedVanishes
      (F := ringedModuleInverseLimitFunctor A ρ) M).1 hacyclic |>.2

-- Proof sketch: the Stacks Project vanishing theorem for inverse systems of modules gives
-- `R^p \!\varprojlim(M_n) = 0` for `p > 1`, expressed here for the source-facing varying-ring
-- category `\mathrm{Mod}(\mathbf N, (A_n))`.
/-- For `M ∈ \mathrm{Mod}(\mathbf N, (A_n))`, the cohomology objects
`H^p(R \!\varprojlim(M[0]))` vanish for `p > 1`, where the target is `D(A)` with
`A = \varprojlim_n A_n`. -/
theorem ringedModuleInverseLimit_rightDerived_isZero_of_one_lt
    (M : SeqRingMod.{u, u} A ρ) (p : ℕ) (hp : 1 < p) :
    IsZero (R^p lim(ringedModuleDegreeZero A ρ M)) := by
  -- TODO: first establish the fixed-base module vanishing `R^p lim = 0` for `p > 1`, then
  -- specialize it to the stagewise restricted tower `ringedModuleLimitTower A ρ M`.
  sorry

-- Proof sketch: the inverse-limit functor on `\mathrm{Mod}(\mathbf N, (A_n))` satisfies the same
-- abstract derivability criterion as in the abelian-group case, so every complex admits a
-- quasi-isomorphic replacement whose terms are right acyclic for `\varprojlim`.
/-- Every cochain complex of objects of `\mathrm{Mod}(\mathbf N, (A_n))` is quasi-isomorphic to
one whose terms are right acyclic for inverse limit over `A = \varprojlim_n A_n`. -/
theorem exists_quasiIso_to_termwise_ringedModuleLimit_rightAcyclic
    (K : CochainComplex (SeqRingMod.{u, u} A ρ) ℤ) :
    ∃ (L : CochainComplex (SeqRingMod.{u, u} A ρ) ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ i : ℤ, RightAcyclic (L.X i) :=
  by
  -- Chapter `13` now applies directly once the mono-into-right-acyclic helper above is in place.
  exact
    exists_quasiIso_to_termwise_higherRightDerivedVanishes
      (F := ringedModuleInverseLimitFunctor A ρ) K

-- Proof sketch: once each term is right acyclic for `\varprojlim`, the ordinary termwise
-- inverse-limit complex already computes the total right derived functor by the standard
-- acyclic-resolution argument.
/-- If each degree `K^p` of a cochain complex in `\mathrm{Mod}(\mathbf N, (A_n))` is right
acyclic for inverse limit over `A = \varprojlim_n A_n`, then the termwise inverse-limit complex
computes `R \!\varprojlim(K)`. -/
theorem ringedModuleDerivedInverseLimit_computes_of_termwise_rightAcyclic
    (K : CochainComplex (SeqRingMod.{u, u} A ρ) ℤ)
    (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD
      (HomotopyCategory.quasiIso (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ)).obj K) := by
  -- Once every term is right acyclic, the Chapter `13` computation theorem identifies the
  -- ordinary termwise inverse-limit complex with the chosen unbounded derived inverse limit.
  exact
    computes_unbounded_rightDerived_of_termwise_higherRightDerivedVanishes
      (F := ringedModuleInverseLimitFunctor A ρ) K hK

end SourceFacing

section FixedBaseBridge

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)

/-
Direct downstream fixed-base module files should reuse the canonical owner
`additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` rather than repackage it behind
fresh local wrapper names. The only extra data they repeatedly need are the additive structure on
`lim` and the Grothendieck-abelian structure on `SeqMod`, so those instances belong here.
-/

instance :
    (lim : SeqMod ⥤ ModuleCat A).Additive := by
  -- Reuse the stagewise comparison proof above for the fixed-base module category.
  simpa using sequentialInverseSystemLimit_additive (S := A)

/-- Helper for Lemma 15.88.1: exactness of filtered colimits in the fixed-base inverse-system
category is computed pointwise from exactness in `ModuleCat A`. -/
private theorem sequentialInverseSystemModule_hasExactColimitsOfShape
    (J : Type) [Category J] [IsFiltered J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] :
    HasExactColimitsOfShape J SeqMod := by
  -- Route correction: isolate the functor-category AB5 step before packaging the full
  -- Grothendieck owner on `SeqMod`.
  -- TODO: the mathematical step is pointwise exactness in the functor category; the remaining
  -- work is only to normalize the universe parameters on `HasExactColimitsOfShape`.
  sorry

/-- Helper for Lemma 15.88.1: the fixed-base inverse-system category inherits the small-AB5
package from `ModuleCat A` by pointwise exactness of filtered colimits. -/
private theorem sequentialInverseSystemModule_ab5_zero
    [AB5OfSize.{0, 0} (ModuleCat.{u} A)] :
    AB5OfSize.{0, 0} SeqMod where
  ofShape J _ _ := by
    -- Package the pointwise exact-colimit theorem above as the AB5 owner needed later for the
    -- fixed-base derived inverse-limit argument.
    exact sequentialInverseSystemModule_hasExactColimitsOfShape (A := A) J

/-- Helper for Lemma 15.88.1: `ModuleCat A` satisfies the small-AB5 hypothesis needed for the
pointwise fixed-base Grothendieck package. -/
local instance moduleCat_ab5_zero :
    AB5OfSize.{0, 0} (ModuleCat.{u} A) :=
  -- Reuse the standard small-universe AB5 owner for module categories.
  AB5OfSize_shrink (ModuleCat.{u} A)

/-- Helper for Lemma 15.88.1: the fixed-base inverse-system category is locally small in hom
universe `0` after rewriting to the functor-category surface. -/
local instance sequentialInverseSystemModule_locallySmall_zero :
    LocallySmall.{0} SeqMod := by
  -- TODO: normalize the functor-category `LocallySmall` owner to the fixed-base `SeqMod`
  -- surface without triggering the current universe mismatch.
  sorry

/-- Helper for Lemma 15.88.1: the fixed-base inverse-system category has a separator because the
functor-category surface does. -/
local instance sequentialInverseSystemModule_hasSeparator :
    HasSeparator SeqMod := by
  -- TODO: normalize the functor-category `HasSeparator` owner to the fixed-base `SeqMod`
  -- surface without triggering the current universe mismatch.
  sorry

instance :
    IsGrothendieckAbelian SeqMod := by
  -- Package the functor-category smallness/separator exports together with the pointwise AB5
  -- owner already isolated above.
  let _ : AB5OfSize.{0, 0} SeqMod := sequentialInverseSystemModule_ab5_zero (A := A)
  -- TODO: package the fixed-base Grothendieck owner explicitly once the smallness/separator
  -- bridge elaborates without the current universe mismatch.
  sorry

namespace CategoryTheory

/- Textbook notation for the fixed-base derived inverse-limit object `R lim(K)` in `D(A)`. -/
scoped notation:max "R" " lim(" K ")" =>
  Functor.obj
    (CategoryTheory.additiveFunctorTotalRightDerived
      (CategoryTheory.Limits.lim :
        SequentialInverseSystem (ModuleCat _) ⥤ ModuleCat _))
    K

/- Textbook notation for the cohomology object `R^p lim(K) = H^p(R lim(K))` in `Mod_A`. -/
scoped notation:max "R^" p:max " lim(" K ")" =>
  Functor.obj
    (DerivedCategory.homologyFunctor (ModuleCat _) p)
    (Functor.obj
      (CategoryTheory.additiveFunctorTotalRightDerived
        (CategoryTheory.Limits.lim :
          SequentialInverseSystem (ModuleCat _) ⥤ ModuleCat _))
      K)

end CategoryTheory

end FixedBaseBridge
