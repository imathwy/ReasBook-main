import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_88_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
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
private abbrev sequentialRingedModuleLimitEvaluation (n : ℕ) :
    SeqRingMod A ρ ⥤ limMod A ρ :=
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
    {M N : SeqRingMod A ρ} (f : M ⟶ N) (n : ℕ) :
    (sequentialRingedModuleLimitEvaluationStep A ρ n).app M ≫
        (sequentialRingedModuleLimitEvaluation A ρ n).map f =
      (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
        (sequentialRingedModuleLimitEvaluationStep A ρ n).app N := by
  simpa using ((sequentialRingedModuleLimitEvaluationStep A ρ n).naturality f).symm

/-- The sequential inverse system of `A = \varprojlim_n A_n`-modules attached to
`M ∈ \mathrm{Mod}(\mathbf N, (A_n))`, obtained by stagewise restriction of scalars along the
canonical projections `A → A_n`. -/
abbrev ringedModuleLimitTower (M : SeqRingMod A ρ) :
    SequentialInverseSystem (limMod A ρ) :=
  @Functor.ofOpSequence (limMod A ρ) _
    (fun n ↦ (sequentialRingedModuleLimitEvaluation A ρ n).obj M)
    (fun n ↦ (sequentialRingedModuleLimitEvaluationStep A ρ n).app M)

private theorem ringedModuleLimitTower_naturality
    {M N : SeqRingMod A ρ} (f : M ⟶ N) (n : ℕ) :
    (ringedModuleLimitTower A ρ M).map (homOfLE (Nat.le_succ n)).op ≫
        (sequentialRingedModuleLimitEvaluation A ρ n).map f =
      (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
        (ringedModuleLimitTower A ρ N).map (homOfLE (Nat.le_succ n)).op := by
  have h :
      ∀ {M N : SeqRingMod A ρ} (f : M ⟶ N) (n : ℕ),
        (sequentialRingedModuleLimitEvaluationStep A ρ n).app M ≫
            (sequentialRingedModuleLimitEvaluation A ρ n).map f =
          (sequentialRingedModuleLimitEvaluation A ρ (n + 1)).map f ≫
            (sequentialRingedModuleLimitEvaluationStep A ρ n).app N :=
    @sequentialRingedModuleLimitTower_naturality A _ ρ
  simpa [ringedModuleLimitTower] using
    h f n

private abbrev ringedModuleLimitTowerFunctor :
    SeqRingMod A ρ ⥤ SequentialInverseSystem (limMod A ρ) where
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

/-- The inverse-limit functor
`\mathrm{Mod}(\mathbf N, (A_n)) \to \mathrm{Mod}_A`, where `A = \varprojlim_n A_n`. -/
abbrev ringedModuleInverseLimitFunctor : SeqRingMod A ρ ⥤ limMod A ρ :=
  ringedModuleLimitTowerFunctor A ρ ⋙ lim

local notation "KtoD" => mapHomotopyCategoryToDerived (ringedModuleInverseLimitFunctor A ρ)
local notation "RightAcyclic" =>
  IsRightAcyclicForAdditiveFunctor (ringedModuleInverseLimitFunctor A ρ)

instance :
    Functor.Additive (ringedModuleInverseLimitFunctor A ρ) := by
  sorry

local instance :
    HasInjectiveResolutions (SeqRingMod A ρ) := by
  sorry

local instance :
    IsGrothendieckAbelian (SeqRingMod A ρ) := by
  sorry

/-- Lemma 15.88.1 source-facing owner: for a varying ring system
`A₀ ← A₁ ← A₂ ← ⋯` with inverse limit ring `A = \varprojlim_n A_n`, the inverse-limit functor
`\varprojlim : \mathrm{Mod}(\mathbf N, (A_n)) \to \mathrm{Mod}_A` admits a right derived functor
`R\!\varprojlim : D(\mathrm{Mod}(\mathbf N, (A_n))) \to D(A)`. -/
abbrev ringedModuleDerivedInverseLimitFunctor :
    DerivedCategory (SeqRingMod A ρ) ⥤ dLim A ρ := by
  exact additiveFunctorTotalRightDerived.{max u 1, max u 1, max u 1, 0, 0}
    (ringedModuleInverseLimitFunctor A ρ)

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
    (M : SeqRingMod A ρ) :
    IsDerivedLimit
      ((ringedModuleLimitTower A ρ M) ⋙
        DerivedCategory.singleFunctor (limMod A ρ) 0)
      (R lim((DerivedCategory.singleFunctor (SeqRingMod A ρ) 0).obj M)) := sorry

-- Proof sketch: apply the classical Mittag-Leffler acyclicity criterion to the sequential system
-- of `A`-modules obtained from `M ∈ \mathrm{Mod}(\mathbf N, (A_n))` by stagewise restriction of
-- scalars along `A = \varprojlim_n A_n → A_n`.
/-- A Mittag-Leffler object of `\mathrm{Mod}(\mathbf N, (A_n))`, viewed as a sequential inverse
system of `A`-modules with `A = \varprojlim_n A_n`, is right acyclic for inverse limit. -/
theorem ringedModuleLimit_rightAcyclic_of_isMittagLeffler
    (M : SeqRingMod A ρ)
    (hM : SequentialInverseSystem.IsMittagLeffler (ringedModuleLimitTower A ρ M)) :
    RightAcyclic M :=
  sorry

-- Proof sketch: combine the right-acyclicity statement above with the Chapter 13 companion
-- characterization of right acyclicity by vanishing of the positive right derived functors.
/-- Companion to `ringedModuleLimit_rightAcyclic_of_isMittagLeffler`: a Mittag-Leffler object of
`\mathrm{Mod}(\mathbf N, (A_n))` has vanishing positive right derived functors for inverse
limit. -/
theorem ringedModuleInverseLimit_higherRightDerivedVanishes_of_isMittagLeffler
    (M : SeqRingMod A ρ)
    (hM : SequentialInverseSystem.IsMittagLeffler (ringedModuleLimitTower A ρ M)) :
    ∀ n : ℕ, IsZero (((ringedModuleInverseLimitFunctor A ρ).rightDerived (n + 1)).obj M) :=
  sorry

-- Proof sketch: the Stacks Project vanishing theorem for inverse systems of modules gives
-- `R^p \!\varprojlim(M_n) = 0` for `p > 1`, expressed here for the source-facing varying-ring
-- category `\mathrm{Mod}(\mathbf N, (A_n))`.
/-- For `M ∈ \mathrm{Mod}(\mathbf N, (A_n))`, the cohomology objects
`H^p(R \!\varprojlim(M[0]))` vanish for `p > 1`, where the target is `D(A)` with
`A = \varprojlim_n A_n`. -/
theorem ringedModuleInverseLimit_rightDerived_isZero_of_one_lt
    (M : SeqRingMod A ρ) (p : ℕ) (hp : 1 < p) :
    IsZero (R^p lim((DerivedCategory.singleFunctor (SeqRingMod A ρ) 0).obj M)) := sorry

-- Proof sketch: the inverse-limit functor on `\mathrm{Mod}(\mathbf N, (A_n))` satisfies the same
-- abstract derivability criterion as in the abelian-group case, so every complex admits a
-- quasi-isomorphic replacement whose terms are right acyclic for `\varprojlim`.
/-- Every cochain complex of objects of `\mathrm{Mod}(\mathbf N, (A_n))` is quasi-isomorphic to
one whose terms are right acyclic for inverse limit over `A = \varprojlim_n A_n`. -/
theorem exists_quasiIso_to_termwise_ringedModuleLimit_rightAcyclic
    (K : CochainComplex (SeqRingMod A ρ) ℤ) :
    ∃ (L : CochainComplex (SeqRingMod A ρ) ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ i : ℤ, RightAcyclic (L.X i) :=
  sorry

-- Proof sketch: once each term is right acyclic for `\varprojlim`, the ordinary termwise
-- inverse-limit complex already computes the total right derived functor by the standard
-- acyclic-resolution argument.
/-- If each degree `K^p` of a cochain complex in `\mathrm{Mod}(\mathbf N, (A_n))` is right
acyclic for inverse limit over `A = \varprojlim_n A_n`, then the termwise inverse-limit complex
computes `R \!\varprojlim(K)`. -/
theorem ringedModuleDerivedInverseLimit_computes_of_termwise_rightAcyclic
    (K : CochainComplex (SeqRingMod A ρ) ℤ)
    (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD
      (HomotopyCategory.quasiIso (SeqRingMod A ρ) (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient (SeqRingMod A ρ) (ComplexShape.up ℤ)).obj K) := sorry

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
  sorry

instance :
    IsGrothendieckAbelian SeqMod := by
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

/-! ### Lemma_15_88_1_Base (from Chap15) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open Opposite
open SheafOfModules

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)

/-- The functor `ℕᵒᵖ ⥤ CommRingCat` attached to a sequential inverse system
`A₀ ← A₁ ← A₂ ← ⋯`. -/
abbrev sequentialRingSystem
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    ℕᵒᵖ ⥤ CommRingCat.{u} :=
  @Functor.ofOpSequence CommRingCat.{u} _
    (fun n ↦ CommRingCat.of (A n))
    (fun n ↦ CommRingCat.ofHom (ρ n))

private abbrev sequentialRingSystemAsRingCat
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    ℕᵒᵖ ⥤ RingCat.{u} :=
  sequentialRingSystem A ρ ⋙ forget₂ CommRingCat RingCat

/-- The `RingCat`-valued sheaf on the chaotic site of `ℕ` attached to a sequential inverse
system of commutative rings. -/
abbrev sequentialRingSystemRingSheaf
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    Sheaf NatSite RingCat.{u} :=
  (sheafBotEquivalence RingCat.{u}).inverse.obj (sequentialRingSystemAsRingCat A ρ)

/-- The varying-ring module category `Mod(ℕ, (A_n))`. -/
abbrev SeqRingMod
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :=
  SheafOfModules (sequentialRingSystemRingSheaf A ρ)

instance seqRingMod_abelian
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    Abelian (SeqRingMod A ρ) :=
  SheafOfModules.instAbelian (sequentialRingSystemRingSheaf A ρ)

instance seqRingMod_categoryWithHomology
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    CategoryWithHomology (SeqRingMod A ρ) := by
  sorry

/-- Evaluation at stage `n` on `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    SeqRingMod A ρ ⥤ ModuleCat.{u} (A n) :=
  SheafOfModules.evaluation (sequentialRingSystemRingSheaf A ρ) (op n)

instance sequentialRingedModuleEvaluation_additive
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    (sequentialRingedModuleEvaluation A ρ n).Additive := by
  sorry

instance sequentialRingedModuleEvaluation_preservesZeroMorphisms
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
  sorry

/-- The stage-transition natural transformation on `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleEvaluation A ρ n ⋙ ModuleCat.restrictScalars (ρ n) := by
  simpa [sequentialRingedModuleEvaluation, sequentialRingSystemRingSheaf,
      sequentialRingSystem]
    using Functor.whiskerLeft
      (SheafOfModules.forget (sequentialRingSystemRingSheaf A ρ))
      (PresheafOfModules.restriction
        (sequentialRingSystemAsRingCat A ρ)
        ((homOfLE (Nat.le_succ n)).op))

/-- Evaluation at stage `n` on cochain complexes in `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleCochainEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    CochainComplex (SeqRingMod A ρ) ℤ ⥤ CochainComplex (ModuleCat.{u} (A n)) ℤ :=
  letI : (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
    sorry
  (sequentialRingedModuleEvaluation A ρ n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The stage-`n` cochain complex obtained by evaluating a complex of systems of modules. -/
abbrev sequentialRingedModuleCochainEval
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ)
    (M : CochainComplex (SeqRingMod A ρ) ℤ) :
    CochainComplex (ModuleCat.{u} (A n)) ℤ :=
  (sequentialRingedModuleCochainEvaluation A ρ n).obj M

/-- The induced transition natural transformation on stagewise cochain-complex evaluations. -/
abbrev sequentialRingedModuleCochainEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleCochainEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleCochainEvaluation A ρ n ⋙
        (ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  letI : (sequentialRingedModuleEvaluation A ρ (n + 1)).PreservesZeroMorphisms := by
    sorry
  letI : (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
    sorry
  NatTrans.mapHomologicalComplex (sequentialRingedModuleEvaluationStep A ρ n) (ComplexShape.up ℤ)

end

/-! ### Lemma_15_88_1_Core (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along `A_{n + 1} → A_n`, lifted to derived categories. -/
abbrev sequentialRingedModuleTransitionFunctor
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A n)) ⥤ DerivedCategory (ModuleCat.{u} (A (n + 1))) := by
  sorry

/-- Stagewise derived evaluation for the sequential varying-ring module category. -/
abbrev sequentialRingedModuleDerivedEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) [Abelian (SeqRingMod A ρ)]
    [CategoryWithHomology (SeqRingMod A ρ)] (n : ℕ) :
    DerivedCategory (SeqRingMod A ρ) ⥤ DerivedCategory (ModuleCat.{u} (A n)) := by
  sorry

/-- The induced transition morphism between stagewise derived evaluation functors. -/
abbrev sequentialRingedModuleDerivedEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) [Abelian (SeqRingMod A ρ)]
    [CategoryWithHomology (SeqRingMod A ρ)] (n : ℕ) :
    sequentialRingedModuleDerivedEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleDerivedEvaluation A ρ n ⋙
        sequentialRingedModuleTransitionFunctor A ρ n := by
  sorry

/-! ### Lemma_15_88_1_FixedBase (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

/- Fixed-base bridge extracted from Lemma 15.88.1: direct downstream module files should reuse
the canonical owner `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` and the
textbook `R lim(_)` notation, rather than restating the raw derived-functor term locally. -/

instance :
    (lim : SeqMod ⥤ ModuleCat A).Additive := by
  sorry

instance :
    IsGrothendieckAbelian SeqMod := by
  sorry

namespace CategoryTheory

/-- The fixed-base derived inverse-limit functor on sequential inverse systems of `A`-modules
commutes with the triangulated shift. -/
noncomputable instance derivedInverseLimitFunctor_commShift :
    (additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A) : DSeq ⥤ DMod).CommShift ℤ := by
  sorry

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

end

/-! ### Remark_15_88_2 (from Chap15) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

/- Domain-style sampling for Remark 15.88.2:
- primary domain: modules over a sheaf of rings on the chaotic site of `ℕ`, together with their
  derived global sections;
- sampled owner declarations:
  `sequentialRingSystem`,
  `sequentialRingSystemRingSheaf`,
  `SeqRingMod`,
  `ringedModuleDerivedInverseLimitFunctor`,
  `ringSheaf`,
  `CategoryTheory.Sheaf.ΓNatIsoLim`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- best owner abstraction: the Chapter 15 owners `SeqRingMod` and
  `ringedModuleDerivedInverseLimitFunctor`, together with the canonical commutative-ring-sheaf
  owner `ringSheaf` and the canonical global-sections owner `CategoryTheory.Sheaf.ΓNatIsoLim`;
- primitive data: the sequential inverse system of commutative rings `A₀ ← A₁ ← A₂ ← ⋯`,
  encoded by `sequentialRingSystem A ρ`;
- derived API: the chaotic-site module category `SeqRingMod A ρ`, the underived global-sections
  functor on that module category, its Chapter 15 derived inverse-limit owner
  `ringedModuleDerivedInverseLimitFunctor A ρ`, and the general cohomology-versus-`Ext`
  comparison theorem specialized to this setting.

Source/core/bridge triage:
- `source-facing`: the identification of sheaves of modules on the chaotic site of `ℕ` with
  `Mod(ℕ, (A_n))`, together with the interpretation of `R lim` as `RΓ(\mathbf N, -)`;
- `core/canonical`: `sequentialRingSystem`, `SeqRingMod`,
  `ringedModuleDerivedInverseLimitFunctor`, `ringSheaf`,
  `CategoryTheory.Sheaf.ΓNatIsoLim`, and
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: the explicit module-valued global-sections functor on the chaotic site, compared
  with the Chapter 15 inverse-limit owner.

This file is therefore a bridge/view specialization: it should recall the existing owners rather
than introduce a parallel local ring-sheaf wrapper or a duplicate specialization theorem. -/

local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)

/- The chaotic-site global-sections owner `Γ(\mathbf N, -)` identifies the global sections ring of
the structure sheaf `sequentialRingSystemRingSheaf A ρ` with the inverse limit ring
`A∞ = \varprojlim_n A_n`. -/
#check ((Sheaf.ΓNatIsoLim NatSite RingCat.{u}).app (sequentialRingSystemRingSheaf A ρ) :
  (Sheaf.Γ NatSite RingCat.{u}).obj (sequentialRingSystemRingSheaf A ρ) ≅
    limit (sequentialRingSystem A ρ ⋙ forget₂ CommRingCat RingCat))

/- Remark 15.88.2, owner form: together with the global-sections comparison above, the Chapter 15
owner `ringedModuleDerivedInverseLimitFunctor A ρ` is exactly the source-facing
`R\Gamma(\mathbf N,-)` functor on `\mathrm{Mod}(\mathbf N,(A_n))`. The defining total-right-
derived construction itself is already owned upstream by `Lemma_15_88_1`, so this bridge/view file
recalls that owner rather than restating its construction behind a parallel local theorem. -/
#check (ringedModuleDerivedInverseLimitFunctor A ρ :
  DerivedCategory (SeqRingMod A ρ) ⥤
    DerivedCategory (ModuleCat.{0}
      (((limit (sequentialRingSystem A ρ) : CommRingCat.{u}) : Type u))))

/- Remark 15.88.2 uses the canonical Chapter 21 comparison theorem directly; no new specialization
owner is introduced in this bridge/view file. -/
recall underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology

end

/-! ### Lemma_15_88_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "Qis" => HomologicalComplex.quasiIso SeqMod (up ℤ)

/- Domain-style sampling for Lemma 15.88.3 in the fixed-base derived inverse-limit domain:
- sampled owner declarations:
  * `CategoryTheory.Limits.lim`
  * `CategoryTheory.additiveFunctorTotalRightDerived`
  * `Functor.rightDerivedNatTrans`
  * `CategoryTheory.IsDerivedLimit`
- best owner abstraction: the core/canonical owner remains the chosen total right derived functor
  `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` together with its
  source-facing textbook object notation `R lim(K)` and the Chapter `13` predicate
  `IsDerivedLimit`;
- primitive data: only the fixed-base inverse-limit functor
  `lim : SeqMod ⥤ ModuleCat A`;
- derived API: the stagewise tower in `D(A)` obtained by evaluating an object of
  `D(ℕᵒᵖ ⥤ Mod A)` stagewise, and the Milnor-triangle comparison theorem below.

Source/core/bridge triage:
- `source-facing`: the theorem asserting that the chosen `R lim(K)` is a derived limit of the
  stagewise tower `(K_n^•)_n`;
- `core/canonical`: `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` and
  `IsDerivedLimit`;
- `bridge/view`: the stagewise evaluation functors and the induced tower
  `stagewiseModuleDerivedLimitTower K`, whose ambient base ring is inferred from `K`.

This file therefore keeps the source-facing theorem and its minimal stagewise bridge data, while
reusing the canonical fixed-base owner from `Lemma_15_88_1_FixedBase`. -/

/-- Evaluation at stage `n` on sequential inverse systems of `A`-modules. -/
private abbrev stageEvaluation (n : ℕ) :
    SeqMod ⥤ ModuleCat A :=
  (evaluation ℕᵒᵖ (ModuleCat A)).obj (op n)

local instance stageEvaluation_additive (n : ℕ) :
    (stageEvaluation A n).Additive := by
  infer_instance

local instance stageEvaluation_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (stageEvaluation A n) := by
  infer_instance

local instance stageEvaluation_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (stageEvaluation A n) := by
  infer_instance

/-- The stage-`n` functor on the derived category of sequential inverse systems of `A`-modules.
-/
private abbrev stageDerivedEvaluation (n : ℕ) :
    DSeq ⥤ DMod :=
  (stageEvaluation A n).mapDerivedCategory

local instance stageDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (stageDerivedEvaluation A n).IsRightDerivedFunctor
      ((stageEvaluation A n).mapDerivedCategoryFactors.inv)
      Qis := by
  simpa [stageDerivedEvaluation] using
    (Functor.isRightDerivedFunctor_of_inverts Qis
      ((stageEvaluation A n).mapDerivedCategory)
      ((stageEvaluation A n).mapDerivedCategoryFactors))

/-- The transition natural transformation from stage `n + 1` to stage `n`. -/
private abbrev stageEvaluationStep (n : ℕ) :
    stageEvaluation A (n + 1) ⟶ stageEvaluation A n :=
  (evaluation ℕᵒᵖ (ModuleCat A)).map ((homOfLE (Nat.le_succ n)).op)

/-- The induced transition natural transformation on the derived category. -/
private abbrev stageDerivedEvaluationStep (n : ℕ) :
    stageDerivedEvaluation A (n + 1) ⟶ stageDerivedEvaluation A n :=
  Functor.rightDerivedNatTrans
    (stageDerivedEvaluation A (n + 1))
    (stageDerivedEvaluation A n)
    ((stageEvaluation A (n + 1)).mapDerivedCategoryFactors.inv)
    ((stageEvaluation A n).mapDerivedCategoryFactors.inv)
    Qis
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (stageEvaluationStep A n) (up ℤ))
      DerivedCategory.Q)

/-- The stagewise tower in `D(A)` attached to an object of
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. -/
abbrev stagewiseModuleDerivedLimitTower
    {A : Type u} [CommRing A]
    (K : DerivedCategory (SequentialInverseSystem (ModuleCat A))) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  let X : ℕ → DerivedCategory (ModuleCat A) := fun n ↦ (stageDerivedEvaluation A n).obj K
  Functor.ofOpSequence (fun n ↦
    show X (n + 1) ⟶ X n from (stageDerivedEvaluationStep A n).app K)

private theorem stagewiseModuleDerivedLimitTowerFunctor_step_naturality
    {E D : DSeq} (φ : E ⟶ D) (n : ℕ) :
    (stageDerivedEvaluationStep A n).app E ≫
        (stageDerivedEvaluation A n).map φ =
      (stageDerivedEvaluation A (n + 1)).map φ ≫
        (stageDerivedEvaluationStep A n).app D := by
  simpa using ((stageDerivedEvaluationStep A n).naturality φ).symm

private theorem stagewiseModuleDerivedLimitTower_naturality
    {E D : DSeq} (φ : E ⟶ D) (n : ℕ) :
    (stagewiseModuleDerivedLimitTower E).map (homOfLE (Nat.le_succ n)).op ≫
        (stageDerivedEvaluation A n).map φ =
      (stageDerivedEvaluation A (n + 1)).map φ ≫
        (stagewiseModuleDerivedLimitTower D).map (homOfLE (Nat.le_succ n)).op := by
  simpa [stagewiseModuleDerivedLimitTower] using
    stagewiseModuleDerivedLimitTowerFunctor_step_naturality (A := A) φ n

/-- The stagewise evaluation functor
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A) ⥤ \mathbf N^\mathrm{op} ⥤ D(A)`. -/
abbrev stagewiseModuleDerivedLimitTowerFunctor :
    DSeq ⥤ SequentialInverseSystem DMod where
  obj := stagewiseModuleDerivedLimitTower
  map φ :=
    show stagewiseModuleDerivedLimitTower _ ⟶ stagewiseModuleDerivedLimitTower _ from
      NatTrans.ofOpSequence
        (fun n ↦ (stageDerivedEvaluation A n).map φ)
        (stagewiseModuleDerivedLimitTower_naturality (A := A) φ)
  map_id := by
    intro E
    ext n
    simp
  map_comp := by
    intro E D F φ ψ
    ext n
    simp

/-- Lemma 15.88.3: for `K ∈ D(\mathrm{Mod}(\mathbf N, (A_n)))`, modeled here by the fixed-base
bridge object `DerivedCategory (SequentialInverseSystem (ModuleCat A))`, the canonical total
right derived functor `R \!\varprojlim(K)` of `\varprojlim : \mathbf N^\mathrm{op} \to
\mathrm{Mod}_A \to \mathrm{Mod}_A` is a derived limit of the stagewise tower `(K_n^\bullet)_n`
in `D(A)`.
Equivalently, it fits into the canonical Milnor distinguished triangle
`R \!\varprojlim(K) ⟶ \prod_n K_n^\bullet ⟶ \prod_n K_n^\bullet ⟶
R \!\varprojlim(K)[1]`. -/
theorem moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DSeq) :
    IsDerivedLimit (stagewiseModuleDerivedLimitTower K) (R lim(K)) := sorry

/-! ### Lemma_15_88_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open SequentialInverseSystem

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-
Domain-style sampling for Lemma 15.88.4:
- primary domain: Milnor short exact sequences for derived inverse limits in
  `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedLimit`,
  `stagewiseModuleDerivedLimitTower`,
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`;
- best owner abstraction: the Milnor short exact sequence itself is already owned by the canonical
  Chapter 15 theorem `CategoryTheory.derivedLimit_cohomology_shortExact`; this file only supplies
  the fixed-base stagewise bridge from Lemma `15.88.3`;
- primitive data: only `K : D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)` and the stagewise tower
  `stagewiseModuleDerivedLimitTower K`;
- derived API: the chosen derived-limit witness
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation A K` and the resulting short
  exact sequence on cohomology, whose left term is
  `SequentialInverseSystem.firstDerivedLimit
    ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1))`.

Source/core/bridge triage:
- `source-facing`: the fixed-base module specialization of the Milnor short exact sequence;
- `core/canonical`: `CategoryTheory.derivedLimit_cohomology_shortExact`;
- `bridge/view`: `stagewiseModuleDerivedLimitTower K` together with the derived-limit witness from
  Lemma `15.88.3`.
-/

-- Proof sketch: apply the canonical Milnor short exact sequence owner
-- `CategoryTheory.derivedLimit_cohomology_shortExact` to the stagewise tower from Lemma `15.88.3`.
/-- Lemma 15.88.4: with notation as in Lemma `15.88.3`, the long exact cohomology sequence of the
distinguished triangle for `R \!\varprojlim(K)` breaks into a short exact sequence
`0 \to R^1 \!\varprojlim_n H^{p-1}(K_n^\bullet) \to H^p(R \!\varprojlim(K)) \to
\varprojlim_n H^p(K_n^\bullet) \to 0` of `A`-modules. Here the left term is modeled by the
canonical owner
`SequentialInverseSystem.firstDerivedLimit
  ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1))`. -/
theorem moduleDerivedInverseLimit_cohomology_shortExact
    (K : DSeq) (p : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
          ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1)) ⟶
          R^p lim(K))
      (π :
        R^p lim(K) ⟶
          limit ((stagewiseModuleDerivedLimitTower K) ⋙ H p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-! ### Lemma_15_88_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 15.88.5:
- primary domain: derived module objects on the chaotic ringed site attached to a sequential
  inverse system of commutative rings;
- sampled owner declarations:
  `sequentialRingSystem`,
  `SeqRingMod`,
  `DerivedModuleTower`,
  `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.Realization`;
- best owner abstraction: the chapter owner `DerivedCategory (SeqRingMod A ρ)` together with the
  bridge/view owner `DerivedModuleTower A ρ` from `Lemma_15_88_5_Bridge.lean`;
- primitive data: the inverse-system functor `sequentialRingSystem A ρ` and the compatible tower
  `DerivedModuleTower A ρ`;
- derived API: only the realization-existence statement below, phrased directly in terms of the
  bridge owner declarations already defined upstream.

Source/core/bridge triage:
- `source-facing`: the existence of an object of
  `D(Mod(ℕ, (A_n))) = D(SeqRingMod A ρ)`
  realizing prescribed stagewise derived data;
- `core/canonical`: `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: `DerivedModuleTower`, `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.ofDerivedObject`, and
  `DerivedModuleTower.Realization`.

This file is source-facing only: the tower bridge/view API now lives in
`Lemma_15_88_5_Bridge.lean`, and the theorem below reuses that owner-level bridge directly. -/

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [CategoryWithHomology (SeqRingMod A ρ)]

namespace DerivedModuleTower

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

-- Proof sketch: represent the desired object of
-- `D(naturalNumbersRingedModules (sequentialRingSystem A ρ))` by a complex of module sheaves on
-- the chaotic site of `ℕ`, choose right-fraction representatives of the transition morphisms
-- `φ_n`, and inductively modify the representing complex so that its stagewise evaluations realize
-- the given `K_n` with the prescribed compatibility.
/-- Lemma 15.88.5: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, objects
`K_n ∈ D(A_n)` together with compatible transition maps
`φ_n : K_{n + 1} ⟶ K_n` viewed in `D(A_{n + 1})` by restriction of scalars, encoded here by a
compatible tower `T`, there exists an object of `D(Mod(ℕ, (A_n)))` whose stagewise evaluations
recover the stages of `T` compatibly with its tower maps, together with compatible stagewise
identifications. -/
theorem exists_realization
    (T : DerivedModuleTower A ρ) : ∃ (M : DModSeq), Nonempty (T.Realization M) := sorry

end DerivedModuleTower

end

/-! ### Lemma_15_88_5_Bridge (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CommRingCat
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for the bridge owner of Lemma 15.88.5:
- primary domain: stagewise derived evaluation for modules on the sequential ringed site attached
  to an inverse system `A₀ ← A₁ ← A₂ ← ⋯` of commutative rings;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem.stepMap`,
  `SeqRingMod`,
  `sequentialRingedModuleEvaluation`,
  `sequentialRingedModuleDerivedEvaluationStep`,
  `DerivedModuleTower.Realization`;
- best owner abstraction: the source-facing tower owner `DerivedModuleTower A ρ`, together with
  the canonical bridge/view data obtained by evaluating objects of `DerivedCategory (SeqRingMod A ρ)`
  stagewise;
- primitive data: only the stage objects and transition morphisms of the tower itself;
- derived API: canonical stagewise evaluation through
  `(sequentialRingedModuleEvaluation A ρ n).mapDerivedCategory`, the induced transition natural
  transformation on derived categories, extraction of a tower from a global derived object, tower
  realizations `T.Realization M`.

Source/core/bridge triage:
- `source-facing`: the compatible tower of stage objects in the varying derived categories `D(A_n)`;
- `core/canonical`: the ambient owner `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: the canonical stagewise evaluation functors and the comparison predicate
  `DerivedModuleTower.Realization`. -/

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

/-- A compatible stagewise tower in derived module categories over a sequential inverse system of
commutative rings. This is the shared bridge/view layer for Chapter 15 stagewise arguments. -/
structure DerivedModuleTower
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (σ : ∀ n, R (n + 1) →+* R n) where
  /-- The stage `n` object of the tower. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u} (R n))
  /-- The transition morphism from stage `n + 1` to stage `n`, viewed after restriction of
  scalars along `A_{n + 1} → A_n`. -/
  stepMap (n : ℕ) :
    obj (n + 1) ⟶
      ((show DerivedCategory (ModuleCat.{u} (R n)) ⥤
          DerivedCategory (ModuleCat.{u} (R (n + 1))) from
          sequentialRingedModuleTransitionFunctor R σ n).obj (obj n))

namespace DerivedModuleTower

section LimitRestriction

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The `n`th ring `A_n` in a sequential inverse system of commutative rings. -/
abbrev stageRing (n : ℕ) : Type u :=
  (F.obj (op n) : Type u)

/-- The transition ring map `A_{n + 1} → A_n` in a sequential inverse system. -/
abbrev stageTransitionRingHom (n : ℕ) : stageRing F (n + 1) →+* stageRing F n :=
  (F.map (homOfLE (Nat.le_succ n)).op).hom

/-- The inverse limit ring `A = \varprojlim_n A_n` of the sequential inverse system. -/
abbrev inverseLimitRing : Type u :=
  ((limit F : CommRingCat.{u}) : Type u)

/-- The canonical projection `A → A_n` from the inverse limit ring to the `n`th stage. -/
abbrev limitProjectionRingHom (n : ℕ) : inverseLimitRing F →+* stageRing F n :=
  (limit.π F (op n)).hom

/-- Each stage ring is naturally an algebra over the inverse limit ring. -/
instance instAlgebraInverseLimitRingStageRing (n : ℕ) :
    Algebra (inverseLimitRing F) (stageRing F n) :=
  RingHom.toAlgebra (limitProjectionRingHom F n)

/-- Each transition ring map endows `A_n` with its natural `A_{n + 1}`-algebra structure. -/
instance instAlgebraStageSuccStage (n : ℕ) :
    Algebra (stageRing F (n + 1)) (stageRing F n) :=
  RingHom.toAlgebra (stageTransitionRingHom F n)

local instance restrictScalars_limitProjection_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.restrictScalars (limitProjectionRingHom F n)) := by
  sorry

local instance restrictScalars_limitProjection_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (ModuleCat.restrictScalars (limitProjectionRingHom F n)) := by
  sorry

/-- The `n`th stage object viewed over the inverse limit ring `A` by restriction of scalars
along `A → A_n`. -/
abbrev stageRestrictionToLimit
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (inverseLimitRing F)) :=
  ((ModuleCat.restrictScalars (limitProjectionRingHom F n)).mapDerivedCategory.obj (T.obj n))

/-- The stagewise derived base change
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n`
of a compatible tower along `A_{n + 1} → A_n`. -/
abbrev stageDerivedBaseChange
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (stageTransitionRingHom F n)).obj (T.obj (n + 1))

/-- The derived base change
`K \otimes_A^{\mathbf L} A_n`
of an inverse-limit object along the projection `A → A_n`. -/
abbrev inverseLimitBaseChange
    (K : DerivedCategory (ModuleCat.{u} (inverseLimitRing F))) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (limitProjectionRingHom F n)).obj K

end LimitRestriction

variable [CategoryWithHomology (SeqRingMod A ρ)]

local notation "dStep" n => sequentialRingedModuleTransitionFunctor A ρ n
local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/-- The bridge tower extracted from a canonical object of
`D(naturalNumbersRingedModules (sequentialRingSystem A ρ))` by stagewise derived evaluation. -/
abbrev ofDerivedObject
    (M : DModSeq) :
    DerivedModuleTower A ρ where
  obj n := (sequentialRingedModuleDerivedEvaluation A ρ n).obj M
  stepMap n := by
    simpa using (sequentialRingedModuleDerivedEvaluationStep A ρ n).app M

/-- A realization of the compatible tower `T` by the canonical owner object
`M ∈ D(Mod(ℕ, (A_n)))` is a stagewise identification between `T` and the tower extracted from
`M`, compatible with the canonical transition morphisms. -/
structure Realization
    (T : DerivedModuleTower A ρ) (M : DModSeq) where
  /-- The stagewise identification between the extracted tower of `M` and the target tower `T`. -/
  app (n : ℕ) : (ofDerivedObject M).obj n ≅ T.obj n
  /-- These stagewise identifications intertwine the canonical restriction maps with the tower
  maps. -/
  naturality (n : ℕ) :
    CommSq
      ((ofDerivedObject M).stepMap n)
      (app (n + 1)).hom
      ((dStep n).map (app n).hom)
      (T.stepMap n)

end DerivedModuleTower

end

/-! ### Lemma_15_88_5_TowerBridge (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CommRingCat
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

local instance restrictScalars_preservesFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars f) := by
  sorry

local instance restrictScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars f) := by
  sorry

/-- Restriction of scalars along `R_{n + 1} → R_n`, lifted to derived categories. -/
abbrev sequentialRingedModuleTransitionFunctor
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (σ : ∀ n, R (n + 1) →+* R n) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (R n)) ⥤
      DerivedCategory (ModuleCat.{u} (R (n + 1))) :=
  (ModuleCat.restrictScalars (σ n)).mapDerivedCategory

/-- A compatible stagewise tower in derived module categories over a sequential inverse system of
commutative rings. This is the shared bridge/view layer for Chapter 15 stagewise arguments. -/
structure DerivedModuleTower
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (σ : ∀ n, R (n + 1) →+* R n) where
  /-- The stage `n` object of the tower. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u} (R n))
  /-- The transition morphism from stage `n + 1` to stage `n`, viewed after restriction of
  scalars along `R_{n + 1} → R_n`. -/
  stepMap (n : ℕ) :
    obj (n + 1) ⟶ (sequentialRingedModuleTransitionFunctor R σ n).obj (obj n)

namespace DerivedModuleTower

section LimitRestriction

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The `n`th ring `A_n` in a sequential inverse system of commutative rings. -/
abbrev stageRing (n : ℕ) : Type u :=
  (F.obj (op n) : Type u)

/-- The transition ring map `A_{n + 1} → A_n` in a sequential inverse system. -/
abbrev stageTransitionRingHom (n : ℕ) : stageRing F (n + 1) →+* stageRing F n :=
  (F.map (homOfLE (Nat.le_succ n)).op).hom

/-- The inverse limit ring `A = \varprojlim_n A_n` of the sequential inverse system. -/
abbrev inverseLimitRing : Type u :=
  ((limit F : CommRingCat.{u}) : Type u)

/-- The canonical projection `A → A_n` from the inverse limit ring to the `n`th stage. -/
abbrev limitProjectionRingHom (n : ℕ) : inverseLimitRing F →+* stageRing F n :=
  (limit.π F (op n)).hom

/-- Each stage ring is naturally an algebra over the inverse limit ring. -/
instance instAlgebraInverseLimitRingStageRing (n : ℕ) :
    Algebra (inverseLimitRing F) (stageRing F n) :=
  RingHom.toAlgebra (limitProjectionRingHom F n)

/-- Each transition ring map endows `A_n` with its natural `A_{n + 1}`-algebra structure. -/
instance instAlgebraStageSuccStage (n : ℕ) :
    Algebra (stageRing F (n + 1)) (stageRing F n) :=
  RingHom.toAlgebra (stageTransitionRingHom F n)

/-- The `n`th stage object viewed over a fixed base ring `S` by restriction of scalars
along `S → A_n`. -/
abbrev stageRestrictionToBase
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} S) :=
  (ModuleCat.restrictScalars (algebraMap S (stageRing F n))).mapDerivedCategory.obj (T.obj n)

/-- The stagewise derived base change
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n`
of a compatible tower along `A_{n + 1} → A_n`. -/
abbrev stageDerivedBaseChange
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (stageTransitionRingHom F n)).obj (T.obj (n + 1))

/-- The derived base change
`K \otimes_A^{\mathbf L} A_n`
of an inverse-limit object along the projection `A → A_n`. -/
abbrev inverseLimitBaseChange
    (K : DerivedCategory (ModuleCat.{u} (inverseLimitRing F))) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (limitProjectionRingHom F n)).obj K

private theorem stageRestrictionToBase_algebraMap_comp
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    algebraMap S (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap S (stageRing F (n + 1))) := by
  ext x
  simp [RingHom.algebraMap_toAlgebra,
    IsScalarTower.algebraMap_apply S (stageRing F (n + 1)) (stageRing F n)]

private abbrev stageRestrictionToBaseFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ModuleCat.{u} (stageRing F n) ⥤ ModuleCat.{u} S :=
  ModuleCat.restrictScalars (algebraMap S (stageRing F n))

private abbrev stageRestrictionToBaseDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (stageRestrictionToBaseFunctor F S n).mapDerivedCategory

local instance stageRestrictionToBaseDerivedFunctor_isRightDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseDerivedFunctor F S n).IsRightDerivedFunctor
      ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ)) := by
  simpa [stageRestrictionToBaseDerivedFunctor] using
    (Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ))
      (stageRestrictionToBaseDerivedFunctor F S n)
      ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors))

private abbrev stageRestrictionToBaseThenTransitionFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ModuleCat.{u} (stageRing F n) ⥤ ModuleCat.{u} S :=
  ModuleCat.restrictScalars (stageTransitionRingHom F n) ⋙
    stageRestrictionToBaseFunctor F S (n + 1)

private abbrev stageRestrictionToBaseThenTransitionDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n ⋙
    stageRestrictionToBaseDerivedFunctor F S (n + 1)

private noncomputable abbrev stageRestrictionToBaseThenTransitionFactors
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ((stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))) ≅
      (((DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} (stageRing F n)) ℤ ⥤
            DerivedCategory (ModuleCat.{u} (stageRing F n))) ⋙
        sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n) ⋙
          stageRestrictionToBaseDerivedFunctor F S (n + 1)) := by
  simpa [stageRestrictionToBaseFunctor, stageRestrictionToBaseDerivedFunctor,
      stageRestrictionToBaseThenTransitionFunctor,
      stageRestrictionToBaseThenTransitionDerivedFunctor,
      sequentialRingedModuleTransitionFunctor] using
    calc
      (stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) ≅
        (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
          ((stageRestrictionToBaseFunctor F S (n + 1)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))) :=
        Functor.associator
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          ((stageRestrictionToBaseFunctor F S (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))
      _ ≅
          (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙
            ((DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{u} (stageRing F (n + 1)))) ⋙
              stageRestrictionToBaseDerivedFunctor F S (n + 1)) :=
        Functor.isoWhiskerLeft
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (stageRestrictionToBaseFunctor F S (n + 1)).mapDerivedCategoryFactors.symm
      _ ≅
          (((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
                (ComplexShape.up ℤ)) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{u} (stageRing F (n + 1))))) ⋙
            stageRestrictionToBaseDerivedFunctor F S (n + 1) :=
        (Functor.associator
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
              DerivedCategory (ModuleCat.{u} (stageRing F (n + 1))))
          (stageRestrictionToBaseDerivedFunctor F S (n + 1))).symm
      _ ≅
          (((DerivedCategory.Q :
              CochainComplex (ModuleCat.{u} (stageRing F n)) ℤ ⥤
                DerivedCategory (ModuleCat.{u} (stageRing F n))) ⋙
            sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n) ⋙
              stageRestrictionToBaseDerivedFunctor F S (n + 1)) :=
        by
          simpa [sequentialRingedModuleTransitionFunctor] using
            Functor.isoWhiskerRight
              (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapDerivedCategoryFactors.symm
              (stageRestrictionToBaseDerivedFunctor F S (n + 1))

private theorem stageRestrictionToBaseThenTransitionDerived_isRightDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseThenTransitionDerivedFunctor F S n).IsRightDerivedFunctor
      (stageRestrictionToBaseThenTransitionFactors F S n).hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ)) := by
  sorry

private abbrev stageRestrictionToBaseCompIso
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    stageRestrictionToBaseFunctor F S n ≅
      stageRestrictionToBaseThenTransitionFunctor F S n := by
  simpa [stageRestrictionToBaseFunctor, stageRestrictionToBaseThenTransitionFunctor] using
    (ModuleCat.restrictScalarsComp'
      (algebraMap S (stageRing F (n + 1)))
      (stageTransitionRingHom F n)
      (algebraMap S (stageRing F n))
      (stageRestrictionToBase_algebraMap_comp F S n))

private noncomputable abbrev stageRestrictionToBaseCompIsoOnComplexes
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseFunctor F S n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) ≅
      (stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) :=
  Functor.isoWhiskerRight
    (CategoryTheory.NatIso.mapHomologicalComplex
      (stageRestrictionToBaseCompIso F S n) (ComplexShape.up ℤ))
    (DerivedCategory.Q :
      CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))

private noncomputable abbrev stageRestrictionToBaseDerivedIso
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    stageRestrictionToBaseDerivedFunctor F S n ≅
      stageRestrictionToBaseThenTransitionDerivedFunctor F S n := by
  letI := stageRestrictionToBaseThenTransitionDerived_isRightDerivedFunctor F S n
  exact Functor.rightDerivedNatIso
    (stageRestrictionToBaseDerivedFunctor F S n)
    (stageRestrictionToBaseThenTransitionDerivedFunctor F S n)
    ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors.inv)
    (stageRestrictionToBaseThenTransitionFactors F S n).hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ))
    (stageRestrictionToBaseCompIsoOnComplexes F S n)

private noncomputable abbrev stageRestrictionToBaseStep
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    stageRestrictionToBase F S T (n + 1) ⟶ stageRestrictionToBase F S T n := by
  simpa [stageRestrictionToBase, stageRestrictionToBaseDerivedFunctor] using
    (stageRestrictionToBaseDerivedFunctor F S (n + 1)).map (T.stepMap n) ≫
      (stageRestrictionToBaseDerivedIso F S n).inv.app (T.obj n)

/-- The canonical fixed-base inverse system in `D(S)` attached to `T`, obtained by restricting
each stage `T.obj n ∈ D(A_n)` along the chosen base maps `S → A_n`. -/
abbrev stageRestrictionToBaseTower
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat S) :=
  Functor.ofOpSequence (stageRestrictionToBaseStep F S T)

private theorem limitProjectionRingHom_comp (n : ℕ) :
    limitProjectionRingHom F n =
      (stageTransitionRingHom F n).comp (limitProjectionRingHom F (n + 1)) := by
  ext x
  simpa [stageTransitionRingHom, limitProjectionRingHom] using congrArg
    (fun f : limit F ⟶ F.obj (op n) ↦ f x)
    ((limit.w F ((homOfLE (Nat.le_succ n)).op)).symm)

local instance limitProjection_isScalarTower (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F (n + 1)) (stageRing F n) :=
  by
    apply IsScalarTower.of_algebraMap_eq'
    simpa [RingHom.algebraMap_toAlgebra] using limitProjectionRingHom_comp F n

/-- The `n`th stage object viewed over the inverse limit ring `A` by restriction of scalars
along `A → A_n`. -/
abbrev stageRestrictionToLimit
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (inverseLimitRing F)) :=
  stageRestrictionToBase F (inverseLimitRing F) T n

/-- The canonical fixed-base inverse system in `D(A)` attached to `T`, obtained by restricting
each stage `T.obj n ∈ D(A_n)` along the projection `A = \varprojlim_n A_n → A_n`. -/
abbrev stageRestrictionToLimitTower
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing F)) :=
  stageRestrictionToBaseTower F (inverseLimitRing F) T

end LimitRestriction

end DerivedModuleTower

end
