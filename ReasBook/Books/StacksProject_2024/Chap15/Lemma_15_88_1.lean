import Mathlib
import StacksProject_2024.Chap13.Lemma_13_32_2
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

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
