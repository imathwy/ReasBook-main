import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_1_Core

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

/-- Lemma_15_88_5_Bridge: a compatible stagewise tower in derived module categories over a
sequential inverse system of commutative rings. This is the shared bridge/view layer for Chapter
15 stagewise arguments. -/
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

/-- Helper for Lemma_15_88_5_Bridge: restriction of scalars along the limit projection preserves
finite limits. -/
local instance restrictScalars_limitProjection_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n)) := by
  let G :
      ModuleCat.{u} (inverseLimitRing F) ⥤ AddCommGrpCat.{u} :=
    forget₂ _ AddCommGrpCat
  -- After forgetting to abelian groups, restriction of scalars is just the usual forgetful
  -- functor from modules over the stage ring.
  have :
      PreservesFiniteLimits
        (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n) ⋙ G) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat.{u} (stageRing F n)) AddCommGrpCat.{u})
    infer_instance
  -- The forgetful functor reflects finite limits, so preservation descends back upstairs.
  exact preservesFiniteLimits_of_reflects_of_preserves
    (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n)) G

/-- Helper for Lemma_15_88_5_Bridge: restriction of scalars along the limit projection preserves
finite colimits. -/
local instance restrictScalars_limitProjection_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n)) := by
  let G :
      ModuleCat.{u} (inverseLimitRing F) ⥤ AddCommGrpCat.{u} :=
    forget₂ _ AddCommGrpCat
  -- After forgetting to abelian groups, restriction of scalars is again the usual forgetful
  -- functor from modules over the stage ring.
  have :
      PreservesFiniteColimits
        (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n) ⋙ G) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (stageRing F n)) AddCommGrpCat.{u})
    infer_instance
  -- Reflection along the forgetful functor upgrades the preserved colimits to modules.
  exact preservesFiniteColimits_of_reflects_of_preserves
    (ModuleCat.restrictScalars.{u} (limitProjectionRingHom F n)) G

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

/-- Helper for Lemma_15_88_5_Bridge: the canonical component of the derived evaluation transition
has exactly the tower morphism type required by `DerivedModuleTower.ofDerivedObject`. -/
abbrev ofDerivedObject_stepMap (M : DModSeq) (n : ℕ) :
    (sequentialRingedModuleDerivedEvaluation A ρ (n + 1)).obj M ⟶
      ((show DerivedCategory (ModuleCat.{u} (A n)) ⥤
          DerivedCategory (ModuleCat.{u} (A (n + 1))) from
          sequentialRingedModuleTransitionFunctor A ρ n).obj
        ((sequentialRingedModuleDerivedEvaluation A ρ n).obj M)) :=
  show
    (sequentialRingedModuleDerivedEvaluation A ρ (n + 1)).obj M ⟶
      ((show DerivedCategory (ModuleCat.{u} (A n)) ⥤
          DerivedCategory (ModuleCat.{u} (A (n + 1))) from
          sequentialRingedModuleTransitionFunctor A ρ n).obj
        ((sequentialRingedModuleDerivedEvaluation A ρ n).obj M))
  from (sequentialRingedModuleDerivedEvaluationStep A ρ n).app M

/-- The bridge tower extracted from a canonical object of
`D(naturalNumbersRingedModules (sequentialRingSystem A ρ))` by stagewise derived evaluation. -/
abbrev ofDerivedObject
    (M : DModSeq) :
    DerivedModuleTower A ρ where
  obj n := (sequentialRingedModuleDerivedEvaluation A ρ n).obj M
  -- The tower transitions are the canonical stagewise derived evaluation maps.
  stepMap n := ofDerivedObject_stepMap (A := A) (ρ := ρ) M n

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
