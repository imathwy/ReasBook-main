import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_13_1 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: finite projective modules and reduction modulo an ideal, viewed through the
  full subcategory owner `FiniteProjectiveModuleCat`;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `FiniteProjectiveModuleCat`,
  `ObjectProperty.lift`,
  `surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor`;
- best owner abstraction: the chapter/project owner for this domain is the full subcategory
  `FiniteProjectiveModuleCat R`, with functors into it built canonically from the ambient functor
  by `ObjectProperty.lift`; the reduction functor below is therefore derived API, not primitive
  hand-built category data;
- primitive data: the ambient scalar-extension functor `ModuleCat.extendScalars (Ideal.Quotient.mk
  I)` together with the theorem that it preserves `finiteProjectiveModuleProperty`;
- derived API: the induced functor on finite-projective full subcategories and the map on
  isomorphism classes.

Source/core/bridge triage:
- `source-facing`: the henselian bijectivity and lifting/isomorphism statements below;
- `core/canonical`: `finiteProjectiveModuleProperty`, `FiniteProjectiveModuleCat`, and
  `ObjectProperty.lift`;
- `bridge/view`: reduction modulo `I` as the scalar-extension functor from
  `FiniteProjectiveModuleCat R` to `FiniteProjectiveModuleCat (R ⧸ I)`. -/

-- Proof sketch: reduction modulo `I` is scalar extension along `R → R ⧸ I`, hence preserves
-- finite generation and projectivity for a finite projective module.
/-- Reduction modulo an ideal, viewed as scalar extension to `R ⧸ I`, preserves finite projective
modules. -/
theorem finiteProjectiveReduction_property (I : Ideal R) (P : FiniteProjectiveModuleCat R) :
    finiteProjectiveModuleProperty (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P.obj) := sorry

/-- The functor on finite projective module categories induced by reduction modulo `I`. -/
noncomputable abbrev finiteProjectiveReductionFunctor (I : Ideal R) :
    FiniteProjectiveModuleCat R ⥤ FiniteProjectiveModuleCat (R ⧸ I) :=
  (finiteProjectiveModuleProperty (R ⧸ I)).lift
    ((finiteProjectiveModuleProperty R).ι ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (fun P ↦ finiteProjectiveReduction_property I P)

variable (I : Ideal R) [HenselianRing R I]

-- Proof sketch: surjectivity comes from Lemmas `15.9.11` and `15.11.6`, which produce a finite
-- projective lift after an étale neighborhood and then descend it back along a henselian section.
-- Injectivity is the quotient-isomorphism criterion proved by lifting maps and applying Nakayama's
-- lemma together with the finite-projective endomorphism criterion from Algebra, Lemma `10.16.4`.
/-- Lemma 15.13.1: scalar extension along `R → R ⧸ I`, equivalently reduction `P ↦ P / IP`,
induces a bijection on isomorphism classes of finite projective modules for a henselian pair
`(R, I)`. -/
theorem finiteProjectiveReduction_isoClasses_bijective_of_henselianRing :
    Function.Bijective (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) :=
  sorry

-- Proof sketch: apply the surjective half of
-- `finiteProjectiveReduction_isoClasses_bijective_of_henselianRing` and then identify reduction
-- modulo `I` with the quotient module `P ⧸ I P`.
/-- Every finite projective `R ⧸ I`-module, viewed as an object of
`FiniteProjectiveModuleCat (R ⧸ I)`, lifts to a finite projective `R`-module over a henselian
pair. -/
theorem exists_finiteProjective_lift_of_henselianRing
    (Pbar : FiniteProjectiveModuleCat (R ⧸ I)) :
    ∃ P : FiniteProjectiveModuleCat R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := sorry

-- Proof sketch: lift an isomorphism after reduction to an `R`-linear map, use Nakayama's lemma to
-- make the lift and a reverse lift surjective, and then invoke the criterion that a surjective
-- endomorphism of a finite projective module is an isomorphism.
/-- Two finite projective `R`-modules, viewed in `FiniteProjectiveModuleCat R`, are isomorphic over
a henselian pair once their reductions modulo `I` are isomorphic. -/
theorem finiteProjective_iso_of_quotient_iso_of_henselianRing
    {P₁ P₂ : FiniteProjectiveModuleCat R}
    (h : Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂)) :
    Nonempty (P₁ ≅ P₂) := sorry

end

/-! ### Lemma_15_13_2 (from Chap15) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CommRingCat

universe u

section

variable {A : Type u} [CommRing A]

/-- The object property on `Under (CommRingCat.of A)` selecting finite étale `A`-algebras. -/
abbrev finiteEtaleAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (Under (CommRingCat.of A)) :=
  fun B : Under (CommRingCat.of A) ↦ (Hom.hom B.hom).Finite ∧ (Hom.hom B.hom).Etale

/-- The category of finite étale `A`-algebras, viewed as a full subcategory of
`Under (CommRingCat.of A)`. -/
abbrev finiteEtaleAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (finiteEtaleAlgebraProperty A).FullSubcategory

variable (I : Ideal A)

-- Proof sketch: reduction modulo `I` is base change along `A → A ⧸ I`. Finiteness of the
-- structural map descends under tensoring with the finite `A`-module `A ⧸ I`, and étaleness is
-- preserved by base change, so finite étale `A`-algebras remain finite étale after reduction.
/-- Reduction modulo `I` preserves finite étale `A`-algebras. -/
theorem quotientTensorProd_obj_mem_finiteEtaleAlgebras :
    ∀ B : finiteEtaleAlgebras A,
      finiteEtaleAlgebraProperty (A ⧸ I)
        (((CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I))).obj B.obj) := sorry

/-- The reduction functor `B ↦ B / I B`, formalized as base change along `A → A ⧸ I`, on the
category of finite étale `A`-algebras. -/
abbrev quotientFiniteEtaleAlgebraFunctor :
    finiteEtaleAlgebras A ⥤ finiteEtaleAlgebras (A ⧸ I) :=
  ObjectProperty.lift
    (finiteEtaleAlgebraProperty (A ⧸ I))
    ((finiteEtaleAlgebraProperty A).ι ⋙
      (CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I)))
    (quotientTensorProd_obj_mem_finiteEtaleAlgebras I)

variable [HenselianRing A I]

-- Proof sketch: full faithfulness is controlled by lifting idempotents and sections across the
-- henselian pair, using the finite-algebra idempotent lifting criterion from the henselian TFAE.
-- Essential surjectivity comes from lifting a finite étale `A ⧸ I`-algebra to an étale
-- `A`-algebra and then isolating the finite integral-closure summand whose reduction is the given
-- special fiber.
/-- Lemma 15.13.2: if `(A, I)` is a henselian pair, then reduction modulo `I`, formalized by the
functor `B ↦ B / I B`, induces an equivalence between the category of finite étale `A`-algebras
and the category of finite étale `A ⧸ I`-algebras. -/
theorem quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing :
    Functor.IsEquivalence (quotientFiniteEtaleAlgebraFunctor I) := sorry

end

/-! ### Lemma_15_13_3 (from Chap15) -/
universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

/-
Domain-style sampling:
- primary domain: lifting maps from smooth algebras over a quotient along the henselian étale
  section property;
- sampled owner declarations:
  `Algebra.Smooth.baseChange`,
  `exists_etale_lift_to_quotient_of_smooth`,
  `Ideal.HasEtaleLiftProperty`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the primitive lifting input is the Chapter 15 owner
  `Ideal.HasEtaleLiftProperty`; the henselian hypothesis is derived API here via the chapter TFAE,
  while smoothness is still owned canonically by `Algebra.Smooth`;
- primitive data: the ideal `I`, the smooth `R`-algebra `S`, the quotient map
  `f : S →ₐ[R] A ⧸ I`, and the étale-section owner `I.HasEtaleLiftProperty`;
- derived API: the source-facing henselian corollary obtained by extracting
  `I.HasEtaleLiftProperty` from `HenselianRing A I`.

Source/core/bridge triage:
- `source-facing`: `smooth_exists_lift_of_henselianRing`;
- `core/canonical`: `Algebra.Smooth` and `Ideal.HasEtaleLiftProperty`;
- `bridge/view`: the corollary from `HenselianRing A I` via
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
-/

-- Proof sketch: base change `S` from `R` to `A` to obtain the smooth `A`-algebra `S ⊗[R] A`.
-- Apply the étale lifting statement for smooth algebras modulo `I` to the induced map
-- `S ⊗[R] A → A ⧸ I`, then use the henselian lifting property for étale `A`-algebras to get a
-- section back to `A`. Precompose the resulting composite with `TensorProduct.includeLeft` to
-- obtain the desired lift `S →ₐ[R] A`. The core input used from the target pair is exactly the
-- chapter owner `I.HasEtaleLiftProperty`.
/-- If `S` is a smooth `R`-algebra and reduction modulo `I` on `A` has the étale section lifting
property, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
theorem smooth_exists_lift_of_hasEtaleLiftProperty (I : Ideal A) [Algebra.Smooth R S]
    (hI : I.HasEtaleLiftProperty) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := sorry

/-- Lemma 15.13.3: if `S` is a smooth `R`-algebra, `A` is an `R`-algebra, and `(A, I)` is a
henselian pair, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
theorem smooth_exists_lift_of_henselianRing (I : Ideal A) [Algebra.Smooth R S]
    [HenselianRing A I] (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  -- This is the `HenselianRing A I → I.HasEtaleLiftProperty` bridge from
  -- `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
  have hI : I.HasEtaleLiftProperty := by
    sorry
  exact smooth_exists_lift_of_hasEtaleLiftProperty I hI f

end

end Algebra

/-! ### Lemma_15_13_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CommRingCat
open Opposite
open scoped TensorProduct

noncomputable section

universe u v

section

variable (F : SequentialInverseSystem CommRingCat.{u})

/- Domain-style sampling:
- primary domain: varying-ring sequential module systems over a commutative-ring inverse system
  and their inverse limits over the limit ring;
- sampled owner declarations:
  `SeqRingMod`,
  `sequentialRingedModuleEvaluation`,
  `ringedModuleLimitTower`,
  `ringedModuleInverseLimitFunctor`;
- best owner abstraction: the chapter owner
  `SeqRingMod (fun n ↦ F.obj (op n)) (fun n ↦ (F.stepMap n).hom)` for compatible module systems
  over the varying ring system `F`;
- primitive data: an object `M` of that owner category;
- derived API: its stage modules, successor maps, inverse-limit tower over `A = lim F`, the
  inverse-limit module, and the stagewise base-change comparison maps.

Source/core/bridge triage:
- `source-facing`: Lemma `15.13.4` and its inverse-limit/base-change conclusions;
- `core/canonical`: `SeqRingMod`, `sequentialRingedModuleEvaluation`,
  `ringedModuleLimitTower`, and `ringedModuleInverseLimitFunctor`;
- `bridge/view`: the stagewise and inverse-limit base-change maps induced from the owner-derived
  evaluation and inverse-limit tower.

This refinement therefore deletes the parallel entrywise tower owner from this file. The public
surface is now organized around the intrinsic varying-ring module object, with only thin
source-facing bridge abbreviations for the comparison maps used in the statement. -/

private abbrev stageRing (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) : Type u :=
  (F.obj (op n) : Type u)

private abbrev stageMap (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    stageRing F (n + 1) →+* stageRing F n :=
  (F.stepMap n).hom

private abbrev ownerSystem : SequentialInverseSystem CommRingCat.{u} :=
  sequentialRingSystem (stageRing F) (stageMap F)

private abbrev inverseLimitRing (F : SequentialInverseSystem CommRingCat.{u}) : Type u :=
  ((limit (ownerSystem F) : CommRingCat.{u}) : Type u)

private abbrev stageModule
    (F : SequentialInverseSystem CommRingCat.{u})
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ModuleCat (stageRing F n) :=
  (sequentialRingedModuleEvaluation (stageRing F) (stageMap F) n).obj M

local instance instAlgebraInverseLimitStage (n : ℕ) :
    Algebra (inverseLimitRing F) (stageRing F n) :=
  RingHom.toAlgebra (limit.π (ownerSystem F) (op n)).hom

local instance instAlgebraStageSuccStage (n : ℕ) :
    Algebra (stageRing F (n + 1)) (stageRing F n) :=
  RingHom.toAlgebra (stageMap F n)

local instance instModuleInverseLimitRingStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (inverseLimitRing F) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    simpa [ownerSystem, sequentialRingSystem, stageModule] using
      Module.compHom (stageModule F M n) (limit.π (ownerSystem F) (op n)).hom

local instance instIsScalarTowerInverseLimitRingStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F n) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    simpa [ownerSystem, sequentialRingSystem, stageModule] using
      IsScalarTower.of_compHom (inverseLimitRing F) (stageRing F n) (stageModule F M n)

local instance instModuleStageSuccStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (stageRing F (n + 1)) (stageModule F M n) :=
  Module.compHom (stageModule F M n) (stageMap F n)

local instance instIsScalarTowerStageSuccStageModule
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (stageRing F (n + 1)) (stageRing F n) (stageModule F M n) :=
  IsScalarTower.of_compHom (stageRing F (n + 1)) (stageRing F n) (stageModule F M n)

local instance instIsScalarTowerInverseLimitRingStageSucc
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F (n + 1)) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    exact IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change
        stageMap F n ((limit.π (ownerSystem F) (op (n + 1))).hom r) • m =
          (limit.π (ownerSystem F) (op n)).hom r • m
      rw [show
          (limit.π (ownerSystem F) (op n)).hom =
            (stageMap F n).comp (limit.π (ownerSystem F) (op (n + 1))).hom from by
        ext x
        simpa using congrArg
          (fun f : limit (ownerSystem F) ⟶ (ownerSystem F).obj (op n) ↦ f x)
          ((limit.w (ownerSystem F) ((homOfLE (Nat.le_succ n)).op)).symm)]
      rfl

local instance instModuleInverseLimitRing
    (M : SeqRingMod (stageRing F) (stageMap F)) :
    Module (inverseLimitRing F)
      ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M) := by
  simpa [inverseLimitRing] using
    ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M).isModule

private abbrev restrictedStageModule
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ModuleCat (inverseLimitRing F) :=
  (ModuleCat.restrictScalars (limit.π (ownerSystem F) (op n)).hom).obj (stageModule F M n)

local instance instModuleRestrictedStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (stageRing F n) (restrictedStageModule F M n) :=
  (stageModule F M n).isModule

local instance instIsScalarTowerInverseLimitRingRestrictedStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F n) (restrictedStageModule F M n) := by
  change IsScalarTower (inverseLimitRing F) (stageRing F n) (stageModule F M n)
  infer_instance

private abbrev stageProjection
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M) ⟶
      restrictedStageModule F M n :=
  by
    simpa [restrictedStageModule, ringedModuleInverseLimitFunctor, stageModule] using
      limit.π (ringedModuleLimitTower (stageRing F) (stageMap F) M) (op n)

private abbrev stageStep
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    stageModule F M (n + 1) →ₗ[stageRing F (n + 1)] stageModule F M n :=
  ((sequentialRingedModuleEvaluationStep (stageRing F) (stageMap F) n).app M).hom

/-- The base-change comparison map `A_n ⊗[A_{n + 1}] M_{n + 1} → M_n` induced by the successor
transition map in the owner object `M ∈ SeqRingMod`. -/
abbrev stageBaseChangeComparison
    (M : SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom)) (n : ℕ) :
    ((F.obj (op n) : Type u) ⊗[(F.obj (op (n + 1)) : Type u)]
        ((sequentialRingedModuleEvaluation
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom) (n + 1)).obj M)) →ₗ[(F.obj (op n) : Type u)]
      ((sequentialRingedModuleEvaluation
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom) n).obj M) :=
  (stageStep F M n).liftBaseChange (stageRing F n)

/-- The base-change comparison map `A_n ⊗[A] M → M_n` from the inverse limit module
`M = lim M_n` to the `n`th stage, where `A = lim A_n`. -/
abbrev inverseLimitBaseChangeComparison
    (M : SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom)) (n : ℕ) :
    ((F.obj (op n) : Type u) ⊗[
        ((limit
          (sequentialRingSystem
            (fun n ↦ (F.obj (op n) : Type u))
            (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)]
        ((ringedModuleInverseLimitFunctor
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)).obj M)) →ₗ[(F.obj (op n) : Type u)]
      ((sequentialRingedModuleEvaluation
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom) n).obj M) :=
  by
    simpa [restrictedStageModule, stageModule] using
      (stageProjection F M n).hom.liftBaseChange (stageRing F n)

section

variable (M :
  SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom))
variable [∀ n : ℕ,
  Module.Finite (F.obj (op n))
    ((sequentialRingedModuleEvaluation
      (fun n ↦ (F.obj (op n) : Type u))
      (fun n ↦ (F.stepMap n).hom) n).obj M)]
variable [∀ n : ℕ,
  Module.Flat (F.obj (op (n + 1)))
    ((sequentialRingedModuleEvaluation
      (fun n ↦ (F.obj (op n) : Type u))
      (fun n ↦ (F.stepMap n).hom) (n + 1)).obj M)]
variable [Module.Projective (F.obj (op 0))
  ((sequentialRingedModuleEvaluation
    (fun n ↦ (F.obj (op n) : Type u))
    (fun n ↦ (F.stepMap n).hom) 0).obj M)]

local instance instFlatStage (n : ℕ) : Module.Flat (stageRing F n) (stageModule F M n) := by
  cases n with
  | zero =>
      exact Module.Flat.of_projective
  | succ n =>
      simpa [Nat.succ_eq_add_one] using (inferInstance :
        Module.Flat (stageRing F (n + 1)) (stageModule F M (n + 1)))

-- Proof sketch: apply Lemma `15.11.3` to the inverse system of rings to see that the pair
-- `(A, ker(A → A₀))` is henselian. Then use Lemma `15.13.1` to lift the finite projective
-- `A₀`-module `M₀` to a finite projective `A`-module, and compare its reductions to the later
-- stages by Lemmas `15.3.4` and `15.3.5`.
/-- Lemma 15.13.4 (1): for a sequential inverse system of rings with surjective, locally
nilpotent transition kernels and compatible finite modules whose positive stages are flat, whose
initial stage is projective, and whose successive base changes are isomorphic, the inverse limit
module `M = lim M_n` is finite over the inverse limit ring `A = lim A_n`. -/
theorem inverseLimitModule_finite_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    Module.Finite
      ((limit
        (sequentialRingSystem
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)
      ((ringedModuleInverseLimitFunctor
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom)).obj M) := sorry

-- Proof sketch: the same lifting argument as in part `(1)` produces a finite projective
-- `A`-module lifting `M₀`; the comparison with each stage `M_n` is an isomorphism by Lemmas
-- `15.3.4` and `15.3.5`, so the canonical inverse limit module is projective.
/-- Lemma 15.13.4 (2): under the same hypotheses, the inverse limit module `M = lim M_n` is
projective over the inverse limit ring `A = lim A_n`. -/
theorem inverseLimitModule_projective_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    Module.Projective
      ((limit
        (sequentialRingSystem
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)
      ((ringedModuleInverseLimitFunctor
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom)).obj M) := sorry

-- Proof sketch: after lifting `M₀` to a finite projective `A`-module, compare that lift with the
-- inverse limit module. The successive base-change isomorphisms `A_n ⊗[A_{n+1}] M_{n+1} ≃ M_n`
-- and Lemma `15.3.5` identify the base change of the inverse limit module with each stage `M_n`.
/-- Lemma 15.13.4 (3): for every stage `n`, base change of the inverse limit module `M = lim M_n`
from `A = lim A_n` to `A_n` recovers the stage module `M_n`. -/
theorem inverseLimitBaseChangeComparison_bijective_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n))
    (n : ℕ) :
    Function.Bijective (inverseLimitBaseChangeComparison F M n) := sorry

end

end
