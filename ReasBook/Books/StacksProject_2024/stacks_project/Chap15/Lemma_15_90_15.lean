import Mathlib
import StacksProject_2024.Chap15.«15_6_3_1»
import StacksProject_2024.Chap15.Lemma_15_90_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable (S : Type u) [CommRing S] [Algebra R S]
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable {t : ℕ} (f : Fin t → R)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "Away" => LocalizedModule.Away
local notation "SBase" => S ⊗[R] R'
local notation "fBase" => fun i ↦ algebraMap R R' (f i)
local notation "GlueBase" => Glue SBase fBase

/-
Domain-style sampling for 15.90.15:
- primary domain: formal-glueing base change for module categories;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0`,
  `moduleCatBaseChangeSquare`,
  `CategoryTheory.conjugateEquiv`;
- best owner abstraction:
  the chapter owner should expose the glueing-side base-change functor itself, together with the
  fixed-vertical `Can` and `H⁰` comparison isomorphisms, just as nearby base-change files expose
  named functors and named comparison squares rather than a bare existential package;
- primitive data:
  the glueing-side base-change functor and the two comparison isomorphisms for `Can` and `H⁰`;
- derived API:
  no extra existential wrapper is needed once those named owners are exposed directly.

Source/core/bridge triage:
- `source-facing`: `formalGlueingBaseChangeFunctor`;
- `core/canonical`: functor composition and natural isomorphism squares, with
  `CatCommSqOver` remaining the generic internal owner;
- `bridge/view`: none beyond the named comparison isomorphisms already exposed below.
-/

-- Proof sketch: build the glueing-side base-change functor by transporting the formal-glueing
-- datum along `R → R'`, and then compare the two composites out of `ModuleCat R` by the canonical
-- extension-of-scalars base-change identifications on the base module and on each localized piece.
-- The `H⁰` comparison is the corresponding right-adjoint mate with respect to the adjunctions of
-- Lemma `15.90.11`.
private noncomputable abbrev formalGlueingAwayBaseAlg (i : Fin t) :
    Localization.Away (f i) →ₐ[R] Localization.Away (fBase i) :=
  Localization.awayMapₐ (Algebra.ofId R R') (f i)

private noncomputable abbrev formalGlueingAwayBaseMap (i : Fin t) :
    Localization.Away (f i) →+* Localization.Away (fBase i) :=
  (formalGlueingAwayBaseAlg R' f i).toRingHom

private instance localizedAwayId_isLocalizedModule
    (a : R) (M : Type v) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    IsLocalizedModule.Away a (LinearMap.id : M →ₗ[R] M) := by
  simpa using isLocalizedModule_id (Submonoid.powers a) M (Localization.Away a)

private noncomputable def formalGlueingBaseChangeBase (X : Glue S f) :
    ModuleCat.{max u v} SBase :=
  (ModuleCat.extendScalars (algebraMap S SBase)).obj X.base

private noncomputable def formalGlueingBaseChangeLocal (X : Glue S f) (i : Fin t) :
    ModuleCat.{max u v} (Localization.Away (fBase i)) :=
  (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).obj (X.glue.localModule i)

private abbrev formalGlueingBaseChangeLocalCarrier (X : Glue S f) (i : Fin t) :=
  ↑(formalGlueingBaseChangeLocal S R' f X i)

private theorem formalGlueingAwayBaseSquare_comm (i : Fin t) :
    (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
      (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') := by
  -- Both composites send `x` to the standard localization class of `algebraMap R R' x`.
  let hyMap :
      Submonoid.powers (f i) ≤
        Submonoid.comap (Algebra.ofId R R').toRingHom (Submonoid.powers (fBase i)) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  have hmap (x : R) :
      (formalGlueingAwayBaseAlg R' f i) (algebraMap R (Localization.Away (f i)) x) =
        algebraMap R' (Localization.Away (fBase i)) (algebraMap R R' x) := by
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (f i)) (Localization.Away (f i)) x]
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (fBase i)) (Localization.Away (fBase i))
      (algebraMap R R' x)]
    simpa [formalGlueingAwayBaseAlg, Localization.awayMapₐ, hyMap] using
      (IsLocalization.map_mk' (Q := Localization.Away (fBase i)) hyMap x
        (1 : Submonoid.powers (f i)))
  ext x
  simpa [formalGlueingAwayBaseMap] using hmap x

private instance formalGlueingAwayBaseAlgebra (i : Fin t) :
    Algebra (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  (formalGlueingAwayBaseAlg R' f i).toAlgebra

private instance formalGlueingAwayBaseTower (i : Fin t) :
    IsScalarTower R (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  IsScalarTower.of_algebraMap_eq' (formalGlueingAwayBaseSquare_comm R' f i).symm

private instance formalGlueingBaseChangeTensorModule
    (X : Glue S f) (i : Fin t) :
    Module R ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase) :=
  Module.restrictScalars R R' ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase)

private instance formalGlueingBaseChangeTensorAwayModule
    (X : Glue S f) (i : Fin t) :
    Module (Localization.Away (f i))
      ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase) :=
  Module.restrictScalars
    (Localization.Away (f i))
    (Localization.Away (fBase i))
    ((formalGlueingBaseChangeLocal S R' f X i) ⊗[R'] SBase)

private noncomputable def formalGlueingBaseChangeGluedModule (X : Glue S f) :
    ModuleCat.{max u v} R' :=
  (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.glue.gluedModule)

private noncomputable def formalGlueingBaseChangeCanonicalObj (X : Glue S f) :
    Glue R' fBase :=
  (formalGlueingCan R' fBase).obj (formalGlueingBaseChangeGluedModule S R' f X)

private noncomputable def formalGlueingBaseChangeCanonicalLocalIsoApp
    (X : Glue S f) (i : Fin t) :
    (formalGlueingBaseChangeCanonicalObj S R' f X).glue.localModule i ≅
      formalGlueingBaseChangeLocal S R' f X i :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i) (formalGlueingBaseChangeGluedModule S R' f X)).symm ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app (ModuleCat.of R X.glue.gluedModule)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      ((awayExtendScalarsIso (f i) (ModuleCat.of R X.glue.gluedModule)) ≪≫
        (X.glue.localizedProjectionLinearEquiv i).toModuleIso)

private noncomputable def formalGlueingBaseChangeCanonicalOverlapIsoApp
    (X : Glue S f) (k : Fin t) (i : Fin t) (j : Fin t) :
    ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) ((formalGlueingBaseChangeCanonicalObj S R' f X).glue.localModule k)) ≅
      ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X k)) :=
  (LinearEquiv.extendScalarsOfIsLocalization
      (Submonoid.powers (fBase i * fBase j))
      (Localization.Away (fBase i * fBase j))
      (awayLocalizeLinearEquiv (fBase i * fBase j)
        ((formalGlueingBaseChangeCanonicalLocalIsoApp S R' f X k).toLinearEquiv.restrictScalars R'))).toModuleIso

private noncomputable def formalGlueingBaseChangeLocalOverlapIso
    (X : Glue S f) (i j : Fin t) :
    ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X i)) ≅
      ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueingBaseChangeLocal S R' f X j)) :=
  (formalGlueingBaseChangeCanonicalOverlapIsoApp S R' f X i i j).symm ≪≫
    (formalGlueingBaseChangeCanonicalObj S R' f X).glue.overlapIso i j ≪≫
    formalGlueingBaseChangeCanonicalOverlapIsoApp S R' f X j i j

private theorem formalGlueingBaseChangeLocalCocycle
    (X : Glue S f) :
    AwayModuleGlueingCocycleCondition fBase
      (formalGlueingBaseChangeLocal S R' f X)
      (formalGlueingBaseChangeLocalOverlapIso S R' f X) := by
  sorry

private noncomputable def formalGlueingBaseChangeGlue (X : Glue S f) :
    AwayModuleGlueing fBase where
  localModule := formalGlueingBaseChangeLocal S R' f X
  overlapIso := formalGlueingBaseChangeLocalOverlapIso S R' f X
  cocycle := formalGlueingBaseChangeLocalCocycle S R' f X

private noncomputable def formalGlueingBaseChangeBaseRestrictIsoApp
    (X : Glue S f) :
    ModuleCat.of R' ↑(formalGlueingBaseChangeBase S R' f X) ≅
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.base) :=
  let eTensor :
      ModuleCat.of R' ↑(formalGlueingBaseChangeBase S R' f X) ≅
        ModuleCat.of R' (SBase ⊗[S] X.base) :=
    ((moduleCatExtendScalarsTensorIso S SBase X.base).toLinearEquiv.restrictScalars R').toModuleIso
  let ePushout :
      ModuleCat.of R' (SBase ⊗[S] X.base) ≅
        ModuleCat.of R' (R' ⊗[R] X.base) :=
    (Algebra.IsPushout.cancelBaseChange R R' S SBase X.base).toModuleIso
  let eBase :
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R X.base) ≅
        ModuleCat.of R' (R' ⊗[R] X.base) :=
    moduleCatExtendScalarsTensorIso R R' (ModuleCat.of R X.base)
  eTensor ≪≫ ePushout ≪≫ eBase.symm

private noncomputable def formalGlueingBaseChangeBaseLocalIsoApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
        (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ≅
      (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).obj
        (ModuleCat.of (Localization.Away (f i)) (Away (f i) X.base)) :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i)
    (ModuleCat.of R' (formalGlueingBaseChangeBase S R' f X))).symm ≪≫
    (ModuleCat.extendScalars (algebraMap R' (Localization.Away (fBase i)))).mapIso
      (formalGlueingBaseChangeBaseRestrictIsoApp S R' f X) ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app (ModuleCat.of R X.base)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      (awayExtendScalarsIso (f i) (ModuleCat.of R X.base))

private noncomputable def formalGlueingBaseChangeLocalUnit
    (X : Glue S f) (i : Fin t) :
    X.glue.localModule i →ₗ[Localization.Away (f i)]
      (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
        (formalGlueingBaseChangeLocal S R' f X i) :=
  ((ModuleCat.extendRestrictScalarsAdj (formalGlueingAwayBaseMap R' f i)).unit.app
    (X.glue.localModule i)).hom

private noncomputable def formalGlueingBaseChangeScalarLinearMap :
    S →ₗ[R] SBase :=
  (TensorProduct.mk R S R').flip 1

/-- Helper for Lemma 15.90.15: the base-change tensor generator `s ↦ s ⊗ 1` is additive. -/
private theorem formalGlueingBaseChangeScalarLinearMap_map_add
    (s₁ s₂ : S) :
    TensorProduct.tmul R (s₁ + s₂) (1 : R') =
      TensorProduct.tmul R s₁ (1 : R') + TensorProduct.tmul R s₂ (1 : R') := by
  -- This is the standard additivity of the left tensor factor in `S ⊗[R] R'`.
  simpa using (TensorProduct.add_tmul s₁ s₂ (1 : R'))

/-- Helper for Lemma 15.90.15: the generator `s ⊗ 1` carries an `R`-scalar across base change as
the induced `R`-scalar action on the tensor product. -/
private theorem formalGlueingBaseChangeScalarLinearMap_map_smul
    (a : R) (s : S) :
    TensorProduct.tmul R (a • s) (1 : R') =
      a • TensorProduct.tmul R s (1 : R') := by
  -- Move the `R`-scalar from the left tensor factor to the right one, then read it as the
  -- induced `R`-scalar action on the tensor product.
  calc
    TensorProduct.tmul R (a • s) (1 : R') =
      TensorProduct.tmul R s (a • (1 : R')) := by
        simpa using (TensorProduct.smul_tmul (R := R) (R' := R) a s (1 : R'))
    _ = a • TensorProduct.tmul R s (1 : R') := by
        simpa using (TensorProduct.tmul_smul (R := R) (R' := R) a s (1 : R'))

/-- Helper for Lemma 15.90.15: with a fixed local tensor factor, the source-side scalar transport
on `s ⊗ 1` can be rewritten before handling the outer tensor-product scalar action. -/
private theorem formalGlueingBaseChangeTensorInsertion_right_smul
    (X : Glue S f) (i : Fin t)
    (u : formalGlueingBaseChangeLocalCarrier S R' f X i)
    (a : R) (s : S) :
    TensorProduct.tmul R' u (TensorProduct.tmul R (a • s) (1 : R')) =
      TensorProduct.tmul R' u (a • TensorProduct.tmul R s (1 : R')) := by
  -- This isolates the right-factor rewrite coming from the base-change generator `s ↦ s ⊗ 1`.
  simpa using
    congrArg (TensorProduct.tmul R' u)
      (formalGlueingBaseChangeScalarLinearMap_map_smul (R := R) (S := S) (R' := R') a s)

/-- Helper for Lemma 15.90.15: on the exact owner object for the local carrier, an
`Away(f_i)`-scalar becomes its image under `formalGlueingAwayBaseMap`. -/
private theorem formalGlueingBaseChangeLocalCarrier_restrictScalars_smul
    (X : Glue S f) (i : Fin t) (r : Localization.Away (f i))
    (u : formalGlueingBaseChangeLocal S R' f X i) :
    (r • u :
      ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
        (formalGlueingBaseChangeLocal S R' f X i))) =
      (formalGlueingAwayBaseMap R' f i r) • u := by
  -- Route correction: record the owner-side scalar transport directly, without forcing Lean to
  -- discover the outer `R`-tower before the actual away-map rewrite.
  simpa using
    (ModuleCat.restrictScalars.smul_def' (formalGlueingAwayBaseMap R' f i) r u)

/-- Helper for Lemma 15.90.15: for the restricted local carrier, tensoring with a fixed
base-change scalar is additive in the first tensor factor. -/
private theorem formalGlueingBaseChangeRestrictedLocal_add_tmul
    (X : Glue S f) (i : Fin t)
    (u v : formalGlueingBaseChangeLocalCarrier S R' f X i) (z : SBase) :
    TensorProduct.tmul R' (u + v) z =
      TensorProduct.tmul R' u z + TensorProduct.tmul R' v z := by
  -- View `u ↦ u ⊗ z` as the linear map obtained from the universal tensor-product bilinear map.
  simpa using
    (LinearMap.map_add
      (((TensorProduct.mk R'
          (formalGlueingBaseChangeLocalCarrier S R' f X i) SBase).flip z))
      u v)

/-- Helper for Lemma 15.90.15: for the restricted local carrier, an `R'`-scalar on the first
tensor factor becomes the induced scalar on the tensor product. -/
private theorem formalGlueingBaseChangeRestrictedLocal_smul_tmul
    (X : Glue S f) (i : Fin t)
    (a : R') (u : formalGlueingBaseChangeLocalCarrier S R' f X i) (z : SBase) :
    TensorProduct.tmul R' (a • u) z =
      a • TensorProduct.tmul R' u z := by
  -- The same tensor-product universal map is `R'`-linear in its first argument.
  simpa using
    (LinearMap.map_smul
      (((TensorProduct.mk R'
          (formalGlueingBaseChangeLocalCarrier S R' f X i) SBase).flip z))
      a u)

/-- Helper for Lemma 15.90.15: on the exact restricted tensor target, an owner-side
`Away(f_i)`-scalar acts by scaling the first tensor factor through `formalGlueingAwayBaseMap`. -/
private theorem formalGlueingBaseChangeTensorTarget_owner_away_smul_tmul
    (X : Glue S f) (i : Fin t) (r : Localization.Away (f i))
    (u : formalGlueingBaseChangeLocalCarrier S R' f X i) (z : SBase) :
    (r • TensorProduct.tmul R' u z :
      ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
        (ModuleCat.of (Localization.Away (fBase i))
          (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) =
      TensorProduct.tmul R' ((formalGlueingAwayBaseMap R' f i r) • u) z := by
  -- Route correction: rewrite the owner action on the exact restricted tensor target before
  -- moving the scalar across the pure tensor.
  change
    (((formalGlueingAwayBaseMap R' f i) r) • TensorProduct.tmul R' u z :
      formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) =
      TensorProduct.tmul R' (((formalGlueingAwayBaseMap R' f i) r) • u) z
  simpa using
    (TensorProduct.smul_tmul'
      (R := R')
      ((formalGlueingAwayBaseMap R' f i) r) u z)

/-- Helper for Lemma 15.90.15: after specializing the owner action along `a : R`, the induced
`R`-scalar on the restricted tensor target can be read on the right tensor factor. -/
private theorem formalGlueingBaseChangeTensorTarget_algebraMap_right_smul
    (X : Glue S f) (i : Fin t) (a : R)
    (u : formalGlueingBaseChangeLocalCarrier S R' f X i) (z : SBase) :
    TensorProduct.tmul R' u ((algebraMap R R' a) • z) =
      (a • TensorProduct.tmul R' u z :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
  -- First move the native `R'`-scalar to the tensor product, then identify it with the owner
  -- action coming from `R → Localization.Away (f_i)`.
  have hsq :
      formalGlueingAwayBaseMap R' f i (algebraMap R (Localization.Away (f i)) a) =
        algebraMap R' (Localization.Away (fBase i)) (algebraMap R R' a) := by
    exact congrArg (fun g : R →+* Localization.Away (fBase i) ↦ g a)
      (formalGlueingAwayBaseSquare_comm R' f i)
  calc
    TensorProduct.tmul R' u ((algebraMap R R' a) • z) =
        (algebraMap R R' a) • TensorProduct.tmul R' u z := by
          simpa using
            (TensorProduct.tmul_smul
              (R := R')
              (R' := R')
              (algebraMap R R' a) u z)
    _ = TensorProduct.tmul R' ((algebraMap R R' a) • u) z := by
          symm
          simpa using
            (formalGlueingBaseChangeRestrictedLocal_smul_tmul
              (S := S) (R' := R') (f := f) X i (algebraMap R R' a) u z)
    _ = TensorProduct.tmul R'
          ((algebraMap R' (Localization.Away (fBase i)) (algebraMap R R' a)) • u) z := by
          rfl
    _ = TensorProduct.tmul R' ((formalGlueingAwayBaseMap R' f i
          (algebraMap R (Localization.Away (f i)) a)) • u) z := by
          rw [← hsq]
    _ = ((algebraMap R (Localization.Away (f i)) a) • TensorProduct.tmul R' u z :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
          symm
          rw [formalGlueingBaseChangeTensorTarget_owner_away_smul_tmul
            (S := S) (R' := R') (f := f) X i (algebraMap R (Localization.Away (f i)) a) u z]
    _ = (a • TensorProduct.tmul R' u z :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
          rfl

/-- Helper for Lemma 15.90.15: fixing a local section gives the mixed-scalar tensor insertion
`s ↦ m ⊗ (s ⊗ 1)` as an `R`-linear map into the restricted local tensor product. -/
private noncomputable def formalGlueingBaseChangeTensorInsertion
    (X : Glue S f) (i : Fin t) (m : X.glue.localModule i) :
    S →ₗ[R]
      (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj <|
        ModuleCat.of (Localization.Away (fBase i))
          (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  { toFun := fun s ↦
      TensorProduct.tmul
        R'
        (((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R m) :
          formalGlueingBaseChangeLocalCarrier S R' f X i)
        (TensorProduct.tmul R s (1 : R'))
    map_add' := by
      intro s₁ s₂
      let u : formalGlueingBaseChangeLocalCarrier S R' f X i :=
        (((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) m)
      -- The second tensor factor is additive because `s ↦ s ⊗ 1` is additive and `u ⊗ -`
      -- preserves addition.
      change TensorProduct.tmul R' u (TensorProduct.tmul R (s₁ + s₂) (1 : R')) = _
      calc
        TensorProduct.tmul R' u (TensorProduct.tmul R (s₁ + s₂) (1 : R')) =
            TensorProduct.tmul R' u
              (TensorProduct.tmul R s₁ (1 : R') + TensorProduct.tmul R s₂ (1 : R')) := by
                congr 1
                simpa using (TensorProduct.add_tmul s₁ s₂ (1 : R'))
        _ = TensorProduct.tmul R' u (TensorProduct.tmul R s₁ (1 : R')) +
              TensorProduct.tmul R' u (TensorProduct.tmul R s₂ (1 : R')) := by
                simpa using
                  (TensorProduct.tmul_add u
                    (TensorProduct.tmul R s₁ (1 : R'))
                    (TensorProduct.tmul R s₂ (1 : R')))
    map_smul' := by
      intro a s
      let u : formalGlueingBaseChangeLocalCarrier S R' f X i :=
        (((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) m)
      -- Rewrite the source-side scalar in the right tensor factor and then read it as the
      -- induced `R`-scalar on the exact restricted tensor target.
      change
        TensorProduct.tmul R' u (TensorProduct.tmul R (a • s) (1 : R')) =
          (a • TensorProduct.tmul R' u (TensorProduct.tmul R s (1 : R')) :
            ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
              (ModuleCat.of (Localization.Away (fBase i))
                (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase))))
      rw [formalGlueingBaseChangeTensorInsertion_right_smul
        (S := S) (R' := R') (f := f) X i u a s]
      simpa using
        (formalGlueingBaseChangeTensorTarget_algebraMap_right_smul
          (S := S) (R' := R') (f := f) X i a u (TensorProduct.tmul R s (1 : R'))) }
private noncomputable def formalGlueingBaseChangeComparisonAux₂
    (X : Glue S f) (i : Fin t) :
    X.glue.localModule i →ₗ[R]
      S →ₗ[R]
        (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj <|
          ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  { toFun := fun m ↦
      formalGlueingBaseChangeTensorInsertion S R' f X i m
    map_add' := by
      intro m₁ m₂
      ext s
      -- Route correction: the named insertion map turns outer `m`-linearity into ordinary
      -- additivity of the local unit map followed by additivity in the first tensor factor.
      change formalGlueingBaseChangeTensorInsertion S R' f X i (m₁ + m₂) s =
        formalGlueingBaseChangeTensorInsertion S R' f X i m₁ s +
          formalGlueingBaseChangeTensorInsertion S R' f X i m₂ s
      simp only [formalGlueingBaseChangeTensorInsertion, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.map_add]
      simpa using
        (formalGlueingBaseChangeRestrictedLocal_add_tmul
          (S := S) (R' := R') (f := f) X i
          ((((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) m₁) :
            formalGlueingBaseChangeLocalCarrier S R' f X i)
          ((((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) m₂) :
            formalGlueingBaseChangeLocalCarrier S R' f X i)
          (TensorProduct.tmul R s (1 : R')))
    map_smul' := by
      intro a m
      ext s
      let u : formalGlueingBaseChangeLocalCarrier S R' f X i :=
        (((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) m)
      let z : SBase := TensorProduct.tmul R s (1 : R')
      have hsq :
          formalGlueingAwayBaseMap R' f i (algebraMap R (Localization.Away (f i)) a) =
            algebraMap R' (Localization.Away (fBase i)) (algebraMap R R' a) := by
        exact congrArg (fun g : R →+* Localization.Away (fBase i) ↦ g a)
          (formalGlueingAwayBaseSquare_comm R' f i)
      have hu :
          ((((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) (a • m)) :
            formalGlueingBaseChangeLocalCarrier S R' f X i) =
            (algebraMap R R' a) • u := by
        -- Rewrite the source-side `R`-scalar through the restricted away action on the local
        -- carrier, then identify it with the native `R'`-action.
        calc
          ((((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) (a • m)) :
              formalGlueingBaseChangeLocalCarrier S R' f X i) =
              ((((algebraMap R (Localization.Away (f i)) a) • u :
                ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
                  (formalGlueingBaseChangeLocal S R' f X i)))) :
                formalGlueingBaseChangeLocalCarrier S R' f X i) := by
                  simp only [u, LinearMap.map_smul]
          _ = ((formalGlueingAwayBaseMap R' f i
                (algebraMap R (Localization.Away (f i)) a)) • u) := by
                simpa using
                  (formalGlueingBaseChangeLocalCarrier_restrictScalars_smul
                    (S := S) (R' := R') (f := f) X i
                    (algebraMap R (Localization.Away (f i)) a) u)
          _ = (algebraMap R' (Localization.Away (fBase i)) (algebraMap R R' a)) • u := by
                rw [hsq]
          _ = (algebraMap R R' a) • u := by
                rfl
      -- After rewriting the first tensor factor, the remaining scalar law is the native
      -- `R'`-linearity of `u ↦ u ⊗ z`.
      change
        TensorProduct.tmul R'
            ((((formalGlueingBaseChangeLocalUnit S R' f X i).restrictScalars R) (a • m)) :
              formalGlueingBaseChangeLocalCarrier S R' f X i)
            z =
          (a • TensorProduct.tmul R' u z :
            ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
              (ModuleCat.of (Localization.Away (fBase i))
                (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase))))
      rw [hu]
      calc
        TensorProduct.tmul R' ((algebraMap R R' a) • u) z =
            (algebraMap R R' a) • TensorProduct.tmul R' u z := by
              simpa [u, z] using
                (formalGlueingBaseChangeRestrictedLocal_smul_tmul
                  (S := S) (R' := R') (f := f) X i (algebraMap R R' a) u z)
        _ = (a • TensorProduct.tmul R' u z :
            ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
              (ModuleCat.of (Localization.Away (fBase i))
                (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
              rfl }

/-- Helper for Lemma 15.90.15: the insertion map carries the owner `Away(f_i)`-scalar on the local
input to the exact restricted tensor target. -/
private theorem formalGlueingBaseChangeTensorInsertion_away_smul
    (X : Glue S f) (i : Fin t) (r : Localization.Away (f i))
    (m : X.glue.localModule i) (s : S) :
    formalGlueingBaseChangeTensorInsertion S R' f X i (r • m) s =
      (r • formalGlueingBaseChangeTensorInsertion S R' f X i m s :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
  let u : formalGlueingBaseChangeLocalCarrier S R' f X i :=
    ((formalGlueingBaseChangeLocalUnit S R' f X i) m :
      formalGlueingBaseChangeLocalCarrier S R' f X i)
  let z : SBase := TensorProduct.tmul R s (1 : R')
  have hu :
      ((formalGlueingBaseChangeLocalUnit S R' f X i) (r • m) :
        formalGlueingBaseChangeLocalCarrier S R' f X i) =
        (formalGlueingAwayBaseMap R' f i r) • u := by
    -- Move the owner-side away scalar through the local unit map before comparing tensor factors.
    calc
      ((formalGlueingBaseChangeLocalUnit S R' f X i) (r • m) :
          formalGlueingBaseChangeLocalCarrier S R' f X i) =
          ((((r • (formalGlueingBaseChangeLocalUnit S R' f X i m) :
              ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
                (formalGlueingBaseChangeLocal S R' f X i)))) :
            ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
              (formalGlueingBaseChangeLocal S R' f X i))) :
            formalGlueingBaseChangeLocalCarrier S R' f X i) := by
              simp
      _ = (formalGlueingAwayBaseMap R' f i r) • u := by
            simpa [u] using
              (formalGlueingBaseChangeLocalCarrier_restrictScalars_smul
                (S := S) (R' := R') (f := f) X i r u)
  -- Route correction: isolate the away-scalar transport at the insertion level before lifting.
  change
    TensorProduct.tmul R'
        ((formalGlueingBaseChangeLocalUnit S R' f X i) (r • m) :
          formalGlueingBaseChangeLocalCarrier S R' f X i)
        z =
      (r • TensorProduct.tmul R'
          (((formalGlueingBaseChangeLocalUnit S R' f X i) m :
            formalGlueingBaseChangeLocalCarrier S R' f X i)) z :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase))))
  rw [hu]
  simpa [u, z] using
    (formalGlueingBaseChangeTensorTarget_owner_away_smul_tmul
      (S := S) (R' := R') (f := f) X i r u z).symm

/-- Helper for Lemma 15.90.15: on a pure tensor, the underlying tensor lift for the comparison map
respects the owner `Away(f_i)`-scalar. -/
private theorem formalGlueingBaseChangeComparisonAux₁_tmul_owner_smul
    (X : Glue S f) (i : Fin t) (r : Localization.Away (f i))
    (m : X.glue.localModule i) (s : S) :
    (TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i))
        (r • TensorProduct.tmul R m s) =
      (r • (TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i))
          (TensorProduct.tmul R m s) :
        ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
          (ModuleCat.of (Localization.Away (fBase i))
            (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
  -- Normalize the source-side action to the first tensor factor, then evaluate the tensor lift on
  -- a pure tensor and appeal to the insertion-level scalar formula.
  rw [TensorProduct.smul_tmul']
  simp only [TensorProduct.lift.tmul, formalGlueingBaseChangeComparisonAux₂]
  exact
    formalGlueingBaseChangeTensorInsertion_away_smul
      (S := S) (R' := R') (f := f) X i r m s

/-- Helper for Lemma 15.90.15: the tensor lift defining the local comparison map is
`Away(f_i)`-linear after reducing to pure tensors. -/
private theorem formalGlueingBaseChangeComparisonAux₁_map_smul
    (X : Glue S f) (i : Fin t) :
    ∀ (r : Localization.Away (f i)) (z : X.glue.localModule i ⊗[R] S),
      (TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i)) (r • z) =
        (r • (TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i)) z :
          ↑((ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj
            (ModuleCat.of (Localization.Away (fBase i))
              (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase)))) := by
  intro r z
  -- Reduce the scalar law to pure tensors, where the previous helper gives the exact formula.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro m s
    simpa using
      (formalGlueingBaseChangeComparisonAux₁_tmul_owner_smul
        (S := S) (R' := R') (f := f) X i r m s)
  · intro z₁ z₂ hz₁ hz₂
    simpa [smul_add, map_add, hz₁, hz₂]

private noncomputable def formalGlueingBaseChangeComparisonAux₁
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (f i))
      (X.glue.localModule i ⊗[R] S) ⟶
      (ModuleCat.restrictScalars (formalGlueingAwayBaseMap R' f i)).obj <|
        ModuleCat.of (Localization.Away (fBase i))
          (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  ModuleCat.ofHom
    { toFun := TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i)
      map_add' := (TensorProduct.lift (formalGlueingBaseChangeComparisonAux₂ S R' f X i)).map_add
      map_smul' := formalGlueingBaseChangeComparisonAux₁_map_smul S R' f X i }

private noncomputable def formalGlueingBaseChangeComparisonHomApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
      (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ⟶
      ModuleCat.of (Localization.Away (fBase i))
        (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase) :=
  (formalGlueingBaseChangeBaseLocalIsoApp S R' f X i).hom ≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (X.comparisonIso i).hom ≫
    ((ModuleCat.extendRestrictScalarsAdj (formalGlueingAwayBaseMap R' f i)).homEquiv
      (ModuleCat.of (Localization.Away (f i)) (X.glue.localModule i ⊗[R] S))
      (ModuleCat.of (Localization.Away (fBase i))
        (formalGlueingBaseChangeLocal S R' f X i ⊗[R'] SBase))
      ).symm (formalGlueingBaseChangeComparisonAux₁ S R' f X i)

private theorem formalGlueingBaseChangeComparisonHomApp_isIso
    (X : Glue S f) (i : Fin t) :
    IsIso (formalGlueingBaseChangeComparisonHomApp S R' f X i) := by
  sorry

private noncomputable def formalGlueingBaseChangeComparisonIsoApp
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
        (Away (fBase i) (formalGlueingBaseChangeBase S R' f X)) ≅
      ModuleCat.of (Localization.Away (fBase i))
        ((formalGlueingBaseChangeGlue S R' f X).localModule i ⊗[R'] SBase) := by
  exact
    @CategoryTheory.asIso
      _ _ _ _
      (formalGlueingBaseChangeComparisonHomApp S R' f X i)
      (formalGlueingBaseChangeComparisonHomApp_isIso S R' f X i)

private theorem formalGlueingBaseChangeComparisonOverlap
    (X : Glue S f) (i j : Fin t) :
    CommSq
      (formalGlueingComparisonOnOverlap fBase
        (formalGlueingBaseChangeBase S R' f X)
        (formalGlueingBaseChangeGlue S R' f X)
        (formalGlueingBaseChangeComparisonIsoApp S R' f X) i j)
      (𝟙 _)
      (formalGlueingTensorOverlapMap fBase (formalGlueingBaseChangeGlue S R' f X) i j)
      (formalGlueingComparisonOnOppositeOverlap fBase
        (formalGlueingBaseChangeBase S R' f X)
        (formalGlueingBaseChangeGlue S R' f X)
        (formalGlueingBaseChangeComparisonIsoApp S R' f X) i j) := by
  sorry

private noncomputable def formalGlueingBaseChangeObj (X : Glue S f) :
    GlueBase :=
  { base := formalGlueingBaseChangeBase S R' f X
    glue := formalGlueingBaseChangeGlue S R' f X
    comparisonIso := formalGlueingBaseChangeComparisonIsoApp S R' f X
    comparison_overlap := formalGlueingBaseChangeComparisonOverlap S R' f X }

private theorem formalGlueingBaseChangeMapComparison
    {X Y : Glue S f} (φ : X ⟶ Y) (i : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i))
          (((ModuleCat.extendScalars (algebraMap S SBase)).map φ.base).hom.restrictScalars R')))
      (formalGlueingBaseChangeComparisonIsoApp S R' f X i).hom
      (formalGlueingBaseChangeComparisonIsoApp S R' f Y i).hom
      (ModuleCat.ofHom <|
        (LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (fBase i)) (Localization.Away (fBase i)))
          (TensorProduct.map
            (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
              (φ.glue.localMap i)).hom.restrictScalars R')
            (LinearMap.id : SBase →ₗ[R'] SBase))) := by
  sorry

private theorem formalGlueingBaseChangeMapOverlapComm
    {X Y : Glue S f} (φ : X ⟶ Y) (i j : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i * fBase j))
          (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
            (φ.glue.localMap i)).hom.restrictScalars R')))
      (formalGlueingBaseChangeLocalOverlapIso S R' f X i j).hom
      (formalGlueingBaseChangeLocalOverlapIso S R' f Y i j).hom
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (fBase i * fBase j))
          (((ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f j)).map
            (φ.glue.localMap j)).hom.restrictScalars R'))) := by
  sorry

private noncomputable def formalGlueingBaseChangeMap
    {X Y : Glue S f} (φ : X ⟶ Y) :
    formalGlueingBaseChangeObj S R' f X ⟶ formalGlueingBaseChangeObj S R' f Y :=
  { base := (ModuleCat.extendScalars (algebraMap S SBase)).map φ.base
    glue :=
      { localMap := fun i ↦
          (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (φ.glue.localMap i)
        overlap_comm := formalGlueingBaseChangeMapOverlapComm S R' f φ }
    comparison_comm := formalGlueingBaseChangeMapComparison S R' f φ }

private theorem formalGlueingBaseChangeFunctor_map_id
    (X : Glue S f) :
    formalGlueingBaseChangeMap S R' f (𝟙 X) = 𝟙 (formalGlueingBaseChangeObj S R' f X) := by
  -- The base-change morphism is defined componentwise, so identity is checked on base and locals.
  apply FormalGlueingDatum.Hom.ext
  · change (ModuleCat.extendScalars (algebraMap S SBase)).map (𝟙 X.base) = 𝟙 _
    simpa using (ModuleCat.extendScalars (algebraMap S SBase)).map_id X.base
  · intro i
    change (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
        (𝟙 (X.glue.localModule i)) = 𝟙 _
    simpa using (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map_id
      (X.glue.localModule i)

private theorem formalGlueingBaseChangeFunctor_map_comp
    {X Y Z : Glue S f} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    formalGlueingBaseChangeMap S R' f (φ ≫ ψ) =
      formalGlueingBaseChangeMap S R' f φ ≫ formalGlueingBaseChangeMap S R' f ψ := by
  -- Composition is inherited componentwise from the extension-of-scalars functors.
  apply FormalGlueingDatum.Hom.ext
  · change (ModuleCat.extendScalars (algebraMap S SBase)).map (φ.base ≫ ψ.base) =
        (ModuleCat.extendScalars (algebraMap S SBase)).map φ.base ≫
          (ModuleCat.extendScalars (algebraMap S SBase)).map ψ.base
    simpa using (ModuleCat.extendScalars (algebraMap S SBase)).map_comp φ.base ψ.base
  · intro i
    change (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map
        (φ.glue.localMap i ≫ ψ.glue.localMap i) =
      (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (φ.glue.localMap i) ≫
        (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map (ψ.glue.localMap i)
    simpa using (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).map_comp
      (φ.glue.localMap i) (ψ.glue.localMap i)

/-- Lemma 15.90.15: the canonical glueing-side base-change functor
`Glue(R → S, f₁, \ldots, fₜ) ⥤ Glue(R' → S ⊗[R] R', f₁', \ldots, fₜ')`. -/
noncomputable def formalGlueingBaseChangeFunctor :
    Glue S f ⥤ GlueBase :=
  { obj := formalGlueingBaseChangeObj S R' f
    map := fun φ ↦ formalGlueingBaseChangeMap S R' f φ
    map_id := formalGlueingBaseChangeFunctor_map_id S R' f
    map_comp := formalGlueingBaseChangeFunctor_map_comp S R' f }

private theorem formalGlueingTensorBaseSquare_comm :
    (algebraMap S SBase).comp (algebraMap R S) =
      (algebraMap R' SBase).comp (algebraMap R R') := by
  -- Both composites are the canonical map from `R` into the tensor-product base change ring.
  ext x
  change
    (((Algebra.TensorProduct.includeLeft : S →ₐ[R] SBase).toRingHom.comp (algebraMap R S)) x) =
      (((Algebra.TensorProduct.includeRight : R' →ₐ[R] SBase).toRingHom.comp
        (algebraMap R R')) x)
  simpa using congrArg (fun g : R →+* SBase ↦ g x)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R] SBase).toRingHom.comp (algebraMap R S)) =
        ((Algebra.TensorProduct.includeRight : R' →ₐ[R] SBase).toRingHom.comp
          (algebraMap R R')))

private noncomputable def formalGlueingCanBaseChangeBaseIsoApp
    (M : ModuleCat.{max u v} R) :
    ((ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M).base ≅
      ((formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M).base :=
  let hcomm :
      (algebraMap S SBase).comp (algebraMap R S) =
        (algebraMap R' SBase).comp (algebraMap R R') :=
    formalGlueingTensorBaseSquare_comm S R'
  ((moduleCatBaseChangeSquare
      (algebraMap S SBase)
      (algebraMap R' SBase)
      (algebraMap R S)
      (algebraMap R R')
      hcomm).iso.app M).symm

private noncomputable def formalGlueingCanBaseChangeLocalIsoApp
    (M : ModuleCat.{max u v} R) (i : Fin t) :
    ((ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M).glue.localModule i ≅
      ((formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M).glue.localModule i :=
  let hcomm :
      (formalGlueingAwayBaseMap R' f i).comp (algebraMap R (Localization.Away (f i))) =
        (algebraMap R' (Localization.Away (fBase i))).comp (algebraMap R R') :=
    formalGlueingAwayBaseSquare_comm R' f i
  (awayExtendScalarsIso (fBase i)
      ((ModuleCat.extendScalars (algebraMap R R')).obj M)).symm ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap R' f i)
        (algebraMap R' (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R R')
        hcomm).iso.app M).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap R' f i)).mapIso
      (awayExtendScalarsIso (f i) M)

private noncomputable def formalGlueingCanBaseChangeIsoApp
    (M : ModuleCat.{max u v} R) :
    (ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase).obj M ≅
      (formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f).obj M :=
  { hom :=
      { base := (formalGlueingCanBaseChangeBaseIsoApp S R' f M).hom
        glue :=
          { localMap := fun i ↦ (formalGlueingCanBaseChangeLocalIsoApp S R' f M i).hom
            overlap_comm := by
              intro i j
              sorry }
        comparison_comm := by
          intro i
          sorry }
    inv :=
      { base := (formalGlueingCanBaseChangeBaseIsoApp S R' f M).inv
        glue :=
          { localMap := fun i ↦ (formalGlueingCanBaseChangeLocalIsoApp S R' f M i).inv
            overlap_comm := by
              intro i j
              sorry }
        comparison_comm := by
          intro i
          sorry }
    hom_inv_id := by
      sorry
    inv_hom_id := by
      sorry }

/-- Lemma 15.90.15, `Can`-square form: the canonical formal-glueing functor commutes with base
change up to the indicated fixed-vertical natural isomorphism. -/
noncomputable def formalGlueingCanBaseChangeIso
    :
    ModuleCat.extendScalars (algebraMap R R') ⋙ formalGlueingCan SBase fBase ≅
      formalGlueingCan S f ⋙ formalGlueingBaseChangeFunctor S R' f :=
  NatIso.ofComponents
    (formalGlueingCanBaseChangeIsoApp S R' f)
    (by
      intro M N φ
      sorry)

private noncomputable def formalGlueingH0BaseChangeHomApp
    (X : Glue S f) :
    (formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R')).obj X ⟶
      (formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase).obj X :=
  let β :
      (formalGlueingCan SBase fBase).obj
          ((ModuleCat.extendScalars (algebraMap R R')).obj ((formalGlueingH0 S f).obj X)) ⟶
        (formalGlueingBaseChangeFunctor S R' f).obj X :=
    (formalGlueingCanBaseChangeIsoApp S R' f ((formalGlueingH0 S f).obj X)).hom ≫
      (formalGlueingBaseChangeFunctor S R' f).map
        ((formalGlueingCanAdjunction f).counit.app X)
  (formalGlueingCanAdjunction fBase).homEquiv _ _ β

private theorem formalGlueingH0BaseChangeHomApp_isIso
    (X : Glue S f) :
    IsIso (formalGlueingH0BaseChangeHomApp S R' f X) := by
  sorry

private noncomputable def formalGlueingH0BaseChangeIsoApp
    (X : Glue S f) :
    (formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase).obj X ≅
      (formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R')).obj X :=
  letI := formalGlueingH0BaseChangeHomApp_isIso S R' f X
  (asIso (formalGlueingH0BaseChangeHomApp S R' f X)).symm

/-- Lemma 15.90.15, `H⁰`-square form: the degree-zero functor commutes with base change up to the
indicated fixed-vertical natural isomorphism. -/
noncomputable def formalGlueingH0BaseChangeIso
    :
    formalGlueingBaseChangeFunctor S R' f ⋙ formalGlueingH0 SBase fBase ≅
      formalGlueingH0 S f ⋙ ModuleCat.extendScalars (algebraMap R R') :=
  NatIso.ofComponents
    (formalGlueingH0BaseChangeIsoApp S R' f)
    (by
      intro X Y φ
      sorry)

end
