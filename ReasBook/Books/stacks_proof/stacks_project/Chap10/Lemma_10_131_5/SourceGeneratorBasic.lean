import StacksProject_2024.Chap10.Lemma_10_131_5.StageDifferentialBridge

open CategoryTheory
open Ring.DirectLimit

universe u

noncomputable section

namespace Lemma_10_131_5

section

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-- Helper for Lemma 10.131.5: the class in the direct-limit source module represented by the
stage generator `1 ⊗ d x`. -/
noncomputable abbrev stageDirectLimitSourceGenerator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    kaehlerDifferentialDirectLimitModule hcomm :=
  let _ : DecidableEq I := Classical.decEq I
  Module.DirectLimit.of S∞ I
    (fun i ↦ stageKaehlerDifferentialBaseChange i)
    (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i
    (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
        (@stageKaehlerDifferential I R S _ _ _ i))
      (CommRingCat.KaehlerDifferential.d x))

/-- Helper for Lemma 10.131.5: the stage generator family vanishes on base-ring images. -/
theorem stageDirectLimitSourceGenerator_on_algebraMap
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (r : R i) :
    stageDirectLimitSourceGenerator hcomm i (algebraMap (R i) (S i) r) = 0 := by
  -- The universal derivation vanishes on base-ring images, so the represented class is zero.
  classical
  unfold stageDirectLimitSourceGenerator
  have hmap :
      CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i)
          (algebraMap (R i) (S i) r) = 0 := by
    simpa using
      (ModuleCat.Derivation.d_map
        (D := CommRingCat.KaehlerDifferential.D (@stageHom I R S _ _ _ i)) r)
  rw [hmap, ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rw [TensorProduct.tmul_zero]
  exact
    (Module.DirectLimit.of S∞ I
      (fun i ↦ stageKaehlerDifferentialBaseChange i)
      (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i).map_zero

/-- Helper for Lemma 10.131.5: the stage generator family is additive in the stage variable. -/
theorem stageDirectLimitSourceGenerator_add
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x y : S i) :
    stageDirectLimitSourceGenerator hcomm i (x + y) =
      stageDirectLimitSourceGenerator hcomm i x +
        stageDirectLimitSourceGenerator hcomm i y := by
  -- The stage generator is obtained by applying two linear maps to `d (x + y)`, so additivity is
  -- immediate once the universal derivation is rewritten by `d_add`.
  classical
  unfold stageDirectLimitSourceGenerator
  have hadd :
      CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) (x + y) =
        CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x +
          CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) y := by
    simpa using
      (ModuleCat.Derivation.d_add
        (D := CommRingCat.KaehlerDifferential.D (@stageHom I R S _ _ _ i)) x y)
  rw [hadd]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rw [TensorProduct.tmul_add]
  exact
    (Module.DirectLimit.of S∞ I
      (fun i ↦ stageKaehlerDifferentialBaseChange i)
      (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i).map_add
        ((1 : S∞) ⊗ₜ[S i] CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x)
        ((1 : S∞) ⊗ₜ[S i] CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) y)

/-- Helper for Lemma 10.131.5: the stage square-zero lift sends `x : S_i` to the direct-limit
image of `x` together with the class of its differential generator. -/
noncomputable abbrev stageDirectLimitTargetSquareZeroLiftFun
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt S∞ ↑(kaehlerDifferentialDirectLimitModule hcomm) :=
  TrivSqZeroExt.inl (stageDirectLimitTargetMap i x) +
    TrivSqZeroExt.inr (stageDirectLimitSourceGenerator hcomm i x)

/-- Helper for Lemma 10.131.5: the first projection of the stage square-zero lift is the stage map
to the target ring direct limit. -/
theorem stageDirectLimitTargetSquareZeroLiftFun_fst
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt.fst (stageDirectLimitTargetSquareZeroLiftFun hcomm i x) =
      stageDirectLimitTargetMap i x := by
  -- The square-zero lift was defined as `inl` of the stage image plus `inr` of the generator.
  simp [stageDirectLimitTargetSquareZeroLiftFun]

/-- Helper for Lemma 10.131.5: the second projection of the stage square-zero lift is the stage
generator class in the source direct limit. -/
theorem stageDirectLimitTargetSquareZeroLiftFun_snd
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt.snd (stageDirectLimitTargetSquareZeroLiftFun hcomm i x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- The `inl` term contributes no second component, so only the named generator remains.
  simp [stageDirectLimitTargetSquareZeroLiftFun]

/-- Helper for Lemma 10.131.5: the stage square-zero lift preserves zero. -/
theorem stageDirectLimitTargetSquareZeroLift_map_zero
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    stageDirectLimitTargetSquareZeroLiftFun hcomm i 0 = 0 := by
  -- Both coordinates vanish: the first by functoriality of the direct-limit map,
  -- and the second because differentials vanish on base-ring images.
  have hzero :
      stageDirectLimitSourceGenerator hcomm i 0 = 0 := by
    simpa using stageDirectLimitSourceGenerator_on_algebraMap (hcomm := hcomm) i (0 : R i)
  apply TrivSqZeroExt.ext
  · simp [stageDirectLimitTargetSquareZeroLiftFun]
  · simp [stageDirectLimitTargetSquareZeroLiftFun, hzero]

/-- Helper for Lemma 10.131.5: the stage square-zero lift preserves one. -/
theorem stageDirectLimitTargetSquareZeroLift_map_one
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    stageDirectLimitTargetSquareZeroLiftFun hcomm i 1 = 1 := by
  -- The first coordinate is the unit in the target ring, and the second coordinate vanishes
  -- because `1` comes from the base ring.
  have hone :
      stageDirectLimitSourceGenerator hcomm i 1 = 0 := by
    simpa using stageDirectLimitSourceGenerator_on_algebraMap (hcomm := hcomm) i (1 : R i)
  apply TrivSqZeroExt.ext
  · simp [stageDirectLimitTargetSquareZeroLiftFun]
  · simp [stageDirectLimitTargetSquareZeroLiftFun, hone]

/-- Helper for Lemma 10.131.5: the stage square-zero lift preserves addition. -/
theorem stageDirectLimitTargetSquareZeroLift_map_add
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x y : S i) :
    stageDirectLimitTargetSquareZeroLiftFun hcomm i (x + y) =
      stageDirectLimitTargetSquareZeroLiftFun hcomm i x +
        stageDirectLimitTargetSquareZeroLiftFun hcomm i y := by
  -- Addition is checked coordinatewise, using additivity of the stage generator family.
  apply TrivSqZeroExt.ext
  · simp [stageDirectLimitTargetSquareZeroLiftFun]
  · simp [stageDirectLimitTargetSquareZeroLiftFun, stageDirectLimitSourceGenerator_add]

end

end Lemma_10_131_5
