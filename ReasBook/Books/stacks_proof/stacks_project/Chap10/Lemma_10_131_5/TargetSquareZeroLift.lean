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

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-- Helper for Lemma 10.131.5: the canonical square-zero lift on `S∞` associated to the universal
derivation `d : S∞ → Ω[S∞⁄R∞]`. -/
noncomputable abbrev targetKaehlerSquareZeroLiftFun
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x : S∞) :
    TrivSqZeroExt S∞ ↑(directLimitDifferential hcomm) :=
  TrivSqZeroExt.inl x + TrivSqZeroExt.inr (CommRingCat.KaehlerDifferential.d x)

/-- Helper for Lemma 10.131.5: the target square-zero lift preserves zero. -/
theorem targetKaehlerSquareZeroLift_map_zero
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    targetKaehlerSquareZeroLiftFun hcomm 0 = 0 := by
  -- Both coordinates vanish because the universal derivation sends `0` to `0`.
  have hzero :
      CommRingCat.KaehlerDifferential.d
          (f := CommRingCat.ofHom (directLimitRingHom hcomm)) (0 : S∞) = 0 := by
    simpa [map_zero] using
      (ModuleCat.Derivation.d_map
        (D := CommRingCat.KaehlerDifferential.D (CommRingCat.ofHom (directLimitRingHom hcomm)))
        (0 : R∞))
  simp [targetKaehlerSquareZeroLiftFun, hzero]

/-- Helper for Lemma 10.131.5: the target square-zero lift preserves one. -/
theorem targetKaehlerSquareZeroLift_map_one
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    targetKaehlerSquareZeroLiftFun hcomm 1 = 1 := by
  -- The first coordinate is `1`, while the differential of `1` vanishes.
  have hone :
      CommRingCat.KaehlerDifferential.d
          (f := CommRingCat.ofHom (directLimitRingHom hcomm)) (1 : S∞) = 0 := by
    simpa [map_one] using
      (ModuleCat.Derivation.d_map
        (D := CommRingCat.KaehlerDifferential.D (CommRingCat.ofHom (directLimitRingHom hcomm)))
        (1 : R∞))
  simp [targetKaehlerSquareZeroLiftFun, hone]

/-- Helper for Lemma 10.131.5: the target square-zero lift preserves addition. -/
theorem targetKaehlerSquareZeroLift_map_add
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x y : S∞) :
    targetKaehlerSquareZeroLiftFun hcomm (x + y) =
      targetKaehlerSquareZeroLiftFun hcomm x + targetKaehlerSquareZeroLiftFun hcomm y := by
  -- Compare both coordinates separately; on the differential coordinate this is exactly `d_add`.
  apply TrivSqZeroExt.ext
  · simp [targetKaehlerSquareZeroLiftFun]
  · have hadd :
        CommRingCat.KaehlerDifferential.d
            (f := CommRingCat.ofHom (directLimitRingHom hcomm)) (x + y) =
          CommRingCat.KaehlerDifferential.d
              (f := CommRingCat.ofHom (directLimitRingHom hcomm)) x +
            CommRingCat.KaehlerDifferential.d
              (f := CommRingCat.ofHom (directLimitRingHom hcomm)) y := by
        simpa using
          (ModuleCat.Derivation.d_add
            (D := CommRingCat.KaehlerDifferential.D (CommRingCat.ofHom (directLimitRingHom hcomm)))
            x y)
    simp [targetKaehlerSquareZeroLiftFun, hadd]

/-- Helper for Lemma 10.131.5: the target square-zero lift is multiplicative because the
universal derivation satisfies Leibniz. -/
theorem targetKaehlerSquareZeroLift_map_mul
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x y : S∞) :
    targetKaehlerSquareZeroLiftFun hcomm (x * y) =
      targetKaehlerSquareZeroLiftFun hcomm x * targetKaehlerSquareZeroLiftFun hcomm y := by
  -- Compare both coordinates, using Leibniz on the differential coordinate.
  apply TrivSqZeroExt.ext
  · simp [targetKaehlerSquareZeroLiftFun]
  · have hmul :
        CommRingCat.KaehlerDifferential.d
            (f := CommRingCat.ofHom (directLimitRingHom hcomm)) (x * y) =
          x • CommRingCat.KaehlerDifferential.d
              (f := CommRingCat.ofHom (directLimitRingHom hcomm)) y +
            y • CommRingCat.KaehlerDifferential.d
              (f := CommRingCat.ofHom (directLimitRingHom hcomm)) x := by
        simpa using
          (ModuleCat.Derivation.d_mul
            (D := CommRingCat.KaehlerDifferential.D
              (CommRingCat.ofHom (directLimitRingHom hcomm))) x y)
    simp [targetKaehlerSquareZeroLiftFun, hmul, TrivSqZeroExt.snd_mul]

/-- Helper for Lemma 10.131.5: the canonical square-zero lift on `S∞` associated to the universal
derivation `d : S∞ → Ω[S∞⁄R∞]`. -/
noncomputable def targetKaehlerSquareZeroLift
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    S∞ →+* TrivSqZeroExt S∞ ↑(directLimitDifferential hcomm) :=
  { toFun := targetKaehlerSquareZeroLiftFun hcomm
    map_one' := targetKaehlerSquareZeroLift_map_one hcomm
    map_mul' := targetKaehlerSquareZeroLift_map_mul hcomm
    map_zero' := targetKaehlerSquareZeroLift_map_zero hcomm
    map_add' := targetKaehlerSquareZeroLift_map_add hcomm }

end

end Lemma_10_131_5
