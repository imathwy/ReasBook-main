/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part3

open scoped Pointwise

section Chap03
section Section13

/-- For a nonempty convex set `C`, its `EReal`-valued support function is closed, proper, convex,
and positively homogeneous. -/
lemma section13_supportFunctionEReal_closedProperConvex_posHom {n : Nat} (C : Set (Fin n → Real))
    (hCne : Set.Nonempty C) (hC : Convex ℝ C) :
    ClosedConvexFunction (supportFunctionEReal C) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (supportFunctionEReal C) ∧
        PositivelyHomogeneous (supportFunctionEReal C) := by
  simpa using
    (exists_supportFunctionEReal_iff_closedProperConvex_posHom (n := n) (f := supportFunctionEReal C)).1
      ⟨C, hCne, hC, rfl⟩

/-- The `EReal`-valued support function of a nonempty convex set never takes the value `⊥`. -/
lemma section13_supportFunctionEReal_ne_bot {n : Nat} (C : Set (Fin n → Real))
    (hCne : Set.Nonempty C) (hC : Convex ℝ C) :
    ∀ xStar : Fin n → Real, supportFunctionEReal C xStar ≠ (⊥ : EReal) := by
  intro xStar
  have hf :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hC
  exact hf.2.1.2.2 xStar (by simp)

/-- The `EReal`-valued support function of a nonempty convex set is subadditive. -/
lemma section13_supportFunctionEReal_subadditive {n : Nat} (C : Set (Fin n → Real))
    (hCne : Set.Nonempty C) (hC : Convex ℝ C) :
    ∀ xStar₁ xStar₂ : Fin n → Real,
      supportFunctionEReal C (xStar₁ + xStar₂) ≤
        supportFunctionEReal C xStar₁ + supportFunctionEReal C xStar₂ := by
  have hf :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hC
  have hnotbot : ∀ xStar : Fin n → Real, supportFunctionEReal C xStar ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot (n := n) (C := C) hCne hC
  exact subadditive_of_convex_posHom (hpos := hf.2.2) hf.1.1 hnotbot

/-- Text 13.2.3: Let `C ⊆ ℝ^n` be a nonempty convex set. Then the (extended-real) support function
is lower semicontinuous on `ℝ^n`, and it satisfies the subadditivity inequality

`δ^*(xStar₁ + xStar₂ | C) ≤ δ^*(xStar₁ | C) + δ^*(xStar₂ | C)` for all `xStar₁`, `xStar₂`. -/
theorem deltaStar_lowerSemicontinuous_and_add_le {n : Nat} (C : Set (Fin n → Real))
    (hCne : Set.Nonempty C) (hC : Convex ℝ C) :
    LowerSemicontinuous (supportFunctionEReal C) ∧
      ∀ xStar₁ xStar₂ : Fin n → Real,
        supportFunctionEReal C (xStar₁ + xStar₂) ≤
          supportFunctionEReal C xStar₁ + supportFunctionEReal C xStar₂ := by
  have hf :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hC
  refine ⟨hf.1.2, section13_supportFunctionEReal_subadditive (n := n) (C := C) hCne hC⟩

/-- Bridge `Real.sqrt (dotProduct x x)` to the Euclidean norm on `EuclideanSpace`. -/
lemma section13_sqrt_dotProduct_self_eq_norm_euclideanSpace {n : Nat} (x : Fin n → Real) :
    Real.sqrt (dotProduct x x) =
      ‖((EuclideanSpace.equiv (Fin n) ℝ).symm x : EuclideanSpace ℝ (Fin n))‖ := by
  classical
  have hdot :
      dotProduct x x =
        inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
    simpa using (dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := x))
  calc
    Real.sqrt (dotProduct x x) =
        Real.sqrt
          (inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
            ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) := by
          simp [hdot]
    _ = ‖((EuclideanSpace.equiv (Fin n) ℝ).symm x : EuclideanSpace ℝ (Fin n))‖ := by
          exact
            (norm_eq_sqrt_real_inner
              ((EuclideanSpace.equiv (Fin n) ℝ).symm x : EuclideanSpace ℝ (Fin n))).symm

/-- Cauchy--Schwarz in the `dotProduct` notation used throughout this section. -/
lemma section13_dotProduct_le_sqrt_mul_sqrt {n : Nat} (x y : Fin n → Real) :
    dotProduct x y ≤ Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y) := by
  classical
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  let xE : EuclideanSpace ℝ (Fin n) := eL.symm x
  let yE : EuclideanSpace ℝ (Fin n) := eL.symm y
  have hxy : dotProduct x y = inner ℝ xE yE := by
    simpa [eL, xE, yE] using (dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := y))
  have hxx : Real.sqrt (dotProduct x x) = ‖xE‖ := by
    simpa [eL, xE] using (section13_sqrt_dotProduct_self_eq_norm_euclideanSpace (n := n) (x := x))
  have hyy : Real.sqrt (dotProduct y y) = ‖yE‖ := by
    simpa [eL, yE] using (section13_sqrt_dotProduct_self_eq_norm_euclideanSpace (n := n) (x := y))
  calc
    dotProduct x y = inner ℝ xE yE := hxy
    _ ≤ ‖xE‖ * ‖yE‖ := real_inner_le_norm xE yE
    _ = Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y) := by
          simp [hxx, hyy]

/-- If `y` lies in the unit Euclidean ball, then `dotProduct x y` is bounded by the Euclidean
norm of `x`. -/
lemma section13_dotProduct_le_sqrt_of_sqrt_dotProduct_self_le_one {n : Nat} (x y : Fin n → Real)
    (hy : Real.sqrt (dotProduct y y) ≤ (1 : Real)) :
    dotProduct x y ≤ Real.sqrt (dotProduct x x) := by
  have hcs :=
    section13_dotProduct_le_sqrt_mul_sqrt (n := n) (x := x) (y := y)
  have hxnonneg : 0 ≤ Real.sqrt (dotProduct x x) := Real.sqrt_nonneg _
  have hmul :
      Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y) ≤ Real.sqrt (dotProduct x x) :=
    mul_le_of_le_one_right hxnonneg hy
  exact le_trans hcs hmul

/-- For any `x`, the supremum of `y ↦ dotProduct x y` over the unit Euclidean ball is attained by a
normalized vector. -/
lemma section13_exists_dotProduct_eq_sqrt {n : Nat} (x : Fin n → Real) :
    ∃ y : Fin n → Real,
      Real.sqrt (dotProduct y y) ≤ (1 : Real) ∧
        dotProduct x y = Real.sqrt (dotProduct x x) := by
  classical
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simp
    · simp [hx]
  · let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
    let u : EuclideanSpace ℝ (Fin n) := eL.symm x
    have hu : u ≠ 0 := by
      intro hu0
      apply hx
      calc
        x = eL u := by simp [u]
        _ = eL 0 := by simp [hu0]
        _ = 0 := by simp
    have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hnorm_ne : ‖u‖ ≠ 0 := ne_of_gt hnorm_pos
    set yE : EuclideanSpace ℝ (Fin n) := (‖u‖)⁻¹ • u
    set y : Fin n → Real := eL yE
    refine ⟨y, ?_, ?_⟩
    · have hy_norm : ‖yE‖ = (1 : Real) := by
        calc
          ‖yE‖ = ‖(‖u‖)⁻¹ • u‖ := by simp [yE]
          _ = ‖(‖u‖)⁻¹‖ * ‖u‖ := by simp [norm_smul]
          _ = |(‖u‖)⁻¹| * ‖u‖ := by simp
          _ = (‖u‖)⁻¹ * ‖u‖ := by
                simp [abs_of_nonneg (inv_nonneg.2 (le_of_lt hnorm_pos))]
          _ = 1 := by simp [inv_mul_cancel₀ hnorm_ne]
      have hy_sqrt : Real.sqrt (dotProduct y y) = ‖yE‖ := by
        simpa [y, yE, eL] using
          (section13_sqrt_dotProduct_self_eq_norm_euclideanSpace (n := n) (x := y))
      simp [hy_sqrt, hy_norm]
    · have hx_sqrt : Real.sqrt (dotProduct x x) = ‖u‖ := by
        simpa [u, eL] using
          (section13_sqrt_dotProduct_self_eq_norm_euclideanSpace (n := n) (x := x))
      have hxy : dotProduct x y = inner ℝ u yE := by
        simpa [u, y, yE, eL] using (dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := y))
      have hinner : inner ℝ u yE = ‖u‖ := by
        calc
          inner ℝ u yE = inner ℝ u ((‖u‖)⁻¹ • u) := by simp [yE]
          _ = (‖u‖)⁻¹ * inner ℝ u u := by
                simpa using (real_inner_smul_right u u (‖u‖)⁻¹)
          _ = (‖u‖)⁻¹ * (‖u‖ * ‖u‖) := by
                rw [real_inner_self_eq_norm_mul_norm u]
          _ = ‖u‖ := by
                calc
                  (‖u‖)⁻¹ * (‖u‖ * ‖u‖) = ((‖u‖)⁻¹ * ‖u‖) * ‖u‖ := by
                    simp [mul_assoc]
                  _ = (1 : Real) * ‖u‖ := by simp [inv_mul_cancel₀ hnorm_ne]
                  _ = ‖u‖ := by simp
      calc
        dotProduct x y = inner ℝ u yE := hxy
        _ = ‖u‖ := hinner
        _ = Real.sqrt (dotProduct x x) := by simp [hx_sqrt]

/-- Text 13.2.4: Let `B := { y ∈ ℝ^n | |y| ≤ 1 }` be the unit Euclidean ball. Then for every
`x ∈ ℝ^n`,

`|x| = sup { ⟪x, y⟫ | y ∈ B } = δ^*(x | B)`. -/
theorem euclideanNorm_eq_sSup_dotProduct_unitEuclideanBall_eq_deltaStar {n : Nat}
    (x : Fin n → Real) :
    let B : Set (Fin n → Real) := {y | Real.sqrt (dotProduct y y) ≤ (1 : Real)}
    Real.sqrt (dotProduct x x) =
        sSup (Set.image (fun y : Fin n → Real => dotProduct x y) B) ∧
      sSup (Set.image (fun y : Fin n → Real => dotProduct x y) B) = deltaStar B x := by
  intro B
  set S : Set ℝ := Set.image (fun y : Fin n → Real => dotProduct x y) B with hS
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, by simp⟩
    simp [B]
  have hUpper : ∀ r ∈ S, r ≤ Real.sqrt (dotProduct x x) := by
    intro r hr
    rcases hr with ⟨y, hyB, rfl⟩
    exact
      section13_dotProduct_le_sqrt_of_sqrt_dotProduct_self_le_one (n := n) (x := x) (y := y)
        (by simpa [B] using hyB)
  have hSup_le : sSup S ≤ Real.sqrt (dotProduct x x) := csSup_le hSne hUpper
  have hBdd : BddAbove S := by
    refine ⟨Real.sqrt (dotProduct x x), ?_⟩
    intro r hr
    exact hUpper r hr
  have hSqrt_le : Real.sqrt (dotProduct x x) ≤ sSup S := by
    rcases section13_exists_dotProduct_eq_sqrt (n := n) (x := x) with ⟨y, hyB, hyEq⟩
    have hyS : dotProduct x y ∈ S := by
      refine ⟨y, ?_, rfl⟩
      simpa [B] using hyB
    calc
      Real.sqrt (dotProduct x x) = dotProduct x y := by simpa using hyEq.symm
      _ ≤ sSup S := le_csSup hBdd hyS
  have hEq : Real.sqrt (dotProduct x x) = sSup S := le_antisymm hSqrt_le hSup_le
  refine ⟨?_, ?_⟩
  · simpa [hS] using hEq
  · simpa [deltaStar] using (supportFunction_eq_sSup_image_dotProduct (C := B) (x := x)).symm

/-- Membership in `{a} + λ • B` can be rewritten using the explicit parametrization `a + λ • y`,
with `y ∈ B`. -/
lemma section13_mem_singleton_add_smul_unitEuclideanBall_iff {n : Nat} (a z : Fin n → Real)
    (lam : ℝ) :
    let B : Set (Fin n → Real) := {y | Real.sqrt (dotProduct y y) ≤ (1 : Real)}
    z ∈ ({a} : Set (Fin n → Real)) + (lam • B) ↔ ∃ y, y ∈ B ∧ z = a + lam • y := by
  intro B
  constructor
  · intro hz
    rcases (Set.mem_add).1 hz with ⟨u, hu, v, hv, rfl⟩
    have hu' : u = a := by simpa using hu
    subst hu'
    rcases (Set.mem_smul_set).1 hv with ⟨y, hyB, rfl⟩
    exact ⟨y, hyB, rfl⟩
  · rintro ⟨y, hyB, rfl⟩
    refine Set.add_mem_add (by simp) ?_
    exact (Set.mem_smul_set).2 ⟨y, hyB, rfl⟩

/-- Every dot product over the translated/scaled unit Euclidean ball is bounded by
`⟪x, a⟫ + λ‖x‖` when `λ ≥ 0`. -/
lemma section13_dotProduct_le_dotProduct_add_mul_sqrt_of_mem_singleton_add_smul_unitEuclideanBall
    {n : Nat} (a x z : Fin n → Real) (lam : ℝ) (hlam : 0 ≤ lam) :
    let B : Set (Fin n → Real) := {y | Real.sqrt (dotProduct y y) ≤ (1 : Real)}
    z ∈ ({a} : Set (Fin n → Real)) + (lam • B) →
      dotProduct x z ≤ dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
  intro B hz
  rcases
      (section13_mem_singleton_add_smul_unitEuclideanBall_iff (n := n) (a := a) (z := z)
            (lam := lam)).1 (by simpa [B] using hz) with
    ⟨y, hyB, rfl⟩
  have hdot_le :
      dotProduct x y ≤ Real.sqrt (dotProduct x x) :=
    section13_dotProduct_le_sqrt_of_sqrt_dotProduct_self_le_one (n := n) (x := x) (y := y)
      (by simpa [B] using hyB)
  have hmul_le :
      lam * dotProduct x y ≤ lam * Real.sqrt (dotProduct x x) :=
    mul_le_mul_of_nonneg_left hdot_le hlam
  calc
    dotProduct x (a + lam • y) = dotProduct x a + lam * dotProduct x y := by
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
    _ ≤ dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul_le (dotProduct x a)

/-- The supremum of `z ↦ ⟪x, z⟫` over `{a} + λ • B` is attained at `a + λ • y`, where `y`
maximizes `⟪x, ·⟫` over `B`. -/
lemma section13_exists_mem_singleton_add_smul_unitEuclideanBall_dotProduct_eq {n : Nat}
    (a x : Fin n → Real) (lam : ℝ) :
    let B : Set (Fin n → Real) := {y | Real.sqrt (dotProduct y y) ≤ (1 : Real)}
    ∃ z ∈ ({a} : Set (Fin n → Real)) + (lam • B),
      dotProduct x z = dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
  intro B
  rcases section13_exists_dotProduct_eq_sqrt (n := n) (x := x) with ⟨y, hyB, hyEq⟩
  have hyB' : y ∈ B := by simpa [B] using hyB
  refine ⟨a + lam • y, ?_, ?_⟩
  · refine Set.add_mem_add (by simp) ?_
    exact (Set.mem_smul_set).2 ⟨y, hyB', rfl⟩
  · calc
      dotProduct x (a + lam • y) = dotProduct x a + lam * dotProduct x y := by
        simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
      _ = dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
        simp [hyEq]

/-- Text 13.2.5: Let `B := { y ∈ ℝ^n | |y| ≤ 1 }` be the unit Euclidean ball. More generally, for
any `a ∈ ℝ^n` and `λ ≥ 0`, the support function of the ball `a + λ B` is given by

`δ^*(x | a + λ B) = ⟪x, a⟫ + λ |x|`. -/
theorem deltaStar_singleton_add_smul_unitEuclideanBall {n : Nat} (a x : Fin n → Real) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    let B : Set (Fin n → Real) := {y | Real.sqrt (dotProduct y y) ≤ (1 : Real)}
    deltaStar (({a} : Set (Fin n → Real)) + (lam • B)) x =
      dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
  intro B
  set C : Set (Fin n → Real) := ({a} : Set (Fin n → Real)) + (lam • B) with hC
  set S : Set ℝ := Set.image (fun z : Fin n → Real => dotProduct x z) C with hS
  have hSne : S.Nonempty := by
    refine ⟨dotProduct x (a + lam • (0 : Fin n → Real)), ?_⟩
    refine ⟨a + lam • (0 : Fin n → Real), ?_, rfl⟩
    have h0B : (0 : Fin n → Real) ∈ B := by simp [B]
    have h0smul : lam • (0 : Fin n → Real) ∈ lam • B :=
      (Set.mem_smul_set).2 ⟨0, h0B, rfl⟩
    have ha : a ∈ ({a} : Set (Fin n → Real)) := by simp
    simpa [hC] using Set.add_mem_add ha h0smul
  have hUpper : ∀ r ∈ S, r ≤ dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
    intro r hr
    rcases hr with ⟨z, hzC, rfl⟩
    have hzC' : z ∈ ({a} : Set (Fin n → Real)) + (lam • B) := by
      simpa [hC] using hzC
    exact
      section13_dotProduct_le_dotProduct_add_mul_sqrt_of_mem_singleton_add_smul_unitEuclideanBall
        (n := n) (a := a) (x := x) (z := z) (lam := lam) hlam (by simpa [B] using hzC')
  have hSup_le : sSup S ≤ dotProduct x a + lam * Real.sqrt (dotProduct x x) := csSup_le hSne hUpper
  have hBdd : BddAbove S := by
    refine ⟨dotProduct x a + lam * Real.sqrt (dotProduct x x), ?_⟩
    intro r hr
    exact hUpper r hr
  have hLower : dotProduct x a + lam * Real.sqrt (dotProduct x x) ≤ sSup S := by
    have hw :
        ∃ z ∈ ({a} : Set (Fin n → Real)) + (lam • B),
          dotProduct x z = dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
      simpa [B] using
        (section13_exists_mem_singleton_add_smul_unitEuclideanBall_dotProduct_eq (n := n) (a := a)
          (x := x) (lam := lam))
    rcases hw with ⟨z, hzC, hzEq⟩
    have hzS : dotProduct x z ∈ S := by
      refine ⟨z, ?_, rfl⟩
      simpa [hC] using hzC
    have hz_le : dotProduct x z ≤ sSup S := le_csSup hBdd hzS
    simpa [hzEq] using hz_le
  have hEq : sSup S = dotProduct x a + lam * Real.sqrt (dotProduct x x) :=
    le_antisymm hSup_le hLower
  have hSupport : deltaStar C x = sSup S := by
    simpa [deltaStar, hS] using (supportFunction_eq_sSup_image_dotProduct (C := C) (x := x))
  have hMain : deltaStar C x = dotProduct x a + lam * Real.sqrt (dotProduct x x) := by
    calc
      deltaStar C x = sSup S := hSupport
      _ = dotProduct x a + lam * Real.sqrt (dotProduct x x) := hEq
  simpa [hC] using hMain

end Section13
end Chap03
