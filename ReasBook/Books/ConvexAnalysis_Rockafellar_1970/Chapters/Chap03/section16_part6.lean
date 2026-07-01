/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part5

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Corollary 16.3.1.3: Let `A : ℝ^n →ₗ[ℝ] ℝ^m` be a linear map and let `D ⊆ ℝ^m` be convex.
If there exists `x` such that `A x ∈ ri D`, then the closure on `D` can be omitted in Corollary
16.3.1.2. Equivalently, for every `xStar`,

`δ^*(xStar | A⁻¹ D) = inf { δ^*(yStar | D) | A^* yStar = xStar }`,

and the infimum is attained (or the value is `+∞` if the affine fiber is empty). -/
theorem section16_supportFunctionEReal_preimage_eq_adjoint_image_of_exists_mem_ri {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (D : Set (Fin m → ℝ))
    (hD : Convex ℝ D)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' D)) :
    let Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    ((supportFunctionEReal
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ∧
      ∀ xStar : Fin n → ℝ,
        sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar}) =
            ⊤ ∨
          ∃ yStar : EuclideanSpace ℝ (Fin m),
            Aadj yStar = WithLp.toLp 2 xStar ∧
              supportFunctionEReal D (yStar : Fin m → ℝ) =
                sInf
                  ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                        supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                    {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  let g : (Fin m → ℝ) → EReal := indicatorFunction D
  obtain ⟨hgproper, hri'⟩ :=
    section16_properConvexFunctionOn_indicatorFunction_of_exists_mem_ri
      (A := A) (D := D) hD hri
  have hgconv : ConvexFunction g := by
    simpa [g] using (convexFunction_indicator_of_convex (C := D) hD)
  have hcl_precomp :
      convexFunctionClosure (fun x : Fin n → ℝ => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ) :=
    section16_convexFunctionClosure_precomp_eq_precomp_convexFunctionClosure_of_exists_mem_ri
      (A := A) (g := g) (hgproper := hgproper) hri'
  have hprecomp :
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fenchelConjugate n (fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ)) := by
    calc
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
          fenchelConjugate n
            (convexFunctionClosure (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ))) := by
        simpa using
          (fenchelConjugate_eq_of_convexFunctionClosure (n := n)
            (f := fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ))).symm
      _ =
          fenchelConjugate n (fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ)) := by
        simp [hcl_precomp]
  have hmain :=
    section16_fenchelConjugate_precomp_convexFunctionClosure_eq_convexFunctionClosure_adjoint_image
      (A := A) (g := g) hgconv
  have hEq_closure :
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        convexFunctionClosure
          (fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
    exact hprecomp.trans hmain
  have hclosed_att :=
    section16_adjointImage_closed_and_attained_of_exists_mem_ri_effectiveDomain
      (A := A) (g := g) (hgproper := hgproper) hri'
  have hclosed_att' :
      (convexFunctionClosure
            (fun xStar : Fin n → ℝ =>
              sInf
                ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                      fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                  {yStar | Aadj yStar = WithLp.toLp 2 xStar})) =
          fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ∧
        ∀ xStar : Fin n → ℝ,
          sInf
                ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                      fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                  {yStar | Aadj yStar = WithLp.toLp 2 xStar}) =
              ⊤ ∨
            ∃ yStar : EuclideanSpace ℝ (Fin m),
              Aadj yStar = WithLp.toLp 2 xStar ∧
                fenchelConjugate m g (yStar : Fin m → ℝ) =
                  sInf
                    ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                          fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                      {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
    simpa [Aadj] using hclosed_att
  have hEq :
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  fenchelConjugate m g (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
    simpa [hclosed_att'.1] using hEq_closure
  have hpreimage :
      (fun x : Fin n → ℝ => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        indicatorFunction
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) := by
    simpa [g] using (section16_indicator_precomp_eq_indicator_preimage (A := A) (D := D))
  have hEq_support :
      supportFunctionEReal
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
    simpa [hpreimage, g, section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hEq
  have hfinal :
      (supportFunctionEReal
            (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) =
          fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ∧
        ∀ xStar : Fin n → ℝ,
          sInf
                ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                      supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                  {yStar | Aadj yStar = WithLp.toLp 2 xStar}) =
              ⊤ ∨
            ∃ yStar : EuclideanSpace ℝ (Fin m),
              Aadj yStar = WithLp.toLp 2 xStar ∧
                supportFunctionEReal D (yStar : Fin m → ℝ) =
                  sInf
                    ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                          supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                      {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
    refine ⟨hEq_support, ?_⟩
    intro xStar
    have hAtt := hclosed_att'.2 xStar
    simpa [g, section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hAtt
  simpa [Aadj] using hfinal

end Section16
end Chap03
