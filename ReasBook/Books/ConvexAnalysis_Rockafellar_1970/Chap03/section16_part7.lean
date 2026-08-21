/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section03_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part6

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Theorem 16.3.3: Let `A : ℝ^n →ₗ[ℝ] ℝ^m` be a linear transformation. For a convex function `g`
on `ℝ^m`, if there exists `x` with `A x ∈ ri (dom g)`, then the closure operation in Theorem
16.3.2 can be omitted, i.e. `(g ∘ A)^* = A^* g^*`.

Equivalently, for each `xStar`, one has

`(g ∘ A)^*(xStar) = inf { g^*(yStar) | A^* yStar = xStar }`,

and the infimum is attained (or the value is `+∞` if the affine fiber is empty). -/
theorem section16_fenchelConjugate_precomp_eq_adjoint_image_of_exists_mem_ri_effectiveDomain
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) (hg : ConvexFunction g)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) :
    let Aadj :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    ((fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
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
                      {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  have hgoal :
      ((fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
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
                        {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
    by_cases hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g
    · have hcl_precomp :
          convexFunctionClosure (fun x : Fin n → ℝ => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
            fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ) :=
        section16_convexFunctionClosure_precomp_eq_precomp_convexFunctionClosure_of_exists_mem_ri
          (A := A) (g := g) (hgproper := hgproper) hri
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
          (A := A) (g := g) hg
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
          (A := A) (g := g) (hgproper := hgproper) hri
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
      refine ⟨?_, ?_⟩
      · simpa using hEq
      · simpa using hclosed_att'.2
    · have htop :=
        section16_fenchelConjugate_precomp_eq_top_of_improper_of_exists_mem_ri
          (A := A) (g := g) hg hri hgproper
      have hprecomp :
          fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) = constPosInf n :=
        htop.1
      have hstar : fenchelConjugate m g = constPosInf m := htop.2
      have hsInf :
          ∀ xStar : Fin n → ℝ,
            sInf
                  ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                        fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                    {yStar | Aadj yStar = WithLp.toLp 2 xStar}) = ⊤ := by
        intro xStar
        have hstar' :
            ∀ yStar : EuclideanSpace ℝ (Fin m),
              fenchelConjugate m g (yStar : Fin m → ℝ) = (⊤ : EReal) := by
          intro yStar
          simpa [constPosInf] using congrArg (fun f => f (yStar : Fin m → ℝ)) hstar
        by_cases hnonempty :
            {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar}.Nonempty
        · have himage :
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar}) = {(⊤ : EReal)} := by
            ext z
            constructor
            · rintro ⟨yStar, hyStar, rfl⟩
              simp [hstar' yStar]
            · intro hz
              rcases hnonempty with ⟨y0, hy0⟩
              refine ⟨y0, hy0, ?_⟩
              simpa [hstar' y0] using hz.symm
          simp [himage]
        · have hempty :
              {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} =
                (∅ : Set _) :=
            (Set.not_nonempty_iff_eq_empty).1 hnonempty
          simp [hempty]
      have hEq :
          fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
            fun xStar : Fin n → ℝ =>
              sInf
                ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                      fenchelConjugate m g (yStar : Fin m → ℝ)) ''
                  {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
        funext xStar
        simp [hprecomp, constPosInf, hsInf xStar]
      refine ⟨hEq, ?_⟩
      intro xStar
      left
      exact hsInf xStar
  simpa [Aadj] using hgoal

/-- Text 16.0.4: Example of the conjugate of a function built from one-dimensional convex
functions and linear functionals.

Let `h : ℝⁿ → ℝ ∪ {±∞}` be given by
`h(x) = g₁(⟪a₁, x⟫) + ⋯ + gₘ(⟪aₘ, x⟫)`, where each `gᵢ` is closed proper convex on `ℝ` and
`a₁, …, aₘ ∈ ℝⁿ`. Writing `h = g ∘ A` where `A x = (⟪a₁, x⟫, …, ⟪aₘ, x⟫)` and
`g(η₁, …, ηₘ) = g₁(η₁) + ⋯ + gₘ(ηₘ)`, one has `g^*(η₁⋆, …, ηₘ⋆) = g₁^*(η₁⋆) + ⋯ + gₘ^*(ηₘ⋆)`.
Therefore `(A^* g^*)(x⋆)` is the infimum of `g₁^*(η₁⋆) + ⋯ + gₘ^*(ηₘ⋆)` over all
`(η₁⋆, …, ηₘ⋆)` such that `η₁⋆ a₁ + ⋯ + ηₘ⋆ aₘ = x⋆`.

The conjugate `h^*` is the closure of `A^* g^*` (Theorem 16.3.2). If there exists `x` with
`⟪aᵢ, x⟫ ∈ ri (dom gᵢ)` for `i = 1, …, m`, then the infimum is attained and `h^* = A^* g^*`
(Theorem 16.3.3). -/
theorem section16_fenchelConjugate_sum_inner_precomp_of_exists_mem_ri_effectiveDomain
    {n m : Nat} (a : Fin m → EuclideanSpace ℝ (Fin n)) (g1 : Fin m → ℝ → EReal)
    (hg : ConvexFunction (fun y : Fin m → ℝ => ∑ i, g1 i (y i)))
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        (((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap).comp
              (LinearMap.pi fun i => (innerSL ℝ (a i)).toLinearMap))
            x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ))
                (fun y : Fin m → ℝ => ∑ i, g1 i (y i)))) :
    let g : (Fin m → ℝ) → EReal := fun y => ∑ i, g1 i (y i)
    let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
      (((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap).comp
        (LinearMap.pi fun i => (innerSL ℝ (a i)).toLinearMap))
    let h : (Fin n → ℝ) → EReal := fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)
    let Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    ((fenchelConjugate n h =
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
                      {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
  classical
  let g : (Fin m → ℝ) → EReal := fun y => ∑ i, g1 i (y i)
  let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap).comp
      (LinearMap.pi fun i => (innerSL ℝ (a i)).toLinearMap))
  have hg' : ConvexFunction g := by
    simpa [g] using hg
  have hri' :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    simpa [g, A] using hri
  have hmain :=
    section16_fenchelConjugate_precomp_eq_adjoint_image_of_exists_mem_ri_effectiveDomain
      (A := A) (g := g) hg' hri'
  simpa [g, A] using hmain

/-- Text 16.0.5: Interpreting the identity `(g ∘ A)^* = A^* g^*` (in the case where no closure is
needed) as a `sup`/`inf` formula.

For any `xStar ∈ ℝⁿ`, one has

`sup {⟪x, xStar⟫ - g (A x) | x ∈ ℝⁿ} = inf {g^* yStar | A^* yStar = xStar}`. -/
lemma section16_sup_dotProduct_sub_precomp_eq_sInf_fenchelConjugate_fiber {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (g : (Fin m → ℝ) → EReal)
    (xStar : Fin n → ℝ)
    (hEq :
      let Aadj :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
        ((LinearMap.adjoint :
                (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                  (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
              A)
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  fenchelConjugate m g (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) :
    let Aadj :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    sSup
          (Set.range fun x : Fin n → ℝ =>
            ((dotProduct x xStar : ℝ) : EReal) - g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                fenchelConjugate m g (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
  classical
  have hEq' := (by simpa using hEq)
  have hEq_x := congrArg (fun f => f xStar) hEq'
  simpa [fenchelConjugate] using hEq_x

/-- A finite sum of `EReal` values is not `⊥` if all terms are not `⊥`. -/
lemma section16_sum_ne_bot_of_ne_bot {ι : Type*} (s : Finset ι) (b : ι → EReal)
    (hb : ∀ i ∈ s, b i ≠ ⊥) : (Finset.sum s b) ≠ ⊥ := by
  classical
  revert b hb
  refine Finset.induction_on s ?base ?step
  · intro b hb
    simp
  · intro a s ha hs b hb
    have hb_a : b a ≠ ⊥ := hb a (by simp [ha])
    have hb_s : ∀ i ∈ s, b i ≠ ⊥ := by
      intro i hi
      exact hb i (by simp [hi])
    have hs_ne_bot : Finset.sum s b ≠ ⊥ := hs b hb_s
    have hsum_ne_bot : b a + Finset.sum s b ≠ ⊥ :=
      (EReal.add_ne_bot_iff).2 ⟨hb_a, hs_ne_bot⟩
    simpa [Finset.sum_insert, ha] using hsum_ne_bot

/-- Negation distributes over finite sums of non-`⊥` `EReal` values. -/
lemma section16_neg_sum_eq_sum_neg {ι : Type*} (s : Finset ι) (b : ι → EReal)
    (hb : ∀ i ∈ s, b i ≠ ⊥) :
    -(Finset.sum s b) = Finset.sum s (fun i => -b i) := by
  classical
  revert b hb
  refine Finset.induction_on s ?base ?step
  · intro b hb
    simp
  · intro a s ha hs b hb
    have hb_a : b a ≠ ⊥ := hb a (by simp [ha])
    have hb_s : ∀ i ∈ s, b i ≠ ⊥ := by
      intro i hi
      exact hb i (by simp [hi])
    have hs_eq : -(Finset.sum s b) = Finset.sum s (fun i => -b i) := hs b hb_s
    have hs_ne_bot : Finset.sum s b ≠ ⊥ := section16_sum_ne_bot_of_ne_bot s b hb_s
    have hneg : -(b a + Finset.sum s b) = -b a - Finset.sum s b :=
      EReal.neg_add (Or.inl hb_a) (Or.inr hs_ne_bot)
    calc
      -(Finset.sum (insert a s) b) = -b a - Finset.sum s b := by
        simpa [Finset.sum_insert, ha] using hneg
      _ = -b a + -(Finset.sum s b) := by simp [sub_eq_add_neg]
      _ = -b a + Finset.sum s (fun i => -b i) := by rw [hs_eq]
      _ = Finset.sum (insert a s) (fun i => -b i) := by
        simp [Finset.sum_insert, ha]

/-- Supremum of a sum of independent variables equals the sum of suprema. -/
lemma section16_iSup_add_iSup_eq_iSup_prod {α β : Type*} (u : α → EReal) (v : β → EReal) :
    (iSup u) + (iSup v) = iSup (fun p : α × β => u p.1 + v p.2) := by
  refine le_antisymm ?h1 ?h2
  · refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases (lt_iSup_iff).1 ha with ⟨i, hi⟩
    rcases (lt_iSup_iff).1 hb with ⟨j, hj⟩
    have hle : a + b ≤ u i + v j := add_le_add (le_of_lt hi) (le_of_lt hj)
    exact le_trans hle (le_iSup (fun p : α × β => u p.1 + v p.2) ⟨i, j⟩)
  · refine iSup_le ?_
    intro p
    exact add_le_add (le_iSup u p.1) (le_iSup v p.2)

/-- Supremum over a `Fin`-indexed sum equals the sum of suprema. -/
lemma section16_iSup_fin_sum_eq_sum_iSup {n m : Nat}
    (g : Fin m → (Fin n → ℝ) → EReal) :
    iSup (fun x' : Fin m → Fin n → ℝ => ∑ i, g i (x' i)) =
      ∑ i, iSup (fun x : Fin n → ℝ => g i x) := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hsplit :
          iSup (fun x' : Fin (m + 1) → Fin n → ℝ => ∑ i, g i (x' i)) =
            iSup (fun x' : Fin (m + 1) → Fin n → ℝ =>
              g 0 (x' 0) + ∑ i : Fin m, g (Fin.succ i) (x' (Fin.succ i))) := by
        refine iSup_congr ?_
        intro x'
        simp [Fin.sum_univ_succ]
      have hpair :
          iSup (fun x' : Fin (m + 1) → Fin n → ℝ =>
              g 0 (x' 0) + ∑ i : Fin m, g (Fin.succ i) (x' (Fin.succ i))) =
            iSup (fun p : (Fin n → ℝ) × (Fin m → Fin n → ℝ) =>
              g 0 p.1 + ∑ i : Fin m, g (Fin.succ i) (p.2 i)) := by
        refine (Equiv.iSup_congr (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n → ℝ)).symm ?_)
        intro x'
        rfl
      calc
        iSup (fun x' : Fin (m + 1) → Fin n → ℝ => ∑ i, g i (x' i))
            = iSup (fun x' : Fin (m + 1) → Fin n → ℝ =>
                g 0 (x' 0) + ∑ i : Fin m, g (Fin.succ i) (x' (Fin.succ i))) := hsplit
        _ = iSup (fun p : (Fin n → ℝ) × (Fin m → Fin n → ℝ) =>
              g 0 p.1 + ∑ i : Fin m, g (Fin.succ i) (p.2 i)) := hpair
        _ = iSup (fun x : Fin n → ℝ => g 0 x) +
              iSup (fun x' : Fin m → Fin n → ℝ => ∑ i : Fin m, g (Fin.succ i) (x' i)) := by
              simpa using
                (section16_iSup_add_iSup_eq_iSup_prod
                  (u := fun x : Fin n → ℝ => g 0 x)
                  (v := fun x' : Fin m → Fin n → ℝ => ∑ i : Fin m, g (Fin.succ i) (x' i))).symm
        _ = ∑ i : Fin (m + 1), iSup (fun x : Fin n → ℝ => g i x) := by
              simp [Fin.sum_univ_succ, ih]

/-- Coercion of a real finite sum into `EReal` equals the finite sum of coercions. -/
lemma section16_coe_finset_sum {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    ((Finset.sum s b : ℝ) : EReal) = Finset.sum s (fun i => (b i : EReal)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    simp [ha, hs, EReal.coe_add]

/-- Coercion of a dot-product sum into `EReal` equals the sum of coerced dot products. -/
lemma section16_coe_sum_dotProduct_eq_sum_coe_dotProduct {n m : Nat}
    (x' : Fin m → Fin n → ℝ) (xStar : Fin n → ℝ) :
    (((∑ i, x' i ⬝ᵥ xStar) : ℝ) : EReal) =
      ∑ i, (((x' i) ⬝ᵥ xStar : ℝ) : EReal) := by
  classical
  simpa using
    (section16_coe_finset_sum (s := (Finset.univ : Finset (Fin m)))
      (b := fun i : Fin m => (x' i ⬝ᵥ xStar)))

/-- Rewrite a dot-product minus a sum as a sum of dot-product differences. -/
lemma section16_sum_dotProduct_sub_sum_eq_sum_sub {n m : Nat}
    (x' : Fin m → Fin n → ℝ) (xStar : Fin n → ℝ)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    (((∑ i, x' i) ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i (x' i) =
      ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i)) := by
  classical
  have hdot :
      (∑ i, x' i) ⬝ᵥ xStar = ∑ i, x' i ⬝ᵥ xStar := by
    simpa using
      (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
        (u := fun i : Fin m => x' i) (v := xStar))
  have hdot' :
      ((∑ i, x' i) ⬝ᵥ xStar : ℝ) = ∑ i, (x' i ⬝ᵥ xStar : ℝ) := by
    simpa using hdot
  have hcoe :
      (((∑ i, x' i) ⬝ᵥ xStar : ℝ) : EReal) =
        ∑ i, (((x' i) ⬝ᵥ xStar : ℝ) : EReal) := by
    simpa [hdot'] using
      (section16_coe_sum_dotProduct_eq_sum_coe_dotProduct
        (x' := x') (xStar := xStar))
  have hneg :
      -(∑ i, f i (x' i)) = ∑ i, -(f i (x' i)) := by
    refine section16_neg_sum_eq_sum_neg (s := (Finset.univ : Finset (Fin m)))
      (b := fun i : Fin m => f i (x' i)) ?_
    intro i hi
    have hbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f i x ≠ ⊥ := (hf i).2.2
    exact hbot (x' i) (by simp)
  have hsum :
      ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i)) =
        (∑ i, (((x' i) ⬝ᵥ xStar : ℝ) : EReal)) + ∑ i, -(f i (x' i)) := by
    simp [sub_eq_add_neg, Finset.sum_add_distrib]
  calc
    (((∑ i, x' i) ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i (x' i)
        = (((∑ i, x' i) ⬝ᵥ xStar : ℝ) : EReal) + -(∑ i, f i (x' i)) := by
            simp [sub_eq_add_neg]
    _ = (((∑ i, x' i) ⬝ᵥ xStar : ℝ) : EReal) + ∑ i, -(f i (x' i)) := by
            rw [hneg]
    _ = (∑ i, (((x' i) ⬝ᵥ xStar : ℝ) : EReal)) + ∑ i, -(f i (x' i)) := by
            simp [hcoe]
    _ = ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i)) := by
            symm
            exact hsum

/-- Theorem 16.4.1: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`. Then the Fenchel conjugate
of their infimal convolution is the sum of their Fenchel conjugates:

`(f₁ □ ⋯ □ fₘ)^* = f₁^* + ⋯ + fₘ^*`.

In this development, `f₁ □ ⋯ □ fₘ` is `infimalConvolutionFamily f`, and `fᵢ^*` is
`fenchelConjugate n (f i)`. -/
theorem section16_fenchelConjugate_infimalConvolutionFamily {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (infimalConvolutionFamily f) =
      fun xStar => ∑ i, fenchelConjugate n (f i) xStar := by
  classical
  funext xStar
  let A : (Fin m → Fin n → ℝ) → (Fin n → ℝ) := fun x' => ∑ i, x' i
  let g : (Fin m → Fin n → ℝ) → EReal :=
    fun x' => (((A x') ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i (x' i)
  have hfiber :
      ∀ x : Fin n → ℝ,
        ((x ⬝ᵥ xStar : ℝ) : EReal) - infimalConvolutionFamily f x =
          sSup (g '' {x' | A x' = x}) := by
    intro x
    have hset :
        {z : EReal | ∃ x' : Fin m → Fin n → ℝ, A x' = x ∧ z = ∑ i, f i (x' i)} =
          (fun x' => ∑ i, f i (x' i)) '' {x' | A x' = x} := by
      ext z
      constructor
      · rintro ⟨x', hx, rfl⟩
        exact ⟨x', hx, rfl⟩
      · rintro ⟨x', hx, rfl⟩
        exact ⟨x', hx, rfl⟩
    have hInf :
        infimalConvolutionFamily f x =
          sInf ((fun x' => ∑ i, f i (x' i)) '' {x' | A x' = x}) := by
      simp [infimalConvolutionFamily, hset, A]
    have hSub :
        ((x ⬝ᵥ xStar : ℝ) : EReal) - infimalConvolutionFamily f x =
          sSup ((fun x' => ((x ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i (x' i)) '' {x' | A x' = x}) := by
      simpa [hInf] using
        (section16_coeReal_sub_sInf_image_eq_sSup_image
          (S := {x' | A x' = x}) (φ := fun x' => ∑ i, f i (x' i)) (a := (x ⬝ᵥ xStar)))
    have hset' :
        ((fun x' => ((x ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i (x' i)) '' {x' | A x' = x}) =
          (g '' {x' | A x' = x}) := by
      ext z
      constructor
      · rintro ⟨x', hx, rfl⟩
        refine ⟨x', hx, ?_⟩
        have hx' : A x' = x := by simpa using hx
        simp [g, hx']
      · rintro ⟨x', hx, rfl⟩
        refine ⟨x', hx, ?_⟩
        have hx' : A x' = x := by simpa using hx
        simp [g, hx']
    simpa [hset'] using hSub
  have hrange :
      Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - infimalConvolutionFamily f x) =
        Set.range (fun x => sSup (g '' {x' | A x' = x})) := by
    ext z
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, by simp [hfiber x]⟩
  have hcollapse :
      sSup (Set.range (fun x => sSup (g '' {x' | A x' = x}))) = sSup (Set.range g) := by
    simpa using
      (section16_sSup_range_sSup_fiber_image_eq_sSup_range_total (A := A) (g := g))
  have hmain :
      fenchelConjugate n (infimalConvolutionFamily f) xStar = sSup (Set.range g) := by
    unfold fenchelConjugate
    calc
      sSup (Set.range fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - infimalConvolutionFamily f x)
          = sSup (Set.range fun x => sSup (g '' {x' | A x' = x})) := by
              simp [hrange]
      _ = sSup (Set.range g) := hcollapse
  have hrewrite :
      ∀ x' : Fin m → Fin n → ℝ,
        g x' = ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i)) := by
    intro x'
    simpa [g, A] using
      (section16_sum_dotProduct_sub_sum_eq_sum_sub (x' := x') (xStar := xStar) (f := f) (hf := hf))
  have hrange' :
      Set.range g =
        Set.range (fun x' : Fin m → Fin n → ℝ =>
          ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i))) := by
    ext z
    constructor
    · rintro ⟨x', rfl⟩
      exact ⟨x', by simp [hrewrite x']⟩
    · rintro ⟨x', rfl⟩
      exact ⟨x', by simp [hrewrite x']⟩
  calc
    fenchelConjugate n (infimalConvolutionFamily f) xStar
        = sSup (Set.range g) := hmain
    _ =
        sSup
          (Set.range fun x' : Fin m → Fin n → ℝ =>
            ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i))) := by
          simp [hrange']
    _ = iSup (fun x' : Fin m → Fin n → ℝ =>
          ∑ i, ((((x' i) ⬝ᵥ xStar : ℝ) : EReal) - f i (x' i))) := by
          simp [sSup_range]
    _ = ∑ i, iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f i x) := by
          simpa using
            (section16_iSup_fin_sum_eq_sum_iSup
              (g := fun i x => ((x ⬝ᵥ xStar : ℝ) : EReal) - f i x))
    _ = ∑ i, fenchelConjugate n (f i) xStar := by
          classical
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [fenchelConjugate_eq_iSup]

/-- The infimal convolution of indicator functions is the indicator of the Minkowski sum. -/
lemma section16_infimalConvolutionFamily_indicatorFunction_eq_indicatorFunction_sum {n m : Nat}
    (C : Fin m → Set (Fin n → ℝ)) :
    infimalConvolutionFamily (fun i => indicatorFunction (C i)) = indicatorFunction (∑ i, C i) := by
  classical
  funext x
  by_cases hx : x ∈ ∑ i, C i
  · have hx' :
        ∃ z : Fin m → Fin n → ℝ,
          (∀ i, z i ∈ C i) ∧ (∑ i, z i) = x := by
      have hx' : x ∈ ∑ i, ((1 : ℝ) • C i) := by
        simpa [one_smul] using hx
      rcases
          (mem_sum_smul_set_iff_exists_points (C := C) (w := fun _ => (1 : ℝ)) (x := x)).1 hx'
        with ⟨z, hz, hsum⟩
      refine ⟨z, hz, ?_⟩
      simpa [one_smul] using hsum.symm
    have hle :
        infimalConvolutionFamily (fun i => indicatorFunction (C i)) x ≤ (0 : EReal) := by
      unfold infimalConvolutionFamily
      refine sInf_le ?_
      rcases hx' with ⟨z, hz, hsum⟩
      refine ⟨z, hsum, ?_⟩
      simp [indicatorFunction, hz]
    have hge :
        (0 : EReal) ≤ infimalConvolutionFamily (fun i => indicatorFunction (C i)) x := by
      unfold infimalConvolutionFamily
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨x', hxsum, rfl⟩
      by_cases hmem : ∀ i, x' i ∈ C i
      · simp [indicatorFunction, hmem]
      · obtain ⟨i0, hi0⟩ := not_forall.mp hmem
        have htop : indicatorFunction (C i0) (x' i0) = (⊤ : EReal) := by
          simp [indicatorFunction, hi0]
        have hbot :
            ∀ j ∈ (Finset.univ : Finset (Fin m)),
              indicatorFunction (C j) (x' j) ≠ (⊥ : EReal) := by
          intro j hj
          by_cases hjmem : x' j ∈ C j
          · simp [indicatorFunction, hjmem]
          · simp [indicatorFunction, hjmem]
        have hsum_top :
            (∑ i, indicatorFunction (C i) (x' i)) = (⊤ : EReal) := by
          have hi0' : i0 ∈ (Finset.univ : Finset (Fin m)) := by simp
          exact
            sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
              (f := fun i => indicatorFunction (C i) (x' i)) (i := i0) hi0' htop hbot
        simp [hsum_top]
    have hEq :
        infimalConvolutionFamily (fun i => indicatorFunction (C i)) x = (0 : EReal) :=
      le_antisymm hle hge
    simpa [indicatorFunction, hx] using hEq
  · have htop_le :
        (⊤ : EReal) ≤ infimalConvolutionFamily (fun i => indicatorFunction (C i)) x := by
      unfold infimalConvolutionFamily
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨x', hxsum, rfl⟩
      have hnot : ¬ ∀ i, x' i ∈ C i := by
        intro hall
        have hx' :
            x ∈ ∑ i, ((1 : ℝ) • C i) := by
          refine
            (mem_sum_smul_set_iff_exists_points (C := C) (w := fun _ => (1 : ℝ)) (x := x)).2 ?_
          refine ⟨x', hall, ?_⟩
          simpa [one_smul] using hxsum.symm
        have hx'' : x ∈ ∑ i, C i := by
          simpa [one_smul] using hx'
        exact hx hx''
      obtain ⟨i0, hi0⟩ := not_forall.mp hnot
      have htop : indicatorFunction (C i0) (x' i0) = (⊤ : EReal) := by
        simp [indicatorFunction, hi0]
      have hbot :
          ∀ j ∈ (Finset.univ : Finset (Fin m)),
            indicatorFunction (C j) (x' j) ≠ (⊥ : EReal) := by
        intro j hj
        by_cases hjmem : x' j ∈ C j
        · simp [indicatorFunction, hjmem]
        · simp [indicatorFunction, hjmem]
      have hsum_top :
          (∑ i, indicatorFunction (C i) (x' i)) = (⊤ : EReal) := by
        have hi0' : i0 ∈ (Finset.univ : Finset (Fin m)) := by simp
        exact
          sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
            (f := fun i => indicatorFunction (C i) (x' i)) (i := i0) hi0' htop hbot
      simp [hsum_top]
    have hEq :
        infimalConvolutionFamily (fun i => indicatorFunction (C i)) x = (⊤ : EReal) :=
      le_antisymm le_top htop_le
    simpa [indicatorFunction, hx] using hEq

/-- Corollary 16.4.1.1: Let `C₁, …, Cₘ` be non-empty convex sets in `ℝⁿ`. Then the support function
`δ^*(· | C)` sends Minkowski sums to pointwise sums:

`δ^*(· | C₁ + ⋯ + Cₘ) = δ^*(· | C₁) + ⋯ + δ^*(· | Cₘ)`. -/
theorem section16_deltaStar_sum {n m : Nat} (C : Fin m → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty) :
    supportFunctionEReal (∑ i, C i) = fun xStar => ∑ i, supportFunctionEReal (C i) xStar := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i)) := by
    intro i
    exact properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C i) (hC i) (hCne i)
  have hEq :=
    section16_fenchelConjugate_infimalConvolutionFamily
      (f := fun i => indicatorFunction (C i)) hproper
  simpa [section16_infimalConvolutionFamily_indicatorFunction_eq_indicatorFunction_sum,
    section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hEq

/-- The convex-function closure of an indicator function is the indicator of the set closure. -/
lemma section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure {n : Nat}
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (hCne : C.Nonempty) :
    convexFunctionClosure (indicatorFunction C) = indicatorFunction (closure C) := by
  have hconv : ConvexFunction (indicatorFunction C) := by
    simpa [ConvexFunction] using
      (properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C) hC hCne).1
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) =
        convexFunctionClosure (indicatorFunction C) :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
      (f := indicatorFunction C) hconv
  have hclConv :
      fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) =
        clConv n (indicatorFunction C) :=
    fenchelConjugate_biconjugate_eq_clConv (n := n) (f := indicatorFunction C)
  calc
    convexFunctionClosure (indicatorFunction C) =
        fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) := by
          symm
          exact hbiconj
    _ = clConv n (indicatorFunction C) := hclConv
    _ = indicatorFunction (closure C) :=
      section13_clConv_indicatorFunction_eq_indicatorFunction_closure (C := C) hC hCne

/-- The sum of indicator functions is the indicator of the intersection. -/
lemma section16_sum_indicatorFunction_eq_indicatorFunction_iInter {n m : Nat}
    (C : Fin m → Set (Fin n → ℝ)) :
    (fun x => ∑ i, indicatorFunction (C i) x) = indicatorFunction (⋂ i, C i) := by
  classical
  funext x
  by_cases hx : x ∈ ⋂ i, C i
  · have hx' : ∀ i, x ∈ C i := by
      simpa [Set.mem_iInter] using hx
    simp [indicatorFunction, hx, hx']
  · have hnot' : ¬ ∀ i, x ∈ C i := by
      simpa [Set.mem_iInter] using hx
    obtain ⟨i0, hi0⟩ := not_forall.mp hnot'
    have htop : indicatorFunction (C i0) x = (⊤ : EReal) := by
      simp [indicatorFunction, hi0]
    have hbot :
        ∀ j ∈ (Finset.univ : Finset (Fin m)),
          indicatorFunction (C j) x ≠ (⊥ : EReal) := by
      intro j hj
      by_cases hjmem : x ∈ C j
      · simp [indicatorFunction, hjmem]
      · simp [indicatorFunction, hjmem]
    have hsum_top :
        (∑ i, indicatorFunction (C i) x) = (⊤ : EReal) := by
      have hi0' : i0 ∈ (Finset.univ : Finset (Fin m)) := by simp
      exact
        sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => indicatorFunction (C i) x) (i := i0) hi0' htop hbot
    simpa [indicatorFunction, hx] using hsum_top

/-- Corollary 16.4.1.2. Let `C₁, …, Cₘ` be non-empty convex sets in `ℝⁿ`. Then the support function
of the intersection of their closures is the convex-function closure of the infimal convolution of
the support functions:

`δ^*(· | cl C₁ ∩ ⋯ ∩ cl Cₘ) = cl (δ^*(· | C₁) ⊕ ⋯ ⊕ δ^*(· | Cₘ))`.

In this development, `δ^*` is `supportFunctionEReal`, `cl` is `convexFunctionClosure`, and `⊕` is
modeled by `infimalConvolutionFamily`. -/
theorem section16_supportFunctionEReal_iInter_closure_eq_convexFunctionClosure_infimalConvolutionFamily
    {n m : Nat} (C : Fin m → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (hCne : ∀ i, (C i).Nonempty) :
    supportFunctionEReal (⋂ i, closure (C i)) =
      convexFunctionClosure (infimalConvolutionFamily fun i => supportFunctionEReal (C i)) := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i)) := by
    intro i
    exact properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C i) (hC i) (hCne i)
  have hsum :
      (fun x => ∑ i, convexFunctionClosure (indicatorFunction (C i)) x) =
        indicatorFunction (⋂ i, closure (C i)) := by
    funext x
    have hsum' :=
      congrArg (fun g => g x)
        (section16_sum_indicatorFunction_eq_indicatorFunction_iInter (C := fun i => closure (C i)))
    have hsum'' :
        (∑ i, convexFunctionClosure (indicatorFunction (C i)) x) =
          ∑ i, indicatorFunction (closure (C i)) x := by
      classical
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hcl :=
        section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure
          (C := C i) (hC := hC i) (hCne := hCne i)
      simpa using congrArg (fun g => g x) hcl
    exact hsum''.trans hsum'
  let fStar : Fin m → (Fin n → ℝ) → EReal :=
    fun i => fenchelConjugate n (indicatorFunction (C i))
  have hproperStar :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStar i) := by
    intro i
    simpa [fStar] using
      (proper_fenchelConjugate_of_proper (n := n) (f := indicatorFunction (C i)) (hproper i))
  have hEq :
      fenchelConjugate n (infimalConvolutionFamily fStar) =
        fun xStar => ∑ i, fenchelConjugate n (fStar i) xStar := by
    simpa [fStar] using
      (section16_fenchelConjugate_infimalConvolutionFamily (f := fStar) hproperStar)
  have hconv : ∀ i, ConvexFunction (indicatorFunction (C i)) := by
    intro i
    simpa [ConvexFunction] using (hproper i).1
  have hEq1 :
      fenchelConjugate n (infimalConvolutionFamily fStar) =
        fun xStar => ∑ i, convexFunctionClosure (indicatorFunction (C i)) xStar := by
    funext xStar
    have hEq' := congrArg (fun g => g xStar) hEq
    have hsum' :
        (∑ i, fenchelConjugate n (fStar i) xStar) =
          ∑ i, convexFunctionClosure (indicatorFunction (C i)) xStar := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hbiconj :
          fenchelConjugate n (fenchelConjugate n (indicatorFunction (C i))) =
            convexFunctionClosure (indicatorFunction (C i)) :=
        section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
          (f := indicatorFunction (C i)) (hconv i)
      have hbiconj' := congrArg (fun g => g xStar) hbiconj
      simpa [fStar] using hbiconj'
    exact hEq'.trans hsum'
  have hEq2 := congrArg (fun g => fenchelConjugate n g) hEq1
  have hconvInf : ConvexFunction (infimalConvolutionFamily fStar) := by
    have hconv_on := convexFunctionOn_inf_sum_of_proper (f := fStar) hproperStar
    simpa [ConvexFunction, infimalConvolutionFamily] using hconv_on
  have hbiconjInf :
      fenchelConjugate n (fenchelConjugate n (infimalConvolutionFamily fStar)) =
        convexFunctionClosure (infimalConvolutionFamily fStar) :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
      (f := infimalConvolutionFamily fStar) hconvInf
  have hEq3 :
      convexFunctionClosure (infimalConvolutionFamily fStar) =
        fenchelConjugate n (fun xStar => ∑ i, convexFunctionClosure (indicatorFunction (C i)) xStar) := by
    simpa [hbiconjInf] using hEq2
  have hEq4 :
      convexFunctionClosure (infimalConvolutionFamily fStar) =
        fenchelConjugate n (indicatorFunction (⋂ i, closure (C i))) := by
    simpa [hsum] using hEq3
  have hEq5 :
      convexFunctionClosure (infimalConvolutionFamily fStar) =
        supportFunctionEReal (⋂ i, closure (C i)) := by
    simpa [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hEq4
  simpa [fStar, section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using
    hEq5.symm

/-- The conjugate of the infimal convolution of conjugates is the sum of closures. -/
lemma section16_fenchelConjugate_infimalConvolutionFamily_conjugates_eq_sum_closure {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) =
      fun xStar => ∑ i, convexFunctionClosure (f i) xStar := by
  classical
  let fStar : Fin m → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i)
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStar i) := by
    intro i
    simpa [fStar] using
      (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hf i))
  have hEq :
      fenchelConjugate n (infimalConvolutionFamily fStar) =
        fun xStar => ∑ i, fenchelConjugate n (fStar i) xStar :=
    section16_fenchelConjugate_infimalConvolutionFamily (f := fStar) hproper
  have hconv : ∀ i, ConvexFunction (f i) := by
    intro i
    simpa [ConvexFunction] using (hf i).1
  funext xStar
  have hEq' := congrArg (fun g => g xStar) hEq
  have hsum :
      (∑ i, fenchelConjugate n (fStar i) xStar) =
        ∑ i, convexFunctionClosure (f i) xStar := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbiconj :
        fenchelConjugate n (fenchelConjugate n (f i)) = convexFunctionClosure (f i) :=
      section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
        (f := f i) (hconv i)
    have hbiconj' := congrArg (fun g => g xStar) hbiconj
    simpa [fStar] using hbiconj'
  exact hEq'.trans hsum

/-- The infimal convolution of conjugates is a convex function. -/
lemma section16_convexFunction_infimalConvolutionFamily_conjugates {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    ConvexFunction (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
    intro i
    simpa using (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hf i))
  have hconv_on :=
    (convexFunctionOn_inf_sum_of_proper (f := fun i => fenchelConjugate n (f i)) hproper)
  simpa [ConvexFunction, infimalConvolutionFamily] using hconv_on

/-- Conjugating the sum-closure identity yields the closure statement. -/
lemma section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily_proof_step
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (fun x => ∑ i, convexFunctionClosure (f i) x) =
      convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
  classical
  let fStar : Fin m → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i)
  have hEq :
      fenchelConjugate n (infimalConvolutionFamily fStar) =
        fun xStar => ∑ i, convexFunctionClosure (f i) xStar := by
    simpa [fStar] using
      (section16_fenchelConjugate_infimalConvolutionFamily_conjugates_eq_sum_closure (f := f) hf)
  have hEq' := congrArg (fun g => fenchelConjugate n g) hEq
  have hconv : ConvexFunction (infimalConvolutionFamily fStar) := by
    simpa [fStar] using
      (section16_convexFunction_infimalConvolutionFamily_conjugates (f := f) hf)
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n (infimalConvolutionFamily fStar)) =
        convexFunctionClosure (infimalConvolutionFamily fStar) :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
      (f := infimalConvolutionFamily fStar) hconv
  have hEq'' :
      convexFunctionClosure (infimalConvolutionFamily fStar) =
        fenchelConjugate n (fun xStar => ∑ i, convexFunctionClosure (f i) xStar) := by
    simpa [hbiconj] using hEq'
  simpa [fStar] using hEq''.symm

/-- Theorem 16.4.2: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`. Then

`(cl f₁ + ⋯ + cl fₘ)^* = cl (f₁^* □ ⋯ □ fₘ^*)`.

Here `cl` is the convex-function closure `convexFunctionClosure`, `^*` is the Fenchel conjugate
`fenchelConjugate n`, the sum is pointwise (written as `∑ i`), and `□` is the infimal convolution
family `infimalConvolutionFamily`. -/
theorem section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (fun x => ∑ i, convexFunctionClosure (f i) x) =
      convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
  simpa using
    (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily_proof_step
      (f := f) hf)

/-- Under a common relative-interior point, the sum of closures equals the closure of the sum. -/
lemma section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
      convexFunctionClosure (fun x => ∑ i, f i x) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
  have hri' :
      ∃ x : EuclideanSpace ℝ (Fin n),
        ∀ i : Fin m,
          x ∈
            euclideanRelativeInterior n
              (Set.image e.symm
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    rcases hri with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    intro i
    have hx0i :
        x0 ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      (Set.mem_iInter.1 hx0) i
    have hx0i' :
        x0 ∈
          euclideanRelativeInterior n
            (e ⁻¹' effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
      simpa [e] using hx0i
    simpa [ContinuousLinearEquiv.image_symm_eq_preimage] using hx0i'
  have hclosure :
      convexFunctionClosure (fun x => ∑ i, f i x) =
        fun x => ∑ i, convexFunctionClosure (f i) x := by
    simpa [e] using
      (convexFunctionClosure_sum_eq_sum_closure (f := f) hf hri')
  simpa using hclosure.symm

end Section16
end Chap03
