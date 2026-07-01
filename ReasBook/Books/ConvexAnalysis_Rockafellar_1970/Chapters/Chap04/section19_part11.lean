/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part10

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.4: split a finite upper bound on `f₁ x + f₂ x`
into real upper bounds for each summand. -/
lemma helperForTheorem_19_4_splitRealUpperBound
    {n : ℕ} {f₁ f₂ : (Fin n → ℝ) → EReal}
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂)
    {x : Fin n → ℝ} {μ : ℝ}
    (hsum : f₁ x + f₂ x ≤ (μ : EReal)) :
    ∃ μ₁ μ₂ : ℝ, f₁ x ≤ (μ₁ : EReal) ∧ f₂ x ≤ (μ₂ : EReal) ∧ μ₁ + μ₂ = μ := by
  have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hf₁bot : f₁ x ≠ (⊥ : EReal) :=
    hproper₁.2.2 x hx_univ
  have hf₂bot : f₂ x ≠ (⊥ : EReal) :=
    hproper₂.2.2 x hx_univ
  exact
    helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁bot) (hb_bot := hf₂bot) (hab := hsum)

/-- Helper for Theorem 19.4: add two real-valued epigraph bounds in `EReal`. -/
lemma helperForTheorem_19_4_addUpperBounds
    {n : ℕ} {f₁ f₂ : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ₁ μ₂ : ℝ}
    (hμ₁ : f₁ x ≤ (μ₁ : EReal))
    (hμ₂ : f₂ x ≤ (μ₂ : EReal)) :
    f₁ x + f₂ x ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
  calc
    f₁ x + f₂ x ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hμ₁ hμ₂
    _ = ((μ₁ + μ₂ : ℝ) : EReal) := by simp [EReal.coe_add]

/-- Helper for Theorem 19.4: identify the `Fin.castSucc` coordinates of
`prodLinearEquiv_append_coord`. -/
lemma helperForTheorem_19_4_castSucc_coord_prodLinearEquiv_append_coord
    {n : ℕ} :
    ∀ (x0 : Fin n → ℝ) (μ0 : ℝ) (j0 : Fin n),
      x0 j0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.castSucc j0) := by
  intro x0 μ0 j0
  change x0 j0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.castSucc j0)
  change x0 j0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.castSucc j0))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) = x0 j0 := by
    exact Fin.append_left (u := x0) (v := Function.const (Fin 1) μ0) j0
  exact (happ'.trans happend).symm

/-- Helper for Theorem 19.4: identify the `Fin.last` coordinate of
`prodLinearEquiv_append_coord`. -/
lemma helperForTheorem_19_4_last_coord_prodLinearEquiv_append_coord
    {n : ℕ} :
    ∀ (x0 : Fin n → ℝ) (μ0 : ℝ),
      μ0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.last n) := by
  intro x0 μ0
  change μ0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.last n)
  change μ0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.last n))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) = μ0 := by
    change Fin.append x0 (Function.const (Fin 1) μ0) (Fin.natAdd n (0 : Fin 1)) = μ0
    exact Fin.append_right (u := x0) (v := Function.const (Fin 1) μ0) (0 : Fin 1)
  exact (happ'.trans happend).symm

/-- Theorem 19.4: If `f₁` and `f₂` are proper polyhedral convex functions, then `f₁ + f₂`
is polyhedral. -/
theorem polyhedralConvexFunction_add_of_proper
    (n : ℕ) (f₁ f₂ : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f₁ →
      IsPolyhedralConvexFunction n f₂ →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ →
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ →
            IsPolyhedralConvexFunction n (fun x => f₁ x + f₂ x) := by
  intro hf₁poly hf₂poly hproper₁ hproper₂
  refine ⟨?_, ?_⟩
  · exact convexFunctionOn_add_of_proper hproper₁ hproper₂
  · let μMap1 : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (i := Fin.natAdd n (0 : Fin 2)) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ)
    let μMap2 : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (i := Fin.natAdd n (1 : Fin 2)) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ)
    let L₁ : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          μMap1
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let L₂ : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          μMap2
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let B : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          (μMap1 + μMap2)
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let E₁ : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f₁)
    let E₂ : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f₂)
    let P : Set (Fin (n + 2) → ℝ) := (L₁ ⁻¹' E₁) ∩ (L₂ ⁻¹' E₂)
    have hE₁poly : IsPolyhedralConvexSet (n + 1) E₁ := by
      simpa [E₁, prodLinearEquiv_append_coord] using hf₁poly.2
    have hE₂poly : IsPolyhedralConvexSet (n + 1) E₂ := by
      simpa [E₂, prodLinearEquiv_append_coord] using hf₂poly.2
    have hPre₁ : IsPolyhedralConvexSet (n + 2) (L₁ ⁻¹' E₁) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) L₁).2
          E₁ hE₁poly
    have hPre₂ : IsPolyhedralConvexSet (n + 2) (L₂ ⁻¹' E₂) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) L₂).2
          E₂ hE₂poly
    have hPpoly : IsPolyhedralConvexSet (n + 2) P := by
      exact helperForTheorem_19_1_polyhedral_inter hPre₁ hPre₂
    have hImagePoly : IsPolyhedralConvexSet (n + 1) (B '' P) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) B).1
          P hPpoly
    have hcoord_castSucc :
        ∀ (x0 : Fin n → ℝ) (μ0 : ℝ) (j0 : Fin n),
          x0 j0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.castSucc j0) :=
      helperForTheorem_19_4_castSucc_coord_prodLinearEquiv_append_coord (n := n)
    have hcoord_last :
        ∀ (x0 : Fin n → ℝ) (μ0 : ℝ),
          μ0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.last n) :=
      helperForTheorem_19_4_last_coord_prodLinearEquiv_append_coord (n := n)
    have hTargetEq :
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => f₁ x + f₂ x)) =
        B '' P := by
      ext y
      constructor
      · rintro ⟨⟨x, μ⟩, hEpi, rfl⟩
        have hsum : f₁ x + f₂ x ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff (f := fun x => f₁ x + f₂ x)).1 hEpi
        rcases helperForTheorem_19_4_splitRealUpperBound
          (hproper₁ := hproper₁) (hproper₂ := hproper₂) (hsum := hsum) with
          ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
        let z : Fin (n + 2) → ℝ :=
          Fin.append x (Fin.cases μ₁ (fun _ : Fin 1 => μ₂))
        have hz_right : z (Fin.natAdd n (1 : Fin 2)) = μ₂ := by
          dsimp [z]
          simp only [Fin.append_right]
          simpa using
            (Fin.cases_succ (motive := fun _ : Fin 2 => ℝ)
              (zero := μ₁) (succ := fun _ : Fin 1 => μ₂) (i := (0 : Fin 1)))
        have hL₁z : L₁ z = prodLinearEquiv_append_coord (n := n) (x, μ₁) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₁ z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) := by
                simp [L₁, μMap1]
              _ = μ₁ := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁)) (Fin.last n) := by
                exact hcoord_last x μ₁
          · intro j
            calc
              L₁ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₁]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁)) (Fin.castSucc j) := by
                exact hcoord_castSucc x μ₁ j
        have hL₂z : L₂ z = prodLinearEquiv_append_coord (n := n) (x, μ₂) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₂ z (Fin.last n) = z (Fin.natAdd n (1 : Fin 2)) := by
                simp [L₂, μMap2]
              _ = μ₂ := hz_right
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₂)) (Fin.last n) := by
                exact hcoord_last x μ₂
          · intro j
            calc
              L₂ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₂]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₂)) (Fin.castSucc j) := by
                exact hcoord_castSucc x μ₂ j
        have hBz : B z = prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              B z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) + z (Fin.natAdd n (1 : Fin 2)) := by
                simp [B, μMap1, μMap2]
              _ = μ₁ + μ₂ := by simp [z, hz_right]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂)) (Fin.last n) := by
                exact hcoord_last x (μ₁ + μ₂)
          · intro j
            calc
              B z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [B]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂)) (Fin.castSucc j) := by
                exact hcoord_castSucc x (μ₁ + μ₂) j
        have hmemE₁ : L₁ z ∈ E₁ := by
          have hpair : prodLinearEquiv_append_coord (n := n) (x, μ₁) ∈ E₁ := by
            exact ⟨(x, μ₁), (mem_epigraph_univ_iff (f := f₁)).2 hμ₁, rfl⟩
          simpa [hL₁z] using hpair
        have hmemE₂ : L₂ z ∈ E₂ := by
          have hpair : prodLinearEquiv_append_coord (n := n) (x, μ₂) ∈ E₂ := by
            exact ⟨(x, μ₂), (mem_epigraph_univ_iff (f := f₂)).2 hμ₂, rfl⟩
          simpa [hL₂z] using hpair
        have hBy : B z = prodLinearEquiv_append_coord (n := n) (x, μ) := by
          simpa [hμsum] using hBz
        exact ⟨z, ⟨hmemE₁, hmemE₂⟩, hBy⟩
      · rintro ⟨z, hzP, hzy⟩
        rcases hzP with ⟨hz₁, hz₂⟩
        let xz : Fin n → ℝ := fun i => z (Fin.castAdd 2 i)
        let μ₁z : ℝ := z (Fin.natAdd n (0 : Fin 2))
        let μ₂z : ℝ := z (Fin.natAdd n (1 : Fin 2))
        have hL₁z : L₁ z = prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₁ z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) := by
                simp [L₁, μMap1]
              _ = μ₁z := by simp [μ₁z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z)) (Fin.last n) := by
                exact hcoord_last xz μ₁z
          · intro j
            calc
              L₁ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₁]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz μ₁z j
        have hL₂z : L₂ z = prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₂ z (Fin.last n) = z (Fin.natAdd n (1 : Fin 2)) := by
                simp [L₂, μMap2]
              _ = μ₂z := by simp [μ₂z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₂z)) (Fin.last n) := by
                exact hcoord_last xz μ₂z
          · intro j
            calc
              L₂ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₂]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₂z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz μ₂z j
        have hBz : B z = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              B z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) + z (Fin.natAdd n (1 : Fin 2)) := by
                simp [B, μMap1, μMap2]
              _ = μ₁z + μ₂z := by simp [μ₁z, μ₂z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z)) (Fin.last n) := by
                exact hcoord_last xz (μ₁z + μ₂z)
          · intro j
            calc
              B z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [B]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz (μ₁z + μ₂z) j
        have hfx₁ : f₁ xz ≤ (μ₁z : EReal) := by
          rcases hz₁ with ⟨p, hpEpi, hpEq⟩
          have hpcoord :
              prodLinearEquiv_append_coord (n := n) p =
                prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := by
            calc
              prodLinearEquiv_append_coord (n := n) p = L₁ z := hpEq
              _ = prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := hL₁z
          have hpPair : p = (xz, μ₁z) :=
            (prodLinearEquiv_append_coord (n := n)).injective hpcoord
          have hpIneq : f₁ p.1 ≤ (p.2 : EReal) :=
            (mem_epigraph_univ_iff (f := f₁)).1 hpEpi
          simpa [hpPair] using hpIneq
        have hfx₂ : f₂ xz ≤ (μ₂z : EReal) := by
          rcases hz₂ with ⟨p, hpEpi, hpEq⟩
          have hpcoord :
              prodLinearEquiv_append_coord (n := n) p =
                prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := by
            calc
              prodLinearEquiv_append_coord (n := n) p = L₂ z := hpEq
              _ = prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := hL₂z
          have hpPair : p = (xz, μ₂z) :=
            (prodLinearEquiv_append_coord (n := n)).injective hpcoord
          have hpIneq : f₂ p.1 ≤ (p.2 : EReal) :=
            (mem_epigraph_univ_iff (f := f₂)).1 hpEpi
          simpa [hpPair] using hpIneq
        have hsum_le : f₁ xz + f₂ xz ≤ ((μ₁z + μ₂z : ℝ) : EReal) := by
          exact helperForTheorem_19_4_addUpperBounds (hμ₁ := hfx₁) (hμ₂ := hfx₂)
        have hycoord : y = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := by
          calc
            y = B z := hzy.symm
            _ = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := hBz
        refine
          ⟨(xz, μ₁z + μ₂z),
            (mem_epigraph_univ_iff (f := fun x => f₁ x + f₂ x)).2 hsum_le, ?_⟩
        simp [hycoord]
    have hpoly_target_coord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => f₁ x + f₂ x)) := by
      simpa [hTargetEq] using hImagePoly
    simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Theorem 19.5: scalar multiples of a polyhedral convex set are polyhedral. -/
lemma helperForTheorem_19_5_smul_polyhedral_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    ∀ a : ℝ, IsPolyhedralConvexSet n (a • C) := by
  intro a
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    a • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have hImage : IsPolyhedralConvexSet n (A '' C) :=
    (polyhedralConvexSet_image_preimage_linear n n A).1 C hCpoly
  have hEq : a • C = A '' C := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [A]
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      simpa [A] using hxy
  simpa [hEq] using hImage

/-- Helper for Theorem 19.5: if a nonempty set is represented as a mixed convex hull,
that mixed convex hull is nonempty. -/
lemma helperForTheorem_19_5_mixedConvexHull_nonempty_of_nonempty_of_eq
    {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (hCeq : C = mixedConvexHull (n := n) S₀ S₁) :
    (mixedConvexHull (n := n) S₀ S₁).Nonempty := by
  rcases hCne with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [← hCeq] using hx

/-- Helper for Theorem 19.5: the mixed hull generated by `{0}` and `S₁` sits in the
recession cone of `mixedConvexHull S₀ S₁`. -/
lemma helperForTheorem_19_5_directionHull_subset_recessionCone_of_mixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} :
    mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ ⊆
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
  have hConv : Convex ℝ (Set.recessionCone (mixedConvexHull (n := n) S₀ S₁)) := by
    have hMixedConv : Convex ℝ (mixedConvexHull (n := n) S₀ S₁) :=
      convex_mixedConvexHull (n := n) S₀ S₁
    exact recessionCone_convex_fin (C := mixedConvexHull (n := n) S₀ S₁) hMixedConv
  have hZero : ({0} : Set (Fin n → ℝ)) ⊆ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
    intro x hx
    have hx0 : x = 0 := by
      simpa using hx
    subst hx0
    intro y hy t ht
    simpa using hy
  have hRec :
      ∀ d ∈ S₁, ∀ x ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁),
        ∀ t : ℝ, 0 ≤ t →
          x + t • d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
    intro d hd x hx t ht
    have hdRec : d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) :=
      mem_recessionCone_mixedConvexHull_of_mem_directions
        (n := n) (S₀ := S₀) (S₁ := S₁) (d := d) hd
    intro y hy s hs
    have hsx : y + s • x ∈ mixedConvexHull (n := n) S₀ S₁ :=
      hx hy hs
    have hs_nonneg : 0 ≤ s * t :=
      mul_nonneg hs ht
    have hsd : (y + s • x) + (s * t) • d ∈ mixedConvexHull (n := n) S₀ S₁ :=
      hdRec hsx hs_nonneg
    have hsd' : y + s • (x + t • d) ∈ mixedConvexHull (n := n) S₀ S₁ := by
      simpa [smul_add, smul_smul, add_assoc, add_left_comm, add_comm, mul_assoc] using hsd
    exact hsd'
  exact
    mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
      (S₀ := ({0} : Set (Fin n → ℝ)))
      (S₁ := S₁)
      (Ccand := Set.recessionCone (mixedConvexHull (n := n) S₀ S₁))
      hConv hZero hRec

/-- Helper for Theorem 19.5: a nonempty mixed convex hull must have at least one point-generator.
-/
lemma helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hMixedNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty) :
    S₀.Nonempty := by
  by_contra hS₀ne
  have hS₀empty : S₀ = (∅ : Set (Fin n → ℝ)) :=
    (Set.not_nonempty_iff_eq_empty).1 hS₀ne
  have hMixedEmpty : mixedConvexHull (n := n) S₀ S₁ = (∅ : Set (Fin n → ℝ)) := by
    simpa [hS₀empty] using (mixedConvexHull_empty_points (n := n) (S₁ := S₁))
  rcases hMixedNonempty with ⟨x, hx⟩
  have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
    rw [hMixedEmpty] at hx
    exact hx
  exact Set.notMem_empty x hxEmpty

/-- Helper for Theorem 19.5: the recession cone of `cone S₁` equals `cone S₁`. -/
lemma helperForTheorem_19_5_recessionCone_cone_eq_cone
    {n : ℕ} {S₁ : Set (Fin n → ℝ)} :
    Set.recessionCone (cone n S₁) = cone n S₁ := by
  have hcone : IsConvexCone n (cone n S₁) := by
    simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₁)] using
      (isConvexCone_convexConeGenerated (n := n) (S₁ := S₁))
  have hadd :
      ∀ x ∈ cone n S₁, ∀ y ∈ cone n S₁, x + y ∈ cone n S₁ :=
    isConvexCone_add_closed n (cone n S₁) hcone
  have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ :=
    (Set.mem_insert_iff).2 (Or.inl rfl)
  have h0cone : (0 : Fin n → ℝ) ∈ cone n S₁ := by
    exact (subset_convexHull (𝕜 := ℝ) (s := ray n S₁)) h0ray
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    have hyone : (0 : Fin n → ℝ) + (1 : ℝ) • y ∈ cone n S₁ :=
      hy (x := 0) h0cone (t := 1) (by norm_num)
    simpa using hyone
  · intro y hy x hx t ht
    by_cases ht0 : t = 0
    · subst ht0
      simpa using hx
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hty : t • y ∈ cone n S₁ := hcone.1 y hy t htpos
      exact hadd x hx (t • y) hty

/-- Helper for Theorem 19.5: with finite nonempty point-generators, the recession cone of
`conv S₀ + cone S₁` is exactly `cone S₁`. -/
lemma helperForTheorem_19_5_recessionCone_conv_add_cone_of_finite_points
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (conv S₀ + cone n S₁) = cone n S₁ := by
  classical
  let A : Set (Fin n → ℝ) := conv S₀
  let B : Set (Fin n → ℝ) := cone n S₁
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let A' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' A
  let B' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' B
  have hAne : A.Nonempty := by
    rcases hS₀ne with ⟨x, hx⟩
    have hxA : x ∈ A := by
      change x ∈ conv S₀
      exact (subset_convexHull (𝕜 := ℝ) (s := S₀)) hx
    exact ⟨x, hxA⟩
  have hAconv : Convex ℝ A := by
    simpa [A, conv] using (convex_convexHull (𝕜 := ℝ) (s := S₀))
  have hAclosed : IsClosed A := by
    simpa [A, conv] using hS₀fin.isClosed_convexHull
  have hS₀bdd : Bornology.IsBounded S₀ := hS₀fin.isBounded
  have hAbdd : Bornology.IsBounded A := by
    simpa [A, conv] using (isBounded_convexHull (s := S₀)).2 hS₀bdd
  have hArecZero : Set.recessionCone A = ({0} : Set (Fin n → ℝ)) :=
    recessionCone_eq_singleton_zero_of_closed_bounded_convex_fin
      (n := n) (C := A) hAne hAclosed hAconv hAbdd
  have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ :=
    (Set.mem_insert_iff).2 (Or.inl rfl)
  have h0B : (0 : Fin n → ℝ) ∈ B := by
    change (0 : Fin n → ℝ) ∈ cone n S₁
    exact (subset_convexHull (𝕜 := ℝ) (s := ray n S₁)) h0ray
  have hBne : B.Nonempty := ⟨0, h0B⟩
  have hBconv : Convex ℝ B := by
    simpa [B, cone, conv] using (convex_convexHull (𝕜 := ℝ) (s := ray n S₁))
  have hBclosed : IsClosed B := by
    simpa [B] using
      (helperForTheorem_19_1_isClosed_cone_of_finite_generators
        (m := n) (T := S₁) hS₁fin)
  have hBrec : Set.recessionCone B = B :=
    helperForTheorem_19_5_recessionCone_cone_eq_cone
      (n := n) (S₁ := S₁)
  have hA'ne : A'.Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hB'ne : B'.Nonempty := by
    rcases hBne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hA'conv : Convex ℝ A' := by
    simpa [A'] using hAconv.linear_image e.symm.toLinearMap
  have hB'conv : Convex ℝ B' := by
    simpa [B'] using hBconv.linear_image e.symm.toLinearMap
  have hA'closed : IsClosed A' := by
    simpa [A'] using (e.symm.toHomeomorph.isClosed_image).2 hAclosed
  have hB'closed : IsClosed B' := by
    simpa [B'] using (e.symm.toHomeomorph.isClosed_image).2 hBclosed
  have hA'recZero : Set.recessionCone A' = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    calc
      Set.recessionCone A' = e.symm '' Set.recessionCone A := by
        simpa [A'] using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := A))
      _ = e.symm '' ({0} : Set (Fin n → ℝ)) := by
        simp [hArecZero]
      _ = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        simp
  have hB'recEq : Set.recessionCone B' = B' := by
    calc
      Set.recessionCone B' = e.symm '' Set.recessionCone B := by
        simpa [B'] using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := B))
      _ = e.symm '' B := by
        simp [hBrec]
      _ = B' := rfl
  have hopp :
      ∀ z,
        z ∈ Set.recessionCone A' → -z ∈ Set.recessionCone B' → z = 0 := by
    intro z hzA _hzB
    have hz0 : z ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [hA'recZero] using hzA
    simpa [Set.mem_singleton_iff] using hz0
  have hrecAdd' : Set.recessionCone (A' + B') = Set.recessionCone A' + Set.recessionCone B' :=
    (closed_add_recessionCone_eq_of_no_opposite_recession
      (C1 := A') (C2 := B') (hC1ne := hA'ne) (hC2ne := hB'ne)
      (hC1conv := hA'conv) (hC2conv := hB'conv)
      (hC1closed := hA'closed) (hC2closed := hB'closed) (hopp := hopp)).2
  have hzero_add_rec :
      ({0} : Set (EuclideanSpace ℝ (Fin n))) + Set.recessionCone B' = Set.recessionCone B' := by
    ext z
    constructor
    · intro hz
      rcases (Set.mem_add).1 hz with ⟨u, hu, v, hv, huv⟩
      have hu0 : u = 0 := by
        simpa [Set.mem_singleton_iff] using hu
      have hzv : z = v := by
        simpa [hu0] using huv.symm
      simpa [hzv] using hv
    · intro hz
      have h0mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        simp
      have hsum : (0 : EuclideanSpace ℝ (Fin n)) + z = z := by
        simp
      exact (Set.mem_add).2 ⟨0, h0mem, z, hz, hsum⟩
  have hrecAddEqB' : Set.recessionCone (A' + B') = B' := by
    calc
      Set.recessionCone (A' + B') = Set.recessionCone A' + Set.recessionCone B' := hrecAdd'
      _ = ({0} : Set (EuclideanSpace ℝ (Fin n))) + Set.recessionCone B' := by
        simp [hA'recZero]
      _ = Set.recessionCone B' := hzero_add_rec
      _ = B' := hB'recEq
  have hsumEq : A' + B' = e.symm '' (A + B) := by
    simpa [A', B', e] using
      (euclideanEquiv_symm_image_add (n := n) (C1 := A) (C2 := B)).symm
  have hrecImageSum : Set.recessionCone (A' + B') = e.symm '' Set.recessionCone (A + B) := by
    calc
      Set.recessionCone (A' + B') = Set.recessionCone (e.symm '' (A + B)) := by
        simp [hsumEq]
      _ = e.symm '' Set.recessionCone (A + B) := by
        simpa using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := A + B))
  have himageEq : e.symm '' Set.recessionCone (A + B) = B' := by
    calc
      e.symm '' Set.recessionCone (A + B) = Set.recessionCone (A' + B') := hrecImageSum.symm
      _ = B' := hrecAddEqB'
  have hrecAB : Set.recessionCone (A + B) = B := by
    ext x
    constructor
    · intro hx
      have hxImage : e.symm x ∈ e.symm '' Set.recessionCone (A + B) := ⟨x, hx, rfl⟩
      have hxB' : e.symm x ∈ B' := by
        simpa [himageEq] using hxImage
      rcases hxB' with ⟨y, hyB, hyEq⟩
      have hyx : y = x := by
        exact e.symm.injective hyEq
      simpa [B, hyx] using hyB
    · intro hx
      have hxB' : e.symm x ∈ B' := ⟨x, hx, rfl⟩
      have hxImage : e.symm x ∈ e.symm '' Set.recessionCone (A + B) := by
        simpa [himageEq] using hxB'
      rcases hxImage with ⟨y, hyRec, hyEq⟩
      have hyx : y = x := by
        exact e.symm.injective hyEq
      simpa [hyx] using hyRec
  simpa [A, B, conv] using hrecAB

/-- Helper for Theorem 19.5: for finite mixed-hull data, every recession direction lies in the
mixed hull generated by `{0}` and the direction set. -/
lemma helperForTheorem_19_5_recessionCone_subset_directionHull_of_finiteMixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) ⊆
      mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
  have hreprPair := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
  have hrepr : mixedConvexHull (n := n) S₀ S₁ = conv S₀ + cone n S₁ :=
    hreprPair.1.trans hreprPair.2
  have hrecEq :
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) = cone n S₁ := by
    calc
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) = Set.recessionCone (conv S₀ + cone n S₁) := by
        simp [hrepr]
      _ = cone n S₁ :=
        helperForTheorem_19_5_recessionCone_conv_add_cone_of_finite_points
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hdirEq : cone n S₁ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
    simpa using (mixedConvexHull_singleton_zero_eq_cone (n := n) (T := S₁)).symm
  intro x hx
  have hxCone : x ∈ cone n S₁ := by
    simpa [hrecEq] using hx
  simpa [hdirEq] using hxCone

/-- Helper for Theorem 19.5: finite mixed-hull representations satisfy
`0⁺(mixedConvexHull S₀ S₁) = mixedConvexHull {0} S₁`. -/
lemma helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) =
      mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
  refine Set.Subset.antisymm ?_ ?_
  · exact
      helperForTheorem_19_5_recessionCone_subset_directionHull_of_finiteMixedHull
        (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  · exact
      helperForTheorem_19_5_directionHull_subset_recessionCone_of_mixedHull
        (n := n) (S₀ := S₀) (S₁ := S₁)

/-- Helper for Theorem 19.5: the recession cone of a nonempty polyhedral convex set is
polyhedral. -/
lemma helperForTheorem_19_5_recessionCone_polyhedral_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet n (Set.recessionCone C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
          (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  have hCfg : IsFinitelyGeneratedConvexSet n C :=
    (hTFAE.out 0 2).1 hCpoly
  rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
  have hMixNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty :=
    helperForTheorem_19_5_mixedConvexHull_nonempty_of_nonempty_of_eq
      (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCne hCeq
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := n) (S₀ := S₀) (S₁ := S₁) hMixNonempty
  have hRecEq :
      Set.recessionCone C = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
    calc
      Set.recessionCone C = Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
        simp [hCeq]
      _ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ :=
        helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hRecConv : Convex ℝ (Set.recessionCone C) :=
    recessionCone_convex_fin (C := C) hCconv
  have hRecFG : IsFinitelyGeneratedConvexSet n (Set.recessionCone C) := by
    refine ⟨({0} : Set (Fin n → ℝ)), S₁, ?_, hS₁fin, ?_⟩
    · simp
    · exact hRecEq
  exact
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := n) (C := Set.recessionCone C) hRecConv hRecFG

/-- Theorem 19.5: Let `C` be a non-empty polyhedral convex set. Then `λ • C` is polyhedral for
every scalar `λ`, the recession cone `0^+ C` is polyhedral, and if `C` is represented as a mixed
convex hull of a finite set of points and directions, then `0^+ C` is the mixed convex hull of
the origin together with the directions. -/
theorem polyhedralConvexSet_smul_recessionCone_and_representation
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    C.Nonempty →
    IsPolyhedralConvexSet n C →
      (∀ a : ℝ, IsPolyhedralConvexSet n (a • C)) ∧
        IsPolyhedralConvexSet n (Set.recessionCone C) ∧
        (∀ (S₀ S₁ : Set (Fin n → ℝ)),
          Set.Finite S₀ →
          Set.Finite S₁ →
          C = mixedConvexHull (n := n) S₀ S₁ →
            Set.recessionCone C =
              mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁) := by
  intro hCne hCpoly
  refine ⟨?_, ?_, ?_⟩
  · exact
      helperForTheorem_19_5_smul_polyhedral_of_polyhedral
        (n := n) (C := C) hCpoly
  · exact
      helperForTheorem_19_5_recessionCone_polyhedral_of_polyhedral
        (n := n) (C := C) hCne hCpoly
  · intro S₀ S₁ hS₀fin hS₁fin hCeq
    have hMixNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty :=
      helperForTheorem_19_5_mixedConvexHull_nonempty_of_nonempty_of_eq
        (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCne hCeq
    have hS₀ne : S₀.Nonempty :=
      helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
        (n := n) (S₀ := S₀) (S₁ := S₁) hMixNonempty
    calc
      Set.recessionCone C = Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
        simp [hCeq]
      _ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ :=
        helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne

/-- Helper for Corollary 19.5.1: polyhedrality of the transformed epigraph implies
convexity of the corresponding function. -/
lemma helperForCorollary_19_5_1_convexFunctionOn_of_polyhedralTransformedEpigraph
    {n : ℕ} {g : (Fin n → ℝ) → EReal}
    (hpoly :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) g)) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
  let e := prodLinearEquiv_append_coord (n := n)
  have hconv_image :
      Convex ℝ (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForTheorem_19_1_polyhedral_isConvex
      (n := n + 1)
      (C := e '' epigraph (Set.univ : Set (Fin n → ℝ)) g)
      hpoly
  have hconv_preimage :
      Convex ℝ (e ⁻¹' (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g)) :=
    hconv_image.linear_preimage e.toLinearMap
  have hpreimage_eq :
      e ⁻¹' (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g) =
        epigraph (Set.univ : Set (Fin n → ℝ)) g := by
    exact Set.preimage_image_eq _ e.injective
  simpa [ConvexFunctionOn, e, hpreimage_eq] using hconv_preimage

/-- Helper for Corollary 19.5.1: packaging transformed-epigraph polyhedrality as
`IsPolyhedralConvexFunction`. -/
lemma helperForCorollary_19_5_1_polyhedralConvexFunction_of_polyhedralTransformedEpigraph
    {n : ℕ} {g : (Fin n → ℝ) → EReal}
    (hpoly :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) g)) :
    IsPolyhedralConvexFunction n g := by
  refine ⟨?_, ?_⟩
  · exact
      helperForCorollary_19_5_1_convexFunctionOn_of_polyhedralTransformedEpigraph
        (n := n) (g := g) hpoly
  · simpa [prodLinearEquiv_append_coord] using hpoly

/-- Helper for Corollary 19.5.1: the recession cone of the transformed epigraph of `f`
is the transformed epigraph of `recessionFunction f`. -/
lemma helperForCorollary_19_5_1_recessionCone_transformedEpigraph_eq_transformedEpigraph_recessionFunction
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Set.recessionCone
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f)) =
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
  let g : Fin 1 → (Fin n → ℝ) → EReal := fun _ => f
  have hconv_epi :
      ∀ i : Fin 1,
        Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (g i)) := by
    intro i
    simpa [g] using
      (convex_epigraph_of_convexFunctionOn (f := f) hconv)
  have hproper_family :
      ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i) := by
    intro i
    simpa [g] using hproper
  have hk :
      ∀ (i : Fin 1) (y : Fin n → ℝ),
        recessionFunction f y =
          sSup { r : EReal | ∃ x : Fin n → ℝ, r = g i (x + y) - g i x } := by
    intro i y
    simpa [g] using
      (section16_recessionFunction_eq_sSup_unrestricted (f := f) y)
  have hrec_epi :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
    have hrec :=
      recessionCone_epigraph_eq_epigraph_k (f := g) (k := recessionFunction f)
        hconv_epi hproper_family hk
    simpa [g] using hrec (i := 0)
  let e := prodLinearEquiv_append_coord (n := n)
  calc
    Set.recessionCone (e '' epigraph (Set.univ : Set (Fin n → ℝ)) f)
        = e '' Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
          simpa [e] using
            (recessionCone_image_linearEquiv (e := e)
              (C := epigraph (Set.univ : Set (Fin n → ℝ)) f))
    _ = e '' epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
          simp [hrec_epi]

/-- Helper for Corollary 19.5.1: a proper convex function takes a non-`⊤` value. -/
lemma helperForCorollary_19_5_1_exists_nonTop_value_of_proper
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∃ x, f x ≠ (⊤ : EReal) := by
  rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hproper with
    ⟨x0, r0, hx0⟩
  refine ⟨x0, ?_⟩
  rw [hx0]
  exact EReal.coe_ne_top r0

/-- Helper for Corollary 19.5.1: positive right scalar multiples have polyhedral
transformed epigraph. -/
lemma helperForCorollary_19_5_1_transformedEpigraph_rightScalarMultiple_polyhedral_of_pos
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {lam : ℝ} (hlam : 0 < lam) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) := by
  let C : Set (Fin (n + 1) → ℝ) :=
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) f)
  have hCne : C.Nonempty := by
    rcases hproper.2.1 with ⟨p, hp⟩
    refine ⟨(prodLinearEquiv_append_coord (n := n)) p, ?_⟩
    exact ⟨p, hp, rfl⟩
  have hCpoly : IsPolyhedralConvexSet (n + 1) C := by
    simpa [C, prodLinearEquiv_append_coord] using hfpoly.2
  have hpoly_smul : IsPolyhedralConvexSet (n + 1) (lam • C) := by
    have hthm :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n + 1) (C := C) hCne hCpoly
    exact hthm.1 lam
  have hEq :
      lam • C =
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) := by
    simpa [C] using
      (smul_embedded_epigraph_eq_embedded_epigraph_rightScalarMultiple
        (f := f) (hf := hfpoly.1) (lam := lam) hlam)
  simpa [hEq] using hpoly_smul

/-- Helper for Corollary 19.5.1: the endpoint `λ = 0` gives a polyhedral
right scalar multiple. -/
lemma helperForCorollary_19_5_1_zero_scalar_case_polyhedral
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsPolyhedralConvexFunction n (rightScalarMultiple f 0) := by
  have hfinite : ∃ x, f x ≠ (⊤ : EReal) :=
    helperForCorollary_19_5_1_exists_nonTop_value_of_proper
      (n := n) (f := f) hproper
  have hzero_eq :
      rightScalarMultiple f 0 = indicatorFunction ({0} : Set (Fin n → ℝ)) :=
    rightScalarMultiple_zero_eq_indicator (f := f) hfpoly.1 hfinite
  have hzero_poly : IsPolyhedralConvexSet n ({0} : Set (Fin n → ℝ)) :=
    helperForTheorem_19_1_zero_set_polyhedral (m := n)
  have hindicator_poly :
      IsPolyhedralConvexFunction n
        (indicatorFunction ({0} : Set (Fin n → ℝ))) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
      (n := n) (C := ({0} : Set (Fin n → ℝ))) hzero_poly
  simpa [hzero_eq] using hindicator_poly

/-- Corollary 19.5.1: If `f` is a proper polyhedral convex function, then the right scalar
multiple `rightScalarMultiple f λ` is polyhedral for every `λ ≥ 0`, and the recession function
`recessionFunction f` (the case `λ = 0^+`) is polyhedral. -/
theorem polyhedralConvexFunction_rightScalarMultiple_and_recession
    (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      (∀ lam : ℝ, 0 ≤ lam → IsPolyhedralConvexFunction n (rightScalarMultiple f lam)) ∧
      IsPolyhedralConvexFunction n (recessionFunction f) := by
  intro hfpoly hproper
  refine ⟨?_, ?_⟩
  · intro lam hlam
    by_cases hlam0 : lam = 0
    · subst hlam0
      exact
        helperForCorollary_19_5_1_zero_scalar_case_polyhedral
          (n := n) (f := f) hfpoly hproper
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
      have hpoly_trans :
          IsPolyhedralConvexSet (n + 1)
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) :=
        helperForCorollary_19_5_1_transformedEpigraph_rightScalarMultiple_polyhedral_of_pos
          (n := n) (f := f) hfpoly hproper hlam_pos
      exact
        helperForCorollary_19_5_1_polyhedralConvexFunction_of_polyhedralTransformedEpigraph
          (n := n) (g := rightScalarMultiple f lam) hpoly_trans
  · let C : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f)
    have hCne : C.Nonempty := by
      rcases hproper.2.1 with ⟨p, hp⟩
      refine ⟨(prodLinearEquiv_append_coord (n := n)) p, ?_⟩
      exact ⟨p, hp, rfl⟩
    have hCpoly : IsPolyhedralConvexSet (n + 1) C := by
      simpa [C, prodLinearEquiv_append_coord] using hfpoly.2
    have hthm :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n + 1) (C := C) hCne hCpoly
    have hrec_poly : IsPolyhedralConvexSet (n + 1) (Set.recessionCone C) :=
      hthm.2.1
    have hrec_eq :
        Set.recessionCone C =
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
      simpa [C] using
        (helperForCorollary_19_5_1_recessionCone_transformedEpigraph_eq_transformedEpigraph_recessionFunction
          (n := n) (f := f) hfpoly.1 hproper)
    have hpoly_trans :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
      simpa [hrec_eq] using hrec_poly
    exact
      helperForCorollary_19_5_1_polyhedralConvexFunction_of_polyhedralTransformedEpigraph
        (n := n) (g := recessionFunction f) hpoly_trans

/-- Weighted sums using `λ i • C i` for nonzero coefficients and `0^+ C i` for zero
coefficients. -/
def weightedSumSetWithRecession
    (n m : ℕ) (C : Fin m → Set (Fin n → ℝ)) (lam : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∃ y : Fin m → Fin n → ℝ,
      (∀ i, y i ∈ (if lam i = 0 then Set.recessionCone (C i) else (lam i) • (C i))) ∧
      x = ∑ i, y i}


end Section19
end Chap19
