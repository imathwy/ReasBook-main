/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part9

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Corollary 19.3.2: the intersection of the two split preimages is polyhedral
whenever the two source sets are polyhedral. -/
lemma helperForCorollary_19_3_2_polyhedral_preimage_intersection
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (A₁ A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hC₁ : IsPolyhedralConvexSet n C₁)
    (hC₂ : IsPolyhedralConvexSet n C₂) :
    IsPolyhedralConvexSet (n + n) ((A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)) := by
  have hPre₁ : IsPolyhedralConvexSet (n + n) (A₁ ⁻¹' C₁) := by
    exact
      (polyhedralConvexSet_image_preimage_linear (n + n) n A₁).2 C₁ hC₁
  have hPre₂ : IsPolyhedralConvexSet (n + n) (A₂ ⁻¹' C₂) := by
    exact
      (polyhedralConvexSet_image_preimage_linear (n + n) n A₂).2 C₂ hC₂
  exact
    helperForTheorem_19_1_polyhedral_inter
      (hC := hPre₁) (hD := hPre₂)

/-- Helper for Corollary 19.3.2: a linear image of a polyhedral carrier in
`Fin (n+n) → ℝ` is polyhedral in `Fin n → ℝ`. -/
lemma helperForCorollary_19_3_2_image_polyhedral_of_polyhedralCarrier
    {n : ℕ}
    (B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (P : Set (Fin (n + n) → ℝ))
    (hPpoly : IsPolyhedralConvexSet (n + n) P) :
    IsPolyhedralConvexSet n (B '' P) := by
  exact
    (polyhedralConvexSet_image_preimage_linear (n + n) n B).1 P hPpoly

/-- Helper for Corollary 19.3.2: split projections recover the two components from
`Fin.append`. -/
lemma helperForCorollary_19_3_2_append_split_projection_eval
    {n : ℕ} (u v : Fin n → ℝ) :
    (LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
        (Fin.append u v) = u) ∧
      (LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
          (Fin.append u v) = v) := by
  constructor
  · funext i
    change Fin.append u v (Fin.castAdd n i) = u i
    exact Fin.append_left (u := u) (v := v) i
  · funext i
    change Fin.append u v (Fin.natAdd n i) = v i
    exact Fin.append_right (u := u) (v := v) i

/-- Helper for Corollary 19.3.2: appending witnesses from C₁ and C₂ produces a point
in the split-preimage intersection carrier. -/
lemma helperForCorollary_19_3_2_append_mem_split_preimage_intersection
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (A₁ A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hA₁ :
      A₁ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (hA₂ :
      A₂ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (u v : Fin n → ℝ)
    (hu : u ∈ C₁) (hv : v ∈ C₂) :
    Fin.append u v ∈ (A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂) := by
  have hSplit :
      (LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
          (Fin.append u v) = u) ∧
        (LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
            (Fin.append u v) = v) :=
    helperForCorollary_19_3_2_append_split_projection_eval (n := n) (u := u) (v := v)
  have hA₁append : A₁ (Fin.append u v) = u := by
    simpa [hA₁] using hSplit.1
  have hA₂append : A₂ (Fin.append u v) = v := by
    simpa [hA₂] using hSplit.2
  refine ⟨?_, ?_⟩
  · simpa [hA₁append] using hu
  · simpa [hA₂append] using hv

/-- Helper for Corollary 19.3.2: the split-sum linear image of the split-preimage carrier is
exactly the Minkowski sum `C₁ + C₂`. -/
lemma helperForCorollary_19_3_2_sumMap_image_eq_setAdd
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (A₁ A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hA₁ :
      A₁ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (hA₂ :
      A₂ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (hB : B = A₁ + A₂) :
    B '' ((A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)) = C₁ + C₂ := by
  subst hB
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hzP, hzy⟩
    rcases hzP with ⟨hz₁, hz₂⟩
    change y ∈ Set.image2 (· + ·) C₁ C₂
    refine ⟨A₁ z, hz₁, A₂ z, hz₂, ?_⟩
    simpa [LinearMap.add_apply] using hzy
  · intro hy
    change y ∈ Set.image2 (· + ·) C₁ C₂ at hy
    rcases hy with ⟨u, hu, v, hv, rfl⟩
    have hPair : Fin.append u v ∈ (A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂) :=
      helperForCorollary_19_3_2_append_mem_split_preimage_intersection
        (C₁ := C₁) (C₂ := C₂) (A₁ := A₁) (A₂ := A₂) hA₁ hA₂ u v hu hv
    have hSplit :
        (LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
            (Fin.append u v) = u) ∧
          (LinearMap.pi (fun i : Fin n =>
            (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
              (Fin.append u v) = v) :=
      helperForCorollary_19_3_2_append_split_projection_eval (n := n) (u := u) (v := v)
    have hA₁append : A₁ (Fin.append u v) = u := by
      simpa [hA₁] using hSplit.1
    have hA₂append : A₂ (Fin.append u v) = v := by
      simpa [hA₂] using hSplit.2
    refine ⟨Fin.append u v, hPair, ?_⟩
    change (A₁ + A₂) (Fin.append u v) = u + v
    simp [LinearMap.add_apply, hA₁append, hA₂append]

/-- Corollary 19.3.2: If `C₁` and `C₂` are polyhedral convex sets in `ℝ^n`, then `C₁ + C₂`
is polyhedral. -/
theorem polyhedral_convexSet_add
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C₁ →
      IsPolyhedralConvexSet n C₂ →
        IsPolyhedralConvexSet n (C₁ + C₂) := by
  intro hC₁ hC₂
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let P : Set (Fin (n + n) → ℝ) := (A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A₁ + A₂
  have hA₁ :
      A₁ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)) := rfl
  have hA₂ :
      A₂ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)) := rfl
  have hB : B = A₁ + A₂ := rfl
  have hPpoly : IsPolyhedralConvexSet (n + n) P := by
    simpa [P] using
      helperForCorollary_19_3_2_polyhedral_preimage_intersection
        (n := n) (C₁ := C₁) (C₂ := C₂) A₁ A₂ hC₁ hC₂
  have hImagePoly : IsPolyhedralConvexSet n (B '' P) := by
    exact
      helperForCorollary_19_3_2_image_polyhedral_of_polyhedralCarrier
        (n := n) (B := B) (P := P) hPpoly
  have hImageEq : B '' P = C₁ + C₂ := by
    simpa [P] using
      helperForCorollary_19_3_2_sumMap_image_eq_setAdd
        (n := n) (C₁ := C₁) (C₂ := C₂) A₁ A₂ B hA₁ hA₂ hB
  simpa [hImageEq] using hImagePoly

/-- Helper for Corollary 19.3.3: polyhedral convexity of each set implies convexity of both. -/
lemma helperForCorollary_19_3_3_polyhedral_implies_convex_pair
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂poly : IsPolyhedralConvexSet n C₂) :
    Convex ℝ C₁ ∧ Convex ℝ C₂ := by
  exact ⟨
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C₁) hC₁poly,
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C₂) hC₂poly
  ⟩

/-- Helper for Corollary 19.3.3: negation preserves polyhedral convexity. -/
lemma helperForCorollary_19_3_3_neg_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet n (-C) := by
  have hpre :
      IsPolyhedralConvexSet n
        (((-LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⁻¹' C)) :=
    (polyhedralConvexSet_image_preimage_linear n n
      (-LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).2 C hCpoly
  simpa using hpre

/-- Helper for Corollary 19.3.3: the set difference `C₁ - C₂` is polyhedral and closed. -/
lemma helperForCorollary_19_3_3_sub_polyhedral_closed
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂poly : IsPolyhedralConvexSet n C₂) :
    IsPolyhedralConvexSet n (C₁ - C₂) ∧ IsClosed (C₁ - C₂) := by
  have hnegC₂poly : IsPolyhedralConvexSet n (-C₂) :=
    helperForCorollary_19_3_3_neg_polyhedral (n := n) (C := C₂) hC₂poly
  have hsubPoly : IsPolyhedralConvexSet n (C₁ - C₂) := by
    have hadd : IsPolyhedralConvexSet n (C₁ + (-C₂)) :=
      polyhedral_convexSet_add n C₁ (-C₂) hC₁poly hnegC₂poly
    simpa [set_sub_eq_add_neg] using hadd
  have hsubClosed : IsClosed (C₁ - C₂) :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C₁ - C₂) hsubPoly
  exact ⟨hsubPoly, hsubClosed⟩

/-- Helper for Corollary 19.3.3: disjointness excludes `0` from the set difference `C₁ - C₂`. -/
lemma helperForCorollary_19_3_3_zero_not_mem_sub_of_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hdisj : Disjoint C₁ C₂) :
    (0 : Fin n → ℝ) ∉ (C₁ - C₂) := by
  exact zero_not_mem_sub_of_disjoint (hdisj := hdisj)

/-- Helper for Corollary 19.3.3: disjointness and closedness of `C₁ - C₂` force
`0 ∉ closure (C₁ - C₂)`. -/
lemma helperForCorollary_19_3_3_zero_not_mem_closure_sub
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hdisj : Disjoint C₁ C₂)
    (hSubClosed : IsClosed (C₁ - C₂)) :
    (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) := by
  have h0notSub : (0 : Fin n → ℝ) ∉ (C₁ - C₂) :=
    helperForCorollary_19_3_3_zero_not_mem_sub_of_disjoint
      (n := n) (C₁ := C₁) (C₂ := C₂) hdisj
  simpa [hSubClosed.closure_eq] using h0notSub

/-- Helper for Corollary 19.3.3: the Theorem 11.4 criterion yields a strongly separating
hyperplane from `0 ∉ closure (C₁ - C₂)`. -/
lemma helperForCorollary_19_3_3_apply_strongSeparation_iff
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty)
    (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁)
    (hC₂conv : Convex ℝ C₂)
    (h0notClosure : (0 : Fin n → ℝ) ∉ closure (C₁ - C₂)) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := by
  exact
    (exists_hyperplaneSeparatesStrongly_iff_zero_not_mem_closure_sub
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hC₁conv hC₂conv).2
      h0notClosure

/-- Corollary 19.3.3: If `C₁` and `C₂` are non-empty disjoint polyhedral convex sets, there exists
a hyperplane separating `C₁` and `C₂` strongly. -/
theorem exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ)) :
    C₁.Nonempty →
      C₂.Nonempty →
        Disjoint C₁ C₂ →
          IsPolyhedralConvexSet n C₁ →
            IsPolyhedralConvexSet n C₂ →
              ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := by
  intro hC₁ne hC₂ne hdisj hC₁poly hC₂poly
  have hconvPair : Convex ℝ C₁ ∧ Convex ℝ C₂ :=
    helperForCorollary_19_3_3_polyhedral_implies_convex_pair
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁poly hC₂poly
  have hSubClosed : IsClosed (C₁ - C₂) :=
    (helperForCorollary_19_3_3_sub_polyhedral_closed
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁poly hC₂poly).2
  have h0notClosure : (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) :=
    helperForCorollary_19_3_3_zero_not_mem_closure_sub
      (n := n) (C₁ := C₁) (C₂ := C₂) hdisj hSubClosed
  exact
    helperForCorollary_19_3_3_apply_strongSeparation_iff
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hconvPair.1 hconvPair.2 h0notClosure

/-- Helper for Corollary 19.3.4: `infimalConvolution` is an image-under-linear-map infimum for
the split-coordinate sum map. -/
lemma helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
  intro A₁ A₂ B h
  funext x
  have hSetEq :
      {z : EReal | ∃ x' : Fin (n + n) → ℝ, B x' = x ∧ z = h x'} =
        {z : EReal |
          ∃ x₁ x₂ : Fin n → ℝ,
            x₁ + x₂ = x ∧ z = f₁ x₁ + f₂ x₂} := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x', hx', rfl⟩
      refine ⟨A₁ x', A₂ x', ?_, ?_⟩
      · simpa [B, LinearMap.add_apply] using hx'
      · rfl
    · intro hz
      rcases hz with ⟨x₁, x₂, hxsum, rfl⟩
      refine ⟨Fin.append x₁ x₂, ?_, ?_⟩
      · have hA₁ : A₁ (Fin.append x₁ x₂) = x₁ := by
          funext i
          change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
          exact Fin.append_left (u := x₁) (v := x₂) i
        have hA₂ : A₂ (Fin.append x₁ x₂) = x₂ := by
          funext i
          change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
          exact Fin.append_right (u := x₁) (v := x₂) i
        calc
          B (Fin.append x₁ x₂) = A₁ (Fin.append x₁ x₂) + A₂ (Fin.append x₁ x₂) := by
              simp [B, LinearMap.add_apply]
          _ = x₁ + x₂ := by simp [hA₁, hA₂]
          _ = x := hxsum
      · have hA₁ : A₁ (Fin.append x₁ x₂) = x₁ := by
          funext i
          change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
          exact Fin.append_left (u := x₁) (v := x₂) i
        have hA₂ : A₂ (Fin.append x₁ x₂) = x₂ := by
          funext i
          change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
          exact Fin.append_right (u := x₁) (v := x₂) i
        simp [h, hA₁, hA₂]
  simp [imageUnderLinearMap, infimalConvolution, hSetEq]

/-- Helper for Corollary 19.3.4: split a finite real upper bound on `a + b` into real upper
bounds on each summand, assuming neither summand is `⊥`. -/
lemma helperForCorollary_19_3_4_realSplit_of_sum_le_coe
    {a b : EReal} {μ : ℝ}
    (ha_bot : a ≠ (⊥ : EReal))
    (hb_bot : b ≠ (⊥ : EReal))
    (hab : a + b ≤ (μ : EReal)) :
    ∃ μ₁ μ₂ : ℝ,
      a ≤ (μ₁ : EReal) ∧
      b ≤ (μ₂ : EReal) ∧
      μ₁ + μ₂ = μ := by
  have ha_top : a ≠ (⊤ : EReal) := by
    intro ha
    have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
      have hsum_top : a + b = (⊤ : EReal) := by
        calc
          a + b = (⊤ : EReal) + b := by simp [ha]
          _ = (⊤ : EReal) := EReal.top_add_of_ne_bot hb_bot
      have hab' := hab
      rw [hsum_top] at hab'
      exact hab'
    have hμ_top : (μ : EReal) = (⊤ : EReal) := top_unique htop_le
    exact (EReal.coe_ne_top μ) hμ_top
  have hb_top : b ≠ (⊤ : EReal) := by
    intro hb
    have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
      have hsum_top : a + b = (⊤ : EReal) := by
        calc
          a + b = a + (⊤ : EReal) := by simp [hb]
          _ = (⊤ : EReal) := EReal.add_top_of_ne_bot ha_bot
      have hab' := hab
      rw [hsum_top] at hab'
      exact hab'
    have hμ_top : (μ : EReal) = (⊤ : EReal) := top_unique htop_le
    exact (EReal.coe_ne_top μ) hμ_top
  have ha_coe : ((a.toReal : ℝ) : EReal) = a := EReal.coe_toReal ha_top ha_bot
  have hb_coe : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hb_top hb_bot
  have hab_coe :
      ((a.toReal + b.toReal : ℝ) : EReal) ≤ (μ : EReal) := by
    calc
      ((a.toReal + b.toReal : ℝ) : EReal)
          = ((a.toReal : ℝ) : EReal) + ((b.toReal : ℝ) : EReal) := by
              simp [EReal.coe_add]
      _ = a + b := by simp [ha_coe, hb_coe]
      _ ≤ (μ : EReal) := hab
  have hab_real : a.toReal + b.toReal ≤ μ := (EReal.coe_le_coe_iff).1 hab_coe
  refine ⟨a.toReal, μ - a.toReal, ?_, ?_, by ring⟩
  · simp [ha_coe]
  · have hb_real : b.toReal ≤ μ - a.toReal := by linarith [hab_real]
    have hb_le_coe :
        ((b.toReal : ℝ) : EReal) ≤ ((μ - a.toReal : ℝ) : EReal) :=
      (EReal.coe_le_coe_iff).2 hb_real
    simpa [hb_coe] using hb_le_coe

/-- Helper for Corollary 19.3.4: the transformed projected epigraph of the split-sum model equals
the Minkowski sum of the transformed epigraphs of `f₁` and `f₂`. -/
lemma helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    ((fun p => prodLinearEquiv_append (n := n) p) ''
      ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
  intro A₁ A₂ B h
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨⟨z, μ⟩, hp, hpq⟩
    have hz_le : h z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
    have hA₁_univ : A₁ z ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hA₂_univ : A₂ z ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hf₁_bot : f₁ (A₁ z) ≠ (⊥ : EReal) := hproper₁.2.2 (A₁ z) hA₁_univ
    have hf₂_bot : f₂ (A₂ z) ≠ (⊥ : EReal) := hproper₂.2.2 (A₂ z) hA₂_univ
    have hz_split : f₁ (A₁ z) + f₂ (A₂ z) ≤ (μ : EReal) := by
      simpa [h] using hz_le
    rcases helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁_bot) (hb_bot := hf₂_bot) (hab := hz_split)
      with ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
    refine ⟨prodLinearEquiv_append (n := n) (A₁ z, μ₁), ?_,
      prodLinearEquiv_append (n := n) (A₂ z, μ₂), ?_, ?_⟩
    · refine ⟨(A₁ z, μ₁), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := f₁)).2 hμ₁
    · refine ⟨(A₂ z, μ₂), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := f₂)).2 hμ₂
    · have hpair : linearMap_prod B (z, μ) = (A₁ z, μ₁) + (A₂ z, μ₂) := by
        ext <;> simp [linearMap_prod, B, LinearMap.add_apply, hμsum]
      have hq_sum :
          prodLinearEquiv_append (n := n) q =
            prodLinearEquiv_append (n := n) (A₁ z, μ₁) +
              prodLinearEquiv_append (n := n) (A₂ z, μ₂) := by
        calc
          prodLinearEquiv_append (n := n) q
              = prodLinearEquiv_append (n := n) (linearMap_prod B (z, μ)) := by
                  simp [hpq]
          _ = prodLinearEquiv_append (n := n) ((A₁ z, μ₁) + (A₂ z, μ₂)) := by
                simp [hpair]
          _ = prodLinearEquiv_append (n := n) (A₁ z, μ₁) +
                prodLinearEquiv_append (n := n) (A₂ z, μ₂) := by
                simpa using
                  (prodLinearEquiv_append (n := n)).map_add (A₁ z, μ₁) (A₂ z, μ₂)
      exact hq_sum.symm
  · rintro ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    rcases hy₁ with ⟨⟨x₁, μ₁⟩, hp₁, rfl⟩
    rcases hy₂ with ⟨⟨x₂, μ₂⟩, hp₂, rfl⟩
    have hx₁_le : f₁ x₁ ≤ (μ₁ : EReal) := by
      simpa using (mem_epigraph_univ_iff (f := f₁)).1 hp₁
    have hx₂_le : f₂ x₂ ≤ (μ₂ : EReal) := by
      simpa using (mem_epigraph_univ_iff (f := f₂)).1 hp₂
    let z : Fin (n + n) → ℝ := Fin.append x₁ x₂
    have hA₁ : A₁ z = x₁ := by
      funext i
      change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
      exact Fin.append_left (u := x₁) (v := x₂) i
    have hA₂ : A₂ z = x₂ := by
      funext i
      change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
      exact Fin.append_right (u := x₁) (v := x₂) i
    have hz_le : h z ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
      calc
        h z = f₁ (A₁ z) + f₂ (A₂ z) := by
          simp [h]
        _ = f₁ x₁ + f₂ x₂ := by
          simp [hA₁, hA₂]
        _ ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hx₁_le hx₂_le
        _ = ((μ₁ + μ₂ : ℝ) : EReal) := by
          simp [EReal.coe_add]
    refine ⟨linearMap_prod B (z, μ₁ + μ₂), ?_, ?_⟩
    · refine ⟨(z, μ₁ + μ₂), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := h)).2 hz_le
    · calc
        prodLinearEquiv_append (n := n) (linearMap_prod B (z, μ₁ + μ₂))
            = prodLinearEquiv_append (n := n) (B z, μ₁ + μ₂) := by
                simp [linearMap_prod]
        _ = prodLinearEquiv_append (n := n) (x₁ + x₂, μ₁ + μ₂) := by
              have hBz : B z = x₁ + x₂ := by
                simp [B, LinearMap.add_apply, hA₁, hA₂]
              simp [hBz]
        _ = prodLinearEquiv_append (n := n) ((x₁, μ₁) + (x₂, μ₂)) := by
              rfl
        _ = prodLinearEquiv_append (n := n) (x₁, μ₁) +
              prodLinearEquiv_append (n := n) (x₂, μ₂) := by
              simpa using
                (prodLinearEquiv_append (n := n)).map_add (x₁, μ₁) (x₂, μ₂)

/-- Helper for Corollary 19.3.4: coordinate version of
`helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum`. -/
lemma helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
  intro A₁ A₂ B h
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨⟨z, μ⟩, hp, hpq⟩
    have hz_le : h z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
    have hA₁_univ : A₁ z ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hA₂_univ : A₂ z ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hf₁_bot : f₁ (A₁ z) ≠ (⊥ : EReal) := hproper₁.2.2 (A₁ z) hA₁_univ
    have hf₂_bot : f₂ (A₂ z) ≠ (⊥ : EReal) := hproper₂.2.2 (A₂ z) hA₂_univ
    have hz_split : f₁ (A₁ z) + f₂ (A₂ z) ≤ (μ : EReal) := by simpa [h] using hz_le
    rcases helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁_bot) (hb_bot := hf₂_bot) (hab := hz_split)
      with ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
    refine ⟨prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁), ?_,
      prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂), ?_, ?_⟩
    · refine ⟨(A₁ z, μ₁), (mem_epigraph_univ_iff (f := f₁)).2 hμ₁, rfl⟩
    · refine ⟨(A₂ z, μ₂), (mem_epigraph_univ_iff (f := f₂)).2 hμ₂, rfl⟩
    · have hpair : linearMap_prod B (z, μ) = (A₁ z, μ₁) + (A₂ z, μ₂) := by
        ext <;> simp [linearMap_prod, B, LinearMap.add_apply, hμsum]
      have hq_sum :
          prodLinearEquiv_append_coord (n := n) q =
            prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁) +
              prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂) := by
        calc
          prodLinearEquiv_append_coord (n := n) q
              = prodLinearEquiv_append_coord (n := n) (linearMap_prod B (z, μ)) := by
                  simp [hpq]
          _ = prodLinearEquiv_append_coord (n := n) ((A₁ z, μ₁) + (A₂ z, μ₂)) := by
                simp [hpair]
          _ = prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁) +
                prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂) := by
                simpa using
                  (prodLinearEquiv_append_coord (n := n)).map_add (A₁ z, μ₁) (A₂ z, μ₂)
      exact hq_sum.symm
  · rintro ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    rcases hy₁ with ⟨⟨x₁, μ₁⟩, hp₁, rfl⟩
    rcases hy₂ with ⟨⟨x₂, μ₂⟩, hp₂, rfl⟩
    have hx₁_le : f₁ x₁ ≤ (μ₁ : EReal) := by simpa using (mem_epigraph_univ_iff (f := f₁)).1 hp₁
    have hx₂_le : f₂ x₂ ≤ (μ₂ : EReal) := by simpa using (mem_epigraph_univ_iff (f := f₂)).1 hp₂
    let z : Fin (n + n) → ℝ := Fin.append x₁ x₂
    have hA₁ : A₁ z = x₁ := by
      funext i
      change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
      exact Fin.append_left (u := x₁) (v := x₂) i
    have hA₂ : A₂ z = x₂ := by
      funext i
      change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
      exact Fin.append_right (u := x₁) (v := x₂) i
    have hz_le : h z ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
      calc
        h z = f₁ (A₁ z) + f₂ (A₂ z) := by simp [h]
        _ = f₁ x₁ + f₂ x₂ := by simp [hA₁, hA₂]
        _ ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hx₁_le hx₂_le
        _ = ((μ₁ + μ₂ : ℝ) : EReal) := by simp [EReal.coe_add]
    refine ⟨linearMap_prod B (z, μ₁ + μ₂), ?_, ?_⟩
    · refine ⟨(z, μ₁ + μ₂), (mem_epigraph_univ_iff (f := h)).2 hz_le, rfl⟩
    · calc
        prodLinearEquiv_append_coord (n := n) (linearMap_prod B (z, μ₁ + μ₂))
            = prodLinearEquiv_append_coord (n := n) (B z, μ₁ + μ₂) := by simp [linearMap_prod]
        _ = prodLinearEquiv_append_coord (n := n) (x₁ + x₂, μ₁ + μ₂) := by
              have hBz : B z = x₁ + x₂ := by simp [B, LinearMap.add_apply, hA₁, hA₂]
              simp [hBz]
        _ = prodLinearEquiv_append_coord (n := n) ((x₁, μ₁) + (x₂, μ₂)) := by rfl
        _ = prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
              prodLinearEquiv_append_coord (n := n) (x₂, μ₂) := by
              simpa using
                (prodLinearEquiv_append_coord (n := n)).map_add (x₁, μ₁) (x₂, μ₂)

/-- Helper for Corollary 19.3.4: the projected epigraph of the split-sum model is closed, via
its transformed description as a sum of transformed polyhedral epigraphs. -/
lemma helperForCorollary_19_3_4_projectedEpigraph_closed
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
  intro A₁ A₂ B h
  have hEq_coord :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) :=
    helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
      (f₁ := f₁) (f₂ := f₂) (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hpoly₁_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) := by
    simpa [prodLinearEquiv_append_coord] using hf₁poly.2
  have hpoly₂_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂) := by
    simpa [prodLinearEquiv_append_coord] using hf₂poly.2
  have hpoly_sum_coord :
      IsPolyhedralConvexSet (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      polyhedral_convexSet_add (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁))
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂))
        hpoly₁_coord hpoly₂_coord
  have hclosed_sum_coord :
      IsClosed
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n + 1)
      (C :=
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)))
      hpoly_sum_coord).1
  have hclosed_transformed_coord :
      IsClosed
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
    simpa [hEq_coord] using hclosed_sum_coord
  let hhome := ((prodLinearEquiv_append_coord (n := n)).toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed_homeomorphImage :
      IsClosed
        ((hhome : ((Fin n → ℝ) × ℝ) → (Fin (n + 1) → ℝ)) ''
          ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using
      hclosed_transformed_coord
  exact
    (hhome.isClosed_image
      (s := (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)).1
      hclosed_homeomorphImage

/-- Helper for Corollary 19.3.4: the transformed epigraph of `infimalConvolution f₁ f₂` is
polyhedral, obtained from the closed projected-epigraph identity and the transformed sum
description. -/
lemma helperForCorollary_19_3_4_polyhedralEpigraph_infimalConvolution
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    A₁ + A₂
  let h : (Fin (n + n) → ℝ) → EReal :=
    fun z => f₁ (A₁ z) + f₂ (A₂ z)
  have hclosed_proj :
      IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
    exact
      helperForCorollary_19_3_4_projectedEpigraph_closed
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hEq_epi :
      epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) =
        (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := B) (h := h) hclosed_proj)
  have hImageEqInf : imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
    exact
      helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution
        (f₁ := f₁) (f₂ := f₂)
  have hEq_sum :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
        (f₁ := f₁) (f₂ := f₂) (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hpoly₁ :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) :=
    by simpa [prodLinearEquiv_append_coord] using hf₁poly.2
  have hpoly₂ :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂) :=
    by simpa [prodLinearEquiv_append_coord] using hf₂poly.2
  have hpoly_sum :
      IsPolyhedralConvexSet (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      polyhedral_convexSet_add (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁))
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂))
        hpoly₁ hpoly₂
  have htarget_eq :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    calc
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂))
          = ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h)) := by
                simp [hImageEqInf]
      _ = ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
              simp [hEq_epi]
      _ = (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := hEq_sum
  have hpoly_target_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
    simpa [htarget_eq] using hpoly_sum
  simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Corollary 19.3.4: isolate the first summand in an equality
`u + v = x` as `u = x - v`. -/
lemma helperForCorollary_19_3_4_eq_sub_of_add_eq
    {n : ℕ} {u v x : Fin n → ℝ}
    (h : u + v = x) :
    u = x - v := by
  have hsub := congrArg (fun t : Fin n → ℝ => t - v) h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub

/-- Helper for Corollary 19.3.4: when the infimal-convolution value at `x` is finite, the
infimum is attained by some `y`. -/
lemma helperForCorollary_19_3_4_attainment_of_finite_value
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂)
    (x : Fin n → ℝ) {r : ℝ}
    (hr : infimalConvolution f₁ f₂ x = (r : EReal)) :
    ∃ y : Fin n → ℝ, infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y := by
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    A₁ + A₂
  let h : (Fin (n + n) → ℝ) → EReal :=
    fun z => f₁ (A₁ z) + f₂ (A₂ z)
  have hclosed_proj : IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
    exact
      helperForCorollary_19_3_4_projectedEpigraph_closed
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hEq_epi_image :
      epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) =
        (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := B) (h := h) hclosed_proj)
  have hImageEqInf : imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
    exact helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution (f₁ := f₁) (f₂ := f₂)
  have hr_image : imageUnderLinearMap B h x = (r : EReal) := by
    calc
      imageUnderLinearMap B h x = infimalConvolution f₁ f₂ x := by
        simp [hImageEqInf]
      _ = (r : EReal) := hr
  have hmem_epi :
      (x, r) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) := by
    refine (mem_epigraph_univ_iff (f := imageUnderLinearMap B h)).2 ?_
    simp [hr_image]
  have hmem_image :
      (x, r) ∈ (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [hEq_epi_image] using hmem_epi
  have hz_exists :
      ∃ z : Fin (n + n) → ℝ, B z = x ∧ h z ≤ (r : EReal) := by
    simpa [image_epigraph_linearMap_eq (A := B) (h := h)] using hmem_image
  rcases hz_exists with ⟨z, hzB, hzle⟩
  have hsInf_le_hz : imageUnderLinearMap B h x ≤ h z := by
    have hz_mem_set :
        h z ∈ {w : EReal | ∃ z' : Fin (n + n) → ℝ, B z' = x ∧ w = h z'} := by
      exact ⟨z, hzB, rfl⟩
    simpa [imageUnderLinearMap] using sInf_le hz_mem_set
  have hhz_le_image : h z ≤ imageUnderLinearMap B h x := by
    simpa [hr_image] using hzle
  have himage_eq_hz : imageUnderLinearMap B h x = h z :=
    le_antisymm hsInf_le_hz hhz_le_image
  have hA₁A₂ : A₁ z + A₂ z = x := by
    simpa [B, LinearMap.add_apply] using hzB
  have hA₁eq : A₁ z = x - A₂ z :=
    helperForCorollary_19_3_4_eq_sub_of_add_eq (h := hA₁A₂)
  refine ⟨A₂ z, ?_⟩
  calc
    infimalConvolution f₁ f₂ x = imageUnderLinearMap B h x := by
      simp [hImageEqInf]
    _ = h z := himage_eq_hz
    _ = f₁ (A₁ z) + f₂ (A₂ z) := by simp [h]
    _ = f₁ (x - A₂ z) + f₂ (A₂ z) := by simp [hA₁eq]

/-- Helper for Corollary 19.3.4: if the infimal-convolution value at `x` is `⊤`, the defining
infimum is attained by the witness `y = 0`. -/
lemma helperForCorollary_19_3_4_attainment_of_top_value
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (htop : infimalConvolution f₁ f₂ x = (⊤ : EReal)) :
    ∃ y : Fin n → ℝ, infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y := by
  refine ⟨0, ?_⟩
  have hsInf_le :
      infimalConvolution f₁ f₂ x ≤ f₁ (x - 0) + f₂ 0 := by
    have hmem :
        (f₁ (x - 0) + f₂ 0 : EReal) ∈
          {z : EReal |
            ∃ x₁ x₂ : Fin n → ℝ,
              x₁ + x₂ = x ∧ z = f₁ x₁ + f₂ x₂} := by
      refine ⟨x - 0, 0, ?_, ?_⟩
      · simp
      · simp
    simpa [infimalConvolution] using (sInf_le hmem)
  have htop_le : (⊤ : EReal) ≤ f₁ (x - 0) + f₂ 0 := by
    simpa [htop] using hsInf_le
  have hvalue_top : f₁ (x - 0) + f₂ 0 = (⊤ : EReal) := top_unique htop_le
  calc
    infimalConvolution f₁ f₂ x = (⊤ : EReal) := htop
    _ = f₁ (x - 0) + f₂ 0 := hvalue_top.symm

/-- Helper for Corollary 19.3.4: any `EReal` value that is neither `⊤` nor `⊥` equals the
coercion of its `toReal` value. -/
lemma helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
    {v : EReal}
    (hTop : v ≠ (⊤ : EReal))
    (hBot : v ≠ (⊥ : EReal)) :
    v = ((v.toReal : ℝ) : EReal) := by
  simpa using (EReal.coe_toReal hTop hBot).symm

/-- Corollary 19.3.4: If `f₁` and `f₂` are proper polyhedral convex functions on `ℝ^n`, then
`infimalConvolution f₁ f₂` is a polyhedral convex function. Moreover, if
`infimalConvolution f₁ f₂` is proper, the infimum in the definition of
`(f₁ \sqcup f₂)(x)` is attained for each `x`. -/
theorem polyhedralConvexFunction_infimalConvolution
    (n : ℕ) (f₁ f₂ : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f₁ →
      IsPolyhedralConvexFunction n f₂ →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ →
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ →
            IsPolyhedralConvexFunction n (infimalConvolution f₁ f₂) ∧
              (ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                (infimalConvolution f₁ f₂) →
                ∀ x : Fin n → ℝ,
                  ∃ y : Fin n → ℝ,
                    infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y) := by
  intro hf₁poly hf₂poly hproper₁ hproper₂
  have hconv_inf :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂) :=
    convexFunctionOn_infimalConvolution_of_proper
      (f := f₁) (g := f₂) hproper₁ hproper₂
  have hpoly_inf :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => (prodLinearEquiv_append (n := n)) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
    exact
      helperForCorollary_19_3_4_polyhedralEpigraph_infimalConvolution
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  refine ⟨⟨hconv_inf, hpoly_inf⟩, ?_⟩
  intro hproper_inf x
  by_cases htop : infimalConvolution f₁ f₂ x = (⊤ : EReal)
  · exact
      helperForCorollary_19_3_4_attainment_of_top_value
        (f₁ := f₁) (f₂ := f₂) (x := x) htop
  · have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hbot : infimalConvolution f₁ f₂ x ≠ (⊥ : EReal) :=
      hproper_inf.2.2 x hx_univ
    let r : ℝ := (infimalConvolution f₁ f₂ x).toReal
    have hr : infimalConvolution f₁ f₂ x = (r : EReal) := by
      simpa [r] using
        helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := htop) (hBot := hbot)
    exact
      helperForCorollary_19_3_4_attainment_of_finite_value
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
        (x := x) (r := r) hr


end Section19
end Chap19
