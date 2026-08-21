/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part8

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Corollary 19.2.1: a polyhedral set yields a polyhedral indicator function
via the max-affine-plus-indicator representation with `k = 0`. -/
lemma helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (indicatorFunction C) := by
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hCpoly with
    ⟨m, b, β, hCeq⟩
  have hrepr :
      ∃ (k m : ℕ) (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ),
        k ≤ m ∧
          indicatorFunction C =
            (fun x =>
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
                indicatorFunction
                  (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                    (∑ j, y j * b i j) ≤ β i})
                  x) := by
    refine ⟨0, m, b, β, Nat.zero_le m, ?_⟩
    funext x
    let D : Set (Fin n → ℝ) :=
      {y | ∀ i : Fin m, (0 : ℕ) ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
    have hD : D = C := by
      calc
        D = {y : Fin n → ℝ | ∀ i : Fin m, (∑ j, y j * b i j) ≤ β i} := by
              ext y
              simp [D]
        _ = ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
              ext y
              simp [closedHalfSpaceLE, dotProduct]
        _ = C := by
              exact hCeq.symm
    have hSupZero :
        (sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < 0 ∧ r = (∑ j, x j * b i j) - β i} : ℝ) = 0 := by
      simp
    calc
      indicatorFunction C x = indicatorFunction (C := D) x := by
        simp [hD]
      _ = (0 : EReal) + indicatorFunction (C := D) x := by
        simp
      _ =
          ((sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < 0 ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
        simp
  exact
    ((polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := indicatorFunction C)).2 hrepr).1

/-- Helper for Corollary 19.2.1: an equality between an indicator and a max-affine-plus-
indicator representation forces equality of the underlying sets. -/
lemma helperForCorollary_19_2_1_indicatorRepresentation_forces_setEquality
    {n k m : ℕ} {C D : Set (Fin n → ℝ)}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hrepr :
      indicatorFunction C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x) :
    C = D := by
  ext x
  constructor
  · intro hxC
    by_contra hxD
    have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
    have hzero_top : (0 : EReal) = (⊤ : EReal) := by
      calc
        (0 : EReal) = indicatorFunction C x := by
          simp [indicatorFunction, hxC]
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ = (⊤ : EReal) := by
          simp [indicatorFunction, hxD]
    have hzero_ne_top : (0 : EReal) ≠ (⊤ : EReal) := by
      simp
    exact hzero_ne_top hzero_top
  · intro hxD
    by_contra hxC
    have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
    have htop_coe :
        (⊤ : EReal) =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
      calc
        (⊤ : EReal) = indicatorFunction C x := by
          simp [indicatorFunction, hxC]
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
              simp [indicatorFunction, hxD]
    exact (EReal.coe_ne_top _) htop_coe.symm

/-- Helper for Corollary 19.2.1: if the indicator function is polyhedral, then the set is
polyhedral. -/
lemma helperForCorollary_19_2_1_polyhedralSet_of_indicatorPolyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C)) :
    IsPolyhedralConvexSet n C := by
  have hIndicatorNonbot :
      ∀ x : Fin n → ℝ, indicatorFunction C x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : x ∈ C <;> simp [indicatorFunction, hx]
  rcases
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := indicatorFunction C)).1 ⟨hIndicatorPoly, hIndicatorNonbot⟩ with
    ⟨k, m, b, β, hk, hrepr⟩
  let D : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  have hreprD :
      indicatorFunction C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
    simpa [D] using hrepr
  have hCD : C = D :=
    helperForCorollary_19_2_1_indicatorRepresentation_forces_setEquality
      (C := C) (D := D) (b := b) (β := β) hreprD
  have hDpoly : IsPolyhedralConvexSet n D := by
    refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n D).2 ?_
    let b' : Fin m → Fin n → ℝ := fun i => if k ≤ (i : ℕ) then b i else 0
    let β' : Fin m → ℝ := fun i => if k ≤ (i : ℕ) then β i else 0
    refine ⟨m, b', β', ?_⟩
    ext y
    constructor
    · intro hy
      refine Set.mem_iInter.mpr ?_
      intro i
      by_cases hki : k ≤ (i : ℕ)
      · have hyi : (∑ j, y j * b i j) ≤ β i := hy i hki
        simpa [closedHalfSpaceLE, b', β', hki] using hyi
      · simp [closedHalfSpaceLE, b', β', hki]
    · intro hy i hki
      have hmem : y ∈ closedHalfSpaceLE n (b' i) (β' i) :=
        Set.mem_iInter.mp hy i
      simpa [closedHalfSpaceLE, b', β', hki] using hmem
  simpa [hCD] using hDpoly

/-- Helper for Corollary 19.2.1: a closed convex polyhedral set has a polyhedral
support function. -/
lemma helperForCorollary_19_2_1_supportFunctionPolyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hClosed : IsClosed C) (hConv : Convex ℝ C)
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (supportFunctionEReal C) := by
  have hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
      (n := n) (C := C) hCpoly
  have hConjPoly :
      IsPolyhedralConvexFunction n (fenchelConjugate n (indicatorFunction C)) :=
    polyhedralConvexFunction_fenchelConjugate
      (n := n) (f := indicatorFunction C) hIndicatorPoly
  have hConjEq :
      fenchelConjugate n (indicatorFunction C) = supportFunctionEReal C :=
    (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
      (C := C) hConv hClosed).1
  simpa [hConjEq] using hConjPoly

/-- Helper for Corollary 19.2.1: if the support function is polyhedral, then the closed
convex set is polyhedral. -/
lemma helperForCorollary_19_2_1_polyhedralSet_of_supportFunctionPolyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hClosed : IsClosed C) (hConv : Convex ℝ C)
    (hSupportPoly : IsPolyhedralConvexFunction n (supportFunctionEReal C)) :
    IsPolyhedralConvexSet n C := by
  have hConjPoly :
      IsPolyhedralConvexFunction n (fenchelConjugate n (supportFunctionEReal C)) :=
    polyhedralConvexFunction_fenchelConjugate
      (n := n) (f := supportFunctionEReal C) hSupportPoly
  have hConjEq :
      fenchelConjugate n (supportFunctionEReal C) = indicatorFunction C :=
    (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
      (C := C) hConv hClosed).2
  have hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C) := by
    simpa [hConjEq] using hConjPoly
  exact
    helperForCorollary_19_2_1_polyhedralSet_of_indicatorPolyhedral
      (n := n) (C := C) hIndicatorPoly

/-- Helper for Corollary 19.2.1: under closedness and convexity, polyhedrality of `C`
is equivalent to polyhedrality of its support function. -/
lemma helperForCorollary_19_2_1_polyhedralSet_iff_supportFunctionPolyhedral_of_closed_convex
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hClosed : IsClosed C) (hConv : Convex ℝ C) :
    (IsPolyhedralConvexSet n C ↔
      IsPolyhedralConvexFunction n (supportFunctionEReal C)) := by
  constructor
  · intro hCpoly
    exact
      helperForCorollary_19_2_1_supportFunctionPolyhedral_of_polyhedralSet
        (n := n) (C := C) hClosed hConv hCpoly
  · intro hSupportPoly
    exact
      helperForCorollary_19_2_1_polyhedralSet_of_supportFunctionPolyhedral
        (n := n) (C := C) hClosed hConv hSupportPoly

/-- Corollary 19.2.1: A closed convex set `C` is polyhedral iff its support function
`δ^*(· | C)` is polyhedral. -/
theorem polyhedral_convexSet_iff_supportFunction_polyhedral
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsClosed C → Convex ℝ C →
      (IsPolyhedralConvexSet n C ↔
        IsPolyhedralConvexFunction n (supportFunctionEReal C)) := by
  intro hClosed hConv
  exact
    helperForCorollary_19_2_1_polyhedralSet_iff_supportFunctionPolyhedral_of_closed_convex
      (n := n) (C := C) hClosed hConv

/-- Helper for Corollary 19.2.2: a polyhedral convex set has a polyhedral support
function. -/
lemma helperForCorollary_19_2_2_supportFunction_polyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (supportFunctionEReal C) := by
  have hClosedC : IsClosed C :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n) (C := C) hCpoly).1
  have hConvC : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  exact
    (polyhedral_convexSet_iff_supportFunction_polyhedral (n := n) (C := C)
      hClosedC hConvC).1 hCpoly

/-- Helper for Corollary 19.2.2: the element `(1 : EReal)` is not top. -/
lemma helperForCorollary_19_2_2_one_ne_top :
    (1 : EReal) ≠ (⊤ : EReal) := by
  simpa using (EReal.coe_ne_top (1 : ℝ))

/-- Helper for Corollary 19.2.2: when `C = ∅`, the polar sublevel set at level `1`
is all of `ℝ^n`, hence polyhedral. -/
lemma helperForCorollary_19_2_2_emptyCase_univ_polyhedral
    (n : ℕ) :
    IsPolyhedralConvexSet n
      {xStar : Fin n → ℝ | supportFunctionEReal (∅ : Set (Fin n → ℝ)) xStar ≤ (1 : EReal)} := by
  have hSetEqUniv :
      {xStar : Fin n → ℝ | supportFunctionEReal (∅ : Set (Fin n → ℝ)) xStar ≤ (1 : EReal)} =
        (Set.univ : Set (Fin n → ℝ)) := by
    ext xStar
    simp [supportFunctionEReal]
  classical
  let ι : Type := PEmpty
  let b : ι → Fin n → ℝ := fun i => nomatch i
  let β : ι → ℝ := fun i => nomatch i
  have hPolyUniv : IsPolyhedralConvexSet n (Set.univ : Set (Fin n → ℝ)) := by
    refine ⟨ι, inferInstance, b, β, ?_⟩
    ext x
    simp [closedHalfSpaceLE, b, β]
  simpa [hSetEqUniv] using hPolyUniv

/-- Helper for Corollary 19.2.2: finitely many affine upper bounds of the form
`(∑ j, x j * b i j) ≤ (if i < k then β i + 1 else β i)` define a polyhedral convex set. -/
lemma helperForCorollary_19_2_2_piecewiseBounds_polyhedral
    {n k m : ℕ} {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ} :
    IsPolyhedralConvexSet n
      {x : Fin n → ℝ |
        ∀ i : Fin m, (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i)} := by
  refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n _).2 ?_
  refine ⟨m, b, (fun i => if (i : ℕ) < k then β i + 1 else β i), ?_⟩
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro i
    have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hx i
    simpa [closedHalfSpaceLE] using hxi
  · intro hx i
    have hmem : x ∈
        closedHalfSpaceLE n (b i) (if (i : ℕ) < k then β i + 1 else β i) :=
      Set.mem_iInter.mp hx i
    simpa [closedHalfSpaceLE] using hmem

/-- Corollary 19.2.2: The polar of a polyhedral convex set is polyhedral. -/
theorem polyhedral_convexSet_polar_polyhedral
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet n
        {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
  intro hCpoly
  by_cases hCempty : C = ∅
  · subst hCempty
    simpa using helperForCorollary_19_2_2_emptyCase_univ_polyhedral (n := n)
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hCempty
  have hConvC : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hSupportPoly : IsPolyhedralConvexFunction n (supportFunctionEReal C) :=
    helperForCorollary_19_2_2_supportFunction_polyhedral_of_polyhedralSet
      (n := n) (C := C) hCpoly
  have hSupportNonbot :
      ∀ xStar : Fin n → ℝ, supportFunctionEReal C xStar ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot (n := n) (C := C) hCne hConvC
  rcases
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := supportFunctionEReal C)).1 ⟨hSupportPoly, hSupportNonbot⟩ with
    ⟨k, m, b, β, hk, hrepr⟩
  let D : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  have hreprD :
      supportFunctionEReal C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
    simpa [D] using hrepr
  let P : Set (Fin n → ℝ) :=
    {x | ∀ i : Fin m, (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i)}
  have hSetEq :
      {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} = P := by
    ext x
    constructor
    · intro hx
      have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hreprD
      have hx_main :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x ≤ (1 : EReal) := by
        simpa [hreprx] using hx
      have hxD : x ∈ D := by
        by_contra hxD
        have htop_le_one : (⊤ : EReal) ≤ (1 : EReal) := by
          simpa [indicatorFunction, hxD] using hx_main
        have hone_top : (1 : EReal) = ⊤ := top_le_iff.mp htop_le_one
        exact helperForCorollary_19_2_2_one_ne_top hone_top
      intro i
      by_cases hki : (i : ℕ) < k
      · have hsup_le_one :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) ≤
            (1 : EReal) := by
          simpa [indicatorFunction, hxD] using hx_main
        have hsup_real_le_one :
            sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} ≤ 1 := by
          exact_mod_cast hsup_le_one
        let S : Set ℝ :=
          {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
        have hSfinite : S.Finite := by
          refine (Set.finite_range (fun i : Fin m => (∑ j, x j * b i j) - β i)).subset ?_
          intro r hr
          rcases hr with ⟨i, hki', rfl⟩
          exact ⟨i, rfl⟩
        have hSbdd : BddAbove S := hSfinite.bddAbove
        have hbound_all : ∀ r : ℝ, r ∈ S → r ≤ 1 := by
          intro r hr
          exact le_trans (le_csSup hSbdd hr) hsup_real_le_one
        have hbound_i : (∑ j, x j * b i j) - β i ≤ 1 := by
          exact hbound_all _ ⟨i, hki, rfl⟩
        have hbound_i' : (∑ j, x j * b i j) ≤ β i + 1 := by
          linarith
        simpa [hki] using hbound_i'
      · have hki_ge : k ≤ (i : ℕ) := Nat.le_of_not_lt hki
        have hbound_i : (∑ j, x j * b i j) ≤ β i := hxD i hki_ge
        simpa [hki] using hbound_i
    · intro hxP
      have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hreprD
      have hxD : x ∈ D := by
        intro i hki_ge
        have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hxP i
        have hki_not : ¬ (i : ℕ) < k := Nat.not_lt.mpr hki_ge
        simpa [hki_not] using hxi
      have hsup_real_le_one :
          sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} ≤ 1 := by
        let S : Set ℝ :=
          {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
        have hs : ∀ r : ℝ, r ∈ S → r ≤ 1 := by
          intro r hr
          rcases hr with ⟨i, hki, rfl⟩
          have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hxP i
          have hxi' : (∑ j, x j * b i j) ≤ β i + 1 := by
            simpa [hki] using hxi
          linarith
        by_cases hS : S.Nonempty
        · exact csSup_le hS hs
        · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
          simp [S, hS_empty]
      have hsup_le_one :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) ≤
            (1 : EReal) := by
        exact_mod_cast hsup_real_le_one
      calc
        supportFunctionEReal C x =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
              simp [indicatorFunction, hxD]
        _ ≤ (1 : EReal) := hsup_le_one
  have hPpoly : IsPolyhedralConvexSet n P := by
    simpa [P] using
      (helperForCorollary_19_2_2_piecewiseBounds_polyhedral
        (n := n) (k := k) (m := m) (b := b) (β := β))
  simpa [hSetEq, P] using hPpoly

/-- Helper for Theorem 19.3: linear images of polyhedral convex sets are finitely generated. -/
lemma helperForTheorem_19_3_image_finitelyGenerated_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsFinitelyGeneratedConvexSet m (A '' C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
        (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  have hCfg : IsFinitelyGeneratedConvexSet n C :=
    (hTFAE.out 0 2).1 hCpoly
  exact
    helperForCorollary_19_1_2_linearImage_finitelyGeneratedSet
      (n := n) (p := m) (C := C) hCfg A

/-- Helper for Theorem 19.3: linear images of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_3_image_polyhedral_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet m (A '' C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hImageConv : Convex ℝ (A '' C) := hCconv.linear_image A
  have hImageFG : IsFinitelyGeneratedConvexSet m (A '' C) :=
    helperForTheorem_19_3_image_finitelyGenerated_of_polyhedral (A := A) (C := C) hCpoly
  exact
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := m) (C := A '' C) hImageConv hImageFG

/-- Helper for Theorem 19.3: the preimage of one closed half-space under `A` is the
corresponding closed half-space with normal transformed by the transpose matrix of `A`. -/
lemma helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (β : ℝ) :
    A ⁻¹' (closedHalfSpaceLE m b β) =
      closedHalfSpaceLE n
        (((LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A).transpose.mulVec b)
        β := by
  let M : Matrix (Fin m) (Fin n) ℝ :=
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A
  ext x
  have hAx : A x = M.mulVec x := by
    have hrepr :=
      LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) A x
    ext i
    have hrepr_i := congrArg (fun v : Fin m → ℝ => v i) hrepr
    simpa [M, Pi.basisFun_repr] using hrepr_i.symm
  have hvec : Matrix.vecMul b M = M.transpose.mulVec b := by
    simpa using (Matrix.mulVec_transpose (A := M) (x := b)).symm
  have hdot :
      dotProduct (A x) b = dotProduct x (M.transpose.mulVec b) := by
    calc
      dotProduct (A x) b = dotProduct (M.mulVec x) b := by simp [hAx]
      _ = b ⬝ᵥ M.mulVec x := by simp [dotProduct_comm]
      _ = Matrix.vecMul b M ⬝ᵥ x := Matrix.dotProduct_mulVec b M x
      _ = M.transpose.mulVec b ⬝ᵥ x := by simp [hvec]
      _ = dotProduct x (M.transpose.mulVec b) := by simp [dotProduct_comm]
  constructor
  · intro hx
    have hAxLe : dotProduct (A x) b ≤ β := by
      simpa [closedHalfSpaceLE] using hx
    have hxLe : dotProduct x (M.transpose.mulVec b) ≤ β := by
      simpa [hdot] using hAxLe
    simpa [closedHalfSpaceLE, M] using hxLe
  · intro hx
    have hxLe : dotProduct x (M.transpose.mulVec b) ≤ β := by
      simpa [closedHalfSpaceLE, M] using hx
    have hAxLe : dotProduct (A x) b ≤ β := by
      simpa [hdot] using hxLe
    simpa [closedHalfSpaceLE] using hAxLe

/-- Helper for Theorem 19.3: linear preimages of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_3_preimage_polyhedral_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {D : Set (Fin m → ℝ)}
    (hDpoly : IsPolyhedralConvexSet m D) :
    IsPolyhedralConvexSet n (A ⁻¹' D) := by
  let M : Matrix (Fin m) (Fin n) ℝ :=
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces m D).1 hDpoly with
    ⟨k, b, β, hD⟩
  refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n (A ⁻¹' D)).2 ?_
  refine ⟨k, (fun i => M.transpose.mulVec (b i)), β, ?_⟩
  ext x
  constructor
  · intro hx
    have hAx_mem : A x ∈ D := hx
    have hAxInter : A x ∈ ⋂ i, closedHalfSpaceLE m (b i) (β i) := by
      simpa [hD] using hAx_mem
    refine Set.mem_iInter.mpr ?_
    intro i
    have hAx_i : A x ∈ closedHalfSpaceLE m (b i) (β i) :=
      Set.mem_iInter.mp hAxInter i
    have hx_pre : x ∈ A ⁻¹' (closedHalfSpaceLE m (b i) (β i)) := hAx_i
    simpa [M, helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq (A := A) (b := b i) (β := β i)]
      using hx_pre
  · intro hx
    have hxInter : x ∈ ⋂ i, closedHalfSpaceLE n (M.transpose.mulVec (b i)) (β i) := hx
    have hAxInter : A x ∈ ⋂ i, closedHalfSpaceLE m (b i) (β i) := by
      refine Set.mem_iInter.mpr ?_
      intro i
      have hx_i : x ∈ closedHalfSpaceLE n (M.transpose.mulVec (b i)) (β i) :=
        Set.mem_iInter.mp hxInter i
      have hx_pre : x ∈ A ⁻¹' (closedHalfSpaceLE m (b i) (β i)) := by
        simpa
          [M, helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq (A := A) (b := b i) (β := β i)]
          using hx_i
      exact hx_pre
    change A x ∈ D
    simpa [hD] using hAxInter

/-- Helper for Theorem 19.3: for fixed `A`, the image-preservation branch holds pointwise
in the set variable. -/
lemma helperForTheorem_19_3_image_branch
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet m (A '' C) := by
  intro C hCpoly
  exact helperForTheorem_19_3_image_polyhedral_of_polyhedral (A := A) (C := C) hCpoly

/-- Helper for Theorem 19.3: for fixed `A`, the preimage-preservation branch holds
pointwise in the set variable. -/
lemma helperForTheorem_19_3_preimage_branch
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ∀ D : Set (Fin m → ℝ), IsPolyhedralConvexSet m D →
      IsPolyhedralConvexSet n (A ⁻¹' D) := by
  intro D hDpoly
  exact helperForTheorem_19_3_preimage_polyhedral_of_polyhedral (A := A) (D := D) hDpoly

/-- Helper for Theorem 19.3: for a fixed linear map, both the image-preservation and
preimage-preservation polyhedrality statements hold together. -/
lemma helperForTheorem_19_3_image_and_preimage_polyhedral
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet m (A '' C)) ∧
      (∀ D : Set (Fin m → ℝ), IsPolyhedralConvexSet m D →
        IsPolyhedralConvexSet n (A ⁻¹' D)) := by
  constructor
  · exact helperForTheorem_19_3_image_branch (A := A)
  · exact helperForTheorem_19_3_preimage_branch (A := A)

/-- Theorem 19.3: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. Then `A '' C` is a
polyhedral convex set in `ℝ^m` for each polyhedral convex set `C` in `ℝ^n`, and `A ⁻¹' D` is a
polyhedral convex set in `ℝ^n` for each polyhedral convex set `D` in `ℝ^m`. -/
theorem polyhedralConvexSet_image_preimage_linear
    (n m : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet m (A '' C)) ∧
      (∀ D : Set (Fin m → ℝ), IsPolyhedralConvexSet m D →
        IsPolyhedralConvexSet n (A ⁻¹' D)) := by
  exact helperForTheorem_19_3_image_and_preimage_polyhedral (A := A)

/-- Helper for Corollary 19.3.1: coordinate conjugate of `linearMap_prod A` between
`Fin`-function models of product spaces. -/
noncomputable def helperForCorollary_19_3_1_linearMapProdCoord
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  ((prodLinearEquiv_append_coord (n := m)).toLinearMap).comp
    ((linearMap_prod A).comp ((prodLinearEquiv_append_coord (n := n)).symm.toLinearMap))

/-- Helper for Corollary 19.3.1: after converting product points to `Fin` coordinates, the
image under `linearMap_prod A` is exactly the image under the conjugated map. -/
lemma helperForCorollary_19_3_1_image_linearMapProdCoord
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    {S : Set ((Fin n → ℝ) × ℝ)} :
    ((fun p => prodLinearEquiv_append_coord (n := m) p) '' ((linearMap_prod A) '' S)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) '' S) := by
  ext y
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(prodLinearEquiv_append_coord (n := n)) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨linearMap_prod A x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]

/-- Helper for Corollary 19.3.1: in `Fin` coordinates, the epigraph of
`inverseImageUnderLinearMap A g` is the preimage of the transformed epigraph of `g` under the
conjugated product map. -/
lemma helperForCorollary_19_3_1_transformedEpigraphCoord_inverseImage_eq_preimage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal} :
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ⁻¹'
        ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
          epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, μ⟩
    have hxle : g (A x) ≤ (μ : EReal) := by
      simpa [inverseImageUnderLinearMap] using
        (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).1 hp
    refine ⟨(A x, μ), ?_, ?_⟩
    · exact (mem_epigraph_univ_iff (f := g)).2 hxle
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply, linearMap_prod]
  · intro hz
    let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm z
    have hz' :
        helperForCorollary_19_3_1_linearMapProdCoord A z ∈
          (fun q => prodLinearEquiv_append_coord (n := m) q) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      exact hz
    have hlin_epi : linearMap_prod A p ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      rcases hz' with ⟨q, hq, hqeq⟩
      have hqeq' : q = linearMap_prod A p := by
        apply (prodLinearEquiv_append_coord (n := m)).injective
        calc
          (prodLinearEquiv_append_coord (n := m)) q
              = helperForCorollary_19_3_1_linearMapProdCoord A z := hqeq
          _ = (prodLinearEquiv_append_coord (n := m)) (linearMap_prod A p) := by
                simp [p, helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]
      simpa [hqeq'] using hq
    have hp_epi : p ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g) := by
      rcases p with ⟨x, μ⟩
      have hAx_epi : (A x, μ) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
        simpa [linearMap_prod] using hlin_epi
      have hxle : g (A x) ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hAx_epi
      have hxle' : inverseImageUnderLinearMap A g x ≤ (μ : EReal) := by
        simpa [inverseImageUnderLinearMap] using hxle
      exact (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).2 hxle'
    refine ⟨p, hp_epi, ?_⟩
    simp [p]

/-- Helper for Corollary 19.3.1: the projected epigraph of a polyhedral convex function under
`linearMap_prod A` is closed. -/
lemma helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
  have hpoly_coord_domain :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [prodLinearEquiv_append_coord] using hfpoly.2
  have hpoly_coord_image :
      IsPolyhedralConvexSet (m + 1)
        (Acoord ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    have himg := (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1) Acoord).1
    exact himg _ hpoly_coord_domain
  have hclosed_embedded :
      IsClosed
        (Acoord ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := m + 1)
      (C := Acoord ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f))
      hpoly_coord_image).1
  have himage_eq :
      ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
        ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) =
          Acoord ''
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [Acoord] using
      (helperForCorollary_19_3_1_image_linearMapProdCoord
        (A := A) (S := epigraph (Set.univ : Set (Fin n → ℝ)) f))
  have hclosed_image :
      IsClosed
        ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
          ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    simpa [himage_eq] using hclosed_embedded
  let hhome := ((prodLinearEquiv_append_coord (n := m)).toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed_homeomorphImage :
      IsClosed
        ((hhome : ((Fin m → ℝ) × ℝ) → (Fin (m + 1) → ℝ)) ''
          ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed_image
  exact
    (hhome.isClosed_image
      (s := (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)).1
      hclosed_homeomorphImage

/-- Helper for Corollary 19.3.1: in `Fin` coordinates, the epigraph of
`imageUnderLinearMap A f` is exactly the image of the transformed epigraph of `f` under the
conjugated product map. -/
lemma helperForCorollary_19_3_1_transformedEpigraphCoord_imageUnderLinearMap_eq_image
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  calc
    ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f))
        = ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
              simp [hEq_epi]
    _ = (helperForCorollary_19_3_1_linearMapProdCoord A) ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
              exact
                helperForCorollary_19_3_1_image_linearMapProdCoord
                  (A := A) (S := epigraph (Set.univ : Set (Fin n → ℝ)) f)

/-- Helper for Corollary 19.3.1: in embedded coordinates, the epigraph of `imageUnderLinearMap`
is exactly the linear image of the embedded epigraph. -/
lemma helperForCorollary_19_3_1_transformedEpigraph_imageUnderLinearMap_eq_embeddedImage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ((fun p => prodLinearEquiv_append (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) =
      (fun z => (linearMap_prod_embedded (A := A)) z) ''
        ((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  calc
    ((fun p => prodLinearEquiv_append (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f))
        = ((fun p => prodLinearEquiv_append (n := m) p) ''
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
              simp [hEq_epi]
    _ = (fun z => (linearMap_prod_embedded (A := A)) z) ''
          ((fun p => prodLinearEquiv_append (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
              simpa using (image_linearMap_prod_embedded (A := A) (h := f))

/-- Helper for Corollary 19.3.1: if `imageUnderLinearMap A f y` is finite, then the infimum is
attained at some `x` with `A x = y`. -/
lemma helperForCorollary_19_3_1_attainment_of_finite_imageValue
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ∀ y : Fin m → ℝ,
      (∃ r : ℝ, imageUnderLinearMap A f y = (r : EReal)) →
        ∃ x : Fin n → ℝ, A x = y ∧ imageUnderLinearMap A f y = f x := by
  intro y hyfinite
  rcases hyfinite with ⟨r, hr⟩
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  have hmem_epi :
      (y, r) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) := by
    refine (mem_epigraph_univ_iff (f := imageUnderLinearMap A f)).2 ?_
    simp [hr]
  have hmem_image :
      (y, r) ∈ (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [hEq_epi] using hmem_epi
  have hx_exists :
      ∃ x : Fin n → ℝ, A x = y ∧ f x ≤ (r : EReal) := by
    simpa [image_epigraph_linearMap_eq (A := A) (h := f)] using hmem_image
  rcases hx_exists with ⟨x, hxA, hxle⟩
  have hsInf_le_fx : imageUnderLinearMap A f y ≤ f x := by
    have hxmem :
        f x ∈ {z : EReal | ∃ x' : Fin n → ℝ, A x' = y ∧ z = f x'} := by
      exact ⟨x, hxA, rfl⟩
    simpa [imageUnderLinearMap] using (sInf_le hxmem)
  have hfx_le_image : f x ≤ imageUnderLinearMap A f y := by
    simpa [hr] using hxle
  exact ⟨x, hxA, le_antisymm hsInf_le_fx hfx_le_image⟩

/-- Helper for Corollary 19.3.1: in embedded coordinates, the epigraph of
`inverseImageUnderLinearMap` is the preimage of the embedded epigraph under
`linearMap_prod_embedded`. -/
lemma helperForCorollary_19_3_1_transformedEpigraph_inverseImage_eq_embeddedPreimage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal} :
    ((fun p => prodLinearEquiv_append (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) =
      (fun z => (linearMap_prod_embedded (A := A)) z) ⁻¹'
        ((fun p => prodLinearEquiv_append (n := m) p) ''
          epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, μ⟩
    have hxle : g (A x) ≤ (μ : EReal) := by
      simpa [inverseImageUnderLinearMap] using
        (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).1 hp
    refine ⟨(A x, μ), ?_, ?_⟩
    · exact (mem_epigraph_univ_iff (f := g)).2 hxle
    · simp [linearMap_prod_embedded, LinearMap.comp_apply, linearMap_prod]
  · intro hz
    let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append (n := n)).symm z
    have hz' :
        (linearMap_prod_embedded (A := A)) z ∈
          (fun q => prodLinearEquiv_append (n := m) q) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      exact hz
    have hlin_epi : linearMap_prod A p ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      rcases hz' with ⟨q, hq, hqeq⟩
      have hqeq' : q = linearMap_prod A p := by
        apply (prodLinearEquiv_append (n := m)).injective
        calc
          (prodLinearEquiv_append (n := m)) q = (linearMap_prod_embedded (A := A)) z := hqeq
          _ = (prodLinearEquiv_append (n := m)) (linearMap_prod A p) := by
                simp [p, linearMap_prod_embedded, LinearMap.comp_apply]
      simpa [hqeq'] using hq
    have hp_epi : p ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g) := by
      rcases p with ⟨x, μ⟩
      have hAx_epi : (A x, μ) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
        simpa [linearMap_prod] using hlin_epi
      have hxle : g (A x) ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hAx_epi
      exact (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).2
        (by simpa [inverseImageUnderLinearMap] using hxle)
    refine ⟨p, hp_epi, ?_⟩
    simp [p]

/-- Helper for Corollary 19.3.1: polyhedral convexity is preserved by
`imageUnderLinearMap` for polyhedral convex functions. -/
lemma helperForCorollary_19_3_1_polyhedral_imageUnderLinearMap
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    IsPolyhedralConvexFunction m (imageUnderLinearMap A f) := by
  refine ⟨?_, ?_⟩
  · simpa [imageUnderLinearMap] using
      (convexFunctionOn_inf_fiber_linearMap (A := A) (h := f) hfpoly.1)
  · have hpoly_coord_domain :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [prodLinearEquiv_append_coord] using hfpoly.2
    let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
    have hpoly_embedded_image :
        IsPolyhedralConvexSet (m + 1)
          (Acoord ''
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
      have himg :=
        (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1)
          Acoord).1
      exact himg _ hpoly_coord_domain
    have hEq :=
      helperForCorollary_19_3_1_transformedEpigraphCoord_imageUnderLinearMap_eq_image
        (A := A) (f := f) hfpoly
    have hpoly_target_coord :
        IsPolyhedralConvexSet (m + 1)
          ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) := by
      simpa [hEq, Acoord] using hpoly_embedded_image
    simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Corollary 19.3.1: polyhedral convexity is preserved by
`inverseImageUnderLinearMap` for polyhedral convex functions. -/
lemma helperForCorollary_19_3_1_polyhedral_inverseImageUnderLinearMap
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal}
    (hgpoly : IsPolyhedralConvexFunction m g) :
    IsPolyhedralConvexFunction n (inverseImageUnderLinearMap A g) := by
  refine ⟨?_, ?_⟩
  · simpa [inverseImageUnderLinearMap] using
      (convexFunctionOn_precomp_linearMap (A := A) (g := g) hgpoly.1)
  · let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
    have hpoly_target_coord :
        IsPolyhedralConvexSet (m + 1)
          ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
      simpa [prodLinearEquiv_append_coord] using hgpoly.2
    have hpoly_embedded_preimage :
        IsPolyhedralConvexSet (n + 1)
          (Acoord ⁻¹'
            ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
              epigraph (Set.univ : Set (Fin m → ℝ)) g)) := by
      have hpre :=
        (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1)
          Acoord).2
      exact hpre _ hpoly_target_coord
    have hEq :=
      helperForCorollary_19_3_1_transformedEpigraphCoord_inverseImage_eq_preimage
        (A := A) (g := g)
    have hpoly_source_coord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) := by
      simpa [hEq, Acoord] using hpoly_embedded_preimage
    simpa [prodLinearEquiv_append_coord] using hpoly_source_coord

/-- Helper for Corollary 19.3.1: polyhedrality of `imageUnderLinearMap` together with
attainment of finite image values. -/
lemma helperForCorollary_19_3_1_imageUnderLinearMap_polyhedral_and_attainment
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    IsPolyhedralConvexFunction m (imageUnderLinearMap A f) ∧
      (∀ y : Fin m → ℝ,
        (∃ r : ℝ, imageUnderLinearMap A f y = (r : EReal)) →
          ∃ x : Fin n → ℝ, A x = y ∧ imageUnderLinearMap A f y = f x) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForCorollary_19_3_1_polyhedral_imageUnderLinearMap
        (A := A) (f := f) hfpoly
  · exact
      helperForCorollary_19_3_1_attainment_of_finite_imageValue
        (A := A) (f := f) hfpoly

/-- Corollary 19.3.1: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. For each
polyhedral convex function `f` on `ℝ^n`, the convex function `Af` is polyhedral on `ℝ^m`, and
the infimum in its definition, if finite, is attained. For each polyhedral convex function `g`
on `ℝ^m`, `gA` is polyhedral on `ℝ^n`. -/
theorem polyhedralConvexFunction_image_preimage_linear
    (n m : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ f : (Fin n → ℝ) → EReal,
      IsPolyhedralConvexFunction n f →
        IsPolyhedralConvexFunction m (imageUnderLinearMap A f) ∧
          (∀ y : Fin m → ℝ,
            (∃ r : ℝ, imageUnderLinearMap A f y = (r : EReal)) →
              ∃ x : Fin n → ℝ, A x = y ∧ imageUnderLinearMap A f y = f x)) ∧
    (∀ g : (Fin m → ℝ) → EReal,
      IsPolyhedralConvexFunction m g →
        IsPolyhedralConvexFunction n (inverseImageUnderLinearMap A g)) := by
  constructor
  · intro f hfpoly
    exact
      helperForCorollary_19_3_1_imageUnderLinearMap_polyhedral_and_attainment
        (A := A) (f := f) hfpoly
  · intro g hgpoly
    exact
      helperForCorollary_19_3_1_polyhedral_inverseImageUnderLinearMap
        (A := A) (g := g) hgpoly


end Section19
end Chap19
