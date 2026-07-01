/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part9

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- Represent `g` as a support function when its epigraph is the closed cone `closure coneK`. -/
lemma exists_supportFunctionEReal_eq_convexFunctionClosure_of_epigraph_eq_closure_coneK {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    {g : (Fin n → Real) → EReal}
    (hcone :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g =
        closure (coneK (n := n) Sstar)) :
    ∃ D : Set (Fin n → Real), D.Nonempty ∧ Convex ℝ D ∧ g = supportFunctionEReal D := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hconv_epi : Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
    have hconvK : Convex ℝ (coneK (n := n) Sstar) := convex_coneK (n := n) Sstar
    simpa [hcone] using hconvK.closure
  have hconv : ConvexFunction g := by
    simpa [ConvexFunction] using hconv_epi
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
    simp [hcone]
  have hclosed_sub :
      ∀ α : Real, IsClosed {x : Fin n → Real | g x ≤ (α : EReal)} :=
    closed_sublevel_of_closed_epigraph (f := g) hclosed_epi
  have hlsc : LowerSemicontinuous g :=
    (lowerSemicontinuous_iff_closed_sublevel (f := g)).2 hclosed_sub
  have hclosed : ClosedConvexFunction g := ⟨hconv, hlsc⟩
  have hne_epi : Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
    refine ⟨(0 : (Fin n → Real) × Real), ?_⟩
    have hmem : (0 : (Fin n → Real) × Real) ∈ closure (coneK (n := n) Sstar) := by
      have hzero : (0 : (Fin n → Real) × Real) ∈ coneK (n := n) Sstar := by
        have :
            (0 : (Fin n → Real) × Real) ∈
              Set.insert (0 : (Fin n → Real) × Real)
                (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
                  Set ((Fin n → Real) × Real)) :=
          (Set.mem_insert_iff).2 (Or.inl rfl)
        simpa [coneK] using this
      exact subset_closure hzero
    simpa [hcone] using hmem
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  rcases hCne with ⟨x0, hx0C⟩
  have hhalfspace :
      closure (coneK (n := n) Sstar) ⊆
        {p : (Fin n → Real) × Real | dotProduct x0 p.1 ≤ p.2} := by
    intro p hp
    have hp' :
        p ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
      have hsubset :
          closure (coneK (n := n) Sstar) ⊆
            epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
        simpa [C] using
          (closure_coneK_subset_epigraph_supportFunctionEReal (n := n) Sstar hC_ne)
      exact hsubset hp
    have hle : supportFunctionEReal C p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hp'
    have hdot :
        ∀ x ∈ C, (dotProduct x p.1 : Real) ≤ p.2 :=
      (section13_supportFunctionEReal_le_coe_iff (C := C) (y := p.1) (μ := p.2)).1 hle
    exact hdot x0 hx0C
  have hnotbot : ∀ x : Fin n → Real, g x ≠ (⊥ : EReal) := by
    intro x hxbot
    have hle : g x ≤ ((dotProduct x0 x - 1 : Real) : EReal) := by
      simp [hxbot]
    have hmem : (x, dotProduct x0 x - 1) ∈
        epigraph (S := (Set.univ : Set (Fin n → Real))) g :=
      (mem_epigraph_univ_iff (f := g)).2 hle
    have hmem' : (x, dotProduct x0 x - 1) ∈ closure (coneK (n := n) Sstar) := by
      simpa [hcone] using hmem
    have hineq : dotProduct x0 x ≤ dotProduct x0 x - 1 := hhalfspace hmem'
    linarith
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
    refine ⟨?_, hne_epi, ?_⟩
    · simpa [ConvexFunction] using hconv
    · intro x hxuniv
      simpa using hnotbot x
  have hcone_epi :
      ∀ t : Real, 0 < t →
        Set.image (fun p : (Fin n → Real) × Real => t • p)
            (epigraph (S := (Set.univ : Set (Fin n → Real))) g) ⊆
          epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
    intro t ht p hp
    rcases hp with ⟨p, hp, rfl⟩
    have hp' : p ∈ closure (coneK (n := n) Sstar) := by
      simpa [hcone] using hp
    have hcont :
        Continuous fun q : (Fin n → Real) × Real => t • q := by
      simpa using (continuous_const_smul t : Continuous fun q : (Fin n → Real) × Real => t • q)
    have himage :
        (fun q : (Fin n → Real) × Real => t • q) '' closure (coneK (n := n) Sstar) ⊆
          closure ((fun q : (Fin n → Real) × Real => t • q) '' coneK (n := n) Sstar) :=
      image_closure_subset_closure_image hcont
    have hsubset :
        (fun q : (Fin n → Real) × Real => t • q) '' coneK (n := n) Sstar ⊆
          coneK (n := n) Sstar := by
      intro q hq
      rcases hq with ⟨q, hq, rfl⟩
      exact smul_mem_coneK (n := n) (Sstar := Sstar) ht hq
    have hmem' :
        t • p ∈ closure (coneK (n := n) Sstar) := by
      have hmem'' :
          t • p ∈
            closure ((fun q : (Fin n → Real) × Real => t • q) '' coneK (n := n) Sstar) :=
        himage ⟨p, hp', rfl⟩
      exact (closure_mono hsubset) hmem''
    simpa [hcone] using hmem'
  have hpos : PositivelyHomogeneous g :=
    posHom_of_epigraph_cone (f := g) hcone_epi
  exact
    (exists_supportFunctionEReal_iff_closedProperConvex_posHom (n := n) (f := g)).2
      ⟨hclosed, hproper, hpos⟩

/-- If the epigraph of a support function contains `Sstar`, then the support set lies in `C`. -/
lemma support_set_subset_intersectionOfHalfspaces_of_epigraph_contains_Sstar {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) {D : Set (Fin n → Real)}
    {g : (Fin n → Real) → EReal} (hg : g = supportFunctionEReal D)
    (hSstar : Sstar ⊆ epigraph (S := (Set.univ : Set (Fin n → Real))) g) :
    D ⊆ intersectionOfHalfspaces (n := n) Sstar := by
  intro x hxD p hpS
  have hp : (p.1, p.2) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) g := hSstar hpS
  have hle : g p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := g)).1 hp
  have hle' : supportFunctionEReal D p.1 ≤ (p.2 : EReal) := by
    simpa [hg] using hle
  have hdot :
      ∀ x ∈ D, (dotProduct x p.1 : Real) ≤ p.2 :=
    (section13_supportFunctionEReal_le_coe_iff (C := D) (y := p.1) (μ := p.2)).1 hle'
  have hxle : dotProduct p.1 x ≤ p.2 := by
    simpa [dotProduct_comm] using hdot x hxD
  simpa [dotProduct_comm_bridge_for_supportFunction] using hxle

/-- The epigraph of `supportFunctionEReal C` is contained in the epigraph of `g`. -/
lemma epigraph_supportFunctionEReal_subset_epigraph_convexFunctionClosure {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    {g : (Fin n → Real) → EReal}
    (hcone :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g =
        closure (coneK (n := n) Sstar)) :
    epigraph (S := (Set.univ : Set (Fin n → Real)))
        (supportFunctionEReal (intersectionOfHalfspaces (n := n) Sstar)) ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  obtain ⟨D, hDne, hDconv, hgsupp⟩ :=
    exists_supportFunctionEReal_eq_convexFunctionClosure_of_epigraph_eq_closure_coneK
      (n := n) Sstar hC_ne (g := g) hcone
  have hSstar :
      Sstar ⊆ epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
    intro p hp
    have hp' : p ∈ adjoinVertical (n := n) Sstar := by
      exact Or.inl hp
    have hp'' :
        p ∈ (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
          Set ((Fin n → Real) × Real)) :=
      (ConvexCone.subset_hull (R := Real) (s := adjoinVertical (n := n) Sstar)) hp'
    have hpcone : p ∈ coneK (n := n) Sstar := by
      simpa [coneK] using (Or.inr hp'')
    have hpcl : p ∈ closure (coneK (n := n) Sstar) := subset_closure hpcone
    simpa [hcone] using hpcl
  have hDsubset : D ⊆ C :=
    support_set_subset_intersectionOfHalfspaces_of_epigraph_contains_Sstar (n := n) (Sstar := Sstar)
      (D := D) (g := g) hgsupp hSstar
  intro p hp
  rcases p with ⟨y, μ⟩
  have hleC : supportFunctionEReal C y ≤ (μ : EReal) :=
    (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hp
  have hdotC :
      ∀ x ∈ C, (dotProduct x y : Real) ≤ μ :=
    (section13_supportFunctionEReal_le_coe_iff (C := C) (y := y) (μ := μ)).1 hleC
  have hdotD : ∀ x ∈ D, (dotProduct x y : Real) ≤ μ := by
    intro x hxD
    exact hdotC x (hDsubset hxD)
  have hleD : supportFunctionEReal D y ≤ (μ : EReal) :=
    (section13_supportFunctionEReal_le_coe_iff (C := D) (y := y) (μ := μ)).2 hdotD
  have hle : g y ≤ (μ : EReal) := by
    simpa [hgsupp] using hleD
  exact (mem_epigraph_univ_iff (f := g)).2 hle

/-- Proposition 17.2.8 (Epigraph of the support function as the closure of `K`), LaTeX label
`prop:epi_clK`. Assume `C ≠ ∅`, where `C = intersectionOfHalfspaces S*` as in Definition 17.2.5,
and let `f, K` be as in Definition 17.2.7. Then

`epi (supportFunction · C) = epi (cl f) = closure (epi f) = closure K`.

In this formalization, `cl f` is modeled as `convexFunctionClosure` applied to the function
`f : ℝⁿ → (ℝ ∪ {+∞})` embedded into `EReal`. -/
theorem epigraph_supportFunction_eq_epigraph_convexFunctionClosure_eq_closure_epigraph_eq_closure_coneK
    {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
    let f : (Fin n → Real) → EReal :=
      fun xStar =>
        match infMuInCone (n := n) Sstar xStar with
        | (μ : Real) => (μ : EReal)
        | ⊤ => (⊤ : EReal)
    epigraph (S := (Set.univ : Set (Fin n → Real)))
          (supportFunctionEReal C) =
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) ∧
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ∧
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (coneK (n := n) Sstar)) := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  let f : (Fin n → Real) → EReal :=
    fun xStar =>
      match infMuInCone (n := n) Sstar xStar with
      | (μ : Real) => (μ : EReal)
      | ⊤ => (⊤ : EReal)
  have hclosure :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    simpa [f] using
      (epigraph_convexFunctionClosure_eq_closure_epigraph_of_infMuInCone (n := n) Sstar)
  have hcone :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (coneK (n := n) Sstar) := by
    apply le_antisymm
    · -- `epigraph f ⊆ closure (coneK)` remains the hard direction.
      have hsubset :
          epigraph (S := (Set.univ : Set (Fin n → Real))) f ⊆
            closure (coneK (n := n) Sstar) := by
        simpa [f] using
          (mem_epigraph_infMuInCone_imp_mem_closure_coneK (n := n) Sstar hC_ne)
      exact closure_minimal hsubset isClosed_closure
    ·
      have hsubset :
          coneK (n := n) Sstar ⊆
            epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
        simpa [f] using (coneK_subset_epigraph_infMuInCone (n := n) Sstar hC_ne)
      exact closure_mono hsubset
  have hsupport :
      epigraph (S := (Set.univ : Set (Fin n → Real)))
          (supportFunctionEReal C) =
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) := by
    apply le_antisymm
    ·
      have hcone' :
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
            closure (coneK (n := n) Sstar) := by
        calc
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := hclosure
          _ = closure (coneK (n := n) Sstar) := hcone
      have hsubset :
          epigraph (S := (Set.univ : Set (Fin n → Real)))
              (supportFunctionEReal C) ⊆
            epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) := by
        simpa [C] using
          (epigraph_supportFunctionEReal_subset_epigraph_convexFunctionClosure (n := n)
              Sstar hC_ne (g := convexFunctionClosure f) hcone')
      exact hsubset
    ·
      have hcone' :
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
            closure (coneK (n := n) Sstar) := by
        calc
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := hclosure
          _ = closure (coneK (n := n) Sstar) := hcone
      have hsubset :
          closure (coneK (n := n) Sstar) ⊆
            epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
        simpa [C] using
          (closure_coneK_subset_epigraph_supportFunctionEReal (n := n) Sstar hC_ne)
      simpa [hcone'] using hsubset
  refine ⟨?_, ?_, ?_⟩
  · exact hsupport
  · exact hclosure
  · exact hcone

/-- Addition preserves membership in `coneK`. -/
lemma coneK_add_mem {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    {a b : (Fin n → Real) × Real} (ha : a ∈ coneK (n := n) Sstar)
    (hb : b ∈ coneK (n := n) Sstar) :
    a + b ∈ coneK (n := n) Sstar := by
  classical
  let K : ConvexCone ℝ ((Fin n → Real) × Real) :=
    ConvexCone.hull Real (adjoinVertical (n := n) Sstar)
  have ha' : a = 0 ∨ a ∈ (K : Set ((Fin n → Real) × Real)) := by
    have ha' :
        a ∈ Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using ha
    exact (Set.mem_insert_iff).1 ha'
  have hb' : b = 0 ∨ b ∈ (K : Set ((Fin n → Real) × Real)) := by
    have hb' :
        b ∈ Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using hb
    exact (Set.mem_insert_iff).1 hb'
  rcases ha' with rfl | haK
  · simpa using hb
  · rcases hb' with rfl | hbK
    · simpa using ha
    ·
      have hsum : a + b ∈ (K : Set ((Fin n → Real) × Real)) := K.add_mem haK hbK
      have :
          a + b ∈
            Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
        (Set.mem_insert_iff).2 (Or.inr hsum)
      simpa [coneK, K] using this

/-- Nonnegative scaling preserves membership in `coneK`. -/
lemma coneK_smul_mem_of_nonneg {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    {t : Real} (ht : 0 ≤ t) {a : (Fin n → Real) × Real} (ha : a ∈ coneK (n := n) Sstar) :
    t • a ∈ coneK (n := n) Sstar := by
  by_cases ht0 : t = 0
  · subst ht0
    have :
        (0 : (Fin n → Real) × Real) ∈
          Set.insert (0 : (Fin n → Real) × Real)
            (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
              Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [coneK] using this
  ·
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    exact smul_mem_coneK (n := n) (Sstar := Sstar) htpos ha

/-- Conic combinations of the vertical vector and points of `Sstar` lie in `coneK`. -/
lemma conicCombination_mem_coneK {n m : Nat} (Sstar : Set ((Fin n → Real) × Real))
    (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real)
    (hp : ∀ i, p i ∈ Sstar) (hlam0 : 0 ≤ lam0) (hlam : ∀ i, 0 ≤ lam i) :
    lam0 • verticalVector n + ∑ i, lam i • p i ∈ coneK (n := n) Sstar := by
  classical
  have hvert : verticalVector n ∈ coneK (n := n) Sstar := by
    have hvert' : verticalVector n ∈ adjoinVertical (n := n) Sstar := by
      simp [adjoinVertical]
    have hvert'' :
        verticalVector n ∈
          (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
            Set ((Fin n → Real) × Real)) :=
      (ConvexCone.subset_hull (R := Real) (s := adjoinVertical (n := n) Sstar)) hvert'
    have :
        verticalVector n ∈
          Set.insert (0 : (Fin n → Real) × Real)
            (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
              Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inr hvert'')
    simpa [coneK] using this
  have hvertical : lam0 • verticalVector n ∈ coneK (n := n) Sstar :=
    coneK_smul_mem_of_nonneg (n := n) (Sstar := Sstar) hlam0 hvert
  have hsum :
      (∑ i, lam i • p i) ∈ coneK (n := n) Sstar := by
    have hsum' :
        ∀ s : Finset (Fin m),
          (Finset.sum s (fun i => lam i • p i)) ∈ coneK (n := n) Sstar := by
      refine Finset.induction ?h0 ?hstep
      ·
        have :
            (0 : (Fin n → Real) × Real) ∈
              Set.insert (0 : (Fin n → Real) × Real)
                (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
                  Set ((Fin n → Real) × Real)) :=
          (Set.mem_insert_iff).2 (Or.inl rfl)
        simpa [coneK] using this
      · intro a s ha hs
        have hp_mem : p a ∈ coneK (n := n) Sstar := by
          have hp' : p a ∈ adjoinVertical (n := n) Sstar := by
            simp [adjoinVertical, hp a]
          have hp'' :
              p a ∈
                (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
                  Set ((Fin n → Real) × Real)) :=
            (ConvexCone.subset_hull (R := Real) (s := adjoinVertical (n := n) Sstar)) hp'
          have :
              p a ∈
                Set.insert (0 : (Fin n → Real) × Real)
                  (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
                    Set ((Fin n → Real) × Real)) :=
            (Set.mem_insert_iff).2 (Or.inr hp'')
          simpa [coneK] using this
        have hterm :
            lam a • p a ∈ coneK (n := n) Sstar :=
          coneK_smul_mem_of_nonneg (n := n) (Sstar := Sstar) (hlam a) hp_mem
        have hsum'' :
            lam a • p a + Finset.sum s (fun i => lam i • p i) ∈ coneK (n := n) Sstar :=
          coneK_add_mem (n := n) (Sstar := Sstar) hterm hs
        simpa [Finset.sum_insert, ha] using hsum''
    simpa using hsum' (Finset.univ : Finset (Fin m))
  exact coneK_add_mem (n := n) (Sstar := Sstar) hvertical hsum

/-- Combine two conic representations by concatenating coefficients. -/
lemma conicRep_add {n m1 m2 : Nat}
    (p1 : Fin m1 → (Fin n → Real) × Real) (p2 : Fin m2 → (Fin n → Real) × Real)
    (lam01 lam02 : Real) (lam1 : Fin m1 → Real) (lam2 : Fin m2 → Real) :
    (lam01 • verticalVector n + ∑ i, lam1 i • p1 i) +
        (lam02 • verticalVector n + ∑ i, lam2 i • p2 i) =
      (lam01 + lam02) • verticalVector n +
        ∑ i : Fin (m1 + m2), (Fin.append lam1 lam2 i) • (Fin.append p1 p2 i) := by
  classical
  have hsum :
      (∑ i : Fin (m1 + m2), (Fin.append lam1 lam2 i) • (Fin.append p1 p2 i)) =
        (∑ i : Fin m1, lam1 i • p1 i) + ∑ i : Fin m2, lam2 i • p2 i := by
    simpa [Fin.append_left, Fin.append_right] using
      (Fin.sum_univ_add (f := fun i : Fin (m1 + m2) =>
        (Fin.append lam1 lam2 i) • (Fin.append p1 p2 i)))
  have hsmul :
      lam01 • verticalVector n + lam02 • verticalVector n =
        (lam01 + lam02) • verticalVector n := by
    simp [add_smul]
  calc
    (lam01 • verticalVector n + ∑ i, lam1 i • p1 i) +
        (lam02 • verticalVector n + ∑ i, lam2 i • p2 i) =
        (lam01 • verticalVector n + lam02 • verticalVector n) +
          ((∑ i, lam1 i • p1 i) + ∑ i, lam2 i • p2 i) := by
            ac_rfl
    _ = (lam01 + lam02) • verticalVector n +
          ((∑ i, lam1 i • p1 i) + ∑ i, lam2 i • p2 i) := by
            simp [hsmul]
    _ = (lam01 + lam02) • verticalVector n +
          ∑ i : Fin (m1 + m2), (Fin.append lam1 lam2 i) • (Fin.append p1 p2 i) := by
            simp [hsum]

/-- Scaling a conic representation scales all coefficients. -/
lemma conicRep_smul_pos {n m : Nat} (t : Real)
    (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real) :
    t • (lam0 • verticalVector n + ∑ i, lam i • p i) =
      (t * lam0) • verticalVector n + ∑ i, (t * lam i) • p i := by
  classical
  have hsum :
      t • ∑ i, lam i • p i = ∑ i, t • (lam i • p i) := by
    simpa using
      (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => lam i • p i) (r := t))
  calc
    t • (lam0 • verticalVector n + ∑ i, lam i • p i) =
        t • (lam0 • verticalVector n) + t • ∑ i, lam i • p i := by
          simp [smul_add]
    _ = (t * lam0) • verticalVector n + ∑ i, t • (lam i • p i) := by
          simp [hsum, smul_smul]
    _ = (t * lam0) • verticalVector n + ∑ i, (t * lam i) • p i := by
          simp [smul_smul]

/-- Elements of `adjoinVertical` admit a conic representation. -/
lemma adjoinVertical_subset_conicRep {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    {q : (Fin n → Real) × Real} (hq : q ∈ adjoinVertical (n := n) Sstar) :
    ∃ (m : Nat) (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
      (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
        q = lam0 • verticalVector n + ∑ i, lam i • p i := by
  rcases hq with hq | hq
  ·
    refine ⟨1, (fun _ => q), 0, (fun _ => 1), ?_, ?_, ?_, ?_⟩
    · intro i
      simpa using hq
    · simp
    · intro i
      simp
    · simp
  ·
    have hq' : q = verticalVector n := by
      simpa using hq
    refine ⟨0, (fun i : Fin 0 => (0, 0)), 1, (fun i : Fin 0 => 0), ?_, ?_, ?_, ?_⟩
    · intro i
      exact (Fin.elim0 i)
    · simp
    · intro i
      exact (Fin.elim0 i)
    · simp [hq']

/-- Membership in the hull of `adjoinVertical` yields a conic representation. -/
lemma mem_hull_adjoinVertical_imp_exists_conicCombination {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) {q : (Fin n → Real) × Real}
    (hq :
      q ∈ (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
        Set ((Fin n → Real) × Real))) :
    ∃ (m : Nat) (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
      (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
        q = lam0 • verticalVector n + ∑ i, lam i • p i := by
  classical
  let Krep : ConvexCone ℝ ((Fin n → Real) × Real) :=
    { carrier :=
        {q | ∃ (m : Nat) (p : Fin m → (Fin n → Real) × Real) (lam0 : Real)
            (lam : Fin m → Real),
          (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
            q = lam0 • verticalVector n + ∑ i, lam i • p i}
      smul_mem' := by
        intro t ht q hq
        rcases hq with ⟨m, p, lam0, lam, hp, hlam0, hlam, hEq⟩
        refine ⟨m, p, t * lam0, (fun i => t * lam i), hp, ?_, ?_, ?_⟩
        · exact mul_nonneg (le_of_lt ht) hlam0
        · intro i
          exact mul_nonneg (le_of_lt ht) (hlam i)
        ·
          calc
            t • q = t • (lam0 • verticalVector n + ∑ i, lam i • p i) := by
              simp [hEq]
            _ = (t * lam0) • verticalVector n + ∑ i, (t * lam i) • p i := by
              simpa using
                (conicRep_smul_pos (n := n) (t := t) (p := p) (lam0 := lam0) (lam := lam))
      add_mem' := by
        intro x hx y hy
        rcases hx with ⟨m1, p1, lam01, lam1, hp1, hlam01, hlam1, hEq1⟩
        rcases hy with ⟨m2, p2, lam02, lam2, hp2, hlam02, hlam2, hEq2⟩
        refine ⟨m1 + m2, Fin.append p1 p2, lam01 + lam02, Fin.append lam1 lam2, ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro i
            simpa [Fin.append_left] using hp1 i
          · intro i
            simpa [Fin.append_right] using hp2 i
        · exact add_nonneg hlam01 hlam02
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro i
            simpa [Fin.append_left] using hlam1 i
          · intro i
            simpa [Fin.append_right] using hlam2 i
        ·
          calc
            x + y =
                (lam01 • verticalVector n + ∑ i, lam1 i • p1 i) +
                (lam02 • verticalVector n + ∑ i, lam2 i • p2 i) := by
                  simp [hEq1, hEq2]
            _ = (lam01 + lam02) • verticalVector n +
                ∑ i : Fin (m1 + m2), (Fin.append lam1 lam2 i) • (Fin.append p1 p2 i) := by
                  simpa using
                    (conicRep_add (n := n) (p1 := p1) (p2 := p2) (lam01 := lam01)
                      (lam02 := lam02) (lam1 := lam1) (lam2 := lam2))
    }
  have hsubset :
      adjoinVertical (n := n) Sstar ⊆ (Krep : Set ((Fin n → Real) × Real)) := by
    intro q hq
    exact adjoinVertical_subset_conicRep (n := n) (Sstar := Sstar) hq
  have hsubset' :
      (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
          Set ((Fin n → Real) × Real)) ⊆
        (Krep : Set ((Fin n → Real) × Real)) := by
    intro q hq
    exact (ConvexCone.hull_min (s := adjoinVertical (n := n) Sstar) (C := Krep) hsubset) hq
  have hmem : q ∈ (Krep : Set ((Fin n → Real) × Real)) := hsubset' hq
  simpa [Krep] using hmem

/-- Lemma 17.2.9 (Membership in `K` via conic combinations), LaTeX label `lem:K_conic`.

Let `K` be the convex cone generated by `S* ∪ {(0, 1)}` (here: `K = coneK Sstar`). Then
`(x*, μ*) ∈ K` if and only if there exist finitely many points `(xᵢ*, μᵢ*) ∈ S*` and
coefficients `λ₀, λ₁, …, λₘ ≥ 0` such that

`(x*, μ*) = λ₀ (0, 1) + ∑ i, λᵢ (xᵢ*, μᵢ*)`.

In that case, `x* = ∑ i, λᵢ xᵢ*` and `μ* ≥ ∑ i, λᵢ μᵢ*`. -/
lemma mem_coneK_iff_exists_conicCombination {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    (xStar : Fin n → Real) (muStar : Real) :
    (xStar, muStar) ∈ coneK (n := n) Sstar ↔
      ∃ (m : Nat) (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
        (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
          (xStar, muStar) = lam0 • verticalVector n + ∑ i, lam i • p i := by
  constructor
  · intro hmem
    have hmem' :
        (xStar, muStar) = 0 ∨
          (xStar, muStar) ∈
            (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
              Set ((Fin n → Real) × Real)) := by
      simpa [coneK] using (Set.mem_insert_iff).1 hmem
    rcases hmem' with hzero | hmemhull
    ·
      refine ⟨0, (fun i : Fin 0 => (0, 0)), 0, (fun i : Fin 0 => 0), ?_, ?_, ?_, ?_⟩
      · intro i
        exact (Fin.elim0 i)
      · simp
      · intro i
        exact (Fin.elim0 i)
      · simp [hzero]
    ·
      exact mem_hull_adjoinVertical_imp_exists_conicCombination (n := n) (Sstar := Sstar) hmemhull
  · rintro ⟨m, p, lam0, lam, hp, hlam0, hlam, hEq⟩
    have hmem :
        lam0 • verticalVector n + ∑ i, lam i • p i ∈ coneK (n := n) Sstar :=
      conicCombination_mem_coneK (n := n) (Sstar := Sstar) p lam0 lam hp hlam0 hlam
    simpa [hEq] using hmem

/-- Lemma 17.2.9 (Membership in `K` via conic combinations), consequences: from a conic
representation of `(x*, μ*)` using the vertical vector `(0, 1)` and points of `S*`, one obtains
`x* = ∑ i, λᵢ xᵢ*` and `μ* ≥ ∑ i, λᵢ μᵢ*`. -/
lemma conicCombination_components {n m : Nat} (xStar : Fin n → Real) (muStar : Real)
    (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real)
    (hlam0 : 0 ≤ lam0)
    (hEq : (xStar, muStar) = lam0 • verticalVector n + ∑ i, lam i • p i) :
    xStar = ∑ i, lam i • (p i).1 ∧ muStar ≥ ∑ i, lam i * (p i).2 := by
  have hx :
      xStar = ∑ i, lam i • (p i).1 := by
    have hx' := congrArg Prod.fst hEq
    simpa [fst_sum, verticalVector] using hx'
  have hmu :
      muStar = lam0 + ∑ i, lam i * (p i).2 := by
    have hmu' := congrArg Prod.snd hEq
    simpa [snd_sum, verticalVector, mul_comm, mul_left_comm, mul_assoc] using hmu'
  refine ⟨hx, ?_⟩
  linarith

/-- Carathéodory bound for conic combinations over `adjoinVertical`. -/
lemma mem_coneK_imp_exists_nonnegLinearCombination_adjoinVertical_le {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (xStar : Fin n → Real) (muStar : Real) :
    (xStar, muStar) ∈ coneK (n := n) Sstar →
      ∃ k : Nat, k ≤ n + 1 ∧
        ∃ v : Fin k → (Fin n → Real) × Real, ∃ c : Fin k → Real,
          (∀ i, v i ∈ adjoinVertical (n := n) Sstar) ∧ (∀ i, 0 ≤ c i) ∧
            (xStar, muStar) = ∑ i, c i • v i := by
  classical
  intro hmem
  have hmem' :
      (xStar, muStar) = 0 ∨
        (xStar, muStar) ∈
          (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
            Set ((Fin n → Real) × Real)) := by
    simpa [coneK] using (Set.mem_insert_iff).1 hmem
  rcases hmem' with hzero | hmemhull
  ·
    refine ⟨0, by simp, (fun i : Fin 0 => (0, 0)), (fun i : Fin 0 => 0), ?_, ?_, ?_⟩
    · intro i
      exact (Fin.elim0 i)
    · intro i
      exact (Fin.elim0 i)
    · simp [hzero]
  ·
    let e : ((Fin n → Real) × Real) ≃ₗ[Real] (Fin (n + 1) → Real) :=
      prodLinearEquiv_append_coord (n := n)
    let T : Set (Fin (n + 1) → Real) := e '' adjoinVertical (n := n) Sstar
    have hTne : T.Nonempty := by
      refine ⟨e (verticalVector n), ?_⟩
      refine ⟨verticalVector n, ?_, rfl⟩
      simp [adjoinVertical]
    have hmem_e_hull :
        e (xStar, muStar) ∈
          (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) := by
      have hsubset :
          adjoinVertical (n := n) Sstar ⊆
            (ConvexCone.comap e.toLinearMap (ConvexCone.hull Real T) :
              Set ((Fin n → Real) × Real)) := by
        intro q hq
        have hqT : e q ∈ T := ⟨q, hq, rfl⟩
        have hqHull :
            e q ∈ (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) :=
          (ConvexCone.subset_hull (R := Real) (s := T)) hqT
        simpa using hqHull
      have hsubset' :
          (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
              Set ((Fin n → Real) × Real)) ⊆
            (ConvexCone.comap e.toLinearMap (ConvexCone.hull Real T) :
              Set ((Fin n → Real) × Real)) := by
        intro q hq
        exact
          (ConvexCone.hull_min (s := adjoinVertical (n := n) Sstar)
              (C := ConvexCone.comap e.toLinearMap (ConvexCone.hull Real T)) hsubset) hq
      have hqmem :
          (xStar, muStar) ∈
            (ConvexCone.comap e.toLinearMap (ConvexCone.hull Real T) :
              Set ((Fin n → Real) × Real)) :=
        hsubset' hmemhull
      simpa using hqmem
    have hmem_e :
        e (xStar, muStar) ∈ convexConeGenerated (n + 1) T := by
      have hmem_insert :
          e (xStar, muStar) ∈
            Set.insert (0 : Fin (n + 1) → Real)
              (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) :=
        (Set.mem_insert_iff).2 (Or.inr hmem_e_hull)
      simpa [convexConeGenerated] using hmem_insert
    rcases
        mem_convexConeGenerated_imp_exists_nonnegLinearCombination_le
          (n := n + 1) (T := T) hTne hmem_e with
      ⟨k, hk, v, c, hv, hc, hEq⟩
    let v' : Fin k → (Fin n → Real) × Real := fun i => e.symm (v i)
    have hv' : ∀ i, v' i ∈ adjoinVertical (n := n) Sstar := by
      intro i
      rcases hv i with ⟨q, hq, hqeq⟩
      have hq' : v' i = q := by
        apply e.injective
        simp [v', hqeq]
      simpa [hq'] using hq
    have hsum :
        e.symm (∑ i, c i • v i) = ∑ i, c i • e.symm (v i) := by
      calc
        e.symm (∑ i, c i • v i) = ∑ i, e.symm (c i • v i) := by
          exact
            (map_sum (g := e.symm) (f := fun i => c i • v i)
              (s := (Finset.univ : Finset (Fin k))))
        _ = ∑ i, c i • e.symm (v i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (e.symm.map_smul (c i) (v i))
    have hEq' : (xStar, muStar) = ∑ i, c i • v' i := by
      have hEq' := congrArg e.symm hEq
      simpa [v', hsum] using hEq'
    refine ⟨k, hk, v', c, hv', hc, hEq'⟩

/-- Extract a linearly independent subfamily from a conic representation over `adjoinVertical`. -/
lemma mem_coneK_imp_exists_linIndep_nonnegLinearCombination_adjoinVertical_le {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (xStar : Fin n → Real) (muStar : Real) :
    (xStar, muStar) ∈ coneK (n := n) Sstar →
      ∃ k : Nat, k ≤ n + 1 ∧
        ∃ v : Fin k → (Fin n → Real) × Real, ∃ c : Fin k → Real,
          (∀ i, v i ∈ adjoinVertical (n := n) Sstar) ∧ (∀ i, 0 ≤ c i) ∧
            (xStar, muStar) = ∑ i, c i • v i ∧ LinearIndependent ℝ v := by
  classical
  intro hmem
  rcases
      mem_coneK_imp_exists_nonnegLinearCombination_adjoinVertical_le (n := n) (Sstar := Sstar)
        (xStar := xStar) (muStar := muStar) hmem with
    ⟨k, hk, v, c, hv, hc, hEq⟩
  by_cases hzero : (xStar, muStar) = 0
  ·
    refine ⟨0, by simp, (fun i : Fin 0 => (0, 0)), (fun i : Fin 0 => 0), ?_, ?_, ?_, ?_⟩
    · intro i
      exact (Fin.elim0 i)
    · intro i
      exact (Fin.elim0 i)
    · simp [hzero]
    ·
      simp
  ·
    let e : ((Fin n → Real) × Real) ≃ₗ[Real] (Fin (n + 1) → Real) :=
      prodLinearEquiv_append_coord (n := n)
    let u : Fin k → Fin (n + 1) → Real := fun i => e (v i)
    have hEq_e : e (xStar, muStar) = ∑ i, c i • u i := by
      have hsum :
          e (∑ i, c i • v i) = ∑ i, c i • e (v i) := by
        calc
          e (∑ i, c i • v i) = ∑ i, e (c i • v i) := by
            exact
              (map_sum (g := e) (f := fun i => c i • v i)
                (s := (Finset.univ : Finset (Fin k))))
          _ = ∑ i, c i • e (v i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact (e.map_smul (c i) (v i))
      calc
        e (xStar, muStar) = e (∑ i, c i • v i) := by simp [hEq]
        _ = ∑ i, c i • u i := by simp [u, hsum]
    have hzero' : e (xStar, muStar) ≠ 0 := by
      intro h
      have : (xStar, muStar) = 0 := (e.map_eq_zero_iff).1 h
      exact hzero this
    rcases
        exists_linearIndependent_nonnegLinearCombination_subfamily
          (n := n + 1) (x := e (xStar, muStar)) (v := u) (c := c) hc hEq_e hzero' with
      ⟨m, hm, e0, c0, hc0, hlin, hsum0⟩
    let v' : Fin m → (Fin n → Real) × Real := fun j => v (e0 j)
    have hv' : ∀ j, v' j ∈ adjoinVertical (n := n) Sstar := by
      intro j
      simpa [v'] using hv (e0 j)
    have hEq' : (xStar, muStar) = ∑ j, c0 j • v' j := by
      have hsum0' := congrArg e.symm hsum0
      have hsum' :
          e.symm (∑ j, c0 j • u (e0 j)) = ∑ j, c0 j • e.symm (u (e0 j)) := by
        calc
          e.symm (∑ j, c0 j • u (e0 j)) = ∑ j, e.symm (c0 j • u (e0 j)) := by
            exact
              (map_sum (g := e.symm) (f := fun j => c0 j • u (e0 j))
                (s := (Finset.univ : Finset (Fin m))))
          _ = ∑ j, c0 j • e.symm (u (e0 j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact (e.symm.map_smul (c0 j) (u (e0 j)))
      have hsum0'' :
          (xStar, muStar) = ∑ j, c0 j • e.symm (u (e0 j)) := by
        calc
          (xStar, muStar) = e.symm (e (xStar, muStar)) := by
            simp
          _ = e.symm (∑ j, c0 j • u (e0 j)) := by
            simp [hsum0]
          _ = ∑ j, c0 j • e.symm (u (e0 j)) := by
            simp [hsum']
      simpa [v', u] using hsum0''
    have hlin' : LinearIndependent ℝ v' := by
      have hker : LinearMap.ker (e.symm : _ ≃ₗ[Real] _).toLinearMap = ⊥ := by
        exact LinearMap.ker_eq_bot.2 e.symm.injective
      have hlin' :=
        (LinearIndependent.map' hlin (e.symm : _ ≃ₗ[Real] _).toLinearMap hker)
      have hlin'' : LinearIndependent ℝ (fun j => e.symm (u (e0 j))) := by
        simpa [Function.comp] using hlin'
      have hfun : (fun j => e.symm (u (e0 j))) = v' := by
        funext j
        simp [u, v']
      simpa [hfun] using hlin''
    refine ⟨m, le_trans hm hk, v', c0, hv', hc0, hEq', hlin'⟩

/-- Split a conic combination over `adjoinVertical` into vertical and `Sstar` parts. -/
lemma split_adjoinVertical_conicCombination {n k : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (v : Fin k → (Fin n → Real) × Real) (c : Fin k → Real)
    (hv : ∀ i, v i ∈ adjoinVertical (n := n) Sstar) (hc : ∀ i, 0 ≤ c i) :
    ∃ m : Nat, m ≤ k ∧
      ∃ (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
        (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
          (∑ i, c i • v i) = lam0 • verticalVector n + ∑ i, lam i • p i := by
  classical
  by_cases hSstar : Sstar = ∅
  ·
    have hv' : ∀ i, v i = verticalVector n := by
      intro i
      have hmem := hv i
      simpa [adjoinVertical, hSstar] using hmem
    let lam0 : Real := ∑ i, c i
    have hlam0 : 0 ≤ lam0 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact hc i
    have hEq :
        ∑ i, c i • v i = lam0 • verticalVector n := by
      calc
        ∑ i, c i • v i = ∑ i, c i • verticalVector n := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hv' i]
        _ = (∑ i, c i) • verticalVector n := by
          simpa using
            (Finset.sum_smul (s := (Finset.univ : Finset (Fin k))) (f := c)
              (x := verticalVector n)).symm
        _ = lam0 • verticalVector n := rfl
    refine ⟨0, by simp, (fun i : Fin 0 => (0, 0)), lam0, (fun i : Fin 0 => 0), ?_, ?_, ?_, ?_⟩
    · intro i
      exact (Fin.elim0 i)
    · exact hlam0
    · intro i
      exact (Fin.elim0 i)
    · simp [hEq]
  ·
    have hSstar' : Sstar.Nonempty := Set.nonempty_iff_ne_empty.mpr hSstar
    rcases hSstar' with ⟨p0, hp0⟩
    let lam0 : Real := ∑ i, if v i = verticalVector n then c i else 0
    let lam : Fin k → Real := fun i => if v i = verticalVector n then 0 else c i
    let p : Fin k → (Fin n → Real) × Real :=
      fun i => if v i = verticalVector n then p0 else v i
    have hp : ∀ i, p i ∈ Sstar := by
      intro i
      by_cases hvi : v i = verticalVector n
      · simp [p, hvi, hp0]
      ·
        have hvi' : v i ∈ Sstar := by
          have hmem := hv i
          simpa [adjoinVertical, hvi] using hmem
        simp [p, hvi, hvi']
    have hlam0 : 0 ≤ lam0 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      by_cases hvi : v i = verticalVector n
      · simp [hvi, hc i]
      · simp [hvi]
    have hlam : ∀ i, 0 ≤ lam i := by
      intro i
      by_cases hvi : v i = verticalVector n
      · simp [lam, hvi]
      · simp [lam, hvi, hc i]
    have hsum_lam :
        ∑ i, lam i • p i = ∑ i, (if v i = verticalVector n then 0 else c i) • v i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hvi : v i = verticalVector n
      · simp [lam, p, hvi]
      · simp [lam, p, hvi]
    have hsum_vert :
        ∑ i, (if v i = verticalVector n then c i else 0) • v i =
          lam0 • verticalVector n := by
      calc
        ∑ i, (if v i = verticalVector n then c i else 0) • v i =
            ∑ i, (if v i = verticalVector n then c i else 0) • verticalVector n := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hvi : v i = verticalVector n
              · simp [hvi]
              · simp [hvi]
        _ = (∑ i, if v i = verticalVector n then c i else 0) • verticalVector n := by
              simpa using
                (Finset.sum_smul (s := (Finset.univ : Finset (Fin k)))
                  (f := fun i => if v i = verticalVector n then c i else 0)
                  (x := verticalVector n)).symm
        _ = lam0 • verticalVector n := rfl
    have hsum_split :
        ∑ i, c i • v i =
          ∑ i, (if v i = verticalVector n then c i else 0) • v i +
            ∑ i, (if v i = verticalVector n then 0 else c i) • v i := by
      have hterm :
          (fun i => c i • v i) =
            (fun i =>
              (if v i = verticalVector n then c i else 0) • v i +
                (if v i = verticalVector n then 0 else c i) • v i) := by
        funext i
        by_cases hvi : v i = verticalVector n
        · simp [hvi]
        · simp [hvi]
      simp [hterm, Finset.sum_add_distrib]
    have hEq :
        ∑ i, c i • v i = lam0 • verticalVector n + ∑ i, lam i • p i := by
      calc
        ∑ i, c i • v i =
            ∑ i, (if v i = verticalVector n then c i else 0) • v i +
              ∑ i, (if v i = verticalVector n then 0 else c i) • v i := hsum_split
        _ = lam0 • verticalVector n +
              ∑ i, (if v i = verticalVector n then 0 else c i) • v i := by
              rw [hsum_vert]
        _ = lam0 • verticalVector n + ∑ i, lam i • p i := by
              rw [hsum_lam.symm]
    refine ⟨k, le_rfl, p, lam0, lam, hp, hlam0, hlam, hEq⟩

/-- Corollary 17.2.10 (Carath\'eodory bounds for conic representations), LaTeX label
`cor:caratheodory_bounds`.

In the conic representation from Lemma 17.2.9 (`mem_coneK_iff_exists_conicCombination`), one can
choose:

(1) `m ≤ n + 1` (by Carath\'eodory's theorem in `ℝ^{n+1}`);
(2) `m ≤ n` (via the "bottoms of simplices" argument, as in Corollary 17.1.3). -/
theorem mem_coneK_imp_exists_conicCombination_le_add_one {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (xStar : Fin n → Real) (muStar : Real) :
    (xStar, muStar) ∈ coneK (n := n) Sstar →
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
          (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
            (xStar, muStar) = lam0 • verticalVector n + ∑ i, lam i • p i := by
  intro hmem
  rcases
      mem_coneK_imp_exists_nonnegLinearCombination_adjoinVertical_le (n := n) (Sstar := Sstar)
        (xStar := xStar) (muStar := muStar) hmem with
    ⟨k, hk, v, c, hv, hc, hEq⟩
  rcases
      split_adjoinVertical_conicCombination (n := n) (Sstar := Sstar) (v := v) (c := c) hv hc with
    ⟨m, hm, p, lam0, lam, hp, hlam0, hlam, hEq'⟩
  refine ⟨m, le_trans hm hk, p, lam0, lam, hp, hlam0, hlam, ?_⟩
  calc
    (xStar, muStar) = ∑ i, c i • v i := hEq
    _ = lam0 • verticalVector n + ∑ i, lam i • p i := hEq'

/-- Feasibility bounds the vertical component of a conic sum over `Sstar`. -/
lemma conicSum_snd_nonneg_of_mem_intersectionOfHalfspaces {n m : Nat}
    {Sstar : Set ((Fin n → Real) × Real)} {x0 : Fin n → Real}
    (hx0 : x0 ∈ intersectionOfHalfspaces (n := n) Sstar)
    (p : Fin m → (Fin n → Real) × Real) (lam : Fin m → Real)
    (hp : ∀ i, p i ∈ Sstar) (hlam : ∀ i, 0 ≤ lam i) :
    x0 ⬝ᵥ (∑ i, lam i • (p i).1) ≤ ∑ i, lam i * (p i).2 := by
  classical
  have hx0' : ∀ q ∈ Sstar, x0 ⬝ᵥ q.1 ≤ q.2 := by
    simpa [intersectionOfHalfspaces] using hx0
  have hle_i : ∀ i, lam i * (x0 ⬝ᵥ (p i).1) ≤ lam i * (p i).2 := by
    intro i
    have hq : x0 ⬝ᵥ (p i).1 ≤ (p i).2 := hx0' (p i) (hp i)
    exact mul_le_mul_of_nonneg_left hq (hlam i)
  have hsum :
      ∑ i, lam i * (x0 ⬝ᵥ (p i).1) ≤ ∑ i, lam i * (p i).2 := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hle_i i
  have hdot :
      x0 ⬝ᵥ (∑ i, lam i • (p i).1) = ∑ i, lam i * (x0 ⬝ᵥ (p i).1) := by
    calc
      x0 ⬝ᵥ (∑ i, lam i • (p i).1) = ∑ i, x0 ⬝ᵥ lam i • (p i).1 := by
        simpa using
          (dotProduct_sum (u := x0) (s := (Finset.univ : Finset (Fin m)))
            (v := fun i => lam i • (p i).1))
      _ = ∑ i, lam i * (x0 ⬝ᵥ (p i).1) := by
        simp [dotProduct_smul, smul_eq_mul]
  simpa [hdot] using hsum


end Section17
end Chap04
