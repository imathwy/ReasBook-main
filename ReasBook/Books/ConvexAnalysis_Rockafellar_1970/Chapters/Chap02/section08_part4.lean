/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part3

noncomputable section
open scoped Pointwise

section Chap02
section Section08

/-- Definition 8.4.2. Let `C` be a non-empty convex set. The set
`lin(C) := (-0^+ C) ∩ 0^+ C` is called the lineality space of `C`. -/
def Set.linealitySpace {n : Nat} (C : Set (EuclideanSpace Real (Fin n))) :
    Set (EuclideanSpace Real (Fin n)) :=
  (-Set.recessionCone C) ∩ Set.recessionCone C

/-- Definition 8.4.3. The directions of the vectors `y` in the lineality space of `C` are called
directions in which `C` is linear. -/
def Set.IsLinearDirection {n : Nat} (C : Set (EuclideanSpace Real (Fin n)))
    (y : EuclideanSpace Real (Fin n)) : Prop :=
  y ∈ Set.linealitySpace C

/-- Definition 8.4.4. The dimension of the lineality space `lin(C)` is called the lineality of
`C`. -/
def Set.lineality {n : Nat} (C : Set (EuclideanSpace Real (Fin n))) : Nat :=
  Module.finrank Real (Submodule.span Real (Set.linealitySpace C))

/-- The lineality space of a convex set is a submodule. -/
lemma linealitySpace_isSubmodule {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCconv : Convex Real C) :
    ∃ L : Submodule Real (EuclideanSpace Real (Fin n)), (L : Set _) = Set.linealitySpace C := by
  classical
  refine ⟨{ carrier := Set.linealitySpace C
          , add_mem' := ?_
          , zero_mem' := ?_
          , smul_mem' := ?_ }, rfl⟩
  · intro y z hy hz
    have hy' : y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      simpa [Set.linealitySpace] using hy
    have hz' : z ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      simpa [Set.linealitySpace] using hz
    rcases hy' with ⟨hyneg, hypos⟩
    rcases hz' with ⟨hzneg, hzpos⟩
    have hyneg' : -y ∈ Set.recessionCone C := by simpa using hyneg
    have hzneg' : -z ∈ Set.recessionCone C := by simpa using hzneg
    have hypos' : ∀ x ∈ C, x + y ∈ C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hypos
    have hzpos' : ∀ x ∈ C, x + z ∈ C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hzpos
    have hyneg'' : ∀ x ∈ C, x + (-y) ∈ C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hyneg'
    have hzneg'' : ∀ x ∈ C, x + (-z) ∈ C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hzneg'
    have hsum : y + z ∈ Set.recessionCone C := by
      have hsum' : (y + z) ∈ { y | ∀ x ∈ C, x + y ∈ C } := by
        intro x hx
        have hx' : x + y ∈ C := hypos' x hx
        have hx'' : x + y + z ∈ C := hzpos' (x + y) hx'
        simpa [add_assoc] using hx''
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hsum'
    have hsum_neg : -(y + z) ∈ Set.recessionCone C := by
      have hsum' : (-(y + z)) ∈ { y | ∀ x ∈ C, x + y ∈ C } := by
        intro x hx
        have hx' : x + (-y) ∈ C := hyneg'' x hx
        have hx'' : x + (-y) + (-z) ∈ C := hzneg'' (x + (-y)) hx'
        simpa [add_assoc, add_comm, add_left_comm, neg_add] using hx''
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hsum'
    have hsum_neg' : y + z ∈ -Set.recessionCone C := by
      simpa using hsum_neg
    simpa [Set.linealitySpace] using And.intro hsum_neg' hsum
  · have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
      simp [recessionCone_eq_add_mem (C := C) hCconv]
    have hzero_neg : (0 : EuclideanSpace Real (Fin n)) ∈ -Set.recessionCone C := by
      simpa using hzero
    change (0 : EuclideanSpace Real (Fin n)) ∈ (-Set.recessionCone C) ∩ Set.recessionCone C
    exact ⟨hzero_neg, hzero⟩
  · intro r y hy
    have hy' : y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      simpa [Set.linealitySpace] using hy
    rcases hy' with ⟨hyneg, hypos⟩
    have hyneg' : -y ∈ Set.recessionCone C := by simpa using hyneg
    by_cases hr0 : r = 0
    · have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
        simp [recessionCone_eq_add_mem (C := C) hCconv]
      have hzero_neg : (0 : EuclideanSpace Real (Fin n)) ∈ -Set.recessionCone C := by
        simpa using hzero
      have hzero_lin : (0 : EuclideanSpace Real (Fin n)) ∈ Set.linealitySpace C := by
        simpa [Set.linealitySpace] using And.intro hzero_neg hzero
      simpa [hr0] using hzero_lin
    · by_cases hrpos : 0 < r
      · have hpos : r • y ∈ Set.recessionCone C :=
          recessionCone_smul_pos (C := C) hypos hrpos
        have hneg : r • (-y) ∈ Set.recessionCone C :=
          recessionCone_smul_pos (C := C) hyneg' hrpos
        have hneg' : -(r • y) ∈ Set.recessionCone C := by
          simpa [smul_neg] using hneg
        have hneg'' : r • y ∈ -Set.recessionCone C := by
          simpa using hneg'
        simpa [Set.linealitySpace] using And.intro hneg'' hpos
      · have hrneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hrpos) hr0
        let t : Real := -r
        have htpos : 0 < t := by
          dsimp [t]
          linarith
        have htpos' : t • (-y) ∈ Set.recessionCone C :=
          recessionCone_smul_pos (C := C) hyneg' htpos
        have htpos'' : t • y ∈ Set.recessionCone C :=
          recessionCone_smul_pos (C := C) hypos htpos
        have hpos : r • y ∈ Set.recessionCone C := by
          have : r • y = t • (-y) := by
            simp [t, smul_neg, neg_smul]
          simpa [this] using htpos'
        have hneg : -(r • y) ∈ Set.recessionCone C := by
          have : -(r • y) = t • y := by
            simp [t, neg_smul]
          simpa [this] using htpos''
        have hneg' : r • y ∈ -Set.recessionCone C := by
          simpa using hneg
        simpa [Set.linealitySpace] using And.intro hneg' hpos

/-- The lineality space is contained in the direction of the affine span. -/
lemma linealitySpace_subset_direction_affineSpan {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) :
    Set.linealitySpace C ⊆ (affineSpan Real C).direction := by
  intro y hy
  rcases hCne with ⟨x0, hx0⟩
  have hCne' : C.Nonempty := ⟨x0, hx0⟩
  have hy'' : y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    simpa [Set.linealitySpace] using hy
  have hEq :
      (-Set.recessionCone C) ∩ Set.recessionCone C =
        { y : EuclideanSpace Real (Fin n) | Set.image (fun x => x + y) C = C } :=
    linealitySpace_eq_translation (C := C) hCne' hCconv
  have hy' : y ∈ { y : EuclideanSpace Real (Fin n) | Set.image (fun x => x + y) C = C } :=
    hEq ▸ hy''
  have hyadd : ∀ x ∈ C, x + y ∈ C :=
    (add_mem_of_image_eq (C := C) (y := y) hy').1
  have hx0y : x0 + y ∈ C := hyadd x0 hx0
  have hx0y' : x0 + y ∈ affineSpan Real C :=
    subset_affineSpan (k := Real) (s := C) hx0y
  have hx0' : x0 ∈ affineSpan Real C := subset_affineSpan (k := Real) (s := C) hx0
  have hdir : (x0 + y) -ᵥ x0 ∈ (affineSpan Real C).direction :=
    AffineSubspace.vsub_mem_direction (s := affineSpan Real C) hx0y' hx0'
  simpa [vsub_eq_sub, add_assoc] using hdir

/-- Rank zero forces the affine span direction to be the lineality submodule. -/
lemma direction_eq_linealitySpace_of_rank_eq_zero {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) (hrank : Set.rank C = 0) :
    ∃ L : Submodule Real (EuclideanSpace Real (Fin n)),
      (L : Set _) = Set.linealitySpace C ∧ (affineSpan Real C).direction = L := by
  rcases linealitySpace_isSubmodule (C := C) hCconv with ⟨L, hL⟩
  have hsubset : Set.linealitySpace C ⊆ (affineSpan Real C).direction :=
    linealitySpace_subset_direction_affineSpan (C := C) hCne hCconv
  have hspan_le :
      Submodule.span Real (Set.linealitySpace C) ≤ (affineSpan Real C).direction :=
    Submodule.span_le.2 hsubset
  have hle :
      Module.finrank Real (affineSpan Real C).direction ≤
        Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) := by
    have hrank' :
        Module.finrank Real (affineSpan Real C).direction -
            Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) = 0 := by
      simpa [Set.rank, Set.linealitySpace] using hrank
    exact (Nat.sub_eq_zero_iff_le).1 hrank'
  have hspan_eq :
      Submodule.span Real (Set.linealitySpace C) = (affineSpan Real C).direction :=
    Submodule.eq_of_le_of_finrank_le hspan_le hle
  have hspan_eq_L : Submodule.span Real (Set.linealitySpace C) = L := by
    simpa [hL] using (Submodule.span_eq (p := L))
  have hdir_eq : (affineSpan Real C).direction = L := by
    calc
      (affineSpan Real C).direction =
          Submodule.span Real (Set.linealitySpace C) := by
            simpa using hspan_eq.symm
      _ = L := hspan_eq_L
  exact ⟨L, hL, hdir_eq⟩

/-- Rank zero implies the set is a translate of its lineality space. -/
lemma C_eq_translate_linealitySpace {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) (hrank : Set.rank C = 0) :
    ∃ x0 ∈ C, C = (fun v => x0 + v) '' Set.linealitySpace C := by
  rcases hCne with ⟨x0, hx0⟩
  have hCne' : C.Nonempty := ⟨x0, hx0⟩
  rcases direction_eq_linealitySpace_of_rank_eq_zero (C := C) hCne' hCconv hrank with
    ⟨L, hL, hdir_eq⟩
  have htrans : Set.image (fun v => x0 + v) (Set.linealitySpace C) ⊆ C := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy'' : y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      simpa [Set.linealitySpace] using hy
    have hEq :
        (-Set.recessionCone C) ∩ Set.recessionCone C =
          { y : EuclideanSpace Real (Fin n) | Set.image (fun x => x + y) C = C } :=
      linealitySpace_eq_translation (C := C) hCne' hCconv
    have hy' : y ∈ { y : EuclideanSpace Real (Fin n) | Set.image (fun x => x + y) C = C } :=
      hEq ▸ hy''
    have hyadd : ∀ x ∈ C, x + y ∈ C :=
      (add_mem_of_image_eq (C := C) (y := y) hy').1
    exact hyadd x0 hx0
  have hsubset : C ⊆ Set.image (fun v => x0 + v) (Set.linealitySpace C) := by
    intro x hx
    have hx0' : x0 ∈ affineSpan Real C := subset_affineSpan (k := Real) (s := C) hx0
    have hx' : x ∈ affineSpan Real C := subset_affineSpan (k := Real) (s := C) hx
    have hdir : x -ᵥ x0 ∈ (affineSpan Real C).direction :=
      AffineSubspace.vsub_mem_direction (s := affineSpan Real C) hx' hx0'
    have hdir' : x - x0 ∈ L := by
      have hdir'' : x - x0 ∈ (affineSpan Real C).direction := by
        simpa [vsub_eq_sub] using hdir
      simpa [hdir_eq] using hdir''
    have hlin : x - x0 ∈ Set.linealitySpace C := by
      rw [← hL]
      exact hdir'
    refine ⟨x - x0, hlin, ?_⟩
    simp
  refine ⟨x0, hx0, ?_⟩
  exact Set.Subset.antisymm hsubset htrans

/-- An affine subspace has rank zero. -/
lemma rank_affineSubspace_eq_zero {n : Nat}
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    (hM : (M : Set (EuclideanSpace Real (Fin n))).Nonempty) :
    Set.rank (M : Set (EuclideanSpace Real (Fin n))) = 0 := by
  have hrec : Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) =
      (M.direction : Set (EuclideanSpace Real (Fin n))) :=
    recessionCone_affineSubspace_eq_direction (M := M) hM (L := M.direction) rfl
  have hneg :
      (- (M.direction : Set (EuclideanSpace Real (Fin n)))) =
        (M.direction : Set (EuclideanSpace Real (Fin n))) := by
    ext y
    constructor
    · intro hy
      have hy' : -y ∈ M.direction := by simpa using hy
      exact (M.direction.neg_mem_iff).1 hy'
    · intro hy
      have hy' : -y ∈ M.direction := (M.direction.neg_mem_iff).2 hy
      simpa using hy'
  have hlin :
      (-Set.recessionCone (M : Set (EuclideanSpace Real (Fin n)))) ∩
          Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) =
        (M.direction : Set (EuclideanSpace Real (Fin n))) := by
    simp [hrec, hneg]
  have hspan : affineSpan Real (M : Set (EuclideanSpace Real (Fin n))) = M := by
    simp
  have hdir :
      (affineSpan Real (M : Set (EuclideanSpace Real (Fin n)))).direction = M.direction := by
    simp [hspan]
  have hrank0 :
      Set.rank (M : Set (EuclideanSpace Real (Fin n))) =
        Module.finrank Real (affineSpan Real (M : Set (EuclideanSpace Real (Fin n)))).direction -
          Module.finrank Real
            (Submodule.span Real
              ((-Set.recessionCone (M : Set (EuclideanSpace Real (Fin n)))) ∩
                Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))))) := rfl
  have hrank1 := hrank0
  rw [hdir] at hrank1
  have hrank2 := hrank1
  rw [hlin] at hrank2
  have hspan_eq' : Submodule.span Real (M.direction : Set _) = M.direction := by
    simp
  have hrank3 := hrank2
  rw [hspan_eq'] at hrank3
  simpa using hrank3

/-- Theorem 8.4.7. Let `C` be a non-empty convex set. Then `C` has rank `0` if and only if `C`
is an affine set. -/
theorem rank_eq_zero_iff_isAffineSet {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) :
    Set.rank C = 0 ↔
      IsAffineSet n
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n) :
            EuclideanSpace Real (Fin n) → Fin n → Real)
          '' C) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  constructor
  · intro hrank
    obtain ⟨x0, hx0, hCeq⟩ :=
      C_eq_translate_linealitySpace (C := C) hCne hCconv hrank
    rcases linealitySpace_isSubmodule (C := C) hCconv with ⟨L, hL⟩
    let s : AffineSubspace Real (EuclideanSpace Real (Fin n)) := AffineSubspace.mk' x0 L
    have hCeq' : C = (fun v => x0 + v) '' (L : Set (EuclideanSpace Real (Fin n))) := by
      simpa [hL] using hCeq
    have hs : (s : Set (EuclideanSpace Real (Fin n))) = C := by
      have hmk :
          (s : Set (EuclideanSpace Real (Fin n))) =
            (fun v => x0 + v) '' (L : Set (EuclideanSpace Real (Fin n))) := by
        ext x
        constructor
        · intro hx
          refine ⟨x - x0, ?_, ?_⟩
          · simpa [vsub_eq_sub] using hx
          · simp
        · rintro ⟨v, hv, rfl⟩
          have : (x0 + v) -ᵥ x0 = v := by
            simp
          simpa [s, AffineSubspace.mem_mk', this] using hv
      calc
        (s : Set (EuclideanSpace Real (Fin n))) =
            (fun v => x0 + v) '' (L : Set (EuclideanSpace Real (Fin n))) := hmk
        _ = C := hCeq'.symm
    have hAff :
        ∃ s' : AffineSubspace Real (Fin n → Real),
          (s' : Set (Fin n → Real)) = e '' C := by
      refine ⟨s.map (e.toLinearEquiv.toLinearMap.toAffineMap), ?_⟩
      simp [AffineSubspace.coe_map, hs]
    exact (isAffineSet_iff_affineSubspace n (e '' C)).2 hAff
  · intro hAff
    rcases (isAffineSet_iff_affineSubspace n (e '' C)).1 hAff with ⟨s, hs⟩
    let s' : AffineSubspace Real (EuclideanSpace Real (Fin n)) :=
      AffineSubspace.map (e.symm.toLinearEquiv.toLinearMap.toAffineMap) s
    have hs' : (s' : Set (EuclideanSpace Real (Fin n))) = C := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        have hy' : y ∈ e '' C := by
          simpa [hs] using hy
        rcases hy' with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        refine ⟨e x, ?_, ?_⟩
        · have : e x ∈ e '' C := ⟨x, hx, rfl⟩
          simpa [hs] using this
        · simp
    have hne : (s' : Set (EuclideanSpace Real (Fin n))).Nonempty := by
      simpa [hs'] using hCne
    have hrank : Set.rank (s' : Set (EuclideanSpace Real (Fin n))) = 0 :=
      rank_affineSubspace_eq_zero (M := s') hne
    simpa [hs'] using hrank

/-- A line is nonempty. -/
lemma nonempty_of_isLine {n : Nat} {L : Set (Fin n → Real)} (hL : IsLine n L) :
    Set.Nonempty L := by
  rcases hL with ⟨hAff, hdim⟩
  by_contra hne
  have hdim' : affineSetDim n L hAff = -1 := by
    simp [affineSetDim, hne]
  have hbad : (1 : Int) = -1 := by
    exact hdim.symm.trans hdim'
  exact (by decide : (1 : Int) ≠ -1) hbad

set_option maxHeartbeats 400000 in
-- Needed for finrank/lineality simplification in this lemma.
/-- Rank equals dimension iff the lineality span has finrank zero. -/
lemma rank_eq_dim_iff_lineality_finrank_zero {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) :
    Set.rank C = Module.finrank Real (affineSpan Real C).direction ↔
      Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) = 0 := by
  have hsubset : Set.linealitySpace C ⊆ (affineSpan Real C).direction :=
    linealitySpace_subset_direction_affineSpan (C := C) hCne hCconv
  have hspan_le :
      Submodule.span Real (Set.linealitySpace C) ≤ (affineSpan Real C).direction :=
    Submodule.span_le.2 hsubset
  have hfin_le :
      Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) ≤
        Module.finrank Real (affineSpan Real C).direction :=
    Submodule.finrank_mono hspan_le
  let a := Module.finrank Real (affineSpan Real C).direction
  let b := Module.finrank Real (Submodule.span Real (Set.linealitySpace C))
  constructor
  · intro hrank
    have hrank' : a - b = a := by
      have hrank' := hrank
      simp [Set.rank] at hrank'
      exact hrank'
    have hEq : a = a + b := (Nat.sub_eq_iff_eq_add hfin_le).1 hrank'
    have hEq' : a + 0 = a + b := by
      simpa using hEq
    have hb : b = 0 := by
      exact (Nat.add_left_cancel hEq').symm
    simp [b, hb]
  · intro hb
    have hb' :
        Module.finrank Real
            (Submodule.span Real ((-Set.recessionCone C) ∩ Set.recessionCone C)) = 0 := by
      simpa [Set.linealitySpace, b] using hb
    simp [Set.rank, hb']

/-- A translate of the span of a nonzero vector is a line. -/
lemma isLine_of_translate_span_singleton {n : Nat} {y : Fin n → Real} (hy : y ≠ 0)
    (x0 : Fin n → Real) :
    IsLine n (SetTranslate n (Submodule.span Real {y} : Set (Fin n → Real)) x0) := by
  classical
  let M : Set (Fin n → Real) :=
    SetTranslate n (Submodule.span Real {y} : Set (Fin n → Real)) x0
  have hM : IsAffineSet n M := by
    have hsub : IsAffineSet n (Submodule.span Real {y} : Set (Fin n → Real)) :=
      isAffineSet_of_submodule n (Submodule.span Real {y})
    dsimp [M]
    exact isAffineSet_translate n (Submodule.span Real {y} : Set (Fin n → Real)) x0 hsub
  have hne : Set.Nonempty M := by
    refine ⟨x0, ?_⟩
    refine ⟨0, ?_, by simp⟩
    simp
  let L0 : Submodule Real (Fin n → Real) :=
    Classical.choose (parallel_submodule_unique_of_affine n M hM hne).exists
  have hL0 : IsParallelAffineSet n M (L0 : Set (Fin n → Real)) :=
    (Classical.choose_spec (parallel_submodule_unique_of_affine n M hM hne).exists).1
  have hparallel : IsParallelAffineSet n M (Submodule.span Real {y} : Set (Fin n → Real)) := by
    refine ⟨x0, ?_⟩
    rfl
  have hL0_eq : L0 = Submodule.span Real {y} :=
    parallel_submodule_unique n M L0 (Submodule.span Real {y}) hL0 hparallel
  have hfin : Module.finrank Real L0 = 1 := by
    rw [hL0_eq]
    simpa using (finrank_span_singleton (v := y) (K := Real) hy)
  have hdim : affineSetDim n M hM = 1 := by
    simp [affineSetDim, hne, L0, hfin]
  exact ⟨hM, hdim⟩

/-- A nonzero lineality direction yields a line contained in the image. -/
lemma exists_line_of_nonzero_lineality {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hlin : ∃ y, y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    ∃ L : Set (Fin n → Real), IsLine n L ∧
      L ⊆
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n) :
            EuclideanSpace Real (Fin n) → Fin n → Real)
          '' C) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  rcases hCne with ⟨x0, hx0⟩
  rcases hlin with ⟨y, hyne, hy⟩
  have hyne' : e y ≠ 0 := by
    intro h
    apply hyne
    have h' := congrArg e.symm h
    simpa using h'
  let L : Set (Fin n → Real) :=
    SetTranslate n (Submodule.span Real {e y} : Set (Fin n → Real)) (e x0)
  have hLline : IsLine n L := by
    simpa [L] using
      (isLine_of_translate_span_singleton (n := n) (y := e y) hyne' (x0 := e x0))
  have hsubset : L ⊆ e '' C := by
    intro z hz
    rcases hz with ⟨v, hv, rfl⟩
    have hv' : v ∈ (Real ∙ e y) := hv
    rcases (Submodule.mem_span_singleton).1 hv' with ⟨r, rfl⟩
    rcases hy with ⟨hyneg, hypos⟩
    have hypos' : y ∈ Set.recessionCone C := hypos
    have hyneg' : -y ∈ Set.recessionCone C := by
      simpa using hyneg
    have hx : x0 + r • y ∈ C := by
      by_cases hr : 0 ≤ r
      · exact hypos' hx0 hr
      · have hr' : 0 ≤ -r := by linarith
        have hx' : x0 + (-r) • (-y) ∈ C := hyneg' hx0 hr'
        simpa [smul_neg, neg_smul] using hx'
    refine ⟨x0 + r • y, hx, ?_⟩
    calc
      e (x0 + r • y) = e x0 + r • e y := by simp
      _ = r • e y + e x0 := by simp [add_comm]
  exact ⟨L, hLline, hsubset⟩

/-- A line contained in the image yields a nonzero lineality direction. -/
lemma nonzero_lineality_of_line {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hline :
      ∃ L : Set (Fin n → Real), IsLine n L ∧
        L ⊆
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n) :
              EuclideanSpace Real (Fin n) → Fin n → Real)
            '' C)) :
    ∃ y : EuclideanSpace Real (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  rcases hline with ⟨L, hLline, hLsubset⟩
  rcases hLline with ⟨hLaff, hLdim⟩
  have hneL : Set.Nonempty L := nonempty_of_isLine ⟨hLaff, hLdim⟩
  let L0 : Submodule Real (Fin n → Real) :=
    Classical.choose (parallel_submodule_unique_of_affine n L hLaff hneL).exists
  have hL0 : IsParallelAffineSet n L (L0 : Set (Fin n → Real)) :=
    (Classical.choose_spec (parallel_submodule_unique_of_affine n L hLaff hneL).exists).1
  rcases hL0 with ⟨a, hLtrans⟩
  have haL : a ∈ L := by
    have : (0 : Fin n → Real) + a ∈ SetTranslate n (L0 : Set (Fin n → Real)) a := by
      exact ⟨0, L0.zero_mem, by simp⟩
    simpa [hLtrans] using this
  have haCimg : a ∈ e '' C := hLsubset haL
  rcases haCimg with ⟨a0, ha0, ha0eq⟩
  have hdim' : affineSetDim n L hLaff = Int.ofNat (Module.finrank Real L0) := by
    simp [affineSetDim, hneL, L0]
  have hfin : Module.finrank Real L0 = 1 := by
    apply Int.ofNat.inj
    calc
      Int.ofNat (Module.finrank Real L0) = affineSetDim n L hLaff := by
        exact hdim'.symm
      _ = 1 := hLdim
  have hnebot : (L0 : Submodule Real (Fin n → Real)) ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank Real L0 = 0 :=
      (Submodule.finrank_eq_zero (S := L0)).2 hbot
    have : (1 : Nat) = 0 := by
      exact hfin.symm.trans h0
    exact one_ne_zero this
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hnebot with ⟨y0, hy0L0, hy0ne⟩
  let y : EuclideanSpace Real (Fin n) := e.symm y0
  have hyne : y ≠ 0 := by
    intro h
    apply hy0ne
    have h' := congrArg e h
    have : y0 = 0 := by
      simpa [y] using h'
    exact this
  have hhalf :
      ∀ y0 ∈ L0, ∀ t : Real, 0 ≤ t → a0 + t • (e.symm y0) ∈ C := by
    intro y0 hy0 t ht
    have hy0' : t • y0 ∈ L0 := L0.smul_mem t hy0
    have hzL : a + t • y0 ∈ L := by
      have hzL' : t • y0 + a ∈ L := by
        have : t • y0 + a ∈ SetTranslate n (L0 : Set (Fin n → Real)) a := by
          exact ⟨t • y0, hy0', rfl⟩
        simpa [hLtrans] using this
      simpa [add_comm] using hzL'
    have hzC : a + t • y0 ∈ e '' C := hLsubset hzL
    rcases hzC with ⟨x, hxC, hx_eq⟩
    have hx_eq' : x = a0 + t • (e.symm y0) := by
      apply e.injective
      have hmap : e (a0 + t • (e.symm y0)) = a + t • y0 := by
        calc
          e (a0 + t • (e.symm y0)) = e a0 + t • e (e.symm y0) := by simp
          _ = a + t • y0 := by simp [ha0eq]
      simpa [hmap] using hx_eq
    simpa [hx_eq'] using hxC
  have hypos : y ∈ Set.recessionCone C := by
    have hhalf_y : ∀ t : Real, 0 ≤ t → a0 + t • y ∈ C := by
      intro t ht
      simpa [y] using hhalf y0 hy0L0 t ht
    exact halfline_mem_recessionCone (C := C) hCne hCclosed hCconv (x0 := a0) (y := y) hhalf_y
  have hyneg : -y ∈ Set.recessionCone C := by
    have hy0neg : -y0 ∈ L0 := L0.neg_mem hy0L0
    have hhalf_y : ∀ t : Real, 0 ≤ t → a0 + t • (-y) ∈ C := by
      intro t ht
      have h' := hhalf (-y0) hy0neg t ht
      simpa [y] using h'
    exact halfline_mem_recessionCone (C := C) hCne hCclosed hCconv (x0 := a0) (y := -y) hhalf_y
  have hyneg' : y ∈ -Set.recessionCone C := by
    simpa using hyneg
  refine ⟨y, hyne, ?_⟩
  change y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C
  exact ⟨hyneg', hypos⟩

/-- Theorem 8.4.8. The rank of a closed convex set equals its dimension if and only if the set
contains no lines. -/
theorem rank_eq_dim_iff_no_lines {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCclosed : IsClosed C) (hCconv : Convex Real C) :
    Set.rank C = Module.finrank Real (affineSpan Real C).direction ↔
      ¬ ∃ L : Set (Fin n → Real), IsLine n L ∧
        L ⊆
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n) :
              EuclideanSpace Real (Fin n) → Fin n → Real)
            '' C) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  by_cases hCne : C.Nonempty
  · have hrank :
        Set.rank C = Module.finrank Real (affineSpan Real C).direction ↔
          Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) = 0 :=
      rank_eq_dim_iff_lineality_finrank_zero (C := C) hCne hCconv
    have hline_iff :
        (∃ y, y ≠ 0 ∧ y ∈ Set.linealitySpace C) ↔
          ∃ L : Set (Fin n → Real), IsLine n L ∧ L ⊆ e '' C := by
      constructor
      · intro hy
        exact exists_line_of_nonzero_lineality (C := C) hCne hy
      · intro hline
        exact nonzero_lineality_of_line (C := C) hCne hCclosed hCconv hline
    have hno_line_iff :
        (¬ ∃ y, y ≠ 0 ∧ y ∈ Set.linealitySpace C) ↔
          ¬ ∃ L : Set (Fin n → Real), IsLine n L ∧ L ⊆ e '' C :=
      not_congr hline_iff
    have hfin_no :
        Module.finrank Real (Submodule.span Real (Set.linealitySpace C)) = 0 ↔
          ¬ ∃ y, y ≠ 0 ∧ y ∈ Set.linealitySpace C := by
      constructor
      · intro hfin
        have hspan_eq :
            Submodule.span Real (Set.linealitySpace C) = ⊥ :=
          (Submodule.finrank_eq_zero (S := Submodule.span Real (Set.linealitySpace C))).1 hfin
        intro hy
        rcases hy with ⟨y, hyne, hy⟩
        have hyspan :
            y ∈ Submodule.span Real (Set.linealitySpace C) :=
          Submodule.subset_span hy
        have hy0 : y = 0 := by
          have : y ∈ (⊥ : Submodule Real (EuclideanSpace Real (Fin n))) := by
            simpa [hspan_eq] using hyspan
          simpa using this
        exact hyne hy0
      · intro hno
        have hsubset :
            Set.linealitySpace C ⊆ ({0} : Set (EuclideanSpace Real (Fin n))) := by
          intro y hy
          by_contra hyne
          have hyne' : y ≠ 0 := by
            simpa using hyne
          exact hno ⟨y, hyne', hy⟩
        have hspan_eq :
            Submodule.span Real (Set.linealitySpace C) = ⊥ :=
          (Submodule.span_eq_bot).2 hsubset
        exact
          (Submodule.finrank_eq_zero (S := Submodule.span Real (Set.linealitySpace C))).2 hspan_eq
    exact hrank.trans (hfin_no.trans hno_line_iff)
  · have hCempty : C = ∅ := by
      classical
      by_contra hne
      exact hCne (Set.nonempty_iff_ne_empty.2 hne)
    have hleft :
        Set.rank C = Module.finrank Real (affineSpan Real C).direction := by
      have hspan : affineSpan Real C = ⊥ := (affineSpan_eq_bot (k := Real) (s := C)).2 hCempty
      have hdir : (affineSpan Real C).direction = ⊥ := by
        simp [hspan]
      have hdir0 : Module.finrank Real (affineSpan Real C).direction = 0 := by
        simp [hdir]
      have hrank0 : Set.rank C = 0 := by
        simp [Set.rank, hdir0]
      simp [hdir0, hrank0]
    have hright :
        ¬ ∃ L : Set (Fin n → Real), IsLine n L ∧ L ⊆ e '' C := by
      intro hline
      rcases hline with ⟨L, hLline, hLsubset⟩
      have hneL : Set.Nonempty L := nonempty_of_isLine hLline
      rcases hneL with ⟨x, hx⟩
      have hx' : x ∈ e '' C := hLsubset hx
      rcases hx' with ⟨y, hy, _⟩
      exact hCne ⟨y, hy⟩
    constructor
    · intro _; exact hright
    · intro _; exact hleft

end Section08
end Chap02
