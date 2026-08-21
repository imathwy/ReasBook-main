/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section01_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2

open scoped Pointwise

section Chap03
section Section13

/-- Text 13.0.1: Let `C` be a convex set. The support function `δ^*(· | C)` of `C` is defined by

`δ^*(x^* | C) = sup { ⟪x, x^*⟫ | x ∈ C }`. -/
noncomputable abbrev deltaStar {n : Nat} (C : Set (Fin n → Real)) : (Fin n → Real) → ℝ :=
  supportFunction C

/-- Rewrite `supportFunction` as an `sSup` over an image. -/
lemma supportFunction_eq_sSup_image_dotProduct {n : Nat} (C : Set (Fin n → Real))
    (x : Fin n → Real) :
    supportFunction C x = sSup (Set.image (fun y : Fin n → Real => dotProduct x y) C) := by
  classical
  have hset :
      {r : ℝ | ∃ y ∈ C, r = dotProduct x y} =
        Set.image (fun y : Fin n → Real => dotProduct x y) C := by
    ext r
    constructor
    · rintro ⟨y, hyC, rfl⟩
      exact ⟨y, hyC, rfl⟩
    · rintro ⟨y, hyC, rfl⟩
      exact ⟨y, hyC, rfl⟩
  simp [supportFunction, hset]

/-- The dot-product image-set at `-xStar` is the `(-1)`-scaled dot-product image-set at `xStar`. -/
lemma image_dotProduct_neg_left_eq_neg_smul_image_dotProduct {n : Nat} (C : Set (Fin n → Real))
    (xStar : Fin n → Real) :
    Set.image (fun y : Fin n → Real => dotProduct (-xStar) y) C =
      (-1 : ℝ) • Set.image (fun y : Fin n → Real => dotProduct y xStar) C := by
  classical
  ext r
  constructor
  · rintro ⟨y, hyC, rfl⟩
    refine (Set.mem_smul_set).2 ?_
    refine ⟨dotProduct y xStar, ⟨y, hyC, rfl⟩, ?_⟩
    simp [dotProduct_comm]
  · intro hr
    rcases (Set.mem_smul_set).1 hr with ⟨s, hsS, hsEq⟩
    rcases hsS with ⟨y, hyC, rfl⟩
    refine ⟨y, hyC, ?_⟩
    calc
      dotProduct (-xStar) y = (-1 : ℝ) • dotProduct y xStar := by
        simp [dotProduct_comm]
      _ = r := hsEq

/-- Scaling a real set by `-1` swaps `sSup` and `sInf`. -/
lemma sSup_neg_one_smul_eq_neg_sInf (S : Set ℝ) : sSup ((-1 : ℝ) • S) = -sInf S := by
  simpa using (Real.sSup_smul_of_nonpos (a := (-1 : ℝ)) (by norm_num) S)

/-- Text 13.0.2: Let `C` be a convex set. Then

`inf { ⟪x, x^*⟫ | x ∈ C } = -δ^*(-x^* | C)`,

where `δ^*(· | C)` is the support function of `C`. -/
theorem sInf_dotProduct_eq_neg_deltaStar {n : Nat} (C : Set (Fin n → Real)) (xStar : Fin n → Real)
    (_hC : Convex ℝ C) :
    sInf (Set.image (fun x => dotProduct x xStar) C) = -(deltaStar C (-xStar)) := by
  classical
  set S : Set ℝ := Set.image (fun x : Fin n → Real => dotProduct x xStar) C with hS
  have hdelta : deltaStar C (-xStar) = -sInf S := by
    calc
      deltaStar C (-xStar) = supportFunction C (-xStar) := by simp [deltaStar]
      _ = sSup (Set.image (fun y : Fin n → Real => dotProduct (-xStar) y) C) := by
        exact supportFunction_eq_sSup_image_dotProduct (C := C) (x := -xStar)
      _ = sSup ((-1 : ℝ) • S) := by
        have himage :
            Set.image (fun y : Fin n → Real => dotProduct (-xStar) y) C = (-1 : ℝ) • S := by
          simpa [hS] using
            (image_dotProduct_neg_left_eq_neg_smul_image_dotProduct (C := C) (xStar := xStar))
        rw [himage]
      _ = -sInf S := by simpa using (sSup_neg_one_smul_eq_neg_sInf (S := S))
  simp [hS, hdelta]

/-- Rewrite `deltaStar` as an `sSup` of `dotProduct x xStar` over `x ∈ C`. -/
lemma deltaStar_eq_sSup_image_dotProduct_right {n : Nat} (C : Set (Fin n → Real))
    (xStar : Fin n → Real) :
    deltaStar C xStar = sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C) := by
  classical
  have himage :
      Set.image (fun y : Fin n → Real => dotProduct xStar y) C =
        Set.image (fun y : Fin n → Real => dotProduct y xStar) C := by
    refine Set.image_congr' ?_
    intro y
    simp [dotProduct_comm]
  calc
    deltaStar C xStar = supportFunction C xStar := by simp [deltaStar]
    _ = sSup (Set.image (fun y : Fin n → Real => dotProduct xStar y) C) := by
      simpa using (supportFunction_eq_sSup_image_dotProduct (C := C) (x := xStar))
    _ = sSup (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) := by
      rw [himage]

/-- Convert the pointwise bound on the dot-product image-set to a halfspace inclusion. -/
lemma forall_image_dotProduct_le_iff_subset_halfspace {n : Nat} (C : Set (Fin n → Real))
    (xStar : Fin n → Real) (β : ℝ) :
    (∀ r ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C, r ≤ β) ↔
      C ⊆ { x | dotProduct x xStar ≤ β } := by
  constructor
  · intro himage x hxC
    have hximg :
        dotProduct x xStar ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C :=
      ⟨x, hxC, rfl⟩
    exact himage _ hximg
  · intro hsubset r hr
    rcases hr with ⟨x, hxC, rfl⟩
    exact hsubset hxC

/-- A `csSup` inequality over the dot-product image-set is equivalent to a pointwise bound. -/
lemma csSup_image_dotProduct_le_iff {n : Nat} (C : Set (Fin n → Real)) (xStar : Fin n → Real)
    (β : ℝ) (hCne : C.Nonempty)
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    (sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C) ≤ β) ↔
      (∀ r ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C, r ≤ β) := by
  simpa using
    (csSup_le_iff (s := Set.image (fun x : Fin n → Real => dotProduct x xStar) C) (a := β) hbdd
      (hCne.image (fun x : Fin n → Real => dotProduct x xStar)))

/-- Text 13.0.3: Let `C` be a convex set. Then

`C ⊆ { x | ⟪x, x^*⟫ ≤ β }` if and only if `β ≥ δ^*(x^* | C)`. -/
theorem subset_halfspace_iff_ge_deltaStar {n : Nat} (C : Set (Fin n → Real)) (xStar : Fin n → Real)
    (β : ℝ) (_hC : Convex ℝ C) (hCne : C.Nonempty)
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    C ⊆ { x | dotProduct x xStar ≤ β } ↔ β ≥ deltaStar C xStar := by
  classical
  constructor
  · intro hsubset
    have hpoint :
        ∀ r ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C, r ≤ β := by
      intro r hr
      rcases hr with ⟨x, hxC, rfl⟩
      exact hsubset hxC
    have hsSup :
        sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C) ≤ β :=
      csSup_le (hCne.image (fun x : Fin n → Real => dotProduct x xStar)) hpoint
    have : deltaStar C xStar ≤ β := by
      simpa [deltaStar_eq_sSup_image_dotProduct_right] using hsSup
    simpa using this
  · intro hβ
    have : deltaStar C xStar ≤ β := by
      simpa using hβ
    have hsSup :
        sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C) ≤ β := by
      simpa [deltaStar_eq_sSup_image_dotProduct_right] using this
    have hpoint :
        ∀ r ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C, r ≤ β :=
      (csSup_image_dotProduct_le_iff (C := C) (xStar := xStar) (β := β) hCne hbdd).1 hsSup
    exact (forall_image_dotProduct_le_iff_subset_halfspace (C := C) (xStar := xStar) (β := β)).1 hpoint

/-- Text 13.0.4: Let `C ⊆ ℝ^n` be a nonempty convex set. The barrier cone of `C`, equivalently the
effective domain of the support function `δ^*(· | C)`, is

`bar C = dom (δ^*(· | C)) = {x^* | sup {⟪x, x^*⟫ | x ∈ C} < +∞ }`. -/
noncomputable def barrierCone13 {n : Nat} (C : Set (Fin n → Real)) : Set (Fin n → Real) :=
  effectiveDomain (Set.univ : Set (Fin n → Real)) (fun xStar =>
    sSup {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : Real) : EReal)})

/-- The support function is unchanged by taking the (topological) closure of the set. -/
lemma deltaStar_eq_deltaStar_closure {n : Nat} (C : Set (Fin n → Real)) (xStar : Fin n → Real) :
    deltaStar C xStar = deltaStar (closure C) xStar := by
  classical
  by_cases hCempty : C = ∅
  · simp [deltaStar_eq_sSup_image_dotProduct_right, hCempty]
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
  set f : (Fin n → Real) → ℝ := fun x => dotProduct x xStar
  set S : Set ℝ := Set.image f C
  set T : Set ℝ := Set.image f (closure C)
  have hSne : S.Nonempty := by
    simpa [S] using hCne.image f
  have hSsub : S ⊆ T := by
    intro r hr
    rcases hr with ⟨x, hxC, rfl⟩
    exact ⟨x, subset_closure hxC, rfl⟩
  by_cases hSbdd : BddAbove S
  · set β : ℝ := sSup S
    have hsubset : C ⊆ {x : Fin n → Real | f x ≤ β} := by
      intro x hxC
      have hxS : f x ∈ S := ⟨x, hxC, rfl⟩
      exact le_csSup hSbdd hxS
    have hcont : Continuous f := by
      simpa [f] using (Continuous.dotProduct (continuous_id) continuous_const)
    have hclosed : IsClosed ({x : Fin n → Real | f x ≤ β} : Set (Fin n → Real)) := by
      simpa [Set.preimage, Set.Iic] using (isClosed_Iic.preimage hcont)
    have hclsubset : closure C ⊆ {x : Fin n → Real | f x ≤ β} := by
      exact (IsClosed.closure_subset_iff hclosed).2 hsubset
    have hpoint : ∀ r ∈ T, r ≤ β := by
      intro r hr
      rcases hr with ⟨x, hxcl, rfl⟩
      exact hclsubset hxcl
    have hTne : T.Nonempty := by
      simpa [T] using (hCne.closure.image f)
    have hTbdd : BddAbove T := ⟨β, hpoint⟩
    have hle₁ : sSup S ≤ sSup T :=
      csSup_le_csSup hTbdd hSne hSsub
    have hle₂ : sSup T ≤ sSup S := by
      have : sSup T ≤ β := csSup_le hTne hpoint
      simpa [β] using this
    have hsSup : sSup S = sSup T := le_antisymm hle₁ hle₂
    simpa [deltaStar_eq_sSup_image_dotProduct_right, S, T, f] using hsSup
  · have hTbdd : ¬ BddAbove T := by
      intro hTbdd
      exact hSbdd (hTbdd.mono hSsub)
    simp [deltaStar_eq_sSup_image_dotProduct_right, S, T, f,
      Real.sSup_of_not_bddAbove hSbdd, Real.sSup_of_not_bddAbove hTbdd]

/-- For a convex set, the closure of its intrinsic (relative) interior equals its closure. -/
lemma closure_intrinsicInterior_eq_closure_of_convex {n : Nat} (C : Set (Fin n → Real))
    (hC : Convex ℝ C) :
    closure (intrinsicInterior ℝ C) = closure C := by
  refine le_antisymm ?_ ?_
  · exact closure_mono intrinsicInterior_subset
  · by_cases hCne : C.Nonempty
    · exact closure_subset_closure_intrinsicInterior_of_convex_nonempty n C hC hCne
    · have hCempty : C = ∅ := (Set.not_nonempty_iff_eq_empty).1 hCne
      simp [hCempty]

/-- Text 13.0.5: For any convex set `C`, one has

`δ^*(x^* | C) = δ^*(x^* | cl C) = δ^*(x^* | ri C)` for all `x^*`, where `cl` denotes closure and
`ri` denotes relative (intrinsic) interior. -/
theorem deltaStar_eq_closure_eq_intrinsicInterior {n : Nat} (C : Set (Fin n → Real))
    (hC : Convex ℝ C) :
    ∀ xStar : Fin n → Real,
      deltaStar C xStar = deltaStar (closure C) xStar ∧
        deltaStar (closure C) xStar = deltaStar (intrinsicInterior ℝ C) xStar := by
  intro xStar
  constructor
  · exact deltaStar_eq_deltaStar_closure (C := C) (xStar := xStar)
  · have hcl : closure (intrinsicInterior ℝ C) = closure C :=
      closure_intrinsicInterior_eq_closure_of_convex (C := C) hC
    calc
      deltaStar (closure C) xStar = deltaStar (closure (intrinsicInterior ℝ C)) xStar := by
        simp [hcl.symm]
      _ = deltaStar (intrinsicInterior ℝ C) xStar := by
        simpa using
          (deltaStar_eq_deltaStar_closure (C := intrinsicInterior ℝ C) (xStar := xStar)).symm

/-- If the dot-product image is bounded above, any member of `C` satisfies the supporting inequality. -/
lemma section13_dotProduct_le_deltaStar_of_mem {n : Nat} {C : Set (Fin n → Real)}
    {xStar y : Fin n → Real}
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) (hy : y ∈ C) :
    dotProduct y xStar ≤ deltaStar C xStar := by
  classical
  have hyimg :
      dotProduct y xStar ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C :=
    ⟨y, hy, rfl⟩
  simpa [deltaStar_eq_sSup_image_dotProduct_right] using (le_csSup hbdd hyimg)

/-- A bound on the dot-product image at `-xStar` gives a lower bound on the dot-product image at `xStar`. -/
lemma section13_bddBelow_image_dotProduct_of_bddAbove_image_dotProduct_neg {n : Nat}
    (C : Set (Fin n → Real)) (xStar : Fin n → Real)
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x (-xStar)) C)) :
    BddBelow (Set.image (fun x : Fin n → Real => dotProduct x xStar) C) := by
  rcases hbdd with ⟨β, hβ⟩
  refine ⟨-β, ?_⟩
  rintro r ⟨y, hyC, rfl⟩
  have h : dotProduct y (-xStar) ≤ β :=
    hβ ⟨y, hyC, rfl⟩
  have h' : -(dotProduct y xStar) ≤ β := by
    simpa [dotProduct_neg] using h
  simpa using (neg_le_neg h')

/-- For a point `x ∈ C`, being a maximizer of `dotProduct · xStar` is equivalent to equality with `deltaStar`. -/
lemma section13_isMaxOn_dotProduct_iff_eq_deltaStar_of_mem {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (xStar x : Fin n → Real) (hxC : x ∈ C)
    (hbdd : BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    IsMaxOn (fun y : Fin n → Real => dotProduct y xStar) C x ↔
      dotProduct x xStar = deltaStar C xStar := by
  classical
  constructor
  · intro hxmax
    have hle : ∀ y ∈ C, dotProduct y xStar ≤ dotProduct x xStar := hxmax
    have hsSup_le :
        sSup (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) ≤ dotProduct x xStar := by
      refine csSup_le (hCne.image (fun y : Fin n → Real => dotProduct y xStar)) ?_
      intro r hr
      rcases hr with ⟨y, hyC, rfl⟩
      exact hle y hyC
    have hximg :
        dotProduct x xStar ∈ Set.image (fun y : Fin n → Real => dotProduct y xStar) C :=
      ⟨x, hxC, rfl⟩
    have hxle_sup :
        dotProduct x xStar ≤ sSup (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) :=
      le_csSup hbdd hximg
    have hsSup_eq :
        sSup (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) = dotProduct x xStar :=
      le_antisymm hsSup_le hxle_sup
    simp [deltaStar_eq_sSup_image_dotProduct_right, hsSup_eq]
  · intro hxEq y hyC
    have hyLe : dotProduct y xStar ≤ deltaStar C xStar :=
      section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := y) hbdd hyC
    simpa [hxEq] using hyLe

/-- If `-deltaStar (-xStar) ≠ deltaStar xStar`, then a maximizer of `dotProduct · xStar` is not a minimizer. -/
lemma section13_exists_lt_dotProduct_of_ne_neg_deltaStar {n : Nat} {C : Set (Fin n → Real)}
    (hC : Convex ℝ C) (x xStar : Fin n → Real) (hxC : x ∈ C)
    (hxEq : dotProduct x xStar = deltaStar C xStar)
    (hne : -(deltaStar C (-xStar)) ≠ deltaStar C xStar)
    (hbdd : BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    ∃ y, y ∈ C ∧ dotProduct y xStar < dotProduct x xStar := by
  classical
  by_contra h
  have hnot : ∀ y, y ∈ C → ¬ dotProduct y xStar < dotProduct x xStar := by
    intro y hyC hylt
    exact h ⟨y, hyC, hylt⟩
  have hle : ∀ y, y ∈ C → dotProduct y xStar ≤ dotProduct x xStar := by
    intro y hyC
    have hyLe : dotProduct y xStar ≤ deltaStar C xStar :=
      section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := y) hbdd hyC
    simpa [hxEq] using hyLe
  have heq : ∀ y, y ∈ C → dotProduct y xStar = dotProduct x xStar := by
    intro y hyC
    exact (le_antisymm (hle y hyC) (le_of_not_gt (hnot y hyC)))
  let S : Set ℝ := Set.image (fun y : Fin n → Real => dotProduct y xStar) C
  have hxS : dotProduct x xStar ∈ S := ⟨x, hxC, rfl⟩
  have hlb : ∀ r ∈ S, dotProduct x xStar ≤ r := by
    rintro r ⟨y, hyC, rfl⟩
    simp [heq y hyC]
  have hbddBelow : BddBelow S := ⟨dotProduct x xStar, hlb⟩
  have hsInf : sInf S = dotProduct x xStar := by
    refine le_antisymm (csInf_le hbddBelow hxS) ?_
    exact le_csInf ⟨dotProduct x xStar, hxS⟩ hlb
  have : -(deltaStar C (-xStar)) = dotProduct x xStar := by
    simpa [S] using (sInf_dotProduct_eq_neg_deltaStar (C := C) (xStar := xStar) hC).symm.trans hsInf
  exact hne (this.trans hxEq)

/-- Theorem 13.1: Let `C` be a convex set. Then `x ∈ cl C` if and only if
`⟪x, x^*⟫ ≤ δ^*(x^* | C)` for every `x^*`. Moreover, `x ∈ ri C` if and only if the same condition
holds, but with strict inequality for each `x^*` such that `-δ^*(-x^* | C) ≠ δ^*(x^* | C)`. One has
`x ∈ int C` if and only if `⟪x, x^*⟫ < δ^*(x^* | C)` for every `x^*`. -/
theorem mem_closure_iff_forall_dotProduct_le_deltaStar {n : Nat} (C : Set (Fin n → Real))
    (x : Fin n → Real) (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    x ∈ closure C ↔ ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C xStar := by
  classical
  constructor
  · intro hxcl xStar
    rcases hCbd xStar with ⟨β, hβ⟩
    have hsubset : C ⊆ {y : Fin n → Real | dotProduct y xStar ≤ β} :=
      (forall_image_dotProduct_le_iff_subset_halfspace (C := C) (xStar := xStar) (β := β)).1 hβ
    have hclosed : IsClosed ({y : Fin n → Real | dotProduct y xStar ≤ β} : Set (Fin n → Real)) := by
      simpa using (isClosed_setOf_dotProduct_le (n := n) (b := xStar) (β := β))
    have hclsubset : closure C ⊆ {y : Fin n → Real | dotProduct y xStar ≤ β} :=
      (IsClosed.closure_subset_iff hclosed).2 hsubset
    have hβ' : ∀ r ∈ Set.image (fun y : Fin n → Real => dotProduct y xStar) (closure C), r ≤ β := by
      rintro r ⟨y, hycl, rfl⟩
      exact hclsubset hycl
    have hbddcl :
        BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) (closure C)) :=
      ⟨β, hβ'⟩
    have hximg :
        dotProduct x xStar ∈
          Set.image (fun y : Fin n → Real => dotProduct y xStar) (closure C) :=
      ⟨x, hxcl, rfl⟩
    have hxle :
        dotProduct x xStar ≤
          sSup (Set.image (fun y : Fin n → Real => dotProduct y xStar) (closure C)) :=
      le_csSup hbddcl hximg
    have hxle' : dotProduct x xStar ≤ deltaStar (closure C) xStar := by
      simpa [deltaStar_eq_sSup_image_dotProduct_right] using hxle
    have hδ : deltaStar (closure C) xStar = deltaStar C xStar :=
      (deltaStar_eq_deltaStar_closure (C := C) (xStar := xStar)).symm
    simpa [hδ] using hxle'
  · intro hxall
    by_contra hxcl
    have hdisj :
        Disjoint (closure ({x} : Set (Fin n → Real))) (closure C) := by
      have : Disjoint ({x} : Set (Fin n → Real)) (closure C) :=
        Set.disjoint_singleton_left.2 hxcl
      simpa [closure_singleton] using this
    rcases
        exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n := n)
          ({x} : Set (Fin n → Real)) C (Set.singleton_nonempty x) hCne
          (convex_singleton (𝕜 := Real) (c := x)) hC hdisj
          (Or.inl Bornology.isBounded_singleton) with
      ⟨H, hH⟩
    rcases hH with ⟨_h₁ne, _h₂ne, b, β, _hb0, _hHdef, ε, _hεpos, hcases⟩
    let B : Set (Fin n → Real) := {z | ‖z‖ ≤ (1 : Real)}
    have h0B : (0 : Fin n → Real) ∈ ε • B := by
      refine ⟨0, ?_, by simp⟩
      simp [B]
    have hx_thick : x ∈ ({x} : Set (Fin n → Real)) + (ε • B) := by
      refine ⟨x, by simp, 0, h0B, by simp⟩
    cases hcases with
    | inl h =>
        have hx_lt : dotProduct x b < β := by
          simpa [B] using h.1 hx_thick
        have hC_gt : ∀ y ∈ C, β < dotProduct y b := by
          intro y hyC
          have hy_thick : y ∈ C + (ε • B) := by
            refine ⟨y, hyC, 0, h0B, by simp⟩
          simpa [B] using h.2 hy_thick
        have hsup_le : deltaStar C (-b) ≤ -β := by
          have hpoint :
              ∀ r ∈ Set.image (fun y : Fin n → Real => dotProduct y (-b)) C, r ≤ -β := by
            rintro r ⟨y, hyC, rfl⟩
            have : dotProduct y (-b) < -β := by
              simpa [dotProduct_neg] using (neg_lt_neg (hC_gt y hyC))
            exact le_of_lt this
          have hne :
              (Set.image (fun y : Fin n → Real => dotProduct y (-b)) C).Nonempty := by
            simpa using hCne.image (fun y : Fin n → Real => dotProduct y (-b))
          have hsSup : sSup (Set.image (fun y : Fin n → Real => dotProduct y (-b)) C) ≤ -β :=
            csSup_le hne hpoint
          simpa [deltaStar_eq_sSup_image_dotProduct_right] using hsSup
        have hx_gt : -β < dotProduct x (-b) := by
          simpa [dotProduct_neg] using (neg_lt_neg hx_lt)
        have hxle : dotProduct x (-b) ≤ deltaStar C (-b) := hxall (-b)
        have : dotProduct x (-b) ≤ -β := le_trans hxle hsup_le
        exact (not_lt_of_ge this) hx_gt
    | inr h =>
        have hx_gt : β < dotProduct x b := by
          simpa [B] using h.2 hx_thick
        have hC_lt : ∀ y ∈ C, dotProduct y b < β := by
          intro y hyC
          have hy_thick : y ∈ C + (ε • B) := by
            refine ⟨y, hyC, 0, h0B, by simp⟩
          simpa [B] using h.1 hy_thick
        have hsup_le : deltaStar C b ≤ β := by
          have hpoint :
              ∀ r ∈ Set.image (fun y : Fin n → Real => dotProduct y b) C, r ≤ β := by
            rintro r ⟨y, hyC, rfl⟩
            exact le_of_lt (hC_lt y hyC)
          have hne :
              (Set.image (fun y : Fin n → Real => dotProduct y b) C).Nonempty := by
            simpa using hCne.image (fun y : Fin n → Real => dotProduct y b)
          have hsSup : sSup (Set.image (fun y : Fin n → Real => dotProduct y b) C) ≤ β :=
            csSup_le hne hpoint
          simpa [deltaStar_eq_sSup_image_dotProduct_right] using hsSup
        have hxle : dotProduct x b ≤ deltaStar C b := hxall b
        have : dotProduct x b ≤ β := le_trans hxle hsup_le
        exact (not_lt_of_ge this) hx_gt

/-- Theorem 13.1 (relative interior characterization): for convex `C`, membership in the relative
(intrinsic) interior is equivalent to the supporting-inequality condition,
with strict inequality for each `x^*` such that `-δ^*(-x^* | C) ≠ δ^*(x^* | C)`. -/
theorem mem_intrinsicInterior_iff_forall_dotProduct_le_deltaStar_and_forall_of_ne {n : Nat}
    (C : Set (Fin n → Real)) (x : Fin n → Real) (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧
        (∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C xStar) ∧
          ∀ xStar : Fin n → Real,
            (-(deltaStar C (-xStar)) ≠ deltaStar C xStar) →
              dotProduct x xStar < deltaStar C xStar := by
  classical
  constructor
  · intro hxri
    have hxC : x ∈ C := intrinsicInterior_subset (𝕜 := ℝ) (s := C) hxri
    refine ⟨hxC, ?_, ?_⟩
    · intro xStar
      exact section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := x) (hCbd xStar)
        hxC
    · intro xStar hne
      have hxle : dotProduct x xStar ≤ deltaStar C xStar :=
        section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := x) (hCbd xStar) hxC
      by_contra hnot
      have hxEq : dotProduct x xStar = deltaStar C xStar := by
        by_contra hne'
        exact hnot (lt_of_le_of_ne hxle hne')
      rcases
          section13_exists_lt_dotProduct_of_ne_neg_deltaStar (C := C) hC x xStar hxC hxEq hne
            (hCbd xStar) with
        ⟨y0, hy0C, hy0lt⟩
      have hxmax : IsMaxOn (fun y : Fin n → Real => dotProduct y xStar) C x := by
        intro y hyC
        have hyLe : dotProduct y xStar ≤ deltaStar C xStar :=
          section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := y) (hCbd xStar) hyC
        simpa [hxEq] using hyLe
      have hxfr' : x ∈ C ∧ x ∈ intrinsicFrontier ℝ C := by
        refine
          (mem_intrinsicFrontier_iff_exists_isMaxOn_linearFunctional (n := n) (C := C) hC x).2 ?_
        refine ⟨dotProduct_strongDual (n := n) xStar, ?_, ?_, hxC⟩
        · refine ⟨y0, hy0C, ?_⟩
          simpa [dotProduct_strongDual_apply] using hy0lt
        · intro y hyC
          simpa [dotProduct_strongDual_apply] using (hxmax (a := y) hyC)
      have hxnotfr : x ∉ intrinsicFrontier ℝ C := by
        intro hxfr
        rcases (mem_intrinsicInterior (𝕜 := ℝ) (s := C) (x := x)).1 hxri with ⟨y, hyint, hyEq⟩
        rcases (mem_intrinsicFrontier (𝕜 := ℝ) (s := C) (x := x)).1 hxfr with ⟨z, hzfr, hzEq⟩
        have hyz : y = z := by
          apply Subtype.ext
          exact hyEq.trans hzEq.symm
        exact hzfr.2 (by simpa [hyz] using hyint)
      exact hxnotfr hxfr'.2
  · rintro ⟨hxC, hle, hstrict⟩
    have hxnotfr : x ∉ intrinsicFrontier ℝ C := by
      intro hxfr
      have hxCF : x ∈ C ∧ x ∈ intrinsicFrontier ℝ C := ⟨hxC, hxfr⟩
      rcases
          (mem_intrinsicFrontier_iff_exists_isMaxOn_linearFunctional (n := n) (C := C) hC x).1 hxCF with
        ⟨l, ⟨y0, hy0C, hy0lt⟩, hxmax, _hxC⟩
      let xStar : Fin n → Real :=
        fun i => l (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
      have hl_apply : ∀ y : Fin n → Real, l y = dotProduct y xStar := by
        intro y
        simpa [xStar] using (strongDual_apply_eq_dotProduct (g := l) y)
      have hxmax' : IsMaxOn (fun y : Fin n → Real => dotProduct y xStar) C x := by
        intro y hyC
        have : l y ≤ l x := hxmax (a := y) hyC
        simpa [hl_apply y, hl_apply x] using this
      have hxEq :
          dotProduct x xStar = deltaStar C xStar :=
        (section13_isMaxOn_dotProduct_iff_eq_deltaStar_of_mem (C := C) hCne xStar x hxC (hCbd xStar)).1
          hxmax'
      have hy0lt' : dotProduct y0 xStar < dotProduct x xStar := by
        simpa [hl_apply y0, hl_apply x] using hy0lt
      have hy0ltδ : dotProduct y0 xStar < deltaStar C xStar := by
        exact lt_of_lt_of_le hy0lt' (hle xStar)
      have hbddBelow :
          BddBelow (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) :=
        section13_bddBelow_image_dotProduct_of_bddAbove_image_dotProduct_neg (C := C) xStar
          (hCbd (-xStar))
      have hsInf_le :
          sInf (Set.image (fun y : Fin n → Real => dotProduct y xStar) C) ≤ dotProduct y0 xStar :=
        csInf_le hbddBelow ⟨y0, hy0C, rfl⟩
      have hneg_le : -(deltaStar C (-xStar)) ≤ dotProduct y0 xStar := by
        simpa [sInf_dotProduct_eq_neg_deltaStar (C := C) (xStar := xStar) hC] using hsInf_le
      have hne : -(deltaStar C (-xStar)) ≠ deltaStar C xStar :=
        ne_of_lt (lt_of_le_of_lt hneg_le hy0ltδ)
      have hlt : dotProduct x xStar < deltaStar C xStar := hstrict xStar hne
      rw [hxEq] at hlt
      exact (lt_irrefl (deltaStar C xStar)) hlt
    have hxcl : x ∈ intrinsicClosure ℝ C := subset_intrinsicClosure (𝕜 := ℝ) (s := C) hxC
    have hxmem : x ∈ intrinsicClosure ℝ C \ intrinsicFrontier ℝ C := ⟨hxcl, hxnotfr⟩
    -- Rewrite the goal using `intrinsicClosure \ intrinsicFrontier = intrinsicInterior`.
    rw [← intrinsicClosure_diff_intrinsicFrontier (𝕜 := ℝ) (s := C)]
    exact hxmem

/-- Theorem 13.1 (interior characterization): for convex `C`, membership in the (topological)
interior is equivalent to strict supporting inequalities `⟪x, x^*⟫ < δ^*(x^* | C)` for all `x^*`. -/
theorem mem_interior_iff_forall_dotProduct_lt_deltaStar {n : Nat} (C : Set (Fin n → Real))
    (x : Fin n → Real) (hC : Convex ℝ C)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    x ∈ interior C ↔
      x ∈ C ∧ ∀ xStar : Fin n → Real, xStar ≠ 0 → dotProduct x xStar < deltaStar C xStar := by
  classical
  constructor
  · intro hxint
    have hxC : x ∈ C := interior_subset hxint
    refine ⟨hxC, ?_⟩
    intro xStar hxStar0
    have hxnhds : C ∈ nhds x := (mem_interior_iff_mem_nhds).1 hxint
    rcases Metric.mem_nhds_iff.1 hxnhds with ⟨ε, hεpos, hball⟩
    have hnormpos : 0 < ‖xStar‖ := norm_pos_iff.2 hxStar0
    let t : Real := ε / (2 * ‖xStar‖)
    have htpos : 0 < t := by
      have hden : 0 < 2 * ‖xStar‖ := mul_pos (by norm_num) hnormpos
      exact div_pos hεpos hden
    have htlt : ‖t • xStar‖ < ε := by
      have : ‖t • xStar‖ = t * ‖xStar‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      -- `t * ‖xStar‖ = ε / 2`.
      have htcalc : t * ‖xStar‖ = ε / 2 := by
        have hxnorm : (‖xStar‖ : ℝ) ≠ 0 := ne_of_gt hnormpos
        have : (ε / (2 * ‖xStar‖)) * ‖xStar‖ = ε / 2 := by
          field_simp [hxnorm]
        simpa [t] using this
      -- `ε / 2 < ε` since `ε > 0`.
      have hhalf : ε / 2 < ε := by nlinarith
      simpa [this, htcalc] using hhalf
    have hyball : x + t • xStar ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htlt
    have hyC : x + t • xStar ∈ C := hball hyball
    have hxStarpos : 0 < dotProduct xStar xStar := by
      have h := (Matrix.dotProduct_self_star_pos_iff (v := xStar)).2 hxStar0
      simpa using h
    have hinc : dotProduct x xStar < dotProduct (x + t • xStar) xStar := by
      have : dotProduct (x + t • xStar) xStar = dotProduct x xStar + t * dotProduct xStar xStar := by
        -- Use commutativity to expand along the right argument.
        calc
          dotProduct (x + t • xStar) xStar
              = dotProduct xStar (x + t • xStar) := by simp [dotProduct_comm]
          _ = dotProduct xStar x + dotProduct xStar (t • xStar) := by
                simp [dotProduct_add]
          _ = dotProduct x xStar + t * dotProduct xStar xStar := by
                simp [dotProduct_comm, dotProduct_smul, smul_eq_mul]
      have hpos : 0 < t * dotProduct xStar xStar := mul_pos htpos hxStarpos
      simpa [this] using (lt_add_of_pos_right (dotProduct x xStar) hpos)
    have hyle : dotProduct (x + t • xStar) xStar ≤ deltaStar C xStar :=
      section13_dotProduct_le_deltaStar_of_mem (C := C) (xStar := xStar) (y := x + t • xStar)
        (hCbd xStar) hyC
    exact lt_of_lt_of_le hinc hyle
  · rintro ⟨hxC, hstrict⟩
    by_contra hxint
    have hxfr : x ∈ frontier C := by
      refine ⟨subset_closure hxC, ?_⟩
      exact hxint
    have hb := exists_nonzero_normal_of_mem_frontier_of_convex (n := n) (C := C) hC x hxC hxfr
    rcases hb with ⟨b, hb0, hb_le⟩
    have hxmax : IsMaxOn (fun y : Fin n → Real => dotProduct y b) C x := by
      intro y hyC
      exact hb_le y hyC
    have hCne : C.Nonempty := ⟨x, hxC⟩
    have hxEq :
        dotProduct x b = deltaStar C b :=
      (section13_isMaxOn_dotProduct_iff_eq_deltaStar_of_mem (C := C) hCne b x hxC (hCbd b)).1 hxmax
    have hlt : dotProduct x b < deltaStar C b := hstrict b hb0
    rw [hxEq] at hlt
    exact (lt_irrefl (deltaStar C b)) hlt

/-- If the dot-product image of `C` is bounded above, then so is the dot-product image of `closure C`. -/
lemma section13_bddAbove_image_dotProduct_closure {n : Nat} (C : Set (Fin n → Real))
    (xStar : Fin n → Real)
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) (closure C)) := by
  classical
  rcases hbdd with ⟨β, hβ⟩
  have hsubset : C ⊆ {y : Fin n → Real | dotProduct y xStar ≤ β} :=
    (forall_image_dotProduct_le_iff_subset_halfspace (C := C) (xStar := xStar) (β := β)).1 hβ
  have hclosed : IsClosed ({y : Fin n → Real | dotProduct y xStar ≤ β} : Set (Fin n → Real)) := by
    simpa using (isClosed_setOf_dotProduct_le (n := n) (b := xStar) (β := β))
  have hclsubset : closure C ⊆ {y : Fin n → Real | dotProduct y xStar ≤ β} :=
    (IsClosed.closure_subset_iff hclosed).2 hsubset
  refine ⟨β, ?_⟩
  rintro r ⟨y, hycl, rfl⟩
  exact hclsubset hycl

/-- Monotonicity of `deltaStar` under set inclusion (assuming nonempty domain and bounded range). -/
lemma section13_deltaStar_le_of_subset {n : Nat} {C₁ C₂ : Set (Fin n → Real)} (xStar : Fin n → Real)
    (hsub : C₁ ⊆ C₂) (hC₁ne : C₁.Nonempty)
    (hC₂bd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂)) :
    deltaStar C₁ xStar ≤ deltaStar C₂ xStar := by
  classical
  set S : Set ℝ := Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁
  set T : Set ℝ := Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂
  have hSne : S.Nonempty := by
    simpa [S] using hC₁ne.image (fun x : Fin n → Real => dotProduct x xStar)
  have hSsub : S ⊆ T := by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact ⟨x, hsub hx, rfl⟩
  have hsup : sSup S ≤ sSup T := csSup_le_csSup (by simpa [T] using hC₂bd) hSne hSsub
  simpa [deltaStar_eq_sSup_image_dotProduct_right, S, T] using hsup

/-- Corollary 13.1.1. For convex sets `C₁` and `C₂` in `ℝ^n`, one has `cl C₁ ⊆ cl C₂` if and
only if `δ^*(· | C₁) ≤ δ^*(· | C₂)`. -/
theorem closure_subset_iff_deltaStar_le {n : Nat} (C₁ C₂ : Set (Fin n → Real))
    (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁bd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C₁))
    (hC₂bd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C₂)) :
    closure C₁ ⊆ closure C₂ ↔ deltaStar C₁ ≤ deltaStar C₂ := by
  constructor
  · intro hsub xStar
    have hsub' : C₁ ⊆ closure C₂ := by
      intro x hx
      exact hsub (subset_closure hx)
    have hbd' :
        BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) (closure C₂)) :=
      section13_bddAbove_image_dotProduct_closure (C := C₂) (xStar := xStar) (hC₂bd xStar)
    have hle : deltaStar C₁ xStar ≤ deltaStar (closure C₂) xStar :=
      section13_deltaStar_le_of_subset (C₁ := C₁) (C₂ := closure C₂) xStar hsub' hC₁ne hbd'
    simpa [deltaStar_eq_deltaStar_closure (C := C₂) (xStar := xStar)] using hle
  · intro hle x hxcl
    have hxle : ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₁ xStar :=
      (mem_closure_iff_forall_dotProduct_le_deltaStar (C := C₁) (x := x) hC₁ hC₁ne hC₁bd).1 hxcl
    have hxle' : ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₂ xStar := by
      intro xStar
      exact le_trans (hxle xStar) (hle xStar)
    exact
      (mem_closure_iff_forall_dotProduct_le_deltaStar (C := C₂) (x := x) hC₂ hC₂ne hC₂bd).2 hxle'

/-- For a convex set `C` with well-defined support function, the set of points satisfying all
supporting inequalities is the closure of `C`. -/
lemma section13_setOf_forall_dotProduct_le_deltaStar_eq_closure {n : Nat} (C : Set (Fin n → Real))
    (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C xStar} =
      closure C := by
  ext x
  simpa using
    (mem_closure_iff_forall_dotProduct_le_deltaStar (C := C) (x := x) hC hCne hCbd).symm

/-- Text 13.1.2: Let `C ⊆ ℝ^n` be a closed convex set. Define

`D := { x | ∀ x^*, ⟪x, x^*⟫ ≤ δ^*(x^* | C) }`.

Then `D = C`. In particular, `C` is completely determined by its support function. -/
theorem setOf_forall_dotProduct_le_deltaStar_eq_of_isClosed {n : Nat} (C : Set (Fin n → Real))
    (hC : Convex ℝ C) (hCclosed : IsClosed C) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C)) :
    {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C xStar} = C := by
  calc
    {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C xStar} =
        closure C := by
          simpa using
            (section13_setOf_forall_dotProduct_le_deltaStar_eq_closure (C := C) hC hCne hCbd)
    _ = C := hCclosed.closure_eq

/-- Text 13.1.2 (support function determines a closed convex set): if two closed convex sets have
the same (finite) support function, then they are equal. -/
theorem eq_of_isClosed_of_convex_of_deltaStar_eq {n : Nat} {C₁ C₂ : Set (Fin n → Real)}
    (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂) (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂)
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁bd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C₁))
    (hC₂bd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun y : Fin n → Real => dotProduct y xStar) C₂))
    (hδ : deltaStar C₁ = deltaStar C₂) : C₁ = C₂ := by
  have hrepr₁ :
      {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₁ xStar} =
        C₁ :=
    setOf_forall_dotProduct_le_deltaStar_eq_of_isClosed (C := C₁) hC₁ hC₁closed hC₁ne hC₁bd
  have hrepr₂ :
      {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₂ xStar} =
        C₂ :=
    setOf_forall_dotProduct_le_deltaStar_eq_of_isClosed (C := C₂) hC₂ hC₂closed hC₂ne hC₂bd
  calc
    C₁ = {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₁ xStar} := by
      simpa using hrepr₁.symm
    _ =
        {x : Fin n → Real | ∀ xStar : Fin n → Real, dotProduct x xStar ≤ deltaStar C₂ xStar} := by
      ext x
      simp [hδ]
    _ = C₂ := by simpa using hrepr₂

/-- The dot-product image of a Minkowski sum is the pointwise sum of the dot-product images. -/
lemma section13_image_dotProduct_add_eq {n : Nat} (C₁ C₂ : Set (Fin n → Real))
    (xStar : Fin n → Real) :
    Set.image (fun x : Fin n → Real => dotProduct x xStar) (C₁ + C₂) =
      Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁ +
        Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂ := by
  classical
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (Set.mem_add).1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have hx₁img :
        dotProduct x₁ xStar ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁ :=
      ⟨x₁, hx₁, rfl⟩
    have hx₂img :
        dotProduct x₂ xStar ∈ Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂ :=
      ⟨x₂, hx₂, rfl⟩
    have hdot :
        dotProduct (x₁ + x₂) xStar = dotProduct x₁ xStar + dotProduct x₂ xStar := by
      simp [add_dotProduct]
    have : dotProduct x₁ xStar + dotProduct x₂ xStar ∈
        Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁ +
          Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂ :=
      Set.add_mem_add hx₁img hx₂img
    simpa [hdot] using this
  · intro hr
    rcases (Set.mem_add).1 hr with ⟨r₁, hr₁, r₂, hr₂, rfl⟩
    rcases hr₁ with ⟨x₁, hx₁, rfl⟩
    rcases hr₂ with ⟨x₂, hx₂, rfl⟩
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · exact Set.add_mem_add hx₁ hx₂
    · simp [add_dotProduct]

/-- If both dot-product image-sets are bounded above, then the supremum over their sum splits. -/
lemma section13_sSup_image_dotProduct_add {n : Nat} (C₁ C₂ : Set (Fin n → Real))
    (xStar : Fin n → Real)
    (hC₁ne : Set.Nonempty C₁) (hC₂ne : Set.Nonempty C₂)
    (hbdd₁ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁))
    (hbdd₂ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂)) :
    sSup
        (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁ +
          Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂) =
      sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁) +
        sSup (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂) := by
  classical
  simpa using
    (csSup_add
      (hs₀ := hC₁ne.image (fun x : Fin n → Real => dotProduct x xStar))
      (hs₁ := hbdd₁)
      (ht₀ := hC₂ne.image (fun x : Fin n → Real => dotProduct x xStar))
      (ht₁ := hbdd₂))

/-- Boundedness in direction `xStar` makes the Real-valued support function additive under sums. -/
lemma section13_deltaStar_add_of_bddAbove {n : Nat} (C₁ C₂ : Set (Fin n → Real))
    (xStar : Fin n → Real)
    (hC₁ne : Set.Nonempty C₁) (hC₂ne : Set.Nonempty C₂)
    (hbdd₁ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁))
    (hbdd₂ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂)) :
    deltaStar (C₁ + C₂) xStar = deltaStar C₁ xStar + deltaStar C₂ xStar := by
  classical
  simp [deltaStar_eq_sSup_image_dotProduct_right, section13_image_dotProduct_add_eq,
    section13_sSup_image_dotProduct_add (C₁ := C₁) (C₂ := C₂) (xStar := xStar) hC₁ne hC₂ne hbdd₁
      hbdd₂]

/-- Text 13.1.3: The support function of the sum of two non-empty convex sets `C₁` and `C₂` is
given by

`δ^*(x^* | C₁ + C₂) = δ^*(x^* | C₁) + δ^*(x^* | C₂)`. -/
theorem deltaStar_add {n : Nat} (C₁ C₂ : Set (Fin n → Real)) (xStar : Fin n → Real)
    (_hC₁ : Convex ℝ C₁) (_hC₂ : Convex ℝ C₂) (hC₁ne : Set.Nonempty C₁) (hC₂ne : Set.Nonempty C₂)
    (hbdd₁ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₁))
    (hbdd₂ : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C₂)) :
    deltaStar (C₁ + C₂) xStar = deltaStar C₁ xStar + deltaStar C₂ xStar := by
  simpa using
    (section13_deltaStar_add_of_bddAbove (C₁ := C₁) (C₂ := C₂) (xStar := xStar) hC₁ne hC₂ne hbdd₁
      hbdd₂)

/-- For indicator functions, points outside the set contribute `⊥` to the Fenchel conjugate. -/
lemma section13_fenchelConjugate_indicatorFunction_eq_sSup_image_dotProduct {n : Nat}
    (C : Set (Fin n → Real)) (xStar : Fin n → Real) :
    fenchelConjugate n (indicatorFunction C) xStar =
      sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) := by
  classical
  unfold fenchelConjugate
  set f : (Fin n → Real) → EReal :=
    fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - indicatorFunction C x
  set g : (Fin n → Real) → EReal := fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)
  apply le_antisymm
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ C
    · have hxmem : g x ∈ Set.image g C := ⟨x, hx, rfl⟩
      have : g x ≤ sSup (Set.image g C) := le_sSup hxmem
      simpa [f, g, indicatorFunction, hx] using this
    · simp [f, g, indicatorFunction, hx]
  · refine sSup_le ?_
    rintro y ⟨x, hx, rfl⟩
    have hxmem : g x ∈ Set.range f := by
      refine ⟨x, ?_⟩
      simp [f, g, indicatorFunction, hx]
    exact le_sSup hxmem

/-- Coercion commutes with `sSup` for a nonempty, bounded-above set of reals. -/
lemma section13_sSup_image_coe_real_eq_coe_sSup (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    sSup ((fun r : ℝ => (r : EReal)) '' S) = ((sSup S : ℝ) : EReal) := by
  classical
  refine EReal.eq_of_forall_le_coe_iff ?_
  intro μ
  have hSup_le :
      sSup ((fun r : ℝ => (r : EReal)) '' S) ≤ (μ : EReal) ↔ ∀ r ∈ S, r ≤ μ := by
    constructor
    · intro h r hr
      have hr' : ((r : ℝ) : EReal) ∈ ((fun r : ℝ => (r : EReal)) '' S) := ⟨r, hr, rfl⟩
      have : ((r : ℝ) : EReal) ≤ (μ : EReal) := le_trans (le_sSup hr') h
      exact (EReal.coe_le_coe_iff.1 this)
    · intro h
      refine sSup_le ?_
      rintro y ⟨r, hr, rfl⟩
      exact EReal.coe_le_coe_iff.2 (h r hr)
  have hcsSup_le : (sSup S ≤ μ) ↔ (∀ r ∈ S, r ≤ μ) :=
    (csSup_le_iff (s := S) (a := μ) hbdd hne)
  calc
    sSup ((fun r : ℝ => (r : EReal)) '' S) ≤ (μ : EReal) ↔ ∀ r ∈ S, r ≤ μ := hSup_le
    _ ↔ sSup S ≤ μ := by simpa using hcsSup_le.symm
    _ ↔ ((sSup S : ℝ) : EReal) ≤ (μ : EReal) := by
      simp

/-- Text 13.1.4: Let `C ⊆ ℝ^n` be a convex set, and let `δ(· | C)` be its indicator function,
`δ(x | C) = 0` for `x ∈ C` and `δ(x | C) = +∞` for `x ∉ C`.

Then the convex conjugate of `δ(· | C)` is the support function of `C`. More precisely, for every
`xStar`,

`δ*(xStar | C) = sup_x (⟪x, xStar⟫ - δ(x | C)) = sup_{x ∈ C} ⟪x, xStar⟫`. -/
theorem fenchelConjugate_indicatorFunction_eq_deltaStar {n : Nat} (C : Set (Fin n → Real))
    (xStar : Fin n → Real) (hCne : C.Nonempty)
    (hbdd : BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    fenchelConjugate n (indicatorFunction C) xStar = ((deltaStar C xStar : ℝ) : EReal) := by
  classical
  have hSup :
      fenchelConjugate n (indicatorFunction C) xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) :=
    section13_fenchelConjugate_indicatorFunction_eq_sSup_image_dotProduct (C := C) (xStar := xStar)
  -- Convert the `EReal` supremum into the coercion of the real supremum.
  set S : Set ℝ := Set.image (fun x : Fin n → Real => dotProduct x xStar) C
  have hS :
      ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) =
        ((fun r : ℝ => (r : EReal)) '' S) := by
    classical
    ext y
    constructor
    · rintro ⟨x, hxC, rfl⟩
      refine ⟨dotProduct x xStar, ?_, rfl⟩
      exact ⟨x, hxC, rfl⟩
    · rintro ⟨r, ⟨x, hxC, rfl⟩, rfl⟩
      exact ⟨x, hxC, by simp [dotProduct]⟩
  have hSne : S.Nonempty := by
    simpa [S] using hCne.image (fun x : Fin n → Real => dotProduct x xStar)
  calc
    fenchelConjugate n (indicatorFunction C) xStar
        =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) := hSup
    _ = sSup ((fun r : ℝ => (r : EReal)) '' S) := by rw [hS]
    _ = ((sSup S : ℝ) : EReal) := section13_sSup_image_coe_real_eq_coe_sSup (S := S) hSne hbdd
    _ = ((deltaStar C xStar : ℝ) : EReal) := by
      simp [deltaStar_eq_sSup_image_dotProduct_right, deltaStar, S]

/-- Under directional boundedness, the Fenchel conjugate of the indicator function equals the
Real-valued support function (coerced to `EReal`). -/
lemma section13_fenchelConjugate_indicatorFunction_eq_deltaStar_fun {n : Nat} (C : Set (Fin n → Real))
    (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    fenchelConjugate n (indicatorFunction C) =
      fun xStar : Fin n → Real => ((deltaStar C xStar : ℝ) : EReal) := by
  funext xStar
  simpa using
    (fenchelConjugate_indicatorFunction_eq_deltaStar (C := C) (xStar := xStar) hCne (hCbd xStar))

/-- If `x ∈ closure C`, then any affine map majorized by `indicatorFunction C` is nonpositive at `x`. -/
lemma section13_affine_le_indicatorFunction_le_zero_on_closure {n : Nat} {C : Set (Fin n → Real)}
    (h : AffineMap ℝ (Fin n → Real) Real)
    (hh : ∀ y : Fin n → Real, (h y : EReal) ≤ indicatorFunction C y) :
    ∀ x : Fin n → Real, x ∈ closure C → h x ≤ 0 := by
  classical
  rcases affineMap_exists_dotProduct_sub (h := h) with ⟨b, β, hb⟩
  intro x hxcl
  have hsubset : C ⊆ {y : Fin n → Real | dotProduct y b ≤ β} := by
    intro y hyC
    have hy0 : (h y : EReal) ≤ (0 : EReal) := by
      simpa [indicatorFunction, hyC] using hh y
    have hy0' : h y ≤ 0 := by
      exact (EReal.coe_le_coe_iff).1 (by simpa using hy0)
    have : dotProduct y b - β ≤ 0 := by
      simpa [hb y] using hy0'
    exact (sub_nonpos).1 this
  have hclosed : IsClosed ({y : Fin n → Real | dotProduct y b ≤ β} : Set (Fin n → Real)) := by
    simpa using (isClosed_setOf_dotProduct_le (n := n) (b := b) (β := β))
  have hclsubset : closure C ⊆ {y : Fin n → Real | dotProduct y b ≤ β} :=
    (IsClosed.closure_subset_iff hclosed).2 hsubset
  have hxle : dotProduct x b ≤ β := hclsubset hxcl
  calc
    h x = dotProduct x b - β := hb x
    _ ≤ 0 := (sub_nonpos).2 hxle


end Section13
end Chap03
