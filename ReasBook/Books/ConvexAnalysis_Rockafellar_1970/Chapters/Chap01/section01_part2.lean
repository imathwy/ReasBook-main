/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Pengfei Hao, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part1

section Chap01
section Section01

/-- Theorem 1.4: Given `b ∈ R^m` and an `m × n` real matrix `B`, the set
`M = {x ∈ R^n | Bx = b}` is an affine set in `R^n`. Moreover, every affine set in `R^n`
can be represented in this way. -/
theorem affineSet_iff_eq_mulVec (m n : Nat) (b : Fin m → Real)
    (B : Matrix (Fin m) (Fin n) Real) :
    IsAffineSet n {x : Fin n → Real | B.mulVec x = b} ∧
      (∀ M : Set (Fin n → Real), IsAffineSet n M →
        ∃ m' : Nat, ∃ b' : Fin m' → Real,
          ∃ B' : Matrix (Fin m') (Fin n) Real,
            M = {x : Fin n → Real | B'.mulVec x = b'}) := by
  classical
  refine ⟨isAffineSet_mulVec_eq (m:=m) (n:=n) (b:=b) (B:=B), ?_⟩
  intro M hM
  by_cases hne : Set.Nonempty M
  · rcases (parallel_submodule_unique_of_affine n M hM hne).exists with ⟨L, hL⟩
    rcases hL.1 with ⟨a, hMa⟩
    rcases exists_linearMap_with_ker n L with ⟨m', f, hker⟩
    have hset : M = {x : Fin n → Real | f x = f a} := by
      simpa [hMa] using (translate_eq_linear_fiber (n:=n) (L:=L) (a:=a) (f:=f) hker)
    let B' : Matrix (Fin m') (Fin n) Real :=
      LinearMap.toMatrix (Pi.basisFun Real (Fin n)) (Pi.basisFun Real (Fin m')) f
    have hmul : ∀ x, B'.mulVec x = f x := by
      simpa [B'] using (linearMap_toMatrix_mulVec (m:=m') (n:=n) f)
    refine ⟨m', f a, B', ?_⟩
    ext x
    constructor
    · intro hx
      have hx' : f x = f a := by
        have : x ∈ {x : Fin n → Real | f x = f a} := by simpa [hset] using hx
        simpa using this
      simpa [hmul] using hx'
    · intro hx
      have hx' : f x = f a := by
        simpa [hmul] using hx
      have : x ∈ {x : Fin n → Real | f x = f a} := by simpa using hx'
      simpa [hset] using this
  · refine ⟨1, (fun _ => (1 : Real)), 0, ?_⟩
    ext x
    constructor
    · intro hx
      exfalso
      exact hne ⟨x, hx⟩
    · intro hx
      exfalso
      have hx' : (0 : Fin 1 → Real) = (fun _ => (1 : Real)) := by
        simpa using hx
      have h0' : (0 : Real) = 1 := by
        simpa using congrArg (fun f => f 0) hx'
      exact zero_ne_one h0'

open Classical in
/-- A matrix fiber is the intersection of its row equation sets. -/
lemma mulVec_eq_sInter_rowSets (m n : Nat) (B : Matrix (Fin m) (Fin n) Real)
    (b : Fin m → Real) :
    {x : Fin n → Real | B.mulVec x = b} =
      ⋂₀ ((Finset.univ.image
        (fun i : Fin m => {x : Fin n → Real | (B i) ⬝ᵥ x = b i})) :
        Set (Set (Fin n → Real))) := by
  classical
  ext x
  constructor
  · intro hx
    refine (Set.mem_sInter).2 ?_
    intro H hH
    have hH' : H ∈ (Finset.univ.image
        (fun i : Fin m => {x : Fin n → Real | (B i) ⬝ᵥ x = b i})) := hH
    rcases Finset.mem_image.1 hH' with ⟨i, _, rfl⟩
    have hx' : B.mulVec x = b := by
      simpa using hx
    have hx_i : (B i) ⬝ᵥ x = b i := by
      have h := congrArg (fun f => f i) hx'
      simpa [Matrix.mulVec] using h
    simpa using hx_i
  · intro hx
    apply funext
    intro i
    have hmem :
        {x : Fin n → Real | (B i) ⬝ᵥ x = b i} ∈
          (Finset.univ.image
            (fun i : Fin m => {x : Fin n → Real | (B i) ⬝ᵥ x = b i})) := by
      refine Finset.mem_image.2 ?_
      exact ⟨i, Finset.mem_univ i, rfl⟩
    have hx_i : x ∈ {x : Fin n → Real | (B i) ⬝ᵥ x = b i} :=
      (Set.mem_sInter).1 hx _ hmem
    have hx_eq : (B i) ⬝ᵥ x = b i := by
      simpa using hx_i
    simpa [Matrix.mulVec] using hx_eq

/-- A nonzero normal vector gives a hyperplane as a row equation set. -/
lemma rowSet_isHyperplane_of_ne_zero (n : Nat) (b : Fin n → Real) (β : Real) (hb : b ≠ 0) :
    IsHyperplane n {x : Fin n → Real | x ⬝ᵥ b = β} := by
  have hn : 0 < n := by
    by_contra h
    have hzero : n = 0 := Nat.eq_zero_of_not_pos h
    subst hzero
    apply hb
    funext i
    exact (Fin.elim0 i)
  exact (hyperplane_iff_eq_dotProduct n hn).1 β b hb

/-- The equation for a zero row is either `univ` or `empty`. -/
lemma rowSet_eq_univ_or_empty_of_zero (n : Nat) (β : Real) :
    {x : Fin n → Real | (0 : Fin n → Real) ⬝ᵥ x = β} =
      (if β = 0 then Set.univ else (∅ : Set (Fin n → Real))) := by
  ext x
  by_cases hβ : β = 0
  · simp [hβ, dotProduct_comm, dotProduct_zero]
  · simp [hβ, dotProduct_comm, dotProduct_zero, eq_comm]

/-- The empty set is a finite intersection of two parallel hyperplanes when `n > 0`. -/
lemma empty_eq_sInter_two_hyperplanes (n : Nat) (hn : 0 < n) :
    ∃ S : Finset (Set (Fin n → Real)),
      (∀ H ∈ S, IsHyperplane n H) ∧
        (⋂₀ (S : Set (Set (Fin n → Real))) = (∅ : Set (Fin n → Real))) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let b : Fin n → Real := Pi.single i0 (1 : Real)
  have hb : b ≠ 0 := by
    intro hzero
    have : (1 : Real) = 0 := by
      simpa [b] using congrArg (fun f => f i0) hzero
    exact one_ne_zero this
  let H0 : Set (Fin n → Real) := {x : Fin n → Real | x ⬝ᵥ b = 0}
  let H1 : Set (Fin n → Real) := {x : Fin n → Real | x ⬝ᵥ b = 1}
  let S : Finset (Set (Fin n → Real)) := {H0, H1}
  refine ⟨S, ?_, ?_⟩
  · intro H hH
    have hH' : H = H0 ∨ H = H1 := by
      simpa [S] using hH
    rcases hH' with rfl | rfl
    · exact rowSet_isHyperplane_of_ne_zero n b 0 hb
    · exact rowSet_isHyperplane_of_ne_zero n b 1 hb
  · ext x
    constructor
    · intro hx
      have hx0 : x ⬝ᵥ b = 0 := by
        have hx0' : x ∈ H0 := (Set.mem_sInter).1 hx _ (by simp [S])
        simpa [H0] using hx0'
      have hx1 : x ⬝ᵥ b = 1 := by
        have hx1' : x ∈ H1 := (Set.mem_sInter).1 hx _ (by simp [S])
        simpa [H1] using hx1'
      have hx1' := hx1
      simp [hx0] at hx1'
    · intro hx
      exact hx.elim

/-- Corollary 1.4.1. Every affine subset of `R^n` is an intersection of a finite collection
of hyperplanes. -/
theorem affineSet_eq_sInter_hyperplanes (n : Nat) (M : Set (Fin n → Real)) (hn : 0 < n) :
    IsAffineSet n M →
      ∃ S : Finset (Set (Fin n → Real)),
        (∀ H ∈ S, IsHyperplane n H) ∧ M = ⋂₀ (S : Set (Set (Fin n → Real))) := by
  classical
  intro hM
  have hrepr := (affineSet_iff_eq_mulVec (m:=0) (n:=n) (b:=0) (B:=0)).2
  rcases hrepr M hM with ⟨m, b, B, hMrepr⟩
  let rowSet : Fin m → Set (Fin n → Real) :=
    fun i => {x : Fin n → Real | (B i) ⬝ᵥ x = b i}
  by_cases hbad : ∃ i : Fin m, B i = 0 ∧ b i ≠ 0
  · have hMempty : M = (∅ : Set (Fin n → Real)) := by
      ext x
      constructor
      · intro hx
        rcases hbad with ⟨i, hBi, hbi⟩
        have hx' : B.mulVec x = b := by
          simpa [hMrepr] using hx
        have hx_i : (B i) ⬝ᵥ x = b i := by
          have h := congrArg (fun f => f i) hx'
          simpa [Matrix.mulVec] using h
        have : (0 : Real) = b i := by
          simpa [hBi, dotProduct_comm, dotProduct_zero] using hx_i
        exact (hbi this.symm).elim
      · intro hx
        exact hx.elim
    rcases empty_eq_sInter_two_hyperplanes n hn with ⟨S, hS, hSempty⟩
    refine ⟨S, hS, ?_⟩
    simp [hMempty, hSempty]
  · have hzero : ∀ i : Fin m, B i = 0 → b i = 0 := by
      intro i hBi
      by_contra hbi
      exact hbad ⟨i, hBi, hbi⟩
    let Sidx : Finset (Fin m) := Finset.univ.filter (fun i => B i ≠ 0)
    let S : Finset (Set (Fin n → Real)) := Sidx.image rowSet
    have hS : ∀ H ∈ S, IsHyperplane n H := by
      intro H hH
      rcases Finset.mem_image.1 hH with ⟨i, hi, rfl⟩
      have hi' : B i ≠ 0 := by
        have hi' := hi
        dsimp [Sidx] at hi'
        exact (Finset.mem_filter.1 hi').2
      have hH' : IsHyperplane n {x : Fin n → Real | x ⬝ᵥ (B i) = b i} :=
        rowSet_isHyperplane_of_ne_zero n (B i) (b i) hi'
      simpa [rowSet, dotProduct_comm] using hH'
    have hM_sInter_full :
        M = ⋂₀ ((Finset.univ.image rowSet) : Set (Set (Fin n → Real))) := by
      have h := (mulVec_eq_sInter_rowSets (m:=m) (n:=n) (B:=B) (b:=b))
      simpa [rowSet, hMrepr] using h
    have hInter_eq :
        ⋂₀ ((Finset.univ.image rowSet) : Set (Set (Fin n → Real))) =
          ⋂₀ (S : Set (Set (Fin n → Real))) := by
      ext x
      constructor
      · intro hx
        refine (Set.mem_sInter).2 ?_
        intro H hH
        have hH' : H ∈ S := hH
        rcases Finset.mem_image.1 hH' with ⟨i, hi, rfl⟩
        have hmem : rowSet i ∈ (Finset.univ.image rowSet) := by
          refine Finset.mem_image.2 ?_
          exact ⟨i, Finset.mem_univ i, rfl⟩
        have hx' : x ∈ rowSet i := (Set.mem_sInter).1 hx _ hmem
        simpa [rowSet] using hx'
      · intro hx
        refine (Set.mem_sInter).2 ?_
        intro H hH
        have hH' : H ∈ (Finset.univ.image rowSet) := hH
        rcases Finset.mem_image.1 hH' with ⟨i, _, rfl⟩
        by_cases hBi : B i = 0
        · have hbi0 : b i = 0 := hzero i hBi
          have hx' : (B i) ⬝ᵥ x = b i := by
            simp [hBi, hbi0, dotProduct_comm, dotProduct_zero]
          simpa [rowSet] using hx'
        · have hi' : i ∈ Sidx := by
            have hi' : i ∈ Finset.univ.filter (fun i => B i ≠ 0) := by
              exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hBi⟩
            simpa [Sidx] using hi'
          have hmem : rowSet i ∈ S := by
            refine Finset.mem_image.2 ?_
            exact ⟨i, hi', rfl⟩
          have hx' : x ∈ rowSet i := (Set.mem_sInter).1 hx _ hmem
          simpa [rowSet] using hx'
    refine ⟨S, hS, ?_⟩
    exact hM_sInter_full.trans hInter_eq

/-- Text 1.9: A set of `m + 1` points `b0, b1, ..., bm` is said to be affinely independent if
`aff {b0, b1, ..., bm}` is `m`-dimensional. -/
def IsAffinelyIndependent (m n : Nat) (b : Fin (m + 1) → Fin n → Real) : Prop :=
  let S : Set (Fin n → Real) := Set.range b
  let hS : IsAffineSet n (affineHull n S) :=
    (isAffineSet_iff_affineSubspace n (affineHull n S)).2 ⟨affineSpan Real S, rfl⟩
  affineSetDim n (affineHull n S) hS = (m : Int)

/-- Text 1.9 (mathlib): The book's notion agrees with `AffineIndependent`. -/
theorem isAffinelyIndependent_iff_affineIndependent (m n : Nat)
    (b : Fin (m + 1) → Fin n → Real) :
    IsAffinelyIndependent m n b ↔ AffineIndependent Real b := by
  classical
  have hS : IsAffineSet n (affineHull n (Set.range b)) :=
    (isAffineSet_iff_affineSubspace n (affineHull n (Set.range b))).2
      ⟨affineSpan Real (Set.range b), rfl⟩
  have hne : Set.Nonempty (affineHull n (Set.range b)) := by
    refine ⟨b 0, ?_⟩
    have hb0 : b 0 ∈ Set.range b := ⟨0, rfl⟩
    have hsubset :
        Set.range b ⊆ affineSpan Real (Set.range b) :=
      subset_affineSpan (k:=Real) (V:=Fin n → Real) (P:=Fin n → Real) (Set.range b)
    have hb0' : b 0 ∈ (affineSpan Real (Set.range b) : Set (Fin n → Real)) :=
      hsubset hb0
    simpa [affineHull] using hb0'
  let L : Submodule Real (Fin n → Real) :=
    Classical.choose
      (parallel_submodule_unique_of_affine n (affineHull n (Set.range b)) hS hne).exists
  have hLspec :
      IsParallelAffineSet n (affineHull n (Set.range b)) (L : Set (Fin n → Real)) ∧
        (L : Set (Fin n → Real)) =
          {x | ∃ a ∈ affineHull n (Set.range b), ∃ c ∈ affineHull n (Set.range b), x = a - c} :=
    (Classical.choose_spec
      (parallel_submodule_unique_of_affine n (affineHull n (Set.range b)) hS hne).exists)
  have hLset : (L : Set (Fin n → Real)) =
      (affineHull n (Set.range b)) -ᵥ (affineHull n (Set.range b)) := by
    ext x
    constructor
    · intro hx
      rcases (by simpa [hLspec.2] using hx) with ⟨a, ha, b', hb', rfl⟩
      exact (Set.mem_vsub).2 ⟨a, ha, b', hb', by simp [vsub_eq_sub]⟩
    · intro hx
      rcases (Set.mem_vsub).1 hx with ⟨a, ha, b', hb', hxab⟩
      have hxab' : x = a - b' := by
        simpa [vsub_eq_sub] using hxab.symm
      have : x ∈ {x | ∃ a ∈ affineHull n (Set.range b),
          ∃ c ∈ affineHull n (Set.range b), x = a - c} :=
        ⟨a, ha, b', hb', hxab'⟩
      simpa [hLspec.2] using this
  have hdir_set :
      ((affineSpan Real (Set.range b)).direction : Set (Fin n → Real)) =
        (affineHull n (Set.range b)) -ᵥ (affineHull n (Set.range b)) := by
    have hne' : (affineSpan Real (Set.range b) : Set (Fin n → Real)).Nonempty := by
      simpa [affineHull] using hne
    simpa [affineHull] using
      (AffineSubspace.coe_direction_eq_vsub_set (s:=affineSpan Real (Set.range b)) hne')
  have hLdir : L = (affineSpan Real (Set.range b)).direction := by
    ext x
    change
      x ∈ (L : Set (Fin n → Real)) ↔
        x ∈ ((affineSpan Real (Set.range b)).direction : Set (Fin n → Real))
    simp [hLset, hdir_set]
  have hdim :
      affineSetDim n (affineHull n (Set.range b)) hS =
        Int.ofNat (Module.finrank Real (vectorSpan Real (Set.range b))) := by
    have hdim' :
        affineSetDim n (affineHull n (Set.range b)) hS =
          Int.ofNat (Module.finrank Real L) := by
      simp [affineSetDim, hne, L]
    have hfinrank :
        Module.finrank Real L =
          Module.finrank Real (affineSpan Real (Set.range b)).direction := by
      exact
        congrArg (fun S : Submodule Real (Fin n → Real) => Module.finrank Real S) hLdir
    have hfinrank' :
        Module.finrank Real (affineSpan Real (Set.range b)).direction =
          Module.finrank Real (vectorSpan Real (Set.range b)) := by
      exact
        congrArg (fun S : Submodule Real (Fin n → Real) => Module.finrank Real S)
          (direction_affineSpan (k:=Real) (s:=Set.range b))
    have hdim'' :
        affineSetDim n (affineHull n (Set.range b)) hS =
          Int.ofNat (Module.finrank Real (affineSpan Real (Set.range b)).direction) := by
      simpa [hfinrank] using hdim'
    simpa [hfinrank'] using hdim''
  have hcard : Fintype.card (Fin (m + 1)) = m + 1 := by simp
  constructor
  · intro h
    have h' :
        Module.finrank Real (vectorSpan Real (Set.range b)) = m := by
      have : Int.ofNat (Module.finrank Real (vectorSpan Real (Set.range b))) = (m : Int) := by
        have h' :
            affineSetDim n (affineHull n (Set.range b)) hS = (m : Int) := by
          simpa [IsAffinelyIndependent] using h
        simpa [hdim] using h'
      exact Int.ofNat.inj this
    exact
      (affineIndependent_iff_finrank_vectorSpan_eq (k:=Real) (p:=b) (n:=m) hcard).2 h'
  · intro h
    have h' :
        Module.finrank Real (vectorSpan Real (Set.range b)) = m :=
      (affineIndependent_iff_finrank_vectorSpan_eq (k:=Real) (p:=b) (n:=m) hcard).1 h
    have hdim' :
        affineSetDim n (affineHull n (Set.range b)) hS = (m : Int) := by
      calc
        affineSetDim n (affineHull n (Set.range b)) hS
            = Int.ofNat (Module.finrank Real (vectorSpan Real (Set.range b))) := hdim
        _ = (m : Int) := by simp [h']
    simpa [IsAffinelyIndependent] using hdim'

open scoped Pointwise

/-- Translating a set equals pointwise `vadd` in this commutative setting. -/
lemma setTranslate_eq_vadd (n : Nat) (S : Set (Fin n → Real)) (a : Fin n → Real) :
    SetTranslate n S a = a +ᵥ S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp [vadd_eq_add, add_comm]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp [vadd_eq_add, add_comm]

/-- Translating the difference set by `b0` recovers the original points. -/
lemma translate_range_sub_eq_union (m n : Nat) (b0 : Fin n → Real) (b : Fin m → Fin n → Real) :
    SetTranslate n ({0} ∪ Set.range (fun i : Fin m => b i - b0)) b0 =
      ({b0} ∪ Set.range b) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · left
      simpa using hy
    · right
      rcases hy with ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp
  · intro hx
    rcases hx with hx | hx
    · have hx' : x = b0 := by
        simpa using hx
      subst hx'
      refine ⟨0, ?_, ?_⟩
      · left; simp
      · simp
    · rcases hx with ⟨i, rfl⟩
      refine ⟨b i - b0, ?_, ?_⟩
      · right; exact ⟨i, rfl⟩
      · simp

/-- Affine hull commutes with translation. -/
lemma affineHull_translate (n : Nat) (S : Set (Fin n → Real)) (a : Fin n → Real) :
    affineHull n (SetTranslate n S a) = SetTranslate n (affineHull n S) a := by
  have h :=
    congrArg (fun (s : AffineSubspace Real (Fin n → Real)) => (s : Set (Fin n → Real)))
      (AffineSubspace.pointwise_vadd_span (v:=a) (s:=S) (k:=Real)
        (P:=Fin n → Real))
  simpa [affineHull, setTranslate_eq_vadd] using h.symm

/-- Affine independence of `b0, b1, ..., bm` is equivalent to linear independence
of the difference vectors. -/
lemma affineIndependent_iff_linearIndependent_b0 (m n : Nat)
    (b0 : Fin n → Real) (b : Fin m → Fin n → Real) :
    IsAffinelyIndependent m n (Fin.cases b0 (fun i => b i)) ↔
      LinearIndependent Real (fun i : Fin m => b i - b0) := by
  classical
  have h_aff :
      IsAffinelyIndependent m n (Fin.cases b0 (fun i => b i)) ↔
        AffineIndependent Real (Fin.cases b0 (fun i => b i)) :=
    isAffinelyIndependent_iff_affineIndependent m n (Fin.cases b0 (fun i => b i))
  have h_vsub :
      AffineIndependent Real (Fin.cases b0 (fun i => b i)) ↔
        LinearIndependent Real
          (fun i : {x // x ≠ (0 : Fin (m + 1))} =>
            (Fin.cases b0 (fun i => b i) i) - b0) := by
    simpa [vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub (k:=Real)
        (p:=Fin.cases b0 (fun i => b i)) (i1:= (0 : Fin (m + 1))))
  have h_equiv :
      LinearIndependent Real (fun i : Fin m => b i - b0) ↔
        LinearIndependent Real
          (fun i : {x // x ≠ (0 : Fin (m + 1))} =>
            (Fin.cases b0 (fun i => b i) i) - b0) := by
    let e : Fin m ≃ {i : Fin (m + 1) // i ≠ 0} :=
      { toFun := fun i => ⟨Fin.succ i, by simp⟩
        invFun := fun i => Fin.pred i.1 i.2
        left_inv := by intro i; simp
        right_inv := by intro i; ext; simp }
    simpa [Function.comp, e] using
      (linearIndependent_equiv (R:=Real) (e:=e)
        (f:=fun i : {x // x ≠ (0 : Fin (m + 1))} =>
          (Fin.cases b0 (fun i => b i) i) - b0))
  exact h_aff.trans (h_vsub.trans h_equiv.symm)

/-- Text 1.9.1: Let `b0, b1, ..., bm ∈ ℝ^n` and set
`L = aff {0, b1 - b0, ..., bm - b0}`. Then `aff {b0, b1, ..., bm} = b0 + L`.
Moreover, the points `b0, b1, ..., bm` are affinely independent if and only if the
vectors `b1 - b0, ..., bm - b0` are linearly independent. -/
theorem affineHull_eq_translate_and_affineIndependent_iff_linearIndependent
    (m n : Nat) (b0 : Fin n → Real) (b : Fin m → Fin n → Real) :
    let S : Set (Fin n → Real) := {b0} ∪ Set.range b
    let L : Set (Fin n → Real) :=
      affineHull n ({0} ∪ Set.range (fun i : Fin m => b i - b0))
    affineHull n S = SetTranslate n L b0 ∧
      (IsAffinelyIndependent m n (Fin.cases b0 (fun i => b i)) ↔
        LinearIndependent Real (fun i : Fin m => b i - b0)) := by
  classical
  dsimp
  refine ⟨?_, ?_⟩
  · have hS :
        SetTranslate n ({0} ∪ Set.range (fun i : Fin m => b i - b0)) b0 =
          insert b0 (Set.range b) := by
      simpa using
        (translate_range_sub_eq_union (m:=m) (n:=n) (b0:=b0) (b:=b))
    rw [← hS]
    simpa using
      (affineHull_translate (n:=n)
        (S:= {0} ∪ Set.range (fun i : Fin m => b i - b0)) (a:=b0))
  · simpa using
      (affineIndependent_iff_linearIndependent_b0 (m:=m) (n:=n) (b0:=b0) (b:=b))

/-- Membership in an affine hull of a finite family yields full-index coefficients. -/
lemma exists_coeffs_univ_of_mem_affineHull_range {m n : Nat}
    {b : Fin (m + 1) → Fin n → Real} {x : Fin n → Real}
    (hx : x ∈ affineHull n (Set.range b)) :
    ∃ coeffs : Fin (m + 1) → Real,
      Finset.sum Finset.univ (fun i => coeffs i) = 1 ∧
      Finset.sum Finset.univ (fun i => coeffs i • b i) = x := by
  classical
  have hx' : x ∈ affineSpan Real (Set.range b) := by
    simpa [affineHull] using hx
  obtain ⟨s, w, hw, hxcomb⟩ :=
    (mem_affineSpan_iff_eq_affineCombination (k:=Real) (V:=Fin n → Real)
        (p1:=x) (p:=b)).1 hx'
  let coeffs : Fin (m + 1) → Real := (Set.indicator (↑s) w)
  have hsum : Finset.sum Finset.univ (fun i => coeffs i) = 1 := by
    have hsum' : (∑ i, coeffs i) = ∑ i ∈ s, w i := by
      simpa [coeffs] using
        (Finset.sum_indicator_subset w (Finset.subset_univ s))
    calc
      Finset.sum Finset.univ (fun i => coeffs i) = ∑ i ∈ s, w i := by simpa using hsum'
      _ = 1 := hw
  refine ⟨coeffs, hsum, ?_⟩
  have hcomb :
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs = x := by
    have hcomb' :
        s.affineCombination Real b w =
          (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs := by
      simpa [coeffs] using
        (Finset.affineCombination_indicator_subset (k:=Real) (w:=w) (p:=b)
          (s₁:=s) (s₂:=Finset.univ) (h:=Finset.subset_univ s))
    calc
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs
          = s.affineCombination Real b w := by simpa using hcomb'.symm
      _ = x := by simpa using hxcomb.symm
  have hlin :=
    affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs) hsum
  calc
    Finset.sum Finset.univ (fun i => coeffs i • b i)
        = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs := by
            symm; exact hlin
    _ = x := hcomb

/-- Affine independence is equivalent to uniqueness of full-index coefficients. -/
lemma affineIndependent_iff_unique_coeffs_univ (m n : Nat) (b : Fin (m + 1) → Fin n → Real) :
    AffineIndependent Real b ↔
      ∀ coeffs₁ coeffs₂ : Fin (m + 1) → Real,
        Finset.sum Finset.univ (fun i => coeffs₁ i) = 1 →
        Finset.sum Finset.univ (fun i => coeffs₂ i) = 1 →
        Finset.sum Finset.univ (fun i => coeffs₁ i • b i) =
          Finset.sum Finset.univ (fun i => coeffs₂ i • b i) →
        coeffs₁ = coeffs₂ := by
  classical
  constructor
  · intro h coeffs₁ coeffs₂ hsum₁ hsum₂ hcomb
    have h' :=
      (affineIndependent_iff_eq_of_fintype_affineCombination_eq (k:=Real) (p:=b)).1 h
    have hcomb' :
        (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₁ =
          (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₂ := by
      have hlin₁ :=
        affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs₁) hsum₁
      have hlin₂ :=
        affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs₂) hsum₂
      calc
        (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₁
            = Finset.sum Finset.univ (fun i => coeffs₁ i • b i) := hlin₁
        _ = Finset.sum Finset.univ (fun i => coeffs₂ i • b i) := hcomb
        _ = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₂ := by
            symm; exact hlin₂
    exact h' coeffs₁ coeffs₂ (by simpa using hsum₁) (by simpa using hsum₂) hcomb'
  · intro h
    refine (affineIndependent_iff_eq_of_fintype_affineCombination_eq (k:=Real) (p:=b)).2 ?_
    intro coeffs₁ coeffs₂ hsum₁ hsum₂ hcomb
    have hcomb' :
        Finset.sum Finset.univ (fun i => coeffs₁ i • b i) =
          Finset.sum Finset.univ (fun i => coeffs₂ i • b i) := by
      have hlin₁ :=
        affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs₁) hsum₁
      have hlin₂ :=
        affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs₂) hsum₂
      calc
        Finset.sum Finset.univ (fun i => coeffs₁ i • b i)
            = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₁ := by
                symm; exact hlin₁
        _ = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₂ := hcomb
        _ = Finset.sum Finset.univ (fun i => coeffs₂ i • b i) := hlin₂
    exact h coeffs₁ coeffs₂ (by simpa using hsum₁) (by simpa using hsum₂) hcomb'

/-- Text 1.9.2: Let `b0, b1, ..., bm ∈ ℝ^n` and set `M = aff {b0, b1, ..., bm}`.
Every point `x ∈ M` admits a representation
`x = λ0 b0 + ··· + λm bm` with `λ0 + ··· + λm = 1`.
Moreover, the coefficients `(λ0, ..., λm)` are unique iff the points are affinely independent. -/
theorem affineHull_exists_affineCombination_and_unique_iff_affineIndependent
    (m n : Nat) (b : Fin (m + 1) → Fin n → Real) :
    let M : Set (Fin n → Real) := affineHull n (Set.range b)
    (∀ x ∈ M, ∃ coeffs : Fin (m + 1) → Real,
        Finset.sum Finset.univ (fun i => coeffs i) = 1 ∧
        Finset.sum Finset.univ (fun i => coeffs i • b i) = x) ∧
      (IsAffinelyIndependent m n b ↔
        ∀ x ∈ M, ∀ coeffs₁ coeffs₂ : Fin (m + 1) → Real,
          Finset.sum Finset.univ (fun i => coeffs₁ i) = 1 →
          Finset.sum Finset.univ (fun i => coeffs₂ i) = 1 →
          Finset.sum Finset.univ (fun i => coeffs₁ i • b i) = x →
          Finset.sum Finset.univ (fun i => coeffs₂ i • b i) = x →
          coeffs₁ = coeffs₂) := by
  classical
  dsimp
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa using
      (exists_coeffs_univ_of_mem_affineHull_range (m:=m) (n:=n) (b:=b) hx)
  · constructor
    · intro h x hx coeffs₁ coeffs₂ hsum₁ hsum₂ hcomb₁ hcomb₂
      have h_aff : AffineIndependent Real b :=
        (isAffinelyIndependent_iff_affineIndependent m n b).1 h
      have huniq :=
        (affineIndependent_iff_unique_coeffs_univ (m:=m) (n:=n) (b:=b)).1 h_aff
      have hcomb :
          Finset.sum Finset.univ (fun i => coeffs₁ i • b i) =
            Finset.sum Finset.univ (fun i => coeffs₂ i • b i) := by
        calc
          Finset.sum Finset.univ (fun i => coeffs₁ i • b i) = x := hcomb₁
          _ = Finset.sum Finset.univ (fun i => coeffs₂ i • b i) := hcomb₂.symm
      exact huniq coeffs₁ coeffs₂ hsum₁ hsum₂ hcomb
    · intro h
      apply (isAffinelyIndependent_iff_affineIndependent m n b).2
      refine (affineIndependent_iff_unique_coeffs_univ (m:=m) (n:=n) (b:=b)).2 ?_
      intro coeffs₁ coeffs₂ hsum₁ hsum₂ hcomb
      let x : Fin n → Real := Finset.sum Finset.univ (fun i => coeffs₁ i • b i)
      have hx : x ∈ affineHull n (Set.range b) := by
        have hsum₁' :
            ∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), coeffs₁ i = (1 : Real) := by
          simpa using hsum₁
        have hcomb₁ :
            (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs₁ = x := by
          have hlin :=
            affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs₁) hsum₁
          simpa [x] using hlin
        have hx' : x ∈ affineSpan Real (Set.range b) := by
          have hmem :=
            affineCombination_mem_affineSpan (k:=Real) (s:=Finset.univ) (w:=coeffs₁) hsum₁' b
          simpa [hcomb₁] using hmem
        simpa [affineHull] using hx'
      have hx1 : Finset.sum Finset.univ (fun i => coeffs₁ i • b i) = x := by
        simp [x]
      have hx2 : Finset.sum Finset.univ (fun i => coeffs₂ i • b i) = x := by
        calc
          Finset.sum Finset.univ (fun i => coeffs₂ i • b i)
              = Finset.sum Finset.univ (fun i => coeffs₁ i • b i) := by
                  symm; exact hcomb
          _ = x := by simp [x]
      exact h x hx coeffs₁ coeffs₂ hsum₁ hsum₂ hx1 hx2



end Section01
end Chap01
