/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part2

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- The coordinate-sum linear map on `Fin m`-indexed tuples. -/
def sumLinearMap {n m : Nat} :
    (Fin m → EuclideanSpace Real (Fin n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
  { toFun := fun x => ∑ i, x i
    map_add' := by
      intro x y
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro r x
      simpa using
        (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => x i) (r := r)).symm }

/-- The image of the product set under the sum map is the Minkowski sum. -/
lemma image_sumLinearMap_pi_eq_sum {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) :
    sumLinearMap (n := n) (m := m) '' (Set.pi Set.univ C) = ∑ i, C i := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxmem :
        ∀ i, x i ∈ C i := by
      intro i
      exact (Set.mem_pi.mp hx) i (by simp)
    refine
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
          (f := fun i => C i) _).2 ?_
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      exact hxmem i
    · simp [sumLinearMap]
  · intro hy
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
            (f := fun i => C i) y).1 hy with ⟨x, hxmem, hsum⟩
    have hxpi : x ∈ Set.pi Set.univ C := by
      refine (Set.mem_pi).2 ?_
      intro i hi
      exact hxmem (i := i) (by simp)
    refine ⟨x, hxpi, ?_⟩
    simpa [sumLinearMap] using hsum

/-- Linear equivalence between `EuclideanSpace Real (Fin (m * n))` and block vectors. -/
noncomputable def euclideanSpace_equiv_prod_block {n m : Nat} :
    EuclideanSpace Real (Fin (m * n)) ≃ₗ[Real] (Fin m → EuclideanSpace Real (Fin n)) := by
  classical
  have hcard : Fintype.card (Fin m × Fin n) = m * n := by
    simp
  let efinProd : Fin m × Fin n ≃ Fin (m * n) :=
    Fintype.equivFinOfCardEq hcard
  let efin : Fin (m * n) ≃ Fin m × Fin n := efinProd.symm
  let e1 :
      EuclideanSpace Real (Fin (m * n)) ≃ₗ[Real] (Fin (m * n) → Real) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m * n))).toLinearEquiv
  let e2 : (Fin (m * n) → Real) ≃ₗ[Real] (Fin m × Fin n → Real) :=
    LinearEquiv.piCongrLeft (R := Real) (φ := fun _ : Fin m × Fin n => Real) efin
  let e3 : (Fin m × Fin n → Real) ≃ₗ[Real] ((Σ i : Fin m, Fin n) → Real) :=
    (LinearEquiv.piCongrLeft (R := Real) (φ := fun _ : Fin m × Fin n => Real)
      (Equiv.sigmaEquivProd (Fin m) (Fin n))).symm
  let e4 : ((Σ i : Fin m, Fin n) → Real) ≃ₗ[Real] (Fin m → Fin n → Real) :=
    LinearEquiv.piCurry (R := Real) (κ := fun _ : Fin m => Fin n) (α := fun _ _ => Real)
  let e5 : (Fin m → Fin n → Real) ≃ₗ[Real] (Fin m → EuclideanSpace Real (Fin n)) :=
    LinearEquiv.piCongrRight (R := Real)
      (fun _ => (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv)
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

/-- The block product set in `ℝ^{m n}` associated to `C`. -/
def blockSet {n m : Nat} (C : Fin m → Set (EuclideanSpace Real (Fin n))) :
    Set (EuclideanSpace Real (Fin (m * n))) :=
  (euclideanSpace_equiv_prod_block (n := n) (m := m)) ⁻¹' Set.pi Set.univ C

/-- The block sum linear map on `EuclideanSpace Real (Fin (m * n))`. -/
def blockSumLinearMap {n m : Nat} :
    EuclideanSpace Real (Fin (m * n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
  (sumLinearMap (n := n) (m := m)).comp
    (euclideanSpace_equiv_prod_block (n := n) (m := m)).toLinearMap

/-- The block equivalence sends `blockSet` to the product set. -/
lemma image_equiv_block_eq_pi {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) :
    (euclideanSpace_equiv_prod_block (n := n) (m := m)) '' blockSet (n := n) (m := m) C =
      Set.pi Set.univ C := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [blockSet] using hx
  · intro hy
    refine ⟨(euclideanSpace_equiv_prod_block (n := n) (m := m)).symm y, ?_, by simp⟩
    simpa [blockSet] using hy

/-- Membership in the closure of `blockSet` is coordinatewise closure. -/
lemma mem_closure_block_iff {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (x : EuclideanSpace Real (Fin (m * n))) :
    x ∈ closure (blockSet (n := n) (m := m) C) ↔
      ∀ i, (euclideanSpace_equiv_prod_block (n := n) (m := m) x) i ∈ closure (C i) := by
  classical
  have hpre :
      closure (blockSet (n := n) (m := m) C) =
        (euclideanSpace_equiv_prod_block (n := n) (m := m)).toContinuousLinearEquiv ⁻¹'
          closure (Set.pi Set.univ C) := by
    simpa [blockSet] using
      (ContinuousLinearEquiv.preimage_closure
        (e := (euclideanSpace_equiv_prod_block (n := n) (m := m)).toContinuousLinearEquiv)
        (s := Set.pi Set.univ C)).symm
  have hx :
      x ∈ closure (blockSet (n := n) (m := m) C) ↔
        (euclideanSpace_equiv_prod_block (n := n) (m := m) x) ∈ closure (Set.pi Set.univ C) := by
    simp [hpre]
  have hx' :
      (euclideanSpace_equiv_prod_block (n := n) (m := m) x) ∈ closure (Set.pi Set.univ C) ↔
        ∀ i, (euclideanSpace_equiv_prod_block (n := n) (m := m) x) i ∈ closure (C i) := by
    simpa using
      (mem_closure_pi (I := Set.univ) (s := C)
        (x := (euclideanSpace_equiv_prod_block (n := n) (m := m) x)))
  exact hx.trans hx'

/-- Recession cone of the block set is coordinatewise recession. -/
lemma mem_recessionCone_block_iff {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (hCne : ∀ i, Set.Nonempty (C i))
    (z : EuclideanSpace Real (Fin (m * n))) :
    z ∈ Set.recessionCone (closure (blockSet (n := n) (m := m) C)) ↔
      ∀ i,
        (euclideanSpace_equiv_prod_block (n := n) (m := m) z) i ∈
          Set.recessionCone (closure (C i)) := by
  classical
  let e := euclideanSpace_equiv_prod_block (n := n) (m := m)
  classical
  choose x0 hx0 using hCne
  constructor
  · intro hz i xi hxi t ht
    let xfun : Fin m → EuclideanSpace Real (Fin n) := fun j =>
      if h : j = i then xi else x0 j
    let x : EuclideanSpace Real (Fin (m * n)) := e.symm xfun
    have hx : x ∈ closure (blockSet (n := n) (m := m) C) := by
      apply (mem_closure_block_iff (C := C) (x := x)).2
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [x, xfun, e] using hxi
      · have hx0' : x0 j ∈ closure (C j) := subset_closure (hx0 j)
        simpa [x, xfun, hji, e] using hx0'
    have hxz : x + t • z ∈ closure (blockSet (n := n) (m := m) C) := hz hx ht
    have hxz' := (mem_closure_block_iff (C := C) (x := x + t • z)).1 hxz
    have hxzi : (e (x + t • z)) i ∈ closure (C i) := hxz' i
    have hxzi' : (e (x + t • z)) i = xi + t • (e z) i := by
      have hx_eq : e x = xfun := by
        simp [x]
      calc
        (e (x + t • z)) i = (e x + t • e z) i := by simp
        _ = xfun i + t • (e z) i := by simp [hx_eq]
        _ = xi + t • (e z) i := by simp [xfun]
    simpa [hxzi'] using hxzi
  · intro hz x hx t ht
    apply (mem_closure_block_iff (C := C) (x := x + t • z)).2
    have hx' := (mem_closure_block_iff (C := C) (x := x)).1 hx
    intro i
    have hx_i : (e x) i ∈ closure (C i) := hx' i
    have hz_i : (e z) i ∈ Set.recessionCone (closure (C i)) := hz i
    have hmem : (e x) i + t • (e z) i ∈ closure (C i) := hz_i hx_i ht
    have hxzi' : (e (x + t • z)) i = (e x) i + t • (e z) i := by
      simp
    simpa [hxzi'] using hmem

/-- The block equivalence sends the block recession cone to the product of recession cones. -/
lemma image_equiv_recessionCone_block_eq_pi {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (hCne : ∀ i, Set.Nonempty (C i)) :
    (euclideanSpace_equiv_prod_block (n := n) (m := m)) ''
        Set.recessionCone (closure (blockSet (n := n) (m := m) C)) =
      Set.pi Set.univ (fun i => Set.recessionCone (closure (C i))) := by
  classical
  let e := euclideanSpace_equiv_prod_block (n := n) (m := m)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine (Set.mem_pi).2 ?_
    intro i hi
    exact (mem_recessionCone_block_iff (C := C) hCne (z := x)).1 hx i
  · intro hy
    have hy' :
        ∀ i, y i ∈ Set.recessionCone (closure (C i)) := by
      intro i
      exact (Set.mem_pi.mp hy) i (by simp)
    have hx :
        e.symm y ∈ Set.recessionCone (closure (blockSet (n := n) (m := m) C)) := by
      apply (mem_recessionCone_block_iff (C := C) hCne (z := e.symm y)).2
      intro i
      simpa [e] using hy' i
    refine ⟨e.symm y, hx, by simp [e]⟩

/-- Corollary 9.1.1. Let `C1, ..., Cm` be non-empty convex sets in `R^n`. Assume that whenever
`z1, ..., zm` satisfy `zi ∈ 0^+ (cl Ci)` and `z1 + ... + zm = 0`, then each `zi` lies in the
lineality space of `cl Ci`. Then `cl (C1 + ... + Cm) = cl C1 + ... + cl Cm` and
`0^+ (cl (C1 + ... + Cm)) = 0^+ (cl C1) + ... + 0^+ (cl Cm)`. In particular, if each `Ci` is
closed then `C1 + ... + Cm` is closed. -/
theorem closure_sum_eq_sum_closure_of_recessionCone_sum_zero_lineality
    {n m : Nat} (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCconv : ∀ i, Convex Real (C i))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (closure (C i))) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (C i))) :
    closure (∑ i, C i) = ∑ i, closure (C i) ∧
      Set.recessionCone (closure (∑ i, C i)) =
        ∑ i, Set.recessionCone (closure (C i)) ∧
      ((∀ i, IsClosed (C i)) → IsClosed (∑ i, C i)) := by
  classical
  let e := euclideanSpace_equiv_prod_block (n := n) (m := m)
  let Cflat : Set (EuclideanSpace Real (Fin (m * n))) := blockSet (n := n) (m := m) C
  let Aflat : EuclideanSpace Real (Fin (m * n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    blockSumLinearMap (n := n) (m := m)
  have hCflat_ne : Set.Nonempty Cflat := by
    classical
    choose x0 hx0 using hCne
    let xfun : Fin m → EuclideanSpace Real (Fin n) := x0
    have hxpi : xfun ∈ Set.pi Set.univ C := by
      refine (Set.mem_pi).2 ?_
      intro i hi
      exact hx0 i
    let x : EuclideanSpace Real (Fin (m * n)) := e.symm xfun
    have hx : x ∈ Cflat := by
      simpa [Cflat, blockSet, e, x] using hxpi
    exact ⟨x, hx⟩
  have hCflat_conv : Convex Real Cflat := by
    have hpi : Convex Real (Set.pi Set.univ C) := by
      refine convex_pi ?_
      intro i hi
      simpa using hCconv i
    simpa [Cflat, blockSet] using
      (Convex.affine_preimage (f := (e.toLinearMap).toAffineMap) hpi)
  have hlineal_flat :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure Cflat) → Aflat z = 0 →
        z ∈ Set.linealitySpace (closure Cflat) := by
    intro z _hz0 hzrec hzA
    have hzrec' :
        ∀ i, (e z) i ∈ Set.recessionCone (closure (C i)) :=
      (mem_recessionCone_block_iff (C := C) hCne (z := z)).1 (by
        simpa [Cflat, blockSet] using hzrec)
    have hsum : ∑ i, (e z) i = 0 := by
      simpa [Aflat, blockSumLinearMap, sumLinearMap, e] using hzA
    have hlineal_coord :
        ∀ i, (e z) i ∈ Set.linealitySpace (closure (C i)) :=
      hlineal (fun i => (e z) i) hzrec' hsum
    have hzneg : -z ∈ Set.recessionCone (closure Cflat) := by
      have hzneg' :
          ∀ i, (e (-z)) i ∈ Set.recessionCone (closure (C i)) := by
        intro i
        have hlin_i :
            (e z) i ∈ (-Set.recessionCone (closure (C i))) ∩ Set.recessionCone (closure (C i)) := by
          simpa [Set.linealitySpace] using hlineal_coord i
        have hneg_i : - (e z) i ∈ Set.recessionCone (closure (C i)) := by
          simpa using hlin_i.1
        have : (e (-z)) i = - (e z) i := by simp
        simpa [this] using hneg_i
      have : -z ∈ Set.recessionCone (closure (blockSet (n := n) (m := m) C)) := by
        exact (mem_recessionCone_block_iff (C := C) hCne (z := -z)).2 hzneg'
      simpa [Cflat, blockSet] using this
    have hzneg' : z ∈ -Set.recessionCone (closure Cflat) := by
      simpa using hzneg
    have : z ∈ (-Set.recessionCone (closure Cflat)) ∩ Set.recessionCone (closure Cflat) :=
      ⟨hzneg', hzrec⟩
    simpa [Set.linealitySpace] using this
  have hmain :=
    linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
      (n := m * n) (m := n) (C := Cflat) hCflat_ne hCflat_conv Aflat hlineal_flat
  have he : e '' Cflat = Set.pi Set.univ C := by
    simpa [Cflat, blockSet, e] using (image_equiv_block_eq_pi (C := C))
  have he_closure :
      e '' closure Cflat = Set.pi Set.univ (fun i => closure (C i)) := by
    calc
      e '' closure Cflat = closure (e '' Cflat) := by
        simpa using (e.toContinuousLinearEquiv.image_closure (s := Cflat))
      _ = closure (Set.pi Set.univ C) := by simp [he]
      _ = Set.pi Set.univ (fun i => closure (C i)) := by
        simpa using (closure_pi_set (I := Set.univ) (s := C))
  have he_rec :
      e '' Set.recessionCone (closure Cflat) =
        Set.pi Set.univ (fun i => Set.recessionCone (closure (C i))) := by
    simpa [Cflat, blockSet, e] using
      (image_equiv_recessionCone_block_eq_pi (C := C) hCne)
  have hAflat_image :
      Aflat '' Cflat = ∑ i, C i := by
    have hAflat :
        Aflat '' Cflat =
          sumLinearMap (n := n) (m := m) '' (e '' Cflat) := by
      have h := (Set.image_image (sumLinearMap (n := n) (m := m)) (e : _ → _) Cflat)
      simpa [Aflat, blockSumLinearMap] using h.symm
    calc
      Aflat '' Cflat =
          sumLinearMap (n := n) (m := m) '' (e '' Cflat) := hAflat
      _ = sumLinearMap (n := n) (m := m) '' Set.pi Set.univ C := by simp [he]
      _ = ∑ i, C i := image_sumLinearMap_pi_eq_sum (C := C)
  have hAflat_closure :
      Aflat '' closure Cflat = ∑ i, closure (C i) := by
    have hAflat :
        Aflat '' closure Cflat =
          sumLinearMap (n := n) (m := m) '' (e '' closure Cflat) := by
      have h := (Set.image_image (sumLinearMap (n := n) (m := m)) (e : _ → _) (closure Cflat))
      simpa [Aflat, blockSumLinearMap] using h.symm
    calc
      Aflat '' closure Cflat =
          sumLinearMap (n := n) (m := m) '' (e '' closure Cflat) := hAflat
      _ = sumLinearMap (n := n) (m := m) '' Set.pi Set.univ (fun i => closure (C i)) := by
        simp [he_closure]
      _ = ∑ i, closure (C i) := image_sumLinearMap_pi_eq_sum (C := fun i => closure (C i))
  have hAflat_rec :
      Aflat '' Set.recessionCone (closure Cflat) =
        ∑ i, Set.recessionCone (closure (C i)) := by
    have hAflat :
        Aflat '' Set.recessionCone (closure Cflat) =
          sumLinearMap (n := n) (m := m) '' (e '' Set.recessionCone (closure Cflat)) := by
      have h :=
        (Set.image_image (sumLinearMap (n := n) (m := m)) (e : _ → _)
          (Set.recessionCone (closure Cflat)))
      simpa [Aflat, blockSumLinearMap] using h.symm
    calc
      Aflat '' Set.recessionCone (closure Cflat) =
          sumLinearMap (n := n) (m := m) '' (e '' Set.recessionCone (closure Cflat)) := hAflat
      _ =
          sumLinearMap (n := n) (m := m) ''
            Set.pi Set.univ (fun i => Set.recessionCone (closure (C i))) := by
        simp [he_rec]
      _ = ∑ i, Set.recessionCone (closure (C i)) := by
        simpa using
          (image_sumLinearMap_pi_eq_sum
            (C := fun i => Set.recessionCone (closure (C i))))
  have hclosure :
      closure (∑ i, C i) = ∑ i, closure (C i) := by
    calc
      closure (∑ i, C i) = closure (Aflat '' Cflat) := by simp [hAflat_image]
      _ = Aflat '' closure Cflat := hmain.1
      _ = ∑ i, closure (C i) := hAflat_closure
  have hrec :
      Set.recessionCone (closure (∑ i, C i)) =
        ∑ i, Set.recessionCone (closure (C i)) := by
    have hclosure_sum : closure (∑ i, C i) = Aflat '' closure Cflat := by
      calc
        closure (∑ i, C i) = closure (Aflat '' Cflat) := by simp [hAflat_image]
        _ = Aflat '' closure Cflat := hmain.1
    have hrec0 :
        Set.recessionCone (closure (∑ i, C i)) =
          Set.recessionCone (Aflat '' closure Cflat) :=
      congrArg Set.recessionCone hclosure_sum
    calc
      Set.recessionCone (closure (∑ i, C i)) =
          Set.recessionCone (Aflat '' closure Cflat) := hrec0
      _ = Aflat '' Set.recessionCone (closure Cflat) := hmain.2.1
      _ = ∑ i, Set.recessionCone (closure (C i)) := hAflat_rec
  refine ⟨hclosure, hrec, ?_⟩
  intro hCclosed
  have hsum : (∑ i, closure (C i)) = ∑ i, C i := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  have hclosure' : closure (∑ i, C i) = ∑ i, C i := by
    calc
      closure (∑ i, C i) = ∑ i, closure (C i) := hclosure
      _ = ∑ i, C i := hsum
  exact (closure_eq_iff_isClosed).1 hclosure'

/-- Corollary 9.1.1.1. Under the hypotheses of Corollary 9.1.1, if all `C_i` are closed,
then `C_1 + ... + C_m` is closed. -/
theorem closed_sum_of_closed_sets_of_recessionCone_sum_zero_lineality
    {n m : Nat} (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCconv : ∀ i, Convex Real (C i))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (closure (C i))) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (C i)))
    (hCclosed : ∀ i, IsClosed (C i)) :
    IsClosed (∑ i, C i) := by
  have h :=
    closure_sum_eq_sum_closure_of_recessionCone_sum_zero_lineality (C := C) hCne hCconv
      hlineal
  exact h.2.2 hCclosed

/-- Zero belongs to the lineality space of any set. -/
lemma zero_mem_linealitySpace {n : Nat} (C : Set (EuclideanSpace Real (Fin n))) :
    (0 : EuclideanSpace Real (Fin n)) ∈ Set.linealitySpace C := by
  have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa using hx
  have hzero_neg : (0 : EuclideanSpace Real (Fin n)) ∈ -Set.recessionCone C := by
    simpa using hzero
  simpa [Set.linealitySpace] using And.intro hzero_neg hzero

/-- In the `Fin 2` case, no-opposite-recession implies lineality. -/
lemma lineality_of_no_opposite_recession_fin2
    {n : Nat} (C : Fin 2 → Set (EuclideanSpace Real (Fin n)))
    (hC0closed : IsClosed (C 0)) (hC1closed : IsClosed (C 1))
    (hopp :
      ∀ z,
        z ∈ Set.recessionCone (C 0) → -z ∈ Set.recessionCone (C 1) → z = 0) :
    ∀ z : Fin 2 → EuclideanSpace Real (Fin n),
      (∀ i, z i ∈ Set.recessionCone (closure (C i))) →
      (∑ i, z i) = 0 →
      ∀ i, z i ∈ Set.linealitySpace (closure (C i)) := by
  classical
  intro z hzrec hsum i
  have hz0 : z 0 ∈ Set.recessionCone (C 0) := by
    simpa [hC0closed.closure_eq] using hzrec 0
  have hz1 : z 1 ∈ Set.recessionCone (C 1) := by
    simpa [hC1closed.closure_eq] using hzrec 1
  have hsum' : z 0 + z 1 = 0 := by
    simpa [Fin.sum_univ_two] using hsum
  have hz1eq : z 1 = -z 0 := by
    have hsum'' : z 1 + z 0 = 0 := by
      simpa [add_comm] using hsum'
    exact eq_neg_of_add_eq_zero_left hsum''
  have hz0neg : -z 0 ∈ Set.recessionCone (C 1) := by
    simpa [hz1eq] using hz1
  have hz0zero : z 0 = 0 := hopp _ hz0 hz0neg
  have hz1zero : z 1 = 0 := by
    simpa [hz0zero] using hsum'
  fin_cases i
  · simpa [hC0closed.closure_eq, hz0zero] using
      (zero_mem_linealitySpace (C := C 0))
  · simpa [hC1closed.closure_eq, hz1zero] using
      (zero_mem_linealitySpace (C := C 1))

/-- Corollary 9.1.2. Let `C1` and `C2` be non-empty closed convex sets in `R^n`. Assume there is
no direction of recession of `C1` whose opposite is a direction of recession of `C2` (in
particular, this holds if either `C1` or `C2` is bounded). Then `C1 + C2` is closed and
`0^+ (C1 + C2) = 0^+ C1 + 0^+ C2`. -/
theorem closed_add_recessionCone_eq_of_no_opposite_recession
    {n : Nat} {C1 C2 : Set (EuclideanSpace Real (Fin n))}
    (hC1ne : Set.Nonempty C1) (hC2ne : Set.Nonempty C2)
    (hC1conv : Convex Real C1) (hC2conv : Convex Real C2)
    (hC1closed : IsClosed C1) (hC2closed : IsClosed C2)
    (hopp :
      ∀ z,
        z ∈ Set.recessionCone C1 → -z ∈ Set.recessionCone C2 → z = 0) :
    IsClosed (C1 + C2) ∧
      Set.recessionCone (C1 + C2) = Set.recessionCone C1 + Set.recessionCone C2 := by
  classical
  let C : Fin 2 → Set (EuclideanSpace Real (Fin n)) := fun i => if i = 0 then C1 else C2
  have hCne : ∀ i, Set.Nonempty (C i) := by
    intro i
    fin_cases i
    · simpa [C] using hC1ne
    · simpa [C] using hC2ne
  have hCconv : ∀ i, Convex Real (C i) := by
    intro i
    fin_cases i
    · simpa [C] using hC1conv
    · simpa [C] using hC2conv
  have hCclosed : ∀ i, IsClosed (C i) := by
    intro i
    fin_cases i
    · simpa [C] using hC1closed
    · simpa [C] using hC2closed
  have hC0closed : IsClosed (C 0) := by
    simpa [C] using hC1closed
  have hC1closed' : IsClosed (C 1) := by
    simpa [C] using hC2closed
  have hopp' :
      ∀ z,
        z ∈ Set.recessionCone (C 0) → -z ∈ Set.recessionCone (C 1) → z = 0 := by
    intro z hz0 hz1
    have hz0' : z ∈ Set.recessionCone C1 := by
      simpa [C] using hz0
    have hz1' : -z ∈ Set.recessionCone C2 := by
      simpa [C] using hz1
    exact hopp z hz0' hz1'
  have hlineal :
      ∀ z : Fin 2 → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (closure (C i))) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (C i)) :=
    lineality_of_no_opposite_recession_fin2 (C := C) hC0closed hC1closed' hopp'
  have h :=
    closure_sum_eq_sum_closure_of_recessionCone_sum_zero_lineality (C := C) hCne hCconv
      hlineal
  have hclosed_sum : IsClosed (∑ i, C i) := h.2.2 hCclosed
  have hclosed : IsClosed (C1 + C2) := by
    simpa [C, Fin.sum_univ_two] using hclosed_sum
  have hCclosed' : ∀ i, closure (C i) = C i := by
    intro i
    exact (hCclosed i).closure_eq
  have hrec' :
      Set.recessionCone (∑ i, C i) = ∑ i, Set.recessionCone (C i) := by
    have hrec'' := h.2.1
    rw [hclosed_sum.closure_eq] at hrec''
    simpa [hCclosed'] using hrec''
  have hrec :
      Set.recessionCone (C1 + C2) = Set.recessionCone C1 + Set.recessionCone C2 := by
    simpa [C, Fin.sum_univ_two] using hrec'
  exact ⟨hclosed, hrec⟩

/- Corollary 9.1.3. Let `K₁, …, Kₘ` be non-empty convex cones in `R^n`. Assume that if
`zᵢ ∈ cl Kᵢ` for `i = 1, …, m` and `z₁ + ⋯ + zₘ = 0`, then each `zᵢ` lies in the lineality
space of `cl Kᵢ`. Then `cl (K₁ + ⋯ + Kₘ) = cl K₁ + ⋯ + cl Kₘ`. -/
/-- Convexity is preserved when transporting a convex cone through `EuclideanSpace.equiv`. -/
lemma convex_of_IsConvexCone_image_equiv {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))}
    (hKcone :
      IsConvexCone n
        (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) K)) :
    Convex Real K := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  have hconv_image : Convex Real (Set.image e K) := hKcone.2
  have hpre :
      Convex Real (e ⁻¹' (Set.image e K)) :=
    (Convex.affine_preimage (f := (e.toLinearMap).toAffineMap) hconv_image)
  have hpre_eq : e ⁻¹' (Set.image e K) = K := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : x = y := e.injective hxy.symm
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  simpa [hpre_eq] using hpre

/-- Positive scaling in `K` inherited from the cone structure of its coordinate image. -/
lemma pos_smul_mem_of_IsConvexCone_image_equiv {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))}
    (hKcone :
      IsConvexCone n
        (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) K)) :
    ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K := by
  classical
  intro x hx t ht
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  have hx' : e x ∈ Set.image e K := ⟨x, hx, rfl⟩
  have hsmul : t • e x ∈ Set.image e K := hKcone.1 (e x) hx' t ht
  rcases hsmul with ⟨y, hy, hyeq⟩
  have hmap : t • e x = e (t • x) := by
    exact (LinearEquiv.map_smul (e := e.toLinearEquiv) t x).symm
  have hy_eq : y = t • x := by
    apply e.injective
    calc
      e y = t • e x := hyeq
      _ = e (t • x) := hmap
  simpa [hy_eq] using hy

/-- A nonempty set closed under positive scaling has `0` in its closure. -/
lemma zero_mem_closure_of_pos_smul_closed {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))}
    (hKne : K.Nonempty)
    (hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K) :
    (0 : EuclideanSpace Real (Fin n)) ∈ closure K := by
  classical
  rcases hKne with ⟨x, hx⟩
  by_cases hx0 : x = 0
  · simpa [hx0] using (subset_closure hx)
  refine (Metric.mem_closure_iff).2 ?_
  intro ε hε
  let t : Real := ε / (‖x‖ + 1)
  have htpos : 0 < t := by
    have hxpos : 0 < ‖x‖ + 1 := by linarith [norm_nonneg x]
    exact div_pos hε hxpos
  refine ⟨t • x, hsmul x hx t htpos, ?_⟩
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    simpa [Real.norm_eq_abs, abs_of_pos htpos] using (norm_smul t x)
  have hxpos : 0 < ‖x‖ + 1 := by linarith [norm_nonneg x]
  have hfrac : ‖x‖ / (‖x‖ + 1) < (1 : Real) := by
    have hlt : ‖x‖ < ‖x‖ + 1 := by linarith
    exact (div_lt_one hxpos).2 hlt
  have hlt : t * ‖x‖ < ε := by
    have ht_eq : t * ‖x‖ = ε * (‖x‖ / (‖x‖ + 1)) := by
      calc
        t * ‖x‖ = (ε / (‖x‖ + 1)) * ‖x‖ := rfl
        _ = ε * ‖x‖ / (‖x‖ + 1) := by
          simpa using (div_mul_eq_mul_div ε (‖x‖ + 1) ‖x‖)
        _ = ε * (‖x‖ / (‖x‖ + 1)) := by
          simp [mul_div_assoc]
    have hlt' : ε * (‖x‖ / (‖x‖ + 1)) < ε * 1 := by
      exact mul_lt_mul_of_pos_left hfrac hε
    calc
      t * ‖x‖ = ε * (‖x‖ / (‖x‖ + 1)) := ht_eq
      _ < ε * 1 := hlt'
      _ = ε := by simp
  have : dist (t • x) 0 < ε := by
    simpa [dist_eq_norm, hnorm] using hlt
  simpa using this

/-- The recession cone of the closure of a convex cone is the closure itself. -/
lemma recessionCone_closure_eq_of_convexCone {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))}
    (hKne : K.Nonempty)
    (hKcone :
      IsConvexCone n
        (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) K)) :
    Set.recessionCone (closure K) = closure K := by
  classical
  have hKconv : Convex Real K := convex_of_IsConvexCone_image_equiv (K := K) hKcone
  have hKsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K :=
    pos_smul_mem_of_IsConvexCone_image_equiv (K := K) hKcone
  have hcl_conv : Convex Real (closure K) := hKconv.closure
  have hcl_smul :
      ∀ x ∈ closure K, ∀ t : Real, 0 < t → t • x ∈ closure K := by
    intro x hx t ht
    have hx' : t • x ∈ t • closure K := by
      refine ⟨x, hx, rfl⟩
    have hx'' : t • x ∈ closure (t • K) :=
      (smul_closure_subset (c := t) (s := K)) hx'
    have hsubset : closure (t • K) ⊆ closure K := by
      refine closure_mono ?_
      intro y hy
      rcases hy with ⟨x, hxK, rfl⟩
      exact hKsmul x hxK t ht
    exact hsubset hx''
  have hcl_add :
      ∀ x ∈ closure K, ∀ y ∈ closure K, x + y ∈ closure K := by
    intro x hx y hy
    have hmid : midpoint Real x y ∈ closure K := Convex.midpoint_mem hcl_conv hx hy
    have htwo : (2 : Real) • midpoint Real x y ∈ closure K :=
      hcl_smul _ hmid 2 (by norm_num)
    have hsum : x + y = (2 : Real) • midpoint Real x y := by
      calc
        x + y = midpoint Real x y + midpoint Real x y := by
          simp
        _ = (2 : Real) • midpoint Real x y := by
          simpa using (two_smul Real (midpoint Real x y)).symm
    simpa [hsum] using htwo
  have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ closure K :=
    zero_mem_closure_of_pos_smul_closed (K := K) hKne hKsmul
  have hrec :
      Set.recessionCone (closure K) =
        { y : EuclideanSpace Real (Fin n) | ∀ x ∈ closure K, x + y ∈ closure K } :=
    recessionCone_eq_add_mem (C := closure K) hcl_conv
  ext y
  constructor
  · intro hy
    have hy' :
        y ∈ { y : EuclideanSpace Real (Fin n) | ∀ x ∈ closure K, x + y ∈ closure K } := by
      simpa [hrec] using hy
    have : 0 + y ∈ closure K := hy' 0 hzero
    simpa using this
  · intro hy
    have hy' : ∀ x ∈ closure K, x + y ∈ closure K := by
      intro x hx
      exact hcl_add x hx y hy
    have :
        y ∈ { y : EuclideanSpace Real (Fin n) | ∀ x ∈ closure K, x + y ∈ closure K } := hy'
    simpa [hrec] using this

theorem closure_sum_eq_sum_closure_of_convexCone_sum_zero_lineality
    {n m : Nat} (K : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hKne : ∀ i, Set.Nonempty (K i))
    (hKcone :
      ∀ i,
        IsConvexCone n
          (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) (K i)))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ closure (K i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (K i))) :
    closure (∑ i, K i) = ∑ i, closure (K i) := by
  classical
  have hKconv : ∀ i, Convex Real (K i) := by
    intro i
    exact convex_of_IsConvexCone_image_equiv (K := K i) (hKcone i)
  have hrec : ∀ i, Set.recessionCone (closure (K i)) = closure (K i) := by
    intro i
    exact
      recessionCone_closure_eq_of_convexCone (K := K i) (hKne i) (hKcone i)
  have hlineal' :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (closure (K i))) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (K i)) := by
    intro z hz hsum
    have hz' : ∀ i, z i ∈ closure (K i) := by
      intro i
      simpa [hrec i] using hz i
    exact hlineal z hz' hsum
  exact
    (closure_sum_eq_sum_closure_of_recessionCone_sum_zero_lineality (C := K) hKne hKconv
        hlineal').1

/- Remark 9.1.0.2. The recession cone `0^+ (A C)` can differ from `A (0^+ C)` even when
`C` and `A C` are closed; for instance with `C = {(xi1, xi2) | xi2 ≥ xi1^2}` and
`A (xi1, xi2) = xi1`. -/
/-- The parabola set `{x | x1 ≥ x0^2}` is closed. -/
lemma isClosed_parabola :
    IsClosed {x : EuclideanSpace Real (Fin 2) | x 1 ≥ (x 0) ^ 2} := by
  have hcont0 : Continuous (fun x : EuclideanSpace Real (Fin 2) => x 0) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => Real)
        (i := (0 : Fin 2)))
  have hcont1 : Continuous (fun x : EuclideanSpace Real (Fin 2) => x 1) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => Real)
        (i := (1 : Fin 2)))
  have hcont_sq : Continuous (fun x : EuclideanSpace Real (Fin 2) => (x 0) ^ 2) := by
    simpa [pow_two] using hcont0.mul hcont0
  simpa [ge_iff_le] using (isClosed_le hcont_sq hcont1)

/-- The projection of the parabola set onto the first coordinate is all of `ℝ`. -/
lemma image_parabola_eq_univ :
    let C : Set (EuclideanSpace Real (Fin 2)) := {x | x 1 ≥ (x 0) ^ 2}
    let A : EuclideanSpace Real (Fin 2) → EuclideanSpace Real (Fin 1) :=
      fun x =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => x 0)
    A '' C = (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
  classical
  intro C A
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
    let μ : Real := coords1 y 0
    let x : EuclideanSpace Real (Fin 2) := !₂[μ, μ ^ 2]
    have hx0 : x 0 = μ := by simp [x]
    have hx1 : x 1 = μ ^ 2 := by simp [x]
    have hxC : x ∈ C := by
      simp [C, hx0, hx1]
    have hy_fun : coords1 y = fun _ : Fin 1 => μ := by
      ext i
      fin_cases i
      simp [μ]
    have hy_eq : coords1.symm (fun _ : Fin 1 => μ) = y := by
      simpa [hy_fun] using coords1.symm_apply_apply y
    have hAx : A x = y := by
      simpa [A, hx0] using hy_eq
    exact ⟨x, hxC, hAx⟩

/-- The recession cone of the parabola is the vertical ray `{(0, z2) | z2 ≥ 0}`. -/
lemma recessionCone_parabola_eq :
    Set.recessionCone {x : EuclideanSpace Real (Fin 2) | x 1 ≥ (x 0) ^ 2} =
      {z : EuclideanSpace Real (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} := by
  ext z
  constructor
  · intro hz
    have hz_prop : ∀ t : Real, 0 ≤ t → (t • z) 1 ≥ ((t • z) 0) ^ 2 := by
      intro t ht
      have hmem := hz (x := 0) (by simp) (t := t) ht
      simpa using hmem
    have hz0 : z 0 = 0 := by
      by_contra hz0ne
      have hz0sq_pos : 0 < (z 0) ^ 2 := by
        simpa [sq_pos_iff] using hz0ne
      by_cases hz1neg : z 1 < 0
      · have h1 := hz_prop 1 (by exact zero_le_one)
        have hz1ge : z 1 ≥ (z 0) ^ 2 := by simpa using h1
        have hz0sq_nonneg : 0 ≤ (z 0) ^ 2 := by
          exact sq_nonneg (z 0)
        linarith
      · have hz1_nonneg : 0 ≤ z 1 :=
          le_of_not_gt (by simpa using hz1neg)
        let t : Real := z 1 / (z 0) ^ 2 + 1
        have htpos : 0 < t := by
          have hz1_div_nonneg : 0 ≤ z 1 / (z 0) ^ 2 :=
            div_nonneg hz1_nonneg (le_of_lt hz0sq_pos)
          linarith
        have hineq := hz_prop t (le_of_lt htpos)
        have htne : t ≠ 0 := ne_of_gt htpos
        have hineq' : z 1 ≥ t * (z 0) ^ 2 := by
          have hineq' : t * z 1 ≥ t ^ 2 * (z 0) ^ 2 := by
            simpa [mul_pow] using hineq
          have hineq'' : (1 / t) * (t * z 1) ≥ (1 / t) * (t ^ 2 * (z 0) ^ 2) := by
            have hpos : 0 ≤ (1 / t) := by
              exact le_of_lt (by simpa using (inv_pos.mpr htpos))
            exact mul_le_mul_of_nonneg_left hineq' hpos
          field_simp [htne] at hineq''
          simpa [mul_comm, mul_left_comm, mul_assoc] using hineq''
        have hcontr : z 1 ≥ z 1 + (z 0) ^ 2 := by
          have ht_def : t * (z 0) ^ 2 = z 1 + (z 0) ^ 2 := by
            dsimp [t]
            field_simp [hz0ne]
          simpa [ht_def] using hineq'
        linarith
    have hz1_nonneg : 0 ≤ z 1 := by
      have h1 := hz_prop 1 (by exact zero_le_one)
      have hz1ge : z 1 ≥ (z 0) ^ 2 := by simpa using h1
      simpa [hz0] using hz1ge
    exact ⟨hz0, hz1_nonneg⟩
  · intro hz
    rcases hz with ⟨hz0, hz1_nonneg⟩
    intro x hx t ht
    have hx0 : (x + t • z) 0 = x 0 + t * z 0 := by simp
    have hx1 : (x + t • z) 1 = x 1 + t * z 1 := by simp
    have hsq : (x 0 + t * z 0) ^ 2 = (x 0) ^ 2 := by simp [hz0]
    have htz1_nonneg : 0 ≤ t * z 1 := mul_nonneg ht hz1_nonneg
    have hx1_ge : x 1 ≥ (x 0) ^ 2 := hx
    have hineq : x 1 + t * z 1 ≥ (x 0 + t * z 0) ^ 2 := by
      have : x 1 + t * z 1 ≥ x 1 := by linarith
      linarith [hx1_ge, hsq]
    have : (x + t • z) 1 ≥ ((x + t • z) 0) ^ 2 := by
      simpa [hx0, hx1] using hineq
    simpa using this

/-- The image of the recession cone under the projection is `{0}`. -/
lemma image_recessionCone_parabola_eq_singleton :
    let C : Set (EuclideanSpace Real (Fin 2)) := {x | x 1 ≥ (x 0) ^ 2}
    let A : EuclideanSpace Real (Fin 2) → EuclideanSpace Real (Fin 1) :=
      fun x =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => x 0)
    A '' Set.recessionCone C = ({0} : Set (EuclideanSpace Real (Fin 1))) := by
  classical
  intro C A
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hrec :
        Set.recessionCone C =
          {z : EuclideanSpace Real (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} := by
      simpa [C] using recessionCone_parabola_eq
    have hz' : z 0 = 0 ∧ 0 ≤ z 1 := by
      have : z ∈ {z : EuclideanSpace Real (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} := by
        simpa [hrec] using hz
      simpa using this
    have hAz : A z = 0 := by
      ext i
      fin_cases i
      simp [A, hz'.1]
    simp [hAz]
  · intro hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    refine ⟨0, ?_, ?_⟩
    · intro x hx t ht
      simpa using hx
    · ext i
      fin_cases i
      simp [A]
lemma recessionCone_image_ne_image_recessionCone_parabola :
    let C : Set (EuclideanSpace Real (Fin 2)) := {x | x 1 ≥ (x 0) ^ 2}
    let A : EuclideanSpace Real (Fin 2) → EuclideanSpace Real (Fin 1) :=
      fun x =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => x 0)
    IsClosed C ∧ IsClosed (A '' C) ∧
      Set.recessionCone (A '' C) ≠ A '' Set.recessionCone C := by
  classical
  let C : Set (EuclideanSpace Real (Fin 2)) := {x | x 1 ≥ (x 0) ^ 2}
  let A : EuclideanSpace Real (Fin 2) → EuclideanSpace Real (Fin 1) :=
    fun x =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => x 0)
  have hCclosed : IsClosed C := by
    simpa [C] using isClosed_parabola
  have hAC : A '' C = (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
    simpa [C, A] using image_parabola_eq_univ
  have hACclosed : IsClosed (A '' C) := by
    simp [hAC]
  have hrec_univ : Set.recessionCone (A '' C) =
      (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
    ext y
    constructor
    · intro _hy
      exact Set.mem_univ y
    · intro _hy x hx t ht
      simp [hAC]
  have hrec_image :
      A '' Set.recessionCone C = ({0} : Set (EuclideanSpace Real (Fin 1))) := by
    simpa [C, A] using image_recessionCone_parabola_eq_singleton
  refine ⟨hCclosed, hACclosed, ?_⟩
  intro hEq
  have hv :
      (!₂[(1 : Real)] : EuclideanSpace Real (Fin 1)) ∈
        (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
    simp
  have hvrec :
      (!₂[(1 : Real)] : EuclideanSpace Real (Fin 1)) ∈
        Set.recessionCone (A '' C) := by
    simpa [hrec_univ.symm] using hv
  have hvimage :
      (!₂[(1 : Real)] : EuclideanSpace Real (Fin 1)) ∈
        A '' Set.recessionCone C := by
    rw [← hEq]
    exact hvrec
  have hv' :
      (!₂[(1 : Real)] : EuclideanSpace Real (Fin 1)) ∈
        ({0} : Set (EuclideanSpace Real (Fin 1))) := by
    rw [← hrec_image]
    exact hvimage
  have hv0 :
      (!₂[(1 : Real)] : EuclideanSpace Real (Fin 1)) = 0 := by
    exact (Set.mem_singleton_iff.mp hv')
  have h10 : (1 : Real) = 0 := by
    have h := congrArg (fun v : EuclideanSpace Real (Fin 1) => v 0) hv0
    simp at h
  linarith

/-- The fiber infimum under a linear map is convex when the original function is convex. -/
lemma convexFunction_linearMap_infimum {n m : Nat}
    {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hconv : ConvexFunction h) :
    ConvexFunction
      (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
  have hconv_on : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h := by
    simpa [ConvexFunction] using hconv
  have hconv_on' :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) :=
    convexFunctionOn_inf_fiber_linearMap (A := A) (h := h) hconv_on
  simpa [ConvexFunction] using hconv_on'

/-- The epigraph of the fiber infimum is nonempty if the original epigraph is nonempty. -/
lemma nonempty_epigraph_linearMap_infimum {n m : Nat}
    {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) h)) :
    Set.Nonempty
      (epigraph (Set.univ : Set (Fin m → Real))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })) := by
  classical
  rcases hne with ⟨⟨x, μ⟩, hx⟩
  refine ⟨(A x, μ), ?_⟩
  have hxle : h x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hx
  have hxmem :
      h x ∈ { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } := by
    exact ⟨x, rfl, rfl⟩
  have hle :
      sInf { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } ≤ h x :=
    sInf_le hxmem
  have hle' :
      sInf { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } ≤ (μ : EReal) :=
    le_trans hle hxle
  exact (mem_epigraph_univ_iff
    (f := fun y => sInf { z : EReal | ∃ x' : Fin n → Real, A x' = y ∧ z = h x' })).2 hle'

/-- The lifted linear map on product spaces sending `(x, μ)` to `(A x, μ)`. -/
def linearMap_prod {n m : Nat} (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (Fin n → Real) × Real →ₗ[Real] (Fin m → Real) × Real :=
  { toFun := fun p => (A p.1, p.2)
    map_add' := by
      intro p q
      ext <;> simp
    map_smul' := by
      intro r p
      ext <;> simp }

/-- Linear equivalence between `(Fin n → ℝ) × ℝ` and `ℝ^{n+1}` via append. -/
noncomputable def prodLinearEquiv_append {n : Nat} :
    ((Fin n → Real) × Real) ≃ₗ[Real] EuclideanSpace Real (Fin (n + 1)) := by
  classical
  let eN : (Fin n → Real) ≃ₗ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv
  let e1 : Real ≃ₗ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv)
  let g :
      ((Fin n → Real) × Real) ≃ₗ[Real]
        (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    LinearEquiv.prodCongr eN e1
  exact g.trans (appendAffineEquiv n 1).linear

/-- Conjugate `linearMap_prod` under the append equivalence. -/
noncomputable def linearMap_prod_embedded {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin (m + 1)) :=
  LinearMap.comp (prodLinearEquiv_append (n := m)).toLinearMap
    (LinearMap.comp (linearMap_prod A) (prodLinearEquiv_append (n := n)).symm.toLinearMap)

/-- The embedded image matches the image under the conjugated linear map. -/
lemma image_linearMap_prod_embedded {n m : Nat} {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (prodLinearEquiv_append (n := m)) ''
        ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) =
      (linearMap_prod_embedded (A := A)) ''
        ((prodLinearEquiv_append (n := n)) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
  classical
  ext y
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(prodLinearEquiv_append (n := n)) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [linearMap_prod_embedded, LinearMap.comp_apply]
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(linearMap_prod A x), ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [linearMap_prod_embedded, LinearMap.comp_apply]

end Section09
end Chap02
