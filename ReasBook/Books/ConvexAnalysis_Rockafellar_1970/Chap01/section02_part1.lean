/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section02

/-- Definition 2.0.1. A subset `C` of `Real^n` is convex if `(1 - λ) • x + λ • y ∈ C`
whenever `x ∈ C`, `y ∈ C`, and `0 < λ < 1`. -/
def IsConvexSet (n : Nat) (C : Set (Fin n → Real)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ t : Real, 0 < t → t < 1 →
    (1 - t) • x + t • y ∈ C

/-- Convert the book's strict-parameter definition to mathlib's `Convex`. -/
lemma isConvexSet_imp_convex (n : Nat) (C : Set (Fin n → Real)) :
    IsConvexSet n C → Convex Real C := by
  intro hC
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  have hb1 : b < (1 : Real) := by linarith
  have hmem := hC x hx y hy b hb hb1
  have hcoeff : 1 - b = a := by linarith
  simpa [hcoeff] using hmem

/-- Convert mathlib's `Convex` to the book's strict-parameter definition. -/
lemma convex_imp_isConvexSet (n : Nat) (C : Set (Fin n → Real)) :
    Convex Real C → IsConvexSet n C := by
  intro hC x hx y hy t ht0 ht1
  have ht0' : 0 < 1 - t := by linarith
  have hab : (1 - t) + t = (1 : Real) := by ring
  have hmem :=
    (convex_iff_forall_pos).1 hC hx hy ht0' ht0 hab
  exact hmem

/-- The book's convexity definition is equivalent to mathlib's `Convex` for subsets of `Real^n`. -/
theorem isConvexSet_iff_convex (n : Nat) (C : Set (Fin n → Real)) :
    IsConvexSet n C ↔ Convex Real C := by
  constructor
  · exact isConvexSet_imp_convex n C
  · exact convex_imp_isConvexSet n C

/-- Definition 2.0.2. The set `{(1 - λ) • x + λ • y | 0 ≤ λ ≤ 1}` is called the (closed) line
segment between `x` and `y`. -/
def lineSegment (n : Nat) (x y : Fin n → Real) : Set (Fin n → Real) :=
  segment (𝕜:=Real) x y

/-- The book's description of the line segment as an image of `Icc (0:Real) 1` agrees with
mathlib's `segment`. -/
theorem lineSegment_eq_image (n : Nat) (x y : Fin n → Real) :
    lineSegment n x y =
      (fun t : Real => (1 - t) • x + t • y) '' Set.Icc (0 : Real) 1 := by
  simpa [lineSegment] using (segment_eq_image (𝕜:=Real) (x:=x) (y:=y))

/-- Definition 2.0.3. For non-zero `b ∈ Real^n` and `β ∈ Real`,
the set `{x | ⟪x, b⟫ ≤ β}` is a closed half-space. -/
def closedHalfSpaceLE (n : Nat) (b : Fin n → Real) (β : Real) : Set (Fin n → Real) :=
  {x : Fin n → Real | x ⬝ᵥ b ≤ β}

/-- Definition 2.0.3. For non-zero `b ∈ Real^n` and `β ∈ Real`,
the set `{x | ⟪x, b⟫ ≥ β}` is a closed half-space. -/
def closedHalfSpaceGE (n : Nat) (b : Fin n → Real) (β : Real) : Set (Fin n → Real) :=
  {x : Fin n → Real | x ⬝ᵥ b ≥ β}

/-- Definition 2.0.3. For non-zero `b ∈ Real^n` and `β ∈ Real`,
the set `{x | ⟪x, b⟫ < β}` is an open half-space. -/
def openHalfSpaceLT (n : Nat) (b : Fin n → Real) (β : Real) : Set (Fin n → Real) :=
  {x : Fin n → Real | x ⬝ᵥ b < β}

/-- Definition 2.0.3. For non-zero `b ∈ Real^n` and `β ∈ Real`,
the set `{x | ⟪x, b⟫ > β}` is an open half-space. -/
def openHalfSpaceGT (n : Nat) (b : Fin n → Real) (β : Real) : Set (Fin n → Real) :=
  {x : Fin n → Real | x ⬝ᵥ b > β}

/-- Theorem 2.1. The intersection of an arbitrary collection of convex sets is convex. -/
theorem convex_iInter_family {ι : Sort*} (n : Nat) (C : ι → Set (Fin n → Real))
    (hC : ∀ i, Convex Real (C i)) : Convex Real (⋂ i, C i) := by
  simpa using (convex_iInter (s:=C) hC)

/-- The dot product with a fixed vector is linear in the left argument. -/
lemma isLinearMap_dotProduct_left (n : Nat) (b : Fin n → Real) :
    IsLinearMap ℝ (fun x : Fin n → Real => x ⬝ᵥ b) := by
  refine { map_add := ?_, map_smul := ?_ }
  · intro x y
    simp
  · intro c x
    simp

/-- Each half-space defined by a dot product inequality is convex. -/
lemma convex_dotProduct_le (n : Nat) (b : Fin n → Real) (β : Real) :
    Convex Real {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  simpa using
    (convex_halfSpace_le (f:=fun x : Fin n → Real => x ⬝ᵥ b)
      (h:=isLinearMap_dotProduct_left n b) β)

/-- Corollary 2.1.1. For vectors `b i ∈ Real^n` and scalars `β i ∈ Real` indexed by an
arbitrary set `ι`, the set `C = {x | ⟪x, b i⟫ ≤ β i, ∀ i}` is convex. -/
theorem convex_set_of_dotProduct_le {ι : Sort*} (n : Nat) (b : ι → Fin n → Real)
    (β : ι → Real) :
    Convex Real {x : Fin n → Real | ∀ i, x ⬝ᵥ b i ≤ β i} := by
  have hC : ∀ i, Convex Real {x : Fin n → Real | x ⬝ᵥ b i ≤ β i} := fun i =>
    convex_dotProduct_le n (b i) (β i)
  have hset :
      (⋂ i, {x : Fin n → Real | x ⬝ᵥ b i ≤ β i}) =
        {x : Fin n → Real | ∀ i, x ⬝ᵥ b i ≤ β i} := by
    ext x
    simp
  simpa [hset] using (convex_iInter_family (n:=n)
    (C:=fun i => {x : Fin n → Real | x ⬝ᵥ b i ≤ β i}) hC)

/-- Definition 2.1.2. A set is a polyhedral convex set if it can be expressed as the
intersection of finitely many closed half-spaces in `Real^n`. -/
def IsPolyhedralConvexSet (n : Nat) (C : Set (Fin n → Real)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Fin n → Real) (β : ι → Real),
    C = ⋂ i, closedHalfSpaceLE n (b i) (β i)

/-- Definition 2.2.10. A vector sum `λ₁ x₁ + ⋯ + λₘ xₘ` is called a convex combination of
`x₁, ..., xₘ` if `λ i ≥ 0` for all `i` and `λ₁ + ⋯ + λₘ = 1`. -/
def IsConvexCombination (n m : Nat) (x : Fin m → Fin n → Real) (y : Fin n → Real) : Prop :=
  ∃ w : Fin m → Real, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧ y = ∑ i, w i • x i

/-- A convex set contains all finite convex combinations of its elements. -/
lemma convex_mem_of_isConvexCombination (n : Nat) (C : Set (Fin n → Real)) :
    Convex Real C →
      ∀ m (x : Fin m → Fin n → Real) (y : Fin n → Real),
        (∀ i, x i ∈ C) →
        IsConvexCombination n m x y →
        y ∈ C := by
  intro hC m x y hx hy
  rcases hy with ⟨w, hw_nonneg, hw_sum, rfl⟩
  have hw_nonneg' : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ w i := by
    intro i hi
    exact hw_nonneg i
  have hx' : ∀ i ∈ (Finset.univ : Finset (Fin m)), x i ∈ C := by
    intro i hi
    exact hx i
  have hw_sum' : ∑ i ∈ (Finset.univ : Finset (Fin m)), w i = (1 : Real) := by
    simpa using hw_sum
  simpa using
    (Convex.sum_mem (s:=C) (t:=Finset.univ) (w:=w) (z:=x) hC hw_nonneg' hw_sum' hx')

/-- A two-point convex combination is an `IsConvexCombination`. -/
lemma isConvexCombination_two (n : Nat) (x y : Fin n → Real) (a b : Real) :
    0 ≤ a → 0 ≤ b → a + b = 1 →
    IsConvexCombination n 2 (fun i : Fin 2 => if i = 0 then x else y) (a • x + b • y) := by
  intro ha hb hab
  refine ⟨fun i : Fin 2 => if i = 0 then a else b, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ha, hb]
  · simpa [Fin.sum_univ_two] using hab
  · simp [Fin.sum_univ_two]

/-- If a set contains all finite convex combinations of its elements, then it is convex. -/
lemma convex_of_contains_convexCombinations (n : Nat) (C : Set (Fin n → Real)) :
    (∀ m (x : Fin m → Fin n → Real) (y : Fin n → Real),
        (∀ i, x i ∈ C) →
        IsConvexCombination n m x y →
        y ∈ C) →
    Convex Real C := by
  intro hcomb x hx y hy a b ha hb hab
  have hx' : ∀ i : Fin 2, (fun i : Fin 2 => if i = 0 then x else y) i ∈ C := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have hcomb' :=
    hcomb 2 (fun i : Fin 2 => if i = 0 then x else y) (a • x + b • y) hx'
  exact hcomb' (isConvexCombination_two n x y a b ha hb hab)

/-- Theorem 2.2. A subset of `Real^n` is convex if and only if it contains all the
convex combinations of its elements. -/
theorem convex_iff_contains_convex_combinations (n : Nat) (C : Set (Fin n → Real)) :
    Convex Real C ↔
      ∀ m (x : Fin m → Fin n → Real) (y : Fin n → Real),
        (∀ i, x i ∈ C) →
        IsConvexCombination n m x y →
        y ∈ C := by
  constructor
  · intro hC
    exact convex_mem_of_isConvexCombination n C hC
  · intro hcomb
    exact convex_of_contains_convexCombinations n C hcomb

/-- Definition 2.3.10. The intersection of all convex sets containing a subset `S ⊆ Real^n`
is called the convex hull of `S` and is denoted by `conv S`. -/
def convexHullIntersection (n : Nat) (S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  ⋂ (C : {C : Set (Fin n → Real) // S ⊆ C ∧ Convex Real C}), C.1

/-- The book's convex hull definition agrees with mathlib's `convexHull`. -/
theorem convexHullIntersection_eq_convexHull (n : Nat) (S : Set (Fin n → Real)) :
    convexHullIntersection n S = convexHull Real S := by
  ext x
  constructor
  · intro hx
    have hx' :
        ∀ C : {C : Set (Fin n → Real) // S ⊆ C ∧ Convex Real C}, x ∈ C.1 := by
      simpa [convexHullIntersection] using hx
    have hx'' : ∀ t, S ⊆ t → Convex Real t → x ∈ t := by
      intro t hst htconv
      exact hx' ⟨t, hst, htconv⟩
    exact (mem_convexHull_iff (𝕜:=Real) (s:=S) (x:=x)).2 hx''
  · intro hx
    have hx' : ∀ t, S ⊆ t → Convex Real t → x ∈ t :=
      (mem_convexHull_iff (𝕜:=Real) (s:=S) (x:=x)).1 hx
    have hx'' :
        ∀ C : {C : Set (Fin n → Real) // S ⊆ C ∧ Convex Real C}, x ∈ C.1 := by
      intro C
      exact hx' C.1 C.2.1 C.2.2
    simpa [convexHullIntersection] using hx''

/-- Convert a `Fintype`-indexed convex combination into a `Fin m`-indexed one. -/
lemma exists_fin_convexCombination_of_exists_fintype (n : Nat) (S : Set (Fin n → Real))
    (y : Fin n → Real) :
    (∃ (ι : Type) (_ : Fintype ι) (w : ι → Real) (z : ι → Fin n → Real),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = y) →
    ∃ m : Nat, ∃ x : Fin m → Fin n → Real,
      (∀ i, x i ∈ S) ∧ IsConvexCombination n m x y := by
  classical
  rintro ⟨ι, _inst, w, z, hw0, hw1, hz, hsum⟩
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, z ∘ e.symm, ?_, ?_⟩
  · intro i
    simpa using hz (e.symm i)
  · refine ⟨fun i => w (e.symm i), ?_, ?_, ?_⟩
    · intro i
      exact hw0 (e.symm i)
    · have hsum : ∑ i, w (e.symm i) = ∑ i, w i := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i))
      simpa [hsum] using hw1
    · have hsum' :
          ∑ i, w (e.symm i) • z (e.symm i) = ∑ i, w i • z i := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i • z i))
      calc
        y = ∑ i, w i • z i := by simpa using hsum.symm
        _ = ∑ i, w (e.symm i) • z (e.symm i) := by simpa using hsum'.symm

/-- Characterize membership in the convex hull via `IsConvexCombination`. -/
lemma mem_convexHull_iff_exists_fin_isConvexCombination (n : Nat) (S : Set (Fin n → Real))
    (y : Fin n → Real) :
    y ∈ convexHull Real S ↔
      ∃ m : Nat, ∃ x : Fin m → Fin n → Real,
        (∀ i, x i ∈ S) ∧ IsConvexCombination n m x y := by
  constructor
  · intro hy
    have h := (mem_convexHull_iff_exists_fintype (R:=Real) (s:=S) (x:=y)).1 hy
    exact exists_fin_convexCombination_of_exists_fintype n S y h
  · rintro ⟨m, x, hxS, hcomb⟩
    rcases hcomb with ⟨w, hw0, hw1, hy⟩
    exact
      mem_convexHull_of_exists_fintype (s:=S) (x:=y) (w:=w) (z:=x)
        hw0 hw1 hxS (by simpa using hy.symm)

/-- Theorem 2.3. For any `S ⊆ Real^n`, `conv S` consists of all the convex combinations
of the elements of `S`. -/
theorem convexHull_eq_setOf_convexCombination (n : Nat) (S : Set (Fin n → Real)) :
    convexHull Real S =
      {y : Fin n → Real |
        ∃ m : Nat, ∃ x : Fin m → Fin n → Real,
          (∀ i, x i ∈ S) ∧ IsConvexCombination n m x y} := by
  ext y
  constructor
  · intro hy
    exact (mem_convexHull_iff_exists_fin_isConvexCombination n S y).1 hy
  · intro hy
    exact (mem_convexHull_iff_exists_fin_isConvexCombination n S y).2 hy

/-- Choose indices witnessing membership in `Set.range`. -/
lemma range_choice_index {n m k : Nat} (b : Fin (m + 1) → Fin n → Real)
    {x : Fin k → Fin n → Real} (hx : ∀ i, x i ∈ Set.range b) :
    ∃ f : Fin k → Fin (m + 1), ∀ i, x i = b (f i) := by
  classical
  refine ⟨fun i => Classical.choose (by simpa using hx i), ?_⟩
  intro i
  have h := Classical.choose_spec (by simpa using hx i)
  simpa using h.symm

/-- Summing weights over fibers preserves nonnegativity and total weight. -/
lemma weights_fiber_sum_eq {k m : Nat} (f : Fin k → Fin (m + 1)) (w : Fin k → Real)
    (hw : ∀ i, 0 ≤ w i) :
    (∀ j, 0 ≤ ∑ i, if f i = j then w i else 0) ∧
      (∑ j, ∑ i, if f i = j then w i else 0) = ∑ i, w i := by
  classical
  have hw0 : ∀ j, 0 ≤ ∑ i, if f i = j then w i else 0 := by
    intro j
    have hnonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (if f i = j then w i else 0) := by
      intro i hi
      by_cases hfj : f i = j
      · simp [hfj, hw i]
      · simp [hfj]
    simpa using (Finset.sum_nonneg hnonneg)
  have hsum : (∑ j, ∑ i, if f i = j then w i else 0) = ∑ i, w i := by
    change (Finset.univ.sum fun j => Finset.univ.sum fun i => if f i = j then w i else 0) =
        Finset.univ.sum fun i => w i
    calc
      Finset.univ.sum (fun j => Finset.univ.sum fun i => if f i = j then w i else 0)
          = Finset.univ.sum (fun i => Finset.univ.sum fun j => if f i = j then w i else 0) := by
            simpa using
              (Finset.sum_comm (s := (Finset.univ : Finset (Fin (m + 1))))
                (t := (Finset.univ : Finset (Fin k)))
                (f := fun j i => if f i = j then w i else 0))
      _ = Finset.univ.sum (fun i => w i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp
  exact ⟨hw0, hsum⟩

/-- Summing weights over fibers preserves the weighted sum. -/
lemma weighted_sum_fiber_eq {n m k : Nat} (b : Fin (m + 1) → Fin n → Real)
    (f : Fin k → Fin (m + 1)) (w : Fin k → Real) (x : Fin k → Fin n → Real)
    (hx : ∀ i, x i = b (f i)) :
    ∑ j, (∑ i, if f i = j then w i else 0) • b j = ∑ i, w i • x i := by
  classical
  have hsmul :
      (∑ j, (∑ i, if f i = j then w i else 0) • b j) =
        ∑ j, ∑ i, (if f i = j then w i else 0) • b j := by
    change (Finset.univ.sum fun j =>
      (Finset.univ.sum fun i => if f i = j then w i else 0) • b j) =
        Finset.univ.sum fun j =>
          Finset.univ.sum fun i => (if f i = j then w i else 0) • b j
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa using
      (Finset.sum_smul (s := Finset.univ)
        (f := fun i => if f i = j then w i else 0) (x := b j))
  calc
    ∑ j, (∑ i, if f i = j then w i else 0) • b j
        = ∑ j, ∑ i, (if f i = j then w i else 0) • b j := hsmul
    _ = ∑ i, ∑ j, (if f i = j then w i else 0) • b j := by
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset (Fin (m + 1))))
              (t := (Finset.univ : Finset (Fin k)))
              (f := fun j i => (if f i = j then w i else 0) • b j))
    _ = ∑ i, w i • b (f i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hrewrite :
              (∑ j, (if f i = j then w i else 0) • b j) =
                ∑ j, (if f i = j then w i • b j else 0) := by
            change (Finset.univ.sum fun j => (if f i = j then w i else 0) • b j) =
                Finset.univ.sum fun j => if f i = j then w i • b j else 0
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hfj : f i = j
            · simp [hfj]
            · simp [hfj]
          have hsum_ite :
              (∑ j, if f i = j then w i • b j else 0) = w i • b (f i) := by
            simp
          calc
            ∑ j, (if f i = j then w i else 0) • b j
                = ∑ j, if f i = j then w i • b j else 0 := hrewrite
            _ = w i • b (f i) := hsum_ite
    _ = ∑ i, w i • x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hx i]

/-- Corollary 2.3.1. The convex hull of a finite subset `{b_0, ..., b_m}` of `Real^n`
consists of all vectors of the form `λ_0 b_0 + ⋯ + λ_m b_m` with `λ_i ≥ 0` and
`λ_0 + ⋯ + λ_m = 1`. -/
theorem convexHull_range_eq_setOf_weighted_sum (n m : Nat)
    (b : Fin (m + 1) → Fin n → Real) :
    convexHull Real (Set.range b) =
      {y : Fin n → Real |
        ∃ w : Fin (m + 1) → Real, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧
          y = ∑ i, w i • b i} := by
  ext y
  constructor
  · intro hy
    have hy' :
        ∃ k : Nat, ∃ x : Fin k → Fin n → Real,
          (∀ i, x i ∈ Set.range b) ∧ IsConvexCombination n k x y := by
      simpa [convexHull_eq_setOf_convexCombination] using hy
    rcases hy' with ⟨k, x, hx, hcomb⟩
    rcases hcomb with ⟨w, hw0, hw1, hyw⟩
    rcases range_choice_index (b:=b) (x:=x) hx with ⟨f, hf⟩
    let w' : Fin (m + 1) → Real := fun j => ∑ i, if f i = j then w i else 0
    have hweights := weights_fiber_sum_eq (f:=f) (w:=w) hw0
    refine ⟨w', ?_, ?_, ?_⟩
    · simpa [w'] using hweights.1
    · calc
        ∑ j, w' j = ∑ i, w i := by simpa [w'] using hweights.2
        _ = 1 := hw1
    · have hsum :
          ∑ j, w' j • b j = ∑ i, w i • x i := by
        simpa [w'] using
          (weighted_sum_fiber_eq (b:=b) (f:=f) (w:=w) (x:=x) (hx:=hf))
      calc
        y = ∑ i, w i • x i := by simpa using hyw
        _ = ∑ j, w' j • b j := by simpa using hsum.symm
  · rintro ⟨w, hw0, hw1, hy⟩
    have hy' :
        ∃ k : Nat, ∃ x : Fin k → Fin n → Real,
          (∀ i, x i ∈ Set.range b) ∧ IsConvexCombination n k x y := by
      refine ⟨m + 1, b, ?_, ?_⟩
      · intro i
        exact ⟨i, rfl⟩
      · exact ⟨w, hw0, hw1, by simpa using hy⟩
    simpa [convexHull_eq_setOf_convexCombination] using hy'

/-- Definition 2.3.11. A set which is the convex hull of finitely many points is called
a polytope. -/
def IsPolytope (n : Nat) (P : Set (Fin n → Real)) : Prop :=
  ∃ S : Set (Fin n → Real), S.Finite ∧ P = convexHull Real S

/-- Definition 2.3.12. If `{b_0, b_1, ..., b_m}` is affinely independent, its convex hull is
called an `m`-dimensional simplex and `b_0, ..., b_m` are the vertices of the simplex. -/
def IsSimplex (n m : Nat) (P : Set (Fin n → Real)) : Prop :=
  ∃ b : Fin (m + 1) → Fin n → Real, AffineIndependent Real b ∧
    P = convexHull Real (Set.range b)

/-- Definition 2.3.13. For an `m`-dimensional simplex with vertices `b_0, ..., b_m`,
the point `λ_0 b_0 + ⋯ + λ_m b_m` with `λ_0 = ⋯ = λ_m = 1 / (m + 1)` is called the
midpoint or barycenter of the simplex. -/
noncomputable def simplexBarycenter (n m : Nat) (b : Fin (m + 1) → Fin n → Real) :
    Fin n → Real :=
  (Finset.univ).centroid (k:=Real) b

/-- Definition 2.4.10. The dimension of a convex set `C` is the dimension of the affine
hull of `C`. -/
noncomputable def convexSetDim (n : Nat) (C : Set (Fin n → Real)) : Nat :=
  Module.finrank Real (affineSpan Real C).direction

/-- Any simplex contained in `C` has dimension at most `convexSetDim n C`. -/
lemma simplex_dim_le_convexSetDim (n : Nat) (C : Set (Fin n → Real)) :
    ∀ m P, P ⊆ C → IsSimplex n m P → m ≤ convexSetDim n C := by
  classical
  intro m P hPC hsimplex
  rcases hsimplex with ⟨b, hb_ind, rfl⟩
  have hsubset' : Set.range b ⊆ convexHull Real (Set.range b) := by
    simpa using (subset_convexHull (𝕜:=Real) (s:=Set.range b))
  have hsubset : Set.range b ⊆ C := by
    intro x hx
    exact hPC (hsubset' hx)
  have hcard_le :
      m + 1 ≤ Module.finrank Real (vectorSpan Real (Set.range b)) + 1 := by
    simpa using (AffineIndependent.card_le_finrank_succ (k:=Real) (p:=b) hb_ind)
  have hle' : m ≤ Module.finrank Real (vectorSpan Real (Set.range b)) := by
    exact Nat.le_of_succ_le_succ hcard_le
  have hspan_le : vectorSpan Real (Set.range b) ≤ vectorSpan Real C :=
    vectorSpan_mono (k:=Real) hsubset
  have hle : m ≤ Module.finrank Real (vectorSpan Real C) :=
    le_trans hle' (Submodule.finrank_mono hspan_le)
  have hle'': m ≤ Module.finrank Real (affineSpan Real C).direction := by
    rw [direction_affineSpan]
    exact hle
  simpa [convexSetDim] using hle''

/-- Construct a simplex from a finite affinely independent subset of a convex set. -/
lemma simplex_of_affineIndependent_finite (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) {t : Set (Fin n → Real)} (htC : t ⊆ C)
    (htind : AffineIndependent Real ((↑) : t → Fin n → Real)) {m : Nat} [Fintype t]
    (hcard : Fintype.card t = m + 1) :
    ∃ P ⊆ C, IsSimplex n m P := by
  classical
  have hcard' : Fintype.card (Fin (m + 1)) = Fintype.card t := by
    simpa using hcard.symm
  let e : Fin (m + 1) ≃ t := Fintype.equivOfCardEq hcard'
  let b : Fin (m + 1) → Fin n → Real := fun i => (e i : Fin n → Real)
  refine ⟨convexHull Real (Set.range b), ?_, ?_⟩
  · have hrange : Set.range b ⊆ C := by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact htC (e i).property
    exact convexHull_min hrange hC
  · refine ⟨b, ?_, rfl⟩
    have hb_ind : AffineIndependent Real b := by
      simpa [b, Function.comp] using
        (AffineIndependent.comp_embedding (p:=((↑) : t → Fin n → Real))
          e.toEmbedding htind)
    exact hb_ind

/-- A nonempty convex set contains a simplex of dimension `convexSetDim`. -/
lemma exists_simplex_dim_convexSetDim (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) (hCne : C.Nonempty) :
    ∃ P ⊆ C, IsSimplex n (convexSetDim n C) P := by
  classical
  obtain ⟨t, htC, htspan, htind⟩ :=
    exists_affineIndependent (k:=Real) (V:=Fin n → Real) (s:=C)
  have htfin : t.Finite := by
    simpa using
      (finite_set_of_fin_dim_affineIndependent (k:=Real) (s:=t)
        (f:=((↑) : t → Fin n → Real)) htind)
  letI : Fintype t := htfin.fintype
  have ht_nonempty : t.Nonempty := by
    have hspan_nonempty : (affineSpan Real t : Set (Fin n → Real)).Nonempty := by
      have hCspan : (affineSpan Real C : Set (Fin n → Real)).Nonempty := by
        simpa using (affineSpan_nonempty (k:=Real) (s:=C)).2 hCne
      simpa [htspan] using hCspan
    exact (affineSpan_nonempty (k:=Real) (s:=t)).1 hspan_nonempty
  haveI : Nonempty t := by
    rcases ht_nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  have hrange : Set.range (fun x : t => (x : Fin n → Real)) = t := by
    ext x
    constructor
    · rintro ⟨x', rfl⟩
      exact x'.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard_le_range :
      Fintype.card t ≤
        Module.finrank Real (vectorSpan Real (Set.range fun x : t => (x : Fin n → Real))) + 1 := by
    simpa using
      (AffineIndependent.card_le_finrank_succ (k:=Real)
        (p:=fun x : t => (x : Fin n → Real)) htind)
  have hcard_le :
      Fintype.card t ≤ Module.finrank Real (vectorSpan Real t) + 1 := by
    calc
      Fintype.card t ≤
          Module.finrank Real
              (vectorSpan Real (Set.range fun x : t => (x : Fin n → Real))) + 1 :=
        hcard_le_range
      _ = Module.finrank Real (vectorSpan Real t) + 1 := by
        rw [hrange]
  have hle_card_range :
      Module.finrank Real (vectorSpan Real (Set.range fun x : t => (x : Fin n → Real))) + 1 ≤
        Fintype.card t := by
    simpa using
      (finrank_vectorSpan_range_add_one_le (k:=Real)
        (p:=fun x : t => (x : Fin n → Real)))
  have hle_card :
      Module.finrank Real (vectorSpan Real t) + 1 ≤ Fintype.card t := by
    calc
      Module.finrank Real (vectorSpan Real t) + 1 =
          Module.finrank Real
              (vectorSpan Real (Set.range fun x : t => (x : Fin n → Real))) + 1 := by
        rw [hrange]
      _ ≤ Fintype.card t := hle_card_range
  have hcard_eq : Fintype.card t = Module.finrank Real (vectorSpan Real t) + 1 :=
    le_antisymm hcard_le hle_card
  have hcard : Fintype.card t = convexSetDim n C + 1 := by
    have hdir : (affineSpan Real C).direction = (affineSpan Real t).direction := by
      simpa using congrArg AffineSubspace.direction htspan.symm
    have hdim : convexSetDim n C = Module.finrank Real (vectorSpan Real t) := by
      calc
        convexSetDim n C = Module.finrank Real (affineSpan Real C).direction := rfl
        _ = Module.finrank Real (affineSpan Real t).direction := by
          rw [hdir]
        _ = Module.finrank Real (vectorSpan Real t) := by
          rw [direction_affineSpan]
    calc
      Fintype.card t = Module.finrank Real (vectorSpan Real t) + 1 := hcard_eq
      _ = convexSetDim n C + 1 := by simp [hdim]
  exact simplex_of_affineIndependent_finite n C hC htC htind hcard

/-- Theorem 2.4. The dimension of a convex set `C` is the maximum of the dimensions of the
simplices contained in `C`. -/
theorem convexSetDim_isGreatest_simplex_dim (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) (hCne : C.Nonempty) :
    IsGreatest {m : Nat | ∃ P : Set (Fin n → Real), P ⊆ C ∧ IsSimplex n m P}
      (convexSetDim n C) := by
  refine ⟨?_, ?_⟩
  · rcases exists_simplex_dim_convexSetDim n C hC hCne with ⟨P, hPC, hsimplex⟩
    exact ⟨P, hPC, hsimplex⟩
  · intro m hm
    rcases hm with ⟨P, hPC, hsimplex⟩
    exact simplex_dim_le_convexSetDim n C m P hPC hsimplex

/-- Definition 2.5.9. A subset `K` of `Real^n` is a cone if it is closed under positive
scalar multiplication, i.e. `λ • x ∈ K` when `x ∈ K` and `λ > 0`. -/
def IsConeSet (n : Nat) (K : Set (Fin n → Real)) : Prop :=
  ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K

/-- Definition 2.5.10. A convex cone is a cone which is also a convex set. -/
def IsConvexCone (n : Nat) (K : Set (Fin n → Real)) : Prop :=
  IsConeSet n K ∧ Convex Real K

/-- The intersection of cone sets is a cone. -/
lemma IsConeSet_iInter_family {ι : Sort*} (n : Nat) (K : ι → Set (Fin n → Real))
    (hK : ∀ i, IsConeSet n (K i)) : IsConeSet n (⋂ i, K i) := by
  intro x hx t ht
  have hx' : ∀ i, x ∈ K i := by
    simpa using hx
  have htx : ∀ i, t • x ∈ K i := fun i => hK i x (hx' i) t ht
  simpa using htx

/-- Theorem 2.5. The intersection of an arbitrary collection of convex cones is a convex cone. -/
theorem convexCone_iInter_family {ι : Sort*} (n : Nat) (K : ι → Set (Fin n → Real))
    (hK : ∀ i, IsConvexCone n (K i)) : IsConvexCone n (⋂ i, K i) := by
  refine ⟨?_, ?_⟩
  · exact IsConeSet_iInter_family (n:=n) (K:=K) (fun i => (hK i).1)
  · exact convex_iInter_family (n:=n) (C:=K) (hC:=fun i => (hK i).2)

/-- A closed half-space through the origin is a cone. -/
lemma IsConeSet_dotProduct_le_zero (n : Nat) (b : Fin n → Real) :
    IsConeSet n {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  intro x hx t ht
  have hsmul : t • (x ⬝ᵥ b) ≤ 0 :=
    smul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) hx
  simpa using hsmul

/-- A closed half-space through the origin is a convex cone. -/
lemma IsConvexCone_dotProduct_le_zero (n : Nat) (b : Fin n → Real) :
    IsConvexCone n {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  refine ⟨IsConeSet_dotProduct_le_zero n b, ?_⟩
  simpa using (convex_dotProduct_le n b (0 : Real))

/-- Intersections of dot-product half-spaces encode pointwise inequalities. -/
lemma iInter_setOf_dotProduct_le_zero {ι : Sort*} (n : Nat) (b : ι → Fin n → Real) :
    (⋂ i, {x : Fin n → Real | x ⬝ᵥ b i ≤ 0}) =
      {x : Fin n → Real | ∀ i, x ⬝ᵥ b i ≤ 0} := by
  ext x
  simp

/-- Corollary 2.5.1. Let `b i ∈ Real^n` for `i ∈ I`, where `I` is an arbitrary index set.
Then `K = {x ∈ Real^n | ⟪x, b i⟫ ≤ 0, i ∈ I}` is a convex cone. -/
theorem convexCone_of_dotProduct_le_zero {ι : Sort*} (n : Nat) (b : ι → Fin n → Real) :
    IsConvexCone n {x : Fin n → Real | ∀ i, x ⬝ᵥ b i ≤ 0} := by
  have hK :
      ∀ i, IsConvexCone n {x : Fin n → Real | x ⬝ᵥ b i ≤ 0} := fun i =>
    IsConvexCone_dotProduct_le_zero n (b i)
  simpa [iInter_setOf_dotProduct_le_zero (n:=n) (b:=b)] using
    (convexCone_iInter_family (n:=n)
      (K:=fun i => {x : Fin n → Real | x ⬝ᵥ b i ≤ 0}) hK)

/-- Definition 2.5.11. The non-negative orthant of `Real^n` is the set of
vectors `x = (xi_1, ..., xi_n)` with `xi_i ≥ 0` for all coordinates. -/
def nonNegativeOrthant (n : Nat) : Set (Fin n → Real) :=
  {x : Fin n → Real | ∀ i, 0 ≤ x i}

/-- Definition 2.5.12. The positive orthant of `Real^n` is the set of vectors
`x = (xi_1, ..., xi_n)` with `xi_i > 0` for all coordinates. -/
def positiveOrthant (n : Nat) : Set (Fin n → Real) :=
  {x : Fin n → Real | ∀ i, 0 < x i}

/-- Definition 2.5.13. It is customary to write `x ≥ x'` if `x - x'` belongs to the
non-negative orthant, i.e. if `ξ_j ≥ ξ'_j` for `j = 1, ..., n`. -/
def coordwiseGE (n : Nat) (x x' : Fin n → Real) : Prop :=
  x - x' ∈ nonNegativeOrthant n

/-- The book's coordinatewise order agrees with the pointwise order on `Fin n → Real`. -/
theorem coordwiseGE_iff_le (n : Nat) (x x' : Fin n → Real) :
    coordwiseGE n x x' ↔ x' ≤ x := by
  constructor
  · intro hx
    have hx' : ∀ i, 0 ≤ (x - x') i := by
      simpa [coordwiseGE, nonNegativeOrthant] using hx
    intro i
    have hx'' : 0 ≤ x i - x' i := by
      simpa using hx' i
    exact (sub_nonneg).1 hx''
  · intro hx
    have hx' : ∀ i, 0 ≤ (x - x') i := by
      intro i
      have : 0 ≤ x i - x' i := (sub_nonneg).2 (hx i)
      simpa using this
    simpa [coordwiseGE, nonNegativeOrthant] using hx'

/-- A convex cone is closed under addition. -/
lemma isConvexCone_add_closed (n : Nat) (K : Set (Fin n → Real)) :
    IsConvexCone n K → ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
  intro hK x hx y hy
  rcases hK with ⟨hcone, hconvex⟩
  have hmid : midpoint Real x y ∈ K := Convex.midpoint_mem hconvex hx hy
  have htwo : (2 : Real) • midpoint Real x y ∈ K :=
    hcone (midpoint Real x y) hmid 2 (by norm_num)
  have hsum : x + y = (2 : Real) • midpoint Real x y := by
    calc
      x + y = midpoint Real x y + midpoint Real x y := by
        simp
      _ = (2 : Real) • midpoint Real x y := by
        simpa using (two_smul Real (midpoint Real x y)).symm
  simpa [hsum] using htwo

/-- Positive scalar closure and add-closure give two-point positive combinations. -/
lemma pos_combo_mem_of_add_closed_and_pos_smul_closed (n : Nat) (K : Set (Fin n → Real))
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K) :
    ∀ x ∈ K, ∀ y ∈ K, ∀ a b : Real, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ K := by
  intro x hx y hy a b ha hb hab
  have hx' : a • x ∈ K := hsmul x hx a ha
  have hy' : b • y ∈ K := hsmul y hy b hb
  exact hadd (a • x) hx' (b • y) hy'

/-- Add-closure and positive scalar closure imply convexity. -/
lemma convex_of_add_closed_and_pos_smul_closed (n : Nat) (K : Set (Fin n → Real))
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K) :
    Convex Real K := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  exact
    pos_combo_mem_of_add_closed_and_pos_smul_closed n K hadd hsmul x hx y hy a b ha hb hab

/-- Theorem 2.6. A subset of `Real^n` is a convex cone if and only if it is closed under
addition and positive scalar multiplication. -/
theorem isConvexCone_iff_add_closed_and_pos_smul_closed (n : Nat) (K : Set (Fin n → Real)) :
    IsConvexCone n K ↔
      (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧
        (∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K) := by
  constructor
  · intro hK
    refine ⟨?_, ?_⟩
    · exact isConvexCone_add_closed n K hK
    · intro x hx t ht
      exact hK.1 x hx t ht
  · rintro ⟨hadd, hsmul⟩
    refine ⟨?_, ?_⟩
    · exact hsmul
    · exact convex_of_add_closed_and_pos_smul_closed n K hadd hsmul

/-- Finite positive linear combinations from add-closure and positive scalar closure. -/
lemma pos_linear_combo_mem_of_add_closed_and_pos_smul_closed (n : Nat) (K : Set (Fin n → Real))
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K) :
    ∀ m : Nat, ∀ x : Fin (m + 1) → Fin n → Real, ∀ w : Fin (m + 1) → Real,
      (∀ i, x i ∈ K) → (∀ i, 0 < w i) → (∑ i, w i • x i) ∈ K := by
  intro m
  induction m with
  | zero =>
      intro x w hx hw
      have hx0 : x 0 ∈ K := hx 0
      have hw0 : 0 < w 0 := hw 0
      simpa [Fin.sum_univ_one] using hsmul (x 0) hx0 (w 0) hw0
  | succ m ih =>
      intro x w hx hw
      have hhead : w 0 • x 0 ∈ K := hsmul (x 0) (hx 0) (w 0) (hw 0)
      have htail :
          (∑ i : Fin (m + 1), w (Fin.succ i) • x (Fin.succ i)) ∈ K := by
        apply ih
        · intro i
          exact hx (Fin.succ i)
        · intro i
          exact hw (Fin.succ i)
      have hsum :
          (∑ i : Fin (m + 2), w i • x i) =
            w 0 • x 0 + ∑ i : Fin (m + 1), w (Fin.succ i) • x (Fin.succ i) := by
        simp [Fin.sum_univ_succ]
      simpa [hsum] using hadd (w 0 • x 0) hhead
        (∑ i : Fin (m + 1), w (Fin.succ i) • x (Fin.succ i)) htail

/-- Positive scaling follows from closure under positive linear combinations. -/
lemma pos_smul_closed_of_pos_linear_combinations (n : Nat) (K : Set (Fin n → Real))
    (hcomb :
      ∀ m : Nat, ∀ x : Fin (m + 1) → Fin n → Real, ∀ w : Fin (m + 1) → Real,
        (∀ i, x i ∈ K) → (∀ i, 0 < w i) → (∑ i, w i • x i) ∈ K) :
    ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K := by
  intro x hx t ht
  have hx' : ∀ i : Fin 1, (fun _ : Fin 1 => x) i ∈ K := by
    intro i
    simpa using hx
  have hw' : ∀ i : Fin 1, 0 < (fun _ : Fin 1 => t) i := by
    intro i
    simpa using ht
  have hcomb' := hcomb 0 (fun _ : Fin 1 => x) (fun _ : Fin 1 => t) hx' hw'
  simpa [Fin.sum_univ_one] using hcomb'

/-- Add-closure follows from closure under positive linear combinations. -/
lemma add_closed_of_pos_linear_combinations (n : Nat) (K : Set (Fin n → Real))
    (hcomb :
      ∀ m : Nat, ∀ x : Fin (m + 1) → Fin n → Real, ∀ w : Fin (m + 1) → Real,
        (∀ i, x i ∈ K) → (∀ i, 0 < w i) → (∑ i, w i • x i) ∈ K) :
    ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
  intro x hx y hy
  have hx' : ∀ i : Fin 2, (fun i : Fin 2 => if i = 0 then x else y) i ∈ K := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have hw' : ∀ i : Fin 2, 0 < (fun _ : Fin 2 => (1 : Real)) i := by
    intro i
    simp
  have hcomb' :=
    hcomb 1 (fun i : Fin 2 => if i = 0 then x else y) (fun _ : Fin 2 => (1 : Real)) hx' hw'
  simpa [Fin.sum_univ_two] using hcomb'

/-- Corollary 2.6.1. A subset of `Real^n` is a convex cone if and only if it contains all the
positive linear combinations of its elements, i.e. sums `λ₁ x₁ + ⋯ + λ_m x_m` with `λ_i > 0`. -/
theorem isConvexCone_iff_contains_pos_linear_combinations (n : Nat) (K : Set (Fin n → Real)) :
    IsConvexCone n K ↔
      ∀ m : Nat, ∀ x : Fin (m + 1) → Fin n → Real, ∀ w : Fin (m + 1) → Real,
        (∀ i, x i ∈ K) →
        (∀ i, 0 < w i) →
        (∑ i, w i • x i) ∈ K := by
  constructor
  · intro hK
    rcases (isConvexCone_iff_add_closed_and_pos_smul_closed n K).1 hK with ⟨hadd, hsmul⟩
    exact pos_linear_combo_mem_of_add_closed_and_pos_smul_closed n K hadd hsmul
  · intro hcomb
    have hsmul :
        ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K :=
      pos_smul_closed_of_pos_linear_combinations n K hcomb
    have hadd :
        ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K :=
      add_closed_of_pos_linear_combinations n K hcomb
    exact (isConvexCone_iff_add_closed_and_pos_smul_closed n K).2 ⟨hadd, hsmul⟩

/-- A point is a positive linear combination of elements of a set. -/
def IsPosLinearCombination (n : Nat) (S : Set (Fin n → Real)) (y : Fin n → Real) : Prop :=
  ∃ m : Nat, ∃ x : Fin (m + 1) → Fin n → Real, ∃ w : Fin (m + 1) → Real,
    (∀ i, x i ∈ S) ∧ (∀ i, 0 < w i) ∧ y = ∑ i, w i • x i

/-- Positive linear combinations are closed under positive scaling. -/
lemma isPosLinearCombination_smul (n : Nat) (S : Set (Fin n → Real))
    {y : Fin n → Real} (hy : IsPosLinearCombination n S y)
    {t : Real} (ht : 0 < t) :
    IsPosLinearCombination n S (t • y) := by
  rcases hy with ⟨m, x, w, hx, hw, rfl⟩
  refine ⟨m, x, (fun i => t * w i), hx, ?_, ?_⟩
  · intro i
    exact mul_pos ht (hw i)
  · calc
      t • (∑ i, w i • x i) = ∑ i, t • (w i • x i) := by
        simpa using
          (Finset.smul_sum (s:=Finset.univ) (f:=fun i => w i • x i) (r:=t))
      _ = ∑ i, (t * w i) • x i := by
        simp [smul_smul]

/-- The sum of two positive linear combinations is a positive linear combination. -/
lemma isPosLinearCombination_add (n : Nat) (S : Set (Fin n → Real))
    {y₁ y₂ : Fin n → Real} (hy₁ : IsPosLinearCombination n S y₁)
    (hy₂ : IsPosLinearCombination n S y₂) :
    IsPosLinearCombination n S (y₁ + y₂) := by
  rcases hy₁ with ⟨m1, x1, w1, hx1, hw1, rfl⟩
  rcases hy₂ with ⟨m2, x2, w2, hx2, hw2, rfl⟩
  set m' : Nat := m1 + m2 + 1
  have hm : m' + 1 = (m1 + 1) + (m2 + 1) := by
    simp [m', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  let e : Fin (m' + 1) ≃ Fin ((m1 + 1) + (m2 + 1)) := finCongr hm
  let x' : Fin (m' + 1) → Fin n → Real := fun i => (Fin.append x1 x2) (e i)
  let w' : Fin (m' + 1) → Real := fun i => (Fin.append w1 w2) (e i)
  have hx' : ∀ i, x' i ∈ S := by
    have hx'' : ∀ i : Fin ((m1 + 1) + (m2 + 1)), (Fin.append x1 x2) i ∈ S := by
      intro i
      refine (Fin.addCases (m:=m1 + 1) (n:=m2 + 1) ?_ ?_ i)
      · intro i
        simpa using hx1 i
      · intro i
        simpa using hx2 i
    intro i
    simpa [x'] using hx'' (e i)
  have hw' : ∀ i, 0 < w' i := by
    have hw'' : ∀ i : Fin ((m1 + 1) + (m2 + 1)), 0 < (Fin.append w1 w2) i := by
      intro i
      refine (Fin.addCases (m:=m1 + 1) (n:=m2 + 1) ?_ ?_ i)
      · intro i
        simpa using hw1 i
      · intro i
        simpa using hw2 i
    intro i
    simpa [w'] using hw'' (e i)
  have hsum'' :
      (∑ i : Fin ((m1 + 1) + (m2 + 1)), (Fin.append w1 w2) i • (Fin.append x1 x2) i) =
        (∑ i : Fin (m1 + 1), w1 i • x1 i) + (∑ i : Fin (m2 + 1), w2 i • x2 i) := by
    simpa using
      (Fin.sum_univ_add (f:=fun i => (Fin.append w1 w2) i • (Fin.append x1 x2) i)
        (a:=m1 + 1) (b:=m2 + 1))
  have hsum_cast :
      (∑ i : Fin (m' + 1), w' i • x' i) =
        ∑ i : Fin ((m1 + 1) + (m2 + 1)), (Fin.append w1 w2) i • (Fin.append x1 x2) i := by
    simpa [x', w'] using
      (Equiv.sum_comp e (fun i => (Fin.append w1 w2) i • (Fin.append x1 x2) i))
  have hsum' :
      (∑ i : Fin (m' + 1), w' i • x' i) =
        (∑ i : Fin (m1 + 1), w1 i • x1 i) + (∑ i : Fin (m2 + 1), w2 i • x2 i) := by
    exact hsum_cast.trans hsum''
  refine ⟨m', x', w', hx', hw', ?_⟩
  exact hsum'.symm

/-- Corollary 2.6.2. Let `S ⊆ Real^n`, and let `K` be the set of all positive linear
combinations of elements of `S`. Then `K` is the smallest convex cone containing `S`. -/
theorem positiveLinearCombinationCone_isSmallest (n : Nat) (S : Set (Fin n → Real)) :
    let K : Set (Fin n → Real) :=
      {y : Fin n → Real |
        ∃ m : Nat, ∃ x : Fin (m + 1) → Fin n → Real, ∃ w : Fin (m + 1) → Real,
          (∀ i, x i ∈ S) ∧ (∀ i, 0 < w i) ∧ y = ∑ i, w i • x i}
    ; IsConvexCone n K ∧ S ⊆ K ∧
      ∀ K' : Set (Fin n → Real), IsConvexCone n K' → S ⊆ K' → K ⊆ K' := by
  let K : Set (Fin n → Real) :=
    {y : Fin n → Real |
      ∃ m : Nat, ∃ x : Fin (m + 1) → Fin n → Real, ∃ w : Fin (m + 1) → Real,
        (∀ i, x i ∈ S) ∧ (∀ i, 0 < w i) ∧ y = ∑ i, w i • x i}
  have hK : IsConvexCone n K := by
    have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
      intro x hx y hy
      have hx' : IsPosLinearCombination n S x := by
        simpa [K, IsPosLinearCombination] using hx
      have hy' : IsPosLinearCombination n S y := by
        simpa [K, IsPosLinearCombination] using hy
      have hxy : IsPosLinearCombination n S (x + y) :=
        isPosLinearCombination_add n S hx' hy'
      simpa [K, IsPosLinearCombination] using hxy
    have hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K := by
      intro x hx t ht
      have hx' : IsPosLinearCombination n S x := by
        simpa [K, IsPosLinearCombination] using hx
      have htx : IsPosLinearCombination n S (t • x) :=
        isPosLinearCombination_smul n S hx' ht
      simpa [K, IsPosLinearCombination] using htx
    exact (isConvexCone_iff_add_closed_and_pos_smul_closed n K).2 ⟨hadd, hsmul⟩
  have hS : S ⊆ K := by
    intro x hx
    refine ⟨0, (fun _ : Fin 1 => x), (fun _ : Fin 1 => (1 : Real)), ?_, ?_, ?_⟩
    · intro i
      simpa using hx
    · intro i
      simp
    · simp
  have hmin :
      ∀ K' : Set (Fin n → Real), IsConvexCone n K' → S ⊆ K' → K ⊆ K' := by
    intro K' hK' hSK' y hy
    rcases hy with ⟨m, x, w, hxS, hwpos, rfl⟩
    have hcomb := (isConvexCone_iff_contains_pos_linear_combinations n K').1 hK'
    have hxK' : ∀ i, x i ∈ K' := fun i => hSK' (hxS i)
    exact hcomb m x w hxK' hwpos
  dsimp [K]
  exact ⟨hK, hS, hmin⟩

/-- Corollary 2.6.3. Let `C` be a convex set, and let
`K = {λ • x | λ > 0, x ∈ C}`. Then `K` is the smallest convex cone which includes `C`. -/
theorem positiveScalarCone_isSmallest (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) :
    let K : Set (Fin n → Real) :=
      {y : Fin n → Real | ∃ x ∈ C, ∃ t : Real, 0 < t ∧ y = t • x}
    ; IsConvexCone n K ∧ C ⊆ K ∧
      ∀ K' : Set (Fin n → Real), IsConvexCone n K' → C ⊆ K' → K ⊆ K' := by
  let K : Set (Fin n → Real) :=
    {y : Fin n → Real | ∃ x ∈ C, ∃ t : Real, 0 < t ∧ y = t • x}
  have hK : IsConvexCone n K := by
    have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
      intro x hx y hy
      rcases hx with ⟨x1, hx1C, t1, ht1, rfl⟩
      rcases hy with ⟨x2, hx2C, t2, ht2, rfl⟩
      have ht : 0 < t1 + t2 := add_pos ht1 ht2
      have ht0 : t1 + t2 ≠ 0 := ne_of_gt ht
      let a : Real := t1 / (t1 + t2)
      let b : Real := t2 / (t1 + t2)
      have ha : 0 ≤ a := by
        exact div_nonneg (le_of_lt ht1) (le_of_lt ht)
      have hb : 0 ≤ b := by
        exact div_nonneg (le_of_lt ht2) (le_of_lt ht)
      have hab : a + b = 1 := by
        calc
          a + b = (t1 + t2) / (t1 + t2) := by
            simpa [a, b] using (add_div t1 t2 (t1 + t2)).symm
          _ = 1 := by simp [ht0]
      have hxC : a • x1 + b • x2 ∈ C := hC hx1C hx2C ha hb hab
      refine ⟨a • x1 + b • x2, hxC, t1 + t2, ht, ?_⟩
      have h1 : (t1 + t2) * a = t1 := by
        simpa [a] using (mul_div_cancel₀ (a:=t1) (b:=t1 + t2) ht0)
      have h2 : (t1 + t2) * b = t2 := by
        simpa [b] using (mul_div_cancel₀ (a:=t2) (b:=t1 + t2) ht0)
      calc
        t1 • x1 + t2 • x2
            = ((t1 + t2) * a) • x1 + ((t1 + t2) * b) • x2 := by
                simp [h1, h2]
        _ = (t1 + t2) • (a • x1 + b • x2) := by
              simp [smul_add, smul_smul]
    have hsmul : ∀ x ∈ K, ∀ t : Real, 0 < t → t • x ∈ K := by
      intro x hx t ht
      rcases hx with ⟨x1, hx1C, t1, ht1, rfl⟩
      refine ⟨x1, hx1C, t * t1, mul_pos ht ht1, ?_⟩
      simp [smul_smul]
    exact (isConvexCone_iff_add_closed_and_pos_smul_closed n K).2 ⟨hadd, hsmul⟩
  have hCsub : C ⊆ K := by
    intro x hx
    refine ⟨x, hx, 1, by norm_num, ?_⟩
    simp
  have hmin :
      ∀ K' : Set (Fin n → Real), IsConvexCone n K' → C ⊆ K' → K ⊆ K' := by
    intro K' hK' hCK' y hy
    rcases hy with ⟨x, hxC, t, ht, rfl⟩
    exact hK'.1 x (hCK' hxC) t ht
  simpa [K] using ⟨hK, hCsub, hmin⟩

/-- Definition 2.6.10. The convex cone obtained by adjoining the origin to the cone in
Corollary 2.6.2 (equivalently, Corollary 2.6.3) is called the convex cone generated by `S`
(or by a convex set `C`) and is denoted `cone S`. -/
def convexConeGenerated (n : Nat) (S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  Set.insert (0 : Fin n → Real) ((ConvexCone.hull Real S) : Set (Fin n → Real))

/-- The nonnegative ray generated by a set. -/
def rayNonneg (n : Nat) (S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  {y : Fin n → Real | ∃ x ∈ S, ∃ t : Real, 0 ≤ t ∧ y = t • x}

/-- Elements of the nonnegative ray lie in the generated cone. -/
lemma rayNonneg_subset_convexConeGenerated (n : Nat) (S : Set (Fin n → Real)) :
    rayNonneg n S ⊆ convexConeGenerated n S := by
  intro y hy
  rcases hy with ⟨x, hxS, t, ht, rfl⟩
  by_cases ht0 : t = 0
  · subst ht0
    have h0 :
        (0 : Fin n → Real) ∈ Set.insert 0 (ConvexCone.hull Real S : Set (Fin n → Real)) :=
      (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [convexConeGenerated] using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht (by symm; exact ht0)
    have hxHull : x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) :=
      ConvexCone.subset_hull hxS
    have htxHull : t • x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) :=
      (ConvexCone.hull Real S).smul_mem htpos hxHull
    have : t • x = 0 ∨ t • x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := Or.inr htxHull
    simpa [convexConeGenerated, Set.mem_insert_iff, -smul_eq_zero] using this

/-- The generated cone is convex. -/
lemma convexConeGenerated_convex (n : Nat) (S : Set (Fin n → Real)) :
    Convex Real (convexConeGenerated n S) := by
  have hsmul :
      ∀ x ∈ convexConeGenerated n S, ∀ t : Real, 0 < t → t • x ∈ convexConeGenerated n S := by
    intro x hx t ht
    have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := by
      simpa [convexConeGenerated] using hx
    cases hx' with
    | inl hx0 =>
        subst hx0
        have h0 :
            (0 : Fin n → Real) ∈ Set.insert 0 (ConvexCone.hull Real S : Set (Fin n → Real)) :=
          (Set.mem_insert_iff).2 (Or.inl rfl)
        simpa [convexConeGenerated] using h0
    | inr hxHull =>
        have htxHull : t • x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) :=
          (ConvexCone.hull Real S).smul_mem ht hxHull
        have : t • x = 0 ∨ t • x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := Or.inr htxHull
        simpa [convexConeGenerated, Set.mem_insert_iff, -smul_eq_zero] using this
  have hadd :
      ∀ x ∈ convexConeGenerated n S, ∀ y ∈ convexConeGenerated n S,
        x + y ∈ convexConeGenerated n S := by
    intro x hx y hy
    have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := by
      simpa [convexConeGenerated] using hx
    have hy' : y = 0 ∨ y ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := by
      simpa [convexConeGenerated] using hy
    cases hx' with
    | inl hx0 =>
        subst hx0
        simpa [convexConeGenerated, Set.mem_insert_iff] using hy
    | inr hxHull =>
        cases hy' with
        | inl hy0 =>
            subst hy0
            have : x = 0 ∨ x ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := Or.inr hxHull
            simpa [convexConeGenerated, Set.mem_insert_iff] using this
        | inr hyHull =>
            have hsum : x + y ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) :=
              (ConvexCone.hull Real S).add_mem hxHull hyHull
            have : x + y = 0 ∨ x + y ∈ (ConvexCone.hull Real S : Set (Fin n → Real)) := Or.inr hsum
            simpa [convexConeGenerated, Set.mem_insert_iff] using this
  exact convex_of_add_closed_and_pos_smul_closed n (convexConeGenerated n S) hadd hsmul


end Section02
end Chap01
