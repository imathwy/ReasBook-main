/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section03_part1

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- Lifting a point into the cone over `C` preserves relative interior membership. -/
lemma lift_mem_ri_cone_iff (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => 1)
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
      fun x => append y0 x
    ∀ x, x ∈ euclideanRelativeInterior n C ↔ lift x ∈ euclideanRelativeInterior (1 + n) K := by
  classical
  intro coords first tail S K y0 append lift x
  have hriK :
      euclideanRelativeInterior (1 + n) K =
        {v | 0 < first v ∧ tail v ∈ (first v) • euclideanRelativeInterior n C} := by
    simpa [coords, first, tail, S, K] using
      (euclideanRelativeInterior_convexConeGenerated_eq (n := n) (C := C) hC hCne)
  have hfirst_tail :
      first (lift x) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y0) 0 ∧
        tail (lift x) = x := by
    simpa [lift, coords, first, tail, append] using
      (first_tail_append (n := n) (y := y0) (z := x))
  have hy0 : (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y0) 0 = 1 := by
    simp [y0]
  have hfirst : first (lift x) = 1 := by
    simpa [hy0] using hfirst_tail.1
  have htail : tail (lift x) = x := hfirst_tail.2
  constructor
  · intro hx
    have hx' :
        0 < first (lift x) ∧
          tail (lift x) ∈ (first (lift x)) • euclideanRelativeInterior n C := by
      refine ⟨?_, ?_⟩
      · simp [hfirst]
      · refine ⟨x, hx, ?_⟩
        simp [hfirst, htail]
    have : lift x ∈ {v | 0 < first v ∧ tail v ∈ (first v) • euclideanRelativeInterior n C} := hx'
    simpa [hriK] using this
  · intro hx
    have hx' :
        0 < first (lift x) ∧
          tail (lift x) ∈ (first (lift x)) • euclideanRelativeInterior n C := by
      simpa [hriK] using hx
    rcases hx' with ⟨_, hmem⟩
    rcases (Set.mem_smul_set.mp hmem) with ⟨y, hy, hyEq⟩
    have hy' : y = x := by
      have : (1 : Real) • y = tail (lift x) := by
        simpa [hfirst] using hyEq
      simpa [htail] using this
    simpa [hy'] using hy

/-- A finite Minkowski sum of convex sets in Euclidean space is convex. -/
lemma convex_sum_finset_set_euclidean {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Set (EuclideanSpace Real (Fin n))) (hA : ∀ i ∈ s, Convex Real (A i)) :
    Convex Real (s.sum A) := by
  classical
  revert hA
  refine Finset.induction_on s ?h0 ?hstep
  · intro hA
    simpa using (convex_zero (𝕜 := Real) (E := EuclideanSpace Real (Fin n)))
  · intro a s ha hs hAas
    have hconv_a : Convex Real (A a) := hAas a (by simp [ha])
    have hconv_s : Convex Real (s.sum A) :=
      hs (by intro i hi; exact hAas i (by simp [hi]))
    have hconv_add : Convex Real (A a + s.sum A) :=
      hconv_a.add hconv_s
    simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using hconv_add

/-- Choose indices witnessing membership in a union of sets (Euclidean space). -/
lemma choose_index_family_of_mem_iUnion_euclidean {n : ℕ} {ι : Type*} {I : Type*}
    {C : I → Set (EuclideanSpace Real (Fin n))}
    {x : ι → EuclideanSpace Real (Fin n)} (hx : ∀ i, x i ∈ ⋃ j, C j) :
    ∃ f : ι → I, ∀ i, x i ∈ C (f i) := by
  classical
  refine ⟨fun i => Classical.choose (Set.mem_iUnion.1 (hx i)), ?_⟩
  intro i
  have h := Classical.choose_spec (Set.mem_iUnion.1 (hx i))
  simpa using h

/-- Relative interior of a finite Minkowski sum of convex sets. -/
lemma ri_sum_cones_eq_sum_ri (n m : Nat)
    (K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hK : ∀ i, Convex Real (K i)) :
    euclideanRelativeInterior n (∑ i, K i) =
      ∑ i, euclideanRelativeInterior n (K i) := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hconv0 : Convex Real (K 0) := hK 0
      have hconv_rest :
          Convex Real (∑ i : Fin (Nat.succ m), K (Fin.succ i)) := by
        have hA :
            ∀ i ∈ (Finset.univ : Finset (Fin (Nat.succ m))),
              Convex Real (K (Fin.succ i)) := by
          intro i _hi
          exact hK (Fin.succ i)
        simpa using
          (convex_sum_finset_set_euclidean (n := n)
            (s := (Finset.univ : Finset (Fin (Nat.succ m))))
            (A := fun i => K (Fin.succ i)) hA)
      have hri_add :
          euclideanRelativeInterior n
              (K 0 + ∑ i : Fin (Nat.succ m), K (Fin.succ i)) =
            euclideanRelativeInterior n (K 0) +
              euclideanRelativeInterior n (∑ i : Fin (Nat.succ m), K (Fin.succ i)) := by
        exact
          (euclideanRelativeInterior_add_eq_and_closure_add_superset (n := n)
              (C1 := K 0)
              (C2 := ∑ i : Fin (Nat.succ m), K (Fin.succ i))
              hconv0 hconv_rest).1
      have ih' :
          euclideanRelativeInterior n (∑ i : Fin (Nat.succ m), K (Fin.succ i)) =
            ∑ i : Fin (Nat.succ m), euclideanRelativeInterior n (K (Fin.succ i)) := by
        apply ih
        intro i
        exact hK (Fin.succ i)
      calc
        euclideanRelativeInterior n (∑ i, K i) =
            euclideanRelativeInterior n
              (K 0 + ∑ i : Fin (Nat.succ m), K (Fin.succ i)) := by
          simp [Fin.sum_univ_succ]
        _ =
            euclideanRelativeInterior n (K 0) +
              euclideanRelativeInterior n (∑ i : Fin (Nat.succ m), K (Fin.succ i)) := hri_add
        _ =
            euclideanRelativeInterior n (K 0) +
              ∑ i : Fin (Nat.succ m), euclideanRelativeInterior n (K (Fin.succ i)) := by
          simp [ih']
        _ = ∑ i : Fin (Nat.succ (Nat.succ m)), euclideanRelativeInterior n (K i) := by
          simp [Fin.sum_univ_succ]

/-- A vector in `R^{n+1}` is determined by its first and tail coordinates. -/
lemma eq_of_first_tail_eq (n : Nat) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    ∀ u v, first u = first v → tail u = tail v → u = v := by
  classical
  intro coords first tail u v hfirst htail
  apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).injective
  let e : Fin (1 + n) ≃ Fin (n + 1) :=
    (Fin.castOrderIso (Nat.add_comm 1 n)).toEquiv
  have hcoords :
      ∀ i : Fin (n + 1), coords u (e.symm i) = coords v (e.symm i) := by
    intro i
    refine Fin.cases ?h0 ?hrest i
    · have h0 : e.symm (0 : Fin (n + 1)) = 0 := by
        simp [e]
      simpa [h0, first] using hfirst
    · intro j
      have htail' :
          (fun i => coords u (Fin.natAdd 1 i)) =
            (fun i => coords v (Fin.natAdd 1 i)) := by
        have := congrArg (fun z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z) htail
        simpa [tail] using this
      have := congrArg (fun f => f j) htail'
      have hsucc : e.symm (Fin.succ j) = Fin.natAdd 1 j := by
        apply Fin.ext
        simp [e, Fin.natAdd, Nat.add_comm]
      simpa [hsucc] using this
  funext i
  have := hcoords (e i)
  simpa using this

/-- The `first` coordinate scales linearly under scalar multiplication. -/
lemma first_smul (n : Nat) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    ∀ (a : Real) v, first (a • v) = a * first v := by
  classical
  intro coords first a v
  simp [first, coords]

/-- The `tail` map scales linearly under scalar multiplication. -/
lemma tail_smul (n : Nat) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    ∀ (a : Real) v, tail (a • v) = a • tail v := by
  classical
  intro coords tail a v
  apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
  funext j
  simp [tail, coords]

/-- The lift map preserves distances. -/
lemma dist_lift_eq (n : Nat) :
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => 1)
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
      fun x => append y0 x
    ∀ x y, dist (lift x) (lift y) = dist x y := by
  classical
  intro y0 append lift x y
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
        (fun i => coords v (Fin.natAdd 1 i))
  have hfirst_tail_x :
      first (lift x) = 1 ∧ tail (lift x) = x := by
    simpa [coords, first, tail, append, lift, y0] using
      (first_tail_append (n := n) (y := y0) (z := x))
  have hfirst_tail_y :
      first (lift y) = 1 ∧ tail (lift y) = y := by
    simpa [coords, first, tail, append, lift, y0] using
      (first_tail_append (n := n) (y := y0) (z := y))
  have hcoord0_x : (lift x) 0 = 1 := by
    simpa [first, coords] using hfirst_tail_x.1
  have hcoord0_y : (lift y) 0 = 1 := by
    simpa [first, coords] using hfirst_tail_y.1
  have htail_coord_x : ∀ i, (lift x) (Fin.natAdd 1 i) = x i := by
    intro i
    have := congrArg (fun z => z i) hfirst_tail_x.2
    simpa [tail, coords] using this
  have htail_coord_y : ∀ i, (lift y) (Fin.natAdd 1 i) = y i := by
    intro i
    have := congrArg (fun z => z i) hfirst_tail_y.2
    simpa [tail, coords] using this
  have hsum :
      (∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) =
        dist ((lift x) 0) ((lift y) 0) ^ 2 +
          ∑ i : Fin n, dist ((lift x) (Fin.natAdd 1 i)) ((lift y) (Fin.natAdd 1 i)) ^ 2 := by
    classical
    -- Reindex `Fin (1+n)` to `Fin (n+1)` to use `Fin.sum_univ_succ`.
    let e : Fin (1 + n) ≃ Fin (n + 1) :=
      (Fin.castOrderIso (Nat.add_comm 1 n)).toEquiv
    let f' : Fin (n + 1) → Real :=
      fun i => dist ((lift x) (e.symm i)) ((lift y) (e.symm i)) ^ 2
    have hsum' :
        (∑ i : Fin (n + 1), f' i) =
          f' 0 + ∑ i : Fin n, f' (Fin.succ i) := by
      simpa using (Fin.sum_univ_succ (f := f') (n := n))
    have hcast0 : e.symm (0 : Fin (n + 1)) = 0 := by
      simp [e]
    have hcast_succ : ∀ i, e.symm (Fin.succ i) = Fin.natAdd 1 i := by
      intro i
      apply Fin.ext
      simp [e, Fin.natAdd, Nat.add_comm]
    have hsum_cast :
        (∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) =
          ∑ i : Fin (n + 1), f' i := by
      classical
      refine
        Fintype.sum_equiv e (fun i => dist ((lift x) i) ((lift y) i) ^ 2) f' ?_
      intro i
      simp [f']
    calc
      (∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) =
          ∑ i : Fin (n + 1), f' i := hsum_cast
      _ = f' 0 + ∑ i : Fin n, f' (Fin.succ i) := hsum'
      _ = dist ((lift x) 0) ((lift y) 0) ^ 2 +
            ∑ i : Fin n,
              dist ((lift x) (Fin.natAdd 1 i)) ((lift y) (Fin.natAdd 1 i)) ^ 2 := by
        simp [f', hcast0, hcast_succ]
  have hdist_lift :
      dist (lift x) (lift y) =
        √(∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) := by
    simpa using (EuclideanSpace.dist_eq (x := lift x) (y := lift y))
  have hdist_xy :
      dist x y = √(∑ i : Fin n, dist (x i) (y i) ^ 2) := by
    simpa using (EuclideanSpace.dist_eq (x := x) (y := y))
  have hsum' :
      (∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) =
        ∑ i : Fin n, dist (x i) (y i) ^ 2 := by
    have hzero : dist ((lift x) 0) ((lift y) 0) ^ 2 = 0 := by
      have : dist ((lift x) 0) ((lift y) 0) = 0 := by
        simp [hcoord0_x, hcoord0_y]
      simp [this]
    calc
      (∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) =
          dist ((lift x) 0) ((lift y) 0) ^ 2 +
            ∑ i : Fin n, dist ((lift x) (Fin.natAdd 1 i)) ((lift y) (Fin.natAdd 1 i)) ^ 2 := hsum
      _ = ∑ i : Fin n, dist ((lift x) (Fin.natAdd 1 i)) ((lift y) (Fin.natAdd 1 i)) ^ 2 := by
        simp [hzero]
      _ = ∑ i : Fin n, dist (x i) (y i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [htail_coord_x i, htail_coord_y i]
  calc
    dist (lift x) (lift y) =
        √(∑ i : Fin (1 + n), dist ((lift x) i) ((lift y) i) ^ 2) := hdist_lift
    _ = √(∑ i : Fin n, dist (x i) (y i) ^ 2) := by simp [hsum']
    _ = dist x y := by simp [hdist_xy]

/-- Weighted sums of lifts with total weight `1` collapse to a single lift. -/
lemma sum_smul_lift_eq_lift_sum (n m : Nat)
    (w : Fin (Nat.succ m) → Real)
    (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n))
    (hsum : Finset.univ.sum (fun i => w i) = 1) :
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => 1)
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
      fun x => append y0 x
    Finset.univ.sum (fun i => w i • lift (x_i i)) =
      lift (Finset.univ.sum (fun i => w i • x_i i)) := by
  classical
  intro y0 append lift
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
        (fun i => coords v (Fin.natAdd 1 i))
  have hfirst_lift : ∀ i, first (lift (x_i i)) = 1 := by
    intro i
    simpa [coords, first, tail, append, lift, y0] using
      (first_tail_append (n := n) (y := y0) (z := x_i i)).1
  have htail_lift : ∀ i, tail (lift (x_i i)) = x_i i := by
    intro i
    have h :
        tail (append y0 (x_i i)) = x_i i := by
      exact (first_tail_append (n := n) (y := y0) (z := x_i i)).2
    simp [lift, h]
  have hfirst_sum :
      first (Finset.univ.sum (fun i => w i • lift (x_i i))) =
        Finset.univ.sum (fun i => w i) := by
    have hfirst_sum' :
        first (Finset.univ.sum (fun i => w i • lift (x_i i))) =
          Finset.univ.sum (fun i => first (w i • lift (x_i i))) := by
      simp [first, coords]
    calc
      first (Finset.univ.sum (fun i => w i • lift (x_i i))) =
          Finset.univ.sum (fun i => first (w i • lift (x_i i))) := hfirst_sum'
      _ = Finset.univ.sum (fun i => w i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hfirst_smul :
              first (w i • lift (x_i i)) = w i * first (lift (x_i i)) := by
            simp [first, coords]
          simpa [hfirst_lift i] using hfirst_smul
  have htail_sum :
      tail (Finset.univ.sum (fun i => w i • lift (x_i i))) =
        Finset.univ.sum (fun i => w i • x_i i) := by
    have htail_sum' :
        tail (Finset.univ.sum (fun i => w i • lift (x_i i))) =
          Finset.univ.sum (fun i => tail (w i • lift (x_i i))) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have htail_smul : ∀ i, tail (w i • lift (x_i i)) = w i • x_i i := by
      intro i
      have htail_smul' :
          tail (w i • lift (x_i i)) = w i • tail (lift (x_i i)) := by
        simpa [coords, tail] using
          (tail_smul (n := n) (a := w i) (v := lift (x_i i)))
      simpa [htail_lift i] using htail_smul'
    calc
      tail (Finset.univ.sum (fun i => w i • lift (x_i i))) =
          Finset.univ.sum (fun i => tail (w i • lift (x_i i))) := htail_sum'
      _ = Finset.univ.sum (fun i => w i • x_i i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [htail_smul i]
  have hfirst_tail_sum :
      first (lift (Finset.univ.sum (fun i => w i • x_i i))) = 1 ∧
        tail (lift (Finset.univ.sum (fun i => w i • x_i i))) =
          Finset.univ.sum (fun i => w i • x_i i) := by
    simpa [coords, first, tail, append, lift, y0] using
      (first_tail_append (n := n) (y := y0)
        (z := Finset.univ.sum (fun i => w i • x_i i)))
  have hfirst_eq :
      first (Finset.univ.sum (fun i => w i • lift (x_i i))) =
        first (lift (Finset.univ.sum (fun i => w i • x_i i))) := by
    simpa [hsum, hfirst_tail_sum.1] using hfirst_sum
  have htail_eq :
      tail (Finset.univ.sum (fun i => w i • lift (x_i i))) =
        tail (lift (Finset.univ.sum (fun i => w i • x_i i))) := by
    simp [htail_sum, hfirst_tail_sum.2]
  simpa [coords, first, tail] using
    (eq_of_first_tail_eq (n := n)
      (u := Finset.univ.sum (fun i => w i • lift (x_i i)))
      (v := lift (Finset.univ.sum (fun i => w i • x_i i))) hfirst_eq htail_eq)

/-- A norm bound for the perturbation of weights in a weighted sum. -/
lemma weighted_sum_perturb_bound (n m : Nat)
    (w : Fin (Nat.succ m) → Real)
    (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n))
    {δ : Real} (hδ : 0 ≤ δ) :
    let c : Real := 1 + (Nat.succ m : Real) * δ
    let w' : Fin (Nat.succ m) → Real := fun i => (w i + δ) / c
    ‖Finset.univ.sum (fun i => w' i • x_i i) -
        Finset.univ.sum (fun i => w i • x_i i)‖ ≤
      (δ / c) *
        (‖Finset.univ.sum (fun i => x_i i)‖ +
          (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖) := by
  classical
  intro c w'
  have hcpos : 0 < c := by
    have hm : 0 ≤ (Nat.succ m : Real) := by exact_mod_cast (Nat.zero_le _)
    have hnonneg : 0 ≤ (Nat.succ m : Real) * δ := mul_nonneg hm hδ
    linarith
  have hsum :
      Finset.univ.sum (fun i => w' i • x_i i) =
        (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
          (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) := by
    have hterm :
        ∀ i, w' i • x_i i = (w i * c⁻¹) • x_i i + (δ * c⁻¹) • x_i i := by
      intro i
      calc
        w' i • x_i i = ((w i + δ) * c⁻¹) • x_i i := by
          simp [w', div_eq_mul_inv]
        _ = (w i * c⁻¹ + δ * c⁻¹) • x_i i := by
          simp [add_mul]
        _ = (w i * c⁻¹) • x_i i + (δ * c⁻¹) • x_i i := by
          simpa using (add_smul (w i * c⁻¹) (δ * c⁻¹) (x_i i))
    calc
      Finset.univ.sum (fun i => w' i • x_i i) =
          Finset.univ.sum (fun i => (w i * c⁻¹) • x_i i + (δ * c⁻¹) • x_i i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hterm i]
      _ = Finset.univ.sum (fun i => (w i * c⁻¹) • x_i i) +
            Finset.univ.sum (fun i => (δ * c⁻¹) • x_i i) := by
        simp [Finset.sum_add_distrib]
      _ = (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) := by
        have hsum_w :
            Finset.univ.sum (fun i => (w i * c⁻¹) • x_i i) =
              (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) := by
          have :
              (fun i => (w i * c⁻¹) • x_i i) =
                (fun i => (c⁻¹) • (w i • x_i i)) := by
            funext i
            simp [smul_smul, mul_comm]
          simp [this, Finset.smul_sum]
        have hsum_x :
            Finset.univ.sum (fun i => (δ * c⁻¹) • x_i i) =
              (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) := by
          simp [Finset.smul_sum]
        simp [hsum_w, hsum_x]
  have hdiff :
      Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i) =
        (δ * c⁻¹) •
          (Finset.univ.sum (fun i => x_i i) -
            (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)) := by
    have hcoeff : (c⁻¹ - 1) = -((Nat.succ m : Real) * (δ * c⁻¹)) := by
      have : c - 1 = (Nat.succ m : Real) * δ := by
        simp [c, add_comm, mul_comm]
      have h1 : (c⁻¹ - 1) = (1 - c) / c := by
        field_simp [hcpos.ne']
      calc
        (c⁻¹ - 1) = (1 - c) / c := h1
        _ = -((c - 1) / c) := by ring
        _ = -((Nat.succ m : Real) * δ / c) := by simp [this]
        _ = -((Nat.succ m : Real) * (δ * c⁻¹)) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hsub :
        (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            -Finset.univ.sum (fun i => w i • x_i i) =
          (c⁻¹ - 1) • Finset.univ.sum (fun i => w i • x_i i) := by
      calc
        (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            -Finset.univ.sum (fun i => w i • x_i i) =
          (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            (-1 : Real) • Finset.univ.sum (fun i => w i • x_i i) := by
          simp
        _ = (c⁻¹ + -1) • Finset.univ.sum (fun i => w i • x_i i) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_smul (c⁻¹) (-1) (Finset.univ.sum (fun i => w i • x_i i))).symm
        _ = (c⁻¹ - 1) • Finset.univ.sum (fun i => w i • x_i i) := by
          simp [sub_eq_add_neg]
    calc
      Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i) =
          (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) -
            Finset.univ.sum (fun i => w i • x_i i) := by
        simp [hsum]
      _ = (c⁻¹) • Finset.univ.sum (fun i => w i • x_i i) +
            -Finset.univ.sum (fun i => w i • x_i i) +
            (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) := by
        abel
      _ = (c⁻¹ - 1) • Finset.univ.sum (fun i => w i • x_i i) +
            (δ * c⁻¹) • Finset.univ.sum (fun i => x_i i) := by
        simp [hsub]
      _ = (δ * c⁻¹) •
            (Finset.univ.sum (fun i => x_i i) -
              (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)) := by
        simp [hcoeff, sub_eq_add_neg, add_comm, smul_add, smul_smul, mul_comm]
  have hnorm :
      ‖Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i)‖ ≤
        (δ * c⁻¹) *
          (‖Finset.univ.sum (fun i => x_i i)‖ +
            (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖) := by
    have hnonneg : 0 ≤ δ * c⁻¹ := by
      have hcpos' : 0 < c := hcpos
      exact mul_nonneg hδ (le_of_lt (inv_pos.mpr hcpos'))
    calc
      ‖Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i)‖ =
          ‖(δ * c⁻¹) •
              (Finset.univ.sum (fun i => x_i i) -
                (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i))‖ := by
        simp [hdiff]
      _ = (δ * c⁻¹) *
            ‖Finset.univ.sum (fun i => x_i i) -
              (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖ := by
        have habs : ‖(δ * c⁻¹)‖ = δ * c⁻¹ := by
          simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg)
        calc
          ‖(δ * c⁻¹) •
              (Finset.univ.sum (fun i => x_i i) -
                (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i))‖ =
              ‖(δ * c⁻¹)‖ *
                ‖Finset.univ.sum (fun i => x_i i) -
                  (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖ := by
            simpa using
              (norm_smul (δ * c⁻¹)
                (Finset.univ.sum (fun i => x_i i) -
                  (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)))
          _ = (δ * c⁻¹) *
                ‖Finset.univ.sum (fun i => x_i i) -
                  (Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖ := by
            simp [habs]
      _ ≤ (δ * c⁻¹) *
            (‖Finset.univ.sum (fun i => x_i i)‖ +
              ‖(Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖) := by
        gcongr
        simpa using
          (norm_sub_le (Finset.univ.sum (fun i => x_i i))
            ((Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)))
      _ = (δ * c⁻¹) *
            (‖Finset.univ.sum (fun i => x_i i)‖ +
              (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖) := by
        have hnorm_smul :
            ‖(Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖ =
              (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖ := by
          have hnonneg' : 0 ≤ (Nat.succ m : Real) := by
            exact_mod_cast (Nat.zero_le _)
          have hnorm' : ‖(Nat.succ m : Real)‖ = (Nat.succ m : Real) := by
            simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg')
          calc
            ‖(Nat.succ m : Real) • Finset.univ.sum (fun i => w i • x_i i)‖ =
                ‖(Nat.succ m : Real)‖ * ‖Finset.univ.sum (fun i => w i • x_i i)‖ := by
              simpa using
                (norm_smul (Nat.succ m : Real) (Finset.univ.sum (fun i => w i • x_i i)))
            _ = (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖ := by
              rw [hnorm']
        rw [hnorm_smul]
  have hswap' : (δ * c⁻¹) = δ / c := by
    simp [div_eq_mul_inv]
  simpa [hswap'] using hnorm

/-- Membership in the sum of the relative interiors of the lifted cones gives positive weights. -/
lemma mem_sum_ri_cones_iff_weights (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, (C i).Nonempty) (hCconv : ∀ i, Convex Real (C i)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, first v = 1 →
      (v ∈ ∑ i, euclideanRelativeInterior (1 + n) (K i) ↔
        ∃ (w : Fin (Nat.succ m) → Real) (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
          (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
            (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
            tail v = Finset.univ.sum (fun i => w i • x_i i)) := by
  classical
  intro coords first tail S K v hvfirst
  have hriK :
      ∀ i,
        euclideanRelativeInterior (1 + n) (K i) =
          {v | 0 < first v ∧ tail v ∈ (first v) • euclideanRelativeInterior n (C i)} := by
    intro i
    simpa [coords, first, tail, S, K] using
      (euclideanRelativeInterior_convexConeGenerated_eq (n := n) (C := C i)
        (hCconv i) (hCne i))
  constructor
  · intro hv
    rcases
        (Set.mem_finset_sum
            (t := (Finset.univ : Finset (Fin (Nat.succ m))))
            (f := fun i => euclideanRelativeInterior (1 + n) (K i)) v).1 hv with
      ⟨z, hzmem, rfl⟩
    have hzmem' : ∀ i, z i ∈ euclideanRelativeInterior (1 + n) (K i) := by
      intro i
      exact hzmem (i := i) (by simp)
    let w : Fin (Nat.succ m) → Real := fun i => first (z i)
    have hwpos : ∀ i, 0 < w i := by
      intro i
      have hz' :
          0 < first (z i) ∧
            tail (z i) ∈ (first (z i)) • euclideanRelativeInterior n (C i) := by
        simpa [hriK i] using hzmem' i
      simpa [w] using hz'.1
    have hx_i' :
        ∀ i,
          ∃ x, x ∈ euclideanRelativeInterior n (C i) ∧ tail (z i) = w i • x := by
      intro i
      have hz' :
          0 < first (z i) ∧
            tail (z i) ∈ (first (z i)) • euclideanRelativeInterior n (C i) := by
        simpa [hriK i] using hzmem' i
      rcases (Set.mem_smul_set.mp hz'.2) with ⟨x, hxri, hxeq⟩
      refine ⟨x, hxri, ?_⟩
      simpa [w] using hxeq.symm
    choose x_i hx_i_mem hx_i_eq using hx_i'
    have hfirst_sum :
        first (Finset.univ.sum (fun i => z i)) =
          Finset.univ.sum (fun i => first (z i)) := by
      simp [first, coords]
    have hsum : Finset.univ.sum (fun i => w i) = 1 := by
      have hfirst_eq :
          first (Finset.univ.sum (fun i => z i)) = Finset.univ.sum (fun i => w i) := by
        simpa [w] using hfirst_sum
      calc
        Finset.univ.sum (fun i => w i) =
            first (Finset.univ.sum (fun i => z i)) := by
          simpa using hfirst_eq.symm
        _ = 1 := hvfirst
    have htail_sum :
        tail (Finset.univ.sum (fun i => z i)) =
          Finset.univ.sum (fun i => tail (z i)) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have htail_eq :
        tail (Finset.univ.sum (fun i => z i)) =
          Finset.univ.sum (fun i => w i • x_i i) := by
      calc
        tail (Finset.univ.sum (fun i => z i)) =
            Finset.univ.sum (fun i => tail (z i)) := htail_sum
        _ = Finset.univ.sum (fun i => w i • x_i i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hx_i_eq i]
    refine ⟨w, x_i, hwpos, hsum, hx_i_mem, ?_⟩
    simpa using htail_eq
  · intro hx
    rcases hx with ⟨w, x_i, hwpos, hsum, hx_i_mem, hxsum⟩
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => 1)
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
      fun x => append y0 x
    have hfirst_tail_lift :
        ∀ x, first (lift x) = 1 ∧ tail (lift x) = x := by
      intro x
      simpa [coords, first, tail, append, lift, y0] using
        (first_tail_append (n := n) (y := y0) (z := x))
    let z : Fin (Nat.succ m) → EuclideanSpace Real (Fin (1 + n)) :=
      fun i => w i • lift (x_i i)
    have hzmem : ∀ i, z i ∈ euclideanRelativeInterior (1 + n) (K i) := by
      intro i
      have hfirst_lift : first (lift (x_i i)) = 1 := (hfirst_tail_lift (x_i i)).1
      have htail_lift : tail (lift (x_i i)) = x_i i := (hfirst_tail_lift (x_i i)).2
      have hfirst_z : first (z i) = w i := by
        have h := (first_smul (n := n) (a := w i) (v := lift (x_i i)))
        simpa [z, coords, first, hfirst_lift] using h
      have htail_z : tail (z i) = w i • x_i i := by
        have htail_smul :
            tail (w i • lift (x_i i)) = w i • tail (lift (x_i i)) := by
          simpa [coords, tail] using
            (tail_smul (n := n) (a := w i) (v := lift (x_i i)))
        simpa [z, htail_lift] using htail_smul
      have hmem :
          0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • euclideanRelativeInterior n (C i) := by
        refine ⟨?_, ?_⟩
        · simpa [hfirst_z] using hwpos i
        · refine ⟨x_i i, hx_i_mem i, ?_⟩
          simp [hfirst_z, htail_z]
      simpa [hriK i] using hmem
    have hsum_z :
        Finset.univ.sum (fun i => z i) =
          lift (Finset.univ.sum (fun i => w i • x_i i)) := by
      simpa [z, y0, append, lift] using
        (sum_smul_lift_eq_lift_sum (n := n) (m := m) (w := w) (x_i := x_i) hsum)
    have hfirst_tail_sum :
        first (lift (Finset.univ.sum (fun i => w i • x_i i))) = 1 ∧
          tail (lift (Finset.univ.sum (fun i => w i • x_i i))) =
            Finset.univ.sum (fun i => w i • x_i i) := by
      simpa [coords, first, tail, append, lift, y0] using
        (first_tail_append (n := n) (y := y0)
          (z := Finset.univ.sum (fun i => w i • x_i i)))
    have hv_eq :
        v = lift (Finset.univ.sum (fun i => w i • x_i i)) := by
      have hfirst_eq :
          first v = first (lift (Finset.univ.sum (fun i => w i • x_i i))) := by
        simp [hvfirst, hfirst_tail_sum.1]
      have htail_eq :
          tail v = tail (lift (Finset.univ.sum (fun i => w i • x_i i))) := by
        simpa [hfirst_tail_sum.2] using hxsum
      simpa [coords, first, tail] using
        (eq_of_first_tail_eq (n := n) (u := v)
          (v := lift (Finset.univ.sum (fun i => w i • x_i i))) hfirst_eq htail_eq)
    have hv_eq' : v = Finset.univ.sum (fun i => z i) := by
      simpa [hsum_z.symm] using hv_eq
    refine
      (Set.mem_finset_sum
          (t := (Finset.univ : Finset (Fin (Nat.succ m))))
          (f := fun i => euclideanRelativeInterior (1 + n) (K i))
          (a := v)).2 ?_
    refine ⟨z, ?_, hv_eq'.symm⟩
    intro i hi
    exact hzmem i

/-- A point in the convex hull of a finite union of convex sets admits one point per set. -/
lemma convexHull_iUnion_exists_weights_points (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, (C i).Nonempty) (hCconv : ∀ i, Convex Real (C i)) :
    ∀ x ∈ convexHull Real (⋃ i, C i),
      ∃ (w : Fin (Nat.succ m) → Real) (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
        (∀ i, 0 ≤ w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
          (∀ i, x_i i ∈ C i) ∧ x = Finset.univ.sum (fun i => w i • x_i i) := by
  classical
  intro x hx
  rcases (mem_convexHull_iff_exists_fintype (R := Real)
      (s := ⋃ i, C i) (x := x)).1 hx with
    ⟨ι, _hfin, w, y, hw0, hw1, hyUnion, hxsum⟩
  classical
  obtain ⟨f, hyC⟩ := choose_index_family_of_mem_iUnion_euclidean (C := C) (x := y) hyUnion
  choose x0 hx0 using hCne
  let t : Fin (Nat.succ m) → Finset ι :=
    fun j => (Finset.univ : Finset ι).filter (fun i => f i = j)
  let wsum : Fin (Nat.succ m) → Real := fun j => Finset.sum (t j) (fun i => w i)
  let x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n) :=
    fun j =>
      if h : wsum j = 0 then x0 j
      else (1 / wsum j) • (Finset.sum (t j) (fun i => w i • y i))
  have hw_nonneg : ∀ j, 0 ≤ wsum j := by
    intro j
    exact Finset.sum_nonneg (by intro i hi; exact hw0 i)
  have hx_i_mem : ∀ j, x_i j ∈ C j := by
    intro j
    by_cases hzero : wsum j = 0
    · simp [x_i, hzero, hx0]
    · have hpos : 0 < wsum j := by
        exact lt_of_le_of_ne (hw_nonneg j) (Ne.symm hzero)
      have hweights_nonneg :
          ∀ i ∈ t j, 0 ≤ (w i / wsum j) := by
        intro i hi
        exact div_nonneg (hw0 i) (le_of_lt hpos)
      have hweights_sum :
          Finset.sum (t j) (fun i => w i / wsum j) = 1 := by
        have hsum :
            Finset.sum (t j) (fun i => w i / wsum j) =
              (1 / wsum j) * Finset.sum (t j) (fun i => w i) := by
          calc
            Finset.sum (t j) (fun i => w i / wsum j) =
                Finset.sum (t j) (fun i => w i * (wsum j)⁻¹) := by
              simp [div_eq_mul_inv]
            _ = (Finset.sum (t j) (fun i => w i)) * (wsum j)⁻¹ := by
              simpa using
                (Finset.sum_mul (s := t j) (f := fun i => w i) (a := (wsum j)⁻¹)).symm
            _ = (1 / wsum j) * Finset.sum (t j) (fun i => w i) := by
              simp [div_eq_mul_inv, mul_comm]
        have hsum' : Finset.sum (t j) (fun i => w i) = wsum j := by
          simp [wsum]
        calc
          Finset.sum (t j) (fun i => w i / wsum j) =
              (1 / wsum j) * Finset.sum (t j) (fun i => w i) := hsum
          _ = (1 / wsum j) * wsum j := by simp [hsum']
          _ = 1 := by
            field_simp [hzero]
      have hy_mem : ∀ i ∈ t j, y i ∈ C j := by
        intro i hi
        have hf : f i = j := (Finset.mem_filter.1 hi).2
        simpa [hf] using hyC i
      have hsum_mem :
          (Finset.sum (t j) (fun i => (w i / wsum j) • y i)) ∈ C j :=
        (hCconv j).sum_mem hweights_nonneg hweights_sum hy_mem
      have hx_i_eq :
          x_i j = Finset.sum (t j) (fun i => (w i / wsum j) • y i) := by
        have :
            (1 / wsum j) • (Finset.sum (t j) (fun i => w i • y i)) =
              Finset.sum (t j) (fun i => (w i / wsum j) • y i) := by
          simp [div_eq_mul_inv, Finset.smul_sum, smul_smul, mul_comm]
        simpa [x_i, hzero] using this
      simpa [hx_i_eq] using hsum_mem
  have hsum_weights : Finset.univ.sum (fun j => wsum j) = 1 := by
    have hsum' :
        Finset.univ.sum (fun j => wsum j) =
          Finset.univ.sum (fun i : ι => w i) := by
      simpa [wsum, t] using
        (Finset.sum_fiberwise (s := (Finset.univ : Finset ι))
          (g := f) (f := fun i => w i))
    simpa [hsum'] using hw1
  have hterm :
      ∀ j, wsum j • x_i j = Finset.sum (t j) (fun i => w i • y i) := by
    intro j
    by_cases hzero : wsum j = 0
    · have hsum0 : Finset.sum (t j) (fun i => w i) = 0 := by
        simpa [wsum] using hzero
      have hzero_i : ∀ i ∈ t j, w i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := t j) (f := w)
            (fun i hi => hw0 i)).1 hsum0
      have hsum0' : Finset.sum (t j) (fun i => w i • y i) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [hzero_i i hi]
      simp [x_i, hzero, hsum0']
    · have hwsum : wsum j ≠ 0 := hzero
      calc
        wsum j • x_i j =
            wsum j • ((1 / wsum j) • Finset.sum (t j) (fun i => w i • y i)) := by
          simp [x_i, hzero]
        _ = (wsum j * (1 / wsum j)) •
              Finset.sum (t j) (fun i => w i • y i) := by
          simp [smul_smul]
        _ = (1 : Real) • Finset.sum (t j) (fun i => w i • y i) := by
          field_simp [hwsum]
        _ = Finset.sum (t j) (fun i => w i • y i) := by
          simp
  have hxsum' :
      x = Finset.univ.sum (fun j => wsum j • x_i j) := by
    have hsumfiber :
        Finset.univ.sum (fun j => Finset.sum (t j) (fun i => w i • y i)) =
          Finset.univ.sum (fun i : ι => w i • y i) := by
      simpa [t] using
        (Finset.sum_fiberwise (s := (Finset.univ : Finset ι))
          (g := f) (f := fun i => w i • y i))
    calc
      x = Finset.univ.sum (fun i : ι => w i • y i) := by
        simpa using hxsum.symm
      _ = Finset.univ.sum (fun j => Finset.sum (t j) (fun i => w i • y i)) := by
        symm
        exact hsumfiber
      _ = Finset.univ.sum (fun j => wsum j • x_i j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        exact hterm j
  refine ⟨wsum, x_i, hw_nonneg, hsum_weights, hx_i_mem, hxsum'⟩


end Section06
end Chap02
