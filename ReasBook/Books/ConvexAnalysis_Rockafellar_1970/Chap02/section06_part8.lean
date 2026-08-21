/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part7

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- The Minkowski sum of the lifted cones lies in the cone over the convex hull. -/
lemma sum_cones_subset_K0 (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n))) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
    let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    (∑ i, K i) ⊆ K0 := by
  classical
  intro C0 coords first tail S0 K0 S K v hv
  let K0cone : ConvexCone Real (EuclideanSpace Real (Fin (1 + n))) :=
    ConvexCone.hull Real S0
  have hS0 : S0 ⊆ K0 := by
    intro x hx
    exact ConvexCone.subset_hull hx
  have hSsub : ∀ i, S i ⊆ K0 := by
    intro i x hx
    have hxC0 : tail x ∈ C0 := by
      have hxUnion : tail x ∈ ⋃ i, C i := by
        exact Set.mem_iUnion.2 ⟨i, hx.2⟩
      exact (subset_convexHull (𝕜 := Real) (s := ⋃ i, C i)) hxUnion
    exact hS0 ⟨hx.1, hxC0⟩
  have hKsub : ∀ i, K i ⊆ K0 := by
    intro i x hx
    exact (ConvexCone.hull_min (s := S i) (C := K0cone) (hSsub i)) hx
  rcases
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin (Nat.succ m))))
          (f := fun i => K i) v).1 hv with ⟨z, hzmem, hsum⟩
  have hzmem' : ∀ i, z i ∈ K0 := by
    intro i
    exact hKsub i (hzmem (i := i) (by simp))
  have hsum_mem :
      (Finset.univ.sum (fun i => z i)) ∈ K0 := by
    have hsum_mem' :
        ∀ m : Nat,
          ∀ z : Fin (Nat.succ m) → EuclideanSpace Real (Fin (1 + n)),
            (∀ i, z i ∈ K0) →
              (Finset.univ.sum (fun i => z i)) ∈ K0 := by
      intro m
      induction m with
      | zero =>
          intro z hz
          simpa [Fin.sum_univ_one] using hz 0
      | succ m ih =>
          intro z hz
          have hz0 : z 0 ∈ K0 := hz 0
          have hz' : ∀ i : Fin (Nat.succ m), z (Fin.succ i) ∈ K0 := by
            intro i
            exact hz (Fin.succ i)
          have hsum' :
              (Finset.univ.sum (fun i : Fin (Nat.succ m) => z (Fin.succ i))) ∈ K0 :=
            ih _ hz'
          have hsum_eq :
              (Finset.univ.sum (fun i : Fin (Nat.succ (Nat.succ m)) => z i)) =
                z 0 +
                  Finset.univ.sum (fun i : Fin (Nat.succ m) => z (Fin.succ i)) := by
            simp [Fin.sum_univ_succ]
          have hsum_mem :
              z 0 +
                  Finset.univ.sum (fun i : Fin (Nat.succ m) => z (Fin.succ i)) ∈ K0 :=
            (ConvexCone.hull Real S0).add_mem hz0 hsum'
          simpa [hsum_eq] using hsum_mem
    exact hsum_mem' m z hzmem'
  simpa [hsum] using hsum_mem

/-- Base points of the cone over `C0` lie in the closure of the sum of cones. -/
lemma S0_subset_closure_sum_cones (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, (C i).Nonempty) (hCconv : ∀ i, Convex Real (C i)) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    S0 ⊆ closure (∑ i, K i) := by
  classical
  intro C0 coords first tail S0 S K v hv
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
    have h := (first_tail_append (n := n) (y := y0) (z := x))
    simpa [coords, first, tail, append, lift, y0] using h
  obtain ⟨w, x_i, hw0, hsum, hx_i_mem, hxsum⟩ :=
    convexHull_iUnion_exists_weights_points (n := n) (m := m) (C := C) hCne hCconv
      (x := tail v) hv.2
  have hv_eq : v = lift (tail v) := by
    have hfirst : first v = first (lift (tail v)) := by
      have hv1 : first v = 1 := hv.1
      have hfirst_lift : first (lift (tail v)) = 1 := (hfirst_tail_lift (tail v)).1
      simp [hv1, hfirst_lift]
    have htail : tail v = tail (lift (tail v)) := by
      have htail_lift : tail (lift (tail v)) = tail v := by
        simpa using (hfirst_tail_lift (tail v)).2
      simpa using htail_lift.symm
    exact
      (eq_of_first_tail_eq (n := n)
        (u := v) (v := lift (tail v)) hfirst htail)
  refine (Metric.mem_closure_iff).2 ?_
  intro ε hε
  let M : Real :=
    ‖Finset.univ.sum (fun i => x_i i)‖ +
      (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖
  have hMnonneg : 0 ≤ M := by
    have hm : 0 ≤ (Nat.succ m : Real) := by exact_mod_cast (Nat.zero_le _)
    have hsumw : 0 ≤ ‖Finset.univ.sum (fun i => w i • x_i i)‖ := norm_nonneg _
    have hsumx : 0 ≤ ‖Finset.univ.sum (fun i => x_i i)‖ := norm_nonneg _
    exact add_nonneg hsumx (mul_nonneg hm hsumw)
  let δ : Real := ε / (1 + M)
  have hδpos : 0 < δ := by
    have hden : 0 < 1 + M := by linarith
    exact div_pos hε hden
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  let c : Real := 1 + (Nat.succ m : Real) * δ
  have hcpos : 0 < c := by
    have hm : 0 ≤ (Nat.succ m : Real) := by exact_mod_cast (Nat.zero_le _)
    have hmul : 0 ≤ (Nat.succ m : Real) * δ := mul_nonneg hm hδnonneg
    linarith
  let w' : Fin (Nat.succ m) → Real :=
    fun i => (w i + δ) / c
  have hw'pos : ∀ i, 0 < w' i := by
    intro i
    have hnum : 0 < w i + δ := by
      have hw0' : 0 ≤ w i := hw0 i
      linarith
    exact div_pos hnum hcpos
  let z : Fin (Nat.succ m) → EuclideanSpace Real (Fin (1 + n)) :=
    fun i => w' i • lift (x_i i)
  have hzmem : ∀ i, z i ∈ K i := by
    intro i
    have hfirst_lift : first (lift (x_i i)) = 1 := (hfirst_tail_lift (x_i i)).1
    have htail_lift : tail (lift (x_i i)) = x_i i := (hfirst_tail_lift (x_i i)).2
    have hfirst_z : first (z i) = w' i := by
      have h := (first_smul (n := n) (a := w' i) (v := lift (x_i i)))
      simpa [z, coords, first, hfirst_lift] using h
    have htail_z : tail (z i) = w' i • x_i i := by
      have htail_smul :
          tail (w' i • lift (x_i i)) = w' i • tail (lift (x_i i)) := by
        simpa [coords, tail] using
          (tail_smul (n := n) (a := w' i) (v := lift (x_i i)))
      simpa [z, htail_lift] using htail_smul
    have hmem :
        0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
      refine ⟨?_, ?_⟩
      · simpa [hfirst_z] using hw'pos i
      · refine ⟨x_i i, hx_i_mem i, ?_⟩
        simp [hfirst_z, htail_z]
    have hmemK :
        z i ∈ K i ↔
          0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
      simpa [coords, first, tail, S, K] using
        (mem_K_iff_first_tail (n := n) (C := C i) (hCconv i) (v := z i))
    exact (hmemK).2 hmem
  have hsum_mem :
      Finset.univ.sum (fun i => z i) ∈ ∑ i, K i := by
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin (Nat.succ m))))
      (f := fun i => K i) (a := Finset.univ.sum (fun i => z i))).2 ?_
    refine ⟨z, ?_, rfl⟩
    intro i hi
    exact hzmem i
  refine ⟨Finset.univ.sum (fun i => z i), hsum_mem, ?_⟩
  have hsum_w' : Finset.univ.sum (fun i => w' i) = 1 := by
    have hsum_add :
        Finset.univ.sum (fun i => w i + δ) =
          Finset.univ.sum (fun i => w i) +
            Finset.univ.sum (fun _ : Fin (Nat.succ m) => δ) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin (Nat.succ m))))
          (f := fun i => w i) (g := fun _ : Fin (Nat.succ m) => δ))
    have hsum_const :
        Finset.univ.sum (fun _ : Fin (Nat.succ m) => (δ : Real)) =
          (Nat.succ m : Real) * δ := by
      simp
    calc
      Finset.univ.sum (fun i => w' i) =
          (Finset.univ.sum (fun i => w i + δ)) / c := by
        calc
          Finset.univ.sum (fun i => w' i) =
              Finset.univ.sum (fun i => (w i + δ) * c⁻¹) := by
            simp [w', div_eq_mul_inv]
          _ = (Finset.univ.sum (fun i => w i + δ)) * c⁻¹ := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Fin (Nat.succ m))))
                (f := fun i => w i + δ) (a := c⁻¹)).symm
          _ = (Finset.univ.sum (fun i => w i + δ)) / c := by
            simp [div_eq_mul_inv]
      _ = (Finset.univ.sum (fun i => w i) + (Nat.succ m : Real) * δ) / c := by
        simp [hsum_add, hsum_const]
      _ = (1 + (Nat.succ m : Real) * δ) / c := by simp [hsum]
      _ = 1 := by
        have hne : (1 + (Nat.succ m : Real) * δ) ≠ 0 := by
          linarith [hcpos]
        calc
          (1 + (Nat.succ m : Real) * δ) / c =
              (1 + (Nat.succ m : Real) * δ) / (1 + (Nat.succ m : Real) * δ) := by
            simp [c]
          _ = 1 := by
            field_simp [hne]
  have hsum_z :
      Finset.univ.sum (fun i => z i) =
        lift (Finset.univ.sum (fun i => w' i • x_i i)) := by
    simpa [z, y0, append, lift] using
      (sum_smul_lift_eq_lift_sum (n := n) (m := m) (w := w') (x_i := x_i) hsum_w')
  have hv_eq' : v = lift (Finset.univ.sum (fun i => w i • x_i i)) := by
    simpa [hxsum] using hv_eq
  have hdist_eq :
      dist (Finset.univ.sum (fun i => z i)) v =
        ‖Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i)‖ := by
    calc
      dist (Finset.univ.sum (fun i => z i)) v =
          dist (lift (Finset.univ.sum (fun i => w' i • x_i i)))
            (lift (Finset.univ.sum (fun i => w i • x_i i))) := by
        simp [hsum_z, hv_eq']
      _ = dist (Finset.univ.sum (fun i => w' i • x_i i))
            (Finset.univ.sum (fun i => w i • x_i i)) := by
        simpa [y0, append, lift] using
          (dist_lift_eq (n := n)
            (x := Finset.univ.sum (fun i => w' i • x_i i))
            (y := Finset.univ.sum (fun i => w i • x_i i)))
      _ = ‖Finset.univ.sum (fun i => w' i • x_i i) -
            Finset.univ.sum (fun i => w i • x_i i)‖ := by
        simpa using
          (dist_eq_norm (Finset.univ.sum (fun i => w' i • x_i i))
            (Finset.univ.sum (fun i => w i • x_i i)))
  have hperturb :
      ‖Finset.univ.sum (fun i => w' i • x_i i) -
          Finset.univ.sum (fun i => w i • x_i i)‖ ≤
        (δ / c) *
          (‖Finset.univ.sum (fun i => x_i i)‖ +
            (Nat.succ m : Real) * ‖Finset.univ.sum (fun i => w i • x_i i)‖) := by
    simpa [c, w'] using
      (weighted_sum_perturb_bound (n := n) (m := m) (w := w) (x_i := x_i) (δ := δ) hδnonneg)
  have hdist_le :
      dist (Finset.univ.sum (fun i => z i)) v ≤ (δ / c) * M := by
    simpa [hdist_eq, M] using hperturb
  have hcge : 1 ≤ c := by
    have hm : 0 ≤ (Nat.succ m : Real) := by exact_mod_cast (Nat.zero_le _)
    have hmul : 0 ≤ (Nat.succ m : Real) * δ := mul_nonneg hm hδnonneg
    linarith [c, hmul]
  have hδc_le : δ / c ≤ δ := by
    exact div_le_self hδnonneg hcge
  have hmul_le : (δ / c) * M ≤ δ * M :=
    mul_le_mul_of_nonneg_right hδc_le hMnonneg
  have hδM_lt : δ * M < ε := by
    have hden : 0 < 1 + M := by linarith [hMnonneg]
    have hMlt : M < 1 + M := by linarith
    have hmul : ε * M < ε * (1 + M) := by
      exact mul_lt_mul_of_pos_left hMlt hε
    have hdiv : (ε * M) / (1 + M) < ε :=
      (div_lt_iff₀ hden).2 hmul
    have hδM_eq : δ * M = (ε * M) / (1 + M) := by
      simp [δ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [hδM_eq] using hdiv
  have hdist_lt : dist (Finset.univ.sum (fun i => z i)) v < ε :=
    lt_of_le_of_lt (le_trans hdist_le hmul_le) hδM_lt
  exact (by simpa [dist_comm] using hdist_lt)

/-- The lifted cone over `C0` lies in the closure of the sum of cones. -/
lemma K0_subset_closure_sum_cones (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, (C i).Nonempty) (hCconv : ∀ i, Convex Real (C i)) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
    let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    K0 ⊆ closure (∑ i, K i) := by
  classical
  intro C0 coords first tail S0 K0 S K
  let Ksum : ConvexCone Real (EuclideanSpace Real (Fin (1 + n))) :=
    { carrier := ∑ i, K i
      smul_mem' := by
        intro a ha x hx
        rcases
            (Set.mem_finset_sum
                (t := (Finset.univ : Finset (Fin (Nat.succ m))))
                (f := fun i => K i) x).1 hx with ⟨z, hzmem, rfl⟩
        refine
          (Set.mem_finset_sum
              (t := (Finset.univ : Finset (Fin (Nat.succ m))))
              (f := fun i => K i)
              (a • Finset.univ.sum (fun i => z i))).2 ?_
        refine ⟨fun i => a • z i, ?_, ?_⟩
        · intro i hi
          have hz : z i ∈ (ConvexCone.hull Real (S i) : Set _) := by
            simpa [K] using hzmem (i := i) hi
          have hz' : a • z i ∈ (ConvexCone.hull Real (S i) : Set _) :=
            (ConvexCone.hull Real (S i)).smul_mem ha hz
          simpa [K] using hz'
        · have hsum :
              a • Finset.univ.sum (fun i => z i) =
                Finset.univ.sum (fun i => a • z i) := by
            simpa using
              (Finset.smul_sum (r := a) (f := fun i => z i)
                (s := (Finset.univ : Finset (Fin (Nat.succ m)))))
          simpa using hsum.symm
      add_mem' := by
        intro x hx y hy
        rcases
            (Set.mem_finset_sum
                (t := (Finset.univ : Finset (Fin (Nat.succ m))))
                (f := fun i => K i) x).1 hx with ⟨z1, hz1mem, rfl⟩
        rcases
            (Set.mem_finset_sum
                (t := (Finset.univ : Finset (Fin (Nat.succ m))))
                (f := fun i => K i) y).1 hy with ⟨z2, hz2mem, rfl⟩
        refine
          (Set.mem_finset_sum
              (t := (Finset.univ : Finset (Fin (Nat.succ m))))
              (f := fun i => K i)
              (Finset.univ.sum (fun i => z1 i) +
                Finset.univ.sum (fun i => z2 i))).2 ?_
        refine ⟨fun i => z1 i + z2 i, ?_, ?_⟩
        · intro i hi
          have hz1 : z1 i ∈ (ConvexCone.hull Real (S i) : Set _) := by
            simpa [K] using hz1mem (i := i) hi
          have hz2 : z2 i ∈ (ConvexCone.hull Real (S i) : Set _) := by
            simpa [K] using hz2mem (i := i) hi
          have hz : z1 i + z2 i ∈ (ConvexCone.hull Real (S i) : Set _) :=
            (ConvexCone.hull Real (S i)).add_mem hz1 hz2
          simpa [K] using hz
        · simpa using
            (Finset.sum_add_distrib
              (s := (Finset.univ : Finset (Fin (Nat.succ m))))
              (f := fun i => z1 i) (g := fun i => z2 i)) }
  have hS0subset : S0 ⊆ closure (∑ i, K i) := by
    simpa [C0, coords, first, tail, S0, S, K] using
      (S0_subset_closure_sum_cones (n := n) (m := m) (C := C) hCne hCconv)
  have hS0subset' : S0 ⊆ (Ksum.closure : Set _) := by
    simpa [Ksum, ConvexCone.coe_closure] using hS0subset
  have hK0subset : K0 ⊆ (Ksum.closure : Set _) := by
    simpa [K0] using
      (ConvexCone.hull_min (s := S0) (C := Ksum.closure) hS0subset')
  simpa [Ksum, ConvexCone.coe_closure] using hK0subset

/-- Theorem 6.9: Let `C_1, ..., C_m` be non-empty convex sets in `R^n`, and let
`C_0 = conv (C_1 ∪ ... ∪ C_m)`. Then
`ri C_0 = ⋃ {λ_1 ri C_1 + ... + λ_m ri C_m | λ_i > 0, λ_1 + ... + λ_m = 1}`. -/
theorem euclideanRelativeInterior_convexHull_iUnion_eq (n m : Nat)
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (hCne : ∀ i, (C i).Nonempty)
    (hCconv : ∀ i, Convex Real (C i)) :
    euclideanRelativeInterior n (convexHull Real (⋃ i, C i)) =
      {x | ∃ (w : Fin m → Real) (x_i : Fin m → EuclideanSpace Real (Fin n)),
          (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
            (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
            x = Finset.univ.sum (fun i => w i • x_i i)} := by
  classical
  cases m with
  | zero =>
      have hUnion :
          (⋃ i : Fin 0, C i) = (∅ : Set (EuclideanSpace Real (Fin n))) := by
        ext x; simp
      have hri_empty :
          euclideanRelativeInterior n (convexHull Real (⋃ i : Fin 0, C i)) =
            (∅ : Set (EuclideanSpace Real (Fin n))) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' :=
          (euclideanRelativeInterior_subset_closure n
              (convexHull Real (⋃ i : Fin 0, C i))).1 hx
        simp at hx'
      have hRHS :
          {x | ∃ (w : Fin 0 → Real) (x_i : Fin 0 → EuclideanSpace Real (Fin n)),
              (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
                (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                x = Finset.univ.sum (fun i => w i • x_i i)} =
            (∅ : Set (EuclideanSpace Real (Fin n))) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rcases hx with ⟨w, x_i, _hwpos, hsum, _hri, _hxsum⟩
        have : (0 : Real) = 1 := by
          simp at hsum
        linarith
      simpa [hRHS] using hri_empty
  | succ m =>
      let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
      have hC0conv : Convex Real C0 := by
        simpa [C0] using (convex_convexHull (s := ⋃ i, C i) (𝕜 := Real))
      have hUnion_ne : (⋃ i : Fin (Nat.succ m), C i).Nonempty := by
        rcases hCne 0 with ⟨x, hx⟩
        exact ⟨x, Set.mem_iUnion.2 ⟨0, hx⟩⟩
      have hC0ne : C0.Nonempty := by
        rcases hUnion_ne with ⟨x, hx⟩
        exact ⟨x, (subset_convexHull (𝕜 := Real) (s := ⋃ i, C i)) hx⟩
      let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
        EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
      let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
      let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
            (fun i => coords v (Fin.natAdd 1 i))
      let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
      let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
        (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
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
      let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
        fun i => {v | first v = 1 ∧ tail v ∈ C i}
      let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
        fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
      have hlift :
          ∀ x, x ∈ euclideanRelativeInterior n C0 ↔
            lift x ∈ euclideanRelativeInterior (1 + n) K0 := by
        simpa [coords, first, tail, S0, K0, y0, append, lift, C0] using
          (lift_mem_ri_cone_iff (n := n) (C := C0) hC0conv hC0ne)
      have hKconv : ∀ i, Convex Real (K i) := by
        intro i
        simpa [K] using
          (ConvexCone.convex (C := ConvexCone.hull Real (S i)))
      have hri_sum :
          euclideanRelativeInterior (1 + n) (∑ i, K i) =
            ∑ i, euclideanRelativeInterior (1 + n) (K i) := by
        simpa using
          (ri_sum_cones_eq_sum_ri (n := 1 + n) (m := m) (K := K) hKconv)
      have hri_eq :
          euclideanRelativeInterior (1 + n) K0 =
            euclideanRelativeInterior (1 + n) (∑ i, K i) := by
        have hK0conv : Convex Real K0 := by
          simpa [K0] using (ConvexCone.convex (C := ConvexCone.hull Real S0))
        have hsumconv : Convex Real (∑ i, K i) := by
          have hA :
              ∀ i ∈ (Finset.univ : Finset (Fin (Nat.succ m))),
                Convex Real (K i) := by
            intro i _hi
            exact hKconv i
          simpa using
            (convex_sum_finset_set_euclidean (n := 1 + n)
              (s := (Finset.univ : Finset (Fin (Nat.succ m))))
              (A := fun i => K i) hA)
        have hsum_subset : (∑ i, K i) ⊆ K0 := by
          simpa [C0, coords, first, tail, S0, K0, S, K] using
            (sum_cones_subset_K0 (n := n) (m := m) (C := C))
        have hcl_subset : closure (∑ i, K i) ⊆ closure K0 :=
          closure_mono hsum_subset
        have hcl_subset' : closure K0 ⊆ closure (∑ i, K i) := by
          have hK0subset : K0 ⊆ closure (∑ i, K i) := by
            simpa [C0, coords, first, tail, S0, K0, S, K] using
              (K0_subset_closure_sum_cones (n := n) (m := m) (C := C) hCne hCconv)
          have h := closure_mono hK0subset
          simpa [closure_closure] using h
        have hcl_eq : closure K0 = closure (∑ i, K i) :=
          subset_antisymm hcl_subset' hcl_subset
        exact
          (euclidean_closure_eq_iff_relativeInterior_eq_and_between (n := 1 + n)
              (C1 := K0) (C2 := ∑ i, K i) hK0conv hsumconv).1.mp hcl_eq
      ext x; constructor
      · intro hx
        have hx' : lift x ∈ euclideanRelativeInterior (1 + n) K0 := (hlift x).1 hx
        have hx'' : lift x ∈ euclideanRelativeInterior (1 + n) (∑ i, K i) := by
          simpa [hri_eq] using hx'
        have hx''' :
            lift x ∈ ∑ i, euclideanRelativeInterior (1 + n) (K i) := by
          simpa [hri_sum] using hx''
        have hfirst_tail :
            first (lift x) = 1 ∧ tail (lift x) = x := by
          simpa [coords, first, tail, append, lift, y0] using
            (first_tail_append (n := n) (y := y0) (z := x))
        have hweights :
            ∃ (w : Fin (Nat.succ m) → Real)
              (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
              (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
                (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                tail (lift x) = Finset.univ.sum (fun i => w i • x_i i) := by
          have hmem :=
            (mem_sum_ri_cones_iff_weights (n := n) (m := m) (C := C) hCne hCconv)
          have hmem' :
              ∀ v, first v = 1 →
                (v ∈ ∑ i, euclideanRelativeInterior (1 + n) (K i) ↔
                  ∃ (w : Fin (Nat.succ m) → Real)
                    (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
                    (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
                      (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                      tail v = Finset.univ.sum (fun i => w i • x_i i)) := by
            simpa [coords, first, tail, S, K] using hmem
          have hmem_lift := hmem' (lift x)
          have hmem_lift' := hmem_lift hfirst_tail.1
          exact (hmem_lift').1 hx'''
        rcases hweights with ⟨w, x_i, hwpos, hsum, hri, htail⟩
        refine ⟨w, x_i, hwpos, hsum, hri, ?_⟩
        simpa [hfirst_tail.2] using htail
      · intro hx
        rcases hx with ⟨w, x_i, hwpos, hsum, hri, hxsum⟩
        have hfirst_tail :
            first (lift x) = 1 ∧ tail (lift x) = x := by
          simpa [coords, first, tail, append, lift, y0] using
            (first_tail_append (n := n) (y := y0) (z := x))
        have htail :
            tail (lift x) = Finset.univ.sum (fun i => w i • x_i i) := by
          calc
            tail (lift x) = x := hfirst_tail.2
            _ = Finset.univ.sum (fun i => w i • x_i i) := hxsum
        have hmem_sum :
            lift x ∈ ∑ i, euclideanRelativeInterior (1 + n) (K i) := by
          have hmem :=
            (mem_sum_ri_cones_iff_weights (n := n) (m := m) (C := C) hCne hCconv)
          have hmem' :
              ∀ v, first v = 1 →
                (v ∈ ∑ i, euclideanRelativeInterior (1 + n) (K i) ↔
                  ∃ (w : Fin (Nat.succ m) → Real)
                    (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
                    (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
                      (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                      tail v = Finset.univ.sum (fun i => w i • x_i i)) := by
            simpa [coords, first, tail, S, K] using hmem
          have hweights :
              ∃ (w : Fin (Nat.succ m) → Real)
                (x_i : Fin (Nat.succ m) → EuclideanSpace Real (Fin n)),
                (∀ i, 0 < w i) ∧ (Finset.univ.sum (fun i => w i) = 1) ∧
                  (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                  tail (lift x) = Finset.univ.sum (fun i => w i • x_i i) := by
            exact ⟨w, x_i, hwpos, hsum, hri, htail⟩
          have hmem_lift := hmem' (lift x)
          have hmem_lift' := hmem_lift hfirst_tail.1
          exact (hmem_lift').2 hweights
        have hx'' : lift x ∈ euclideanRelativeInterior (1 + n) (∑ i, K i) := by
          simpa [hri_sum] using hmem_sum
        have hx' : lift x ∈ euclideanRelativeInterior (1 + n) K0 := by
          simpa [hri_eq] using hx''
        exact (hlift x).2 hx'

/-- The tail projection agrees with the linear map obtained from `appendAffineEquiv`. -/
lemma tail_linearMap_apply (n : Nat) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
          (M₂ := EuclideanSpace Real (Fin n))).comp
        (appendAffineEquiv 1 n).symm.linear.toLinearMap
    ∀ v, A v = tail v := by
  classical
  intro coords tail A v
  let append :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  let e : (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) ≃ₗ[Real]
      EuclideanSpace Real (Fin (1 + n)) := (appendAffineEquiv 1 n).linear
  let yz := e.symm v
  let y := yz.1
  let z := yz.2
  have hfun : ∀ x, appendAffineEquiv 1 n x = e x := by
    intro x
    simpa [e] using
      congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv 1 n)
  have hv : append y z = v := by
    have h1 : append y z = appendAffineEquiv 1 n (y, z) := by
      simp [append, appendAffineEquiv_apply]
    have h2 : appendAffineEquiv 1 n (y, z) = e (y, z) := hfun (y, z)
    have h3 : e (y, z) = v := by
      simp [y, z, yz]
    exact h1.trans (h2.trans h3)
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  have htail : tail v = z := by
    have htail' : tail (append y z) = z := by
      have hfirst_tail :
          first (append y z) =
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧
            tail (append y z) = z := by
        simpa [coords, first, tail, append] using
          (first_tail_append (n := n) (y := y) (z := z))
      exact hfirst_tail.2
    simpa [hv] using htail'
  have hA : A v = z := by
    simp [A, e, yz, z, LinearMap.comp_apply, AffineEquiv.linear_symm]
  simp [hA, htail]

/-- The tail projection of the lifted cone equals the cone generated by `C`. -/
lemma tail_image_cone_eq_convexCone_hull (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) :
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
    let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
          (M₂ := EuclideanSpace Real (Fin n))).comp
        (appendAffineEquiv 1 n).symm.linear.toLinearMap
    A '' K = (ConvexCone.hull Real C : Set (EuclideanSpace Real (Fin n))) := by
  classical
  intro coords first tail S K A
  let append :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  have hmem :
      ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
    simpa [coords, first, tail, S, K] using
      (mem_K_iff_first_tail (n := n) (C := C) hC)
  have hA : ∀ v, A v = tail v := by
    simpa [coords, tail, A] using (tail_linearMap_apply (n := n))
  ext v; constructor
  · rintro ⟨u, huK, rfl⟩
    have hu' : 0 < first u ∧ tail u ∈ (first u) • C := (hmem u).1 huK
    have : ∃ r : Real, 0 < r ∧ A u ∈ r • C := by
      refine ⟨first u, hu'.1, ?_⟩
      simpa [hA u] using hu'.2
    exact (ConvexCone.mem_hull_of_convex (s := C) hC).2 this
  · intro hv
    rcases (ConvexCone.mem_hull_of_convex (s := C) hC).1 hv with ⟨r, hr, hrC⟩
    rcases hrC with ⟨x, hxC, rfl⟩
    let y : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r)
    let u : EuclideanSpace Real (Fin (1 + n)) := append y (r • x)
    have hy : (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 = r := by
      simp [y]
    have hfirst_tail :
        first u = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧
          tail u = r • x := by
      simpa [coords, first, tail, append, u] using
        (first_tail_append (n := n) (y := y) (z := r • x))
    have hfirst : first u = r := by simpa [hy] using hfirst_tail.1
    have htail : tail u = r • x := hfirst_tail.2
    have hu : u ∈ K := by
      have : 0 < first u ∧ tail u ∈ first u • C := by
        refine ⟨?_, ?_⟩
        · simpa [hfirst] using hr
        · refine ⟨x, hxC, ?_⟩
          simp [hfirst, htail]
      exact (hmem u).2 this
    refine ⟨u, hu, ?_⟩
    simp [hA u, htail]

/-- The tail projection of the relative interior gives positive scalings of `ri C`. -/
lemma tail_image_ri_cone_eq_smul_ri (n : Nat)
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
    let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
          (M₂ := EuclideanSpace Real (Fin n))).comp
        (appendAffineEquiv 1 n).symm.linear.toLinearMap
    A '' euclideanRelativeInterior (1 + n) K =
      {v | ∃ r : Real, 0 < r ∧ ∃ x : EuclideanSpace Real (Fin n),
          x ∈ euclideanRelativeInterior n C ∧ v = r • x} := by
  classical
  intro coords first tail S K A
  let append :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  have hA : ∀ v, A v = tail v := by
    simpa [coords, tail, A] using (tail_linearMap_apply (n := n))
  have hriK :
      euclideanRelativeInterior (1 + n) K =
        {v | 0 < first v ∧ tail v ∈ (first v) • euclideanRelativeInterior n C} := by
    simpa [coords, first, tail, S, K] using
      (euclideanRelativeInterior_convexConeGenerated_eq (n := n) (C := C) hC hCne)
  ext v; constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : 0 < first u ∧ tail u ∈ (first u) • euclideanRelativeInterior n C := by
      simpa [hriK] using hu
    rcases (Set.mem_smul_set.mp hu'.2) with ⟨x, hxri, hx⟩
    refine ⟨first u, hu'.1, x, hxri, ?_⟩
    exact (hA u).trans hx.symm
  · rintro ⟨r, hr, x, hxri, rfl⟩
    let y : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r)
    let u : EuclideanSpace Real (Fin (1 + n)) := append y (r • x)
    have hy : (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 = r := by
      simp [y]
    have hfirst_tail :
        first u = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧
          tail u = r • x := by
      simpa [coords, first, tail, append, u] using
        (first_tail_append (n := n) (y := y) (z := r • x))
    have hfirst : first u = r := by simpa [hy] using hfirst_tail.1
    have htail : tail u = r • x := hfirst_tail.2
    have hu : u ∈ euclideanRelativeInterior (1 + n) K := by
      have : 0 < first u ∧ tail u ∈ first u • euclideanRelativeInterior n C := by
        refine ⟨?_, ?_⟩
        · simpa [hfirst] using hr
        · refine ⟨x, hxri, ?_⟩
          simp [hfirst, htail]
      simpa [hriK] using this
    refine ⟨u, hu, ?_⟩
    simp [hA u, htail]

/-- Text 6.19: More generally, the relative interior of the convex cone in `R^n` generated by
a non-empty convex set `C` consists of the vectors of the form `λ x` with `λ > 0` and
`x ∈ ri C`. -/
theorem euclideanRelativeInterior_convexConeGenerated_eq_smul (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty) :
    let K : Set (EuclideanSpace Real (Fin n)) :=
      (ConvexCone.hull Real C : Set (EuclideanSpace Real (Fin n)))
    euclideanRelativeInterior n K =
      {v | ∃ r : Real, 0 < r ∧ ∃ x : EuclideanSpace Real (Fin n),
          x ∈ euclideanRelativeInterior n C ∧ v = r • x} := by
  classical
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
        (fun i => coords v (Fin.natAdd 1 i))
  let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
  let K' : Set (EuclideanSpace Real (Fin (1 + n))) :=
    (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
  let append :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
        (M₂ := EuclideanSpace Real (Fin n))).comp
      (appendAffineEquiv 1 n).symm.linear.toLinearMap
  have hA_cone :
      A '' K' = (ConvexCone.hull Real C : Set (EuclideanSpace Real (Fin n))) := by
    simpa [coords, first, tail, S, K', A] using
      (tail_image_cone_eq_convexCone_hull (n := n) (C := C) hC)
  have hA_ri :
      A '' euclideanRelativeInterior (1 + n) K' =
        {v | ∃ r : Real, 0 < r ∧ ∃ x : EuclideanSpace Real (Fin n),
            x ∈ euclideanRelativeInterior n C ∧ v = r • x} := by
    simpa [coords, first, tail, S, K', A] using
      (tail_image_ri_cone_eq_smul_ri (n := n) (C := C) hC hCne)
  have hconvK' : Convex Real K' := by
    simpa [K'] using (ConvexCone.convex (C := ConvexCone.hull Real S))
  have hri :
      euclideanRelativeInterior n (A '' K') =
        A '' euclideanRelativeInterior (1 + n) K' :=
    (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
      (n := 1 + n) (m := n) (C := K') hconvK' A).1
  have hfinal :
      euclideanRelativeInterior n (ConvexCone.hull Real C : Set (EuclideanSpace Real (Fin n))) =
        {v | ∃ r : Real, 0 < r ∧ ∃ x : EuclideanSpace Real (Fin n),
            x ∈ euclideanRelativeInterior n C ∧ v = r • x} := by
    simpa [hA_cone, hA_ri] using hri
  simpa using hfinal

/-- A convex cone is invariant under positive scalar multiplication. -/
lemma smul_convexCone_eq_self (n : Nat)
    (K : ConvexCone Real (EuclideanSpace Real (Fin n))) (r : Real) (hr : 0 < r) :
    r • (K : Set (EuclideanSpace Real (Fin n))) = (K : Set (EuclideanSpace Real (Fin n))) := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.smul_mem hr hy
  · intro hx
    have hrne : (r : Real) ≠ 0 := by linarith
    have hrpos : 0 < (1 / r : Real) := by
      simpa [one_div] using (inv_pos.mpr hr)
    refine ⟨(1 / r) • x, K.smul_mem hrpos hx, ?_⟩
    simp [smul_smul, hrne]

/-- A convex set invariant under positive scalings is a convex cone. -/
lemma convexCone_of_convex_smul_invariant (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) (hsmul : ∀ r : Real, 0 < r → r • C = C) :
    ∃ K' : ConvexCone Real (EuclideanSpace Real (Fin n)), (K' : Set _) = C := by
  refine ⟨{ carrier := C, smul_mem' := ?_, add_mem' := ?_ }, rfl⟩
  · intro r hr x hx
    have : r • x ∈ r • C := ⟨x, hx, rfl⟩
    simpa [hsmul r hr] using this
  · intro x hx y hy
    have hmid : ((1 / 2 : Real) • x + (1 / 2 : Real) • y) ∈ C := by
      have ha : (0 : Real) ≤ (1 / 2 : Real) := by norm_num
      have hb : (0 : Real) ≤ (1 / 2 : Real) := by norm_num
      have hab : (1 / 2 : Real) + (1 / 2 : Real) = 1 := by norm_num
      simpa [hab] using hC hx hy ha hb hab
    have h2 : (0 : Real) < 2 := by norm_num
    have hscaled :
        (2 : Real) • ((1 / 2 : Real) • x + (1 / 2 : Real) • y) ∈ C := by
      have :
          (2 : Real) • ((1 / 2 : Real) • x + (1 / 2 : Real) • y) ∈ (2 : Real) • C :=
        ⟨(1 / 2 : Real) • x + (1 / 2 : Real) • y, hmid, rfl⟩
      simpa [hsmul 2 h2] using this
    have hcoeff : (2 : Real) * (1 / 2 : Real) = 1 := by norm_num
    simpa [smul_add, smul_smul, hcoeff] using hscaled

/-- The relative interior of a convex cone is invariant under positive scalings. -/
lemma ri_smul_invariant_of_cone (n : Nat)
    (K : ConvexCone Real (EuclideanSpace Real (Fin n))) (r : Real) (hr : 0 < r) :
    r • euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) =
      euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) := by
  have hconv : Convex Real (K : Set (EuclideanSpace Real (Fin n))) := K.convex
  have hri :
      euclideanRelativeInterior n (r • (K : Set (EuclideanSpace Real (Fin n)))) =
        r • euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) :=
    euclideanRelativeInterior_smul n (K : Set (EuclideanSpace Real (Fin n))) hconv r
  have hsmul :
      r • (K : Set (EuclideanSpace Real (Fin n))) = (K : Set (EuclideanSpace Real (Fin n))) :=
    smul_convexCone_eq_self (n := n) K r hr
  have hri' :
      euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) =
        r • euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) := by
    simpa [hsmul] using hri
  exact hri'.symm

/-- Text 6.20: The relative interior and the closure of a convex cone are convex cones. -/
theorem euclideanRelativeInterior_and_closure_convexCone (n : Nat)
    (K : ConvexCone Real (EuclideanSpace Real (Fin n))) :
    (∃ K' : ConvexCone Real (EuclideanSpace Real (Fin n)),
        (K' : Set (EuclideanSpace Real (Fin n))) =
          euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n)))) ∧
      (∃ K' : ConvexCone Real (EuclideanSpace Real (Fin n)),
        (K' : Set (EuclideanSpace Real (Fin n))) =
          closure (K : Set (EuclideanSpace Real (Fin n)))) := by
  constructor
  · have hconv :
        Convex Real (euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n)))) :=
      convex_euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) K.convex
    have hsmul :
        ∀ r : Real, 0 < r →
          r • euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) =
            euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))) := by
      intro r hr
      exact ri_smul_invariant_of_cone (n := n) K r hr
    simpa using
      (convexCone_of_convex_smul_invariant (n := n)
        (C := euclideanRelativeInterior n (K : Set (EuclideanSpace Real (Fin n))))
        hconv hsmul)
  · refine ⟨K.closure, ?_⟩
    simp

end Section06
end Chap02
