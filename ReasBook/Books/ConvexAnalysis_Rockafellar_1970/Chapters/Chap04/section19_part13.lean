/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part12

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.6: for a family indexed by `Fin (m+1)`, the weighted-union formula
for `closure (convexHull (⋃ i, C i))` follows from the lifted-cone closure-sum identity. -/
lemma helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_closed : ∀ i, IsClosed (C i))
    (h_convex : ∀ i, Convex ℝ (C i)) :
    let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
      fun v => v
    let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
    let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
      fun v i => coords v (Fin.succ i)
    let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
    let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (Fin (n + 1) → ℝ) :=
      (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
    let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
      fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
    closure K0 = closure (∑ i, K i) ∧
      (closure C0 =
        {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
      (∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
  classical
  intro coords first tail C0 S0 K0 S K
  let eN : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
  let CE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => eN '' C i
  have hCE_nonempty : ∀ i, (CE i).Nonempty := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_nonempty_transport_toEuclidean (n := n) (C := C i) (h_nonempty i))
  have hCE_closed : ∀ i, IsClosed (CE i) := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_closed_transport_toEuclidean (n := n) (C := C i) (h_closed i))
  have hCE_convex : ∀ i, Convex ℝ (CE i) := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_convex_transport_toEuclidean (n := n) (C := C i) (h_convex i))
  have hC0_image :
      eN '' C0 = convexHull ℝ (⋃ i, CE i) := by
    simpa [C0, CE, eN] using
      (helperForTheorem_19_6_convexHull_iUnion_image_linearEquiv (n := n) (m := m) (C := C))
  have hweighted_image :
      ∀ lam : Fin (Nat.succ m) → ℝ,
        eN ''
            (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
          ∑ i,
            (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i)) := by
    intro lam
    simpa [CE] using
      (helperForTheorem_19_6_image_weightedUnion_linearEquiv
        (n := n) (m := m) (C := C) (eN := eN.toLinearEquiv) (lam := lam))
  have hclosureE :
      let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
      let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
      let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
      let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
      closure K0E = closure (∑ i, KE i) := by
    simpa [CE] using
      (closure_cone_over_convexHull_eq_closure_sum_cones_succ
        (n := n) (m := m) (C := CE) hCE_nonempty hCE_convex)
  have hsliceE :
      let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
      let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
      closure C0E =
        {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
    have hC0E_convex : Convex ℝ (convexHull ℝ (⋃ i, CE i)) :=
      convex_convexHull (𝕜 := ℝ) (s := ⋃ i, CE i)
    simpa [CE] using
      (closure_C0_eq_first_one_slice_closure_lifted_cone (n := n)
        (C0 := convexHull ℝ (⋃ i, CE i)) hC0E_convex)
  have hmemE :
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
      let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
      ∀ v, firstE v = 1 →
        (v ∈ ∑ i, closure (KE i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tailE v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i))) := by
    simpa [CE] using
      (mem_sum_closure_cones_first_eq_one_iff
        (n := n) (m := Nat.succ m) (C := CE) hCE_nonempty hCE_closed hCE_convex)
  let idxNp1 : Fin (n + 1) ≃ Fin (1 + n) :=
    { toFun := fun i => ⟨i.1, by omega⟩
      invFun := fun i => ⟨i.1, by omega⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  let eNp1Cast : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + n)) :=
    (((LinearEquiv.funCongrLeft ℝ ℝ idxNp1).symm).toContinuousLinearEquiv).trans
      ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))).symm)
  let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
  let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
  let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
  let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
        (fun i => coordsE v (Fin.natAdd 1 i))
  let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
  let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
  let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
  let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
  let weightedC : (Fin (Nat.succ m) → ℝ) → Set (Fin n → ℝ) :=
    fun lam => ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))
  let weightedCE : (Fin (Nat.succ m) → ℝ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun lam => ∑ i, (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i))
  have hclosureE' : closure K0E = closure (∑ i, KE i) := by
    simpa [C0E, coordsE, firstE, tailE, S0E, K0E, SE, KE] using hclosureE
  have hsliceE' :
      closure C0E = {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
    simpa [C0E, coordsE, firstE, tailE, S0E, K0E] using hsliceE
  have hmemE' :
      ∀ v, firstE v = 1 →
        (v ∈ ∑ i, closure (KE i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tailE v ∈ weightedCE lam) := by
    simpa [coordsE, firstE, tailE, SE, KE, weightedCE] using hmemE
  have hfirst_e : ∀ v, firstE (eNp1Cast v) = first v := by
    intro v
    simp [firstE, first, coordsE, coords, eNp1Cast, idxNp1]
  have hfirst_symm : ∀ w, first (eNp1Cast.symm w) = firstE w := by
    intro w
    have h := hfirst_e (eNp1Cast.symm w)
    simpa using h
  have htail_e : ∀ v, tailE (eNp1Cast v) = eN (tail v) := by
    intro v
    apply eN.symm.injective
    funext i
    simp [tailE, coordsE, eNp1Cast, idxNp1, eN, tail, coords]
    have hidx :
        ((⟨1 + (i : ℕ), by omega⟩ : Fin (n + 1))) = Fin.succ i := by
      apply Fin.ext
      simp [Fin.succ, Nat.add_comm]
    simp [hidx]
  have htail_symm : ∀ w, tail (eNp1Cast.symm w) = eN.symm (tailE w) := by
    intro w
    have h := htail_e (eNp1Cast.symm w)
    have h' : tailE w = eN (tail (eNp1Cast.symm w)) := by
      simpa using h
    have h'' := congrArg eN.symm h'
    simpa using h''.symm
  have hCE_pre : ∀ i, eN ⁻¹' CE i = C i := by
    intro i
    calc
      eN ⁻¹' CE i = eN ⁻¹' (eN '' C i) := by simp [CE]
      _ = C i := Set.preimage_image_eq _ eN.injective
  have hC0_pre : eN ⁻¹' C0E = C0 := by
    calc
      eN ⁻¹' C0E = eN ⁻¹' (eN '' C0) := by
        simpa [C0E] using congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) => eN ⁻¹' s) hC0_image.symm
      _ = C0 := Set.preimage_image_eq _ eN.injective
  have hS0_image : eNp1Cast '' S0 = S0E := by
    ext w
    constructor
    · rintro ⟨v, hvS0, rfl⟩
      rcases hvS0 with ⟨hv1, hvC0⟩
      refine ⟨by simpa [hfirst_e v] using hv1, ?_⟩
      have htail_pre : tail v ∈ eN ⁻¹' C0E := by
        simpa [hC0_pre] using hvC0
      simpa [Set.mem_preimage, htail_e v] using htail_pre
    · intro hw
      refine ⟨eNp1Cast.symm w, ?_, by simp⟩
      rcases hw with ⟨hw1, hwC0⟩
      refine ⟨(hfirst_symm w).trans hw1, ?_⟩
      have htail_in : eN.symm (tailE w) ∈ C0 := by
        have htail_pre : eN.symm (tailE w) ∈ eN ⁻¹' C0E := by
          simpa [Set.mem_preimage] using hwC0
        simpa [hC0_pre] using htail_pre
      simpa [htail_symm w] using htail_in
  have hSE_image : ∀ i, eNp1Cast '' S i = SE i := by
    intro i
    ext w
    constructor
    · rintro ⟨v, hvS, rfl⟩
      rcases hvS with ⟨hv1, hvCi⟩
      refine ⟨by simpa [hfirst_e v] using hv1, ?_⟩
      have htail_pre : tail v ∈ eN ⁻¹' CE i := by
        simpa [hCE_pre i] using hvCi
      simpa [Set.mem_preimage, htail_e v] using htail_pre
    · intro hw
      refine ⟨eNp1Cast.symm w, ?_, by simp⟩
      rcases hw with ⟨hw1, hwCi⟩
      refine ⟨(hfirst_symm w).trans hw1, ?_⟩
      have htail_in : eN.symm (tailE w) ∈ C i := by
        have htail_pre : eN.symm (tailE w) ∈ eN ⁻¹' CE i := by
          simpa [Set.mem_preimage] using hwCi
        simpa [hCE_pre i] using htail_pre
      simpa [htail_symm w] using htail_in
  have hK0_image : eNp1Cast '' K0 = K0E := by
    calc
      eNp1Cast '' K0 = eNp1Cast '' (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ)) := by rfl
      _ = (ConvexCone.hull ℝ (eNp1Cast '' S0) : Set (EuclideanSpace ℝ (Fin (1 + n)))) := by
        simpa using
          (helperForTheorem_19_6_convexConeHull_image_linearEquiv
            (e := eNp1Cast.toLinearEquiv) (s := S0))
      _ = K0E := by simp [K0E, hS0_image]
  have hKE_image : ∀ i, eNp1Cast '' K i = KE i := by
    intro i
    calc
      eNp1Cast '' K i = eNp1Cast '' (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ)) := by rfl
      _ = (ConvexCone.hull ℝ (eNp1Cast '' S i) : Set (EuclideanSpace ℝ (Fin (1 + n)))) := by
        simpa using
          (helperForTheorem_19_6_convexConeHull_image_linearEquiv
            (e := eNp1Cast.toLinearEquiv) (s := S i))
      _ = KE i := by simp [KE, hSE_image i]
  have hK0_pre : eNp1Cast ⁻¹' K0E = K0 := by
    calc
      eNp1Cast ⁻¹' K0E = eNp1Cast ⁻¹' (eNp1Cast '' K0) := by simp [hK0_image]
      _ = K0 := Set.preimage_image_eq _ eNp1Cast.injective
  have hKE_pre : ∀ i, eNp1Cast ⁻¹' KE i = K i := by
    intro i
    calc
      eNp1Cast ⁻¹' KE i = eNp1Cast ⁻¹' (eNp1Cast '' K i) := by simp [hKE_image i]
      _ = K i := Set.preimage_image_eq _ eNp1Cast.injective
  have hpreK0closure : eNp1Cast ⁻¹' closure K0E = closure K0 := by
    calc
      eNp1Cast ⁻¹' closure K0E = closure (eNp1Cast ⁻¹' K0E) := by
        simpa using eNp1Cast.preimage_closure K0E
      _ = closure K0 := by simp [hK0_pre]
  have hpreC0closure : eN ⁻¹' closure C0E = closure C0 := by
    calc
      eN ⁻¹' closure C0E = closure (eN ⁻¹' C0E) := by
        simpa using eN.preimage_closure C0E
      _ = closure C0 := by simp [hC0_pre]
  have hpre_sum : eNp1Cast ⁻¹' (∑ i, KE i) = ∑ i, K i := by
    calc
      eNp1Cast ⁻¹' (∑ i, KE i) = ∑ i, (eNp1Cast ⁻¹' KE i) := by
        simpa using
          (helperForTheorem_19_6_preimage_finsetSum_addEquiv
            (e := eNp1Cast.toLinearEquiv.toAddEquiv)
            (A := KE))
      _ = ∑ i, K i := by
        simp [hKE_pre]
  have hpre_sum_closure : eNp1Cast ⁻¹' (∑ i, closure (KE i)) = ∑ i, closure (K i) := by
    calc
      eNp1Cast ⁻¹' (∑ i, closure (KE i)) = ∑ i, (eNp1Cast ⁻¹' closure (KE i)) := by
        simpa using
          (helperForTheorem_19_6_preimage_finsetSum_addEquiv
            (e := eNp1Cast.toLinearEquiv.toAddEquiv)
            (A := fun i => closure (KE i)))
      _ = ∑ i, closure (eNp1Cast ⁻¹' KE i) := by
        simp [eNp1Cast.preimage_closure]
      _ = ∑ i, closure (K i) := by
        simp [hKE_pre]
  have hclosure_main : closure K0 = closure (∑ i, K i) := by
    have hpre := congrArg (fun s : Set (EuclideanSpace ℝ (Fin (1 + n))) => eNp1Cast ⁻¹' s) hclosureE'
    simpa [hpreK0closure, eNp1Cast.preimage_closure, hpre_sum] using hpre
  have hslice_main :
      closure C0 = {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
    ext x
    constructor
    · intro hx
      have hxE : eN x ∈ closure C0E := by
        have hxpre : x ∈ eN ⁻¹' closure C0E := by
          simpa [hpreC0closure] using hx
        simpa [Set.mem_preimage] using hxpre
      have hxE' : eN x ∈ {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
        simpa [hsliceE'] using hxE
      rcases hxE' with ⟨vE, hvEcl, hvE1, hvEtail⟩
      have hvcl : eNp1Cast.symm vE ∈ closure K0 := by
        have hvpre : eNp1Cast.symm vE ∈ eNp1Cast ⁻¹' closure K0E := by
          simpa [Set.mem_preimage] using hvEcl
        simpa [hpreK0closure] using hvpre
      refine ⟨eNp1Cast.symm vE, hvcl, (hfirst_symm vE).trans hvE1, ?_⟩
      apply eN.injective
      calc
        eN (tail (eNp1Cast.symm vE)) = tailE vE := by
          simpa using congrArg eN (htail_symm vE)
        _ = eN x := hvEtail
    · rintro ⟨v, hvcl, hv1, hvx⟩
      have hvEcl : eNp1Cast v ∈ closure K0E := by
        have hvpre : v ∈ eNp1Cast ⁻¹' closure K0E := by
          simpa [hpreK0closure] using hvcl
        simpa [Set.mem_preimage] using hvpre
      have hvE1 : firstE (eNp1Cast v) = 1 := by
        simpa [hfirst_e v] using hv1
      have hvEtail : tailE (eNp1Cast v) = eN x := by
        calc
          tailE (eNp1Cast v) = eN (tail v) := htail_e v
          _ = eN x := by simp [hvx]
      have hxE' : eN x ∈ {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
        exact ⟨eNp1Cast v, hvEcl, hvE1, hvEtail⟩
      have hxE : eN x ∈ closure C0E := by
        simpa [hsliceE'] using hxE'
      have hxpre : x ∈ eN ⁻¹' closure C0E := by
        simpa [Set.mem_preimage] using hxE
      simpa [hpreC0closure] using hxpre
  have hweighted_pre : ∀ lam, eN ⁻¹' weightedCE lam = weightedC lam := by
    intro lam
    simpa [weightedC, weightedCE, CE] using
      (helperForTheorem_19_6_preimage_weightedUnion_linearEquiv
        (n := n) (m := m) (C := C) (eN := eN.toLinearEquiv) (lam := lam))
  have hmem_main :
      ∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈ weightedC lam) := by
    intro v hv1
    have hv1E : firstE (eNp1Cast v) = 1 := by
      simpa [hfirst_e v] using hv1
    have hE := hmemE' (eNp1Cast v) hv1E
    constructor
    · intro hvsum
      have hvpre : v ∈ eNp1Cast ⁻¹' (∑ i, closure (KE i)) := by
        simpa [hpre_sum_closure] using hvsum
      have hvsumE : eNp1Cast v ∈ ∑ i, closure (KE i) := by
        simpa [Set.mem_preimage] using hvpre
      rcases (hE.1 hvsumE) with ⟨lam, hlam_nonneg, hsum_lam, htailE_mem⟩
      have htail_pre : tail v ∈ eN ⁻¹' weightedCE lam := by
        simpa [Set.mem_preimage, htail_e v] using htailE_mem
      have htail_mem : tail v ∈ weightedC lam := by
        simpa [hweighted_pre lam] using htail_pre
      exact ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
    · rintro ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
      have htail_pre : tail v ∈ eN ⁻¹' weightedCE lam := by
        simpa [hweighted_pre lam] using htail_mem
      have htailE_mem : tailE (eNp1Cast v) ∈ weightedCE lam := by
        simpa [Set.mem_preimage, htail_e v] using htail_pre
      have hvsumE : eNp1Cast v ∈ ∑ i, closure (KE i) :=
        (hE.2 ⟨lam, hlam_nonneg, hsum_lam, htailE_mem⟩)
      have hvpre : v ∈ eNp1Cast ⁻¹' (∑ i, closure (KE i)) := by
        simpa [Set.mem_preimage] using hvsumE
      simpa [hpre_sum_closure] using hvpre
  exact ⟨hclosure_main, hslice_main, by simpa [weightedC] using hmem_main⟩

/-- Helper for Theorem 19.6: for a family indexed by `Fin (m+1)`, the weighted-union formula
for `closure (convexHull (⋃ i, C i))` follows from the lifted-cone closure-sum identity. -/
lemma helperForTheorem_19_6_closure_convexHull_eq_weighted_union_core_noLineal
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_closed : ∀ i, IsClosed (C i))
    (h_convex : ∀ i, Convex ℝ (C i))
    (hclosure_sum :
      let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
        fun v => v
      let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
      let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
        fun v i => coords v (Fin.succ i)
      let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
        fun i => {v | first v = 1 ∧ tail v ∈ C i}
      let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
        fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
      closure (∑ i, K i) = ∑ i, closure (K i)) :
    closure (convexHull ℝ (⋃ i, C i)) =
      ⋃ (lam : Fin (Nat.succ m) → ℝ),
        ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  classical
  let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun v => v
  let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
  let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
    fun v i => coords v (Fin.succ i)
  let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
  let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
  let K0 : Set (Fin (n + 1) → ℝ) :=
    (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
  let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
    fun i => {v | first v = 1 ∧ tail v ∈ C i}
  let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
    fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
  have hclosure_sum' : closure (∑ i, K i) = ∑ i, closure (K i) := by
    simpa [coords, first, tail, S, K] using hclosure_sum
  have htransport :=
    helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
      (n := n) (m := m) (C := C) h_nonempty h_closed h_convex
  have htransport' :
      closure K0 = closure (∑ i, K i) ∧
        (closure C0 =
          {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
        (∀ v, first v = 1 →
          (v ∈ ∑ i, closure (K i) ↔
            ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
              tail v ∈
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
    simpa [coords, first, tail, C0, S0, K0, S, K] using htransport
  have hclosureK0 : closure K0 = ∑ i, closure (K i) :=
    htransport'.1.trans hclosure_sum'
  have hslice :
      closure C0 =
        {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := htransport'.2.1
  have hslice_sum :
      ∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) :=
    htransport'.2.2
  ext x
  constructor
  · intro hx
    have hxC0 : x ∈ closure C0 := by
      simpa [C0] using hx
    have hx' : x ∈ {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
      simpa [hslice] using hxC0
    rcases hx' with ⟨v, hvcl, hv1, hvx⟩
    have hvsum : v ∈ ∑ i, closure (K i) := by
      simpa [hclosureK0] using hvcl
    rcases (hslice_sum v hv1).1 hvsum with ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨lam, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨hlam_nonneg, hsum_lam⟩, ?_⟩
    simpa [hvx] using htail_mem
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hlam, htail_mem⟩
    let v : Fin (n + 1) → ℝ := Fin.cases (1 : ℝ) x
    have hv1 : first v = 1 ∧ tail v = x := by
      constructor
      · simp [first, coords, v]
      · funext i
        simp [tail, coords, v]
    have hvsum : v ∈ ∑ i, closure (K i) := by
      exact (hslice_sum v hv1.1).2 ⟨lam, hlam.1, hlam.2, by simpa [hv1.2] using htail_mem⟩
    have hvcl : v ∈ closure K0 := by
      simpa [hclosureK0] using hvsum
    have hx' : x ∈ {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} :=
      ⟨v, hvcl, hv1.1, hv1.2⟩
    have hxC0 : x ∈ closure C0 := by
      simpa [hslice] using hx'
    simpa [C0] using hxC0

/-- Helper for Theorem 19.6: core closure/representation package for
`closure (convexHull (⋃ i, C i))` under polyhedral hypotheses. -/
lemma helperForTheorem_19_6_polyhedral_and_weightedUnion_core
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) ∧
      closure (convexHull ℝ (⋃ i, C i)) =
        ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  classical
  rcases helperForTheorem_19_6_closed_convex_of_polyhedral_family
      (n := n) (m := m) (C := C) h_polyhedral with ⟨h_closed, h_convex⟩
  cases m with
  | zero =>
      have hrepr0 :
          closure (convexHull ℝ (⋃ i : Fin 0, C i)) =
            ⋃ (lam : Fin 0 → ℝ),
              ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
        ext x
        simp
      have hpoly0 : IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i : Fin 0, C i))) := by
        exact
          helperForTheorem_19_6_polyhedral_emptyClosureConvexHull_fin0
            (n := n) (C := C)
      exact ⟨hpoly0, hrepr0⟩
  | succ m' =>
      let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun v => v
      let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
      let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
        fun v i => coords v (Fin.succ i)
      let S : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
        fun i => {v | first v = 1 ∧ tail v ∈ C i}
      let K : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
        fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
      have hK_poly : ∀ i, IsPolyhedralConvexSet (n + 1) (closure (K i)) := by
        intro i
        have hSlice_nonempty :
            ({v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i}).Nonempty :=
          helperForTheorem_19_6_nonempty_liftedSlice
            (n := n) (C := C i) (h_nonempty i)
        have hSlice_poly :
            IsPolyhedralConvexSet (n + 1)
              {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i} :=
          helperForTheorem_19_6_polyhedral_liftedSlice
            (n := n) (C := C i) (h_polyhedral i)
        have hCone_poly :
            IsPolyhedralConvexSet (n + 1)
              (closure
                ((ConvexCone.hull ℝ
                    {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i}) :
                    Set (Fin (n + 1) → ℝ))) :=
          helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
            (d := n + 1)
            (S := {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i})
            hSlice_nonempty hSlice_poly
        simpa [coords, first, tail, S, K] using hCone_poly
      have hclosure_sum : closure (∑ i, K i) = ∑ i, closure (K i) :=
        helperForTheorem_19_6_closure_sum_liftedCones_eq_sum_closure_liftedCones_polyhedral
          (n := n) (m := Nat.succ m') (K := K) hK_poly
      have hrepr :
          closure (convexHull ℝ (⋃ i, C i)) =
            ⋃ (lam : Fin (Nat.succ m') → ℝ),
              ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
        have hclosure_sum_for_repr :
            let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
              fun v => v
            let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
            let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
              fun v i => coords v (Fin.succ i)
            let S : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
              fun i => {v | first v = 1 ∧ tail v ∈ C i}
            let K : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
              fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
            closure (∑ i, K i) = ∑ i, closure (K i) := by
          simpa [coords, first, tail, S, K] using hclosure_sum
        exact
          helperForTheorem_19_6_closure_convexHull_eq_weighted_union_core_noLineal
            (n := n) (m := m') (C := C) h_nonempty h_closed h_convex
            hclosure_sum_for_repr
      have hpoly : IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) := by
        let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
        let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
        let K0 : Set (Fin (n + 1) → ℝ) :=
          (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
        have hsum_poly :
            IsPolyhedralConvexSet (n + 1) (∑ i, closure (K i)) :=
          helperForTheorem_19_6_polyhedral_finset_sum
            (n := n + 1) (m := Nat.succ m')
            (S := fun i => closure (K i)) hK_poly
        have htransport :=
          helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
            (n := n) (m := m') (C := C) h_nonempty h_closed h_convex
        have htransport' :
            closure K0 = closure (∑ i, K i) ∧
              (closure C0 =
                {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
              (∀ v, first v = 1 →
                (v ∈ ∑ i, closure (K i) ↔
                  ∃ (lam : Fin (Nat.succ m') → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
                    tail v ∈
                      ∑ i,
                        (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
          simpa [coords, first, tail, C0, S0, K0, S, K] using htransport
        have hclosureK0 : closure K0 = ∑ i, closure (K i) :=
          htransport'.1.trans hclosure_sum
        have hslice :
            closure C0 =
              {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} :=
          htransport'.2.1
        have hslice_eq_liftPreimage :
            {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} =
              {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ closure K0} := by
          ext x
          constructor
          · rintro ⟨v, hvcl, hv1, hvx⟩
            have hv_eq : v = Fin.cases (1 : ℝ) x := by
              funext j
              refine Fin.cases ?_ ?_ j
              · simpa [first, coords] using hv1
              · intro i
                have htail_i := congrArg (fun f : Fin n → ℝ => f i) hvx
                simpa [tail, coords] using htail_i
            simpa [hv_eq] using hvcl
          · intro hx
            refine ⟨Fin.cases (1 : ℝ) x, ?_, ?_, ?_⟩
            · simpa using hx
            · simp [first, coords]
            · funext i
              simp [tail, coords]
        have hK0_poly : IsPolyhedralConvexSet (n + 1) (closure K0) := by
          simpa [hclosureK0] using hsum_poly
        have hlift_poly :
            IsPolyhedralConvexSet n
              {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ closure K0} :=
          helperForTheorem_19_1_lift_preimage_polyhedral
            (n := n) (K := closure K0) hK0_poly
        have hC0_poly : IsPolyhedralConvexSet n (closure C0) := by
          simpa [hslice, hslice_eq_liftPreimage] using hlift_poly
        simpa [C0] using hC0_poly
      exact ⟨hpoly, hrepr⟩

/-- Helper for Theorem 19.6: the explicit union over raw weight functions with simplex
constraints is equivalent to the subtype-indexed union via
`weightedSumSetWithRecession`. -/
lemma helperForTheorem_19_6_iUnionWeights_eq_weightedSumSubtype
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)} :
    (⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
      ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i)) =
      ⋃ (lam : {lam : Fin m → ℝ // (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1}),
        weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hlam, hx⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨lam, hlam⟩, ?_⟩
    simpa [helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf] using hx
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨(lam : Fin m → ℝ), ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨lam.2, ?_⟩
    simpa [helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf] using hx

/-- Theorem 19.6: If `C₁, …, Cₘ` are non-empty polyhedral convex sets in `ℝ^n` and
`C = cl (conv (C₁ ∪ ··· ∪ Cₘ))`, then `C` is polyhedral convex, and
`C` is the union of weighted sums `λ₁ C₁ + ··· + λₘ Cₘ` over all choices of
`λ_i ≥ 0` with `∑ i, λ_i = 1`, using `0^+ C_i` in place of `0 • C_i` when `λ_i = 0`. -/
theorem polyhedralConvexSet_closure_convexHull_iUnion_weightedSum
    (n m : ℕ) (C : Fin m → Set (Fin n → ℝ)) (C' : Set (Fin n → ℝ))
    (hC' : C' = closure (convexHull ℝ (⋃ i, C i)))
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    IsPolyhedralConvexSet n C' ∧
      C' =
        ⋃ (lam : {lam : Fin m → ℝ // (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1}),
          weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) := by
  subst hC'
  have hcore :
      IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) ∧
        closure (convexHull ℝ (⋃ i, C i)) =
          ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
            ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) :=
    helperForTheorem_19_6_polyhedral_and_weightedUnion_core
      (n := n) (m := m) (C := C) h_nonempty h_polyhedral
  refine ⟨hcore.1, ?_⟩
  calc
    closure (convexHull ℝ (⋃ i, C i)) =
        ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := hcore.2
    _ =
        ⋃ (lam : {lam : Fin m → ℝ // (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1}),
          weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) := by
            simpa using
              (helperForTheorem_19_6_iUnionWeights_eq_weightedSumSubtype
                (n := n) (m := m) (C := C))



end Section19
end Chap19
