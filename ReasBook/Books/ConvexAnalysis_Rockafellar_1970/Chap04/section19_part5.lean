/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19
set_option maxHeartbeats 400000 in
/-- Helper for Corollary 19.1.2: packing coefficient-representation data into finite
generation of the transformed epigraph. -/
lemma helperForCorollary_19_1_2_pack_transformedEpigraph_from_functionRepresentation
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    IsFinitelyGeneratedConvexSet (n + 1)
      ((fun p => (prodLinearEquiv_append_coord (n := n)) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  classical
  have hkm : k + (m - k) = m := Nat.add_sub_of_le hk
  let castKM : Fin (k + (m - k)) → Fin m := Fin.cast hkm
  let leftIdx : Fin k → Fin m := fun i => castKM (Fin.castAdd (m - k) i)
  let rightIdx : Fin (m - k) → Fin m := fun j => castKM (Fin.natAdd k j)
  let pPack : Fin k → Fin (n + 1) → ℝ :=
    fun i =>
      (prodLinearEquiv_append_coord (n := n)) (a (leftIdx i), α (leftIdx i))
  let dPack : Fin (1 + (m - k)) → Fin (n + 1) → ℝ :=
    Fin.append
      (fun _ : Fin 1 =>
        (prodLinearEquiv_append_coord (n := n)) ((0 : Fin n → ℝ), (1 : ℝ)))
      (fun j =>
        (prodLinearEquiv_append_coord (n := n)) (a (rightIdx j), α (rightIdx j)))
  let M : Set (Fin (n + 1) → ℝ) :=
    mixedConvexHull (n := n + 1) (Set.range pPack) (Set.range dPack)
  refine ⟨Set.range pPack, Set.range dPack, Set.finite_range _, Set.finite_range _, ?_⟩
  change
    ((fun p => (prodLinearEquiv_append_coord (n := n)) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) f) = M
  ext y
  constructor
  · intro hy
    rcases hy with ⟨q, hqepi, rfl⟩
    rcases q with ⟨x, μ⟩
    have hfx_le_mu : f x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := f)).1 hqepi
    have hsum_left_eq_filter :
        ∀ lam0 : Fin m → ℝ,
          (∑ i : Fin k, lam0 (leftIdx i)) =
            Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)) (fun i => lam0 i) := by
      intro lam0
      let e : Fin (k + (m - k)) ≃ Fin m := finCongr hkm
      have hleft_from_cast :
          (∑ i : Fin k, lam0 (leftIdx i)) =
            (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
              (fun i => lam0 (castKM i))) := by
        have hsum_castAdd :
            (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
              (fun i => lam0 (castKM i))) =
              ∑ i : Fin k,
                (fun j : Fin (k + (m - k)) => lam0 (castKM j))
                  (Fin.castAdd (m - k) i) := by
          let emb : Fin k ↪ Fin (k + (m - k)) :=
            ⟨Fin.castAdd (m - k), by
              intro i j hij
              simpa using hij⟩
          have hfilter :
              (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k)) =
                Finset.univ.map emb := by
            ext i
            constructor
            · intro hi
              have hik : (i : ℕ) < k := (Finset.mem_filter.mp hi).2
              refine Finset.mem_map.mpr ?_
              refine ⟨i.castLT hik, ?_, ?_⟩
              · simp
              · exact Fin.castAdd_castLT (m - k) i hik
            · intro hi
              rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
              subst hji
              exact Finset.mem_filter.mpr ⟨by simp, Fin.castAdd_lt (m - k) j⟩
          calc
            (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
              (fun i => lam0 (castKM i)))
                = Finset.sum (Finset.univ.map emb) (fun i => lam0 (castKM i)) := by
                    simpa [hfilter]
            _ =
                ∑ i : Fin k,
                  (fun j : Fin (k + (m - k)) => lam0 (castKM j))
                    (Fin.castAdd (m - k) i) := by
                    simp [emb]
        calc
          (∑ i : Fin k, lam0 (leftIdx i))
              = ∑ i : Fin k, (fun j : Fin (k + (m - k)) => lam0 (castKM j))
                  (Fin.castAdd (m - k) i) := by
                  simp [leftIdx]
          _ =
              (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
                (fun i => lam0 (castKM i))) := by
                simpa using hsum_castAdd.symm
      have htransport :
          (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam0 (e i) else 0) =
            (∑ j : Fin m, if (j : ℕ) < k then lam0 j else 0) := by
        simpa [e] using
          (Equiv.sum_comp e (fun j : Fin m => if (j : ℕ) < k then lam0 j else 0))
      have htransport' :
          (∑ i : Fin (k + (m - k)), if (i : ℕ) < k then lam0 (castKM i) else 0) =
            (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam0 (e i) else 0) := by
        simp [e, castKM]
      have hfilter_cast :
          (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
            (fun i => lam0 (castKM i))) =
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam0 i)) := by
        calc
          (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
            (fun i => lam0 (castKM i)))
              = (∑ i : Fin (k + (m - k)), if (i : ℕ) < k then lam0 (castKM i) else 0) := by
                  simp [Finset.sum_filter]
          _ = (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam0 (e i) else 0) :=
                htransport'
          _ = (∑ j : Fin m, if (j : ℕ) < k then lam0 j else 0) := htransport
          _ =
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam0 i)) := by
                  simp [Finset.sum_filter]
      exact hleft_from_cast.trans hfilter_cast
    have hstrict_mem :
        ∀ {x0 : Fin n → ℝ} {μ0 : ℝ},
          f x0 < (μ0 : EReal) →
            (prodLinearEquiv_append_coord (n := n)) (x0, μ0) ∈ M := by
      intro x0 μ0 hfx_lt
      rcases
          helperForCorollary_19_1_2_exists_feasibleCoeffs_lt_mu
            (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
            hrepr (x := x0) (μ := μ0) hfx_lt with
        ⟨lam, hlin, hnorm, hnonneg, hobj_lt⟩
      let q : ℝ := ∑ i, lam i * α i
      have hq_lt_mu : q < μ0 := by
        exact_mod_cast hobj_lt
      let aCoeff : Fin k → ℝ := fun i => lam (leftIdx i)
      let bCoeff : Fin (1 + (m - k)) → ℝ :=
        Fin.append (fun _ : Fin 1 => μ0 - q) (fun j => lam (rightIdx j))
      let preP : Fin k → (Fin n → ℝ) × ℝ :=
        fun i => (a (leftIdx i), α (leftIdx i))
      let preD : Fin (1 + (m - k)) → (Fin n → ℝ) × ℝ :=
        Fin.append
          (fun _ : Fin 1 => ((0 : Fin n → ℝ), (1 : ℝ)))
          (fun j => (a (rightIdx j), α (rightIdx j)))
      have ha_nonneg : ∀ i, 0 ≤ aCoeff i := by
        intro i
        simpa [aCoeff] using hnonneg (leftIdx i)
      have hb_nonneg : ∀ j, 0 ≤ bCoeff j := by
        intro j
        exact Fin.addCases
          (fun j0 => by
            have hq_le_mu : q ≤ μ0 := hq_lt_mu.le
            simpa [bCoeff] using sub_nonneg.mpr hq_le_mu)
          (fun j0 => by
            simpa [bCoeff] using hnonneg (rightIdx j0))
          j
      have hsum_a : (∑ i, aCoeff i) = 1 := by
        calc
          (∑ i, aCoeff i)
              = Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)) (fun i => lam i) :=
                hsum_left_eq_filter lam
          _ = 1 := hnorm
      have hsum_split_coord :
          ∀ j0,
            (∑ i : Fin m, lam i * a i j0) =
              (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
        intro j0
        let g : Fin (k + (m - k)) → ℝ := fun i => lam (castKM i) * a (castKM i) j0
        have hsum_cast :
            (∑ i : Fin (k + (m - k)), g i) = (∑ i : Fin m, lam i * a i j0) := by
          simpa [g, castKM] using
            (Equiv.sum_comp (finCongr hkm) (fun i : Fin m => lam i * a i j0))
        calc
          (∑ i : Fin m, lam i * a i j0) = (∑ i : Fin (k + (m - k)), g i) := by
            simpa using hsum_cast.symm
          _ =
              (∑ i : Fin k, g (Fin.castAdd (m - k) i)) +
                (∑ j : Fin (m - k), g (Fin.natAdd k j)) := by
                simpa using (Fin.sum_univ_add (f := g))
          _ =
              (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
                simp [g, leftIdx, rightIdx]
      have hsum_split_obj :
          (∑ i : Fin m, lam i * α i : ℝ) =
            (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
              (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
        let g : Fin (k + (m - k)) → ℝ := fun i => lam (castKM i) * α (castKM i)
        have hsum_cast :
            (∑ i : Fin (k + (m - k)), g i) = (∑ i : Fin m, lam i * α i : ℝ) := by
          simpa [g, castKM] using
            (Equiv.sum_comp (finCongr hkm) (fun i : Fin m => lam i * α i))
        calc
          (∑ i : Fin m, lam i * α i : ℝ) = (∑ i : Fin (k + (m - k)), g i) := by
            simpa using hsum_cast.symm
          _ =
              (∑ i : Fin k, g (Fin.castAdd (m - k) i)) +
                (∑ j : Fin (m - k), g (Fin.natAdd k j)) := by
                simpa using (Fin.sum_univ_add (f := g))
          _ =
              (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
                (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
                simp [g, leftIdx, rightIdx]
      have hpair :
          (x0, μ0) =
            (∑ i, aCoeff i • preP i) + (∑ j, bCoeff j • preD j) := by
        apply Prod.ext
        · ext j0
          have hsum_dir_fst :
              (∑ j, bCoeff j * (preD j).1 j0) =
                (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
            calc
              (∑ j, bCoeff j * (preD j).1 j0)
                  =
                    (∑ j : Fin 1,
                        bCoeff (Fin.castAdd (m - k) j) * (preD (Fin.castAdd (m - k) j)).1 j0) +
                      (∑ j : Fin (m - k),
                        bCoeff (Fin.natAdd 1 j) * (preD (Fin.natAdd 1 j)).1 j0) := by
                      simpa using
                        (Fin.sum_univ_add
                          (f := fun j : Fin (1 + (m - k)) => bCoeff j * (preD j).1 j0))
              _ = (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
                    simp [bCoeff, preD, rightIdx]
          have hxj := hlin j0
          calc
            x0 j0 = (∑ i : Fin m, lam i * a i j0) := by
              simpa [hxj] using hxj.symm
            _ =
                (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                  (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) :=
                hsum_split_coord j0
            _ =
                (∑ i, aCoeff i * (preP i).1 j0) +
                  (∑ j, bCoeff j * (preD j).1 j0) := by
                  simp [aCoeff, preP, hsum_dir_fst]
            _ = (((∑ i, aCoeff i • preP i) + (∑ j, bCoeff j • preD j)).1) j0 := by
                  simp [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
        · have hsum_dir_snd :
              (∑ j, bCoeff j * (preD j).2) =
                (μ0 - q) + (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
            calc
              (∑ j, bCoeff j * (preD j).2)
                  =
                    (∑ j : Fin 1,
                        bCoeff (Fin.castAdd (m - k) j) * (preD (Fin.castAdd (m - k) j)).2) +
                      (∑ j : Fin (m - k),
                        bCoeff (Fin.natAdd 1 j) * (preD (Fin.natAdd 1 j)).2) := by
                      simpa using
                        (Fin.sum_univ_add
                          (f := fun j : Fin (1 + (m - k)) => bCoeff j * (preD j).2))
              _ = (μ0 - q) + (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
                    simp [bCoeff, preD, rightIdx]
          have hμ_eq : μ0 = q + (μ0 - q) := by ring
          calc
            μ0 = q + (μ0 - q) := hμ_eq
            _ = ((∑ i : Fin m, lam i * α i : ℝ) + (μ0 - q)) := by simp [q]
            _ =
                ((∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
                  (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j))) +
                    (μ0 - q) := by
                    simp [hsum_split_obj]
            _ =
                (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
                  ((μ0 - q) + (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j))) := by
                    ring
            _ = (∑ i, aCoeff i * (preP i).2) + (∑ j, bCoeff j * (preD j).2) := by
                  simp [aCoeff, preP, hsum_dir_snd]
            _ = (((∑ i, aCoeff i • preP i) + (∑ j, bCoeff j • preD j)).2) := by
                  simp [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
      have hy_repr :
          (prodLinearEquiv_append_coord (n := n)) (x0, μ0) =
            (∑ i, aCoeff i • pPack i) + (∑ j, bCoeff j • dPack j) := by
        have hsumP :
            (∑ i, aCoeff i • (prodLinearEquiv_append_coord (n := n)) (preP i)) =
              (∑ i, aCoeff i • pPack i) := by
          simp [pPack, preP]
        have hsumD :
            (∑ j, bCoeff j • (prodLinearEquiv_append_coord (n := n)) (preD j)) =
              (∑ j, bCoeff j • dPack j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hpreD :
              (prodLinearEquiv_append_coord (n := n)) (preD j) = dPack j := by
            exact Fin.addCases
              (fun j0 => by
                fin_cases j0
                simp [preD, dPack])
              (fun j0 => by
                simp [preD, dPack])
              j
          simp [hpreD]
        calc
          (prodLinearEquiv_append_coord (n := n)) (x0, μ0)
              = (prodLinearEquiv_append_coord (n := n))
                  ((∑ i, aCoeff i • preP i) + (∑ j, bCoeff j • preD j)) := by
                    simpa [hpair]
          _ = (∑ i, aCoeff i • (prodLinearEquiv_append_coord (n := n)) (preP i)) +
                (∑ j, bCoeff j • (prodLinearEquiv_append_coord (n := n)) (preD j)) := by
                  simp
          _ = (∑ i, aCoeff i • pPack i) + (∑ j, bCoeff j • dPack j) := by
                simp [hsumP, hsumD]
      exact
        mem_mixedConvexHull_range_of_exists_coeffs
          (n := n + 1) (p := pPack) (d := dPack)
          (y := (prodLinearEquiv_append_coord (n := n)) (x0, μ0))
          aCoeff bCoeff ha_nonneg hb_nonneg hsum_a hy_repr
    have hpolyM : IsPolyhedralConvexSet (n + 1) M :=
      helperForTheorem_19_1_mixedConvexHull_polyhedral_of_finite_generators
        (n := n + 1) (S₀ := Set.range pPack) (S₁ := Set.range dPack)
        (Set.finite_range _) (Set.finite_range _)
    have hclosedM : IsClosed M :=
      (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
        (n := n + 1) (C := M) hpolyM).1
    have hdiv : Filter.Tendsto (fun t : ℕ => (1 : ℝ) / (t + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hμ_tendsto :
        Filter.Tendsto (fun t : ℕ => μ + (1 : ℝ) / (t + 1)) Filter.atTop (𝓝 μ) := by
      simpa [add_comm, add_left_comm, add_assoc] using hdiv.const_add μ
    have hpair_tendsto :
        Filter.Tendsto (fun t : ℕ => (x, μ + (1 : ℝ) / (t + 1))) Filter.atTop (𝓝 (x, μ)) := by
      have hpair' :
          Filter.Tendsto (fun t : ℕ => (x, μ + (1 : ℝ) / (t + 1))) Filter.atTop
            (𝓝 x ×ˢ 𝓝 μ) :=
        tendsto_const_nhds.prodMk hμ_tendsto
      simpa [nhds_prod_eq] using hpair'
    have htrans_tendsto :
        Filter.Tendsto
          (fun t : ℕ => (prodLinearEquiv_append_coord (n := n)) (x, μ + (1 : ℝ) / (t + 1)))
          Filter.atTop
          (𝓝 ((prodLinearEquiv_append_coord (n := n)) (x, μ))) := by
      let eCL : ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
        (prodLinearEquiv_append_coord (n := n)).toContinuousLinearEquiv
      have hcontAt : ContinuousAt eCL (x, μ) := eCL.continuous.continuousAt
      exact hcontAt.tendsto.comp hpair_tendsto
    have hmem_eventually :
        ∀ᶠ t : ℕ in Filter.atTop,
          (prodLinearEquiv_append_coord (n := n)) (x, μ + (1 : ℝ) / (t + 1)) ∈ M := by
      refine Filter.Eventually.of_forall ?_
      intro t
      have hμ_lt : (μ : EReal) < (((μ + (1 : ℝ) / (t + 1)) : ℝ) : EReal) := by
        have hpos : (0 : ℝ) < (1 : ℝ) / (t + 1) := by
          exact one_div_pos.mpr (Nat.cast_add_one_pos t)
        exact_mod_cast (lt_add_of_pos_right μ hpos)
      exact
        hstrict_mem (x0 := x) (μ0 := μ + (1 : ℝ) / (t + 1))
          (lt_of_le_of_lt hfx_le_mu hμ_lt)
    exact IsClosed.mem_of_tendsto hclosedM htrans_tendsto hmem_eventually
  · intro hy
    let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
    have hyq : (prodLinearEquiv_append_coord (n := n)) q = y := by
      simp [q]
    rcases q with ⟨x, μ⟩
    simp at hyq
    have hy' : (prodLinearEquiv_append_coord (n := n)) (x, μ) ∈ M := by
      simpa [hyq] using hy
    have hdecode :
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          ((∑ i, lam i * α i : ℝ) : EReal) ≤ (μ : EReal) := by
      rcases
          exists_strict_mixedConvexCombination_of_mem_mixedConvexHull
            (n := n + 1) (S₀ := Set.range pPack) (S₁ := Set.range dPack)
            (x := (prodLinearEquiv_append_coord (n := n)) (x, μ)) hy' with
        ⟨k', m', p', d', a', b', hp', hd', ha', hb', hsum', hy_repr'⟩
      choose ip hip using hp'
      choose id hid using hd'
      let aFix : Fin k → ℝ :=
        fun i =>
          Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i)) (fun t => a' t)
      let bFix : Fin (1 + (m - k)) → ℝ :=
        fun j =>
          Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j)) (fun t => b' t)
      have haFix_nonneg : ∀ i, 0 ≤ aFix i := by
        intro i
        unfold aFix
        refine Finset.sum_nonneg ?_
        intro t ht
        exact le_of_lt (ha' t)
      have hbFix_nonneg : ∀ j, 0 ≤ bFix j := by
        intro j
        unfold bFix
        refine Finset.sum_nonneg ?_
        intro t ht
        exact le_of_lt (hb' t)
      have hy_repr_fixed :
          (prodLinearEquiv_append_coord (n := n)) (x, μ) =
            (∑ i, aFix i • pPack i) + (∑ j, bFix j • dPack j) := by
        have hsum_points :
            (∑ i, aFix i • pPack i) = ∑ t, a' t • pPack (ip t) := by
          unfold aFix
          calc
            (∑ i,
              (Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i))
                (fun t => a' t)) • pPack i)
                = ∑ i, Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i))
                    (fun t => a' t • pPack i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simpa using
                        (Finset.sum_smul
                          (s := Finset.univ.filter (fun u : Fin k' => ip u = i))
                          (f := fun t : Fin k' => a' t) (x := pPack i))
            _ = ∑ i, ∑ t, (if ip t = i then a' t • pPack i else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simpa using
                    (Finset.sum_filter (s := (Finset.univ : Finset (Fin k')))
                      (p := fun u : Fin k' => ip u = i)
                      (f := fun t : Fin k' => a' t • pPack i))
            _ = ∑ t, ∑ i, (if ip t = i then a' t • pPack i else 0) := by
                  simpa [Finset.sum_comm]
            _ = ∑ t, a' t • pPack (ip t) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  simp
        have hsum_dirs :
            (∑ j, bFix j • dPack j) = ∑ t, b' t • dPack (id t) := by
          unfold bFix
          calc
            (∑ j,
              (Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j))
                (fun t => b' t)) • dPack j)
                = ∑ j, Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j))
                    (fun t => b' t • dPack j) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      simpa using
                        (Finset.sum_smul
                          (s := Finset.univ.filter (fun u : Fin m' => id u = j))
                          (f := fun t : Fin m' => b' t) (x := dPack j))
            _ = ∑ j, ∑ t, (if id t = j then b' t • dPack j else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simpa using
                    (Finset.sum_filter (s := (Finset.univ : Finset (Fin m')))
                      (p := fun u : Fin m' => id u = j)
                      (f := fun t : Fin m' => b' t • dPack j))
            _ = ∑ t, ∑ j, (if id t = j then b' t • dPack j else 0) := by
                  simpa [Finset.sum_comm]
            _ = ∑ t, b' t • dPack (id t) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  simp
        have hsum_points' : (∑ t, a' t • pPack (ip t)) = (∑ t, a' t • p' t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simpa [hip t]
        have hsum_dirs' : (∑ t, b' t • dPack (id t)) = (∑ t, b' t • d' t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simpa [hid t]
        calc
          (prodLinearEquiv_append_coord (n := n)) (x, μ)
              = (∑ t, a' t • p' t) + (∑ t, b' t • d' t) := hy_repr'
          _ = (∑ t, a' t • pPack (ip t)) + (∑ t, b' t • dPack (id t)) := by
                simp [hsum_points', hsum_dirs']
          _ = (∑ i, aFix i • pPack i) + (∑ j, bFix j • dPack j) := by
                simp [hsum_points, hsum_dirs]
      have hsum_aFix : (∑ i, aFix i) = 1 := by
        unfold aFix
        calc
          (∑ i,
              Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i)) (fun t => a' t))
              = ∑ i, ∑ t, (if ip t = i then a' t else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simpa using
                    (Finset.sum_filter (s := (Finset.univ : Finset (Fin k')))
                      (p := fun u : Fin k' => ip u = i) (f := fun t : Fin k' => a' t))
          _ = ∑ t, ∑ i, (if ip t = i then a' t else 0) := by
                simpa [Finset.sum_comm]
          _ = ∑ t, a' t := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                simp
          _ = 1 := hsum'
      have hpair :
          (x, μ) =
            (∑ i, aFix i • ((prodLinearEquiv_append_coord (n := n)).symm (pPack i))) +
              (∑ j, bFix j • ((prodLinearEquiv_append_coord (n := n)).symm (dPack j))) := by
        have hmap := congrArg (fun y => (prodLinearEquiv_append_coord (n := n)).symm y) hy_repr_fixed
        simpa using hmap
      let lamDec : Fin (k + (m - k)) → ℝ :=
        Fin.append aFix (fun j => bFix (Fin.natAdd 1 j))
      let lam : Fin m → ℝ := fun i => lamDec ((finCongr hkm).symm i)
      have hlam_left : ∀ i : Fin k, lam (leftIdx i) = aFix i := by
        intro i
        simp [lam, lamDec, leftIdx, castKM]
      have hlam_right : ∀ j : Fin (m - k), lam (rightIdx j) = bFix (Fin.natAdd 1 j) := by
        intro j
        simp [lam, lamDec, rightIdx, castKM]
      have hsum_split_coord :
          ∀ j0,
            (∑ i : Fin m, lam i * a i j0) =
              (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
        intro j0
        let g : Fin (k + (m - k)) → ℝ := fun i => lam (castKM i) * a (castKM i) j0
        have hsum_cast :
            (∑ i : Fin (k + (m - k)), g i) = (∑ i : Fin m, lam i * a i j0) := by
          simpa [g, castKM] using
            (Equiv.sum_comp (finCongr hkm) (fun i : Fin m => lam i * a i j0))
        calc
          (∑ i : Fin m, lam i * a i j0) = (∑ i : Fin (k + (m - k)), g i) := by
            simpa using hsum_cast.symm
          _ =
              (∑ i : Fin k, g (Fin.castAdd (m - k) i)) +
                (∑ j : Fin (m - k), g (Fin.natAdd k j)) := by
                simpa using (Fin.sum_univ_add (f := g))
          _ =
              (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) := by
                simp [g, leftIdx, rightIdx]
      have hlin : ∀ j0, (∑ i : Fin m, lam i * a i j0) = x j0 := by
        intro j0
        have hxj :
            x j0 =
              (∑ i : Fin k, aFix i * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
          let preP : Fin k → (Fin n → ℝ) × ℝ :=
            fun i => (prodLinearEquiv_append_coord (n := n)).symm (pPack i)
          let preD : Fin (1 + (m - k)) → (Fin n → ℝ) × ℝ :=
            fun j => (prodLinearEquiv_append_coord (n := n)).symm (dPack j)
          have hsum_dir_fst :
              (∑ j, bFix j * (preD j).1 j0) =
                (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
            calc
              (∑ j, bFix j * (preD j).1 j0)
                  =
                    (∑ j : Fin 1,
                        bFix (Fin.castAdd (m - k) j) * (preD (Fin.castAdd (m - k) j)).1 j0) +
                      (∑ j : Fin (m - k),
                        bFix (Fin.natAdd 1 j) * (preD (Fin.natAdd 1 j)).1 j0) := by
                      simpa using
                        (Fin.sum_univ_add
                          (f := fun j : Fin (1 + (m - k)) => bFix j * (preD j).1 j0))
              _ = (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
                    simp [preD, dPack, rightIdx]
          calc
            x j0
                =
                  (((∑ i, aFix i • preP i) + (∑ j, bFix j • preD j)).1) j0 := by
                    have hfst := congrArg (fun z : (Fin n → ℝ) × ℝ => z.1 j0) hpair
                    simpa using hfst
            _ =
                (∑ i, aFix i * (preP i).1 j0) +
                  (∑ j, bFix j * (preD j).1 j0) := by
                  simp [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
            _ =
                (∑ i : Fin k, aFix i * a (leftIdx i) j0) +
                  (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
                  simp [preP, pPack, hsum_dir_fst]
        calc
          (∑ i : Fin m, lam i * a i j0)
              =
                (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) +
                  (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) :=
              hsum_split_coord j0
          _ =
              (∑ i : Fin k, aFix i * a (leftIdx i) j0) +
                (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
                have hleft_eq :
                    (∑ i : Fin k, lam (leftIdx i) * a (leftIdx i) j0) =
                      (∑ i : Fin k, aFix i * a (leftIdx i) j0) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [hlam_left i]
                have hright_eq :
                    (∑ j : Fin (m - k), lam (rightIdx j) * a (rightIdx j) j0) =
                      (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * a (rightIdx j) j0) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [hlam_right j]
                rw [hleft_eq, hright_eq]
          _ = x j0 := by simpa using hxj.symm
      have hsum_left_eq_filter :
          (∑ i : Fin k, lam (leftIdx i)) =
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) := by
        let e : Fin (k + (m - k)) ≃ Fin m := finCongr hkm
        have hleft_from_cast :
            (∑ i : Fin k, lam (leftIdx i)) =
              (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
                (fun i => lam (castKM i))) := by
          rw [helperForCorollary_19_1_2_sum_filter_lt_eq_sum_castAdd
            (k := k) (m := m - k) (g := fun i => lam (castKM i))]
        have htransport :
            (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam (e i) else 0) =
              (∑ j : Fin m, if (j : ℕ) < k then lam j else 0) := by
          simpa [e] using
            (Equiv.sum_comp e (fun j : Fin m => if (j : ℕ) < k then lam j else 0))
        have htransport' :
            (∑ i : Fin (k + (m - k)), if (i : ℕ) < k then lam (castKM i) else 0) =
              (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam (e i) else 0) := by
          simp [e, castKM]
        have hfilter_cast :
            (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
              (fun i => lam (castKM i))) =
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) := by
          calc
            (Finset.sum (Finset.univ.filter (fun i : Fin (k + (m - k)) => (i : ℕ) < k))
              (fun i => lam (castKM i)))
                = (∑ i : Fin (k + (m - k)), if (i : ℕ) < k then lam (castKM i) else 0) := by
                    simp [Finset.sum_filter]
            _ = (∑ i : Fin (k + (m - k)), if ((e i : Fin m) : ℕ) < k then lam (e i) else 0) :=
                  htransport'
            _ = (∑ j : Fin m, if (j : ℕ) < k then lam j else 0) := htransport
            _ =
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) := by
                    simp [Finset.sum_filter]
        exact hleft_from_cast.trans hfilter_cast
      have hnorm :
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 := by
        calc
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i))
              = (∑ i : Fin k, lam (leftIdx i)) := by
                  simpa using hsum_left_eq_filter.symm
          _ = (∑ i : Fin k, aFix i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hlam_left i]
          _ = 1 := hsum_aFix
      have hlamDec_nonneg : ∀ i : Fin (k + (m - k)), 0 ≤ lamDec i := by
        intro i
        refine Fin.addCases ?_ ?_ i
        · intro i0
          simpa [lamDec] using haFix_nonneg i0
        · intro j0
          simpa [lamDec] using hbFix_nonneg (Fin.natAdd 1 j0)
      have hnonneg : ∀ i, 0 ≤ lam i := by
        intro i
        have hi_nonneg := hlamDec_nonneg ((finCongr hkm).symm i)
        simpa [lam] using hi_nonneg
      have hsum_split_obj :
          (∑ i : Fin m, lam i * α i : ℝ) =
            (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
              (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
        let g : Fin (k + (m - k)) → ℝ := fun i => lam (castKM i) * α (castKM i)
        have hsum_cast :
            (∑ i : Fin (k + (m - k)), g i) = (∑ i : Fin m, lam i * α i : ℝ) := by
          simpa [g, castKM] using
            (Equiv.sum_comp (finCongr hkm) (fun i : Fin m => lam i * α i))
        calc
          (∑ i : Fin m, lam i * α i : ℝ) = (∑ i : Fin (k + (m - k)), g i) := by
            simpa using hsum_cast.symm
          _ =
              (∑ i : Fin k, g (Fin.castAdd (m - k) i)) +
                (∑ j : Fin (m - k), g (Fin.natAdd k j)) := by
                simpa using (Fin.sum_univ_add (f := g))
          _ =
              (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
                (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := by
                simp [g, leftIdx, rightIdx]
      have hobj_core :
          (∑ i : Fin m, lam i * α i : ℝ) =
            (∑ i : Fin k, aFix i * α (leftIdx i)) +
              (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * α (rightIdx j)) := by
        calc
          (∑ i : Fin m, lam i * α i : ℝ)
              =
                (∑ i : Fin k, lam (leftIdx i) * α (leftIdx i)) +
                  (∑ j : Fin (m - k), lam (rightIdx j) * α (rightIdx j)) := hsum_split_obj
          _ =
              (∑ i : Fin k, aFix i * α (leftIdx i)) +
                (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * α (rightIdx j)) := by
                simp [hlam_left, hlam_right]
      have hμ_packed :
          μ =
            (∑ i : Fin (k + (1 + (m - k))),
              (Fin.append aFix bFix i) *
                (Fin.append
                  (fun i => α (leftIdx i))
                  (Fin.append (fun _ : Fin 1 => (1 : ℝ))
                    (fun j => α (rightIdx j)))
                  i)) := by
        have hsnd := congrArg (fun z : (Fin n → ℝ) × ℝ => z.2) hpair
        have hsnd' :
            μ =
              (∑ i : Fin k, aFix i * ((prodLinearEquiv_append_coord (n := n)).symm (pPack i)).2) +
                (∑ j : Fin (1 + (m - k)),
                  bFix j * ((prodLinearEquiv_append_coord (n := n)).symm (dPack j)).2) := by
          simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using hsnd
        have hsnd_dir :
            (fun j : Fin (1 + (m - k)) =>
              ((prodLinearEquiv_append_coord (n := n)).symm (dPack j)).2) =
              Fin.append (fun _ : Fin 1 => (1 : ℝ)) (fun j => α (rightIdx j)) := by
          simpa [dPack] using
            (helperForCorollary_19_1_2_decodeSymmSecondCoord_of_appendPacked
              (n := n) (r := m - k)
              (uLeft := fun _ : Fin 1 => ((0 : Fin n → ℝ), (1 : ℝ)))
              (uRight := fun j : Fin (m - k) => (a (rightIdx j), α (rightIdx j))))
        have hsnd_dir_apply :
            ∀ j : Fin (1 + (m - k)),
              ((prodLinearEquiv_append_coord (n := n)).symm (dPack j)).2 =
                Fin.append (fun _ : Fin 1 => (1 : ℝ)) (fun j => α (rightIdx j)) j := by
          intro j
          simpa using congrArg (fun g : Fin (1 + (m - k)) → ℝ => g j) hsnd_dir
        calc
          μ =
              (∑ i : Fin k, aFix i * α (leftIdx i)) +
                (∑ j : Fin (1 + (m - k)),
                  bFix j * ((prodLinearEquiv_append_coord (n := n)).symm (dPack j)).2) := by
                simpa [pPack] using hsnd'
          _ =
              (∑ i : Fin k, aFix i * α (leftIdx i)) +
                (∑ j : Fin (1 + (m - k)),
                  bFix j *
                    (Fin.append (fun _ : Fin 1 => (1 : ℝ))
                      (fun j => α (rightIdx j)) j)) := by
                refine congrArg (fun t : ℝ => (∑ i : Fin k, aFix i * α (leftIdx i)) + t) ?_
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [hsnd_dir_apply j]
          _ =
              (∑ i : Fin (k + (1 + (m - k))),
                (Fin.append aFix bFix i) *
                  (Fin.append
                    (fun i => α (leftIdx i))
                    (Fin.append (fun _ : Fin 1 => (1 : ℝ))
                      (fun j => α (rightIdx j)))
                    i)) := by
                symm
                simpa using
                  (Fin.sum_univ_add
                    (f := fun i : Fin (k + (1 + (m - k))) =>
                      (Fin.append aFix bFix i) *
                        (Fin.append
                          (fun i => α (leftIdx i))
                          (Fin.append (fun _ : Fin 1 => (1 : ℝ))
                            (fun j => α (rightIdx j)))
                          i)))
      have hμ_decomp :
          μ =
            (∑ i : Fin k, aFix i * α (leftIdx i)) +
              bFix (Fin.castAdd (m - k) (0 : Fin 1)) +
              (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * α (rightIdx j)) := by
        calc
          μ =
              (∑ i : Fin (k + (1 + (m - k))),
                (Fin.append aFix bFix i) *
                  (Fin.append
                    (fun i => α (leftIdx i))
                    (Fin.append (fun _ : Fin 1 => (1 : ℝ))
                      (fun j => α (rightIdx j)))
                    i)) := hμ_packed
          _ =
              (∑ i : Fin k, aFix i * α (leftIdx i)) +
                bFix (Fin.castAdd (m - k) (0 : Fin 1)) +
                (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * α (rightIdx j)) := by
                simpa using
                  helperForCorollary_19_1_2_packedObjectiveSum_eq_originalPlusVertical
                    (k := k) (m := m) aFix bFix
                    (fun i => α (leftIdx i))
                    (fun j => α (rightIdx j))
      let qCore : ℝ := ∑ i : Fin m, lam i * α i
      let tVert : ℝ := bFix (Fin.castAdd (m - k) (0 : Fin 1))
      have hqCore_eq :
          qCore =
            (∑ i : Fin k, aFix i * α (leftIdx i)) +
              (∑ j : Fin (m - k), bFix (Fin.natAdd 1 j) * α (rightIdx j)) := by
        simpa [qCore] using hobj_core
      have hdecomp_eq : qCore + tVert = μ := by
        linarith [hqCore_eq, hμ_decomp]
      have hdecomp_le : qCore + tVert ≤ μ := by
        linarith [hdecomp_eq]
      have hdrop :=
        helperForCorollary_19_1_2_objective_dropVertical_le
          (qCore := qCore) (tVert := tVert) (μ := μ)
          hdecomp_le (by simpa [tVert] using hbFix_nonneg (Fin.castAdd (m - k) (0 : Fin 1)))
      have hobj_le :
          ((∑ i, lam i * α i : ℝ) : EReal) ≤ (μ : EReal) := by
        simpa [qCore] using hdrop.2
      exact ⟨lam, hlin, hnorm, hnonneg, hobj_le⟩
    have hmem_img :
        (prodLinearEquiv_append_coord (n := n)) (x, μ) ∈
          ((fun p => (prodLinearEquiv_append_coord (n := n)) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
      helperForCorollary_19_1_2_mem_transformedEpigraphImage_of_decodedFeasible
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hrepr (x := x) (μ := μ) hdecode
    exact hyq ▸ hmem_img

/-- Helper for Corollary 19.1.2: from mixed-hull membership with finite families,
extract fixed-index nonnegative coefficients for the point and direction families. -/
lemma helperForCorollary_19_1_2_exists_fixedCoeffs_of_mem_mixedConvexHull_rangeEarly
    {n k m : ℕ} (p : Fin k → Fin n → ℝ) (d : Fin m → Fin n → ℝ) {y : Fin n → ℝ}
    (hy : y ∈ mixedConvexHull (n := n) (Set.range p) (Set.range d)) :
    ∃ a : Fin k → ℝ, ∃ b : Fin m → ℝ,
      (∀ i, 0 ≤ a i) ∧
      (∀ j, 0 ≤ b j) ∧
      (∑ i, a i) = 1 ∧
      y = (∑ i, a i • p i) + (∑ j, b j • d j) := by
  classical
  rcases
      exists_strict_mixedConvexCombination_of_mem_mixedConvexHull
        (n := n) (S₀ := Set.range p) (S₁ := Set.range d) (x := y) hy with
    ⟨k', m', p', d', a', b', hp', hd', ha', hb', hsum', hy'⟩
  choose ip hip using hp'
  choose id hid using hd'
  let a : Fin k → ℝ :=
    fun i =>
      Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i)) (fun t => a' t)
  let b : Fin m → ℝ :=
    fun j =>
      Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j)) (fun t => b' t)
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    unfold a
    refine Finset.sum_nonneg ?_
    intro t ht
    exact le_of_lt (ha' t)
  have hb_nonneg : ∀ j, 0 ≤ b j := by
    intro j
    unfold b
    refine Finset.sum_nonneg ?_
    intro t ht
    exact le_of_lt (hb' t)
  have hsum_a : (∑ i, a i) = 1 := by
    unfold a
    calc
      (∑ i, Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i)) (fun t => a' t))
          = ∑ i, ∑ t, (if ip t = i then a' t else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using
                (Finset.sum_filter (s := (Finset.univ : Finset (Fin k')))
                  (p := fun u : Fin k' => ip u = i) (f := fun t : Fin k' => a' t))
      _ = ∑ t, ∑ i, (if ip t = i then a' t else 0) := by
            simpa [Finset.sum_comm]
      _ = ∑ t, a' t := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp
      _ = 1 := hsum'
  have hsum_points :
      (∑ i, a i • p i) = ∑ t, a' t • p (ip t) := by
    unfold a
    calc
      (∑ i,
        (Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i)) (fun t => a' t)) • p i)
          = ∑ i, Finset.sum (Finset.univ.filter (fun u : Fin k' => ip u = i))
              (fun t => a' t • p i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using
                (Finset.sum_smul
                  (s := Finset.univ.filter (fun u : Fin k' => ip u = i))
                  (f := fun t : Fin k' => a' t) (x := p i))
      _ = ∑ i, ∑ t, (if ip t = i then a' t • p i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using
              (Finset.sum_filter (s := (Finset.univ : Finset (Fin k')))
                (p := fun u : Fin k' => ip u = i)
                (f := fun t : Fin k' => a' t • p i))
      _ = ∑ t, ∑ i, (if ip t = i then a' t • p i else 0) := by
            simpa [Finset.sum_comm]
      _ = ∑ t, a' t • p (ip t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp
  have hsum_dirs :
      (∑ j, b j • d j) = ∑ t, b' t • d (id t) := by
    unfold b
    calc
      (∑ j,
        (Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j)) (fun t => b' t)) • d j)
          = ∑ j, Finset.sum (Finset.univ.filter (fun u : Fin m' => id u = j))
              (fun t => b' t • d j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simpa using
                (Finset.sum_smul
                  (s := Finset.univ.filter (fun u : Fin m' => id u = j))
                  (f := fun t : Fin m' => b' t) (x := d j))
      _ = ∑ j, ∑ t, (if id t = j then b' t • d j else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa using
              (Finset.sum_filter (s := (Finset.univ : Finset (Fin m')))
                (p := fun u : Fin m' => id u = j)
                (f := fun t : Fin m' => b' t • d j))
      _ = ∑ t, ∑ j, (if id t = j then b' t • d j else 0) := by
            simpa [Finset.sum_comm]
      _ = ∑ t, b' t • d (id t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp
  have hsum_points' :
      (∑ t, a' t • p (ip t)) = (∑ t, a' t • p' t) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simpa [hip t]
  have hsum_dirs' :
      (∑ t, b' t • d (id t)) = (∑ t, b' t • d' t) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simpa [hid t]
  refine ⟨a, b, ha_nonneg, hb_nonneg, hsum_a, ?_⟩
  calc
    y = (∑ t, a' t • p' t) + (∑ t, b' t • d' t) := hy'
    _ = (∑ t, a' t • p (ip t)) + (∑ t, b' t • d (id t)) := by
          simp [hsum_points', hsum_dirs']
    _ = (∑ i, a i • p i) + (∑ j, b j • d j) := by
          simp [hsum_points, hsum_dirs]

/-- Helper for Corollary 19.1.2: finite-generation of the transformed epigraph yields a
polyhedral convex function. -/
lemma helperForCorollary_19_1_2_polyhedralFunction_of_epigraphFG
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hfg_epi :
      IsFinitelyGeneratedConvexSet (n + 1)
        ((fun p => (prodLinearEquiv_append_coord (n := n)) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f)) :
    IsPolyhedralConvexFunction n f := by
  let C : Set (Fin (n + 1) → ℝ) :=
    ((fun p => (prodLinearEquiv_append_coord (n := n)) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) f)
  have hconv_epi : Convex ℝ C := by
    simpa [C] using
      (convex_epigraph_of_convexFunctionOn (f := f) (hf := hconv)).linear_image
        (prodLinearEquiv_append_coord (n := n)).toLinearMap
  have hpolyC : IsPolyhedralConvexSet (n + 1) C :=
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := n + 1) (C := C) hconv_epi (by simpa [C] using hfg_epi)
  have hpoly_append :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => (prodLinearEquiv_append (n := n)) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [C, prodLinearEquiv_append_coord] using hpolyC
  exact ⟨hconv, hpoly_append⟩


end Section19
end Chap19
