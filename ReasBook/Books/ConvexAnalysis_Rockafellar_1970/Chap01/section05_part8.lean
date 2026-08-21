/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part7

section Chap01
section Section05

/-- Each epigraph sits inside the convex hull of the union of epigraphs. -/
lemma epigraph_subset_convexHull_union {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) (i : ι) :
    epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) ⊆
      convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
  intro p hp
  have hsubset :
      (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) ⊆
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
    simpa using
      (subset_convexHull (𝕜 := ℝ)
        (s := ⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)))
  exact hsubset (Set.mem_iUnion.mpr ⟨i, hp⟩)

/-- If a convex function lies below each member, then the convex hull of the union of
their epigraphs lies in its epigraph. -/
lemma convexHull_union_subset_epigraph_of_le {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal} {h : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h)
    (h_le_f : ∀ i, h ≤ f i) :
    convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) h := by
  have hsubset :
      (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) h := by
    intro p hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    have hsubset_i :
        epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) ⊆
          epigraph (S := (Set.univ : Set (Fin n → Real))) h :=
      epigraph_subset_epigraph_of_le (h := h) (g := f i) (h_le_g := h_le_f i)
    exact hsubset_i hi
  have hconv :
      Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) h) :=
    convex_epigraph_of_convexFunctionOn (f := h) hh
  exact convexHull_min hsubset hconv

/-- The `EReal` infimum of a coerced real set matches the coerced real infimum
under nonemptiness and bounded-below hypotheses. -/
lemma sInf_coe_image_eq_sInf_real {A : Set ℝ} (hne : A.Nonempty) (hbdd : BddBelow A) :
    sInf ((fun μ : ℝ => (μ : EReal)) '' A) = ((sInf A : ℝ) : EReal) := by
  classical
  set S : Set EReal := (fun μ : ℝ => (μ : EReal)) '' A
  have hle : ((sInf A : ℝ) : EReal) ≤ sInf S := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨r, hr, rfl⟩
    have hle' : sInf A ≤ r := csInf_le hbdd hr
    exact (EReal.coe_le_coe_iff).2 hle'
  have hge : sInf S ≤ ((sInf A : ℝ) : EReal) := by
    have hSne : S.Nonempty := by
      rcases hne with ⟨r, hr⟩
      exact ⟨(r : EReal), ⟨r, hr, rfl⟩⟩
    have hnot_top : sInf S ≠ (⊤ : EReal) := by
      rcases hSne with ⟨z, hz⟩
      rcases hz with ⟨r, hr, rfl⟩
      intro htop
      have hle' : sInf S ≤ (r : EReal) := sInf_le ⟨r, hr, rfl⟩
      rw [htop] at hle'
      exact (not_top_le_coe r) hle'
    rcases hbdd with ⟨m, hm⟩
    have hmS : (m : EReal) ≤ sInf S := by
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨r, hr, rfl⟩
      exact (EReal.coe_le_coe_iff).2 (hm hr)
    have hnot_bot : sInf S ≠ (⊥ : EReal) := by
      intro hbot
      have hmS' : (m : EReal) ≤ (⊥ : EReal) := by
        have hmS'' := hmS
        simp [hbot] at hmS''
      exact (not_le_of_gt (EReal.bot_lt_coe m)) hmS'
    have hlower : ∀ r ∈ A, (sInf S).toReal ≤ r := by
      intro r hr
      have hle' : sInf S ≤ (r : EReal) := sInf_le ⟨r, hr, rfl⟩
      exact EReal.toReal_le_toReal hle' hnot_bot (EReal.coe_ne_top r)
    have hle_real : (sInf S).toReal ≤ (sInf A : ℝ) :=
      le_csInf hne (by intro r hr; exact hlower r hr)
    have hcoe :
        ((sInf S).toReal : EReal) ≤ ((sInf A : ℝ) : EReal) :=
      (EReal.coe_le_coe_iff).2 hle_real
    have hcoe_eq : ((sInf S).toReal : EReal) = (sInf S : EReal) :=
      EReal.coe_toReal hnot_top hnot_bot
    simpa [hcoe_eq] using hcoe
  exact le_antisymm hge hle

/-- Membership in the convex hull of a union of epigraphs gives a finite convex combination
of epigraph points with explicit indices. -/
lemma mem_convexHull_union_epigraph_iff_fin_combo {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal} {x : Fin n → Real} {μ : Real} :
    (x, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) ↔
      ∃ (m : Nat) (idx : Fin m → ι) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real))
        (μ' : Fin m → Real),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        (Finset.univ.sum (fun i => lam i * μ' i) = μ) ∧
        (∀ i, f (idx i) (x' i) ≤ (μ' i : EReal)) := by
  classical
  constructor
  · intro hx
    rcases
        (mem_convexHull_iff_exists_fintype (R := Real)
            (s := ⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
            (x := (x, μ))).1 hx with
      ⟨ι0, _inst, w, z, hw0, hw1, hz, hsum⟩
    let e : ι0 ≃ Fin (Fintype.card ι0) := Fintype.equivFin ι0
    refine
      ⟨Fintype.card ι0,
        (fun i => Classical.choose (Set.mem_iUnion.1 (hz (e.symm i)))),
        (fun i => w (e.symm i)),
        (fun i => (z (e.symm i)).1),
        (fun i => (z (e.symm i)).2),
        ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hw0 (e.symm i)
    · have hsum' : (∑ i, w (e.symm i)) = ∑ i, w i := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i))
      simpa [hsum'] using hw1
    · have hsum_fst : (∑ i, w i • (z i).1) = x := by
        have h := congrArg Prod.fst hsum
        have h' :
            Finset.univ.sum (fun i => (w i • z i).1) = x := by
          simpa [fst_sum (s := Finset.univ) (f := fun i => w i • z i)] using h
        simpa using h'
      have hsum' :
          (∑ i, w (e.symm i) • (z (e.symm i)).1) = ∑ i, w i • (z i).1 := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i • (z i).1))
      simpa [hsum'] using hsum_fst
    · have hsum_snd : (∑ i, w i • (z i).2) = μ := by
        have h := congrArg Prod.snd hsum
        have h' :
            Finset.univ.sum (fun i => (w i • z i).2) = μ := by
          simpa [snd_sum (s := Finset.univ) (f := fun i => w i • z i)] using h
        simpa [smul_eq_mul] using h'
      have hsum' :
          (∑ i, w (e.symm i) * (z (e.symm i)).2) = ∑ i, w i * (z i).2 := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i • (z i).2))
      have hsum_snd' : (∑ i, w i * (z i).2) = μ := by
        simpa [smul_eq_mul] using hsum_snd
      simpa [hsum'] using hsum_snd'
    · intro i
      have hz' :
          z (e.symm i) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real)))
              (f (Classical.choose (Set.mem_iUnion.1 (hz (e.symm i))))) := by
        have h := Classical.choose_spec (Set.mem_iUnion.1 (hz (e.symm i)))
        simpa using h
      exact (mem_epigraph_univ_iff (f := f
        (Classical.choose (Set.mem_iUnion.1 (hz (e.symm i)))))).1 hz'
  · rintro ⟨m, idx, lam, x', μ', h0, hsum1, hsumx, hsumμ, hle⟩
    refine
      mem_convexHull_of_exists_fintype
        (s := ⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
        (x := (x, μ)) (w := lam) (z := fun i => (x' i, μ' i)) ?_ ?_ ?_ ?_
    · intro i
      exact h0 i
    · simpa using hsum1
    · intro i
      exact Set.mem_iUnion.2 ⟨idx i,
        (mem_epigraph_univ_iff (f := f (idx i))).2 (hle i)⟩
    · apply Prod.ext
      · have hsum_fst :
          (Finset.univ.sum (fun i => (lam i • x' i, lam i * μ' i))).1 =
            Finset.univ.sum (fun i => lam i • x' i) := by
          simp [fst_sum (s := Finset.univ)
            (f := fun i => (lam i • x' i, lam i * μ' i))]
        simpa [hsum_fst] using hsumx
      · have hsum_snd :
          (Finset.univ.sum (fun i => (lam i • x' i, lam i * μ' i))).2 =
            Finset.univ.sum (fun i => lam i * μ' i) := by
          simp [snd_sum (s := Finset.univ)
            (f := fun i => (lam i • x' i, lam i * μ' i))]
        have hsumμ' : Finset.univ.sum (fun i => lam i * μ' i) = μ := by
          simpa [smul_eq_mul] using hsumμ
        simp [hsum_snd, hsumμ']

/-- From properness, there exists a point where the value is not `⊤`. -/
lemma exists_point_ne_top_of_proper {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) :
    ∃ x, f x ≠ ⊤ := by
  rcases hproper with ⟨_, hne, _⟩
  rcases hne with ⟨p, hp⟩
  refine ⟨p.1, ?_⟩
  have hle : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
  intro htop
  have hle' := hle
  rw [htop] at hle'
  exact (not_top_le_coe p.2) hle'

/-- Merge a finite convex combination indexed by `Fin m` into a `Finset`-indexed form. -/
lemma merge_epigraph_combo_finset {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    {m : Nat} {idx : Fin m → ι} {lam : Fin m → Real}
    {x' : Fin m → (Fin n → Real)} {μ' : Fin m → Real} {x : Fin n → Real} {μ : Real}
    (h0 : ∀ i, 0 ≤ lam i)
    (hsum1 : Finset.univ.sum (fun i => lam i) = 1)
    (hsumx : Finset.univ.sum (fun i => lam i • x' i) = x)
    (hsumμ : Finset.univ.sum (fun i => lam i * μ' i) = μ)
    (hle : ∀ i, f (idx i) (x' i) ≤ (μ' i : EReal)) :
    ∃ (s : Finset ι) (lam' : ι → Real) (x'' : ι → (Fin n → Real)) (μ'' : ι → Real),
      (∀ i, 0 ≤ lam' i) ∧
      (∀ i, i ∉ s → lam' i = 0) ∧
      (s.sum (fun i => lam' i) = 1) ∧
      (s.sum (fun i => lam' i • x'' i) = x) ∧
      (s.sum (fun i => lam' i * μ'' i) = μ) ∧
      (∀ i, f i (x'' i) ≤ (μ'' i : EReal)) := by
  classical
  let s : Finset ι := Finset.univ.image idx
  have hne :
      ∀ i, Set.Nonempty
        (epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := fun i => (hf i).2.1
  let x0 : ι → (Fin n → Real) := fun i => (Classical.choose (hne i)).1
  let μ0 : ι → Real := fun i => (Classical.choose (hne i)).2
  have hx0 : ∀ i, f i (x0 i) ≤ (μ0 i : EReal) := by
    intro i
    have hmem := Classical.choose_spec (hne i)
    exact (mem_epigraph_univ_iff (f := f i)).1 hmem
  let fiber : ι → Finset (Fin m) := fun i => Finset.univ.filter (fun j => idx j = i)
  let lam' : ι → Real := fun i => (fiber i).sum (fun j => lam j)
  let x'' : ι → (Fin n → Real) := fun i =>
    if h : lam' i = 0 then x0 i
    else (fiber i).sum (fun j => (lam j / lam' i) • x' j)
  let μ'' : ι → Real := fun i =>
    if h : lam' i = 0 then μ0 i
    else (fiber i).sum (fun j => (lam j / lam' i) * μ' j)
  have hlam'_nonneg : ∀ i, 0 ≤ lam' i := by
    intro i
    refine Finset.sum_nonneg ?_
    intro j hj
    exact h0 j
  have hzero_fiber : ∀ i, lam' i = 0 → ∀ j ∈ fiber i, lam j = 0 := by
    intro i hli j hj
    have hsum_zero : (fiber i).sum (fun k => lam k) = 0 := by
      simpa [lam'] using hli
    have hnonneg : ∀ k ∈ fiber i, 0 ≤ lam k := by
      intro k hk
      exact h0 k
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_zero
    exact hzero j hj
  have hsupport : ∀ i, i ∉ s → lam' i = 0 := by
    intro i hi
    have hnone : ∀ j : Fin m, idx j ≠ i := by
      intro j hji
      have hmem : idx j ∈ s := by
        refine Finset.mem_image_of_mem idx ?_
        simp
      have : i ∈ s := by
        simpa [hji] using hmem
      exact hi this
    have hfilter : fiber i = ∅ := by
      ext j
      simp [fiber, hnone j]
    simp [lam', hfilter]
  have hmulx : ∀ i, lam' i • x'' i = (fiber i).sum (fun j => lam j • x' j) := by
    intro i
    by_cases hli : lam' i = 0
    · have hsum_zero : (fiber i).sum (fun j => lam j • x' j) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        simp [hzero_fiber i hli j hj]
      simp [x'', hli, hsum_zero]
    · calc
        lam' i • x'' i
            = lam' i • (fiber i).sum (fun j => (lam j / lam' i) • x' j) := by
                simp [x'', hli]
        _ = (fiber i).sum (fun j => lam' i • ((lam j / lam' i) • x' j)) := by
              simpa using (Finset.smul_sum (s := fiber i)
                (f := fun j => (lam j / lam' i) • x' j) (r := lam' i))
        _ = (fiber i).sum (fun j => (lam' i * (lam j / lam' i)) • x' j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [smul_smul]
        _ = (fiber i).sum (fun j => lam j • x' j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hmul : lam' i * (lam j / lam' i) = lam j := by
                field_simp [hli]
              simp [hmul]
  have hmulμ : ∀ i, lam' i * μ'' i = (fiber i).sum (fun j => lam j * μ' j) := by
    intro i
    by_cases hli : lam' i = 0
    · have hsum_zero : (fiber i).sum (fun j => lam j * μ' j) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        simp [hzero_fiber i hli j hj]
      simp [μ'', hli, hsum_zero]
    · calc
        lam' i * μ'' i
            = lam' i * (fiber i).sum (fun j => (lam j / lam' i) * μ' j) := by
                simp [μ'', hli]
        _ = (fiber i).sum (fun j => lam' i * ((lam j / lam' i) * μ' j)) := by
              simpa using (Finset.mul_sum (s := fiber i)
                (f := fun j => (lam j / lam' i) * μ' j) (a := lam' i))
        _ = (fiber i).sum (fun j => lam j * μ' j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hmul : lam' i * (lam j / lam' i) = lam j := by
                field_simp [hli]
              calc
                lam' i * ((lam j / lam' i) * μ' j) =
                    (lam' i * (lam j / lam' i)) * μ' j := by ring
                _ = lam j * μ' j := by simp [hmul]
  have hmaps :
      ∀ j ∈ (Finset.univ : Finset (Fin m)), idx j ∈ s := by
    intro j hj
    exact Finset.mem_image_of_mem idx hj
  have hsum_lam' :
      s.sum (fun i => lam' i) = Finset.univ.sum (fun j => lam j) := by
    have hsum :=
      Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin m)))
        (t := s) (g := idx) (f := lam) hmaps
    simpa [lam', fiber] using hsum
  have hsum1' : s.sum (fun i => lam' i) = 1 := by
    simpa [hsum1] using hsum_lam'
  have hsumx' : s.sum (fun i => lam' i • x'' i) = x := by
    have hsum :=
      Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin m)))
        (t := s) (g := idx) (f := fun j => lam j • x' j) hmaps
    have hsum' :
        s.sum (fun i => (fiber i).sum (fun j => lam j • x' j)) =
          Finset.univ.sum (fun j => lam j • x' j) := by
      simpa [fiber] using hsum
    have hsum'' :
        s.sum (fun i => lam' i • x'' i) =
          s.sum (fun i => (fiber i).sum (fun j => lam j • x' j)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hmulx i
    calc
      s.sum (fun i => lam' i • x'' i) =
          Finset.univ.sum (fun j => lam j • x' j) := by
            exact hsum''.trans hsum'
      _ = x := hsumx
  have hsumμ' : s.sum (fun i => lam' i * μ'' i) = μ := by
    have hsum :=
      Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin m)))
        (t := s) (g := idx) (f := fun j => lam j * μ' j) hmaps
    have hsum' :
        s.sum (fun i => (fiber i).sum (fun j => lam j * μ' j)) =
          Finset.univ.sum (fun j => lam j * μ' j) := by
      simpa [fiber] using hsum
    have hsum'' :
        s.sum (fun i => lam' i * μ'' i) =
          s.sum (fun i => (fiber i).sum (fun j => lam j * μ' j)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hmulμ i
    calc
      s.sum (fun i => lam' i * μ'' i) =
          Finset.univ.sum (fun j => lam j * μ' j) := by
            exact hsum''.trans hsum'
      _ = μ := hsumμ
  have hle' : ∀ i, f i (x'' i) ≤ (μ'' i : EReal) := by
    intro i
    by_cases hli : lam' i = 0
    · simpa [x'', μ'', hli] using hx0 i
    · have hconv :
          Convex ℝ
            (epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) :=
        convex_epigraph_of_convexFunctionOn (f := f i) (hf i).1
      have hnonneg : ∀ j ∈ fiber i, 0 ≤ lam j / lam' i := by
        intro j hj
        have hpos : 0 < lam' i := lt_of_le_of_ne (hlam'_nonneg i) (Ne.symm hli)
        exact div_nonneg (h0 j) (le_of_lt hpos)
      have hsum_w : (fiber i).sum (fun j => lam j / lam' i) = 1 := by
        have hsum_div := (Finset.sum_div (s := fiber i) (f := lam) (a := lam' i)).symm
        calc
          (fiber i).sum (fun j => lam j / lam' i) =
              ((fiber i).sum (fun j => lam j)) / lam' i := by
                simpa using hsum_div
          _ = lam' i / lam' i := by simp [lam']
          _ = 1 := by field_simp [hli]
      have hmem :
          ∀ j ∈ fiber i,
            (x' j, μ' j) ∈
              epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        intro j hj
        have hidx : idx j = i := (Finset.mem_filter.1 hj).2
        have hle' : f i (x' j) ≤ (μ' j : EReal) := by
          simpa [hidx] using hle j
        exact (mem_epigraph_univ_iff (f := f i)).2 hle'
      have hcomb' :
          (fiber i).sum (fun j => (lam j / lam' i) • (x' j, μ' j)) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) :=
        hconv.sum_mem hnonneg hsum_w hmem
      have hcomb :
          (fiber i).sum (fun j => ((lam j / lam' i) • x' j, (lam j / lam' i) * μ' j)) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        simpa [smul_eq_mul] using hcomb'
      have hpair' :
          (fiber i).sum (fun j => ((lam j / lam' i) • x' j, (lam j / lam' i) * μ' j)) =
            ((fiber i).sum (fun j => (lam j / lam' i) • x' j),
              (fiber i).sum (fun j => (lam j / lam' i) * μ' j)) := by
        apply Prod.ext
        · simpa using
            (fst_sum (s := fiber i)
              (f := fun j => ((lam j / lam' i) • x' j, (lam j / lam' i) * μ' j)))
        · simpa using
            (snd_sum (s := fiber i)
              (f := fun j => ((lam j / lam' i) • x' j, (lam j / lam' i) * μ' j)))
      have hpair :
          (fiber i).sum (fun j => ((lam j / lam' i) • x' j, (lam j / lam' i) * μ' j)) =
            (x'' i, μ'' i) := by
        simpa [x'', μ'', hli] using hpair'
      have hmem' :
          (x'' i, μ'' i) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        simpa [hpair] using hcomb
      exact (mem_epigraph_univ_iff (f := f i)).1 hmem'
  refine ⟨s, lam', x'', μ'', hlam'_nonneg, hsupport, hsum1', hsumx', hsumμ', hle'⟩

/-- Finset-indexed convex combinations give points in the convex hull of the union of epigraphs. -/
lemma mem_convexHull_union_epigraph_of_finset_combo {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal} {x : Fin n → Real} {s : Finset ι}
    {lam : ι → Real} {x' : ι → (Fin n → Real)} {μ' : ι → Real}
    (h0 : ∀ i, 0 ≤ lam i)
    (hsum1 : s.sum (fun i => lam i) = 1)
    (hsumx : s.sum (fun i => lam i • x' i) = x)
    (hle : ∀ i, f i (x' i) ≤ (μ' i : EReal)) :
    (x, s.sum (fun i => lam i * μ' i)) ∈
      convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
  classical
  refine
    mem_convexHull_of_exists_fintype
      (s := ⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
      (x := (x, s.sum (fun i => lam i * μ' i)))
      (w := fun i : {i // i ∈ s} => lam i.1)
      (z := fun i : {i // i ∈ s} => (x' i.1, μ' i.1)) ?_ ?_ ?_ ?_
  · intro i
    exact h0 i.1
  · have hsum1' :
        (Finset.univ.sum (fun i : {i // i ∈ s} => lam i.1)) = 1 := by
        calc
          (Finset.univ.sum (fun i : {i // i ∈ s} => lam i.1)) =
              s.sum (fun i => lam i) := by
                simpa [Finset.univ_eq_attach] using
                  (Finset.sum_attach (s := s) (f := fun i => lam i))
          _ = 1 := hsum1
    exact hsum1'
  · intro i
    exact Set.mem_iUnion.2 ⟨i.1,
      (mem_epigraph_univ_iff (f := f i.1)).2 (hle i.1)⟩
  · apply Prod.ext
    · have hsumx' :
          (s.attach.sum (fun i => lam i.1 • x' i.1)) = x := by
          calc
            s.attach.sum (fun i => lam i.1 • x' i.1) =
                s.sum (fun i => lam i • x' i) := by
                  simpa using (Finset.sum_attach (s := s) (f := fun i => lam i • x' i))
            _ = x := hsumx
      have hsum_fst :
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).1 =
            s.attach.sum (fun i => lam i.1 • x' i.1) := by
          simpa using
            (fst_sum (s := s.attach)
              (f := fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1)))
      have :
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).1 = x := by
        calc
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).1 =
              s.attach.sum (fun i => lam i.1 • x' i.1) := hsum_fst
          _ = x := hsumx'
      exact this
    · have hsumμ' :
          s.attach.sum (fun i => lam i.1 * μ' i.1) =
            s.sum (fun i => lam i * μ' i) := by
          simpa using (Finset.sum_attach (s := s) (f := fun i => lam i * μ' i))
      have hsum_snd :
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).2 =
            s.attach.sum (fun i => lam i.1 * μ' i.1) := by
          simpa using
            (snd_sum (s := s.attach)
              (f := fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1)))
      have :
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).2 =
            s.sum (fun i => lam i * μ' i) := by
        calc
          (s.attach.sum (fun i => (lam i.1 • x' i.1, lam i.1 * μ' i.1))).2 =
              s.attach.sum (fun i => lam i.1 * μ' i.1) := hsum_snd
          _ = s.sum (fun i => lam i * μ' i) := hsumμ'
      exact this

/-- The convex-hull function family is the `EReal` inf-section for the convex hull of the
union of epigraphs. -/
lemma convexHullFunctionFamily_eq_inf_section_ereal {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) :
    convexHullFunctionFamily f =
      fun x =>
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (x, μ) ∈
            convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) }) := by
  rfl

/-- The convex-hull function family is the greatest convex minorant. -/
lemma convexHullFunctionFamily_greatest_convex_minorant_of_nonempty_bddBelow {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) :
    let g := convexHullFunctionFamily f;
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g ∧
      (∀ i, g ≤ f i) ∧
      ∀ h : (Fin n → Real) → EReal,
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        (∀ i, h ≤ f i) →
        h ≤ g := by
  classical
  set g := convexHullFunctionFamily f
  set F :
      Set ((Fin n → Real) × Real) :=
    convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
  let g' : (Fin n → Real) → EReal :=
    fun x => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F })
  have hEq : g = g' := by
    have hEq' := convexHullFunctionFamily_eq_inf_section_ereal (f := f)
    simpa [g, g', F] using hEq'
  have hconv' :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g' := by
    simpa [g', F] using
      (convexOn_inf_section_of_convex
        (F := F)
        (convex_convexHull (𝕜 := ℝ)
          (s := ⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))))
  have hle' : ∀ i, g' ≤ f i := by
    intro i
    have hsubset :
        epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) ⊆ F := by
      simpa [F] using (epigraph_subset_convexHull_union (f := f) i)
    have hle :
        g' ≤ f i :=
      le_of_epigraph_subset_inf_section (h := f i) (F := F) hsubset
    simpa [g', F] using hle
  have hgreat' :
      ∀ h : (Fin n → Real) → EReal,
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        (∀ i, h ≤ f i) →
        h ≤ g' := by
    intro h hh h_le
    have hsubset :
        F ⊆ epigraph (S := (Set.univ : Set (Fin n → Real))) h := by
      simpa [F] using
        (convexHull_union_subset_epigraph_of_le (f := f) (h := h) hh h_le)
    have hle :
        h ≤ g' :=
      le_inf_section_of_subset_epigraph (h := h) (F := F) hsubset
    simpa [g', F] using hle
  refine And.intro ?_ ?_
  · simpa [g, hEq] using hconv'
  refine And.intro ?_ ?_
  · intro i
    simpa [g, hEq] using hle' i
  · intro h hh h_le
    have hle : h ≤ g' := hgreat' h hh h_le
    simpa [g, hEq] using hle

/-- If some member of the family is finite at `x`, then the fiber over `x` in the convex hull
of the union of epigraphs is nonempty. -/
lemma fiber_nonempty_convexHull_union_of_exists_ne_top {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) {x : Fin n → Real}
    (h : ∃ i, f i x ≠ ⊤) :
    Set.Nonempty
      { μ : ℝ |
        (x, μ) ∈
          convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) } := by
  classical
  rcases h with ⟨i, htop⟩
  refine ⟨(f i x).toReal, ?_⟩
  have hmem :
      (x, (f i x).toReal) ∈
        epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
    exact (mem_epigraph_univ_iff (f := f i)).2 (EReal.le_coe_toReal htop)
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) ⊆
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
    simpa using (epigraph_subset_convexHull_union (f := f) i)
  exact hsubset hmem

/-- For each `x`, either some `f i x` is finite (yielding a nonempty fiber),
or all values are `⊤`. -/
lemma fiber_nonempty_convexHull_union_or_all_top {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) (x : Fin n → Real) :
    Set.Nonempty
        { μ : ℝ |
          (x, μ) ∈
            convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) }
      ∨ (∀ i, f i x = ⊤) := by
  classical
  by_cases h : ∃ i, f i x ≠ ⊤
  · left
    simpa using
      (fiber_nonempty_convexHull_union_of_exists_ne_top (f := f) (x := x) h)
  · right
    intro i
    by_contra hne
    exact h ⟨i, hne⟩

/-- If some member takes the value `⊥` at `x`, then the fiber is unbounded below. -/
lemma not_bddBelow_fiber_convexHull_union_of_exists_bot {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) {x : Fin n → Real}
    (h : ∃ i, f i x = ⊥) :
    ¬ BddBelow
        { μ : ℝ |
          (x, μ) ∈
            convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) } := by
  classical
  rcases h with ⟨i, hi⟩
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) ⊆
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
    simpa using (epigraph_subset_convexHull_union (f := f) i)
  have hmem :
      ∀ μ : ℝ,
        (x, μ) ∈
          convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
    intro μ
    have hμ : (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
      have : f i x ≤ (μ : EReal) := by
        simp [hi]
      exact (mem_epigraph_univ_iff (f := f i)).2 this
    exact hsubset hμ
  have huniv :
      (Set.univ : Set ℝ) ⊆
        { μ : ℝ |
          (x, μ) ∈
            convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) } := by
    intro μ hμ
    simpa using hmem μ
  intro hbdd
  have hbdd_univ : BddBelow (Set.univ : Set ℝ) := hbdd.mono huniv
  exact (not_bddBelow_univ (α := ℝ)) hbdd_univ

/-- Text 5.5.6: `conv { f_i | i ∈ I }` is the greatest convex function `f` (not necessarily
proper) on `R^n` such that `f(x) ≤ f_i(x)` for every `x ∈ R^n` and every `i ∈ I`. -/
theorem convexHullFunctionFamily_greatest_convex_minorant {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) :
    let g := convexHullFunctionFamily f;
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g ∧
      (∀ i, g ≤ f i) ∧
      ∀ h : (Fin n → Real) → EReal,
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        (∀ i, h ≤ f i) →
        h ≤ g := by
  simpa using
    (convexHullFunctionFamily_greatest_convex_minorant_of_nonempty_bddBelow (f := f))

/-- Theorem 5.6: Let `{f_i | i ∈ I}` be a collection of proper convex functions on `R^n`,
and let `f` be the convex hull of the collection. Then
`f(x) = inf { ∑_{i∈I} λ_i f_i(x_i) | ∑_{i∈I} λ_i x_i = x }`,
where the infimum is taken over all representations of `x` as a convex combination
of points `x_i` with only finitely many nonzero coefficients `λ_i`. (The formula is
also valid if one restricts `x_i` to lie in `dom f_i`.) -/
theorem convexHullFunctionFamily_eq_sInf_convexCombination {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ∀ x : Fin n → Real,
      convexHullFunctionFamily f x =
        sInf { z : EReal |
          ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (∀ i, i ∉ s → lam i = 0) ∧
            (s.sum (fun i => lam i) = 1) ∧
            (s.sum (fun i => lam i • x' i) = x) ∧
            z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) } := by
  classical
  intro x
  let A : Set ℝ :=
    { μ : ℝ |
      (x, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) }
  let A' : Set EReal := (fun μ : ℝ => (μ : EReal)) '' A
  let B : Set EReal :=
    { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • x' i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  have hle : sInf B ≤ sInf A' := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨μ, hμ, rfl⟩
    rcases
        (mem_convexHull_union_epigraph_iff_fin_combo (f := f) (x := x) (μ := μ)).1 hμ with
      ⟨m, idx, lam, x', μ', h0, hsum1, hsumx, hsumμ, hleμ⟩
    rcases
        merge_epigraph_combo_finset (f := f) (hf := hf) (idx := idx) (lam := lam) (x' := x')
          (μ' := μ') (x := x) (μ := μ) h0 hsum1 hsumx hsumμ hleμ with
      ⟨s, lam', x'', μ'', h0', hzero', hsum1', hsumx', hsumμ', hle'⟩
    let b : EReal := s.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i))
    have hbmem : b ∈ B := by
      refine ⟨s, lam', x'', h0', hzero', hsum1', hsumx', rfl⟩
    have hb : sInf B ≤ b := sInf_le hbmem
    have hsum_le :
        b ≤ s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      by_cases hli : lam' i = 0
      · simp [hli]
      · have hpos : 0 < lam' i := lt_of_le_of_ne (h0' i) (Ne.symm hli)
        exact ereal_mul_le_mul_of_pos_left_general (t := lam' i) hpos (hle' i)
    have hsumμE :
        s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) = (μ : EReal) := by
      have hsum' :
          s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) =
            s.sum (fun i => ((lam' i * μ'' i : Real) : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [EReal.coe_mul]
      have hsum'' :
          s.sum (fun i => ((lam' i * μ'' i : Real) : EReal)) =
            ((s.sum (fun i => lam' i * μ'' i) : ℝ) : EReal) := by
        simpa using (ereal_coe_sum (s := s) (f := fun i => lam' i * μ'' i))
      calc
        s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal))
            = ((s.sum (fun i => lam' i * μ'' i) : ℝ) : EReal) := by
                exact hsum'.trans hsum''
        _ = (μ : EReal) := by simp [hsumμ']
    exact le_trans hb (by simpa [hsumμE] using hsum_le)
  have hge : sInf A' ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨s, lam, x', h0, hzero, hsum1, hsumx, rfl⟩
    by_cases hztop :
        (s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) = ⊤)
    · simp [hztop]
    · have hnot_top_pos : ∀ i ∈ s, 0 < lam i → f i (x' i) ≠ ⊤ := by
        intro i hi hpos
        by_contra htop
        have hposE : (0 : EReal) < (lam i : EReal) := (EReal.coe_pos).2 hpos
        have hterm_top :
            ((lam i : Real) : EReal) * f i (x' i) = ⊤ := by
          simpa [htop] using (EReal.mul_top_of_pos (x := (lam i : EReal)) hposE)
        have hsum_ne_bot :
            (s.erase i).sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) ≠ ⊥ := by
          refine
            sum_ne_bot_of_ne_bot (s := s.erase i)
              (f := fun i => ((lam i : Real) : EReal) * f i (x' i)) ?_
          intro j hj
          have hne_bot : f j (x' j) ≠ ⊥ := (hf j).2.2 (x' j) (by simp)
          refine (EReal.mul_ne_bot ((lam j : Real) : EReal) (f j (x' j))).2 ?_
          refine ⟨?_, ?_, ?_, ?_⟩
          · left
            exact EReal.coe_ne_bot _
          · right
            exact hne_bot
          · left
            exact EReal.coe_ne_top _
          · left
            exact (EReal.coe_nonneg).2 (h0 j)
        have hsum_top :
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) = ⊤ := by
          have hsum :=
            (Finset.add_sum_erase (s := s)
              (f := fun i => ((lam i : Real) : EReal) * f i (x' i))
              (a := i) (h := hi))
          calc
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i))
                = ((lam i : Real) : EReal) * f i (x' i) +
                    (s.erase i).sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
                      simpa using hsum.symm
            _ = ⊤ := by
                  simpa [hterm_top] using (EReal.top_add_of_ne_bot hsum_ne_bot)
        exact hztop hsum_top
      have hx0 : ∀ i, ∃ x0, f i x0 ≠ ⊤ := by
        intro i
        exact exists_point_ne_top_of_proper (hf i)
      let x0 : ι → (Fin n → Real) := fun i => Classical.choose (hx0 i)
      have hx0top : ∀ i, f i (x0 i) ≠ ⊤ := by
        intro i
        exact Classical.choose_spec (hx0 i)
      let x'' : ι → (Fin n → Real) := fun i => if lam i = 0 then x0 i else x' i
      have hsumx' :
          s.sum (fun i => lam i • x'' i) = x := by
        have hsum_eq :
            s.sum (fun i => lam i • x'' i) =
              s.sum (fun i => lam i • x' i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hli : lam i = 0
          · simp [x'', hli]
          · simp [x'', hli]
        simpa [hsum_eq] using hsumx
      have hnot_top : ∀ i, f i (x'' i) ≠ ⊤ := by
        intro i
        by_cases hli : lam i = 0
        · simp [x'', hli, hx0top]
        · have hi : i ∈ s := by
            by_contra hi
            exact hli (hzero i hi)
          have hpos : 0 < lam i := lt_of_le_of_ne (h0 i) (Ne.symm hli)
          have hnot : f i (x' i) ≠ ⊤ := hnot_top_pos i hi hpos
          simp [x'', hli, hnot]
      have hnot_bot : ∀ i, f i (x'' i) ≠ ⊥ := by
        intro i
        exact (hf i).2.2 (x'' i) (by simp)
      let μ' : ι → Real := fun i => (f i (x'' i)).toReal
      have hleμ' : ∀ i, f i (x'' i) ≤ (μ' i : EReal) := by
        intro i
        have htop : f i (x'' i) ≠ ⊤ := hnot_top i
        have hbot : f i (x'' i) ≠ ⊥ := hnot_bot i
        have hcoe : ((f i (x'' i)).toReal : EReal) = f i (x'' i) :=
          EReal.coe_toReal htop hbot
        simp [μ', hcoe]
      let μ : Real := s.sum (fun i => lam i * μ' i)
      have hmem :
          (x, μ) ∈
            convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
        refine
          mem_convexHull_union_epigraph_of_finset_combo (f := f) (x := x) (s := s)
            (lam := lam) (x' := x'') (μ' := μ') h0 hsum1 hsumx' hleμ'
      have hmem' : (μ : EReal) ∈ A' := by
        refine ⟨μ, ?_, rfl⟩
        simpa [A] using hmem
      have hleA : sInf A' ≤ (μ : EReal) := sInf_le hmem'
      have hsum_x'' :
          s.sum (fun i => ((lam i : Real) : EReal) * f i (x'' i)) =
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hli : lam i = 0
        · simp [x'', hli]
        · simp [x'', hli]
      have hsum_toReal :
          s.sum (fun i => ((lam i : Real) : EReal) * f i (x'' i)) = (μ : EReal) := by
        have hsum' :
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x'' i)) =
              s.sum (fun i => ((lam i * μ' i : Real) : EReal)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have htop : f i (x'' i) ≠ ⊤ := hnot_top i
          have hbot : f i (x'' i) ≠ ⊥ := hnot_bot i
          have hcoe : (μ' i : EReal) = f i (x'' i) := by
            simpa [μ'] using (EReal.coe_toReal htop hbot)
          calc
            ((lam i : Real) : EReal) * f i (x'' i)
                = ((lam i : Real) : EReal) * (μ' i : EReal) := by
                    simp [hcoe]
            _ = ((lam i * μ' i : Real) : EReal) := by simp [EReal.coe_mul]
        have hsum'' :
            s.sum (fun i => ((lam i * μ' i : Real) : EReal)) =
              ((s.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
          simpa using
            (ereal_coe_sum (s := s) (f := fun i => lam i * μ' i))
        calc
          s.sum (fun i => ((lam i : Real) : EReal) * f i (x'' i))
              = ((s.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
                  exact hsum'.trans hsum''
          _ = (μ : EReal) := rfl
      have hz_eq :
          (μ : EReal) =
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
        exact hsum_toReal.symm.trans hsum_x''
      simpa [hz_eq] using hleA
  have hEq : sInf A' = sInf B := le_antisymm hge hle
  simpa [convexHullFunctionFamily_eq_inf_section_ereal, A, A', B] using hEq

/-- The singleton indicator plus a constant equals the constant at the point. -/
lemma indicator_add_const_at_point {n : Nat} (a : Fin n → Real) (c : Real) :
    indicatorFunction ({a} : Set (Fin n → Real)) a + (c : EReal) = (c : EReal) := by
  simp [indicatorFunction_singleton_simp]

/-- A bound at `a` implies a global bound by the singleton indicator plus a constant. -/
lemma le_indicator_add_const_of_le_at {n : Nat} {h : (Fin n → Real) → EReal}
    (a : Fin n → Real) (c : Real) (ha : h a ≤ (c : EReal)) :
    h ≤ fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal) := by
  intro x
  by_cases hx : x = a
  · simpa [hx, indicatorFunction_singleton_simp] using ha
  · simp [indicatorFunction_singleton_simp, hx]

/-- The singleton indicator plus a constant is a proper convex function on `Set.univ`. -/
lemma properConvexFunctionOn_indicator_add_const_singleton {n : Nat}
    (a : Fin n → Real) (c : Real) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal)) := by
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal)) := by
    have hCne : ({a} : Set (Fin n → Real)).Nonempty := by
      simp
    have hCconv : Convex ℝ ({a} : Set (Fin n → Real)) := by
      simp
    simpa using (convexFunctionOn_indicator_add_const (C := {a}) hCne hCconv c)
  have hne_epi :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin n → Real))
          (fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal))) := by
    refine ⟨(a, c), ?_⟩
    have :
        (fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal)) a ≤
          (c : EReal) := by
      simp [indicator_add_const_at_point]
    exact
      (mem_epigraph_univ_iff
        (f := fun x => indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal))).2 this
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)),
        indicatorFunction ({a} : Set (Fin n → Real)) x + (c : EReal) ≠ (⊥ : EReal) := by
    intro x hx
    by_cases hx' : x = a
    · simp [indicatorFunction_singleton_simp, hx', EReal.coe_ne_bot]
    · simp [indicatorFunction_singleton_simp, hx']
  exact ⟨hconv, hne_epi, hnotbot⟩

/-- A finite sum is `⊤` if one term is `⊤` and all terms are not `⊥`. -/
lemma sum_eq_top_of_term_top {ι : Type*} (s : Finset ι) (f : ι → EReal) {i : ι}
    (hi : i ∈ s) (htop : f i = ⊤) (hbot : ∀ j ∈ s, f j ≠ ⊥) :
    s.sum f = ⊤ := by
  classical
  have hsum :=
    (Finset.add_sum_erase (s := s) (f := f) (a := i) (h := hi))
  have hsum_ne_bot :
      (s.erase i).sum f ≠ ⊥ := by
    refine sum_ne_bot_of_ne_bot (s := s.erase i) (f := f) ?_
    intro j hj
    have hj' : j ∈ s := (Finset.mem_erase.mp hj).2
    exact hbot j hj'
  calc
    s.sum f = f i + (s.erase i).sum f := by
      simpa using hsum.symm
    _ = ⊤ := by
      simpa [htop] using (EReal.top_add_of_ne_bot hsum_ne_bot)

end Section05
end Chap01
