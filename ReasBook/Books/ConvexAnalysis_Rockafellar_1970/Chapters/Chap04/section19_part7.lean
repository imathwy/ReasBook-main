/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part6

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Corollary 19.1.2: coercing a nonempty lower-bounded real set into `EReal`
preserves its infimum. -/
lemma helperForCorollary_19_1_2_sInf_coe_image_eq_sInf_real
    {T : Set ℝ}
    (hT_nonempty : T.Nonempty)
    (hT_bddBelow : BddBelow T) :
    (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal) = (sInf T : ℝ) := by
  let S' : Set (WithTop ℝ) := ((fun q : ℝ => (q : WithTop ℝ)) '' T)
  have hS'_bdd : BddBelow S' := by
    refine Monotone.map_bddBelow ?_ hT_bddBelow
    intro a b hab
    exact WithTop.coe_le_coe.mpr hab
  have hsInf_S' :
      (WithBot.some (sInf S') : EReal) =
        sInf ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
    simpa using (WithBot.coe_sInf' (α := WithTop ℝ) (s := S') hS'_bdd)
  have hsInf_T : ((sInf T : ℝ) : WithTop ℝ) = sInf S' := by
    simpa [S'] using (WithTop.coe_sInf' (α := ℝ) (s := T) hT_nonempty hT_bddBelow)
  have himage_eq :
      ((fun q : ℝ => (q : EReal)) '' T) =
        ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨q, hqT, rfl⟩
      exact ⟨(q : WithTop ℝ), ⟨q, hqT, rfl⟩, rfl⟩
    · intro hz
      rcases hz with ⟨y, hyS', hyz⟩
      rcases hyS' with ⟨q, hqT, hyq⟩
      subst hyq
      exact ⟨q, hqT, hyz⟩
  calc
    (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal)
        = sInf ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
          simp [himage_eq]
    _ = (WithBot.some (sInf S') : EReal) := by
          simpa using hsInf_S'.symm
    _ = (WithBot.some (((sInf T : ℝ) : WithTop ℝ)) : EReal) := by
          simp [hsInf_T]
    _ = (sInf T : ℝ) := rfl

/-- Helper for Corollary 19.1.2: nonemptiness of the objective-value set gives one
admissible coefficient vector. -/
lemma helperForCorollary_19_1_2_exists_lam_of_nonemptyObjectiveSet
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hSnonempty :
      ({r : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r = ((∑ i, lam i * α i : ℝ) : EReal)}).Nonempty) :
    ∃ (lam : Fin m → ℝ) (r : EReal),
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i) ∧
      r = ((∑ i, lam i * α i : ℝ) : EReal) := by
  rcases hSnonempty with ⟨r, hr⟩
  rcases hr with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
  exact ⟨lam, r, hlin, hnorm, hnonneg, hobj⟩

/-- Helper for Corollary 19.1.2: the objective-value set equals the image of the feasible
coefficient set under the linear objective map (cast to `EReal`). -/
lemma helperForCorollary_19_1_2_objectiveValueSet_eq_image_feasibleCoefficients
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} :
    {r' : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r' = ((∑ i, lam i * α i : ℝ) : EReal)} =
      (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)} := by
  ext r'
  constructor
  · intro hr
    rcases hr with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
    refine ⟨lam, ?_, hobj.symm⟩
    exact ⟨hlin, hnorm, hnonneg⟩
  · intro hr
    rcases hr with ⟨lam, hfeas, hobj⟩
    rcases hfeas with ⟨hlin, hnorm, hnonneg⟩
    exact ⟨lam, hlin, hnorm, hnonneg, hobj.symm⟩

/-- Helper for Corollary 19.1.2: continuity of the coefficient objective map into `EReal`. -/
lemma helperForCorollary_19_1_2_objectiveValueMap_continuous
    {m : ℕ} {α : Fin m → ℝ} :
    Continuous (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) := by
  have hcont_real :
      Continuous (fun lam : Fin m → ℝ => (∑ i, lam i * α i : ℝ)) := by
    exact
      continuous_finset_sum Finset.univ (by
        intro i hi
        exact (continuous_apply i).mul continuous_const)
  exact continuous_coe_real_ereal.comp hcont_real

/-- Helper for Corollary 19.1.2: compactness of the feasible coefficient set implies
closedness of the objective-value set. -/
lemma helperForCorollary_19_1_2_objectiveValueSet_closed_of_compactFeasible
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hcompact_feasible :
      IsCompact
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)}) :
    IsClosed
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  have hcont_obj :
      Continuous (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) :=
    helperForCorollary_19_1_2_objectiveValueMap_continuous (m := m) (α := α)
  have himage_compact :
      IsCompact
        ((fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)}) :=
    hcompact_feasible.image hcont_obj
  have himage_closed :
      IsClosed
        ((fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)}) :=
    himage_compact.isClosed
  have hEq :
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} =
        (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)} :=
    helperForCorollary_19_1_2_objectiveValueSet_eq_image_feasibleCoefficients
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
  simpa [hEq] using himage_closed

/-- Helper for Corollary 19.1.2: finite generation of the feasible coefficient set implies
closedness of the associated objective-value set. -/
lemma helperForCorollary_19_1_2_closed_objectiveValueSet_of_feasibleFG
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hfg_feasible :
      IsFinitelyGeneratedConvexSet m
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)}) :
    IsClosed
      {q : ℝ |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          q = (∑ i, lam i * α i : ℝ)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  let T : Set ℝ :=
    {q : ℝ |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        q = (∑ i, lam i * α i : ℝ)}
  let objectiveToReal : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    ∑ i, α i • LinearMap.proj i
  let realToFin1 : ℝ →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.pi (fun _ : Fin 1 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  let objectiveToFin1 : (Fin m → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
    realToFin1.comp objectiveToReal
  have hObjectiveEval :
      ∀ lam : Fin m → ℝ, objectiveToReal lam = (∑ i, lam i * α i : ℝ) := by
    intro lam
    calc
      objectiveToReal lam = ∑ i, α i * lam i := by
            simp [objectiveToReal]
      _ = ∑ i, lam i * α i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hfgF : IsFinitelyGeneratedConvexSet m F := by
    simpa [F] using hfg_feasible
  have hfg_image : IsFinitelyGeneratedConvexSet 1 (objectiveToFin1 '' F) :=
    helperForCorollary_19_1_2_linearImage_finitelyGeneratedSet
      (n := m) (p := 1) (C := F) (L := objectiveToFin1)
      hfgF
  have hconv_image : Convex ℝ (objectiveToFin1 '' F) := by
    rcases hfg_image with ⟨S₀, S₁, hS₀finite, hS₁finite, hEqImage⟩
    simpa [hEqImage] using convex_mixedConvexHull (n := 1) S₀ S₁
  have hpoly_image : IsPolyhedralConvexSet 1 (objectiveToFin1 '' F) :=
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := 1) (C := objectiveToFin1 '' F) hconv_image hfg_image
  have hclosed_image : IsClosed (objectiveToFin1 '' F) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := 1) (C := objectiveToFin1 '' F) hpoly_image).1
  let embedRealToFin1 : ℝ → Fin 1 → ℝ := fun q _ => q
  have hEmbed_continuous : Continuous embedRealToFin1 :=
    continuous_pi (fun _ => continuous_id)
  have hT_eq_preimage : T = embedRealToFin1 ⁻¹' (objectiveToFin1 '' F) := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨lam, hlin, hnorm, hnonneg, hqObj⟩
      change embedRealToFin1 q ∈ objectiveToFin1 '' F
      refine ⟨lam, ?_, ?_⟩
      · exact ⟨hlin, hnorm, hnonneg⟩
      · funext i
        simp [embedRealToFin1, objectiveToFin1, realToFin1, hObjectiveEval, hqObj]
    · intro hq
      change embedRealToFin1 q ∈ objectiveToFin1 '' F at hq
      rcases hq with ⟨lam, hlamF, hEqFun⟩
      rcases hlamF with ⟨hlin, hnorm, hnonneg⟩
      have hqObj : q = (∑ i, lam i * α i : ℝ) := by
        have hEval := congrArg (fun u : Fin 1 → ℝ => u 0) hEqFun
        exact (by
          simpa [embedRealToFin1, objectiveToFin1, realToFin1, hObjectiveEval] using hEval.symm)
      exact ⟨lam, hlin, hnorm, hnonneg, hqObj⟩
  have hclosed_preimage : IsClosed (embedRealToFin1 ⁻¹' (objectiveToFin1 '' F)) :=
    hclosed_image.preimage hEmbed_continuous
  simpa [hT_eq_preimage, T] using hclosed_preimage

/-- Helper for Corollary 19.1.2: the feasible coefficient set for fixed `x` is finitely
generated because it is the solution set of finitely many linear equalities and inequalities. -/
lemma helperForCorollary_19_1_2_feasibleCoeffSet_finitelyGenerated
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {x : Fin n → ℝ} :
    IsFinitelyGeneratedConvexSet m
      {lam : Fin m → ℝ |
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  let aEq : Fin (n + 1) → Fin m → ℝ :=
    Fin.cases (fun i : Fin m => if (i : ℕ) < k then (1 : ℝ) else 0)
      (fun j : Fin n => fun i : Fin m => a i j)
  let αEq : Fin (n + 1) → ℝ :=
    Fin.cases (1 : ℝ) (fun j : Fin n => x j)
  let bIneq : Fin m → Fin m → ℝ :=
    fun i j => if j = i then (-1 : ℝ) else 0
  let βIneq : Fin m → ℝ := fun _ => 0
  have hpoly_system :
      IsPolyhedralConvexSet m
        {lam : Fin m → ℝ |
          (∀ t, lam ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, lam ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        m (n + 1) m aEq αEq bIneq βIneq)
  have hF_eq_system :
      F =
        {lam : Fin m → ℝ |
          (∀ t, lam ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, lam ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext lam
    simp [F, aEq, αEq, bIneq, βIneq, dotProduct, Finset.sum_filter,
      Fin.forall_fin_succ, and_left_comm, and_assoc]
  have hpolyF : IsPolyhedralConvexSet m F := by
    simpa [hF_eq_system] using hpoly_system
  have hconvF : Convex ℝ F :=
    helperForTheorem_19_1_polyhedral_isConvex (n := m) (C := F) hpolyF
  have hTFAE :
      [IsPolyhedralConvexSet m F,
          (IsClosed F ∧ {C' : Set (Fin m → ℝ) | IsFace (𝕜 := ℝ) F C'}.Finite),
        IsFinitelyGeneratedConvexSet m F].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := m) (C := F) hconvF
  exact (hTFAE.out 0 2).1 hpolyF

/-- Helper for Corollary 19.1.2: closedness of the objective-value set attached to one
finitely generated representation at fixed `x`. -/
lemma helperForCorollary_19_1_2_closed_objectiveValueSet
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} :
    IsClosed
      {q : ℝ |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          q = (∑ i, lam i * α i : ℝ)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  have hfg_feasible : IsFinitelyGeneratedConvexSet m F := by
    simpa [F] using
      helperForCorollary_19_1_2_feasibleCoeffSet_finitelyGenerated
        (n := n) (k := k) (m := m) (a := a) (x := x)
  simpa [F] using
    helperForCorollary_19_1_2_closed_objectiveValueSet_of_feasibleFG
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
      hfg_feasible

/-- Helper for Corollary 19.1.2: if the infimum of the objective-value set is a finite real,
then that real value belongs to the objective-value set. -/
lemma helperForCorollary_19_1_2_memObjectiveSet_of_finiteValue
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hsInf_real :
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = (r : EReal)) :
    (r : EReal) ∈
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  let Sx : Set EReal :=
    {r' : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r' = ((∑ i, lam i * α i : ℝ) : EReal)}
  let T : Set ℝ :=
    {q : ℝ |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        q = (∑ i, lam i * α i : ℝ)}
  have hSx_eq_coeImage_T :
      Sx = (fun q : ℝ => (q : EReal)) '' T := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
      refine ⟨(∑ i, lam i * α i : ℝ), ?_, ?_⟩
      · exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
      · simp [hzobj]
    · intro hz
      rcases hz with ⟨q, hqT, hzq⟩
      rcases hqT with ⟨lam, hlin, hnorm, hnonneg, hqobj⟩
      have hzobj : z = ((∑ i, lam i * α i : ℝ) : EReal) := by
        calc
          z = (q : EReal) := hzq.symm
          _ = ((∑ i, lam i * α i : ℝ) : EReal) := by simp [hqobj]
      exact ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
  have hsInf_real_Sx : sInf Sx = (r : EReal) := by
    simpa [Sx] using hsInf_real
  have hSx_nonempty : Sx.Nonempty :=
    helperForCorollary_19_1_2_nonempty_of_sInf_eq_real
      (S := Sx) (r := r) hsInf_real_Sx
  have hT_nonempty : T.Nonempty := by
    rcases hSx_nonempty with ⟨z, hz⟩
    rcases hz with ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
    refine ⟨(∑ i, lam i * α i : ℝ), ?_⟩
    exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  have hT_bddBelow : BddBelow T := by
    refine ⟨r, ?_⟩
    intro q hqT
    have hqSx : (q : EReal) ∈ Sx := by
      have hqImage : (q : EReal) ∈ (fun q : ℝ => (q : EReal)) '' T :=
        ⟨q, hqT, rfl⟩
      simpa [hSx_eq_coeImage_T] using hqImage
    have hsInf_le_qE : sInf Sx ≤ (q : EReal) := sInf_le hqSx
    have hr_le_qE : (r : EReal) ≤ (q : EReal) := by
      simpa [hsInf_real_Sx] using hsInf_le_qE
    exact (EReal.coe_le_coe_iff).1 hr_le_qE
  have hsInf_coeImage_T :
      (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal) = (sInf T : ℝ) :=
    helperForCorollary_19_1_2_sInf_coe_image_eq_sInf_real
      (T := T) hT_nonempty hT_bddBelow
  have hsInfT_eq_rE : ((sInf T : ℝ) : EReal) = (r : EReal) := by
    calc
      ((sInf T : ℝ) : EReal)
          = sInf ((fun q : ℝ => (q : EReal)) '' T) := by
              exact hsInf_coeImage_T.symm
      _ = sInf Sx := by simp [hSx_eq_coeImage_T]
      _ = (r : EReal) := hsInf_real_Sx
  have hsInfT_eq_r : sInf T = r := by
    exact EReal.coe_injective hsInfT_eq_rE
  have hT_closed : IsClosed T := by
    simpa [T] using
      helperForCorollary_19_1_2_closed_objectiveValueSet
        (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
  have hsInf_mem_T : sInf T ∈ T :=
    IsClosed.csInf_mem hT_closed hT_nonempty hT_bddBelow
  have hr_mem_T : r ∈ T := by
    simpa [hsInfT_eq_r] using hsInf_mem_T
  rcases hr_mem_T with ⟨lam, hlin, hnorm, hnonneg, hrobj⟩
  have hrobjE : (r : EReal) = ((∑ i, lam i * α i : ℝ) : EReal) := by
    simp [hrobj]
  exact ⟨lam, hlin, hnorm, hnonneg, hrobjE⟩

/-- Helper for Corollary 19.1.2: membership of the finite infimum value in the objective set
gives coefficients attaining exactly `f x`. -/
lemma helperForCorollary_19_1_2_attainment_value_of_infMember
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hrfx : f x = (r : EReal))
    (hrmem :
      (r : EReal) ∈
        {r' : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r' = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ∃ (lam : Fin m → ℝ),
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i) ∧
      f x = ((∑ i, lam i * α i : ℝ) : EReal) := by
  rcases hrmem with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
  refine ⟨lam, hlin, hnorm, hnonneg, ?_⟩
  calc
    f x = (r : EReal) := hrfx
    _ = ((∑ i, lam i * α i : ℝ) : EReal) := by simpa using hobj

/-- Helper for Corollary 19.1.2: in a fixed finite-generation representation, finite values are
attained by admissible coefficients. -/
lemma helperForCorollary_19_1_2_attainment_of_finiteValue
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
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
    ∀ x,
      (∃ r : ℝ, f x = (r : EReal)) →
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          f x = ((∑ i, lam i * α i : ℝ) : EReal) := by
  intro x hxfinite
  rcases hxfinite with ⟨r, hrfx⟩
  have hsInf_real :
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = (r : EReal) := by
    calc
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = f x := by
            exact (hrepr x).symm
      _ = (r : EReal) := hrfx
  have hrmem :
      (r : EReal) ∈
        {r' : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r' = ((∑ i, lam i * α i : ℝ) : EReal)} :=
    helperForCorollary_19_1_2_memObjectiveSet_of_finiteValue
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x) (r := r) hsInf_real
  exact
    helperForCorollary_19_1_2_attainment_value_of_infMember
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) (x := x) (r := r)
      hrfx hrmem

/-- Helper for Corollary 19.1.2: a finitely generated representation can be unpacked
into coefficients data together with pointwise attainment for every finite value. -/
lemma helperForCorollary_19_1_2_unpackData_with_attainment
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfgen : IsFinitelyGeneratedConvexFunction n f) :
    ∃ (k m : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ),
      k ≤ m ∧
        (∀ x,
          f x =
            sInf {r : EReal |
              ∃ (lam : Fin m → ℝ),
                (∀ j, (∑ i, lam i * a i j) = x j) ∧
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) = 1 ∧
                (∀ i, 0 ≤ lam i) ∧
                r = ((∑ i, lam i * α i : ℝ) : EReal)}) ∧
        (∀ x,
          (∃ r : ℝ, f x = (r : EReal)) →
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              f x = ((∑ i, lam i * α i : ℝ) : EReal)) := by
  rcases
    helperForCorollary_19_1_2_unpack_finitelyGeneratedData
      (n := n) (f := f) hfgen with
    ⟨k, m, a, α, hk, hrepr⟩
  refine ⟨k, m, a, α, hk, hrepr, ?_⟩
  intro x hxfinite
  exact
    helperForCorollary_19_1_2_attainment_of_finiteValue
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
      hrepr x hxfinite

/-- Corollary 19.1.2: A convex function is polyhedral iff it is finitely generated; such a
function, if proper, is closed; and in the finitely generated representation the infimum at
`x`, when finite, is attained by some coefficients `λ`. -/
theorem polyhedral_convex_iff_finitelyGenerated_and_closed_and_attainment
    (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    (IsPolyhedralConvexFunction n f ↔ IsFinitelyGeneratedConvexFunction n f) ∧
      (IsPolyhedralConvexFunction n f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ClosedConvexFunction f) ∧
      (IsFinitelyGeneratedConvexFunction n f →
        ∃ (k m : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ),
          k ≤ m ∧
            (∀ x,
              f x =
                sInf {r : EReal |
                  ∃ (lam : Fin m → ℝ),
                    (∀ j, (∑ i, lam i * a i j) = x j) ∧
                    (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                      (fun i => lam i)) = 1 ∧
                    (∀ i, 0 ≤ lam i) ∧
                    r = ((∑ i, lam i * α i : ℝ) : EReal)}) ∧
            (∀ x,
              (∃ r : ℝ, f x = (r : EReal)) →
                ∃ (lam : Fin m → ℝ),
                  (∀ j, (∑ i, lam i * a i j) = x j) ∧
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) = 1 ∧
                (∀ i, 0 ≤ lam i) ∧
                f x = ((∑ i, lam i * α i : ℝ) : EReal))) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hfpoly
      exact
        helperForCorollary_19_1_2_polyhedral_imp_finitelyGenerated
          (n := n) (f := f) hfpoly
    · intro hfgen
      exact
        helperForCorollary_19_1_2_finitelyGenerated_imp_polyhedral
          (n := n) (f := f) hfgen
  · intro hfpoly hfproper
    exact
      helperForCorollary_19_1_2_closed_of_polyhedral_proper
        (n := n) (f := f) hfpoly hfproper
  · intro hfgen
    exact
      helperForCorollary_19_1_2_unpackData_with_attainment
        (n := n) (f := f) hfgen

/-- Helper for Text 19.0.11: every signed sum is bounded above by the `ℓ¹` value. -/
lemma helperForText_19_0_11_signedSum_le_absSum
    {n : ℕ} (x : Fin n → ℝ) (σ : Fin n → Bool) :
    (∑ j, x j * (if σ j then (1 : ℝ) else -1)) ≤ ∑ j, |x j| := by
  refine Finset.sum_le_sum ?_
  intro j hj
  by_cases hσ : σ j
  · simp [hσ, le_abs_self]
  · simp [hσ, neg_le_abs]

/-- Helper for Text 19.0.11: choosing coordinate-wise signs attains the `ℓ¹` value. -/
lemma helperForText_19_0_11_exists_sign_attains_absSum
    {n : ℕ} (x : Fin n → ℝ) :
    ∃ σ : Fin n → Bool,
      (∑ j, x j * (if σ j then (1 : ℝ) else -1)) = ∑ j, |x j| := by
  let σ : Fin n → Bool := fun j => if 0 ≤ x j then true else false
  refine ⟨σ, ?_⟩
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hxj : 0 ≤ x j
  · simp [σ, hxj, abs_of_nonneg hxj]
  · have hxj' : x j < 0 := lt_of_not_ge hxj
    simp [σ, hxj, abs_of_neg hxj']

/-- Helper for Text 19.0.11: the supremum over all signed linear forms equals `∑ |x i|`. -/
lemma helperForText_19_0_11_sSup_signedValues_eq_absSum
    {n : ℕ} (x : Fin n → ℝ) :
    sSup {r : ℝ | ∃ σ : Fin n → Bool,
      r = (∑ j, x j * (if σ j then (1 : ℝ) else -1))} = ∑ j, |x j| := by
  let T : Set ℝ :=
    {r : ℝ | ∃ σ : Fin n → Bool,
      r = (∑ j, x j * (if σ j then (1 : ℝ) else -1))}
  let σ0 : Fin n → Bool := fun _ => true
  have hσ0_mem :
      (∑ j, x j * (if σ0 j then (1 : ℝ) else -1)) ∈ T := by
    refine ⟨σ0, rfl⟩
  have hT_nonempty : T.Nonempty := ⟨_, hσ0_mem⟩
  have hT_bddAbove : BddAbove T := by
    refine ⟨∑ j, |x j|, ?_⟩
    intro r hr
    rcases hr with ⟨σ, rfl⟩
    exact helperForText_19_0_11_signedSum_le_absSum (x := x) (σ := σ)
  have hsSup_le : sSup T ≤ ∑ j, |x j| := by
    refine csSup_le hT_nonempty ?_
    intro r hr
    rcases hr with ⟨σ, rfl⟩
    exact helperForText_19_0_11_signedSum_le_absSum (x := x) (σ := σ)
  rcases helperForText_19_0_11_exists_sign_attains_absSum (x := x) with ⟨σmax, hσmax⟩
  have hmax_mem : (∑ j, |x j|) ∈ T := by
    exact ⟨σmax, hσmax.symm⟩
  have hle_sSup : (∑ j, |x j|) ≤ sSup T := le_csSup hT_bddAbove hmax_mem
  have hEq : sSup T = ∑ j, |x j| := le_antisymm hsSup_le hle_sSup
  simpa [T] using hEq

/-- Text 19.0.11: The function `f(x) = |ξ₁| + ··· + |ξₙ|` on `ℝ^n` is polyhedral convex,
since it is the pointwise supremum of the `2^n` linear functions
`x ↦ ε₁ ξ₁ + ··· + εₙ ξₙ` with `εⱼ ∈ {+1, -1}`. -/
theorem polyhedralConvex_absSum (n : ℕ) :
    IsPolyhedralConvexFunction n (fun x => ((∑ i, |x i| : ℝ) : EReal)) := by
  let m : ℕ := Fintype.card (Fin n → Bool)
  let k : ℕ := m
  let e : (Fin n → Bool) ≃ Fin m := Fintype.equivFin (Fin n → Bool)
  let b : Fin m → Fin n → ℝ := fun i j => if (e.symm i) j then (1 : ℝ) else -1
  let β : Fin m → ℝ := fun _ => 0
  let f : (Fin n → ℝ) → EReal := fun x => ((∑ i, |x i| : ℝ) : EReal)
  have hk : k ≤ m := by
    simp [k]
  have hrepr :
      f =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              x := by
    funext x
    have hSetEq :
        {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} =
          {r : ℝ | ∃ σ : Fin n → Bool,
            r = (∑ j, x j * (if σ j then (1 : ℝ) else -1))} := by
      ext r
      constructor
      · intro hr
        rcases hr with ⟨i, hi, hrEq⟩
        have hvalue :
            (∑ j, x j * b i j) - β i =
              (∑ j, x j * (if (e.symm i) j then (1 : ℝ) else -1)) := by
          simp [b, β]
        have hrEq' :
            r = (∑ j, x j * (if (e.symm i) j then (1 : ℝ) else -1)) := by
          calc
            r = (∑ j, x j * b i j) - β i := hrEq
            _ = (∑ j, x j * (if (e.symm i) j then (1 : ℝ) else -1)) := hvalue
        exact ⟨e.symm i, hrEq'⟩
      · intro hr
        rcases hr with ⟨σ, hrEq⟩
        have hi : ((e σ : Fin m) : ℕ) < k := by
          have hi_lt_m : ((e σ : Fin m) : ℕ) < m := (e σ).is_lt
          simpa [k] using hi_lt_m
        have hvalue :
            (∑ j, x j * (if σ j then (1 : ℝ) else -1)) =
              (∑ j, x j * b (e σ) j) - β (e σ) := by
          simp [b, β]
        have hrEq' : r = (∑ j, x j * b (e σ) j) - β (e σ) := by
          calc
            r = (∑ j, x j * (if σ j then (1 : ℝ) else -1)) := hrEq
            _ = (∑ j, x j * b (e σ) j) - β (e σ) := hvalue
        exact ⟨e σ, hi, hrEq'⟩
    have hsSup_eq :
        sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} =
          ∑ j, |x j| := by
      calc
        sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
            = sSup {r : ℝ | ∃ σ : Fin n → Bool,
                r = (∑ j, x j * (if σ j then (1 : ℝ) else -1))} := by
              simp [hSetEq]
        _ = ∑ j, |x j| :=
            helperForText_19_0_11_sSup_signedValues_eq_absSum (x := x)
    have hConstraint :
        x ∈
          {y | ∀ i : Fin m, k ≤ (i : ℕ) →
            (∑ j, y j * b i j) ≤ β i} := by
      intro i hik
      have hikm : m ≤ (i : ℕ) := by
        simpa [k] using hik
      have hnot : ¬ m ≤ (i : ℕ) := Nat.not_le_of_lt i.is_lt
      exact False.elim (hnot hikm)
    have hIndicator :
        indicatorFunction
          (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
            (∑ j, y j * b i j) ≤ β i}) x = (0 : EReal) := by
      simp [indicatorFunction, hConstraint]
    calc
      f x = ((∑ j, |x j| : ℝ) : EReal) := by
        simp [f]
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
            simp [hsSup_eq]
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            (0 : EReal) := by
              simp
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              x := by
                simp [hIndicator]
  have hpoly_nonbot :
      IsPolyhedralConvexFunction n f ∧
        (∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal)) :=
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := f)).2 ⟨k, m, b, β, hk, hrepr⟩
  have hpoly : IsPolyhedralConvexFunction n f := hpoly_nonbot.1
  simpa [f] using hpoly

/-- Text 19.0.12: The Tchebycheff (supremum) norm `f : ℝ^n → ℝ` defined by
`f(x) = max {|ξ₁|, …, |ξₙ|}` (with `x = (ξ₁, …, ξₙ)`) is polyhedral convex, since it is the
pointwise supremum of the `2n` linear functions `x ↦ ε_j ξ_j` with
`ε_j ∈ {+1, -1}` for `j = 1, …, n`. -/
theorem polyhedralConvex_tchebycheffSupNorm (n : ℕ) :
    IsPolyhedralConvexFunction n
      (fun x => ((sSup {r : ℝ | ∃ i : Fin n, r = |x i|} : ℝ) : EReal)) := by
  let m : ℕ := Fintype.card (Fin n × Bool)
  let k : ℕ := m
  let e : (Fin n × Bool) ≃ Fin m := Fintype.equivFin (Fin n × Bool)
  let b : Fin m → Fin n → ℝ :=
    fun i j =>
      if j = (e.symm i).1 then (if (e.symm i).2 then (1 : ℝ) else -1) else 0
  let β : Fin m → ℝ := fun _ => 0
  let f : (Fin n → ℝ) → EReal :=
    fun x => ((sSup {r : ℝ | ∃ i : Fin n, r = |x i|} : ℝ) : EReal)
  have hk : k ≤ m := by
    simp [k]
  have hrepr :
      f =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              x := by
    funext x
    have hsSup_signed_eq_abs :
        sSup {r : ℝ | ∃ p : Fin n × Bool,
          r = x p.1 * (if p.2 then (1 : ℝ) else -1)} =
          sSup {r : ℝ | ∃ i : Fin n, r = |x i|} := by
      by_cases hn : n = 0
      · subst hn
        simp
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        let i0 : Fin n := ⟨0, hn_pos⟩
        let S : Set ℝ :=
          {r : ℝ | ∃ p : Fin n × Bool, r = x p.1 * (if p.2 then (1 : ℝ) else -1)}
        let A : Set ℝ := {r : ℝ | ∃ i : Fin n, r = |x i|}
        have hS_nonempty : S.Nonempty := by
          refine ⟨x i0, ?_⟩
          refine ⟨(i0, true), ?_⟩
          simp [S]
        have hA_nonempty : A.Nonempty := by
          refine ⟨|x i0|, ?_⟩
          refine ⟨i0, rfl⟩
        have hS_finite : S.Finite := by
          refine
            (Set.finite_range
              (fun p : Fin n × Bool => x p.1 * (if p.2 then (1 : ℝ) else -1))).subset ?_
          intro r hr
          rcases hr with ⟨p, hp⟩
          refine ⟨p, hp.symm⟩
        have hA_finite : A.Finite := by
          refine (Set.finite_range (fun i : Fin n => |x i|)).subset ?_
          intro r hr
          rcases hr with ⟨i, hi⟩
          refine ⟨i, hi.symm⟩
        have hS_bddAbove : BddAbove S := hS_finite.bddAbove
        have hA_bddAbove : BddAbove A := hA_finite.bddAbove
        have hsSup_S_le_A : sSup S ≤ sSup A := by
          refine csSup_le hS_nonempty ?_
          intro r hr
          rcases hr with ⟨p, rfl⟩
          have hle_abs :
              x p.1 * (if p.2 then (1 : ℝ) else -1) ≤ |x p.1| := by
            cases hsign : p.2
            · simp [hsign, neg_le_abs]
            · simp [hsign, le_abs_self]
          have hmemA : |x p.1| ∈ A := by
            refine ⟨p.1, rfl⟩
          exact le_trans hle_abs (le_csSup hA_bddAbove hmemA)
        have hsSup_A_le_S : sSup A ≤ sSup S := by
          refine csSup_le hA_nonempty ?_
          intro r hr
          rcases hr with ⟨i, rfl⟩
          by_cases hxi : 0 ≤ x i
          · have hmemS : x i ∈ S := by
              refine ⟨(i, true), ?_⟩
              simp [S]
            calc
              |x i| = x i := abs_of_nonneg hxi
              _ ≤ sSup S := le_csSup hS_bddAbove hmemS
          · have hxi_lt : x i < 0 := lt_of_not_ge hxi
            have hmemSneg : -x i ∈ S := by
              refine ⟨(i, false), ?_⟩
              simp [S]
            calc
              |x i| = -x i := abs_of_neg hxi_lt
              _ ≤ sSup S := le_csSup hS_bddAbove hmemSneg
        have hEq : sSup S = sSup A := le_antisymm hsSup_S_le_A hsSup_A_le_S
        simpa [S, A] using hEq
    have hSetEq :
        {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} =
          {r : ℝ | ∃ p : Fin n × Bool,
            r = x p.1 * (if p.2 then (1 : ℝ) else -1)} := by
      ext r
      constructor
      · intro hr
        rcases hr with ⟨i, hi, hrEq⟩
        have hvalue :
            (∑ j, x j * b i j) - β i =
              x (e.symm i).1 * (if (e.symm i).2 then (1 : ℝ) else -1) := by
          simp [b, β]
        have hrEq' :
            r = x (e.symm i).1 * (if (e.symm i).2 then (1 : ℝ) else -1) := by
          calc
            r = (∑ j, x j * b i j) - β i := hrEq
            _ = x (e.symm i).1 * (if (e.symm i).2 then (1 : ℝ) else -1) := hvalue
        exact ⟨e.symm i, hrEq'⟩
      · intro hr
        rcases hr with ⟨p, hrEq⟩
        have hi : ((e p : Fin m) : ℕ) < k := by
          have hi_lt_m : ((e p : Fin m) : ℕ) < m := (e p).is_lt
          simpa [k] using hi_lt_m
        have hvalue :
            (∑ j, x j * b (e p) j) - β (e p) =
              x p.1 * (if p.2 then (1 : ℝ) else -1) := by
          simp [b, β]
        have hrEq' : r = (∑ j, x j * b (e p) j) - β (e p) := by
          calc
            r = x p.1 * (if p.2 then (1 : ℝ) else -1) := hrEq
            _ = (∑ j, x j * b (e p) j) - β (e p) := hvalue.symm
        exact ⟨e p, hi, hrEq'⟩
    have hsSup_eq :
        sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} =
          sSup {r : ℝ | ∃ i : Fin n, r = |x i|} := by
      calc
        sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
            = sSup {r : ℝ | ∃ p : Fin n × Bool,
                r = x p.1 * (if p.2 then (1 : ℝ) else -1)} := by
              simp [hSetEq]
        _ = sSup {r : ℝ | ∃ i : Fin n, r = |x i|} := hsSup_signed_eq_abs
    have hConstraint :
        x ∈
          {y | ∀ i : Fin m, k ≤ (i : ℕ) →
            (∑ j, y j * b i j) ≤ β i} := by
      intro i hik
      have hikm : m ≤ (i : ℕ) := by
        simpa [k] using hik
      have hnot : ¬ m ≤ (i : ℕ) := Nat.not_le_of_lt i.is_lt
      exact False.elim (hnot hikm)
    have hIndicator :
        indicatorFunction
          (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
            (∑ j, y j * b i j) ≤ β i}) x = (0 : EReal) := by
      simp [indicatorFunction, hConstraint]
    calc
      f x = ((sSup {r : ℝ | ∃ i : Fin n, r = |x i|} : ℝ) : EReal) := by
        simp [f]
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
            simp [hsSup_eq]
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            (0 : EReal) := by
              simp
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              x := by
                simp [hIndicator]
  have hpoly_nonbot :
      IsPolyhedralConvexFunction n f ∧
        (∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal)) :=
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := f)).2 ⟨k, m, b, β, hk, hrepr⟩
  have hpoly : IsPolyhedralConvexFunction n f := hpoly_nonbot.1
  simpa [f] using hpoly

/-- Helper for Text 19.0.13: build an explicit affine line in `ℝ²` with equation `x 1 = 1`
and record that the origin is not on it. -/
lemma helperForText_19_0_13_affineLine_x1_eq_one_data :
    ∃ L : AffineSubspace ℝ (Fin 2 → ℝ),
      Module.finrank ℝ L.direction = 1 ∧
        ((L : Set (Fin 2 → ℝ)) = {x | x 1 = 1}) ∧
        ((0 : Fin 2 → ℝ) ∉ (L : Set (Fin 2 → ℝ))) := by
  let x0 : Fin 2 → ℝ := ![(0 : ℝ), 1]
  let v : Fin 2 → ℝ := ![(1 : ℝ), 0]
  let L : AffineSubspace ℝ (Fin 2 → ℝ) := AffineSubspace.mk' x0 (ℝ ∙ v)
  have hv_ne : v ≠ 0 := by
    intro hv
    have : (1 : ℝ) = 0 := by
      simpa [v] using congrArg (fun z : Fin 2 → ℝ => z 0) hv
    norm_num at this
  have hdir : L.direction = (ℝ ∙ v) := by
    simp [L]
  have hfinrank : Module.finrank ℝ L.direction = 1 := by
    rw [hdir]
    exact finrank_span_singleton hv_ne
  have hcarrier : (L : Set (Fin 2 → ℝ)) = {x : Fin 2 → ℝ | x 1 = 1} := by
    ext x
    constructor
    · intro hx
      have hxdir : x -ᵥ x0 ∈ (ℝ ∙ v) := by
        simpa [L] using (AffineSubspace.mem_mk'.1 hx)
      rcases (Submodule.mem_span_singleton).1 hxdir with ⟨a, ha⟩
      have ha1 : (a • v) 1 = (x -ᵥ x0) 1 := congrArg (fun z : Fin 2 → ℝ => z 1) ha
      have ha1' : x 1 - 1 = 0 := by
        simpa [v, x0, vsub_eq_sub] using ha1.symm
      have hx1 : x 1 = 1 := by linarith
      simpa using hx1
    · intro hx
      have hxdir : x -ᵥ x0 ∈ (ℝ ∙ v) := by
        refine (Submodule.mem_span_singleton).2 ?_
        refine ⟨x 0, ?_⟩
        ext i
        fin_cases i
        · simp [v, x0, vsub_eq_sub]
        · have hx1 : x 1 = 1 := hx
          simp [v, x0, vsub_eq_sub, hx1]
      have hxmk : x ∈ AffineSubspace.mk' x0 (ℝ ∙ v) := (AffineSubspace.mem_mk').2 hxdir
      have hxL : x ∈ L := by
        simpa [L] using hxmk
      exact hxL
  have h0not : (0 : Fin 2 → ℝ) ∉ (L : Set (Fin 2 → ℝ)) := by
    intro h0
    have hzero : (0 : Fin 2 → ℝ) 1 = 1 := by
      simp [hcarrier] at h0
    norm_num at hzero
  exact ⟨L, hfinrank, hcarrier, h0not⟩

/-- Helper for Text 19.0.13: the explicit line `{x | x 1 = 1}` is polyhedral convex. -/
lemma helperForText_19_0_13_lineSet_polyhedral :
    IsPolyhedralConvexSet 2 {x : Fin 2 → ℝ | x 1 = 1} := by
  let a : Fin 1 → Fin 2 → ℝ := fun _ => Pi.single 1 (1 : ℝ)
  let α : Fin 1 → ℝ := fun _ => 1
  let b : Fin 0 → Fin 2 → ℝ := fun _ => 0
  let β : Fin 0 → ℝ := fun _ => 0
  have hpoly :
      IsPolyhedralConvexSet 2
        {x : Fin 2 → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} :=
    polyhedralConvexSet_solutionSet_linearEq_and_inequalities 2 1 0 a α b β
  have hEq :
      {x : Fin 2 → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} =
        {x : Fin 2 → ℝ | x 1 = 1} := by
    ext x
    simp [a, α, b, β, dotProduct]
  rw [hEq] at hpoly
  exact hpoly

/-- Helper for Text 19.0.13: the singleton containing the origin in `ℝ²` is polyhedral
convex. -/
lemma helperForText_19_0_13_originSingleton_polyhedral :
    IsPolyhedralConvexSet 2 ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)) := by
  simpa using (helperForTheorem_19_1_zero_set_polyhedral (m := 2))

/-- Helper for Text 19.0.13: the convex hull of the line `{x | x 1 = 1}` united with
`{0}` is not closed. -/
lemma helperForText_19_0_13_notClosed_convexHull_line_union_origin :
    ¬ IsClosed
      (convexHull ℝ
        ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) := by
  rcases helperForText_19_0_13_affineLine_x1_eq_one_data with ⟨L, hLdim, hLset, h0notin⟩
  have hNotClosed :
      ¬ IsClosed (conv ((L : Set (Fin 2 → ℝ)) ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) :=
    not_isClosed_conv_line_union_singleton (L := L) (p := (0 : Fin 2 → ℝ)) hLdim h0notin
  simpa [conv, hLset] using hNotClosed

/-- Helper for Text 19.0.13: the same convex hull is therefore not polyhedral. -/
lemma helperForText_19_0_13_notPolyhedral_convexHull_line_union_origin :
    ¬ IsPolyhedralConvexSet 2
      (convexHull ℝ
        ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) := by
  intro hpoly
  have hclosed :
      IsClosed
        (convexHull ℝ
          ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := 2)
      (C :=
        convexHull ℝ
          ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ))))
      hpoly).1
  exact helperForText_19_0_13_notClosed_convexHull_line_union_origin hclosed

/-- Text 19.0.13: The convex hull of the union of two polyhedral convex sets need not be
polyhedral; for instance, this occurs for a line and a point not on the line. -/
theorem exists_polyhedralConvexSets_convexHull_union_not_polyhedral :
    ∃ (C₁ C₂ : Set (Fin 2 → ℝ)),
      IsPolyhedralConvexSet 2 C₁ ∧
        IsPolyhedralConvexSet 2 C₂ ∧
          ¬ IsPolyhedralConvexSet 2 (convexHull ℝ (C₁ ∪ C₂)) := by
  refine ⟨{x : Fin 2 → ℝ | x 1 = 1}, ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)), ?_, ?_, ?_⟩
  · exact helperForText_19_0_13_lineSet_polyhedral
  · exact helperForText_19_0_13_originSingleton_polyhedral
  · exact helperForText_19_0_13_notPolyhedral_convexHull_line_union_origin

/-- Helper for Text 19.0.14: every polytope in `ℝ^n` is compact. -/
lemma helperForText_19_0_14_compact_of_polytope
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolytope n C) :
    IsCompact C := by
  rcases hCpoly with ⟨T, hTfinite, hTeq⟩
  rw [hTeq]
  exact hTfinite.isCompact_convexHull

/-- Helper for Text 19.0.14: a nonempty compact set in `ℝ^n` invariant under translation
by `d` must satisfy `d = 0`. -/
lemma helperForText_19_0_14_shift_eq_zero_of_compact_translateInvariant
    {n : ℕ} {C : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty)
    (htranslate : C + {d} = C) :
    d = 0 := by
  have hcontFun : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ d) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ (fun i hi => (continuous_apply i).mul continuous_const))
  have hcont : ContinuousOn (fun x : Fin n → ℝ => x ⬝ᵥ d) C := hcontFun.continuousOn
  rcases hCcompact.exists_isMaxOn hCnonempty hcont with ⟨x, hxC, hxMax⟩
  have hxPlusMemAdd : x + d ∈ C + {d} := by
    refine Set.mem_add.2 ?_
    refine ⟨x, hxC, d, ?_, ?_⟩
    · simp
    · rfl
  have hxPlusMem : x + d ∈ C := by
    simpa [htranslate] using hxPlusMemAdd
  have hmaxIneq : (x + d) ⬝ᵥ d ≤ x ⬝ᵥ d := by
    exact (isMaxOn_iff.mp hxMax) (x + d) hxPlusMem
  have hddLeZero : d ⬝ᵥ d ≤ 0 := by
    have hsumIneq : x ⬝ᵥ d + d ⬝ᵥ d ≤ x ⬝ᵥ d := by
      simpa [add_dotProduct] using hmaxIneq
    linarith
  have hzeroLeDd : 0 ≤ d ⬝ᵥ d := by
    simpa [dotProduct] using (Finset.sum_nonneg (fun i hi => mul_self_nonneg (d i)))
  have hddEqZero : d ⬝ᵥ d = 0 := le_antisymm hddLeZero hzeroLeDd
  exact (dotProduct_self_eq_zero.mp hddEqZero)

/-- Helper for Text 19.0.14: if two translates of `S` both equal `C`, then the
translation vectors coincide. -/
lemma helperForText_19_0_14_unique_translation_parameter
    {n : ℕ} {C S : Set (Fin n → ℝ)} {y₀ y : Fin n → ℝ}
    (hSnonempty : S.Nonempty)
    (hSC : S ⊆ C)
    (hCcompact : IsCompact C)
    (hy₀ : S + {y₀} = C)
    (hy : S + {y} = C) :
    y = y₀ := by
  have hCnonempty : C.Nonempty := by
    rcases hSnonempty with ⟨s, hsS⟩
    exact ⟨s, hSC hsS⟩
  let d : Fin n → ℝ := y - y₀
  have htranslateSubsetLeft : C + {d} ⊆ C := by
    intro z hz
    rcases Set.mem_add.1 hz with ⟨c, hcC, u, huSingleton, hzu⟩
    have huEq : u = d := by
      simpa using huSingleton
    have hcS : c ∈ S + {y₀} := by
      simpa [hy₀] using hcC
    rcases Set.mem_add.1 hcS with ⟨s, hsS, v, hvSingleton, hsv⟩
    have hvEq : v = y₀ := by
      simpa using hvSingleton
    have hzEq : z = s + y := by
      calc
        z = c + u := by
          simpa using hzu.symm
        _ = c + d := by
          rw [huEq]
        _ = (s + v) + d := by
          rw [hsv]
        _ = (s + y₀) + d := by
          rw [hvEq]
        _ = s + y := by
          dsimp [d]
          abel_nf
    have hsAddMem : s + y ∈ S + {y} := by
      refine Set.mem_add.2 ?_
      refine ⟨s, hsS, y, ?_, ?_⟩
      · simp
      · rfl
    have hzMemTranslate : z ∈ S + {y} := by
      exact hzEq ▸ hsAddMem
    have hzMemC : z ∈ C := by
      simpa [hy] using hzMemTranslate
    exact hzMemC
  have htranslateSubsetRight : C ⊆ C + {d} := by
    intro z hzC
    have hzS : z ∈ S + {y} := by
      simpa [hy] using hzC
    rcases Set.mem_add.1 hzS with ⟨s, hsS, u, huSingleton, hzu⟩
    have huEq : u = y := by
      simpa using huSingleton
    have hsAddMemY₀ : s + y₀ ∈ S + {y₀} := by
      refine Set.mem_add.2 ?_
      refine ⟨s, hsS, y₀, ?_, ?_⟩
      · simp
      · rfl
    have hsAddMemC : s + y₀ ∈ C := by
      simpa [hy₀] using hsAddMemY₀
    have hzEq : z = (s + y₀) + d := by
      calc
        z = s + u := by
          simpa using hzu.symm
        _ = s + y := by
          rw [huEq]
        _ = (s + y₀) + d := by
          dsimp [d]
          abel_nf
    have hzMemAdd : z ∈ C + {d} := by
      refine Set.mem_add.2 ?_
      refine ⟨s + y₀, hsAddMemC, d, ?_, ?_⟩
      · simp
      · exact hzEq.symm
    exact hzMemAdd
  have htranslate : C + {d} = C := by
    exact Set.Subset.antisymm htranslateSubsetLeft htranslateSubsetRight
  have hdEqZero : d = 0 :=
    helperForText_19_0_14_shift_eq_zero_of_compact_translateInvariant
      (C := C) (d := d) hCcompact hCnonempty htranslate
  have hySubEqZero : y - y₀ = 0 := by
    simpa [d] using hdEqZero
  exact sub_eq_zero.mp hySubEqZero

/-- Helper for Text 19.0.14: both the empty set and every singleton in `ℝ^n` are
polytopes. -/
lemma helperForText_19_0_14_polytope_of_empty_or_singleton
    (n : ℕ) :
    IsPolytope n (∅ : Set (Fin n → ℝ)) ∧
      ∀ y₀ : Fin n → ℝ, IsPolytope n ({y₀} : Set (Fin n → ℝ)) := by
  constructor
  · refine ⟨∅, Set.finite_empty, ?_⟩
    simp
  · intro y₀
    refine ⟨{y₀}, Set.finite_singleton y₀, ?_⟩
    simp

/-- Helper for Text 19.0.14: a set equals a singleton once it contains the center point
and every element equals that point. -/
lemma helperForText_19_0_14_eq_singleton_of_mem_and_unique
    {α : Type*} {D : Set α} {y₀ : α}
    (hy₀D : y₀ ∈ D)
    (hunique : ∀ y, y ∈ D → y = y₀) :
    D = ({y₀} : Set α) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hyD
    simp [hunique y hyD]
  · intro y hySingleton
    rcases hySingleton with rfl
    exact hy₀D

/-- Text 19.0.14: Let `C ⊆ ℝ^n` be a convex polytope and let `S ⊆ C` be nonempty. For
`y ∈ ℝ^n`, define the translate `S + {y}` and `D := {y | S + {y} = C}`. Then `D` is a
possibly empty convex polytope in `ℝ^n`. -/
theorem polytope_setOf_translate_eq
    (n : ℕ) (C S : Set (Fin n → ℝ)) :
    IsPolytope n C →
      S.Nonempty →
        S ⊆ C →
          IsPolytope n {y : Fin n → ℝ | S + {y} = C} := by
  intro hCpoly hSnonempty hSC
  let D : Set (Fin n → ℝ) := {y : Fin n → ℝ | S + {y} = C}
  change IsPolytope n D
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨y₀, hy₀⟩
    have hCcompact : IsCompact C :=
      helperForText_19_0_14_compact_of_polytope (n := n) (C := C) hCpoly
    have hDeqSingleton : D = ({y₀} : Set (Fin n → ℝ)) := by
      refine helperForText_19_0_14_eq_singleton_of_mem_and_unique
        (D := D) (y₀ := y₀) hy₀ ?_
      intro y hyD
      exact
        helperForText_19_0_14_unique_translation_parameter
          (C := C) (S := S) (y₀ := y₀) (y := y)
          hSnonempty hSC hCcompact hy₀ hyD
    have hSingletonPoly : IsPolytope n ({y₀} : Set (Fin n → ℝ)) :=
      (helperForText_19_0_14_polytope_of_empty_or_singleton n).2 y₀
    rw [hDeqSingleton]
    exact hSingletonPoly
  · have hDforallNotMem : ∀ y : Fin n → ℝ, y ∉ D := by
      intro y hyD
      exact hDne ⟨y, hyD⟩
    have hDeqEmpty : D = (∅ : Set (Fin n → ℝ)) :=
      Set.eq_empty_iff_forall_notMem.mpr hDforallNotMem
    have hEmptyPoly : IsPolytope n (∅ : Set (Fin n → ℝ)) :=
      (helperForText_19_0_14_polytope_of_empty_or_singleton n).1
    rw [hDeqEmpty]
    exact hEmptyPoly


end Section19
end Chap19
