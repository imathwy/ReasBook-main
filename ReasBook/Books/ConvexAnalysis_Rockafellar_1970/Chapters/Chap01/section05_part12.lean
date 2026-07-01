/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part11

section Chap01
section Section05

/-- The simplex of nonnegative weights summing to `1`. -/
def simplexSet (m : Nat) : Set (Fin m → Real) :=
  { lam | (∀ i, 0 ≤ lam i) ∧ Finset.univ.sum (fun i => lam i) = (1 : Real) }

/-- The simplex is convex. -/
lemma convex_simplexSet {m : Nat} : Convex ℝ (simplexSet m) := by
  classical
  intro lam1 h1 lam2 h2 a b ha hb hab
  rcases h1 with ⟨h1nonneg, h1sum⟩
  rcases h2 with ⟨h2nonneg, h2sum⟩
  refine ⟨?_, ?_⟩
  · intro i
    have h1' : 0 ≤ a * lam1 i := by
      exact mul_nonneg ha (h1nonneg i)
    have h2' : 0 ≤ b * lam2 i := by
      exact mul_nonneg hb (h2nonneg i)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg h1' h2'
  · have hsum :
        Finset.univ.sum (fun i => (a * lam1 i + b * lam2 i)) =
          a * Finset.univ.sum (fun i => lam1 i) +
            b * Finset.univ.sum (fun i => lam2 i) := by
        calc
          Finset.univ.sum (fun i => a * lam1 i + b * lam2 i) =
              Finset.univ.sum (fun i => a * lam1 i) +
                Finset.univ.sum (fun i => b * lam2 i) := by
                  simp [Finset.sum_add_distrib]
          _ = a * Finset.univ.sum (fun i => lam1 i) +
                b * Finset.univ.sum (fun i => lam2 i) := by
                  simp [Finset.mul_sum]
    calc
      Finset.univ.sum (fun i => (a • lam1 + b • lam2) i) =
          Finset.univ.sum (fun i => a * lam1 i + b * lam2 i) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      _ = a * Finset.univ.sum (fun i => lam1 i) +
            b * Finset.univ.sum (fun i => lam2 i) := hsum
      _ = a * (1 : Real) + b * (1 : Real) := by simp [h1sum, h2sum]
      _ = (1 : Real) := by linarith [hab]

/-- Projection onto the `x` coordinates (first `n`) in `Fin (n+m)`. -/
def projXLinearMap {n m : Nat} : (Fin (n + m) → Real) →ₗ[Real] (Fin n → Real) :=
  { toFun := fun x i => x (Fin.castAdd m i)
    map_add' := by
      intro x y
      ext i
      rfl
    map_smul' := by
      intro c x
      ext i
      rfl }

/-- Projection onto the `λ` coordinates (last `m`) in `Fin (n+m)`. -/
def projLamLinearMap {n m : Nat} : (Fin (n + m) → Real) →ₗ[Real] (Fin m → Real) :=
  { toFun := fun x i => x (Fin.natAdd n i)
    map_add' := by
      intro x y
      ext i
      rfl
    map_smul' := by
      intro c x
      ext i
      rfl }

/-- Linear map selecting the `i`th `λ` coordinate and all `x` coordinates. -/
def lamXLinearMap {n m : Nat} (i : Fin m) :
    (Fin (n + m) → Real) →ₗ[Real] (Fin (n + 1) → Real) :=
  { toFun := fun x =>
      fun j =>
        Fin.cases (x (Fin.natAdd n i)) (fun k : Fin n => x (Fin.castAdd m k)) j
    map_add' := by
      intro x y
      ext j
      cases j using Fin.cases <;> simp
    map_smul' := by
      intro c x
      ext j
      cases j using Fin.cases <;> simp }

/-- Perspective convexity after selecting the `i`th `λ` coordinate. -/
lemma convexFunctionOn_perspective_coord {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    (i : Fin m) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
      (fun x =>
        if 0 ≤ x (Fin.natAdd n i) then
          rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
        else
          (⊤ : EReal)) := by
  have hpers :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + 1) → Real)))
        (fun y =>
          if 0 ≤ y 0 then
            rightScalarMultiple (f i) (y 0) (fun k => y k.succ)
          else
            (⊤ : EReal)) :=
    (perspective_posHomogeneous_convex (f := f i) (hf := hf i)).1.1
  have hpre :=
    (convexFunctionOn_precomp_linearMap (A := lamXLinearMap (n := n) (m := m) i)
      (g := fun y =>
        if 0 ≤ y 0 then
          rightScalarMultiple (f i) (y 0) (fun k => y k.succ)
        else
          (⊤ : EReal))
      hpers)
  simpa [lamXLinearMap] using hpre

/-- Indicator of the simplex, precomposed with the `λ` projection, is convex. -/
lemma convexFunctionOn_indicator_simplex_precomp {n m : Nat} :
    ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
      (fun x => indicatorFunction (simplexSet m) (projLamLinearMap (n := n) (m := m) x)) := by
  have hconv' : ConvexFunction (indicatorFunction (simplexSet m)) :=
    convexFunction_indicator_of_convex (C := simplexSet m) (convex_simplexSet (m := m))
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
        (indicatorFunction (simplexSet m)) := by
    simpa [ConvexFunction] using hconv'
  simpa [projLamLinearMap] using
    (convexFunctionOn_precomp_linearMap (A := projLamLinearMap (n := n) (m := m))
      (g := indicatorFunction (simplexSet m)) hconv)

/-- Non-`⊥` is preserved by finite sums. -/
lemma finset_sum_ne_bot {α : Type*} [DecidableEq α] (s : Finset α) (f : α → EReal)
    (h : ∀ a ∈ s, f a ≠ (⊥ : EReal)) : s.sum f ≠ (⊥ : EReal) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ha hs h
    have hfa : f a ≠ (⊥ : EReal) := h a (by simp [ha])
    have hsum : s.sum f ≠ (⊥ : EReal) := hs (by
      intro b hb
      exact h b (by simp [hb]))
    simpa [Finset.sum_insert, ha] using add_ne_bot_of_notbot hfa hsum

/-- Theorem 5.8.2: Let `f_1, ..., f_m` be proper convex functions on `ℝ^n`. Then the
function `g(x) = inf { (f_1 λ_1)(x) + ... + (f_m λ_m)(x) | λ_i ≥ 0, λ_1 + ... + λ_m = 1 }`
is convex. -/
theorem convexFunctionOn_inf_sum_rightScalarMultiple_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x =>
        sInf { z : EReal |
          ∃ lam : Fin m → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
            z = Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) x) }) := by
  classical
  -- Work on the combined space with `x` first and `λ` last.
  let gsum : (Fin (n + m) → Real) → EReal :=
    fun x =>
      Finset.univ.sum (fun i =>
        if 0 ≤ x (Fin.natAdd n i) then
          rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
        else
          (⊤ : EReal))
  let gind : (Fin (n + m) → Real) → EReal :=
    fun x => indicatorFunction (simplexSet m) (projLamLinearMap (n := n) (m := m) x)
  have hsum_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real))) gsum := by
    have hpers :
        ∀ i, ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
          (fun x =>
            if 0 ≤ x (Fin.natAdd n i) then
              rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
            else
              (⊤ : EReal)) := by
      intro i
      simpa using (convexFunctionOn_perspective_coord (f := f) hf i)
    have hnotbot :
        ∀ i (x : Fin (n + m) → Real),
          (if 0 ≤ x (Fin.natAdd n i) then
              rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
            else
              (⊤ : EReal)) ≠ (⊥ : EReal) := by
      intro i x
      by_cases hpos : 0 ≤ x (Fin.natAdd n i)
      · by_cases hzero : x (Fin.natAdd n i) = 0
        · have hval :
            rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) =
              (if (fun k => x (Fin.castAdd m k)) = 0 then (0 : EReal) else ⊤) := by
            simpa using
              (rightScalarMultiple_zero_eval (f := f i) (x := fun k => x (Fin.castAdd m k))
                (hne := (hf i).2.1))
          by_cases hx : (fun k => x (Fin.castAdd m k)) = 0
          · have hval' :
                rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (0 : EReal) := by
              simpa [hx] using hval
            have hnotbot' :
                rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
              simp [hval']
            simpa [hpos, hzero, hx] using hnotbot'
          · have hval' :
                rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (⊤ : EReal) := by
              simpa [hx] using hval
            have hnotbot' :
                rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
              simp [hval']
            simpa [hpos, hzero] using hnotbot'
        · have hpos' : 0 < x (Fin.natAdd n i) := lt_of_le_of_ne hpos (Ne.symm hzero)
          have hval :=
            rightScalarMultiple_pos (f := f i) (lam := x (Fin.natAdd n i))
              (_hf := (hf i).1) (hlam := hpos') (x := fun k => x (Fin.castAdd m k))
          have hnotbot :
              rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k)) ≠ ⊥ := by
            simpa [hval] using
              ereal_mul_ne_bot_of_pos hpos'
                ((hf i).2.2 _ (by simp))
          simpa [hpos] using hnotbot
      · simp [hpos]
    -- Use the linear-combination lemma with weights all `1`.
    have hsum' :
        ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
          (fun x =>
            Finset.univ.sum (fun i =>
              ((1 : Real) : EReal) *
                (if 0 ≤ x (Fin.natAdd n i) then
                    rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
                  else
                    (⊤ : EReal)))) := by
      refine
        convexFunctionOn_linearCombination_of_proper (lam := fun _ : Fin m => (1 : Real))
          ?_ ?_
      · intro i
        simp
      · intro i
        refine ⟨hpers i, ?_, ?_⟩
        · -- Nonempty epigraph from properness of perspective and surjectivity.
          rcases (perspective_posHomogeneous_convex (f := f i) (hf := hf i)).1.2.1 with ⟨p, hp⟩
          -- Use a point with the same `x` and `λ_i`, others `0`.
          let x' : Fin n → Real := fun k => p.1 k.succ
          let lam' : Fin m → Real := fun j => if j = i then p.1 0 else 0
          refine ⟨(Fin.append x' lam', p.2), ?_⟩
          change
            Set.univ (Fin.append x' lam') ∧
              (if 0 ≤ (Fin.append x' lam') (Fin.natAdd n i) then
                  rightScalarMultiple (f i) ((Fin.append x' lam') (Fin.natAdd n i))
                    (fun k => (Fin.append x' lam') (Fin.castAdd m k))
                else
                  (⊤ : EReal)) ≤ (p.2 : EReal)
          constructor
          · change True
            trivial
          · simpa [x', lam'] using hp.2
        · intro x hx
          have hnotbot' := hnotbot i x
          simpa using hnotbot'
    simpa [gsum] using hsum'
  have hsum_notbot :
      ∀ x : Fin (n + m) → Real, gsum x ≠ (⊥ : EReal) := by
    intro x
    refine finset_sum_ne_bot (s := (Finset.univ : Finset (Fin m)))
      (f := fun i =>
        if 0 ≤ x (Fin.natAdd n i) then
          rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
        else
          (⊤ : EReal)) ?_
    intro i hi
    by_cases hpos : 0 ≤ x (Fin.natAdd n i)
    · by_cases hzero : x (Fin.natAdd n i) = 0
      · have hval :
          rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) =
            (if (fun k => x (Fin.castAdd m k)) = 0 then (0 : EReal) else ⊤) := by
          simpa using
            (rightScalarMultiple_zero_eval (f := f i) (x := fun k => x (Fin.castAdd m k))
              (hne := (hf i).2.1))
        by_cases hx : (fun k => x (Fin.castAdd m k)) = 0
        · have hval' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (0 : EReal) := by
            simpa [hx] using hval
          have hnotbot' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
            simp [hval']
          simpa [hpos, hzero, hx] using hnotbot'
        · have hval' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (⊤ : EReal) := by
            simpa [hx] using hval
          have hnotbot' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
            simp [hval']
          simpa [hpos, hzero] using hnotbot'
      · have hpos' : 0 < x (Fin.natAdd n i) := lt_of_le_of_ne hpos (Ne.symm hzero)
        have hval :=
          rightScalarMultiple_pos (f := f i) (lam := x (Fin.natAdd n i))
            (_hf := (hf i).1) (hlam := hpos') (x := fun k => x (Fin.castAdd m k))
        have hnotbot :
            rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k)) ≠ ⊥ := by
          simpa [hval] using
            ereal_mul_ne_bot_of_pos hpos'
              ((hf i).2.2 _ (by simp))
        simpa [hpos] using hnotbot
    · simp [hpos]
  have hind_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real))) gind :=
    convexFunctionOn_indicator_simplex_precomp (n := n) (m := m)
  have hind_notbot : ∀ x, gind x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : projLamLinearMap (n := n) (m := m) x ∈ simplexSet m
    · simp [gind, indicatorFunction, hx]
    · simp [gind, indicatorFunction, hx]
  have hHconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
        (fun x => gind x + gsum x) := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin (n + m) → Real)))
        (f := fun x => gind x + gsum x) (hC := convex_univ)
        (hnotbot := ?_)).2 ?_
    · intro x hx
      exact add_ne_bot_of_notbot (hind_notbot x) (hsum_notbot x)
    · intro x hx y hy t ht0 ht1
      have hseg :=
        segment_inequality_add_univ (hf1 := hind_conv) (hf2 := hsum_conv)
          (hnotbot1 := hind_notbot) (hnotbot2 := hsum_notbot) x y t ht0 ht1
      simpa using hseg
  have hconv :=
    convexFunctionOn_inf_fiber_linearMap (A := projXLinearMap (n := n) (m := m))
      (h := fun x => gind x + gsum x) hHconv
  -- Unpack the infimum over the fiber.
  refine (by
    convert hconv using 1
    funext x
    let T : Set EReal :=
      { z : EReal |
        ∃ lam : Fin m → Real,
          (∀ i, 0 ≤ lam i) ∧
          (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
          z = Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) x) }
    let S : Set EReal :=
      { z : EReal |
        ∃ x' : Fin (n + m) → Real,
          projXLinearMap (n := n) (m := m) x' = x ∧ z = gind x' + gsum x' }
    have hset : S = insert (⊤ : EReal) T := by
      ext z
      constructor
      · rintro ⟨x', hx', rfl⟩
        let lam : Fin m → Real := fun i => x' (Fin.natAdd n i)
        have hxcoord : (fun k => x' (Fin.castAdd m k)) = x := by
          ext k
          have h := congrArg (fun f => f k) hx'
          simpa [projXLinearMap] using h
        by_cases hlam : lam ∈ simplexSet m
        · have hlam' :
              (∀ i, 0 ≤ lam i) ∧
                (Finset.univ.sum (fun i => lam i) = (1 : Real)) := by
            simpa [simplexSet] using hlam
          rcases hlam' with ⟨hlam_nonneg, hlam_sum⟩
          have hgsum :
              gsum x' =
                Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) x) := by
            simp [gsum, lam, hxcoord, hlam_nonneg]
          have hgind : gind x' = (0 : EReal) := by
            have hlam'' : projLamLinearMap (n := n) (m := m) x' ∈ simplexSet m := by
              simpa [projLamLinearMap, lam] using hlam
            simp [gind, indicatorFunction, hlam'']
          have hmem :
              gind x' + gsum x' = ⊤ ∨ gind x' + gsum x' ∈ T := by
            refine Or.inr ?_
            refine ⟨lam, hlam_nonneg, hlam_sum, ?_⟩
            simp [hgind, hgsum]
          simpa [Set.mem_insert_iff, T] using hmem
        · have hmem :
              gind x' + gsum x' = ⊤ ∨ gind x' + gsum x' ∈ T := by
            refine Or.inl ?_
            have hlam'' : projLamLinearMap (n := n) (m := m) x' ∉ simplexSet m := by
              simpa [projLamLinearMap, lam] using hlam
            have hgind : gind x' = (⊤ : EReal) := by
              simp [gind, indicatorFunction, hlam'']
            have htop : gind x' + gsum x' = (⊤ : EReal) := by
              simpa [hgind] using (EReal.top_add_of_ne_bot (hsum_notbot x'))
            exact htop
          simpa [Set.mem_insert_iff, T] using hmem
      · intro hz
        have hz' : z = (⊤ : EReal) ∨ z ∈ T := by
          simpa [Set.mem_insert_iff, T] using hz
        rcases hz' with hz | hz
        · subst hz
          let lam0 : Fin m → Real := fun _ => 0
          let x' : Fin (n + m) → Real := Fin.append x lam0
          have hnot : lam0 ∉ simplexSet m := by
            simp [lam0, simplexSet]
          refine ⟨x', ?_, ?_⟩
          · ext i
            simp [projXLinearMap, x']
          · have hlam0 : projLamLinearMap (n := n) (m := m) x' ∉ simplexSet m := by
              simpa [projLamLinearMap, x', lam0] using hnot
            have hgind : gind x' = (⊤ : EReal) := by
              simp [gind, indicatorFunction, hlam0]
            have htop : gind x' + gsum x' = (⊤ : EReal) := by
              simpa [hgind] using (EReal.top_add_of_ne_bot (hsum_notbot x'))
            exact htop.symm
        · rcases hz with ⟨lam, hlam_nonneg, hlam_sum, hz⟩
          let x' : Fin (n + m) → Real := Fin.append x lam
          have hproj : projXLinearMap (n := n) (m := m) x' = x := by
            ext i
            simp [projXLinearMap, x']
          have hgsum :
              gsum x' = Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) x) := by
            simp [gsum, x', hlam_nonneg]
          have hgind : gind x' = (0 : EReal) := by
            have hlam' : projLamLinearMap (n := n) (m := m) x' ∈ simplexSet m := by
              have hlam'' : lam ∈ simplexSet m := by
                exact ⟨hlam_nonneg, hlam_sum⟩
              simpa [projLamLinearMap, x'] using hlam''
            simp [gind, indicatorFunction, hlam']
          refine ⟨x', hproj, ?_⟩
          simp [hz, hgind, hgsum]
    calc
      sInf T = sInf (insert (⊤ : EReal) T) := by
        symm
        calc
          sInf (insert (⊤ : EReal) T) = (⊤ : EReal) ⊓ sInf T := by
            simp [sInf_insert]
          _ = sInf T := by
            simp
      _ = sInf S := by
        simp [hset])

/-- The pointwise supremum of the perspective-coordinate functions is convex. -/
lemma convexFunctionOn_gsup {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
      (fun x =>
        iSup (fun i : Fin m =>
          if 0 ≤ x (Fin.natAdd n i) then
            rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
          else
            (⊤ : EReal))) := by
  classical
  have hpers :
      ∀ i : Fin m,
        ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
          (fun x =>
            if 0 ≤ x (Fin.natAdd n i) then
              rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
            else
              (⊤ : EReal)) := by
    intro i
    simpa using (convexFunctionOn_perspective_coord (f := f) hf i)
  simpa using
    (convexFunctionOn_iSup (f := fun i x =>
      if 0 ≤ x (Fin.natAdd n i) then
        rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
      else
        (⊤ : EReal)) hpers)

/-- The pointwise supremum of the perspective-coordinate functions is never `⊥` when `m > 0`. -/
lemma gsup_ne_bot {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    (hm : 0 < m) :
    ∀ x : Fin (n + m) → Real,
      (iSup (fun i : Fin m =>
        if 0 ≤ x (Fin.natAdd n i) then
          rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
        else
          (⊤ : EReal))) ≠ (⊥ : EReal) := by
  classical
  intro x
  set term : Fin m → EReal :=
    fun i =>
      if 0 ≤ x (Fin.natAdd n i) then
        rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
      else
        (⊤ : EReal)
  have hnotbot_term : ∀ i, term i ≠ (⊥ : EReal) := by
    intro i
    by_cases hpos : 0 ≤ x (Fin.natAdd n i)
    · by_cases hzero : x (Fin.natAdd n i) = 0
      · have hval :
          rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) =
            (if (fun k => x (Fin.castAdd m k)) = 0 then (0 : EReal) else ⊤) := by
          simpa using
            (rightScalarMultiple_zero_eval (f := f i) (x := fun k => x (Fin.castAdd m k))
              (hne := (hf i).2.1))
        by_cases hx : (fun k => x (Fin.castAdd m k)) = 0
        · have hval' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (0 : EReal) := by
            simpa [hx] using hval
          have hnotbot' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
            simp [hval']
          simpa [term, hpos, hzero, hx] using hnotbot'
        · have hval' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) = (⊤ : EReal) := by
            simpa [hx] using hval
          have hnotbot' :
              rightScalarMultiple (f i) 0 (fun k => x (Fin.castAdd m k)) ≠ (⊥ : EReal) := by
            simp [hval']
          simpa [term, hpos, hzero] using hnotbot'
      · have hpos' : 0 < x (Fin.natAdd n i) := lt_of_le_of_ne hpos (Ne.symm hzero)
        have hval :=
          rightScalarMultiple_pos (f := f i) (lam := x (Fin.natAdd n i))
            (_hf := (hf i).1) (hlam := hpos') (x := fun k => x (Fin.castAdd m k))
        have hnotbot :
            rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k)) ≠ ⊥ := by
          simpa [hval] using
            ereal_mul_ne_bot_of_pos hpos'
              ((hf i).2.2 _ (by simp))
        simpa [term, hpos] using hnotbot
    · simp [term, hpos]
  have i0 : Fin m := ⟨0, hm⟩
  by_contra hbot
  have hbot' : iSup term = (⊥ : EReal) := by
    simpa [term] using hbot
  have hle : term i0 ≤ iSup term := by
    exact le_iSup (fun i => term i) i0
  have hle_bot : term i0 ≤ (⊥ : EReal) := by
    simpa [hbot'] using hle
  have hterm : term i0 = (⊥ : EReal) := (le_bot_iff).1 hle_bot
  exact (hnotbot_term i0) hterm

/-- Adding the simplex indicator to the supremum perspective term is convex. -/
lemma convexFunctionOn_gind_add_gsup {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    (hm : 0 < m) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
      (fun x =>
        indicatorFunction (simplexSet m) (projLamLinearMap (n := n) (m := m) x) +
          iSup (fun i : Fin m =>
            if 0 ≤ x (Fin.natAdd n i) then
              rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
            else
              (⊤ : EReal))) := by
  classical
  let gind : (Fin (n + m) → Real) → EReal :=
    fun x => indicatorFunction (simplexSet m) (projLamLinearMap (n := n) (m := m) x)
  let gsup : (Fin (n + m) → Real) → EReal :=
    fun x =>
      iSup (fun i : Fin m =>
        if 0 ≤ x (Fin.natAdd n i) then
          rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
        else
          (⊤ : EReal))
  have hind_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real))) gind :=
    convexFunctionOn_indicator_simplex_precomp (n := n) (m := m)
  have hsup_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real))) gsup := by
    simpa [gsup] using (convexFunctionOn_gsup (n := n) (m := m) (f := f) hf)
  have hind_notbot : ∀ x, gind x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : projLamLinearMap (n := n) (m := m) x ∈ simplexSet m
    · simp [gind, indicatorFunction, hx]
    · simp [gind, indicatorFunction, hx]
  have hsup_notbot : ∀ x, gsup x ≠ (⊥ : EReal) := by
    simpa [gsup] using (gsup_ne_bot (n := n) (m := m) (f := f) hf hm)
  have hHconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
        (fun x => gind x + gsup x) := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin (n + m) → Real)))
        (f := fun x => gind x + gsup x) (hC := convex_univ)
        (hnotbot := ?_)).2 ?_
    · intro x hx
      exact add_ne_bot_of_notbot (hind_notbot x) (hsup_notbot x)
    · intro x hx y hy t ht0 ht1
      have hseg :=
        segment_inequality_add_univ (hf1 := hind_conv) (hf2 := hsup_conv)
          (hnotbot1 := hind_notbot) (hnotbot2 := hsup_notbot) x y t ht0 ht1
      simpa using hseg
  simpa [gind, gsup] using hHconv

/-- Theorem 5.8.3: Let `f_1, ..., f_m` be proper convex functions on `ℝ^n`. Then
`h(x) = inf { max { (f_1 λ_1)(x), ..., (f_m λ_m)(x) } | λ_i ≥ 0, λ_1 + ... + λ_m = 1 }`
is convex. -/
theorem convexFunctionOn_inf_iSup_rightScalarMultiple_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x =>
        sInf { z : EReal |
          ∃ lam : Fin m → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
            z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) x) }) := by
  classical
  by_cases hm : m = 0
  · subst hm
    have hconst :
        (fun x : Fin n → Real =>
          sInf { z : EReal |
            ∃ lam : Fin 0 → Real,
              (∀ i, 0 ≤ lam i) ∧
              (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
              z = iSup (fun i : Fin 0 => rightScalarMultiple (f i) (lam i) x) }) =
          (fun _ => (⊤ : EReal)) := by
      funext x
      simp
    simpa [hconst] using
      (convexFunctionOn_const_top (C := (Set.univ : Set (Fin n → Real))))
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    -- Work on the combined space with `x` first and `λ` last.
    let gsup : (Fin (n + m) → Real) → EReal :=
      fun x =>
        iSup (fun i : Fin m =>
          if 0 ≤ x (Fin.natAdd n i) then
            rightScalarMultiple (f i) (x (Fin.natAdd n i)) (fun k => x (Fin.castAdd m k))
          else
            (⊤ : EReal))
    let gind : (Fin (n + m) → Real) → EReal :=
      fun x => indicatorFunction (simplexSet m) (projLamLinearMap (n := n) (m := m) x)
    have hsup_notbot : ∀ x, gsup x ≠ (⊥ : EReal) := by
      simpa [gsup] using (gsup_ne_bot (n := n) (m := m) (f := f) hf hm')
    have hHconv :
        ConvexFunctionOn (S := (Set.univ : Set (Fin (n + m) → Real)))
          (fun x => gind x + gsup x) := by
      simpa [gind, gsup] using
        (convexFunctionOn_gind_add_gsup (n := n) (m := m) (f := f) hf hm')
    have hconv :=
      convexFunctionOn_inf_fiber_linearMap (A := projXLinearMap (n := n) (m := m))
        (h := fun x => gind x + gsup x) hHconv
    -- Unpack the infimum over the fiber.
    refine (by
      convert hconv using 1
      funext x
      let T : Set EReal :=
        { z : EReal |
          ∃ lam : Fin m → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
            z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) x) }
      let S : Set EReal :=
        { z : EReal |
          ∃ x' : Fin (n + m) → Real,
            projXLinearMap (n := n) (m := m) x' = x ∧ z = gind x' + gsup x' }
      have hset : S = insert (⊤ : EReal) T := by
        ext z
        constructor
        · rintro ⟨x', hx', rfl⟩
          let lam : Fin m → Real := fun i => x' (Fin.natAdd n i)
          have hxcoord : (fun k => x' (Fin.castAdd m k)) = x := by
            ext k
            have h := congrArg (fun f => f k) hx'
            simpa [projXLinearMap] using h
          by_cases hlam : lam ∈ simplexSet m
          · have hlam' :
                (∀ i, 0 ≤ lam i) ∧
                  (Finset.univ.sum (fun i => lam i) = (1 : Real)) := by
              simpa [simplexSet] using hlam
            rcases hlam' with ⟨hlam_nonneg, hlam_sum⟩
            have hgsup :
                gsup x' =
                  iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) x) := by
              simp [gsup, lam, hxcoord, hlam_nonneg]
            have hgind : gind x' = (0 : EReal) := by
              have hlam'' : projLamLinearMap (n := n) (m := m) x' ∈ simplexSet m := by
                simpa [projLamLinearMap, lam] using hlam
              simp [gind, indicatorFunction, hlam'']
            have hmem :
                gind x' + gsup x' = ⊤ ∨ gind x' + gsup x' ∈ T := by
              refine Or.inr ?_
              refine ⟨lam, hlam_nonneg, hlam_sum, ?_⟩
              simp [hgind, hgsup]
            simpa [Set.mem_insert_iff, T] using hmem
          · have hmem :
                gind x' + gsup x' = ⊤ ∨ gind x' + gsup x' ∈ T := by
              refine Or.inl ?_
              have hlam'' : projLamLinearMap (n := n) (m := m) x' ∉ simplexSet m := by
                simpa [projLamLinearMap, lam] using hlam
              have hgind : gind x' = (⊤ : EReal) := by
                simp [gind, indicatorFunction, hlam'']
              have htop : gind x' + gsup x' = (⊤ : EReal) := by
                simpa [hgind] using (EReal.top_add_of_ne_bot (hsup_notbot x'))
              exact htop
            simpa [Set.mem_insert_iff, T] using hmem
        · intro hz
          have hz' : z = (⊤ : EReal) ∨ z ∈ T := by
            simpa [Set.mem_insert_iff, T] using hz
          rcases hz' with hz | hz
          · subst hz
            let lam0 : Fin m → Real := fun _ => 0
            let x' : Fin (n + m) → Real := Fin.append x lam0
            have hnot : lam0 ∉ simplexSet m := by
              simp [lam0, simplexSet]
            refine ⟨x', ?_, ?_⟩
            · ext i
              simp [projXLinearMap, x']
            · have hlam0 : projLamLinearMap (n := n) (m := m) x' ∉ simplexSet m := by
                simpa [projLamLinearMap, x', lam0] using hnot
              have hgind : gind x' = (⊤ : EReal) := by
                simp [gind, indicatorFunction, hlam0]
              have htop : gind x' + gsup x' = (⊤ : EReal) := by
                simpa [hgind] using (EReal.top_add_of_ne_bot (hsup_notbot x'))
              exact htop.symm
          · rcases hz with ⟨lam, hlam_nonneg, hlam_sum, hz⟩
            let x' : Fin (n + m) → Real := Fin.append x lam
            have hproj : projXLinearMap (n := n) (m := m) x' = x := by
              ext i
              simp [projXLinearMap, x']
            have hgsup :
                gsup x' = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) x) := by
              simp [gsup, x', hlam_nonneg]
            have hgind : gind x' = (0 : EReal) := by
              have hlam' : projLamLinearMap (n := n) (m := m) x' ∈ simplexSet m := by
                have hlam'' : lam ∈ simplexSet m := by
                  exact ⟨hlam_nonneg, hlam_sum⟩
                simpa [projLamLinearMap, x'] using hlam''
              simp [gind, indicatorFunction, hlam']
            refine ⟨x', hproj, ?_⟩
            simp [hz, hgind, hgsup]
      calc
        sInf T = sInf (insert (⊤ : EReal) T) := by
          symm
          calc
            sInf (insert (⊤ : EReal) T) = (⊤ : EReal) ⊓ sInf T := by
              simp [sInf_insert]
            _ = sInf T := by
              simp
        _ = sInf S := by
          simp [hset])

/-- Convex combinations preserve the simplex constraints. -/
lemma lam_combo_in_simplex {m : Nat} {lamx lamy : Fin m → Real} {t : Real}
    (hx : lamx ∈ simplexSet m) (hy : lamy ∈ simplexSet m)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun i => (1 - t) * lamx i + t * lamy i) ∈ simplexSet m := by
  have hconv := convex_simplexSet (m := m)
  have h1 : 0 ≤ (1 - t) := by linarith
  have hsum : (1 - t) + t = (1 : Real) := by ring
  have hmem := hconv hx hy (a := 1 - t) (b := t) h1 ht0 hsum
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hmem

/-- Strict inequality for scaled values along convex combinations. -/
lemma mul_f_strict_lt_convex_combo {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    {x y : Fin n → Real} {lamx lamy : Real} {α β : Real} {t : Real}
    (hx : rightScalarMultiple f lamx x < (α : EReal))
    (hy : rightScalarMultiple f lamy y < (β : EReal))
    (ht0 : 0 < t) (ht1 : t < 1)
    (hlamx : 0 ≤ lamx) (hlamy : 0 ≤ lamy) :
    rightScalarMultiple f ((1 - t) * lamx + t * lamy) ((1 - t) • x + t • y) <
      ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
  classical
  let g : (Fin (n + 1) → Real) → EReal :=
    fun y =>
      if 0 ≤ y 0 then
        rightScalarMultiple f (y 0) (fun k => y k.succ)
      else
        (⊤ : EReal)
  have hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin (n + 1) → Real))) g := by
    have hpers :
        ProperConvexFunctionOn (S := (Set.univ : Set (Fin (n + 1) → Real))) g := by
      simpa [g] using (perspective_posHomogeneous_convex (f := f) (hf := hf)).1
    exact hpers.1
  have hstrict := (convexFunctionOn_univ_iff_strict_inequality (f := g)).1 hconv
  let x1 : Fin (n + 1) → Real := fun j => Fin.cases lamx (fun k : Fin n => x k) j
  let y1 : Fin (n + 1) → Real := fun j => Fin.cases lamy (fun k : Fin n => y k) j
  have hx1 : g x1 = rightScalarMultiple f lamx x := by
    simp [g, x1, hlamx]
  have hy1 : g y1 = rightScalarMultiple f lamy y := by
    simp [g, y1, hlamy]
  have hcomb :
      g ((1 - t) • x1 + t • y1) =
        rightScalarMultiple f ((1 - t) * lamx + t * lamy) ((1 - t) • x + t • y) := by
    have hz0 : 0 ≤ (1 - t) * lamx + t * lamy := by
      have h1 : 0 ≤ (1 - t) := by linarith [ht1]
      have h2 : 0 ≤ t := le_of_lt ht0
      exact add_nonneg (mul_nonneg h1 hlamx) (mul_nonneg h2 hlamy)
    have hsucc :
        (fun k : Fin n => ((1 - t) • x1 + t • y1) k.succ) = (1 - t) • x + t • y := by
      funext k
      simp [x1, y1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsucc' :
        (fun k : Fin n => (1 - t) * x1 k.succ + t * y1 k.succ) = (1 - t) • x + t • y := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hsucc
    calc
      g ((1 - t) • x1 + t • y1) =
          rightScalarMultiple f ((1 - t) * lamx + t * lamy)
            (fun k : Fin n => ((1 - t) • x1 + t • y1) k.succ) := by
          simp [g, hz0, x1, y1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      _ = rightScalarMultiple f ((1 - t) * lamx + t * lamy) ((1 - t) • x + t • y) := by
          simp [hsucc']
  have hxg : g x1 < (α : EReal) := by
    simpa [hx1] using hx
  have hyg : g y1 < (β : EReal) := by
    simpa [hy1] using hy
  have hres := hstrict x1 y1 α β t hxg hyg ht0 ht1
  simpa [hcomb] using hres

/-- Theorem 5.8.4: Let `f_1, ..., f_m` be proper convex functions on `ℝ^n`. Then the
function `k` defined by
`k(x) = inf { max { λ_1 f_1(x_1), ..., λ_m f_m(x_m) } }` is convex, with the infimum
taken over `λ_i ≥ 0`, `∑ λ_i = 1`, and `x_1 + ... + x_m = x`. -/
theorem convexFunctionOn_inf_iSup_weighted_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x =>
        sInf { z : EReal |
          ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
            (Finset.univ.sum (fun i => x' i) = x) ∧
            z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (x' i)) }) := by
  classical
  refine
    (convexFunctionOn_univ_iff_strict_inequality (f := fun x =>
        sInf { z : EReal |
          ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
            (Finset.univ.sum (fun i => x' i) = x) ∧
            z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (x' i)) })).2 ?_
  intro x y α β t hfx hfy ht0 ht1
  set Sx : Set EReal :=
    { z : EReal |
      ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
        (Finset.univ.sum (fun i => x' i) = x) ∧
        z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (x' i)) }
  set Sy : Set EReal :=
    { z : EReal |
      ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
        (Finset.univ.sum (fun i => x' i) = y) ∧
        z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (x' i)) }
  set Sxy : Set EReal :=
    { z : EReal |
      ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = (1 : Real)) ∧
        (Finset.univ.sum (fun i => x' i) = (1 - t) • x + t • y) ∧
        z = iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (x' i)) }
  have hneSx : Sx.Nonempty := by
    by_contra hne
    have hSx : Sx = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfx' := hfx
    simp [Sx, hSx, sInf_empty] at hfx'
  have hneSy : Sy.Nonempty := by
    by_contra hne
    have hSy : Sy = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfy' := hfy
    simp [Sy, hSy, sInf_empty] at hfy'
  rcases exists_lt_of_csInf_lt (s := Sx) hneSx (by simpa [Sx] using hfx) with
    ⟨z1, hz1Sx, hz1lt⟩
  rcases exists_lt_of_csInf_lt (s := Sy) hneSy (by simpa [Sy] using hfy) with
    ⟨z2, hz2Sy, hz2lt⟩
  rcases hz1Sx with ⟨lamx, x', hlamx_nonneg, hlamx_sum, hxsum, rfl⟩
  rcases hz2Sy with ⟨lamy, y', hlamy_nonneg, hlamy_sum, hysum, rfl⟩
  let lam : Fin m → Real := fun i => (1 - t) * lamx i + t * lamy i
  let w : Fin m → (Fin n → Real) := fun i => (1 - t) • x' i + t • y' i
  have ht0' : 0 ≤ t := le_of_lt ht0
  have ht1' : t ≤ 1 := le_of_lt ht1
  have hlam_mem : lam ∈ simplexSet m := by
    refine
      lam_combo_in_simplex (m := m) (lamx := lamx) (lamy := lamy) (t := t) ?_ ?_ ht0' ht1'
    · exact ⟨hlamx_nonneg, hlamx_sum⟩
    · exact ⟨hlamy_nonneg, hlamy_sum⟩
  rcases (by simpa [simplexSet] using hlam_mem) with ⟨hlam_nonneg, hlam_sum⟩
  have hsum_w :
      Finset.univ.sum (fun i => w i) = (1 - t) • x + t • y := by
    calc
      Finset.univ.sum (fun i => w i) =
          (1 - t) • Finset.univ.sum (fun i => x' i) +
            t • Finset.univ.sum (fun i => y' i) := by
              simpa [w] using (sum_components_convex_combo (x' := x') (y' := y') (t := t))
      _ = (1 - t) • x + t • y := by
            simp [hxsum, hysum]
  have hfi_lt :
      ∀ i,
        rightScalarMultiple (f i) (lam i) (w i) <
          ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    intro i
    have hx_i : rightScalarMultiple (f i) (lamx i) (x' i) < (α : EReal) := by
      have hle :
          rightScalarMultiple (f i) (lamx i) (x' i) ≤
            iSup (fun j : Fin m => rightScalarMultiple (f j) (lamx j) (x' j)) := by
        exact le_iSup (fun j : Fin m => rightScalarMultiple (f j) (lamx j) (x' j)) i
      exact lt_of_le_of_lt hle hz1lt
    have hy_i : rightScalarMultiple (f i) (lamy i) (y' i) < (β : EReal) := by
      have hle :
          rightScalarMultiple (f i) (lamy i) (y' i) ≤
            iSup (fun j : Fin m => rightScalarMultiple (f j) (lamy j) (y' j)) := by
        exact le_iSup (fun j : Fin m => rightScalarMultiple (f j) (lamy j) (y' j)) i
      exact lt_of_le_of_lt hle hz2lt
    have hmul :=
      mul_f_strict_lt_convex_combo (f := f i) (hf := hf i) (x := x' i) (y := y' i)
        (lamx := lamx i) (lamy := lamy i) (α := α) (β := β) (t := t)
        hx_i hy_i ht0 ht1 (hlamx_nonneg i) (hlamy_nonneg i)
    simpa [lam, w] using hmul
  have hsup_lt :
      iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (w i)) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    by_cases hm : m = 0
    · subst hm
      have hiSup :
          iSup (fun i : Fin 0 => rightScalarMultiple (f i) (lam i) (w i)) = (⊥ : EReal) := by
        simp
      have hbot' : (⊥ : EReal) < ((1 - t) * α + t * β : Real) := by
        simpa using (EReal.bot_lt_coe ((1 - t) * α + t * β))
      have hbot :
          (⊥ : EReal) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
        simpa [EReal.coe_add, EReal.coe_mul] using hbot'
      simpa [hiSup] using hbot
    · have hm' : 0 < m := Nat.pos_of_ne_zero hm
      exact iSup_lt_of_forall_lt_fin (m := m)
        (a := fun i => rightScalarMultiple (f i) (lam i) (w i))
        (r := ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal))
        hm' hfi_lt
  have hmem : iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (w i)) ∈ Sxy := by
    refine ⟨lam, w, hlam_nonneg, hlam_sum, hsum_w, rfl⟩
  have hle : sInf Sxy ≤ iSup (fun i : Fin m => rightScalarMultiple (f i) (lam i) (w i)) :=
    sInf_le hmem
  have hlt :
      sInf Sxy <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
    lt_of_le_of_lt hle hsup_lt
  simpa [Sxy] using hlt

end Section05
end Chap01
