import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_5
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap22.Proposition_22_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

open ERealFunction
open scoped BigOperators InnerProductSpace

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Theorem 22.18: the affine real branch `t ↦ t - c`, viewed in `EReal`, lies in
`Γ(ℝ)`. -/
private theorem realAffineMemGamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ Γ(ℝ) := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The affine branch satisfies Jensen's inequality by direct real arithmetic.
    intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
  · -- Continuity of the affine real branch upgrades to lower semicontinuity.
    simpa using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

/-- Helper for Theorem 22.18: every finite real affine branch in the ambient Hilbert space lies in
`Γ(H)`. -/
private theorem innerSubAddConst_mem_gamma (z u : H) (c : ℝ) :
    (fun x : H ↦ ((⟪x - z, u⟫_ℝ + c : ℝ) : EReal)) ∈ Γ(H) := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The affine branch satisfies Jensen's inequality by direct expansion.
    intro x y a ha0 ha1
    apply le_of_eq
    have hreal :
        ⟪a • x + (1 - a) • y - z, u⟫_ℝ + c =
          a * (⟪x - z, u⟫_ℝ + c) + (1 - a) * (⟪y - z, u⟫_ℝ + c) := by
      have hleft :
          ⟪a • x + (1 - a) • y - z, u⟫_ℝ + c =
            a * ⟪x, u⟫_ℝ + (1 - a) * ⟪y, u⟫_ℝ + ⟪-z, u⟫_ℝ + c := by
        rw [sub_eq_add_neg, inner_add_left, inner_add_left, real_inner_smul_left,
          real_inner_smul_left]
      have hright :
          a * (⟪x - z, u⟫_ℝ + c) + (1 - a) * (⟪y - z, u⟫_ℝ + c) =
            a * ⟪x, u⟫_ℝ + (1 - a) * ⟪y, u⟫_ℝ + ⟪-z, u⟫_ℝ + c := by
        have hx : ⟪x - z, u⟫_ℝ = ⟪x, u⟫_ℝ + ⟪-z, u⟫_ℝ := by
          rw [sub_eq_add_neg, inner_add_left]
        have hy : ⟪y - z, u⟫_ℝ = ⟪y, u⟫_ℝ + ⟪-z, u⟫_ℝ := by
          rw [sub_eq_add_neg, inner_add_left]
        rw [hx, hy]
        ring
      calc
        ⟪a • x + (1 - a) • y - z, u⟫_ℝ + c
            = a * ⟪x, u⟫_ℝ + (1 - a) * ⟪y, u⟫_ℝ + ⟪-z, u⟫_ℝ + c := hleft
        _ = a * (⟪x - z, u⟫_ℝ + c) + (1 - a) * (⟪y - z, u⟫_ℝ + c) := hright.symm
    rw [show (1 - a : EReal) = ((1 - a : ℝ) : EReal) by norm_num, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  · -- Continuity of the affine real branch upgrades to lower semicontinuity.
    have hcont : Continuous fun x : H ↦ ⟪x - z, u⟫_ℝ + c := by
      exact ((continuous_id.sub continuous_const).inner continuous_const).add continuous_const
    simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Theorem 22.18: the singleton graph operator supported at `0` is cyclically
monotone. -/
private theorem originSingletonIsCyclicallyMonotone
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [DecidableEq H] :
    SetValuedOperator.IsCyclicallyMonotone
      ((fun x : H ↦ if x = 0 then ({0} : Set H) else ∅) : SetValuedOperator H H) := by
  refine ⟨fun n hn ↦ ?_⟩
  refine ⟨hn, ?_⟩
  intro x u hu hxn
  -- Every active graph point is forced to be `(0, 0)`, so the whole cycle sum vanishes.
  have hx_zero : ∀ i, i < n → x i = 0 := by
    intro i hi
    have hui : u i ∈ (if x i = 0 then ({0} : Set H) else ∅) := hu i hi
    by_cases hxi : x i = 0
    · exact hxi
    · simp [hxi] at hui
  have hu_zero : ∀ i, i < n → u i = 0 := by
    intro i hi
    have hui : u i ∈ (if x i = 0 then ({0} : Set H) else ∅) := hu i hi
    have hxi : x i = 0 := hx_zero i hi
    simpa [hxi] using hui
  have hsum_zero :
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    by_cases hnext : i + 1 < n
    · simp [hx_zero i hi_lt, hx_zero (i + 1) hnext, hu_zero i hi_lt]
    · have hi_last : i + 1 = n := by
        omega
      simp [hx_zero i hi_lt, hu_zero i hi_lt, hi_last, hxn]
  simpa [hsum_zero]

/-- Helper for Theorem 22.18: a maximally cyclically monotone operator has a nonempty graph. -/
private theorem exists_graphPoint_of_isMaximallyCyclicallyMonotone
    {A : SetValuedOperator H H} (hA : A.IsMaximallyCyclicallyMonotone) :
    (gra A).Nonempty := by
  classical
  by_contra hgraph
  let B : SetValuedOperator H H := fun x ↦ if x = 0 then ({0} : Set H) else ∅
  have hAB : A ≤ B := by
    intro x u hu
    exact False.elim <| hgraph ⟨(x, u), hu⟩
  have hBcyc : B.IsCyclicallyMonotone := originSingletonIsCyclicallyMonotone H
  have hBA : B ≤ A := hA.2 hBcyc hAB
  have hzero_mem : (0 : H) ∈ B 0 := by
    simp [B]
  have hzeroA : (0 : H) ∈ A 0 := hBA 0 hzero_mem
  exact hgraph ⟨(0, 0), by simpa [SetValuedOperator.mem_graph] using hzeroA⟩

/-- Helper for Theorem 22.18: the Rockafellar branch attached to a base graph point and a finite
graph chain records the source affine defect sum. -/
private def rockafellarBranchReal {A : SetValuedOperator H H} (p0 : gra A) :
    List (gra A) → H → ℝ
  | [], y => ⟪y - p0.1.1, p0.1.2⟫_ℝ
  | q :: l, y => ⟪q.1.1 - p0.1.1, p0.1.2⟫_ℝ + rockafellarBranchReal q l y

/-- Helper for Theorem 22.18: the corresponding extended-real Rockafellar branch is the coercion
of the real branch. -/
private def rockafellarBranch {A : SetValuedOperator H H} (p0 : gra A) (l : List (gra A))
    (y : H) : EReal :=
  ((rockafellarBranchReal p0 l y : ℝ) : EReal)

/-- Helper for Theorem 22.18: the Rockafellar potential is the supremum of the finite graph
branches based at `p0`. -/
private def rockafellarPotentialRaw {A : SetValuedOperator H H} (p0 : gra A) : H → EReal :=
  fun x ↦ ⨆ l : List (gra A), rockafellarBranch p0 l x

/-- Helper for Theorem 22.18: the list-based path sum packages the same branch recursion on a
nonempty list of graph points. -/
private def rockafellarPathSum {A : SetValuedOperator H H} :
    List (gra A) → H → ℝ
  | [], _ => 0
  | [p], y => ⟪y - p.1.1, p.1.2⟫_ℝ
  | p :: q :: l, y => ⟪q.1.1 - p.1.1, p.1.2⟫_ℝ + rockafellarPathSum (q :: l) y

/-- Helper for Theorem 22.18: the recursive Rockafellar branch is exactly the path-sum expression
on the list `p0 :: l`. -/
private theorem rockafellarBranchReal_eq_pathSum {A : SetValuedOperator H H} (p0 : gra A)
    (l : List (gra A)) (y : H) :
    rockafellarBranchReal p0 l y = rockafellarPathSum (p0 :: l) y := by
  induction l generalizing p0 with
  | nil =>
      -- The empty chain is the one-point path ending at `y`.
      simp [rockafellarBranchReal, rockafellarPathSum]
  | cons q l ih =>
      -- Peel off the first graph point and apply the induction hypothesis to the tail.
      simp [rockafellarBranchReal, rockafellarPathSum, ih]

/-- Helper for Theorem 22.18: after peeling the first summand, the remaining nat-indexed tail on
`p :: q :: r :: l` is exactly the raw cyclic sum for the smaller chain `q :: r :: l`. -/
private theorem rockafellarPathTailShift_eq_rangeSum {A : SetValuedOperator H H}
    (p q r : gra A) (l : List (gra A)) (y : H) :
    let ptsBig : List (gra A) := p :: q :: r :: l
    let nBig : ℕ := ptsBig.length
    let xBig : ℕ → H := fun i ↦ if hi : i < nBig then (ptsBig.get ⟨i, hi⟩).1.1 else y
    let uBig : ℕ → H := fun i ↦ if hi : i < nBig then (ptsBig.get ⟨i, hi⟩).1.2 else p.1.2
    let ptsTail : List (gra A) := q :: r :: l
    let nTail : ℕ := ptsTail.length
    let xTail : ℕ → H := fun i ↦ if hi : i < nTail then (ptsTail.get ⟨i, hi⟩).1.1 else y
    let uTail : ℕ → H := fun i ↦ if hi : i < nTail then (ptsTail.get ⟨i, hi⟩).1.2 else q.1.2
    Finset.sum (Finset.range nTail) (fun i ↦ ⟪xBig (i + 2) - xBig (i + 1), uBig (i + 1)⟫_ℝ) =
      Finset.sum (Finset.range nTail) (fun i ↦ ⟪xTail (i + 1) - xTail i, uTail i⟫_ℝ) := by
  let ptsBig : List (gra A) := p :: q :: r :: l
  let nBig : ℕ := ptsBig.length
  let xBig : ℕ → H := fun i ↦ if hi : i < nBig then (ptsBig.get ⟨i, hi⟩).1.1 else y
  let uBig : ℕ → H := fun i ↦ if hi : i < nBig then (ptsBig.get ⟨i, hi⟩).1.2 else p.1.2
  let ptsTail : List (gra A) := q :: r :: l
  let nTail : ℕ := ptsTail.length
  let xTail : ℕ → H := fun i ↦ if hi : i < nTail then (ptsTail.get ⟨i, hi⟩).1.1 else y
  let uTail : ℕ → H := fun i ↦ if hi : i < nTail then (ptsTail.get ⟨i, hi⟩).1.2 else q.1.2
  -- Normalize the shifted tail termwise so the induction step can reuse the smaller-chain API.
  change
    Finset.sum (Finset.range nTail) (fun i ↦ ⟪xBig (i + 2) - xBig (i + 1), uBig (i + 1)⟫_ℝ) =
      Finset.sum (Finset.range nTail) (fun i ↦ ⟪xTail (i + 1) - xTail i, uTail i⟫_ℝ)
  have hlen : nBig = nTail + 1 := by
    simp [nBig, ptsBig, nTail, ptsTail]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < nTail := Finset.mem_range.mp hi
  have hi1_big : i + 1 < nBig := by
    rw [hlen]
    exact Nat.succ_lt_succ hi_lt
  by_cases htail : i + 1 < nTail
  · have hbig2 : i + 2 < nBig := by
      rw [hlen]
      exact Nat.succ_lt_succ htail
    -- When the tail index stays inside the smaller chain, both sides read the same graph points.
    simp [ptsBig, ptsTail, xBig, uBig, xTail, uTail, hbig2, hi1_big, htail, hi_lt]
  · have hbig2 : ¬ i + 2 < nBig := by
      rw [hlen]
      intro h
      exact htail (Nat.lt_of_succ_lt_succ h)
    -- At the terminal index, both sides fall back to the common endpoint `y`.
    simp [ptsBig, ptsTail, xBig, uBig, xTail, uTail, hbig2, hi1_big, htail, hi_lt]

/-- Helper for Theorem 22.18: a nontrivial nat-indexed path sum normalizes to the recursive
`rockafellarPathSum` expression. -/
private theorem rockafellarPathSum_cons_cons_eq_rangeSum {A : SetValuedOperator H H}
    (p q : gra A) :
    ∀ (l : List (gra A)) (y : H),
      let pts : List (gra A) := p :: q :: l
      let n : ℕ := pts.length
      let x : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.1 else y
      let u : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.2 else p.1.2
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) =
        rockafellarPathSum pts y := by
  intro l y
  induction l generalizing p q with
  | nil =>
      -- The two-point chain is exactly the head increment followed by the terminal affine term.
      dsimp
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [rockafellarPathSum, add_comm]
  | cons r l ih =>
      -- Route correction: peel the head term, rewrite the shifted tail once, and recurse on
      -- the smaller chain `q :: r :: l`.
      let pts : List (gra A) := p :: q :: r :: l
      let n : ℕ := pts.length
      let x : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.1 else y
      let u : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.2 else p.1.2
      change
        Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) =
          rockafellarPathSum pts y
      have hlen : n = List.length (q :: r :: l) + 1 := by
        simp [n, pts]
      rw [hlen, Finset.sum_range_succ']
      have htail :
          Finset.sum (Finset.range (List.length (q :: r :: l)))
              (fun i ↦ ⟪x (i + 2) - x (i + 1), u (i + 1)⟫_ℝ) =
            Finset.sum (Finset.range (List.length (q :: r :: l))) (fun i ↦
              ⟪(if hi : i + 1 < List.length (q :: r :: l) then
                  ((q :: r :: l).get ⟨i + 1, hi⟩).1.1 else y) -
                (if hi : i < List.length (q :: r :: l) then
                  ((q :: r :: l).get ⟨i, hi⟩).1.1 else y),
                if hi : i < List.length (q :: r :: l) then
                  ((q :: r :: l).get ⟨i, hi⟩).1.2 else q.1.2⟫_ℝ) := by
        -- Repackage the post-`sum_range_succ'` tail as the smaller-chain raw cyclic sum.
        simpa [pts, n, x, u] using rockafellarPathTailShift_eq_rangeSum p q r l y
      rw [htail, ih q r]
      simp [pts, n, x, u, rockafellarPathSum, add_left_comm, add_comm]

/-- Helper for Theorem 22.18: the closed cycle `p0 :: q :: l` has nat-indexed cyclic sum equal to
its `rockafellarPathSum` at the base point. -/
private theorem rockafellarPathSum_closedCycle_eq_rangeSum {A : SetValuedOperator H H}
    (p0 q : gra A) (l : List (gra A)) :
    let pts : List (gra A) := p0 :: q :: l
    let n : ℕ := pts.length
    let x : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.1 else p0.1.1
    let u : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.2 else p0.1.2
    Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) =
      rockafellarPathSum pts p0.1.1 := by
  -- Specialize the generic path-sum bridge to the closed cycle ending back at `p0`.
  simpa using rockafellarPathSum_cons_cons_eq_rangeSum p0 q l p0.1.1

/-- Helper for Theorem 22.18: appending one graph point exposes the final affine term of the
Rockafellar branch. -/
private theorem rockafellarBranchReal_append_eq {A : SetValuedOperator H H} (p0 : gra A)
    (l : List (gra A)) (q : gra A) (y : H) :
    rockafellarBranchReal p0 (l ++ [q]) y =
      rockafellarBranchReal p0 l q.1.1 + ⟪y - q.1.1, q.1.2⟫_ℝ := by
  induction l generalizing p0 with
  | nil =>
      -- The singleton branch is the base-point increment followed by the terminal affine term.
      simp [rockafellarBranchReal]
  | cons r l ih =>
      -- Push the append decomposition through the initial branch step.
      simp [rockafellarBranchReal, ih, add_assoc]

/-- Helper for Theorem 22.18: the extended-real append identity is the coercion of the real branch
formula. -/
private theorem rockafellarBranch_append_eq {A : SetValuedOperator H H} (p0 : gra A)
    (l : List (gra A)) (q : gra A) (y : H) :
    rockafellarBranch p0 (l ++ [q]) y =
      ((⟪y - q.1.1, q.1.2⟫_ℝ : ℝ) : EReal) + rockafellarBranch p0 l q.1.1 := by
  -- Coerce the real append identity to `EReal`.
  rw [rockafellarBranch, rockafellarBranch]
  rw [rockafellarBranchReal_append_eq]
  rw [EReal.coe_add, add_comm]

/-- Helper for Theorem 22.18: every Rockafellar branch is a finite real affine function, hence a
member of `Γ(H)`. -/
private theorem rockafellarBranchReal_eq_affine {A : SetValuedOperator H H} (p0 : gra A)
    (l : List (gra A)) :
    ∃ u : H, ∃ c : ℝ, ∀ y : H, rockafellarBranchReal p0 l y = ⟪y, u⟫_ℝ + c := by
  induction l generalizing p0 with
  | nil =>
      refine ⟨p0.1.2, -⟪p0.1.1, p0.1.2⟫_ℝ, ?_⟩
      intro y
      rw [rockafellarBranchReal, inner_sub_left]
      ring
  | cons q l ih =>
      rcases ih q with ⟨u, c, hc⟩
      refine ⟨u, ⟪q.1.1 - p0.1.1, p0.1.2⟫_ℝ + c, ?_⟩
      intro y
      rw [rockafellarBranchReal, hc]
      ring

/-- Helper for Theorem 22.18: every Rockafellar branch is a finite real affine function, hence a
member of `Γ(H)`. -/
private theorem rockafellarBranch_mem_gamma {A : SetValuedOperator H H} (p0 : gra A)
    (l : List (gra A)) :
    rockafellarBranch p0 l ∈ Γ(H) := by
  rcases rockafellarBranchReal_eq_affine p0 l with ⟨u, c, hc⟩
  -- Rewrite the branch into a canonical affine normal form before invoking the generic `Γ(H)`
  -- affine helper.
  have hbranch :
      rockafellarBranch p0 l = fun y : H ↦ ((⟪y - 0, u⟫_ℝ + c : ℝ) : EReal) := by
    funext y
    rw [rockafellarBranch, hc]
    simp
  rw [hbranch]
  exact innerSubAddConst_mem_gamma 0 u c

/-- Helper for Theorem 22.18: the Rockafellar potential belongs to `Γ(H)` as the supremum of its
affine graph branches. -/
private theorem rockafellarPotentialRaw_mem_gamma {A : SetValuedOperator H H} (p0 : gra A) :
    rockafellarPotentialRaw p0 ∈ Γ(H) := by
  -- Proposition 9.3 packages the pointwise supremum of the branch family.
  refine iSup_mem_gamma
    (fun l : List (gra A) ↦ rockafellarBranch p0 l)
    (fun l ↦ rockafellarBranch_mem_gamma p0 l)

/-- Helper for Theorem 22.18: the empty branch keeps the Rockafellar potential strictly above
`-∞`. -/
private theorem rockafellarPotentialRaw_ne_bot {A : SetValuedOperator H H} (p0 : gra A)
    (x : H) :
    (⊥ : EReal) < rockafellarPotentialRaw p0 x := by
  have hbranch :
      rockafellarBranch p0 [] x ≤ rockafellarPotentialRaw p0 x := by
    exact le_iSup (fun l : List (gra A) ↦ rockafellarBranch p0 l x) []
  have hbot : (⊥ : EReal) < rockafellarBranch p0 [] x := by
    simp [rockafellarBranch, rockafellarBranchReal]
  exact lt_of_lt_of_le hbot hbranch

/-- Helper for Theorem 22.18: the Rockafellar branch at the base point is the closed cyclic sum
of the corresponding finite graph chain. -/
private theorem rockafellarPathSum_closedCycle_le_zero {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 q : gra A) (l : List (gra A)) :
    rockafellarPathSum (p0 :: q :: l) p0.1.1 ≤ 0 := by
  let pts : List (gra A) := p0 :: q :: l
  let n : ℕ := pts.length
  let x : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.1 else p0.1.1
  let u : ℕ → H := fun i ↦ if hi : i < n then (pts.get ⟨i, hi⟩).1.2 else p0.1.2
  have htwo : 2 ≤ n := by
    -- The encoded cycle contains at least the base point and one extra graph point.
    simp [pts, n]
  have hu_mem : ∀ i, i < n → u i ∈ A (x i) := by
    -- Each indexed point of the encoded cycle comes directly from `gra A`.
    intro i hi
    simp only [u, x, hi, if_pos]
    change (pts.get ⟨i, hi⟩).1.2 ∈ A (pts.get ⟨i, hi⟩).1.1
    exact (pts.get ⟨i, hi⟩).2
  have hx_cycle : x n = x 0 := by
    -- The encoded cycle closes by sending the terminal index back to the base point.
    have hzero : 0 < n := by
      simp [pts, n]
    simp [x, n, pts, Nat.not_lt.mpr (le_rfl : n ≤ n), hzero]
  have hineq :
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) ≤ 0 :=
    (hA.isNCyclicallyMonotone htwo).ineq x u hu_mem hx_cycle
  -- Rewrite the raw cyclic sum into the local path-sum normal form before closing.
  rw [rockafellarPathSum_closedCycle_eq_rangeSum p0 q l] at hineq
  exact hineq

/-- Helper for Theorem 22.18: the Rockafellar branch at the base point is nonpositive by the
closed-cycle inequality. -/
private theorem rockafellarBranchReal_at_base_nonpos {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 : gra A) (l : List (gra A)) :
    rockafellarBranchReal p0 l p0.1.1 ≤ 0 := by
  cases l with
  | nil =>
      -- The empty cycle starts and ends at the base graph point, so its branch value is `0`.
      simp [rockafellarBranchReal]
  | cons q l =>
      -- Route correction: bridge through `rockafellarPathSum` instead of asking `simpa` to
      -- normalize the raw nat-indexed cyclic sum and the recursive branch simultaneously.
      calc
        rockafellarBranchReal p0 (q :: l) p0.1.1 = rockafellarPathSum (p0 :: q :: l) p0.1.1 := by
          rw [rockafellarBranchReal_eq_pathSum]
      _ ≤ 0 := rockafellarPathSum_closedCycle_le_zero hA p0 q l

/-- Helper for Theorem 22.18: the Rockafellar potential vanishes at the base graph point. -/
private theorem rockafellarPotentialRaw_base_eq_zero {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 : gra A) :
    rockafellarPotentialRaw p0 p0.1.1 = 0 := by
  -- The empty branch gives the lower bound `0 ≤ f(p0)`.
  have hlower : (0 : EReal) ≤ rockafellarPotentialRaw p0 p0.1.1 := by
    have hzero : rockafellarBranch p0 [] p0.1.1 = 0 := by
      simp [rockafellarBranch, rockafellarBranchReal]
    rw [← hzero]
    exact le_iSup (fun l : List (gra A) ↦ rockafellarBranch p0 l p0.1.1) []
  -- Cyclic monotonicity bounds every branch above by `0`.
  have hupper : rockafellarPotentialRaw p0 p0.1.1 ≤ 0 := by
    refine iSup_le fun l ↦ ?_
    simpa [rockafellarBranch] using rockafellarBranchReal_at_base_nonpos hA p0 l
  exact le_antisymm hupper hlower

/-- Helper for Theorem 22.18: the raw Rockafellar potential is proper because it is never `-∞`
and is finite at the base graph point. -/
private theorem rockafellarPotentialRaw_isProper {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 : gra A) :
    IsProper (rockafellarPotentialRaw p0) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact ne_of_gt (rockafellarPotentialRaw_ne_bot p0 x)
  · refine ⟨p0.1.1, ?_⟩
    rw [mem_dom_iff_ne_top]
    rw [rockafellarPotentialRaw_base_eq_zero hA p0]
    simp

/-- Helper for Theorem 22.18: the packaged Rockafellar potential belongs to `Γ₀(H)`. -/
private def rockafellarPotential {A : SetValuedOperator H H} (hA : A.IsCyclicallyMonotone)
    (p0 : gra A) : H → Set.Ioi (⊥ : EReal) :=
  properIoi (rockafellarPotentialRaw p0) (rockafellarPotentialRaw_isProper hA p0)

/-- Helper for Theorem 22.18: coercing the packaged Rockafellar potential recovers the raw
supremum. -/
private theorem rockafellarPotential_apply {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 : gra A) (x : H) :
    ((rockafellarPotential hA p0 x : Set.Ioi (⊥ : EReal)) : EReal) =
      rockafellarPotentialRaw p0 x := by
  simp [rockafellarPotential]

/-- Helper for Theorem 22.18: the packaged Rockafellar potential is the `Γ₀(H)` representative
attached to the raw branch supremum. -/
private theorem rockafellarPotential_mem_gammaZero {A : SetValuedOperator H H}
    (hA : A.IsCyclicallyMonotone) (p0 : gra A) :
    rockafellarPotential hA p0 ∈ Γ₀(H) := by
  -- Repackage the proper `Γ(H)` branch supremum through `properIoi`.
  simpa [rockafellarPotential] using
    properIoi_mem_gammaZero_of_mem_gamma
      (rockafellarPotentialRaw_isProper hA p0)
      (rockafellarPotentialRaw_mem_gamma p0)

/-- Helper for Theorem 22.18: every graph point of `A` becomes a subgradient of the Rockafellar
potential. -/
private theorem mem_subdifferential_rockafellarPotential_of_mem_graph
    {A : SetValuedOperator H H} (hA : A.IsCyclicallyMonotone) (p0 : gra A)
    {x u : H} (hxu : (x, u) ∈ gra A) :
    u ∈ (∂ (rockafellarPotential hA p0)) x := by
  let q : gra A := ⟨(x, u), hxu⟩
  rw [mem_subdifferential_iff]
  intro y
  -- Route correction: use the append-branch identity and commute the finite real shift through
  -- the branch supremum.
  have hshift :
      ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + rockafellarPotentialRaw p0 x ≤
        rockafellarPotentialRaw p0 y := by
    calc
      ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + rockafellarPotentialRaw p0 x
          = ((⨆ l : List (gra A), rockafellarBranch p0 l x) +
              ((⟪y - x, u⟫_ℝ : ℝ) : EReal)) := by
                simp [rockafellarPotentialRaw, add_comm]
      _ = ⨆ l : List (gra A), rockafellarBranch p0 l x + ((⟪y - x, u⟫_ℝ : ℝ) : EReal) := by
            rw [ereal_iSup_add_of_real_shift]
      _ = ⨆ l : List (gra A), rockafellarBranch p0 (l ++ [q]) y := by
            refine iSup_congr ?_
            intro l
            rw [rockafellarBranch_append_eq, add_comm]
      _ ≤ rockafellarPotentialRaw p0 y := by
            refine iSup_le fun l ↦ ?_
            exact le_iSup (fun l' : List (gra A) ↦ rockafellarBranch p0 l' y) (l ++ [q])
  simpa [rockafellarPotential_apply, add_comm] using hshift

/- Source/core/bridge triage:
- `source-facing`: Theorem 22.18 is Rockafellar's representation theorem for maximally cyclically
  monotone set-valued operators.
- `core/canonical`: the owner objects already live upstream as the Chapter 16 subdifferential `∂`,
  the Chapter 9/16 class `Γ₀(H)`, the Chapter 20 maximal-monotonicity theorem
  `subdifferential_isMaximallyMonotone_of_mem_gammaZero`, and the Chapter 22 owner
  `IsMaximallyCyclicallyMonotone`.
- `bridge/view`: this file is the Chapter 22 bridge identifying the source-facing maximal cyclic
  monotonicity predicate with the canonical subdifferential representation.

Primitive data: a set-valued operator `A : H → 2^H`.
Derived API: existence of a canonical `Γ₀(H)` potential whose subdifferential is `A`. -/
/-- Theorem 22.18 (Rockafellar): a set-valued operator `A : H → 2^H` on a real Hilbert space is
maximally cyclically monotone if and only if there exists `f ∈ Γ₀(H)` such that `A = ∂ f`. -/
theorem isMaximallyCyclicallyMonotone_iff_eq_subdifferential
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : SetValuedOperator H H) :
    A.IsMaximallyCyclicallyMonotone ↔
      ∃ f : H → Set.Ioi (⊥ : EReal), f ∈ Γ₀(H) ∧ A = ∂ f := by
  constructor
  · intro hA
    -- Route correction: switch to the local Rockafellar potential built from a base graph point.
    obtain ⟨p0, hp0⟩ := exists_graphPoint_of_isMaximallyCyclicallyMonotone hA
    let q0 : gra A := ⟨p0, hp0⟩
    let f := rockafellarPotential hA.1 q0
    have hf : f ∈ Γ₀(H) := rockafellarPotential_mem_gammaZero hA.1 q0
    have hsub : A ≤ ∂ f := by
      intro x u hu
      exact mem_subdifferential_rockafellarPotential_of_mem_graph hA.1 q0 hu
    have hcycSub : (∂ f).IsCyclicallyMonotone := by
      exact subdifferential_isCyclicallyMonotone (isProper_of_mem_gammaZero hf)
    have hsup : ∂ f ≤ A := hA.2 hcycSub hsub
    refine ⟨f, hf, le_antisymm hsub hsup⟩
  · rintro ⟨f, hf, rfl⟩
    -- The reverse implication is the direct combination of maximal monotonicity and cyclic
    -- monotonicity of subdifferentials of `Γ₀(H)` functions.
    exact isMaximallyCyclicallyMonotone_of_isMaximalMonotone
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
      (subdifferential_isCyclicallyMonotone (isProper_of_mem_gammaZero hf))

end
end SetValuedOperator
