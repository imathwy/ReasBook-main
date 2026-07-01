/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part6

section Chap03
section Section12

/-- Text 12.3.1: Let `f` be an `n`-dimensional partial affine function on `ℝ^N` with `0 < n < N`
and `m = N - n`, given (after a partition of coordinates `x = (ξ₁, …, ξ_N)`) by a Tucker-type
representation:

`f(x) = (∑_{j=1}^n α₀ⱼ ξⱼ - α₀₀)` if `ξ_{n+i} = ∑_{j=1}^n αᵢⱼ ξⱼ - αᵢ₀` for `i = 1, …, m`,
and `f(x) = +∞` otherwise.

Then the conjugate `f*` is:

`f*(x*) = (∑_{i=1}^m β₀ᵢ ξ*_{n+i} - β₀₀)` if `ξ*ⱼ = ∑_{i=1}^m βⱼᵢ ξ*_{n+i} - βⱼ₀`
for `j = 1, …, n`, and `f*(x*) = +∞` otherwise, where `βⱼᵢ = -αᵢⱼ` for all
`i ∈ {0, …, m}`, `j ∈ {0, …, n}`. -/
theorem fenchelConjugate_partialAffine_tucker (n m : Nat) (hn : 0 < n) (hm : 0 < m) (α00 : Real)
    (α0 : Fin n → Real) (αi0 : Fin m → Real) (α : Fin m → Fin n → Real) :
    let f : (Fin (n + m) → Real) → EReal :=
      fun x =>
        if _ :
            (∀ i : Fin m,
              x (Fin.natAdd n i) =
                (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
          ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
        else
          ⊤
    let fStar : (Fin (n + m) → Real) → EReal :=
      fun xStar =>
        if _ :
            (∀ j : Fin n,
              xStar (Fin.castAdd m j) =
                (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j) then
          ((∑ i : Fin m, (-αi0 i) * xStar (Fin.natAdd n i) + α00 : Real) : EReal)
        else
          ⊤
    fenchelConjugate (n + m) f = fStar := by
  classical
  have _hn' : n ≠ 0 := Nat.ne_of_gt hn
  have _hm' : m ≠ 0 := Nat.ne_of_gt hm
  dsimp
  ext xStar
  -- Abbreviate the coefficient vector and constant term appearing in the reduced range expression.
  let coeff : Fin n → Real :=
    fun j =>
      xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j
  let const : Real := α00 - (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i))
  have hconst :
      (∑ i : Fin m, (-αi0 i) * xStar (Fin.natAdd n i) + α00 : Real) = const := by
    simp [const, sub_eq_add_neg, add_comm]
  unfold fenchelConjugate
  by_cases hxStar :
      (∀ j : Fin n,
        xStar (Fin.castAdd m j) =
          (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j)
  · -- Dual-feasible: the supremum is the constant value.
    rw [if_pos hxStar]
    have hRHS :
        (((∑ i : Fin m, (-αi0 i) * xStar (Fin.natAdd n i) : Real) : EReal) + (α00 : EReal)) =
          (const : EReal) := by
      -- Rewrite the `EReal` sum as a coercion of a real sum, then use `hconst`.
      calc
        (((∑ i : Fin m, (-αi0 i) * xStar (Fin.natAdd n i) : Real) : EReal) + (α00 : EReal)) =
            ((∑ i : Fin m, (-αi0 i) * xStar (Fin.natAdd n i) + α00 : Real) : EReal) := by
          simp
        _ = (const : EReal) := by
          simpa using congrArg (fun r : Real => (r : EReal)) hconst
    -- Rewrite the right-hand side into the `const` form.
    rw [hRHS]
    have hcoeff0 : ∀ j : Fin n, coeff j = 0 := by
      have hiff :=
        tucker_dualConstraint_iff_coeff_eq_zero (n := n) (m := m) (α0 := α0) (α := α)
          (xStar := xStar)
      simpa [coeff] using (hiff.1 hxStar)
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro y ⟨x, rfl⟩
      have hsimp :=
        range_term_partialAffine_tucker_simp (n := n) (m := m) (α00 := α00) (α0 := α0)
          (αi0 := αi0) (α := α) (x := x) (xStar := xStar)
      by_cases hx :
          (∀ i : Fin m,
            x (Fin.natAdd n i) =
              (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i)
      · -- Feasible points: the range term collapses to the constant.
        have hreal :=
          range_term_partialAffine_tucker_real_formula (n := n) (m := m) (α00 := α00) (α0 := α0)
            (αi0 := αi0) (α := α) (x := x) (xStar := xStar) hx
        have hcollapse :
            x ⬝ᵥ xStar - (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) = const := by
          simpa [coeff, const, hcoeff0] using hreal
        -- Use the simplification lemma to reduce the `EReal` range term.
        have :
            (((x ⬝ᵥ xStar : Real) : EReal) -
                (if h :
                    (∀ i : Fin m,
                      x (Fin.natAdd n i) =
                        (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                  ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                else
                  ⊤)) =
              (const : EReal) := by
          -- The `if`-guard is `hx`, and we use `hcollapse` to evaluate the real expression.
          simpa [hx, hcollapse] using hsimp
        exact le_of_eq this
      · -- Infeasible points contribute `⊥`.
        simp [hx]
    · -- Lower bound: pick an explicit feasible point (head = 0, tail determined by the constraints).
      let xHead0 : Fin n → Real := fun _ => 0
      let xTail0 : Fin m → Real := fun i => (∑ j : Fin n, α i j * xHead0 j) - αi0 i
      let x0 : Fin (n + m) → Real := Fin.addCases xHead0 xTail0
      have hx0 :
          (∀ i : Fin m,
            x0 (Fin.natAdd n i) =
              (∑ j : Fin n, α i j * x0 (Fin.castAdd m j)) - αi0 i) := by
        intro i
        simp [x0, xTail0, xHead0]
      have hreal0 :=
        range_term_partialAffine_tucker_real_formula (n := n) (m := m) (α00 := α00) (α0 := α0)
          (αi0 := αi0) (α := α) (x := x0) (xStar := xStar) hx0
      have hcollapse0 :
          x0 ⬝ᵥ xStar - (∑ j : Fin n, α0 j * x0 (Fin.castAdd m j) - α00) = const := by
        simpa [coeff, const, hcoeff0, x0, xHead0] using hreal0
      have hsimp0 :=
        range_term_partialAffine_tucker_simp (n := n) (m := m) (α00 := α00) (α0 := α0)
          (αi0 := αi0) (α := α) (x := x0) (xStar := xStar)
      have hx0term :
          (((x0 ⬝ᵥ xStar : Real) : EReal) -
                (if h :
                    (∀ i : Fin m,
                      x0 (Fin.natAdd n i) =
                        (∑ j : Fin n, α i j * x0 (Fin.castAdd m j)) - αi0 i) then
                  ((∑ j : Fin n, α0 j * x0 (Fin.castAdd m j) - α00 : Real) : EReal)
                else
                  ⊤)) =
              (const : EReal) := by
        simpa [hx0, hcollapse0] using hsimp0
      -- Evaluate the supremum at `x0`.
      have hx0_le_sSup :
          (((x0 ⬝ᵥ xStar : Real) : EReal) -
                (if h :
                    (∀ i : Fin m,
                      x0 (Fin.natAdd n i) =
                        (∑ j : Fin n, α i j * x0 (Fin.castAdd m j)) - αi0 i) then
                  ((∑ j : Fin n, α0 j * x0 (Fin.castAdd m j) - α00 : Real) : EReal)
                else
                  ⊤)) ≤
            sSup (Set.range fun x : Fin (n + m) → Real =>
              (((x ⬝ᵥ xStar : Real) : EReal) -
                (if h :
                    (∀ i : Fin m,
                      x (Fin.natAdd n i) =
                        (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                  ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                else
                  ⊤))) := by
        exact le_sSup ⟨x0, rfl⟩
      have hle : (const : EReal) ≤
          sSup (Set.range fun x : Fin (n + m) → Real =>
            (((x ⬝ᵥ xStar : Real) : EReal) -
              (if h :
                  (∀ i : Fin m,
                    x (Fin.natAdd n i) =
                      (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
              else
                ⊤))) := by
        -- Rewrite the witness value using `hx0term`.
        calc
          (const : EReal) =
              (((x0 ⬝ᵥ xStar : Real) : EReal) -
                  (if h :
                      (∀ i : Fin m,
                        x0 (Fin.natAdd n i) =
                          (∑ j : Fin n, α i j * x0 (Fin.castAdd m j)) - αi0 i) then
                    ((∑ j : Fin n, α0 j * x0 (Fin.castAdd m j) - α00 : Real) : EReal)
                  else
                    ⊤)) := by
                simpa using hx0term.symm
          _ ≤
              sSup (Set.range fun x : Fin (n + m) → Real =>
                (((x ⬝ᵥ xStar : Real) : EReal) -
                  (if h :
                      (∀ i : Fin m,
                        x (Fin.natAdd n i) =
                          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                    ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                  else
                    ⊤))) := hx0_le_sSup
      exact hle
  · -- Dual-infeasible: the supremum is `⊤`.
    rw [if_neg hxStar]
    -- Show `sSup ... = ⊤` by comparing all real upper bounds.
    refine EReal.eq_of_forall_le_coe_iff (a := _) (b := (⊤ : EReal)) (fun μ => ?_)
    constructor
    · intro hle
      -- Derive a contradiction by building a feasible `x` with range term at least `μ + 1`.
      have hiff :=
        tucker_dualConstraint_iff_coeff_eq_zero (n := n) (m := m) (α0 := α0) (α := α)
          (xStar := xStar)
      have hnot_all : ¬ (∀ j : Fin n, coeff j = 0) := by
        intro h0
        have : (∀ j : Fin n,
            xStar (Fin.castAdd m j) =
              (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j) := by
          simpa [coeff] using (hiff.2 h0)
        exact hxStar this
      have hcoeff_exists : ∃ j : Fin n, coeff j ≠ 0 := by
        simpa [not_forall] using hnot_all
      rcases
          exists_head_makes_linear_combo_arbitrarily_large (coeff := coeff) (const := const)
            hcoeff_exists (μ + 1) with
        ⟨xHead, hμ⟩
      -- Build a feasible `x` from `xHead`.
      let xFeasTail : Fin m → Real :=
        fun i => (∑ j : Fin n, α i j * xHead j) - αi0 i
      let xFeas : Fin (n + m) → Real := Fin.addCases xHead xFeasTail
      have hxFeas :
          (∀ i : Fin m,
            xFeas (Fin.natAdd n i) =
              (∑ j : Fin n, α i j * xFeas (Fin.castAdd m j)) - αi0 i) := by
        intro i
        simp [xFeas, xFeasTail]
      have hsimp :=
        range_term_partialAffine_tucker_simp (n := n) (m := m) (α00 := α00) (α0 := α0)
          (αi0 := αi0) (α := α) (x := xFeas) (xStar := xStar)
      have hreal :=
        range_term_partialAffine_tucker_real_formula (n := n) (m := m) (α00 := α00) (α0 := α0)
          (αi0 := αi0) (α := α) (x := xFeas) (xStar := xStar) hxFeas
      have hcollapse :
          xFeas ⬝ᵥ xStar - (∑ j : Fin n, α0 j * xFeas (Fin.castAdd m j) - α00) =
            (∑ j : Fin n, xHead j * coeff j) + const := by
        -- Identify the head coordinates of `xFeas` with `xHead`.
        simpa [xFeas] using hreal
      have hrange :
          (((xFeas ⬝ᵥ xStar : Real) : EReal) -
                (if h :
                    (∀ i : Fin m,
                      xFeas (Fin.natAdd n i) =
                        (∑ j : Fin n, α i j * xFeas (Fin.castAdd m j)) - αi0 i) then
                  ((∑ j : Fin n, α0 j * xFeas (Fin.castAdd m j) - α00 : Real) : EReal)
                else
                  ⊤)) =
            (((∑ j : Fin n, xHead j * coeff j) + const : Real) : EReal) := by
        -- Reduce to the real expression using feasibility.
        simpa [hxFeas, hcollapse] using hsimp
      have hμE :
          ((μ + 1 : Real) : EReal) ≤
            (((∑ j : Fin n, xHead j * coeff j) + const : Real) : EReal) := by
        exact_mod_cast hμ
      have hx_le_sSup :
          (((∑ j : Fin n, xHead j * coeff j) + const : Real) : EReal) ≤
            sSup
              (Set.range fun x : Fin (n + m) → Real =>
                (((x ⬝ᵥ xStar : Real) : EReal) -
                  (if h :
                      (∀ i : Fin m,
                        x (Fin.natAdd n i) =
                          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                    ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                    else
                      ⊤))) := by
        -- `xFeas` provides a witness in the range.
        have hxFeas_le :
            (((xFeas ⬝ᵥ xStar : Real) : EReal) -
                  (if h :
                      (∀ i : Fin m,
                        xFeas (Fin.natAdd n i) =
                          (∑ j : Fin n, α i j * xFeas (Fin.castAdd m j)) - αi0 i) then
                    ((∑ j : Fin n, α0 j * xFeas (Fin.castAdd m j) - α00 : Real) : EReal)
                  else
                    ⊤)) ≤
              sSup
                (Set.range fun x : Fin (n + m) → Real =>
                  (((x ⬝ᵥ xStar : Real) : EReal) -
                    (if h :
                        (∀ i : Fin m,
                          x (Fin.natAdd n i) =
                            (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                      ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                    else
                      ⊤))) := by
          exact le_sSup ⟨xFeas, rfl⟩
        -- Rewrite the left-hand side using `hrange`.
        calc
          (((∑ j : Fin n, xHead j * coeff j) + const : Real) : EReal) =
              (((xFeas ⬝ᵥ xStar : Real) : EReal) -
                  (if h :
                      (∀ i : Fin m,
                        xFeas (Fin.natAdd n i) =
                          (∑ j : Fin n, α i j * xFeas (Fin.castAdd m j)) - αi0 i) then
                    ((∑ j : Fin n, α0 j * xFeas (Fin.castAdd m j) - α00 : Real) : EReal)
                  else
                    ⊤)) := by
                simpa using hrange.symm
          _ ≤
              sSup
                (Set.range fun x : Fin (n + m) → Real =>
                  (((x ⬝ᵥ xStar : Real) : EReal) -
                    (if h :
                        (∀ i : Fin m,
                          x (Fin.natAdd n i) =
                            (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
                      ((∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00 : Real) : EReal)
                    else
                      ⊤))) := hxFeas_le
      have hcontra :
          ((μ + 1 : Real) : EReal) ≤ (μ : EReal) :=
        le_trans hμE (le_trans hx_le_sSup hle)
      have : (μ + 1 : Real) ≤ μ := (EReal.coe_le_coe_iff).1 hcontra
      have : False := by linarith
      exact False.elim this
    · intro htop
      simp at htop

/-- The quadratic extended-real function associated to a linear map `Q` on `ℝ^n`,
`x ↦ (1/2) * ⟪x, Q x⟫`. Here the inner product is written as the dot product `⬝ᵥ` on
coordinates `x : Fin n → ℝ`. -/
noncomputable def quadraticHalfLinear (n : Nat)
    (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) : (Fin n → Real) → EReal :=
  fun x => (((1 / 2 : Real) * (x ⬝ᵥ Q x) : Real) : EReal)

/-- A function `f` on `ℝ^n` is *symmetric with respect to a set `G` of orthogonal linear
transformations* if it is invariant under every element of `G`, i.e. `f (g x) = f x` for all
`g ∈ G` and all `x`. -/
def IsSymmetricWrtOrthogonalSet {α : Type*} (n : Nat)
    (G : Set ((Fin n → Real) ≃ₗᵢ[ℝ] (Fin n → Real)))
    (f : (Fin n → Real) → α) : Prop :=
  ∀ g ∈ G, ∀ x : Fin n → Real, f (g x) = f x

/-- If `g` preserves dot products, then `g.symm` is the adjoint of `g` for the dot product. -/
lemma dotProduct_orthogonal_symm_apply {n : Nat}
    (g : (Fin n → Real) ≃ₗᵢ[ℝ] (Fin n → Real))
    (hg : ∀ x y : Fin n → Real, (g x) ⬝ᵥ (g y) = x ⬝ᵥ y) :
    ∀ x y : Fin n → Real, (g x) ⬝ᵥ y = x ⬝ᵥ (g.symm y) := by
  intro x y
  simpa using (hg x (g.symm y))

/-- The Fenchel conjugate commutes with precomposition by an "orthogonal" map (for the dot
product), with the inverse appearing on the dual side. -/
lemma fenchelConjugate_precomp_orthogonal (n : Nat) (f : (Fin n → Real) → EReal)
    (g : (Fin n → Real) ≃ₗᵢ[ℝ] (Fin n → Real))
    (hAStar : ∀ x y : Fin n → Real, (g x) ⬝ᵥ y = x ⬝ᵥ (g.symm y)) :
    fenchelConjugate n (fun x => f (g x)) = fun xStar => fenchelConjugate n f (g xStar) := by
  classical
  -- Theorem 12.3 with `h = f`, `a = 0`, `aStar = 0`, `α = 0`, and `AStar = g.symm`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (fenchelConjugate_affineTransform (n := n) (h := f) (A := g.toLinearEquiv)
      (AStar := g.symm.toLinearEquiv) (hAStar := hAStar) (a := 0) (aStar := 0) (α := 0))

/-- A lower semicontinuous convex function that never takes the value `-∞` equals its Fenchel
biconjugate. -/
lemma fenchelConjugate_biconjugate_eq_of_closedConvex (n : Nat) (f : (Fin n → Real) → EReal)
    (hf_closed : LowerSemicontinuous f) (hf_convex : ConvexFunction f)
    (hf_ne_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal)) :
    fenchelConjugate n (fenchelConjugate n f) = f := by
  classical
  by_cases hall_top : ∀ x : Fin n → Real, f x = (⊤ : EReal)
  · have hf : f = constPosInf n := by
      funext x
      simp [constPosInf, hall_top x]
    simp [hf, fenchelConjugate_constPosInf, fenchelConjugate_constNegInf]
  · have hx : ∃ x : Fin n → Real, f x ≠ (⊤ : EReal) := by
      simpa [not_forall] using hall_top
    rcases hx with ⟨x0, hx0⟩
    have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hf_ne_bot x0
    have hcoe : ((f x0).toReal : EReal) = f x0 :=
      EReal.coe_toReal (x := f x0) hx0 hx0_ne_bot
    have hne_epi :
        Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      refine ⟨(x0, (f x0).toReal), ?_⟩
      refine ⟨by trivial, ?_⟩
      -- `f x0` is a real value, hence below its `toReal` coercion.
      simp [hcoe]
    have hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      refine ⟨?_, hne_epi, ?_⟩
      · simpa [ConvexFunction] using hf_convex
      · intro x hx
        simpa using hf_ne_bot x
    have hbiconj : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
      fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
    have hcl : clConv n f = f :=
      clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf_closed)
        (hf_proper := hf_proper)
    simp [hbiconj, hcl]

/-- If `f` is invariant under a set `G` of dot-product-orthogonal maps, then its Fenchel conjugate
is invariant under `G`. -/
lemma isSymmetricWrtOrthogonalSet_fenchelConjugate_of_isSymmetricWrtOrthogonalSet (n : Nat)
    (G : Set ((Fin n → Real) ≃ₗᵢ[ℝ] (Fin n → Real))) (f : (Fin n → Real) → EReal)
    (hG :
      ∀ g ∈ G, ∀ x y : Fin n → Real, (g x) ⬝ᵥ (g y) = x ⬝ᵥ y) :
    IsSymmetricWrtOrthogonalSet n G f →
      IsSymmetricWrtOrthogonalSet n G (fenchelConjugate n f) := by
  intro hfG g hg xStar
  have hAStar :
      ∀ x y : Fin n → Real, (g x) ⬝ᵥ y = x ⬝ᵥ (g.symm y) :=
    dotProduct_orthogonal_symm_apply (g := g) (hg := hG g hg)
  have hconj :=
    fenchelConjugate_precomp_orthogonal (n := n) (f := f) (g := g) (hAStar := hAStar)
  have hpre : (fun x : Fin n → Real => f (g x)) = f := by
    funext x
    exact hfG g hg x
  have hconj_apply := congrArg (fun F => F xStar) hconj
  -- Rewrite `(f ∘ g)^*` using Theorem 12.3 and then use `f ∘ g = f`.
  simpa [hpre] using hconj_apply.symm

/-- Corollary 12.3.1. A closed convex function `f` is symmetric with respect to a given set `G`
of orthogonal linear transformations if and only if `f*` is symmetric with respect to `G`. -/
theorem isSymmetricWrtOrthogonalSet_iff_isSymmetricWrtOrthogonalSet_fenchelConjugate (n : Nat)
    (G : Set ((Fin n → Real) ≃ₗᵢ[ℝ] (Fin n → Real)))
    (f : (Fin n → Real) → EReal)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : ConvexFunction f)
    (hf_ne_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal))
    (hG :
      ∀ g ∈ G, ∀ x y : Fin n → Real, (g x) ⬝ᵥ (g y) = x ⬝ᵥ y) :
    IsSymmetricWrtOrthogonalSet n G f ↔
      IsSymmetricWrtOrthogonalSet n G (fenchelConjugate n f) := by
  constructor
  · intro hfG
    exact
      isSymmetricWrtOrthogonalSet_fenchelConjugate_of_isSymmetricWrtOrthogonalSet (n := n) (G := G)
        (f := f) (hG := hG) hfG
  · intro hfStarG
    have hfBiG :
        IsSymmetricWrtOrthogonalSet n G (fenchelConjugate n (fenchelConjugate n f)) :=
      isSymmetricWrtOrthogonalSet_fenchelConjugate_of_isSymmetricWrtOrthogonalSet (n := n) (G := G)
        (f := fenchelConjugate n f) (hG := hG) hfStarG
    have hbiconj :
        fenchelConjugate n (fenchelConjugate n f) = f :=
      fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f) (hf_closed := hf_closed)
        (hf_convex := hf_convex) (hf_ne_bot := hf_ne_bot)
    simpa [hbiconj] using hfBiG

/-- If `P_L` acts as the identity on `L` and `Q ∘ Q' = P_L`, then `Q (Q' xStar) = xStar` on `L`. -/
lemma Q_Q'_apply_eq_of_mem_L {n : Nat}
    (Q Q' P_L : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) (L : Submodule ℝ (Fin n → Real))
    (hQQ' : Q.comp Q' = P_L) (hP_L_id : ∀ xStar : Fin n → Real, xStar ∈ L → P_L xStar = xStar)
    {xStar : Fin n → Real} (hxStar : xStar ∈ L) : Q (Q' xStar) = xStar := by
  have hcomp : Q (Q' xStar) = P_L xStar := by
    simpa [LinearMap.comp_apply] using congrArg (fun T => T xStar) hQQ'
  simpa [hP_L_id xStar hxStar] using hcomp

/-- Completed-square inequality for the range term of the quadratic function
`x ↦ (1/2) * (x ⬝ᵥ Q x)` when `xStar ∈ L = range(Q)`. -/
lemma range_term_quadraticHalfLinear_le_on_L {n : Nat}
    (Q Q' P_L : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) (L : Submodule ℝ (Fin n → Real))
    (hQQ' : Q.comp Q' = P_L) (hP_L_id : ∀ xStar : Fin n → Real, xStar ∈ L → P_L xStar = xStar)
    (hQsymm : ∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y)
    (hQpsd : ∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Q x) {xStar : Fin n → Real} (hxStar : xStar ∈ L) :
    ∀ x : Fin n → Real,
      ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q x ≤ quadraticHalfLinear n Q' xStar := by
  classical
  intro x
  set q : Fin n → Real := Q' xStar
  have hQq : Q q = xStar := by
    simpa [q] using
      Q_Q'_apply_eq_of_mem_L (Q := Q) (Q' := Q') (P_L := P_L) (L := L) hQQ' hP_L_id hxStar
  have hpsd : 0 ≤ (x - q) ⬝ᵥ Q (x - q) := hQpsd (x - q)
  have hqx : (q ⬝ᵥ Q x : Real) = (x ⬝ᵥ Q q : Real) := by
    calc
      (q ⬝ᵥ Q x : Real) = (Q x ⬝ᵥ q : Real) := by simp [dotProduct_comm]
      _ = (x ⬝ᵥ Q q : Real) := by simpa using (hQsymm x q)
  have hEq :
      (x - q) ⬝ᵥ Q (x - q) =
        (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ xStar : Real) + (xStar ⬝ᵥ q : Real) := by
    calc
      (x - q) ⬝ᵥ Q (x - q) =
          (x ⬝ᵥ Q x : Real) - (x ⬝ᵥ Q q : Real) - (q ⬝ᵥ Q x : Real) + (q ⬝ᵥ Q q : Real) := by
            simp [sub_eq_add_neg, add_dotProduct, dotProduct_add, map_add, map_neg, add_assoc,
              add_comm, add_left_comm]
      _ = (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ Q q : Real) + (q ⬝ᵥ Q q : Real) := by
            nlinarith [hqx]
      _ = (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ xStar : Real) + (xStar ⬝ᵥ q : Real) := by
            simp [hQq, dotProduct_comm]
  have hreal :
      (x ⬝ᵥ xStar : Real) - (1 / 2 : Real) * (x ⬝ᵥ Q x) ≤ (1 / 2 : Real) * (xStar ⬝ᵥ q) := by
    have h0 : 0 ≤ (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ xStar : Real) + (xStar ⬝ᵥ q : Real) := by
      have h0' := hpsd
      rw [hEq] at h0'
      exact h0'
    have : 2 * (x ⬝ᵥ xStar : Real) ≤ (x ⬝ᵥ Q x : Real) + (xStar ⬝ᵥ q : Real) := by
      nlinarith
    linarith [h0]
  have hE :
      (((x ⬝ᵥ xStar : Real) - (1 / 2 : Real) * (x ⬝ᵥ Q x) : Real) : EReal) ≤
        (((1 / 2 : Real) * (xStar ⬝ᵥ q) : Real) : EReal) := by
    exact_mod_cast hreal
  simpa [quadraticHalfLinear, q, EReal.coe_sub, EReal.coe_mul, sub_eq_add_neg, mul_assoc, mul_comm,
    mul_left_comm, add_assoc, add_comm, add_left_comm] using hE

/-- Text 12.3.2: Let `Q` be a symmetric positive semi-definite `n × n` matrix and consider the
quadratic convex function `h(x) = (1/2) * ⟪x, Qx⟫`. Let `L = range(Q)` and let `Q'` be the
Moore–Penrose pseudoinverse, characterized by `Q Q' = Q' Q = P_L` where `P_L` is the orthogonal
projection onto `L`. Then the conjugate function `h*` has the piecewise form
`h*(x*) = (1/2) * ⟪x*, Q' x*⟫` for `x* ∈ L` and `h*(x*) = +∞` for `x* ∉ L`. (If `Q` is
nonsingular, then `L = ℝ^n` and `Q' = Q⁻¹`.) -/
theorem fenchelConjugate_quadraticHalfLinear_pseudoinverse (n : Nat)
    (Q Q' P_L : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) (L : Submodule ℝ (Fin n → Real))
    (hL : L = LinearMap.range Q) (hQQ' : Q.comp Q' = P_L) (_hQ'Q : Q'.comp Q = P_L)
    (hP_L_id : ∀ xStar : Fin n → Real, xStar ∈ L → P_L xStar = xStar)
    (hQsymm : ∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y)
    (hQpsd : ∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Q x) :
    fenchelConjugate n (quadraticHalfLinear n Q) =
      (by
        classical
        exact fun xStar =>
          if xStar ∈ L then quadraticHalfLinear n Q' xStar else (⊤ : EReal)) := by
  classical
  ext xStar
  unfold fenchelConjugate
  by_cases hxStar : xStar ∈ L
  · -- On `L`, complete the square to get the exact value.
    rw [if_pos hxStar]
    refine le_antisymm ?_ ?_
    · -- Upper bound by the completed-square inequality.
      refine sSup_le ?_
      rintro y ⟨x, rfl⟩
      exact
        range_term_quadraticHalfLinear_le_on_L (Q := Q) (Q' := Q') (P_L := P_L) (L := L) hQQ'
          hP_L_id hQsymm hQpsd hxStar x
    · -- Lower bound: evaluate the supremum at `x = Q' xStar`.
      have hxQq : Q (Q' xStar) = xStar := by
        simpa using
          Q_Q'_apply_eq_of_mem_L (Q := Q) (Q' := Q') (P_L := P_L) (L := L) hQQ' hP_L_id hxStar
      have hle :
          (((Q' xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q (Q' xStar)) ≤
            sSup
              (Set.range fun x : Fin n → Real =>
                ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q x) :=
        le_sSup ⟨Q' xStar, rfl⟩
      have hterm :
          ((Q' xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q (Q' xStar) =
            quadraticHalfLinear n Q' xStar := by
        -- `⟪Q' x*, x*⟫ - (1/2)⟪Q' x*, Q(Q' x*)⟫ = (1/2)⟪x*, Q' x*⟫`.
        set a : Real := (Q' xStar ⬝ᵥ xStar : Real)
        have ha : a - (1 / 2 : Real) * a = (1 / 2 : Real) * a := by ring
        calc
          ((Q' xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q (Q' xStar) =
              ((a : Real) : EReal) -
                (((1 / 2 : Real) * (Q' xStar ⬝ᵥ Q (Q' xStar) : Real) : Real) : EReal) := by
                  simp [quadraticHalfLinear, a]
          _ = ((a : Real) : EReal) - (((1 / 2 : Real) * a : Real) : EReal) := by
                -- Use `Q (Q' xStar) = xStar`.
                simp [a, hxQq]
          _ = ((a - (1 / 2 : Real) * a : Real) : EReal) := by
                exact (EReal.coe_sub a ((1 / 2 : Real) * a)).symm
          _ = (((1 / 2 : Real) * a : Real) : EReal) := by
                exact_mod_cast ha
          _ = quadraticHalfLinear n Q' xStar := by
                simp [quadraticHalfLinear, a, dotProduct_comm]
      simpa [hterm] using hle
  · -- Off `L`, the range term is unbounded above.
    rw [if_neg hxStar]
    -- Reduce to showing the supremum is `⊤` by real upper bounds.
    refine
      EReal.eq_of_forall_le_coe_iff (a := _) (b := (⊤ : EReal)) (fun μ => ?_)
    constructor
    · intro hle
      -- Construct a linear functional vanishing on `L` but sending `xStar` to `1`,
      -- then represent it as a dot product with a vector `v`.
      rcases
          LinearMap.exists_extend_of_notMem (p := L) (v := xStar) (f := (0 : L →ₗ[ℝ] Real))
            hxStar (1 : Real) with
        ⟨g, hgL, hgxStar⟩
      rcases linearMap_exists_dotProduct_representation (n := n) g with ⟨v, hv⟩
      have hxStar_v : xStar ⬝ᵥ v = 1 := by
        simpa [hv] using hgxStar
      have hQx_v : ∀ x : Fin n → Real, (Q x) ⬝ᵥ v = 0 := by
        intro x
        have hxmem : Q x ∈ L := by
          -- `Q x ∈ range Q = L`.
          rw [hL]
          exact ⟨x, rfl⟩
        have : g (Q x) = 0 := by
          have := congrArg (fun T : L →ₗ[ℝ] Real => T ⟨Q x, hxmem⟩) hgL
          simpa using this
        simpa [hv] using this
      have hQv : Q v = 0 := by
        -- From symmetry, `∀ x, x ⬝ᵥ Q v = 0`; take `x = Q v`.
        have hforall : ∀ x : Fin n → Real, x ⬝ᵥ Q v = 0 := by
          intro x
          have hx : (Q x) ⬝ᵥ v = x ⬝ᵥ Q v := by simpa using (hQsymm x v)
          simpa [hx] using hQx_v x
        have : (Q v) ⬝ᵥ (Q v) = 0 := by simpa using hforall (Q v)
        exact (dotProduct_self_eq_zero).1 this
      -- Evaluate the range term at `x = (μ + 1) • v`.
      set x : Fin n → Real := (μ + 1) • v
      have hx_term :
          ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q x = ((μ + 1 : Real) : EReal) := by
        have hQx : Q x = 0 := by simp [x, hQv]
        have hdot : (x ⬝ᵥ xStar : Real) = μ + 1 := by
          have hdot1 : (x ⬝ᵥ xStar : Real) = (μ + 1) * (v ⬝ᵥ xStar : Real) := by
            simp [x, smul_dotProduct, smul_eq_mul]
          have hvx : (v ⬝ᵥ xStar : Real) = 1 := by
            simpa [dotProduct_comm] using hxStar_v
          simpa [hvx] using hdot1
        simp [quadraticHalfLinear, x, hdot, hQx, sub_eq_add_neg]
      have hx_le_sSup :
          ((μ + 1 : Real) : EReal) ≤
            sSup
              (Set.range fun x : Fin n → Real =>
                ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q x) := by
        have hx_le :
            (((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q x) ≤
              sSup
                (Set.range fun z : Fin n → Real =>
                  ((z ⬝ᵥ xStar : Real) : EReal) - quadraticHalfLinear n Q z) :=
          le_sSup ⟨x, rfl⟩
        simpa [hx_term] using hx_le
      have hcontra : ((μ + 1 : Real) : EReal) ≤ (μ : EReal) := le_trans hx_le_sSup hle
      have : (μ + 1 : Real) ≤ μ := (EReal.coe_le_coe_iff).1 hcontra
      have : False := by linarith
      exact False.elim this
    · intro htop
      simp at htop

/-- Text 12.3.3: A proper convex function `f` on `ℝ^n` is a *partial quadratic convex function* if
it can be written as `f = q + δ(· | M)`, where `q` is a finite quadratic convex function and `M`
is an affine set. Moreover, `f` is partial quadratic iff, after an affine change of coordinates,
it has the form `x ↦ h (A (x - a)) + ⟪x, a*⟫ + α`, where `h` is an elementary partial quadratic
convex function, `A` is a bijective linear map, and `a, a* ∈ ℝ^n`, `α ∈ ℝ`. -/
def IsPartialQuadraticConvexFunction (n : Nat) (f : (Fin n → Real) → EReal) : Prop :=
  ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
    ∃ (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) (b : Fin n → Real) (c : Real)
        (M : AffineSubspace ℝ (Fin n → Real)),
      (∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Q x) ∧
        f =
          fun x =>
            quadraticHalfLinear n Q x + ((x ⬝ᵥ b : Real) : EReal) + (c : EReal) +
              indicatorFunction (M : Set (Fin n → Real)) x

/-- Text 12.3.3 (elementary model): An *elementary partial quadratic convex function* is a
prototype partial quadratic convex function given by a diagonal quadratic form plus the indicator
of a linear subspace. -/
def IsElementaryPartialQuadraticConvexFunction (n : Nat) (h : (Fin n → Real) → EReal) : Prop :=
  ∃ (d : Fin n → Real) (L : Submodule ℝ (Fin n → Real)),
    (∀ i : Fin n, 0 ≤ d i) ∧
      h =
        fun x =>
          (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal) +
            indicatorFunction (L : Set (Fin n → Real)) x

/-- If a proper convex function can be written as `r + δ(· | M)`, then the affine subspace `M`
must be nonempty. This is extracted by taking a point in the (nonempty) epigraph of `f` and
observing that off `M` the indicator term forces `f = ⊤`. -/
lemma exists_mem_affineSubspace_of_proper_of_eq_indicator {n : Nat}
    {f r : (Fin n → Real) → EReal} {M : AffineSubspace ℝ (Fin n → Real)}
    (hfprop : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hr_ne_bot : ∀ x : Fin n → Real, r x ≠ (⊥ : EReal))
    (hfEq : f = fun x => r x + indicatorFunction (M : Set (Fin n → Real)) x) :
    ∃ a : Fin n → Real, a ∈ M := by
  classical
  rcases hfprop.2.1 with ⟨p, hp⟩
  have hp' : (Set.univ : Set (Fin n → Real)) p.1 ∧ f p.1 ≤ (p.2 : EReal) := by
    simpa [epigraph] using hp
  have hle : f p.1 ≤ (p.2 : EReal) := hp'.2
  by_cases hpM : p.1 ∈ (M : Set (Fin n → Real))
  · exact ⟨p.1, hpM⟩
  · have hfTop : f p.1 = (⊤ : EReal) := by
      calc
        f p.1 = r p.1 + indicatorFunction (M : Set (Fin n → Real)) p.1 := by
          simp [hfEq]
        _ = r p.1 + (⊤ : EReal) := by
          simp [indicatorFunction, hpM]
        _ = (⊤ : EReal) := by
          simpa using (EReal.add_top_of_ne_bot (hr_ne_bot p.1))
    have : (⊤ : EReal) ≤ (p.2 : EReal) := by
      have hle' := hle
      rw [hfTop] at hle'
      exact hle'
    exact (not_top_le_coe p.2 this).elim

/-- Re-center the indicator of an affine subspace at a base point: translating by `a ∈ M` turns
`δ(· | M)` into the indicator of the direction submodule `M.direction`. -/
lemma indicatorFunction_affineSubspace_eq_indicator_direction_sub {n : Nat}
    (M : AffineSubspace ℝ (Fin n → Real)) {a : Fin n → Real} (ha : a ∈ M) :
    ∀ x : Fin n → Real,
      indicatorFunction (M : Set (Fin n → Real)) x =
        indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) := by
  classical
  intro x
  by_cases hx : x ∈ (M : Set (Fin n → Real))
  · have hxdir : x - a ∈ M.direction := by
      have : x -ᵥ a ∈ M.direction := AffineSubspace.vsub_mem_direction (s := M) hx ha
      simpa [vsub_eq_sub] using this
    simp [indicatorFunction, hx, hxdir]
  · have hxdir : x - a ∉ M.direction := by
      intro hxdir
      have : x -ᵥ a ∈ M.direction := by simpa [vsub_eq_sub] using hxdir
      have hx' : x ∈ M :=
        (AffineSubspace.vsub_right_mem_direction_iff_mem (s := M) ha x).1 this
      exact hx hx'
    simp [indicatorFunction, hx, hxdir]

/-- Convert dot products on `Fin n → ℝ` into inner products on `EuclideanSpace ℝ (Fin n)` via
`EuclideanSpace.equiv`. This is the bridge that allows the use of spectral-theorem APIs. -/
lemma dotProduct_eq_inner_euclideanSpace (n : Nat) (x y : Fin n → Real) :
    (x ⬝ᵥ y : Real) =
      inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm y) := by
  classical
  -- Use `EuclideanSpace.inner_eq_star_dotProduct` and simplify via the `equiv`/`symm` relation.
  -- Note: for `ℝ`, `star` is the identity.
  have :
      inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm y) =
        (y ⬝ᵥ x : Real) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa [dotProduct_comm] using this.symm

/-- Replace a linear map by its dot-product symmetric part without changing the associated
quadratic form `x ↦ x ⬝ᵥ Q x`. This is implemented by transporting to `EuclideanSpace` and
symmetrizing using the adjoint. -/
lemma linearMap_symmPart_dotProduct_preserves_quadratic {n : Nat}
    (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real)) :
    ∃ Qs : (Fin n → Real) →ₗ[ℝ] (Fin n → Real),
      (∀ x y : Fin n → Real, (Qs x) ⬝ᵥ y = x ⬝ᵥ Qs y) ∧
        ∀ x : Fin n → Real, (x ⬝ᵥ Qs x : Real) = (x ⬝ᵥ Q x : Real) := by
  classical
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  let Qe : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    eL.symm.toLinearMap ∘ₗ Q ∘ₗ eL.toLinearMap
  let Qse : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((1 / 2 : Real) • (Qe + LinearMap.adjoint Qe))
  let Qs : (Fin n → Real) →ₗ[ℝ] (Fin n → Real) :=
    eL.toLinearMap ∘ₗ Qse ∘ₗ eL.symm.toLinearMap
  refine ⟨Qs, ?_, ?_⟩
  · intro x y
    have hQse_symm :
        ∀ u v : EuclideanSpace ℝ (Fin n),
          inner ℝ (Qse u) v = inner ℝ u (Qse v) := by
      intro u v
      have hleft : inner ℝ ((LinearMap.adjoint Qe) u) v = inner ℝ u (Qe v) := by
        simpa using (LinearMap.adjoint_inner_left (A := Qe) (x := v) (y := u))
      have hright : inner ℝ u ((LinearMap.adjoint Qe) v) = inner ℝ (Qe u) v := by
        simpa using (LinearMap.adjoint_inner_right (A := Qe) (x := u) (y := v))
      -- Expand both sides, then use the defining properties of the adjoint.
      simp [Qse, inner_add_left, inner_smul_left, inner_add_right, inner_smul_right, hleft, hright,
        add_comm]
    -- Translate dot products into `EuclideanSpace` inner products and use symmetry of `Qse`.
    -- Start by rewriting dot products via `dotProduct_eq_inner_euclideanSpace`.
    rw [dotProduct_eq_inner_euclideanSpace (n := n) (x := Qs x) (y := y)]
    rw [dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Qs y)]
    -- Normalize the bridge maps back to `eL.symm` (Lean may display these as `WithLp.toLp`).
    change inner ℝ (eL.symm (Qs x)) (eL.symm y) = inner ℝ (eL.symm x) (eL.symm (Qs y))
    -- Cancel the `EuclideanSpace.equiv`/`symm` bridges.
    have hcancel1 : eL.symm (Qs x) = Qse (eL.symm x) := by
      simp [Qs, LinearMap.comp_apply]
    have hcancel2 : eL.symm (Qs y) = Qse (eL.symm y) := by
      simp [Qs, LinearMap.comp_apply]
    simpa [hcancel1, hcancel2] using hQse_symm (eL.symm x) (eL.symm y)
  · intro x
    -- Reduce to the corresponding statement on `EuclideanSpace`.
    have hx :
        (x ⬝ᵥ Qs x : Real) =
          inner ℝ (eL.symm x) (eL.symm (Qs x)) := by
      simpa using dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Qs x)
    have hxQ :
        (x ⬝ᵥ Q x : Real) =
          inner ℝ (eL.symm x) (eL.symm (Q x)) := by
      simpa using dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Q x)
    have hcancel : eL.symm (Qs x) = Qse (eL.symm x) := by
      simp [Qs, LinearMap.comp_apply]
    have hQcancel : eL.symm (Q x) = Qe (eL.symm x) := by
      simp [Qe, LinearMap.comp_apply]
    -- Show `inner u (Qse u) = inner u (Qe u)` for `u = eL.symm x`.
    have hquad :
        inner ℝ (eL.symm x) (Qse (eL.symm x)) = inner ℝ (eL.symm x) (Qe (eL.symm x)) := by
      have hadj :
          inner ℝ (eL.symm x) ((LinearMap.adjoint Qe) (eL.symm x)) =
            inner ℝ (Qe (eL.symm x)) (eL.symm x) := by
        simpa using
          (LinearMap.adjoint_inner_right (A := Qe) (x := eL.symm x) (y := eL.symm x))
      calc
        inner ℝ (eL.symm x) (Qse (eL.symm x)) =
            inner ℝ (eL.symm x)
              (((1 / 2 : Real) • (Qe + LinearMap.adjoint Qe)) (eL.symm x)) := by
                simp [Qse]
        _ = (1 / 2 : Real) *
              (inner ℝ (eL.symm x) (Qe (eL.symm x)) +
                inner ℝ (eL.symm x) ((LinearMap.adjoint Qe) (eL.symm x))) := by
              simp [LinearMap.add_apply, inner_add_right, inner_smul_right, mul_add]
        _ = (1 / 2 : Real) *
              (inner ℝ (eL.symm x) (Qe (eL.symm x)) +
                inner ℝ (Qe (eL.symm x)) (eL.symm x)) := by
              simp [hadj]
        _ = (1 / 2 : Real) *
              (inner ℝ (eL.symm x) (Qe (eL.symm x)) +
                inner ℝ (eL.symm x) (Qe (eL.symm x))) := by
              simp [real_inner_comm]
        _ = inner ℝ (eL.symm x) (Qe (eL.symm x)) := by ring
    -- Translate back to dot products.
    simpa [hx, hxQ, hcancel, hQcancel] using hquad

/-- Transporting an indicator function along a linear equivalence using `Submodule.comap`. -/
lemma indicatorFunction_submodule_comap_linearEquiv {n : Nat} (L : Submodule ℝ (Fin n → Real))
    (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real)) :
    ∀ v : Fin n → Real,
      indicatorFunction ((L.comap A.toLinearMap : Submodule ℝ (Fin n → Real)) : Set (Fin n → Real))
          v =
        indicatorFunction (L : Set (Fin n → Real)) (A v) := by
  classical
  intro v
  by_cases hv : A v ∈ (L : Set (Fin n → Real))
  · have hv' : v ∈ (L.comap A.toLinearMap : Submodule ℝ (Fin n → Real)) := by
      simpa using hv
    simp [indicatorFunction, hv]
  · have hv' : v ∉ (L.comap A.toLinearMap : Submodule ℝ (Fin n → Real)) := by
      simpa using hv
    simp [indicatorFunction, hv]

/-- Translation identity for the quadratic term when `Q` is symmetric with respect to the dot
product. This is the algebraic step used to rewrite a quadratic form in `x` in terms of `x-a`,
plus a linear term and a constant. -/
lemma quadraticHalfLinear_translate_of_dotProduct_symmetric {n : Nat}
    (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real))
    (hQsymm : ∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y) :
    ∀ a x : Fin n → Real,
      quadraticHalfLinear n Q x =
        quadraticHalfLinear n Q (x - a) + ((x ⬝ᵥ Q a : Real) : EReal) +
          (((-(1 / 2 : Real)) * (a ⬝ᵥ Q a) : Real) : EReal) := by
  classical
  intro a x
  -- Work in `Real`, then coerce to `EReal`.
  have hax : (a ⬝ᵥ Q x : Real) = (x ⬝ᵥ Q a : Real) := by
    calc
      (a ⬝ᵥ Q x : Real) = (Q x ⬝ᵥ a : Real) := by simp [dotProduct_comm]
      _ = (x ⬝ᵥ Q a : Real) := by simpa using (hQsymm x a)
  have h_expand :
      (x - a) ⬝ᵥ Q (x - a) =
        (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ Q a : Real) + (a ⬝ᵥ Q a : Real) := by
    calc
      (x - a) ⬝ᵥ Q (x - a) =
          (x ⬝ᵥ Q x : Real) - (x ⬝ᵥ Q a : Real) - (a ⬝ᵥ Q x : Real) + (a ⬝ᵥ Q a : Real) := by
            simp [sub_eq_add_neg, add_dotProduct, dotProduct_add, map_add, map_neg, add_assoc,
              add_comm, add_left_comm]
      _ = (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ Q a : Real) + (a ⬝ᵥ Q a : Real) := by
            nlinarith [hax]
  have hreal :
      (1 / 2 : Real) * (x ⬝ᵥ Q x : Real) =
        (1 / 2 : Real) * ((x - a) ⬝ᵥ Q (x - a) : Real) + (x ⬝ᵥ Q a : Real) +
          (-(1 / 2 : Real)) * (a ⬝ᵥ Q a : Real) := by
    -- Substitute the expansion and simplify.
    rw [h_expand]
    ring
  -- Coerce the real identity into `EReal` and rewrite `quadraticHalfLinear`.
  have hE : (((1 / 2 : Real) * (x ⬝ᵥ Q x) : Real) : EReal) =
      (((1 / 2 : Real) * ((x - a) ⬝ᵥ Q (x - a)) : Real) : EReal) + ((x ⬝ᵥ Q a : Real) : EReal) +
        (((-(1 / 2 : Real)) * (a ⬝ᵥ Q a) : Real) : EReal) := by
    exact_mod_cast hreal
  -- Finish by unfolding `quadraticHalfLinear`.
  simpa [quadraticHalfLinear, add_assoc, add_left_comm, add_comm] using hE

/-- Diagonalize a dot-product symmetric positive semidefinite linear operator on `ℝ^n` by
transporting to `EuclideanSpace` and applying the spectral theorem. -/
lemma exists_linearEquiv_diagonalize_psd_dotProduct {n : Nat}
    (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real))
    (hQsymm : ∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y)
    (hpsd : ∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Q x) :
    ∃ (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real)) (d : Fin n → Real),
      (∀ i : Fin n, 0 ≤ d i) ∧ ∀ x : Fin n → Real, (x ⬝ᵥ Q x : Real) = ∑ i, d i * (A x i) ^ 2 := by
  classical
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → Real) := eL.toLinearEquiv
  let Qe : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.symm.toLinearMap ∘ₗ Q ∘ₗ e.toLinearMap
  have hQe_symm : LinearMap.IsSymmetric Qe := by
    -- Convert to dot products via `dotProduct_eq_inner_euclideanSpace` and apply `hQsymm`.
    intro u v
    have hu :
        inner ℝ (Qe u) v =
          (Q (e u) ⬝ᵥ e v : Real) := by
      -- `inner (Qe u) v = ⬝ᵥ` of the corresponding vectors in `Fin n → ℝ`.
      have :=
        (dotProduct_eq_inner_euclideanSpace (n := n) (x := Q (e u)) (y := e v)).symm
      simpa [Qe, eL, e, LinearMap.comp_apply] using this
    have hv :
        inner ℝ u (Qe v) =
          (e u ⬝ᵥ Q (e v) : Real) := by
      have :=
        (dotProduct_eq_inner_euclideanSpace (n := n) (x := e u) (y := Q (e v))).symm
      simpa [Qe, eL, e, LinearMap.comp_apply] using this
    -- Now use dot-product symmetry of `Q`.
    simpa [hu, hv] using congrArg (fun r : Real => r) (hQsymm (e u) (e v))
  have hpsdE : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ u (Qe u) := by
    intro u
    have hu :
        inner ℝ u (Qe u) = (e u ⬝ᵥ Q (e u) : Real) := by
      have :=
        (dotProduct_eq_inner_euclideanSpace (n := n) (x := e u) (y := Q (e u))).symm
      simpa [Qe, eL, e, LinearMap.comp_apply] using this
    simpa [hu, dotProduct_comm] using hpsd (e u)
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hQe_symm.eigenvectorBasis (n := n) hn
  let d : Fin n → Real := fun i => hQe_symm.eigenvalues hn i
  have hd_nonneg : ∀ i : Fin n, 0 ≤ d i := by
    intro i
    have hpos := hpsdE (b i)
    have hb :
        inner ℝ (b i) (Qe (b i)) = d i := by
      have hTb :
          Qe (b i) = (d i) • b i := by
        dsimp [b, d]
        exact hQe_symm.apply_eigenvectorBasis (hn := hn) (i := i)
      -- `⟪b i, d i • b i⟫ = d i`.
      simp [hTb, d, b, inner_smul_right]
    simpa [hb] using hpos
  -- Define the linear equivalence giving eigen-coordinates on `Fin n → ℝ`.
  let A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real) :=
    (eL.symm.toLinearEquiv.trans (b.repr.toLinearEquiv)).trans e
  refine ⟨A, d, hd_nonneg, ?_⟩
  intro x
  -- Convert the dot product into an inner product on `EuclideanSpace`.
  have hxInner :
      (x ⬝ᵥ Q x : Real) = inner ℝ (eL.symm x) (Qe (eL.symm x)) := by
    have := dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Q x)
    -- `eL.symm (Q x) = Qe (eL.symm x)`.
    simpa [Qe, eL, e, LinearMap.comp_apply] using this
  -- Expand the quadratic form in the eigenbasis coordinates.
  have hdiag :
      inner ℝ (eL.symm x) (Qe (eL.symm x)) =
        ∑ i : Fin n, d i * (A x i) ^ 2 := by
    -- Express `⟪u, Qe u⟫` in the orthonormal eigenbasis coordinates.
    set u : EuclideanSpace ℝ (Fin n) := eL.symm x
    have hsum :
        inner ℝ u (Qe u) = ∑ i : Fin n, (b.repr u i) * (b.repr (Qe u) i) := by
      -- Parseval in an orthonormal basis, rewritten using `repr`.
      simpa [OrthonormalBasis.repr_apply_apply, real_inner_comm, u] using
        (OrthonormalBasis.sum_inner_mul_inner (b := b) (x := u) (y := Qe u)).symm
    have hscale :
        ∀ i : Fin n, b.repr (Qe u) i = d i * b.repr u i := by
      intro i
      have := hQe_symm.eigenvectorBasis_apply_self_apply (hn := hn) (v := u) (i := i)
      -- This lemma is stated for `hQe_symm.eigenvectorBasis hn`, which is `b`.
      simpa [b, d, u, mul_assoc, mul_left_comm, mul_comm] using this
    have hAcoord : ∀ i : Fin n, b.repr u i = A x i := by
      intro i
      simp [A, u, eL, e]
    calc
      inner ℝ (eL.symm x) (Qe (eL.symm x)) =
          ∑ i : Fin n, (b.repr u i) * (b.repr (Qe u) i) := by
            simpa [u] using hsum
      _ = ∑ i : Fin n, d i * (b.repr u i) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hscale i, pow_two, mul_assoc, mul_comm]
      _ = ∑ i : Fin n, d i * (A x i) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hAcoord i]
  -- Finish.
  simpa [hxInner] using hdiag

end Section12
end Chap03
