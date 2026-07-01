/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part8

open scoped Pointwise

section Chap03
section Section13

/-- Theorem 13.4 (primal part): for proper convex `f`, the linearity space of `f*` is the
orthogonal complement of the direction of `affineSpan (dom f)`. -/
lemma section13_span_linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    Submodule.span ℝ (linearitySpace (fenchelConjugate n f)) =
      orthogonalComplement n
        ((affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction) := by
  classical
  set domF : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hdomFne : domF.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf
  -- Auxiliary: compute the support function from constancy of `dotProduct · y`.
  have hsupp_eq_of_const {y : Fin n → Real} {μ : Real}
      (hμ : ∀ x ∈ domF, dotProduct x y = μ) :
      supportFunctionEReal domF y = (μ : EReal) := by
    unfold supportFunctionEReal
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      simp [hμ x hx]
    · rcases hdomFne with ⟨x0, hx0⟩
      refine le_sSup ?_
      exact ⟨x0, hx0, by simp [hμ x0 hx0]⟩
  -- Main equality via elementwise characterization and `span`.
  refine le_antisymm ?_ ?_
  · -- `span (linearitySpace f*) ≤ ...`
    refine Submodule.span_le.2 ?_
    intro y hy
    have hy' :
        supportFunctionEReal domF y ≠ ⊤ ∧
          (-(supportFunctionEReal domF (-y)) = supportFunctionEReal domF y) := by
      simpa [domF] using
        (section13_linearitySpace_fenchelConjugate_iff_supportFunctionEReal_effectiveDomain
          (n := n) (f := f) hf y).1 hy
    have hconst :
        ∃ μ : Real, ∀ x ∈ domF, dotProduct x y = μ :=
      section13_supportFunctionEReal_symm_finite_imp_dotProduct_const (n := n) (C := domF) hdomFne
        (y := y) hy'.1 hy'.2
    have : y ∈ orthogonalComplement n ((affineSpan ℝ domF).direction) :=
      (section13_dotProduct_const_iff_mem_orthogonalComplement_direction_affineSpan (n := n)
          (C := domF) hdomFne y).1 hconst
    simpa [domF] using this
  · -- `... ≤ span (linearitySpace f*)`
    intro y hy
    have hconst :
        ∃ μ : Real, ∀ x ∈ domF, dotProduct x y = μ :=
      (section13_dotProduct_const_iff_mem_orthogonalComplement_direction_affineSpan (n := n)
          (C := domF) hdomFne y).2 (by simpa [domF] using hy)
    rcases hconst with ⟨μ, hμ⟩
    have hsupp : supportFunctionEReal domF y = (μ : EReal) := hsupp_eq_of_const (y := y) hμ
    have hsupp_neg : supportFunctionEReal domF (-y) = ((-μ : Real) : EReal) := by
      have hμ' : ∀ x ∈ domF, dotProduct x (-y) = -μ := by
        intro x hx
        simp [dotProduct_neg, hμ x hx]
      simpa using (hsupp_eq_of_const (y := -y) (μ := -μ) hμ')
    have hy_mem : y ∈ linearitySpace (fenchelConjugate n f) := by
      apply
        (section13_linearitySpace_fenchelConjugate_iff_supportFunctionEReal_effectiveDomain
          (n := n) (f := f) hf y).2
      have hsupp_y' :
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y =
            (μ : EReal) := by
        simpa [domF] using hsupp
      have hsupp_neg' :
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (-y) =
            ((-μ : Real) : EReal) := by
        simpa [domF] using hsupp_neg
      refine ⟨?_, ?_⟩
      ·
        simp [hsupp_y']
      ·
        simp [hsupp_y', hsupp_neg']
    exact Submodule.subset_span hy_mem

/-- Theorem 13.4: Let `f` be a proper convex function on `ℝ^n`. The linearity space of `f^*`
is the orthogonal complement of the subspace parallel to `aff (dom f)`. Dually, if `f` is closed,
the subspace parallel to `aff (dom f^*)` is the orthogonal complement of the linearity space of
`f`, and one has

`linearity f^* = n - dimension f`, and `dimension f^* = n - linearity f`. -/
theorem linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain_and_dual
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (let domF : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
      let domFstar : Set (Fin n → Real) :=
        effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
      (Submodule.span ℝ (linearitySpace (fenchelConjugate n f)) =
            orthogonalComplement n ((affineSpan ℝ domF).direction)) ∧
        (ClosedConvexFunction f →
            (affineSpan ℝ domFstar).direction =
                orthogonalComplement n (Submodule.span ℝ (linearitySpace f)) ∧
              (Module.finrank ℝ (Submodule.span ℝ (linearitySpace (fenchelConjugate n f))) =
                  n - Module.finrank ℝ ((affineSpan ℝ domF).direction)) ∧
                (Module.finrank ℝ ((affineSpan ℝ domFstar).direction) =
                  n - Module.finrank ℝ (Submodule.span ℝ (linearitySpace f))))) := by
  classical
  dsimp
  set domF : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) f
  set domFstar : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hspan :
      Submodule.span ℝ (linearitySpace (fenchelConjugate n f)) =
        orthogonalComplement n ((affineSpan ℝ domF).direction) := by
    simpa [domF] using
      (section13_span_linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain
        (n := n) (f := f) hf)
  refine ⟨hspan, ?_⟩
  intro hclosed
  -- Finrank formula for the primal equality.
  have hfinrank_primal :
      Module.finrank ℝ (Submodule.span ℝ (linearitySpace (fenchelConjugate n f))) =
        n - Module.finrank ℝ ((affineSpan ℝ domF).direction) := by
    calc
      Module.finrank ℝ (Submodule.span ℝ (linearitySpace (fenchelConjugate n f))) =
          Module.finrank ℝ (orthogonalComplement n ((affineSpan ℝ domF).direction)) := by
            simpa using
              congrArg (fun S : Submodule ℝ (Fin n → Real) => Module.finrank ℝ S) hspan
      _ = n - Module.finrank ℝ ((affineSpan ℝ domF).direction) :=
          section13_finrank_orthogonalComplement (n := n) ((affineSpan ℝ domF).direction)
  -- Apply the primal part to `f*` and use biconjugacy under closedness to get `span(linearity f)`.
  have hfStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hclosed.2) (hf_proper := hf)
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = f := by
    have : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
      fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
    simpa [hcl] using this
  have hspan_f :
      Submodule.span ℝ (linearitySpace f) =
        orthogonalComplement n ((affineSpan ℝ domFstar).direction) := by
    -- Apply the primal lemma to `f*` and rewrite `f** = f`.
    have :=
      section13_span_linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain
        (n := n) (f := fenchelConjugate n f) hfStar
    simpa [domFstar, hbiconj] using this
  -- Deduce the direction equality by inclusion + finrank.
  set dirStar : Submodule ℝ (Fin n → Real) := (affineSpan ℝ domFstar).direction
  set L : Submodule ℝ (Fin n → Real) := Submodule.span ℝ (linearitySpace f)
  have hspan_f' : L = orthogonalComplement n dirStar := by simpa [L, dirStar] using hspan_f
  have hdir_le : dirStar ≤ orthogonalComplement n L := by
    intro v hv
    intro x hx
    have hx' : x ∈ orthogonalComplement n dirStar := by simpa [hspan_f'] using hx
    have : x ⬝ᵥ v = 0 := hx' v hv
    simpa [dotProduct_comm] using this
  have hdir_le_n : Module.finrank ℝ dirStar ≤ n := by
    simpa [dirStar, Module.finrank_fin_fun] using
      (Submodule.finrank_le (R := ℝ) (M := (Fin n → Real)) dirStar)
  have hfin_L : Module.finrank ℝ L = n - Module.finrank ℝ dirStar := by
    -- `L = dirStarᗮ`, so compute `finrank L` from `finrank (dirStarᗮ)`.
    calc
      Module.finrank ℝ L = Module.finrank ℝ (orthogonalComplement n dirStar) := by
            simpa using
              congrArg (fun S : Submodule ℝ (Fin n → Real) => Module.finrank ℝ S) hspan_f'
      _ = n - Module.finrank ℝ dirStar := section13_finrank_orthogonalComplement (n := n) dirStar
  have hfin_dirStar : Module.finrank ℝ dirStar = n - Module.finrank ℝ L := by
    -- Rearrange `finrank L = n - finrank dirStar` using `finrank dirStar ≤ n`.
    have hab :
        Module.finrank ℝ L + Module.finrank ℝ dirStar = n := by
      calc
        Module.finrank ℝ L + Module.finrank ℝ dirStar =
            (n - Module.finrank ℝ dirStar) + Module.finrank ℝ dirStar := by simp [hfin_L]
        _ = n := Nat.sub_add_cancel hdir_le_n
    have :
        Module.finrank ℝ dirStar =
          (Module.finrank ℝ L + Module.finrank ℝ dirStar) - Module.finrank ℝ L := by
      simp
    simpa [hab] using this
  have hfinrank_eq :
      Module.finrank ℝ dirStar = Module.finrank ℝ (orthogonalComplement n L) := by
    calc
      Module.finrank ℝ dirStar = n - Module.finrank ℝ L := hfin_dirStar
      _ = Module.finrank ℝ (orthogonalComplement n L) := by
            simpa using (section13_finrank_orthogonalComplement (n := n) L).symm
  have hdir_eq : dirStar = orthogonalComplement n L := by
    exact Submodule.eq_of_le_of_finrank_eq hdir_le (by simpa using hfinrank_eq)
  have hfinrank_dual :
      Module.finrank ℝ ((affineSpan ℝ domFstar).direction) =
        n - Module.finrank ℝ (Submodule.span ℝ (linearitySpace f)) := by
    -- Use the just-proved direction equality and `section13_finrank_orthogonalComplement`.
    simpa [dirStar, L] using hfin_dirStar
  refine ⟨?_, ?_, ?_⟩
  · simpa [dirStar, L] using hdir_eq
  · exact hfinrank_primal
  · exact hfinrank_dual

end Section13
end Chap03
