/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part1

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- The Euclidean-space equivalence reduces to the identity on `Fin n → ℝ`. -/
@[simp] lemma section16_euclideanSpace_equiv_toLp {n : Nat} (x : Fin n → ℝ) :
    (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
  rfl

/-- The inverse Euclidean-space equivalence reduces to `WithLp.toLp`. -/
@[simp] lemma section16_euclideanSpace_equiv_symm_apply {n : Nat} (x : Fin n → ℝ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm x = WithLp.toLp 2 x := by
  rfl

/-- Corollary 16.2.1. Let `A` be a linear transformation from `ℝ^n` to `ℝ^m` and let `g` be a
proper convex function on `ℝ^m`. Then there exists no vector `y* ∈ ℝ^m` such that

`A^* y* = 0`, `(g^*0^+)(y*) ≤ 0`, and `(g^*0^+)(-y*) > 0`

if and only if `A x ∈ ri (dom g)` for at least one `x ∈ ℝ^n`.

Here `dom g` is the effective domain `effectiveDomain univ g`, `ri` is `euclideanRelativeInterior`,
and `(g^*0^+)` is represented as `recessionFunction (fenchelConjugate m g)`. -/
theorem section16_exists_image_mem_ri_effectiveDomain_iff_not_exists_adjoint_eq_zero_recession_ineq
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    (¬ ∃ yStar : EuclideanSpace ℝ (Fin m),
        ((LinearMap.adjoint :
                (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                  (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
              A)
            yStar = 0 ∧
          recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
            recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal)) ↔
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
  classical
  let L : Submodule ℝ (Fin m → ℝ) := LinearMap.range (section16_coordLinearMap A)
  have hnonempty :
      Set.Nonempty
          (((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' (L : Set (Fin m → ℝ))) ∩
            euclideanRelativeInterior m
              ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) ↔
        ∃ x : EuclideanSpace ℝ (Fin n),
          A x ∈
            euclideanRelativeInterior m
              ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    simpa [L] using
      (section16_nonempty_preimage_range_inter_ri_effectiveDomain_iff (A := A) (g := g))
  have horth :
      (∃ xStar : Fin m → ℝ,
          xStar ∈ orthogonalComplement m L ∧
            recessionFunction (fenchelConjugate m g) xStar ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate m g) (-xStar) > (0 : EReal)) ↔
        ∃ yStar : EuclideanSpace ℝ (Fin m),
          ((LinearMap.adjoint :
                  (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                    (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                A)
              yStar = 0 ∧
            recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal) := by
    simpa [L] using
      (section16_exists_orthogonalComplement_range_recession_iff_exists_adjoint_eq_zero_recession
        (A := A) (g := g))
  have hmain :
      Set.Nonempty
          (((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' (L : Set (Fin m → ℝ))) ∩
            euclideanRelativeInterior m
              ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) ↔
        ¬ ∃ xStar : Fin m → ℝ,
            xStar ∈ orthogonalComplement m L ∧
              recessionFunction (fenchelConjugate m g) xStar ≤ (0 : EReal) ∧
                recessionFunction (fenchelConjugate m g) (-xStar) > (0 : EReal) := by
    simpa [L] using
      (section16_subspace_meets_ri_effectiveDomain_iff_not_exists_orthogonal_recession_ineq
        (n := m) (L := L) (f := g) hg)
  have hnot :
      (¬ ∃ yStar : EuclideanSpace ℝ (Fin m),
          ((LinearMap.adjoint :
                  (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                    (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                A)
              yStar = 0 ∧
            recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal)) ↔
        ¬ ∃ xStar : Fin m → ℝ,
            xStar ∈ orthogonalComplement m L ∧
              recessionFunction (fenchelConjugate m g) xStar ≤ (0 : EReal) ∧
                recessionFunction (fenchelConjugate m g) (-xStar) > (0 : EReal) := by
    exact (not_congr horth).symm
  calc
    (¬ ∃ yStar : EuclideanSpace ℝ (Fin m),
        ((LinearMap.adjoint :
                (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                  (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
              A)
            yStar = 0 ∧
          recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
            recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal)) ↔
        ¬ ∃ xStar : Fin m → ℝ,
            xStar ∈ orthogonalComplement m L ∧
              recessionFunction (fenchelConjugate m g) xStar ≤ (0 : EReal) ∧
                recessionFunction (fenchelConjugate m g) (-xStar) > (0 : EReal) := hnot
    _ ↔
        Set.Nonempty
          (((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' (L : Set (Fin m → ℝ))) ∩
            euclideanRelativeInterior m
              ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) := hmain.symm
    _ ↔
        ∃ x : EuclideanSpace ℝ (Fin n),
          A x ∈
            euclideanRelativeInterior m
              ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := hnonempty

/-- Block equivalence between flattened vectors and block families. -/
noncomputable def section16_blockEquivFun {n m : Nat} :
    (Fin (m * n) → ℝ) ≃ₗ[ℝ] (Fin m → (Fin n → ℝ)) :=
  blockEquivFun (n := n) (m := m)

/-- Block projection linear map extracting the `i`-th block. -/
noncomputable def section16_blockLinearMap {n m : Nat} (i : Fin m) :
    (Fin (m * n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (LinearMap.proj i).comp (section16_blockEquivFun (n := n) (m := m)).toLinearMap

/-- Flatten a block family into a single vector. -/
noncomputable def section16_unblock {n m : Nat} :
    (Fin m → Fin n → ℝ) →ₗ[ℝ] (Fin (m * n) → ℝ) :=
  (section16_blockEquivFun (n := n) (m := m)).symm.toLinearMap

/-- Unblocking followed by block projection recovers the original block. -/
lemma section16_blockLinearMap_unblock {n m : Nat} (i : Fin m)
    (x : Fin m → Fin n → ℝ) :
    section16_blockLinearMap (n := n) (m := m) i (section16_unblock (n := n) (m := m) x) =
      x i := by
  classical
  simp [section16_blockLinearMap, section16_unblock, section16_blockEquivFun]

/-- Unblocking the block projections recovers the original vector. -/
lemma section16_unblock_blockLinearMap {n m : Nat} (x : Fin (m * n) → ℝ) :
    section16_unblock (n := n) (m := m)
        (fun i => section16_blockLinearMap (n := n) (m := m) i x) = x := by
  classical
  simp [section16_blockLinearMap, section16_unblock, section16_blockEquivFun]

/-- Diagonal block embedding sending `x` to the constant block family. -/
noncomputable def section16_diagBlockLinearMap {n m : Nat} :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → Fin n → ℝ) :=
  { toFun := fun x => fun _ => x
    map_add' := by
      intro x y
      ext i j
      rfl
    map_smul' := by
      intro r x
      ext i j
      rfl }

/-- Diagonal embedding into the flattened space. -/
noncomputable def section16_diagLinearMap {n m : Nat} :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (m * n) → ℝ) :=
  (section16_unblock (n := n) (m := m)).comp (section16_diagBlockLinearMap (n := n) (m := m))

/-- Block projection of the diagonal embedding is the identity. -/
lemma section16_blockLinearMap_diag {n m : Nat} (i : Fin m) (x : Fin n → ℝ) :
    section16_blockLinearMap (n := n) (m := m) i (section16_diagLinearMap (n := n) (m := m) x) =
      x := by
  classical
  simpa [section16_diagLinearMap, section16_diagBlockLinearMap] using
    (section16_blockLinearMap_unblock (n := n) (m := m) i (fun _ => x))

/-- Each block projection is surjective. -/
lemma section16_blockLinearMap_surjective {n m : Nat} (i : Fin m) :
    Function.Surjective (section16_blockLinearMap (n := n) (m := m) i) := by
  classical
  intro y
  refine ⟨section16_unblock (n := n) (m := m) (fun j => if j = i then y else 0), ?_⟩
  have h := section16_blockLinearMap_unblock (n := n) (m := m) i
    (fun j => if j = i then y else 0)
  simpa using h

/-- Diagonal embedding as a linear map on Euclidean space. -/
noncomputable def section16_diagLinearMapE {n m : Nat} :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m * n)) :=
  (EuclideanSpace.equiv (ι := Fin (m * n)) (𝕜 := ℝ)).symm.toLinearMap
    ∘ₗ (section16_diagLinearMap (n := n) (m := m))
    ∘ₗ (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).toLinearMap

/-- Block projection as a linear map on Euclidean space. -/
noncomputable def section16_blockLinearMapE {n m : Nat} (i : Fin m) :
    EuclideanSpace ℝ (Fin (m * n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.toLinearMap
    ∘ₗ (section16_blockLinearMap (n := n) (m := m) i)
    ∘ₗ (EuclideanSpace.equiv (ι := Fin (m * n)) (𝕜 := ℝ)).toLinearMap

/-- Coercion form of the diagonal map. -/
lemma section16_diagLinearMapE_apply {n m : Nat} (x : EuclideanSpace ℝ (Fin n)) :
    (section16_diagLinearMapE (n := n) (m := m) x : Fin (m * n) → ℝ) =
      section16_diagLinearMap (n := n) (m := m) (x : Fin n → ℝ) := by
  rfl

/-- Coercion form of the block projection. -/
lemma section16_blockLinearMapE_apply {n m : Nat} (i : Fin m)
    (y : EuclideanSpace ℝ (Fin (m * n))) :
    (section16_blockLinearMapE (n := n) (m := m) i y : Fin n → ℝ) =
      section16_blockLinearMap (n := n) (m := m) i (y : Fin (m * n) → ℝ) := by
  rfl

/-- Block projection of the diagonal embedding is the identity on Euclidean space. -/
lemma section16_blockLinearMapE_diag {n m : Nat} (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    section16_blockLinearMapE (n := n) (m := m) i
        (section16_diagLinearMapE (n := n) (m := m) x) =
      x := by
  ext j
  simp [section16_blockLinearMapE_apply, section16_diagLinearMapE_apply,
    section16_blockLinearMap_diag]

/-- Evaluate the block projection via the canonical index equivalence. -/
lemma section16_blockLinearMap_apply_equiv {n m : Nat} (i : Fin m) (x : Fin (m * n) → ℝ)
    (j : Fin n) :
    (section16_blockLinearMap (n := n) (m := m) i x) j =
      x ((Fintype.equivFinOfCardEq (by simp) : Fin m × Fin n ≃ Fin (m * n)) (i, j)) := by
  classical
  simp [section16_blockLinearMap, section16_blockEquivFun, blockEquivFun,
    euclideanSpace_equiv_prod_block, section16_euclideanSpace_equiv_toLp, Sigma.curry,
    piCongrLeft_symm_apply_const, piCongrLeft_apply_const]

/-- Evaluate unblocking via the canonical index equivalence. -/
lemma section16_unblock_apply_equiv {n m : Nat} (xStar : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) :
    (section16_unblock (n := n) (m := m) xStar)
        ((Fintype.equivFinOfCardEq (by simp) : Fin m × Fin n ≃ Fin (m * n)) (i, j)) =
      xStar i j := by
  classical
  simp [section16_unblock, section16_blockEquivFun, blockEquivFun,
    euclideanSpace_equiv_prod_block, Sigma.uncurry]

/-- Dot product against an unblocked vector splits by blocks. -/
lemma section16_dotProduct_unblock_eq_sum_blocks {n m : Nat}
    (xStar : Fin m → Fin n → ℝ) (x : Fin (m * n) → ℝ) :
    dotProduct x (section16_unblock (n := n) (m := m) xStar) =
      ∑ i : Fin m,
        dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) := by
  classical
  let e : Fin m × Fin n ≃ Fin (m * n) := Fintype.equivFinOfCardEq (by simp)
  have hsum :
      ∑ k : Fin (m * n), x k * (section16_unblock (n := n) (m := m) xStar) k =
        ∑ p : Fin m × Fin n, x (e p) * (section16_unblock (n := n) (m := m) xStar) (e p) := by
    refine Fintype.sum_equiv (e := e.symm)
      (f := fun k => x k * (section16_unblock (n := n) (m := m) xStar) k)
      (g := fun p => x (e p) * (section16_unblock (n := n) (m := m) xStar) (e p)) ?_
    intro k
    simp [e]
  have hsum' :
      ∑ p : Fin m × Fin n, x (e p) * (section16_unblock (n := n) (m := m) xStar) (e p) =
        ∑ i : Fin m, ∑ j : Fin n, x (e (i, j)) * xStar i j := by
    have hrewrite :
        (fun p : Fin m × Fin n => x (e p) *
            (section16_unblock (n := n) (m := m) xStar) (e p)) =
          fun p : Fin m × Fin n => x (e p) * xStar p.1 p.2 := by
      funext p
      rcases p with ⟨i, j⟩
      simp [section16_unblock_apply_equiv, e]
    simpa [hrewrite] using
      (Fintype.sum_prod_type (f := fun p : Fin m × Fin n => x (e p) * xStar p.1 p.2))
  calc
    dotProduct x (section16_unblock (n := n) (m := m) xStar) =
        ∑ k : Fin (m * n), x k * (section16_unblock (n := n) (m := m) xStar) k := by
      simp [dotProduct]
    _ = ∑ p : Fin m × Fin n, x (e p) * (section16_unblock (n := n) (m := m) xStar) (e p) := hsum
    _ = ∑ i : Fin m, ∑ j : Fin n, x (e (i, j)) * xStar i j := hsum'
    _ = ∑ i : Fin m,
        dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [dotProduct, section16_blockLinearMap_apply_equiv, e]

/-- Dot product with an unblocked vector splits symmetrically by blocks. -/
lemma section16_dotProduct_unblock_eq_sum_blocks_symm {n m : Nat}
    (xStar : Fin m → Fin n → ℝ) (x : Fin (m * n) → ℝ) :
    dotProduct (section16_unblock (n := n) (m := m) xStar) x =
      ∑ i : Fin m,
        dotProduct (xStar i) (section16_blockLinearMap (n := n) (m := m) i x) := by
  classical
  simpa [dotProduct_comm] using
    (section16_dotProduct_unblock_eq_sum_blocks (n := n) (m := m) (xStar := xStar) (x := x))

/-- The adjoint of the diagonal embedding is the sum of block projections. -/
lemma section16_diagLinearMapE_adjoint_eq_sum_blockLinearMapE {n m : Nat} :
    (LinearMap.adjoint (section16_diagLinearMapE (n := n) (m := m))) =
      ∑ i : Fin m, section16_blockLinearMapE (n := n) (m := m) i := by
  classical
  symm
  refine
    (LinearMap.eq_adjoint_iff
        (A := ∑ i : Fin m, section16_blockLinearMapE (n := n) (m := m) i)
        (B := section16_diagLinearMapE (n := n) (m := m))).2 ?_
  intro x y
  have hsum :
      (y.ofLp) ⬝ᵥ ∑ c : Fin m, (section16_blockLinearMap (n := n) (m := m) c) x.ofLp =
        ∑ c : Fin m, (y.ofLp) ⬝ᵥ (section16_blockLinearMap (n := n) (m := m) c) x.ofLp := by
    simpa using
      (dotProduct_sum (u := y.ofLp) (s := (Finset.univ : Finset (Fin m)))
        (v := fun c => (section16_blockLinearMap (n := n) (m := m) c) x.ofLp))
  have hdot' :
      section16_diagLinearMap (n := n) (m := m) y.ofLp ⬝ᵥ x.ofLp =
        ∑ c : Fin m, (y.ofLp) ⬝ᵥ (section16_blockLinearMap (n := n) (m := m) c) x.ofLp := by
    have hdot'' :
        dotProduct x.ofLp (section16_unblock (n := n) (m := m) (fun _ => y.ofLp)) =
          ∑ c : Fin m,
            dotProduct (section16_blockLinearMap (n := n) (m := m) c x.ofLp) (y.ofLp) := by
      simpa using
        (section16_dotProduct_unblock_eq_sum_blocks (n := n) (m := m)
          (xStar := fun _ => y.ofLp) (x := x.ofLp))
    have hdot''' :
        section16_unblock (n := n) (m := m) (fun _ => y.ofLp) ⬝ᵥ x.ofLp =
          ∑ c : Fin m, (y.ofLp) ⬝ᵥ (section16_blockLinearMap (n := n) (m := m) c) x.ofLp := by
      simpa [dotProduct_comm] using hdot''
    simpa [section16_diagLinearMap, section16_diagBlockLinearMap] using hdot'''
  have hdot :
      (y.ofLp) ⬝ᵥ ∑ c : Fin m, (section16_blockLinearMap (n := n) (m := m) c) x.ofLp =
        section16_diagLinearMap (n := n) (m := m) y.ofLp ⬝ᵥ x.ofLp := by
    exact hsum.trans hdot'.symm
  simpa [EuclideanSpace.inner_eq_star_dotProduct] using hdot

/-- Effective domain of a block-sum is the intersection of block preimages. -/
lemma section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal)) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
    effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
      ⋂ i : Fin m,
        (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
  classical
  intro g
  have hnotbot' :
      ∀ i : Fin m, ∀ x,
        (fun x => f i (section16_blockLinearMap (n := n) (m := m) i x)) x ≠ (⊥ : EReal) := by
    intro i x
    exact hnotbot i (section16_blockLinearMap (n := n) (m := m) i x)
  have hdom :
      effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ))
        (fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)) =
        ⋂ i,
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ))
            (fun x => f i (section16_blockLinearMap (n := n) (m := m) i x)) :=
    effectiveDomain_sum_eq_iInter_univ
      (f := fun i x => f i (section16_blockLinearMap (n := n) (m := m) i x)) hnotbot'
  have hdom' :
      (⋂ i,
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ))
            (fun x => f i (section16_blockLinearMap (n := n) (m := m) i x))) =
        ⋂ i : Fin m,
          (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
    ext x
    simp [Set.mem_iInter, effectiveDomain_eq]
  simpa [g] using hdom.trans hdom'

/-- Properness of the block-sum function assembled from proper convex summands. -/
lemma section16_properConvexFunctionOn_blockSum {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → ℝ))
      (fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)) := by
  classical
  have hproper :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → ℝ))
          (fun x => f i (section16_blockLinearMap (n := n) (m := m) i x)) := by
    intro i
    exact
      properConvexFunctionOn_precomp_linearMap_surjective
        (A := section16_blockLinearMap (n := n) (m := m) i)
        (hA := section16_blockLinearMap_surjective (n := n) (m := m) i)
        (hf := hf i)
  have hdom_ne :
      ∀ i : Fin m,
        Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
    intro i
    have h :=
      (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
        (S := (Set.univ : Set (Fin n → ℝ))) (f := f i)).1 (hf i)
    exact h.2.1
  classical
  choose x0 hx0 using hdom_ne
  have hnot_top_term : ∀ i : Fin m, f i (x0 i) ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f i) (x := x0 i) (hx0 i)
  have hnot_top_sum :
      ∑ i, f i (x0 i) ≠ (⊤ : EReal) := by
    refine finset_sum_ne_top_of_forall (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => f i (x0 i)) ?_
    intro a ha
    exact hnot_top_term a
  have hexists :
      ∃ x : Fin (m * n) → ℝ,
        (∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)) ≠ (⊤ : EReal) := by
    refine ⟨section16_unblock (n := n) (m := m) x0, ?_⟩
    simpa [section16_blockLinearMap_unblock] using hnot_top_sum
  simpa using
    (properConvexFunctionOn_sum_of_exists_ne_top
      (f := fun i x => f i (section16_blockLinearMap (n := n) (m := m) i x))
      hproper hexists)

/-- Image of the block projection on the block-sum effective domain. -/
lemma section16_blockLinearMapE_image_effectiveDomain_blockSum_eq {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (i : Fin m) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ j, f j (section16_blockLinearMap (n := n) (m := m) j x)
    (section16_blockLinearMapE (n := n) (m := m) i) ''
        ((fun z : EuclideanSpace ℝ (Fin (m * n)) => (z : Fin (m * n) → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g) =
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
  classical
  intro g
  have hnotbot : ∀ j : Fin m, ∀ x, f j x ≠ (⊥ : EReal) := by
    intro j x
    exact (hf j).2.2 x (by simp)
  have hdom :
      effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
        ⋂ j : Fin m,
          (section16_blockLinearMap (n := n) (m := m) j) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j) := by
    simpa [g] using
      (section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
        (n := n) (m := m) (f := f) hnotbot)
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' :
        (z : Fin (m * n) → ℝ) ∈
          ⋂ j : Fin m,
            (section16_blockLinearMap (n := n) (m := m) j) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j) := by
      have hz'' : (z : Fin (m * n) → ℝ) ∈
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g := hz
      simpa [hdom] using hz''
    have hz_i :
        section16_blockLinearMap (n := n) (m := m) i (z : Fin (m * n) → ℝ) ∈
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      have hz_i' := (Set.mem_iInter.mp hz' i)
      simpa [Set.mem_preimage] using hz_i'
    have hz_i' :
        (section16_blockLinearMapE (n := n) (m := m) i z : Fin n → ℝ) ∈
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      simpa [section16_blockLinearMapE_apply] using hz_i
    simpa using hz_i'
  · intro hy
    have hy' :
        (y : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := hy
    have hdom_ne :
        ∀ j : Fin m, Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) := by
      intro j
      have h :=
        (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
          (S := (Set.univ : Set (Fin n → ℝ))) (f := f j)).1 (hf j)
      exact h.2.1
    classical
    choose x0 hx0 using hdom_ne
    let xBlocks : Fin m → Fin n → ℝ :=
      fun j => if h : j = i then (y : Fin n → ℝ) else x0 j
    let zFun : Fin (m * n) → ℝ := section16_unblock (n := n) (m := m) xBlocks
    let z : EuclideanSpace ℝ (Fin (m * n)) := WithLp.toLp 2 zFun
    have hz_blocks :
        zFun ∈
          ⋂ j : Fin m,
            (section16_blockLinearMap (n := n) (m := m) j) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j) := by
      refine Set.mem_iInter.2 ?_
      intro j
      have hblock :
          section16_blockLinearMap (n := n) (m := m) j zFun = xBlocks j := by
        simpa [zFun] using
          (section16_blockLinearMap_unblock (n := n) (m := m) j xBlocks)
      have hxj :
          xBlocks j ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j) := by
        by_cases hji : j = i
        · subst hji
          simpa [xBlocks] using hy'
        · simpa [xBlocks, hji] using hx0 j
      simpa [Set.mem_preimage, hblock] using hxj
    have hz_fun :
        zFun ∈ effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g := by
      simpa [hdom] using hz_blocks
    have hz_pre :
        z ∈ ((fun z : EuclideanSpace ℝ (Fin (m * n)) => (z : Fin (m * n) → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g) := by
      simpa [z, zFun] using hz_fun
    have hblockE :
        (section16_blockLinearMapE (n := n) (m := m) i z : Fin n → ℝ) = xBlocks i := by
      simpa [section16_blockLinearMapE_apply, z, zFun] using
        (section16_blockLinearMap_unblock (n := n) (m := m) i xBlocks)
    refine ⟨z, hz_pre, ?_⟩
    ext j
    simp [hblockE, xBlocks]

/-- Coercion from `ℝ` to `EReal` commutes with finite sums. -/
lemma section16_sum_coe {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Finset.sum s (fun i => ((f i : ℝ) : EReal)) = ((Finset.sum s f : ℝ) : EReal) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs, EReal.coe_add]

/-- Supremum of pairwise sums in `EReal` splits as the sum of suprema. -/
lemma section16_sSup_image2_add_eq_sSup_add {S T : Set EReal} :
    sSup (Set.image2 (· + ·) S T) = sSup S + sSup T := by
  classical
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨s, hs, t, ht, rfl⟩
    exact add_le_add (le_sSup hs) (le_sSup ht)
  ·
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases (lt_sSup_iff).1 ha with ⟨s, hs, hsa⟩
    rcases (lt_sSup_iff).1 hb with ⟨t, ht, htb⟩
    have hlt : a + b < s + t := EReal.add_lt_add hsa htb
    have hle : s + t ≤ sSup (Set.image2 (· + ·) S T) := by
      exact le_sSup ⟨s, hs, t, ht, rfl⟩
    exact le_of_lt (lt_of_lt_of_le hlt hle)

/-- Support function of a block-sum domain dominates the sum of blockwise support functions. -/
lemma section16_supportFunction_effectiveDomain_blockSum_unblock_ge_sum {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal) (xStar : Fin m → Fin n → ℝ)
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal)) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
    ∑ i : Fin m,
        supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) ≤
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
        (section16_unblock (n := n) (m := m) xStar) := by
  classical
  intro g
  let domi : Fin m → Set (Fin n → ℝ) := fun i =>
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)
  let S : Fin m → Set EReal := fun i =>
    {z : EReal | ∃ x ∈ domi i, z = ((dotProduct x (xStar i) : ℝ) : EReal)}
  let sumSet : Finset (Fin m) → Set EReal := fun s =>
    {z : EReal | ∃ xBlocks : Fin m → Fin n → ℝ,
      (∀ i ∈ s, xBlocks i ∈ domi i) ∧
      z = Finset.sum s (fun i =>
        ((dotProduct (xBlocks i) (xStar i) : ℝ) : EReal))}
  have hsumSet :
      ∀ s : Finset (Fin m), sSup (sumSet s) = Finset.sum s (fun i => sSup (S i)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hsumSet0 : sumSet (∅ : Finset (Fin m)) = ({0} : Set EReal) := by
        ext z
        constructor
        · rintro ⟨xBlocks, _, rfl⟩
          simp
        · intro hz
          rcases hz with rfl
          refine ⟨fun _ => 0, ?_, by simp⟩
          intro i hi
          simp at hi
      simp [hsumSet0]
    · intro i s hi hs
      have hsumSet_ins :
          sumSet (insert i s) = Set.image2 (· + ·) (sumSet s) (S i) := by
        ext z
        constructor
        · rintro ⟨xBlocks, hx, rfl⟩
          have hx_i : xBlocks i ∈ domi i := hx i (by simp)
          have hx_s : ∀ j ∈ s, xBlocks j ∈ domi j := by
            intro j hj
            have hj' : j ∈ insert i s := by
              simp [hj]
            exact hx j hj'
          have hz1 :
              (Finset.sum s
                  (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal))) ∈ sumSet s :=
            ⟨xBlocks, hx_s, rfl⟩
          have hz2 :
              ((dotProduct (xBlocks i) (xStar i) : ℝ) : EReal) ∈ S i :=
            ⟨xBlocks i, hx_i, rfl⟩
          have hsum :
              Finset.sum (insert i s)
                  (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal)) =
                (Finset.sum s
                    (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal))) +
                  ((dotProduct (xBlocks i) (xStar i) : ℝ) : EReal) := by
            simp [Finset.sum_insert, hi, add_comm]
          exact ⟨_, hz1, _, hz2, hsum.symm⟩
        · rintro ⟨z1, hz1, z2, hz2, rfl⟩
          rcases hz1 with ⟨xBlocks, hxBlocks, rfl⟩
          rcases hz2 with ⟨xi, hxi, rfl⟩
          let xBlocks' : Fin m → Fin n → ℝ := fun j => if h : j = i then xi else xBlocks j
          have hxBlocks' : ∀ j ∈ insert i s, xBlocks' j ∈ domi j := by
            intro j hj
            by_cases hji : j = i
            · subst hji
              simp [xBlocks', hxi]
            · have hj' : j ∈ s := by
                simpa [Finset.mem_insert, hji] using hj
              have hxj := hxBlocks j hj'
              simp [xBlocks', hji, hxj]
          have hsum_s :
              Finset.sum s
                  (fun j => ((dotProduct (xBlocks' j) (xStar j) : ℝ) : EReal)) =
                Finset.sum s
                  (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              exact fun hji => hi (by simpa [hji] using hj)
            simp [xBlocks', hji]
          have hxBlocks'i : xBlocks' i = xi := by
            simp [xBlocks']
          have hsum :
              Finset.sum (insert i s)
                  (fun j => ((dotProduct (xBlocks' j) (xStar j) : ℝ) : EReal)) =
                (Finset.sum s
                    (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal))) +
                  ((dotProduct xi (xStar i) : ℝ) : EReal) := by
            calc
              Finset.sum (insert i s)
                  (fun j => ((dotProduct (xBlocks' j) (xStar j) : ℝ) : EReal)) =
                ((dotProduct (xBlocks' i) (xStar i) : ℝ) : EReal) +
                  Finset.sum s
                    (fun j => ((dotProduct (xBlocks' j) (xStar j) : ℝ) : EReal)) := by
                simp [Finset.sum_insert, hi]
              _ =
                ((dotProduct xi (xStar i) : ℝ) : EReal) +
                  Finset.sum s
                    (fun j => ((dotProduct (xBlocks' j) (xStar j) : ℝ) : EReal)) := by
                simp [hxBlocks'i]
              _ =
                ((dotProduct xi (xStar i) : ℝ) : EReal) +
                  Finset.sum s
                    (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal)) := by
                simp [hsum_s]
              _ =
                (Finset.sum s
                    (fun j => ((dotProduct (xBlocks j) (xStar j) : ℝ) : EReal))) +
                  ((dotProduct xi (xStar i) : ℝ) : EReal) := by
                simp [add_comm]
          exact ⟨xBlocks', hxBlocks', hsum.symm⟩
      have hs' : sSup (sumSet s) = Finset.sum s (fun j => sSup (S j)) := hs
      calc
        sSup (sumSet (insert i s)) =
            sSup (Set.image2 (· + ·) (sumSet s) (S i)) := by
              simp [hsumSet_ins]
        _ = sSup (sumSet s) + sSup (S i) := by
              simpa using (section16_sSup_image2_add_eq_sSup_add (S := sumSet s) (T := S i))
        _ = (Finset.sum s (fun j => sSup (S j))) + sSup (S i) := by
              simp [hs']
        _ = Finset.sum (insert i s) (fun j => sSup (S j)) := by
              simp [Finset.sum_insert, hi, add_comm]
  have hsum :
      ∑ i : Fin m,
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) =
        sSup (sumSet (Finset.univ : Finset (Fin m))) := by
    have h := hsumSet (Finset.univ : Finset (Fin m))
    simpa [S, domi, supportFunctionEReal] using h.symm
  have hsubset :
      sumSet (Finset.univ : Finset (Fin m)) ⊆
        {z : EReal |
          ∃ x ∈ effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g,
            z =
              ((dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) : EReal)} := by
    intro z hz
    rcases hz with ⟨xBlocks, hxBlocks, rfl⟩
    have hxBlocks' : ∀ i : Fin m, xBlocks i ∈ domi i := by
      intro i
      exact hxBlocks i (by simp)
    let x : Fin (m * n) → ℝ := section16_unblock (n := n) (m := m) xBlocks
    have hx_dom :
        x ∈ effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g := by
      have hdom :
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹' domi i := by
        simpa [g, domi] using
          (section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
            (n := n) (m := m) (f := f) hnotbot)
      have hx_mem :
          x ∈
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹' domi i := by
        refine Set.mem_iInter.2 ?_
        intro i
        have hblock :
            section16_blockLinearMap (n := n) (m := m) i x = xBlocks i := by
          simpa [x] using
            (section16_blockLinearMap_unblock (n := n) (m := m) i xBlocks)
        have hx_i : xBlocks i ∈ domi i := hxBlocks' i
        simpa [Set.mem_preimage, hblock] using hx_i
      simpa [hdom, domi] using hx_mem
    have hdot :
        dotProduct x (section16_unblock (n := n) (m := m) xStar) =
          ∑ i : Fin m, dotProduct (xBlocks i) (xStar i) := by
      simpa [x, section16_blockLinearMap_unblock] using
        (section16_dotProduct_unblock_eq_sum_blocks (n := n) (m := m)
          (xStar := xStar) (x := x))
    have hsum_coe :
        (∑ i : Fin m, ((dotProduct (xBlocks i) (xStar i) : ℝ) : EReal)) =
          ((∑ i : Fin m, dotProduct (xBlocks i) (xStar i) : ℝ) : EReal) := by
      simpa using
        (section16_sum_coe (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => dotProduct (xBlocks i) (xStar i)))
    refine ⟨x, hx_dom, ?_⟩
    calc
      (∑ i : Fin m, ((dotProduct (xBlocks i) (xStar i) : ℝ) : EReal))
          = ((∑ i : Fin m, dotProduct (xBlocks i) (xStar i) : ℝ) : EReal) := hsum_coe
      _ = ((dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) : EReal) := by
            simp [hdot]
  have hsSup_le :
      sSup (sumSet (Finset.univ : Finset (Fin m))) ≤
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
            (section16_unblock (n := n) (m := m) xStar) := by
    exact sSup_le_sSup hsubset
  simpa [hsum] using hsSup_le

/-- Support function of a block-sum effective domain splits by blocks. -/
lemma section16_supportFunction_effectiveDomain_blockSum_unblock_eq_sum {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal) (xStar : Fin m → Fin n → ℝ)
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal)) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
        (section16_unblock (n := n) (m := m) xStar) =
      ∑ i : Fin m,
        supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) := by
  classical
  intro g
  -- The `≤` direction follows from bounding each block contribution by its own support function.
  refine le_antisymm ?_ ?_
  · unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx' :
        (x : Fin (m * n) → ℝ) ∈
          ⋂ i : Fin m,
            (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      have hdom :
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        simpa [g] using
          (section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
            (n := n) (m := m) (f := f) hnotbot)
      simpa [hdom] using (hx : (x : Fin (m * n) → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
    have hsum_le :
        ((dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) : EReal) ≤
          ∑ i : Fin m,
            supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) := by
      have hsum :
          (dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) =
            ∑ i : Fin m,
              dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) := by
        simpa using
          (section16_dotProduct_unblock_eq_sum_blocks (n := n) (m := m)
            (xStar := xStar) (x := x))
      have hle :
          ∀ i : Fin m,
            ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) : EReal) ≤
              supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) := by
        intro i
        have hx_i :
            section16_blockLinearMap (n := n) (m := m) i (x : Fin (m * n) → ℝ) ∈
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
          have hx_i' := (Set.mem_iInter.mp hx' i)
          simpa [Set.mem_preimage] using hx_i'
        have hle' :
            ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) : EReal) ≤
              sSup
                {z : EReal |
                  ∃ y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i),
                    z = ((dotProduct y (xStar i) : ℝ) : EReal)} :=
          le_sSup ⟨section16_blockLinearMap (n := n) (m := m) i x, hx_i, rfl⟩
        simpa [supportFunctionEReal] using hle'
      have hsumE :
          ((dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) : EReal) =
            ∑ i : Fin m,
              ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) : EReal) := by
        have hsum_coe :
            (∑ i : Fin m,
                ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) :
                  EReal)) =
              ((∑ i : Fin m,
                  dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) :
                EReal) := by
          simpa using
            (section16_sum_coe (s := (Finset.univ : Finset (Fin m)))
              (f := fun i =>
                dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i)))
        calc
          ((dotProduct x (section16_unblock (n := n) (m := m) xStar) : ℝ) : EReal) =
              ((∑ i : Fin m,
                  dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) :
                EReal) := by
            simp [hsum]
          _ = ∑ i : Fin m,
              ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) :
                EReal) := by
            simpa using hsum_coe.symm
      have hsum_le' :
          (∑ i : Fin m,
              ((dotProduct (section16_blockLinearMap (n := n) (m := m) i x) (xStar i) : ℝ) : EReal)) ≤
            ∑ i : Fin m,
              supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) :=
        Finset.sum_le_sum (fun i _ => hle i)
      simpa [hsumE] using hsum_le'
    simpa using hsum_le
  · -- The reverse inequality requires splitting the supremum over independent block choices.
    simpa [g] using
      (section16_supportFunction_effectiveDomain_blockSum_unblock_ge_sum
        (n := n) (m := m) (f := f) (xStar := xStar) (hnotbot := hnotbot))

/-- Recession of the block-sum conjugate splits by blocks at an unblocked covector. -/
lemma section16_recession_blockSum_unblock_eq_sum {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal) (xStar : Fin m → Fin n → ℝ)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
    recessionFunction (fenchelConjugate (m * n) g) (section16_unblock (n := n) (m := m) xStar) =
      ∑ i : Fin m, recessionFunction (fenchelConjugate n (f i)) (xStar i) := by
  classical
  intro g
  have hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
    intro i x
    exact (hf i).2.2 x (by simp)
  have hsupport :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
          (section16_unblock (n := n) (m := m) xStar) =
        ∑ i : Fin m,
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) (xStar i) := by
    simpa [g] using
      (section16_supportFunction_effectiveDomain_blockSum_unblock_eq_sum
        (n := n) (m := m) (f := f) (xStar := xStar) (hnotbot := hnotbot))
  have hg :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → ℝ)) g := by
    simpa [g] using
      (section16_properConvexFunctionOn_blockSum (n := n) (m := m) (f := f) hf)
  have hsupport_g :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g) =
        recessionFunction (fenchelConjugate (m * n) g) := by
    simpa using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := m * n) (f := g)
        (hf := hg) (fStar0_plus := recessionFunction (fenchelConjugate (m * n) g))
        (hfStar0_plus := by intro y; rfl))
  have hsupport_i (i : Fin m) :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) =
        recessionFunction (fenchelConjugate n (f i)) := by
    simpa using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := f i)
        (hf := hf i) (fStar0_plus := recessionFunction (fenchelConjugate n (f i)))
        (hfStar0_plus := by intro y; rfl))
  simpa [hsupport_g, hsupport_i] using hsupport

end Section16
end Chap03
