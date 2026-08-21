/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Mathlib.LinearAlgebra.Projection

import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section02_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section17_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part8

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Text 19.0.1: A set `C ⊆ ℝ^n` is polyhedral convex if there exist vectors `b i` and
scalars `β i` such that `C` is the intersection of finitely many closed half-spaces
`{x | x ⬝ᵥ b i ≤ β i}`. -/
theorem isPolyhedralConvexSet_iff_exists_finite_halfspaces
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C ↔
      ∃ m : ℕ, ∃ (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ),
        C = ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
  constructor
  · intro hpoly
    rcases hpoly with ⟨ι, hfin, b, β, hC⟩
    letI : Fintype ι := hfin
    refine ⟨Fintype.card ι,
      fun j => b ((Fintype.equivFin ι).symm j),
      fun j => β ((Fintype.equivFin ι).symm j), ?_⟩
    calc
      C = ⋂ i : ι, closedHalfSpaceLE n (b i) (β i) := hC
      _ = ⋂ j : Fin (Fintype.card ι),
            closedHalfSpaceLE n (b ((Fintype.equivFin ι).symm j))
              (β ((Fintype.equivFin ι).symm j)) := by
            ext x
            constructor
            · intro hx
              simp at hx ⊢
              intro j
              exact hx ((Fintype.equivFin ι).symm j)
            · intro hx
              simp at hx ⊢
              intro i
              simpa using hx ((Fintype.equivFin ι) i)
  · rintro ⟨m, b, β, hC⟩
    exact ⟨Fin m, inferInstance, b, β, hC⟩

/-- Helper for Text 19.0.2: an equality is equivalent to two weak inequalities. -/
lemma helperForText_19_0_2_eq_iff_le_and_neg_le
    {n : ℕ} {x a : Fin n → ℝ} {α : ℝ} :
    x ⬝ᵥ a = α ↔ (x ⬝ᵥ a ≤ α) ∧ (x ⬝ᵥ (-a) ≤ -α) := by
  constructor
  · intro h
    refine ⟨le_of_eq h, ?_⟩
    have hneg : x ⬝ᵥ (-a) = -α := by
      simp [dotProduct_neg, h]
    exact le_of_eq hneg
  · intro h
    have hle : x ⬝ᵥ a ≤ α := h.1
    have hneg : x ⬝ᵥ (-a) ≤ -α := h.2
    have hneg' : -(x ⬝ᵥ a) ≤ -α := by
      simpa [dotProduct_neg] using hneg
    have hge : α ≤ x ⬝ᵥ a := (neg_le_neg_iff).1 hneg'
    exact le_antisymm hle hge

/-- Helper for Text 19.0.2: rewrite the mixed system as a finite intersection of half-spaces. -/
lemma helperForText_19_0_2_solutionSet_as_iInter_halfspaces
    (n m k : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ)
    (b : Fin k → Fin n → ℝ) (β : Fin k → ℝ) :
    {x : Fin n → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} =
      ⋂ s : Sum (Fin m) (Sum (Fin m) (Fin k)),
        closedHalfSpaceLE n
          (match s with
          | Sum.inl i => a i
          | Sum.inr s' =>
            match s' with
            | Sum.inl i => -a i
            | Sum.inr j => b j)
          (match s with
          | Sum.inl i => α i
          | Sum.inr s' =>
            match s' with
            | Sum.inl i => -α i
            | Sum.inr j => β j) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j) := by
      simpa using hx
    simp [closedHalfSpaceLE]
    refine ⟨?_, ?_⟩
    · intro i
      exact le_of_eq (hx'.1 i)
    · refine ⟨?_, ?_⟩
      · intro i
        exact le_of_eq (hx'.1 i).symm
      · intro j
        exact hx'.2 j
  · intro hx
    have hx' :
        (∀ i, x ⬝ᵥ a i ≤ α i) ∧
          (∀ i, α i ≤ x ⬝ᵥ a i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j) := by
      simpa [closedHalfSpaceLE] using hx
    simp
    refine ⟨?_, ?_⟩
    · intro i
      exact le_antisymm (hx'.1 i) (hx'.2.1 i)
    · intro j
      exact hx'.2.2 j

/-- Text 19.0.2: The solution set in `ℝ^n` of any finite mixed system of linear equations and
weak linear inequalities is a polyhedral convex set. -/
theorem polyhedralConvexSet_solutionSet_linearEq_and_inequalities
    (n m k : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ)
    (b : Fin k → Fin n → ℝ) (β : Fin k → ℝ) :
    IsPolyhedralConvexSet n
      {x : Fin n → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} := by
  let b' : Sum (Fin m) (Sum (Fin m) (Fin k)) → Fin n → ℝ :=
    fun s =>
      match s with
      | Sum.inl i => a i
      | Sum.inr s' =>
        match s' with
        | Sum.inl i => -a i
        | Sum.inr j => b j
  let β' : Sum (Fin m) (Sum (Fin m) (Fin k)) → ℝ :=
    fun s =>
      match s with
      | Sum.inl i => α i
      | Sum.inr s' =>
        match s' with
        | Sum.inl i => -α i
        | Sum.inr j => β j
  refine ⟨Sum (Fin m) (Sum (Fin m) (Fin k)), inferInstance, b', β', ?_⟩
  simpa [b', β'] using
    (helperForText_19_0_2_solutionSet_as_iInter_halfspaces n m k a α b β)

/-- Helper for Text 19.0.3: intersections of homogeneous closed half-spaces are cones. -/
lemma helperForText_19_0_3_isCone_iInter_halfspaces_zero
    (n m : ℕ) (b : Fin m → Fin n → ℝ) :
    IsConeSet n (⋂ i, closedHalfSpaceLE n (b i) (0 : ℝ)) := by
  have hK : ∀ i, IsConeSet n (closedHalfSpaceLE n (b i) (0 : ℝ)) := by
    intro i
    simpa [closedHalfSpaceLE] using (IsConeSet_dotProduct_le_zero n (b i))
  simpa using
    (IsConeSet_iInter_family (n:=n)
      (K:=fun i => closedHalfSpaceLE n (b i) (0 : ℝ)) hK)

/-- Helper for Text 19.0.3: a cone inside half-spaces forces each dot-product to be nonpositive. -/
lemma helperForText_19_0_3_dot_le_zero_of_cone_and_mem_iInter
    {n : ℕ} {ι : Sort*} {C : Set (Fin n → ℝ)}
    {b : ι → Fin n → ℝ} {β : ι → ℝ}
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hcone : IsConeSet n C) :
    ∀ x ∈ C, ∀ i, x ⬝ᵥ b i ≤ 0 := by
  intro x hx i
  by_contra hpos
  have hxpos : 0 < x ⬝ᵥ b i := lt_of_not_ge (by simpa using hpos)
  have hxne : x ⬝ᵥ b i ≠ 0 := ne_of_gt hxpos
  let t : ℝ := (|β i| + 1) / (x ⬝ᵥ b i)
  have htpos : 0 < t := by
    have hnumpos : 0 < |β i| + 1 := by
      have hnonneg : 0 ≤ |β i| := abs_nonneg (β i)
      linarith
    exact div_pos hnumpos hxpos
  have htxC : t • x ∈ C := hcone x hx t htpos
  have htxC' : t • x ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
    simpa [hC] using htxC
  have htxle_all : ∀ j, (t • x) ⬝ᵥ b j ≤ β j := by
    simpa [closedHalfSpaceLE] using htxC'
  have htxle : (t • x) ⬝ᵥ b i ≤ β i := htxle_all i
  have htxdot : (t • x) ⬝ᵥ b i = |β i| + 1 := by
    have hmul : t * (x ⬝ᵥ b i) = |β i| + 1 := by
      dsimp [t]
      field_simp [hxne]
    calc
      (t • x) ⬝ᵥ b i = t * (x ⬝ᵥ b i) := by
        simp [smul_dotProduct]
      _ = |β i| + 1 := hmul
  have hβlt : β i < |β i| + 1 := by
    have hle : β i ≤ |β i| := le_abs_self (β i)
    have hlt : |β i| < |β i| + 1 := by linarith
    exact lt_of_le_of_lt hle hlt
  have hgt : β i < (t • x) ⬝ᵥ b i := by
    simpa [htxdot] using hβlt
  exact (not_le_of_gt hgt) htxle

/-- Helper for Text 19.0.3: a nonempty cone inside half-spaces forces each `β i` to be nonnegative. -/
lemma helperForText_19_0_3_beta_nonneg_of_cone_and_mem_iInter
    {n : ℕ} {ι : Sort*} {C : Set (Fin n → ℝ)}
    {b : ι → Fin n → ℝ} {β : ι → ℝ}
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hCne : C.Nonempty) (hcone : IsConeSet n C) :
    ∀ i, 0 ≤ β i := by
  intro i
  rcases hCne with ⟨x0, hx0⟩
  by_contra hneg
  have hβneg : β i < 0 := lt_of_not_ge (by simpa using hneg)
  have hx0' : x0 ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
    simpa [hC] using hx0
  have hx0le_all : ∀ j, x0 ⬝ᵥ b j ≤ β j := by
    simpa [closedHalfSpaceLE] using hx0'
  have hx0le : x0 ⬝ᵥ b i ≤ β i := hx0le_all i
  have hx0neg : x0 ⬝ᵥ b i < 0 := lt_of_le_of_lt hx0le hβneg
  have hx0ne : x0 ⬝ᵥ b i ≠ 0 := ne_of_lt hx0neg
  let t : ℝ := (β i / (x0 ⬝ᵥ b i)) / 2
  have htpos : 0 < t := by
    have hpos1 : 0 < β i / (x0 ⬝ᵥ b i) := div_pos_of_neg_of_neg hβneg hx0neg
    have hpos2 : 0 < (2 : ℝ) := by norm_num
    exact div_pos hpos1 hpos2
  have htx0C : t • x0 ∈ C := hcone x0 hx0 t htpos
  have htx0C' : t • x0 ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
    simpa [hC] using htx0C
  have htx0le_all : ∀ j, (t • x0) ⬝ᵥ b j ≤ β j := by
    simpa [closedHalfSpaceLE] using htx0C'
  have htx0le : (t • x0) ⬝ᵥ b i ≤ β i := htx0le_all i
  have htx0dot : (t • x0) ⬝ᵥ b i = β i / 2 := by
    have hmul : t * (x0 ⬝ᵥ b i) = β i / 2 := by
      dsimp [t]
      field_simp [hx0ne]
    calc
      (t • x0) ⬝ᵥ b i = t * (x0 ⬝ᵥ b i) := by
        simp [smul_dotProduct]
      _ = β i / 2 := hmul
  have hβlt : β i < β i / 2 := by
    nlinarith [hβneg]
  have hgt : β i < (t • x0) ⬝ᵥ b i := by
    simpa [htx0dot] using hβlt
  exact (not_le_of_gt hgt) htx0le

/-- Helper for Text 19.0.3: homogenize a half-space representation of a nonempty cone. -/
lemma helperForText_19_0_3_homogenize_iInter_halfspaces
    {n : ℕ} {ι : Sort*} {C : Set (Fin n → ℝ)}
    {b : ι → Fin n → ℝ} {β : ι → ℝ}
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hCne : C.Nonempty) (hcone : IsConeSet n C) :
    C = ⋂ i, closedHalfSpaceLE n (b i) (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    have hdot : ∀ i, x ⬝ᵥ b i ≤ 0 :=
      helperForText_19_0_3_dot_le_zero_of_cone_and_mem_iInter
        (hC:=hC) (hcone:=hcone) x hx
    simpa [closedHalfSpaceLE] using hdot
  · intro hx
    have hx' : ∀ i, x ⬝ᵥ b i ≤ 0 := by
      simpa [closedHalfSpaceLE] using hx
    have hβ : ∀ i, 0 ≤ β i :=
      helperForText_19_0_3_beta_nonneg_of_cone_and_mem_iInter
        (hC:=hC) (hCne:=hCne) (hcone:=hcone)
    have hx'' : ∀ i, x ⬝ᵥ b i ≤ β i := by
      intro i
      exact le_trans (hx' i) (hβ i)
    have hxmem : x ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      simpa [closedHalfSpaceLE] using hx''
    simpa [hC] using hxmem

/-- Text 19.0.3: For a polyhedral convex set `C ⊆ ℝ^n`, `C` is a cone iff it is the
intersection of finitely many closed half-spaces whose boundary hyperplanes pass through the
origin (equivalently, the inequalities are homogeneous with `β i = 0`). -/
theorem polyhedralConvexSet_isCone_iff_iInter_halfspaces_through_origin
    (n : ℕ) (C : Set (Fin n → ℝ))
    (hCne : C.Nonempty) :
    IsPolyhedralConvexSet n C →
      (IsConeSet n C ↔
        ∃ m : ℕ, ∃ (b : Fin m → Fin n → ℝ),
          C = ⋂ i, closedHalfSpaceLE n (b i) (0 : ℝ)) := by
  intro hpoly
  constructor
  · intro hcone
    rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hpoly with ⟨m, b, β, hC⟩
    have hC' :
        C = ⋂ i, closedHalfSpaceLE n (b i) (0 : ℝ) :=
      helperForText_19_0_3_homogenize_iInter_halfspaces
        (hC:=hC) (hCne:=hCne) (hcone:=hcone)
    exact ⟨m, b, hC'⟩
  · rintro ⟨m, b, hC⟩
    simpa [hC] using (helperForText_19_0_3_isCone_iInter_halfspaces_zero n m b)

/-- Text 19.0.4: A convex set `C ⊆ ℝ^n` is called finitely generated if it is the mixed convex
hull of finitely many points and directions (Definition 17.0.4). Equivalently, there exist
vectors `a₁, …, a_m` and an integer `k` with `0 ≤ k ≤ m` such that `C` consists exactly of all
vectors of the form `x = λ₁ a₁ + ··· + λ_m a_m` with `λ₁ + ··· + λ_k = 1` and `λ_i ≥ 0` for
`i = 1, …, m`. -/
def IsFinitelyGeneratedConvexSet (n : ℕ) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (S₀ S₁ : Set (Fin n → ℝ)),
    Set.Finite S₀ ∧ Set.Finite S₁ ∧ C = mixedConvexHull (n := n) S₀ S₁

/-- Text 19.0.5: Let `C ⊆ ℝ^n` be a finitely generated convex cone. A finite set
`{a₁, …, a_m}` is called a set of generators of `C` if
`C = {∑ i, λ i • a i | λ i ≥ 0}` (equivalently, `C = convexConeGenerated n (Set.range a)`). -/
def IsGeneratingSetForConvexCone (n m : ℕ) (C : Set (Fin n → ℝ))
    (a : Fin m → Fin n → ℝ) : Prop :=
  C =
    {x : Fin n → ℝ |
      ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ x = ∑ i, lam i • a i}

/-- Text 19.0.6: The unbounded finitely generated convex sets may be regarded as generalized
polytopes having certain vertices at infinity, like the generalized simplices in §17. -/
def IsGeneralizedPolytopeWithVerticesAtInfinity (n : ℕ) (C : Set (Fin n → ℝ)) : Prop :=
  IsFinitelyGeneratedConvexSet n C ∧ ¬ Bornology.IsBounded C

/-- Helper for Text 19.0.7: a face is a subset of its ambient set. -/
lemma helperForText_19_0_7_face_subset
    {n : ℕ} {C F : Set (Fin n → ℝ)} :
    IsFace (𝕜 := ℝ) C F → F ⊆ C := by
  intro hface
  exact hface.2.1

/-- Helper for Text 19.0.7: a face certifies convexity of the ambient set. -/
lemma helperForText_19_0_7_face_convex
    {n : ℕ} {C F : Set (Fin n → ℝ)} :
    IsFace (𝕜 := ℝ) C F → Convex ℝ C := by
  intro hface
  exact hface.1

/-- Helper for Text 19.0.7: a face is an extreme subset of the ambient set. -/
lemma helperForText_19_0_7_face_isExtreme
    {n : ℕ} {C F : Set (Fin n → ℝ)} :
    IsFace (𝕜 := ℝ) C F → IsExtreme ℝ C F := by
  intro hface
  exact hface.2

/-- Helper for Text 19.0.7: polyhedral convex sets are convex. -/
lemma helperForText_19_0_7_polyhedral_isConvex
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C → Convex ℝ C := by
  rintro ⟨ι, _hfin, b, β, rfl⟩
  have hset :
      (⋂ i, closedHalfSpaceLE n (b i) (β i)) =
        {x : Fin n → ℝ | ∀ i, x ⬝ᵥ b i ≤ β i} := by
    ext x
    simp [closedHalfSpaceLE]
  simpa [hset] using (convex_set_of_dotProduct_le (n := n) (b := b) (β := β))

/-- Helper for Text 19.0.7: the empty set is polyhedral convex. -/
lemma helperForText_19_0_7_polyhedral_empty
    (n : ℕ) :
    IsPolyhedralConvexSet n (∅ : Set (Fin n → ℝ)) := by
  refine ⟨Unit, inferInstance, (fun _ => (0 : Fin n → ℝ)), (fun _ => (-1 : ℝ)), ?_⟩
  ext x
  simp [closedHalfSpaceLE]

/-- Helper for Text 19.0.7: a nonempty convex set in `Fin n → ℝ` has a relative interior point. -/
lemma helperForText_19_0_7_exists_mem_euclideanRelativeInterior_fin_of_convex_nonempty
    {n : ℕ} {F : Set (Fin n → ℝ)}
    (hconvF : Convex ℝ F) (hFne : F.Nonempty) :
    ∃ z, z ∈ euclideanRelativeInterior_fin n F := by
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hconvE : Convex ℝ (e.symm '' F) := by
    simpa using hconvF.linear_image e.symm.toLinearMap
  have hFneE : (e.symm '' F).Nonempty := by
    rcases hFne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  rcases euclideanRelativeInterior_nonempty_of_convex_of_nonempty hconvE hFneE with ⟨z, hz⟩
  refine ⟨e z, ?_⟩
  refine (mem_euclideanRelativeInterior_fin_iff (n := n) (C := F) (x := e z)).2 ?_
  simpa using hz

/-- Helper for Text 19.0.7: adding finitely many equality constraints to a finite half-space
representation preserves polyhedrality. -/
lemma helperForText_19_0_7_activeConstraintIntersection_isPolyhedral
    {n m : ℕ} (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ)
    (A : Set (Fin m)) :
    IsPolyhedralConvexSet n
      ((⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j)) ∩
        ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
  classical
  let a : Fin m → Fin n → ℝ := fun i => if i ∈ A then b i else 0
  let α : Fin m → ℝ := fun i => if i ∈ A then β i else 0
  have hset :
      {x : Fin n → ℝ |
          (∀ i, x ⬝ᵥ a i = α i) ∧
            (∀ j, x ⬝ᵥ b j ≤ β j)} =
        ((⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j)) ∩
          ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · refine Set.mem_iInter.2 ?_
        intro j
        have hxj : x ⬝ᵥ b j ≤ β j := hx.2 j
        simpa [closedHalfSpaceLE] using hxj
      · refine Set.mem_iInter.2 ?_
        intro i
        refine Set.mem_iInter.2 ?_
        intro hiA
        have hxi : x ⬝ᵥ a i = α i := hx.1 i
        have hxi' : x ⬝ᵥ b i = β i := by
          simpa [a, α, hiA] using hxi
        simpa using hxi'
    · intro hx
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hiA : i ∈ A
        ·
          have hxi : x ∈ {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
            have hxi' := (Set.mem_iInter.1 hx.2) i
            exact (Set.mem_iInter.1 hxi') hiA
          simpa [a, α, hiA] using hxi
        ·
          simp [a, α, hiA]
      · intro j
        have hxj : x ∈ closedHalfSpaceLE n (b j) (β j) := (Set.mem_iInter.1 hx.1) j
        simpa [closedHalfSpaceLE] using hxj
  have hpoly :
      IsPolyhedralConvexSet n
        {x : Fin n → ℝ |
          (∀ i, x ⬝ᵥ a i = α i) ∧
            (∀ j, x ⬝ᵥ b j ≤ β j)} :=
    polyhedralConvexSet_solutionSet_linearEq_and_inequalities n m m a α b β
  simpa [hset] using hpoly

/-- Helper for Theorem 19.1: polyhedral convex sets are convex. -/
lemma helperForTheorem_19_1_polyhedral_isConvex
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C → Convex ℝ C := by
  rintro ⟨ι, _hfin, b, β, rfl⟩
  have hset :
      (⋂ i, closedHalfSpaceLE n (b i) (β i)) =
        {x : Fin n → ℝ | ∀ i, x ⬝ᵥ b i ≤ β i} := by
    ext x
    simp [closedHalfSpaceLE]
  simpa [hset] using (convex_set_of_dotProduct_le (n := n) (b := b) (β := β))

/-- Helper for Theorem 19.1: polyhedral convex sets are closed. -/
lemma helperForTheorem_19_1_polyhedral_isClosed
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C → IsClosed C := by
  rintro ⟨ι, _hfin, b, β, rfl⟩
  have hclosed : ∀ i : ι, IsClosed (closedHalfSpaceLE n (b i) (β i)) := by
    intro i
    have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ b i := by
      simpa using
        (continuous_id.dotProduct
          (continuous_const : Continuous fun _ : Fin n → ℝ => b i))
    simpa [closedHalfSpaceLE, Set.preimage, Set.mem_Iic] using
      (isClosed_Iic.preimage hcont)
  simpa using (isClosed_iInter hclosed)

/-- Helper for Theorem 19.1: for convex sets, faces coincide with extreme subsets. -/
lemma helperForTheorem_19_1_faces_as_IsExtreme_under_convex
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) :
    {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'} =
      {C' : Set (Fin n → ℝ) | IsExtreme ℝ C C'} := by
  ext C'
  constructor
  · intro hface
    exact hface.2
  · intro hext
    exact ⟨hc, hext⟩

/-- Helper for Theorem 19.1: without convexity the family of faces is empty. -/
lemma helperForTheorem_19_1_faces_empty_of_not_convex
    {n : ℕ} {C : Set (Fin n → ℝ)} (hconv : ¬ Convex ℝ C) :
    {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'} = ∅ := by
  ext C'
  constructor
  · intro hface
    exact (hconv hface.1).elim
  · intro h
    cases h

/-- Helper for Theorem 19.1: a closed nonconvex set has finitely many faces. -/
lemma helperForTheorem_19_1_closed_nonconvex_faces_finite :
    ∃ C : Set (Fin 1 → ℝ),
      IsClosed C ∧
        Set.Finite {C' : Set (Fin 1 → ℝ) | IsFace (𝕜 := ℝ) C C'} ∧
        ¬ IsPolyhedralConvexSet 1 C := by
  classical
  let x0 : Fin 1 → ℝ := fun _ => 0
  let x1 : Fin 1 → ℝ := fun _ => 1
  let C : Set (Fin 1 → ℝ) := ({x0} ∪ {x1})
  have hnotConvex : ¬ Convex ℝ C := by
    intro hconv
    have hx0 : x0 ∈ C := by
      simp [C, x0]
    have hx1 : x1 ∈ C := by
      simp [C, x1]
    have hcoeff : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
      norm_num
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by
      norm_num
    have hmid : ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x1) ∈ C :=
      hconv hx0 hx1 hcoeff hcoeff hsum
    have hmid_val :
        ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x1) =
          (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
      funext i
      simp [x0, x1]
    have hne0 : (1 / 2 : ℝ) ≠ 0 := by
      norm_num
    have hne1 : (1 / 2 : ℝ) ≠ 1 := by
      norm_num
    have hmid_not : (fun _ : Fin 1 => (1 / 2 : ℝ)) ∉ C := by
      intro hmem
      simp [C, x0, x1] at hmem
      rcases hmem with hmem | hmem
      · have h0 := congrArg (fun f => f 0) hmem
        have h0' : (1 / 2 : ℝ) = 0 := by
          simpa [x0, x1] using h0
        exact (hne0 h0')
      · have h1 := congrArg (fun f => f 0) hmem
        have h1' : (1 / 2 : ℝ) = 1 := by
          simpa [x0, x1] using h1
        exact (hne1 h1')
    have hmid' : (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ C := by
      have hmid' := hmid
      rw [hmid_val] at hmid'
      exact hmid'
    exact hmid_not hmid'
  refine ⟨C, ?_, ?_, ?_⟩
  · have hclosed0 : IsClosed ({x0} : Set (Fin 1 → ℝ)) := isClosed_singleton
    have hclosed1 : IsClosed ({x1} : Set (Fin 1 → ℝ)) := isClosed_singleton
    simpa [C] using hclosed0.union hclosed1
  · have hfaces :
        {C' : Set (Fin 1 → ℝ) | IsFace (𝕜 := ℝ) C C'} = ∅ := by
      ext C'
      constructor
      · intro hface
        exact (hnotConvex hface.1).elim
      · intro h
        cases h
    simpa [hfaces] using
      (Set.finite_empty : Set.Finite (∅ : Set (Set (Fin 1 → ℝ))))
  · intro hpoly
    exact hnotConvex (helperForTheorem_19_1_polyhedral_isConvex 1 C hpoly)

/-- Helper for Theorem 19.1: the stated equivalence fails without convexity. -/
lemma helperForTheorem_19_1_counterexample_equiv_false :
    ∃ C : Set (Fin 1 → ℝ),
      IsClosed C ∧
        Set.Finite {C' : Set (Fin 1 → ℝ) | IsFace (𝕜 := ℝ) C C'} ∧
        ¬ (IsPolyhedralConvexSet 1 C ↔
            (IsClosed C ∧
              Set.Finite {C' : Set (Fin 1 → ℝ) | IsFace (𝕜 := ℝ) C C'})) := by
  rcases helperForTheorem_19_1_closed_nonconvex_faces_finite with
    ⟨C, hclosed, hfinite, hnotpoly⟩
  refine ⟨C, hclosed, hfinite, ?_⟩
  intro hEquiv
  have hpoly : IsPolyhedralConvexSet 1 C := (hEquiv.mpr ⟨hclosed, hfinite⟩)
  exact hnotpoly hpoly

/-- Helper for Theorem 19.1: a tight constraint defines a face of a convex set. -/
lemma helperForTheorem_19_1_isFace_of_tightConstraint
    {n : ℕ} {C : Set (Fin n → ℝ)} {b : Fin n → ℝ} {β : ℝ}
    (hC : C ⊆ closedHalfSpaceLE n b β) (hc : Convex ℝ C) :
    IsFace (𝕜 := ℝ) C (C ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) := by
  refine ⟨hc, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hxC y hyC z hzCz hzseg
    have hxle : x ⬝ᵥ b ≤ β := by
      have hxmem : x ∈ closedHalfSpaceLE n b β := hC hxC
      simpa [closedHalfSpaceLE] using hxmem
    have hyle : y ⬝ᵥ b ≤ β := by
      have hymem : y ∈ closedHalfSpaceLE n b β := hC hyC
      simpa [closedHalfSpaceLE] using hymem
    have hzEq : z ⬝ᵥ b = β := hzCz.2
    rcases hzseg with ⟨a, b', ha, hb, hab, hzrepr⟩
    have hzdot :
        z ⬝ᵥ b = a * (x ⬝ᵥ b) + b' * (y ⬝ᵥ b) := by
      calc
        z ⬝ᵥ b = (a • x + b' • y) ⬝ᵥ b := by simpa [hzrepr]
        _ = (a • x) ⬝ᵥ b + (b' • y) ⬝ᵥ b := by
          simpa using (add_dotProduct (a • x) (b' • y) b)
        _ = a * (x ⬝ᵥ b) + b' * (y ⬝ᵥ b) := by
          simp [smul_dotProduct]
    have hcomb :
        a * (x ⬝ᵥ b) + b' * (y ⬝ᵥ b) = β := by
      simpa [hzdot] using hzEq
    have hle1 :
        a * (x ⬝ᵥ b) + b' * (y ⬝ᵥ b) ≤ a * (x ⬝ᵥ b) + b' * β := by
      have hyle' : b' * (y ⬝ᵥ b) ≤ b' * β := by
        exact mul_le_mul_of_nonneg_left hyle (le_of_lt hb)
      linarith
    have hle2 : β ≤ a * (x ⬝ᵥ b) + b' * β := by
      simpa [hcomb] using hle1
    have hle3 : a * β ≤ a * (x ⬝ᵥ b) := by
      have hbeta : β = a * β + b' * β := by
        calc
          β = 1 * β := by simp
          _ = (a + b') * β := by simpa [hab]
          _ = a * β + b' * β := by ring
      have hle2' : a * β + b' * β ≤ a * (x ⬝ᵥ b) + b' * β := by
        calc
          a * β + b' * β = β := by
            symm
            exact hbeta
          _ ≤ a * (x ⬝ᵥ b) + b' * β := hle2
      exact (add_le_add_iff_right (b' * β)).1 hle2'
    have hge : β ≤ x ⬝ᵥ b := by
      exact le_of_mul_le_mul_left hle3 ha
    have hxeq : x ⬝ᵥ b = β := le_antisymm hxle hge
    exact ⟨hxC, hxeq⟩

/-- Helper for Theorem 19.1: a face lies in all tight constraints at a relative interior point. -/
lemma helperForTheorem_19_1_face_subset_iInter_tightConstraints_of_mem_ri
    {n : ℕ} {ι : Type*} [Fintype ι]
    {C F : Set (Fin n → ℝ)} (b : ι → Fin n → ℝ) (β : ι → ℝ)
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hF : IsFace (𝕜 := ℝ) C F) {z : Fin n → ℝ}
    (hzri : z ∈ euclideanRelativeInterior_fin n F) (hzC : z ∈ C) :
    F ⊆ C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i}, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
  intro x hxF
  have hxC : x ∈ C := hF.2.subset hxF
  refine ⟨hxC, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  refine Set.mem_iInter.2 ?_
  intro hi
  have hCi : C ⊆ closedHalfSpaceLE n (b i) (β i) := by
    intro y hy
    have hy' : y ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      simpa [hC] using hy
    exact (Set.mem_iInter.1 hy') i
  have hface_i :
      IsFace (𝕜 := ℝ) C (C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) :=
    helperForTheorem_19_1_isFace_of_tightConstraint (hC := hCi) (hc := hF.1)
  have hzmem : z ∈ C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
    exact ⟨hzC, hi⟩
  have hri :
      (euclideanRelativeInterior_fin n F ∩
        (C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i})).Nonempty := by
    exact ⟨z, ⟨hzri, hzmem⟩⟩
  have hsubset :
      F ⊆ C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i} :=
    subset_of_isFace_of_convex_of_euclideanRelativeInterior_fin_inter
      (C := C) (C' := C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) (D := F) hface_i
      hF.2.subset hri
  have hxmem : x ∈ C ∩ {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := hsubset hxF
  exact hxmem.2

/-- Helper for Theorem 19.1: a relative-interior point lies in the set. -/
lemma helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ euclideanRelativeInterior_fin n C) : x ∈ C := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hxE :
      e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hx
  have hxE' : e.symm x ∈ e.symm '' C :=
    (euclideanRelativeInterior_subset_closure n (e.symm '' C)).1 hxE
  rcases hxE' with ⟨y, hy, hyEq⟩
  have hxy : y = x := by
    exact e.symm.injective hyEq
  simpa [hxy] using hy

/-- Helper for Theorem 19.1: an active-constraint intersection has a relative-interior point whenever the base point lies in the set. -/
lemma helperForTheorem_19_1_mem_euclideanRelativeInterior_fin_activeConstraintIntersection_of_mem
    {n : ℕ} {ι : Type*} [Fintype ι]
    {C : Set (Fin n → ℝ)} (b : ι → Fin n → ℝ) (β : ι → ℝ)
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    {z : Fin n → ℝ} (hzC : z ∈ C) :
    z ∈ euclideanRelativeInterior_fin n
      (C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i}, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
  classical
  let A : Set ι := {i : ι | z ⬝ᵥ b i = β i}
  let D : Set (Fin n → ℝ) :=
    C ∩ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hzD : z ∈ D := by
    refine ⟨hzC, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    refine Set.mem_iInter.2 ?_
    intro hi
    simpa [A] using hi
  have hzD' : e.symm z ∈ e.symm '' D := ⟨z, hzD, rfl⟩
  have hz_aff :
      e.symm z ∈ (affineSpan ℝ (e.symm '' D) : Set (EuclideanSpace ℝ (Fin n))) :=
    subset_affineSpan (k := ℝ) (s := e.symm '' D) hzD'
  have hAffEq :
      ∀ i ∈ A, ∀ y,
        y ∈ affineSpan ℝ (e.symm '' D) → (e y) ⬝ᵥ b i = β i := by
    intro i hiA y hy
    refine affineSpan_induction (k := ℝ) (s := e.symm '' D) (x := y) hy ?_ ?_
    · intro y hyD
      rcases hyD with ⟨x, hxD, rfl⟩
      have hxD' : x ∈ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := hxD.2
      have hxD_i : x ∈ {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
        have hxD_i' := (Set.mem_iInter.1 hxD') i
        have hxD_i'' := (Set.mem_iInter.1 hxD_i') hiA
        exact hxD_i''
      simpa using hxD_i
    · intro c u v w hu hv hw
      have hcalc :
          (e (c • (u -ᵥ v) +ᵥ w)) ⬝ᵥ b i =
            c * ((e u) ⬝ᵥ b i - (e v) ⬝ᵥ b i) + (e w) ⬝ᵥ b i := by
        calc
          (e (c • (u -ᵥ v) +ᵥ w)) ⬝ᵥ b i
              = (c • (e u - e v) + e w) ⬝ᵥ b i := by
                have hmap :
                    e (c • (u -ᵥ v) +ᵥ w) = c • (e u - e v) + e w := by
                  calc
                    e (c • (u -ᵥ v) +ᵥ w) =
                        e (c • (u - v) + w) := by
                          simp [vsub_eq_sub, vadd_eq_add]
                    _ = c • e (u - v) + e w := by
                          simp [map_add, map_smul]
                    _ = c • (e u - e v) + e w := by
                          simp [map_sub]
                simpa [hmap]
          _ = (c • (e u - e v)) ⬝ᵥ b i + (e w) ⬝ᵥ b i := by
                simpa using (add_dotProduct (c • (e u - e v)) (e w) (b i))
          _ = c * ((e u - e v) ⬝ᵥ b i) + (e w) ⬝ᵥ b i := by
                simp [smul_dotProduct]
          _ = c * ((e u) ⬝ᵥ b i - (e v) ⬝ᵥ b i) + (e w) ⬝ᵥ b i := by
                simp [sub_dotProduct]
      calc
        (e (c • (u -ᵥ v) +ᵥ w)) ⬝ᵥ b i
            = c * ((e u) ⬝ᵥ b i - (e v) ⬝ᵥ b i) + (e w) ⬝ᵥ b i := hcalc
        _ = c * (β i - β i) + β i := by
              simp [hu, hv, hw]
        _ = β i := by ring
  have hzriD :
      e.symm z ∈ euclideanRelativeInterior n (e.symm '' D) := by
    have hUopen :
        ∀ i : ι,
          IsOpen
            (if h : z ⬝ᵥ b i = β i then Set.univ
            else {y : EuclideanSpace ℝ (Fin n) | (e y) ⬝ᵥ b i < β i}) := by
      intro i
      by_cases h : z ⬝ᵥ b i = β i
      · simp [h]
      ·
        have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => (e y) ⬝ᵥ b i := by
          simpa using
            (e.continuous.dotProduct
              (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin n) => b i))
        have hopen :
            IsOpen {y : EuclideanSpace ℝ (Fin n) | (e y) ⬝ᵥ b i < β i} := by
          simpa [Set.preimage, Set.mem_Iio] using (isOpen_Iio.preimage hcont)
        simpa [h] using hopen
    let U : Set (EuclideanSpace ℝ (Fin n)) :=
      ⋂ i : ι,
        (if h : z ⬝ᵥ b i = β i then Set.univ
        else {y : EuclideanSpace ℝ (Fin n) | (e y) ⬝ᵥ b i < β i})
    have hUopen' : IsOpen U := by
      refine isOpen_iInter_of_finite ?_
      intro i
      simpa [U] using hUopen i
    have hy0U : e.symm z ∈ U := by
      refine Set.mem_iInter.2 ?_
      intro i
      by_cases h : z ⬝ᵥ b i = β i
      · simp [U, h]
      ·
        have hzle : z ⬝ᵥ b i ≤ β i := by
          have hzC' : z ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
            simpa [hC] using hzC
          have hzCi : z ∈ closedHalfSpaceLE n (b i) (β i) := (Set.mem_iInter.1 hzC') i
          simpa [closedHalfSpaceLE] using hzCi
        have hzlt : z ⬝ᵥ b i < β i := lt_of_le_of_ne hzle h
        have : (e (e.symm z)) ⬝ᵥ b i < β i := by simpa using hzlt
        simpa [U, h] using this
    have hUmem := IsOpen.mem_nhds hUopen' hy0U
    rcases Metric.mem_nhds_iff.mp hUmem with ⟨ε, hε, hball⟩
    let ε2 : ℝ := ε / 2
    have hε2 : 0 < ε2 := by
      dsimp [ε2]
      linarith
    have hball' : Metric.closedBall (e.symm z) ε2 ⊆ U := by
      intro y hy
      have hy' : y ∈ Metric.ball (e.symm z) ε := by
        have hlt : ε2 < ε := by
          dsimp [ε2]
          linarith
        exact (Metric.closedBall_subset_ball hlt) hy
      exact hball hy'
    refine ⟨hz_aff, ε2, hε2, ?_⟩
    intro y hy
    rcases hy with ⟨hyball, hyAff⟩
    have hyU : y ∈ U := by
      have hyball' : y ∈ Metric.closedBall (e.symm z) ε2 := by
        have hball_eq :
            (fun y => e.symm z + y) '' (ε2 • euclideanUnitBall n) =
              Metric.closedBall (e.symm z) ε2 := by
          have hnorm :
              {y | ‖y‖ ≤ ε2} = ε2 • euclideanUnitBall n :=
            euclidean_normBall_eq_smul_unitBall n ε2 (le_of_lt hε2)
          have hclosed :
              Set.image (fun y => e.symm z + y) {y | ‖y‖ ≤ ε2} =
                Metric.closedBall (e.symm z) ε2 := by
            simpa [Metric.closedBall] using
              (euclidean_closedBall_eq_translate_left n (e.symm z) ε2).symm
          calc
            (fun y => e.symm z + y) '' (ε2 • euclideanUnitBall n) =
                (fun y => e.symm z + y) '' {y | ‖y‖ ≤ ε2} := by
                  simp [hnorm]
            _ = Metric.closedBall (e.symm z) ε2 := hclosed
        simpa [hball_eq] using hyball
      exact hball' hyball'
    let x : Fin n → ℝ := e y
    have hxC : x ∈ C := by
      have hx' : x ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
        refine Set.mem_iInter.2 ?_
        intro i
        by_cases hiA : i ∈ A
        ·
          have hEq : (e y) ⬝ᵥ b i = β i := hAffEq i hiA y hyAff
          have hle : (e y) ⬝ᵥ b i ≤ β i := le_of_eq hEq
          simpa [x, closedHalfSpaceLE] using hle
        ·
          have hyUi : y ∈
              (if h : z ⬝ᵥ b i = β i then Set.univ
              else {y : EuclideanSpace ℝ (Fin n) | (e y) ⬝ᵥ b i < β i}) := by
            have hyU' := Set.mem_iInter.1 hyU i
            simpa [U] using hyU'
          have hlt : (e y) ⬝ᵥ b i < β i := by
            have hneq : z ⬝ᵥ b i ≠ β i := by
              intro hEq
              exact hiA (by simpa [A] using hEq)
            simpa [hneq] using hyUi
          have hle : (e y) ⬝ᵥ b i ≤ β i := le_of_lt hlt
          simpa [x, closedHalfSpaceLE] using hle
      simpa [hC, x] using hx'
    have hxEq : x ∈ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
      refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro hiA
      have hEq : (e y) ⬝ᵥ b i = β i := hAffEq i hiA y hyAff
      simpa [x] using hEq
    refine ⟨x, ⟨hxC, hxEq⟩, ?_⟩
    simp [x]
  have hzriD' :
      z ∈ euclideanRelativeInterior_fin n D :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := D) (x := z)).2 hzriD
  simpa [D, A] using hzriD'

/-- Helper for Theorem 19.1: the active-constraint intersection has the given relative interior point. -/
lemma helperForTheorem_19_1_mem_euclideanRelativeInterior_fin_activeConstraintIntersection
    {n : ℕ} {ι : Type*} [Fintype ι]
    {C F : Set (Fin n → ℝ)} (b : ι → Fin n → ℝ) (β : ι → ℝ)
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hF : IsFace (𝕜 := ℝ) C F) {z : Fin n → ℝ}
    (hzri : z ∈ euclideanRelativeInterior_fin n F) (hzC : z ∈ C) :
    z ∈ euclideanRelativeInterior_fin n
      (C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i}, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
  simpa using
    (helperForTheorem_19_1_mem_euclideanRelativeInterior_fin_activeConstraintIntersection_of_mem
      (n := n) (C := C) (b := b) (β := β) hC hzC)

/-- Helper for Theorem 19.1: a face equals the intersection of its tight constraints at a
relative-interior point. -/
lemma helperForTheorem_19_1_face_eq_iInter_tightConstraints_of_mem_ri
    {n : ℕ} {ι : Type*} [Fintype ι]
    {C F : Set (Fin n → ℝ)} (b : ι → Fin n → ℝ) (β : ι → ℝ)
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i))
    (hF : IsFace (𝕜 := ℝ) C F) {z : Fin n → ℝ}
    (hzri : z ∈ euclideanRelativeInterior_fin n F) (hzC : z ∈ C) :
    C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i}, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} ⊆ F := by
  classical
  let D : Set (Fin n → ℝ) :=
    C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i}, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}
  have hDsubset : D ⊆ C := by
    intro x hx
    exact hx.1
  have hzF : z ∈ F :=
    helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
      (n := n) (C := F) (x := z) hzri
  have hzriD : z ∈ euclideanRelativeInterior_fin n D := by
    simpa [D] using
      (helperForTheorem_19_1_mem_euclideanRelativeInterior_fin_activeConstraintIntersection
        (n := n) (C := C) (F := F) (b := b) (β := β) hC hF hzri hzC)
  have hri :
      (euclideanRelativeInterior_fin n D ∩ F).Nonempty := by
    refine ⟨z, ?_⟩
    refine ⟨hzriD, hzF⟩
  have hsubset :
      D ⊆ F :=
    subset_of_isFace_of_convex_of_euclideanRelativeInterior_fin_inter
      (C := C) (C' := F) (D := D) hF hDsubset hri
  intro x hx
  have hxD : x ∈ D := hx
  exact hsubset hxD

/-- Text 19.0.7: Every face of a polyhedral convex set is itself a polyhedral convex set. -/
theorem polyhedralConvexSet_face
    (n : ℕ) (C F : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C →
      IsFace (𝕜 := ℝ) C F →
        Convex ℝ F →
        IsPolyhedralConvexSet n F := by
  intro hpoly hface hconvF
  by_cases hFempty : F = ∅
  · simpa [hFempty] using helperForText_19_0_7_polyhedral_empty n
  ·
    have hFne : F.Nonempty := Set.nonempty_iff_ne_empty.2 hFempty
    rcases
      helperForText_19_0_7_exists_mem_euclideanRelativeInterior_fin_of_convex_nonempty
        (hconvF := hconvF) hFne with ⟨z, hzri⟩
    have hzF : z ∈ F :=
      helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
        (n := n) (C := F) hzri
    have hzC : z ∈ C := hface.2.subset hzF
    rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hpoly with ⟨m, b, β, hC⟩
    let A : Set (Fin m) := {i : Fin m | z ⬝ᵥ b i = β i}
    have hsubset :
        F ⊆ C ∩ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
      simpa [A] using
        (helperForTheorem_19_1_face_subset_iInter_tightConstraints_of_mem_ri
          (n := n) (C := C) (F := F) (b := b) (β := β) hC hface hzri hzC)
    have hsuperset :
        C ∩ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} ⊆ F := by
      simpa [A] using
        (helperForTheorem_19_1_face_eq_iInter_tightConstraints_of_mem_ri
          (n := n) (C := C) (F := F) (b := b) (β := β) hC hface hzri hzC)
    have hEqF :
        F = C ∩ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i} :=
      Set.Subset.antisymm hsubset hsuperset
    have hpolyActive :
        IsPolyhedralConvexSet n
          ((⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j)) ∩
            ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
      exact
        helperForText_19_0_7_activeConstraintIntersection_isPolyhedral
          (n := n) (m := m) b β A
    have hpolyF :
        IsPolyhedralConvexSet n
          (C ∩ ⋂ i ∈ A, {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
      simpa [hC] using hpolyActive
    simpa [hEqF] using hpolyF

/-- Helper for Theorem 19.1: faces of a finite intersection of half-spaces are finite. -/
lemma helperForTheorem_19_1_faces_finite_of_iInter_halfspaces
    {n : ℕ} {ι : Type*} [Fintype ι]
    {C : Set (Fin n → ℝ)} (b : ι → Fin n → ℝ) (β : ι → ℝ)
    (hC : C = ⋂ i, closedHalfSpaceLE n (b i) (β i)) :
    {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F}.Finite := by
  classical
  let activeFinset : (Fin n → ℝ) → Finset ι :=
    fun z => Finset.univ.filter (fun i => z ⬝ᵥ b i = β i)
  let cell : Finset ι → Set (Fin n → ℝ) :=
    fun s => C ∩ ⋂ i ∈ (s : Set ι), {x : Fin n → ℝ | x ⬝ᵥ b i = β i}
  let g : Finset (Finset ι) → Set (Fin n → ℝ) := fun s => ⋃ t ∈ s, cell t
  have hfaces_subset :
      {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F} ⊆ Set.range g := by
    intro F hF
    let S : Set (Finset ι) := (fun z => activeFinset z) '' F
    have hSfinite : S.Finite := by
      have hfin_univ : (Set.univ : Set (Finset ι)).Finite := by
        simpa using (Set.finite_univ : (Set.univ : Set (Finset ι)).Finite)
      exact hfin_univ.subset (by intro t ht; exact Set.mem_univ t)
    rcases hSfinite.exists_finset_coe with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hsubset1 : F ⊆ g s := by
      intro z hzF
      have hzC : z ∈ C := hF.2.subset hzF
      have hzcell : z ∈ cell (activeFinset z) := by
        refine ⟨hzC, ?_⟩
        refine Set.mem_iInter.2 ?_
        intro i
        refine Set.mem_iInter.2 ?_
        intro hi
        have hi' : i ∈ activeFinset z := by
          simpa using hi
        have hi'' := Finset.mem_filter.1 hi'
        have hiEq : z ⬝ᵥ b i = β i := hi''.2
        simpa using hiEq
      have hmemS : activeFinset z ∈ S := ⟨z, hzF, rfl⟩
      have hmems : activeFinset z ∈ s := by
        have : activeFinset z ∈ (↑s : Set (Finset ι)) := by
          simpa [hs] using hmemS
        simpa using this
      refine Set.mem_iUnion.2 ?_
      refine ⟨activeFinset z, ?_⟩
      refine Set.mem_iUnion.2 ?_
      exact ⟨hmems, hzcell⟩
    have hsubset2 : g s ⊆ F := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨t, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨hts, hxt⟩
      have hts' : t ∈ S := by
        have : t ∈ (↑s : Set (Finset ι)) := by
          simpa using hts
        simpa [hs] using this
      rcases hts' with ⟨z, hzF, rfl⟩
      have hzC : z ∈ C := hF.2.subset hzF
      have hset :
          ((activeFinset z : Finset ι) : Set ι) = {i : ι | z ⬝ᵥ b i = β i} := by
        ext i
        simp [activeFinset]
      have hcell :
          cell (activeFinset z) =
            C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i},
              {x : Fin n → ℝ | x ⬝ᵥ b i = β i} := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hxC, hxI⟩
          refine ⟨hxC, ?_⟩
          refine Set.mem_iInter.2 ?_
          intro i
          refine Set.mem_iInter.2 ?_
          intro hi
          have hi' : i ∈ (activeFinset z : Set ι) := by
            simpa [hset] using hi
          have hi'' : i ∈ activeFinset z := by
            simpa using hi'
          have hxI' := (Set.mem_iInter.1 hxI) i
          have hxI'' := (Set.mem_iInter.1 hxI') hi''
          simpa using hxI''
        · intro hx
          rcases hx with ⟨hxC, hxI⟩
          refine ⟨hxC, ?_⟩
          refine Set.mem_iInter.2 ?_
          intro i
          refine Set.mem_iInter.2 ?_
          intro hi
          have hi' : z ⬝ᵥ b i = β i := by
            have hi'' : i ∈ activeFinset z := by
              simpa using hi
            have hi''' := Finset.mem_filter.1 hi''
            exact hi'''.2
          have hxI' := (Set.mem_iInter.1 hxI) i
          have hxI'' := (Set.mem_iInter.1 hxI') hi'
          simpa using hxI''
      have hzri :
          z ∈ euclideanRelativeInterior_fin n (cell (activeFinset z)) := by
        have hzri' :
            z ∈ euclideanRelativeInterior_fin n
              (C ∩ ⋂ i ∈ {i : ι | z ⬝ᵥ b i = β i},
                {x : Fin n → ℝ | x ⬝ᵥ b i = β i}) := by
          exact
            helperForTheorem_19_1_mem_euclideanRelativeInterior_fin_activeConstraintIntersection_of_mem
              (n := n) (C := C) (b := b) (β := β) hC hzC
        simpa [hcell] using hzri'
      have hDsubset : cell (activeFinset z) ⊆ C := by
        intro y hy
        exact hy.1
      have hri :
          (euclideanRelativeInterior_fin n (cell (activeFinset z)) ∩ F).Nonempty := by
        refine ⟨z, ?_⟩
        refine ⟨hzri, hzF⟩
      have hsubset :
          cell (activeFinset z) ⊆ F :=
        subset_of_isFace_of_convex_of_euclideanRelativeInterior_fin_inter
          (C := C) (C' := F) (D := cell (activeFinset z)) hF hDsubset hri
      exact hsubset hxt
    exact Set.Subset.antisymm hsubset2 hsubset1
  have hfinite : (Set.range g).Finite := Set.finite_range g
  exact hfinite.subset hfaces_subset

/-- Helper for Theorem 19.1: polyhedral convex sets are closed and have finitely many faces. -/
lemma helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    IsPolyhedralConvexSet n C →
      (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite) := by
  intro hpoly
  rcases hpoly with ⟨ι, hfin, b, β, hC⟩
  have hpoly' : IsPolyhedralConvexSet n C := ⟨ι, hfin, b, β, hC⟩
  refine ⟨helperForTheorem_19_1_polyhedral_isClosed n C hpoly', ?_⟩
  exact
    helperForTheorem_19_1_faces_finite_of_iInter_halfspaces
      (n := n) (C := C) (b := b) (β := β) hC

/-- Helper for Theorem 19.1: finite faces yield finitely many extreme points. -/
lemma helperForTheorem_19_1_finiteFaces_imp_finite_extremePoints
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) :
    {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F}.Finite →
      Set.Finite {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x} := by
  classical
  intro hfaces
  let f : (Fin n → ℝ) → Set (Fin n → ℝ) := fun x => {x}
  have hm :
      Set.MapsTo f
        {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
        {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F} := by
    intro x hx
    have hface :
        IsFace (𝕜 := ℝ) C ({x} : Set (Fin n → ℝ)) := by
      have hx' : Convex ℝ C ∧ IsExtremePoint (𝕜 := ℝ) C x := by
        exact ⟨hc, hx⟩
      exact
        (isFace_singleton_iff_isExtremePoint (𝕜 := ℝ) (C := C) x).2 hx'
    simpa [f] using hface
  have hinj :
      Set.InjOn f {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x} := by
    intro x hx y hy hxy
    have hxmem : x ∈ ({x} : Set (Fin n → ℝ)) := by
      simp
    have hxmem' : x ∈ ({y} : Set (Fin n → ℝ)) := by
      simpa [f, hxy] using hxmem
    simpa using hxmem'
  exact Set.Finite.of_injOn hm hinj hfaces


end Section19
end Chap19
