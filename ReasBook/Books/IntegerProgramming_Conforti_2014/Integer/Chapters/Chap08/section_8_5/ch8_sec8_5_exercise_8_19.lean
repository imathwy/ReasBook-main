import Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_18

open scoped BigOperators Matrix

-- Domain sampling note:
-- * core/canonical Chapter 8 Benders owners: `benders_residual`,
--   `benders_subproblem_feasible_set`, `benders_feasibility_cone`
-- * core/canonical Chapter 3 ray owner: `IsExtremeRayOfCone`
-- * bridge/view finite-family owner reused from Exercise 8.18:
--   `IsExtremeRayRepresentativeFamily`
-- * core/canonical mathlib finite-index owners: `Fintype.card_pi`, `Fintype.card_sigma`
-- * source-facing owner kept here: the separable Exercise 8.19 Benders reformulation
-- This file therefore keeps only the separable layer and reuses the upstream Benders/extreme-ray
-- API instead of restating it locally.

universe u

section Exercise819

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {s n : ℕ}
variable {rowDim colDim : Fin s → ℕ}

/-- A finite family `points` represents the extreme points of `P` when each listed point is an
extreme point of `P`, different indices represent different points, and every extreme point of
`P` appears in the family. -/
def IsExtremePointRepresentativeFamily
    (P : Set E)
    {q : ℕ}
    (points : Fin q → E) : Prop :=
  (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
    Pairwise (fun k l ↦ points k ≠ points l) ∧
      ∀ x : E, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k

/-- Unfolding `IsExtremePointRepresentativeFamily P points` gives the source-facing extreme-point,
pairwise-distinct-point, and spanning conditions. -/
theorem isExtremePointRepresentativeFamily_iff
    (P : Set E)
    {q : ℕ}
    (points : Fin q → E) :
    IsExtremePointRepresentativeFamily P points ↔
      (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
        Pairwise (fun k l ↦ points k ≠ points l) ∧
          ∀ x : E, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k :=
  Iff.rfl

theorem IsExtremePointRepresentativeFamily.isExtremePoint
    {P : Set E}
    {q : ℕ}
    {points : Fin q → E}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    (k : Fin q) :
    points k ∈ P.extremePoints ℝ :=
  hpoints.1 k

theorem IsExtremePointRepresentativeFamily.ne
    {P : Set E}
    {q : ℕ}
    {points : Fin q → E}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    {k l : Fin q}
    (hkl : k ≠ l) :
    points k ≠ points l :=
  hpoints.2.1 hkl

theorem IsExtremePointRepresentativeFamily.exists_eq
    {P : Set E}
    {q : ℕ}
    {points : Fin q → E}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    {x : E}
    (hx : x ∈ P.extremePoints ℝ) :
    ∃ k : Fin q, x = points k :=
  hpoints.2.2 x hx

/-- The blockwise dual polyhedron
`Q_i = {u^i ≥ 0 | u^i G_i ≥ h^i}` attached to the `i`-th subproblem of (8.32). -/
def separable_benders_dual_polyhedron
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    (i : Fin s) : Set (Fin (rowDim i) → ℝ) :=
  {u | 0 ≤ u ∧ h i ≤ u ᵥ* G i}

/-- Membership in `separable_benders_dual_polyhedron G h i` is exactly the conjunction `u^i ≥ 0`
and `u^i G_i ≥ h^i`. -/
theorem mem_separable_benders_dual_polyhedron_iff
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    (i : Fin s)
    (u : Fin (rowDim i) → ℝ) :
    u ∈ separable_benders_dual_polyhedron G h i ↔ 0 ≤ u ∧ h i ≤ u ᵥ* G i :=
  Iff.rfl

/-- The feasible set of the separable mixed problem (8.32), where the slave variables are the
dependent family `y^i` indexed by the blocks `i`. -/
def separable_benders_original_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :=
  {xy |
    xy.1 ∈ X ∧
      ∀ i : Fin s,
        xy.2 i ∈ benders_subproblem_feasible_set (G i) (benders_residual (A i) (b i) xy.1)}

/-- Membership in `separable_benders_original_feasible_set A G b X` means `x ∈ X` and each block
component `y^i` solves the ordinary Benders subproblem with right-hand side `b^i - A_i x`. -/
theorem mem_separable_benders_original_feasible_set_iff
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :
    xy ∈ separable_benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        ∀ i : Fin s,
          xy.2 i ∈ benders_subproblem_feasible_set (G i) (benders_residual (A i) (b i) xy.1) :=
  Iff.rfl

/-- The separable original feasible set consists of a global master restriction `x ∈ X` together
with blockwise membership in the ordinary Chapter 8 Benders feasible sets. -/
theorem mem_separable_benders_original_feasible_set_iff_forall_mem_benders_original_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :
    xy ∈ separable_benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        ∀ i : Fin s,
          (xy.1, xy.2 i) ∈ benders_original_feasible_set (A i) (G i) (b i) Set.univ := by
  rw [mem_separable_benders_original_feasible_set_iff]
  constructor
  · intro hxy
    refine ⟨hxy.1, ?_⟩
    intro i
    rw [mem_benders_original_feasible_set_iff]
    exact ⟨Set.mem_univ _, hxy.2 i⟩
  · intro hxy
    refine ⟨hxy.1, ?_⟩
    intro i
    have hi :=
      (mem_benders_original_feasible_set_iff (A i) (G i) (b i) Set.univ (xy.1, xy.2 i)).1
        (hxy.2 i)
    exact hi.2

/-- The value `z_I` of the separable mixed problem (8.32), namely the maximum of
`c x + ∑_i h^i y^i` over the blockwise feasible pairs `(x, y)`. -/
noncomputable def separable_benders_original_value
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ) : ℝ :=
  sSup
    ((fun xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ) ↦
        c ⬝ᵥ xy.1 + ∑ i : Fin s, h i ⬝ᵥ xy.2 i) ''
      separable_benders_original_feasible_set A G b X)

/-- The feasible set of the reformulation from Exercise 8.19(i), with one scalar `η_i` for each
block and with optimality and feasibility cuts indexed by the extreme points and extreme rays of
the corresponding block dual systems. -/
def separable_benders_master_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ) :
    Set ((Fin n → ℝ) × (Fin s → ℝ)) :=
  {xη |
    xη.1 ∈ X ∧
      (∀ i : Fin s, ∀ k : Fin (qK i), xη.2 i ≤ u i k ⬝ᵥ benders_residual (A i) (b i) xη.1) ∧
      ∀ i : Fin s, ∀ j : Fin (qJ i), 0 ≤ r i j ⬝ᵥ benders_residual (A i) (b i) xη.1}

/-- Membership in `separable_benders_master_feasible_set A b X u r` means satisfying the master
restriction `x ∈ X`, every blockwise optimality cut, and every blockwise feasibility cut. -/
theorem mem_separable_benders_master_feasible_set_iff
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (xη : (Fin n → ℝ) × (Fin s → ℝ)) :
    xη ∈ separable_benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        (∀ i : Fin s, ∀ k : Fin (qK i),
          xη.2 i ≤ u i k ⬝ᵥ benders_residual (A i) (b i) xη.1) ∧
        ∀ i : Fin s, ∀ j : Fin (qJ i),
          0 ≤ r i j ⬝ᵥ benders_residual (A i) (b i) xη.1 :=
  Iff.rfl

/-- The separable master feasible set consists of a global master restriction `x ∈ X` together
with blockwise membership in the ordinary Benders master feasible sets. -/
theorem mem_separable_benders_master_feasible_set_iff_forall_mem_benders_master_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (xη : (Fin n → ℝ) × (Fin s → ℝ)) :
    xη ∈ separable_benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        ∀ i : Fin s,
          (xη.1, xη.2 i) ∈ benders_master_feasible_set (A i) (b i) Set.univ (u i) (r i) := by
  rw [mem_separable_benders_master_feasible_set_iff]
  constructor
  · intro hxη
    refine ⟨hxη.1, ?_⟩
    intro i
    rw [mem_benders_master_feasible_set_iff]
    exact ⟨Set.mem_univ _, hxη.2.1 i, hxη.2.2 i⟩
  · intro hxη
    refine ⟨hxη.1, ?_, ?_⟩
    · intro i k
      have hi :=
        (mem_benders_master_feasible_set_iff
          (A i)
          (b i)
          Set.univ
          (u i)
          (r i)
          (xη.1, xη.2 i)).1
          (hxη.2 i)
      exact hi.2.1 k
    · intro i j
      have hi :=
        (mem_benders_master_feasible_set_iff
          (A i)
          (b i)
          Set.univ
          (u i)
          (r i)
          (xη.1, xη.2 i)).1
          (hxη.2 i)
      exact hi.2.2 j

/-- The value of the separable reformulation from Exercise 8.19(i), namely the maximum of
`c x + ∑_i η_i` over the blockwise master feasible pairs `(x, η)`. -/
noncomputable def separable_benders_master_value
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  sSup
    ((fun xη : (Fin n → ℝ) × (Fin s → ℝ) ↦
        c ⬝ᵥ xη.1 + ∑ i : Fin s, xη.2 i) ''
      separable_benders_master_feasible_set A b X u r)

/-- Exercise 8.19 (1). For the separable mixed problem
`z_I := max (c x + ∑_i h^i y^i)` subject to `A_i x + G_i y^i ≤ b^i`, `x ∈ X`, and
`y^i ∈ ℝ_+^{p_i}`, if for each block `i` the family `u i` represents the extreme points of the
dual polyhedron `Q_i = {u^i ≥ 0 | u^i G_i ≥ h^i}` and the family `r i` represents the extreme
rays of the cone `C_i = {u^i ≥ 0 | u^i G_i ≥ 0}`, then the problem can be reformulated as the
master problem maximizing `c x + ∑_i η_i` over `x ∈ X`, `η ∈ ℝ^s`, and the blockwise optimality
and feasibility cuts
`η_i ≤ u^{ik}(b^i - A_i x)` and `r^{ij}(b^i - A_i x) ≥ 0`. -/
theorem separable_benders_original_value_eq_master_value_of_extreme_families
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (hpoints :
      ∀ i : Fin s,
        IsExtremePointRepresentativeFamily (separable_benders_dual_polyhedron G h i) (u i))
    (hrays :
      ∀ i : Fin s,
        IsExtremeRayRepresentativeFamily (benders_feasibility_cone (G i)) (r i)) :
    separable_benders_original_value A G b X c h =
      separable_benders_master_value A b X u r c := sorry

/-- Exercise 8.19 (2). In the standard Benders reformulation of (8.32), the optimality-cut index
set `K` is the product of the blockwise extreme-point index sets `K_i`; therefore its cardinality
is the product of the cardinalities of the `K_i`. -/
theorem card_separable_benders_optimality_index
    (qK : Fin s → ℕ) :
    Fintype.card ((i : Fin s) → Fin (qK i)) = ∏ i : Fin s, qK i := by
  rw [Fintype.card_pi]
  simp

/-- Exercise 8.19 (3). In the standard Benders reformulation of (8.32), the feasibility-cut
index set `J` is the disjoint sum of the blockwise extreme-ray index sets `J_i`; therefore its
cardinality is the sum of the cardinalities of the `J_i`. -/
theorem card_separable_benders_feasibility_index
    (qJ : Fin s → ℕ) :
    Fintype.card (Σ i : Fin s, Fin (qJ i)) = ∑ i : Fin s, qJ i := by
  rw [Fintype.card_sigma]
  simp

end Exercise819
