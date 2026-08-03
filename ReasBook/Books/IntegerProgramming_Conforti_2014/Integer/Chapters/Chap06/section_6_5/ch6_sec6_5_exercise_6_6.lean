import Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_corollary_3_47
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open scoped BigOperators Matrix

-- Semantic recall note: `closedConvexHull` is the mathlib owner for the source's closed convex
-- hull, while Chapter 6.2 Example 6.8 and Remark 6.6 model `P(B)` via the image of the
-- nonnegative ray-coordinate orthant under `IntersectionCut.corner_point`.

noncomputable section

section Exercise66

variable {n p k : ℕ}

/-- The corner relaxation `P(B)` determined by `xbar` and `rays`, viewed in the ambient space as
the image of the nonnegative ray-coordinate orthant under `corner_point`. -/
def exercise_6_6_corner_relaxation
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  IntersectionCut.corner_point xbar rays '' {coeffs | ∀ j : Fin k, 0 ≤ coeffs j}

/-- Membership in `exercise_6_6_corner_relaxation xbar rays` means that the ambient point is
represented by a nonnegative ray-coordinate vector. -/
theorem mem_exercise_6_6_corner_relaxation_iff
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) :
    x ∈ exercise_6_6_corner_relaxation xbar rays ↔
      ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          IntersectionCut.corner_point xbar rays coeffs = x := by
  constructor
  · rintro ⟨coeffs, hcoeffs, hpoint⟩
    exact ⟨coeffs, hcoeffs, hpoint⟩
  · rintro ⟨coeffs, hcoeffs, hpoint⟩
    exact ⟨coeffs, hcoeffs, hpoint⟩

/-- The set `Q`, namely the closed convex hull of the points of `P(B)` lying outside
`interior C`. -/
def exercise_6_6_q
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  closedConvexHull ℝ (exercise_6_6_corner_relaxation xbar rays \ interior C)

/-- `exercise_6_6_q C xbar rays` is the closed convex hull of
`exercise_6_6_corner_relaxation xbar rays \ interior C`. -/
theorem exercise_6_6_q_def
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    exercise_6_6_q C xbar rays =
      closedConvexHull ℝ
        (exercise_6_6_corner_relaxation xbar rays \ interior C) := rfl

/-- The points of `P(B)` satisfying the intersection cut defined by `C`, expressed through a
representing nonnegative ray-coordinate vector. -/
def exercise_6_6_points_satisfying_intersection_cut
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  IntersectionCut.corner_point xbar rays ''
    {coeffs | (∀ j : Fin k, 0 ≤ coeffs j) ∧
      1 ≤ IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs}

/-- Membership in `exercise_6_6_points_satisfying_intersection_cut C xbar rays` is exactly
the existence of a nonnegative ray-coordinate representation satisfying the intersection-cut
inequality. -/
theorem mem_exercise_6_6_points_satisfying_intersection_cut_iff
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) :
    x ∈ exercise_6_6_points_satisfying_intersection_cut C xbar rays ↔
      ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            IntersectionCut.corner_point xbar rays coeffs = x := by
  change
    (∃ coeffs : Fin k → ℝ,
      coeffs ∈ {coeffs | (∀ j : Fin k, 0 ≤ coeffs j) ∧
        1 ≤ IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs} ∧
        IntersectionCut.corner_point xbar rays coeffs = x) ↔
      ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            IntersectionCut.corner_point xbar rays coeffs = x
  constructor
  · rintro ⟨coeffs, ⟨hcoeffs, hineq⟩, hpoint⟩
    exact ⟨coeffs, hcoeffs, hineq, hpoint⟩
  · rintro ⟨coeffs, hcoeffs, hineq, hpoint⟩
    exact ⟨coeffs, ⟨hcoeffs, hineq⟩, hpoint⟩

/-- Helper for Exercise 6.6: if a nonnegative coefficient vector satisfies the strict inequality
`intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1`, then the corresponding corner point lies in
`interior C`. -/
lemma cornerPoint_memInterior_of_cut_lt_one
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    {coeffs : Fin k → ℝ}
    (hcoeffs_nonneg : ∀ j : Fin k, 0 ≤ coeffs j)
    (hcut_lt : IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1) :
    IntersectionCut.corner_point xbar rays coeffs ∈ interior C := by
  rcases IntersectionCut.existsAdmissibleParametersWithStrictWeightSum
      C xbar rays coeffs hxbar_mem hcoeffs_nonneg hcut_lt with
    ⟨t, ht, hweight_sum_lt_one⟩
  -- Rewrite the corner point into the weighted affine normal form used in Theorem 6.5.
  rw [IntersectionCut.cornerPoint_eq_weightedAdmissibleCombination xbar rays coeffs t
    (fun j ↦ ne_of_gt (ht j).1)]
  -- The normalized admissible points lie in `C`, so the convexity/interior lemma applies.
  refine IntersectionCut.weightedCombination_memInterior_of_sum_lt_one
    C xbar hC_convex hxbar_mem
    (fun j : Fin k ↦ coeffs j / t j)
    (fun j : Fin k ↦ xbar + t j • rays j) ?_ hweight_sum_lt_one ?_
  · intro j
    exact div_nonneg (hcoeffs_nonneg j) (ht j).1.le
  · intro j
    exact (ht j).2

/-- Helper for Exercise 6.6: the ambient points that satisfy the intersection cut form a convex
set. -/
lemma exercise_6_6_cutRegion_convex
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Convex ℝ (exercise_6_6_points_satisfying_intersection_cut C xbar rays) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  refine ⟨a • u + b • v, ?_, ?_⟩
  · constructor
    · intro j
      -- Nonnegativity is preserved by convex interpolation in coefficient space.
      simpa [Pi.smul_apply] using
        add_nonneg (mul_nonneg ha (hu.1 j)) (mul_nonneg hb (hv.1 j))
    · have hdot :
          IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ (a • u + b • v) =
            a * (IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ u) +
              b * (IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ v) := by
        calc
          ∑ i : Fin k,
              IntersectionCut.intersection_cut_coeff C xbar rays i *
                ((a • u + b • v) i) =
              ∑ i : Fin k,
                (a * (IntersectionCut.intersection_cut_coeff C xbar rays i * u i) +
                  b * (IntersectionCut.intersection_cut_coeff C xbar rays i * v i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp [Pi.smul_apply]
                    ring
          _ = a * (IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ u) +
                b * (IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ v) := by
                  simp [dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_comm,
                    mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      rw [hdot]
      nlinarith [hu.2, hv.2]
  · -- `corner_point` is affine in the ray coefficients, so convex interpolation commutes with it.
    ext i
    have hsum :
        ∑ j : Fin k, (a * u j + b * v j) * rays j i =
          a * ∑ j : Fin k, u j * rays j i + b * ∑ j : Fin k, v j * rays j i := by
      calc
        ∑ j : Fin k, (a * u j + b * v j) * rays j i =
            ∑ j : Fin k, (a * (u j * rays j i) + b * (v j * rays j i)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
        _ = a * ∑ j : Fin k, u j * rays j i + b * ∑ j : Fin k, v j * rays j i := by
              simp [Finset.mul_sum, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
    have hxbar_split : xbar i = (a + b) * xbar i := by
      simpa using congrArg (fun t : ℝ ↦ t * xbar i) hab.symm
    calc
      IntersectionCut.corner_point xbar rays (a • u + b • v) i =
          xbar i + ∑ j : Fin k, (a * u j + b * v j) * rays j i := by
            simp [IntersectionCut.corner_point_def, Pi.smul_apply, mul_comm, mul_left_comm,
              mul_assoc, add_comm, add_left_comm, add_assoc]
      _ = xbar i + (a * ∑ j : Fin k, u j * rays j i + b * ∑ j : Fin k, v j * rays j i) := by
            rw [hsum]
      _ = (a + b) * xbar i +
            (a * ∑ j : Fin k, u j * rays j i + b * ∑ j : Fin k, v j * rays j i) := by
              conv_lhs => rw [hxbar_split]
      _ = a * (xbar i + ∑ j : Fin k, u j * rays j i) +
            b * (xbar i + ∑ j : Fin k, v j * rays j i) := by
              ring
      _ = (a • IntersectionCut.corner_point xbar rays u +
            b • IntersectionCut.corner_point xbar rays v) i := by
              simp [IntersectionCut.corner_point_def, Pi.smul_apply]
              ring

/-- Helper for Exercise 6.6: every generator of `P(B) \\ interior C` already satisfies the
intersection cut. -/
lemma exercise_6_6_generators_subset_cutRegion
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C) :
    exercise_6_6_corner_relaxation xbar rays \ interior C ⊆
      exercise_6_6_points_satisfying_intersection_cut C xbar rays := by
  intro x hx
  rcases hx with ⟨hx_relax, hx_not_mem_interior⟩
  rcases (mem_exercise_6_6_corner_relaxation_iff xbar rays x).mp hx_relax with
    ⟨coeffs, hcoeffs_nonneg, rfl⟩
  refine (mem_exercise_6_6_points_satisfying_intersection_cut_iff C xbar rays _).2 ?_
  refine ⟨coeffs, hcoeffs_nonneg, ?_, rfl⟩
  by_contra hcut
  have hcut_lt :
      IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1 := lt_of_not_ge hcut
  have hinterior :=
    cornerPoint_memInterior_of_cut_lt_one
      C xbar rays hC_convex hxbar_mem hcoeffs_nonneg hcut_lt
  exact hx_not_mem_interior hinterior

/-- Helper for Exercise 6.6: the ambient-coordinate block of the slack system whose projection
recovers the cut region. -/
def exercise_6_6_cutSystemA : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of <| Matrix.vecCons 0 (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Helper for Exercise 6.6: the coefficient-and-slack block of the linear system whose
projection recovers the cut region. -/
def exercise_6_6_cutSystemB
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (k + 1)) ℝ :=
  let γ := IntersectionCut.intersection_cut_coeff C xbar rays
  let tailRows : Fin n → Fin (k + 1) → ℝ := fun i ↦
    Matrix.vecCons 0 (fun j ↦ -(rays j i))
  Matrix.of <| Matrix.vecCons (Matrix.vecCons (-1) γ) tailRows

/-- Helper for Exercise 6.6: the right-hand side vector of the slack system that encodes the cut
region. -/
def exercise_6_6_cutSystemb
    (xbar : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Matrix.vecCons 1 xbar

/-- Helper for Exercise 6.6: multiplying the ambient-coordinate block by `x` just inserts the
cut row `0` above the identity block. -/
lemma exercise_6_6_cutSystemA_mulVec
    (x : Fin n → ℝ) :
    exercise_6_6_cutSystemA *ᵥ x = Matrix.vecCons 0 x := by
  -- The first row is zero, and the remaining rows are the identity block.
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [exercise_6_6_cutSystemA, Matrix.mulVec, dotProduct]
  · intro i
    change ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) i = x i
    simpa using congrArg (fun v : Fin n → ℝ ↦ v i) (Matrix.one_mulVec x)

/-- Helper for Exercise 6.6: multiplying the slack-system coefficient block by
`Matrix.vecCons s coeffs` isolates the cut equation in the first row and the ray expansion in the
remaining rows. -/
lemma exercise_6_6_cutSystemB_mulVec
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (s : ℝ)
    (coeffs : Fin k → ℝ) :
    exercise_6_6_cutSystemB C xbar rays *ᵥ Matrix.vecCons s coeffs =
      Matrix.vecCons
        (-s + IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs)
        (fun i ↦ -∑ j : Fin k, coeffs j * rays j i) := by
  -- Split off the cut row from the ambient-coordinate rows.
  rw [exercise_6_6_cutSystemB, Matrix.cons_mulVec]
  ext i
  refine Fin.cases ?_ ?_ i
  · have hhead :=
        Matrix.dotProduct_cons (Matrix.vecCons s coeffs) (-1)
          (IntersectionCut.intersection_cut_coeff C xbar rays)
    simpa [dotProduct, mul_comm, mul_left_comm, mul_assoc] using hhead
  · intro i
    rw [Matrix.mulVec_cons]
    simp [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 6.6: a slack variable rewrites the cut region as the projection of a
linear system with nonnegative auxiliary variables. -/
lemma exercise_6_6_cutRegion_eq_projection_of_slackSystem
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    exercise_6_6_points_satisfying_intersection_cut C xbar rays =
      Prod.fst '' {xz : (Fin n → ℝ) × (Fin (k + 1) → ℝ) |
        exercise_6_6_cutSystemA *ᵥ xz.1 +
            exercise_6_6_cutSystemB C xbar rays *ᵥ xz.2 =
          exercise_6_6_cutSystemb xbar ∧
          0 ≤ xz.2} := by
  ext x
  rw [mem_exercise_6_6_points_satisfying_intersection_cut_iff C xbar rays x, mem_image_fst_iff]
  constructor
  · rintro ⟨coeffs, hcoeffs_nonneg, hcut, hpoint⟩
    let s : ℝ := IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs - 1
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      linarith
    refine ⟨Matrix.vecCons s coeffs, ?_⟩
    constructor
    · -- The slack row records the cut inequality, and the remaining rows record `x = corner_point`.
      rw [exercise_6_6_cutSystemA_mulVec, exercise_6_6_cutSystemB_mulVec, exercise_6_6_cutSystemb]
      ext i
      refine Fin.cases ?_ ?_ i
      · dsimp [s]
        ring
      · intro i
        have hxcoord :
            xbar i + ∑ j : Fin k, coeffs j * rays j i = x i := by
          simpa [IntersectionCut.corner_point_def] using congrArg (fun v : Fin n → ℝ ↦ v i) hpoint
        calc
          x i + -∑ j : Fin k, coeffs j * rays j i =
              (xbar i + ∑ j : Fin k, coeffs j * rays j i) + -∑ j : Fin k, coeffs j * rays j i := by
                rw [hxcoord]
          _ = xbar i := by
                ring
    · -- Nonnegativity is exactly the original coefficient nonnegativity plus the slack variable.
      intro i
      refine Fin.cases hs_nonneg ?_ i
      intro j
      exact hcoeffs_nonneg j
  · rintro ⟨z, hz_eq, hz_nonneg⟩
    let s : ℝ := Matrix.vecHead z
    let coeffs : Fin k → ℝ := Matrix.vecTail z
    have hz_split : Matrix.vecCons s coeffs = z := by
      -- Every auxiliary vector splits into its head slack entry and tail coefficient vector.
      ext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        rfl
    have hz_eq' := hz_eq
    rw [← hz_split, exercise_6_6_cutSystemA_mulVec, exercise_6_6_cutSystemB_mulVec,
      exercise_6_6_cutSystemb] at hz_eq'
    have hs_nonneg : 0 ≤ s := by
      simpa [s] using hz_nonneg 0
    have hcoeffs_nonneg : ∀ j : Fin k, 0 ≤ coeffs j := by
      intro j
      simpa [coeffs] using hz_nonneg j.succ
    have hcut_eq :
        -s + IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs = 1 := by
      have hhead := congrArg (fun v : Fin (n + 1) → ℝ ↦ v 0) hz_eq'
      simpa using hhead
    have hcut_ge :
        1 ≤ IntersectionCut.intersection_cut_coeff C xbar rays ⬝ᵥ coeffs := by
      linarith
    have hpoint : IntersectionCut.corner_point xbar rays coeffs = x := by
      -- The ambient-coordinate rows of the slack system recover the original point.
      ext i
      have hcoord :
          x i + -∑ j : Fin k, coeffs j * rays j i = xbar i := by
        have htail := congrArg (fun v : Fin (n + 1) → ℝ ↦ v i.succ) hz_eq'
        simpa using htail
      calc
        IntersectionCut.corner_point xbar rays coeffs i =
            xbar i + ∑ j : Fin k, coeffs j * rays j i := by
              simp [IntersectionCut.corner_point_def]
        _ = (x i + -∑ j : Fin k, coeffs j * rays j i) +
              ∑ j : Fin k, coeffs j * rays j i := by
                rw [hcoord]
        _ = x i := by
              ring
    exact ⟨coeffs, hcoeffs_nonneg, hcut_ge, hpoint⟩

/-- Helper for Exercise 6.6: the points satisfying the intersection cut form a closed set because
they are the projection of a linear system with nonnegative slack variables. -/
lemma exercise_6_6_cutRegion_closed
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    IsClosed (exercise_6_6_points_satisfying_intersection_cut C xbar rays) := by
  rw [exercise_6_6_cutRegion_eq_projection_of_slackSystem C xbar rays,
    polyhedron_x_projection_image_eq_forall_nonneg_multipliers
      exercise_6_6_cutSystemA
      (exercise_6_6_cutSystemB C xbar rays)
      (exercise_6_6_cutSystemb xbar)]
  -- The multiplier description is an intersection of closed half-spaces.
  let S : (Fin (n + 1) → ℝ) → Set (Fin n → ℝ) := fun u ↦
    {x : Fin n → ℝ |
      0 ≤ u ᵥ* exercise_6_6_cutSystemB C xbar rays →
        u ⬝ᵥ (exercise_6_6_cutSystemA *ᵥ x) ≤
          u ⬝ᵥ exercise_6_6_cutSystemb xbar}
  have hS_eq :
      {x : Fin n → ℝ |
        ∀ u : Fin (n + 1) → ℝ,
          0 ≤ u ᵥ* exercise_6_6_cutSystemB C xbar rays →
            u ⬝ᵥ (exercise_6_6_cutSystemA *ᵥ x) ≤
              u ⬝ᵥ exercise_6_6_cutSystemb xbar} =
        ⋂ u : Fin (n + 1) → ℝ, S u := by
    ext x
    simp [S]
  rw [hS_eq]
  refine isClosed_iInter fun (u : Fin (n + 1) → ℝ) ↦ ?_
  by_cases hu : 0 ≤ u ᵥ* exercise_6_6_cutSystemB C xbar rays
  · have hset :
        S u =
          {x : Fin n → ℝ |
            u ⬝ᵥ (exercise_6_6_cutSystemA *ᵥ x) ≤
              u ⬝ᵥ exercise_6_6_cutSystemb xbar} := by
        ext x
        simp [S, hu]
    rw [hset]
    exact isClosed_le (by continuity) continuous_const
  · have hset : S u = Set.univ := by
        ext x
        simp [S, hu]
    rw [hset]
    exact isClosed_univ

/-- Exercise 6.6. Let `C ⊆ ℝ^n` be a closed convex set whose interior contains `xbar` but no
point of `ℤ^p × ℝ^(n - p)`. Let `Q` be the closed convex hull of `P(B) \ interior C`. Then `Q`
is exactly the set of points of `P(B)` satisfying the intersection cut defined by `C`. -/
theorem exercise_6_6_q_eq_points_satisfying_intersection_cut
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free :
      Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    exercise_6_6_q C xbar rays =
      exercise_6_6_points_satisfying_intersection_cut C xbar rays := by
  let _ := hpn
  let _ := hC_closed
  let _ := hC_lattice_free
  have hgenerators :
      exercise_6_6_corner_relaxation xbar rays \ interior C ⊆
        exercise_6_6_points_satisfying_intersection_cut C xbar rays :=
    exercise_6_6_generators_subset_cutRegion C xbar rays hC_convex hxbar_mem
  have hcut_convex :
      Convex ℝ (exercise_6_6_points_satisfying_intersection_cut C xbar rays) :=
    exercise_6_6_cutRegion_convex C xbar rays
  have hcut_closed :
      IsClosed (exercise_6_6_points_satisfying_intersection_cut C xbar rays) :=
    exercise_6_6_cutRegion_closed C xbar rays
  have hq_subset_cut :
      exercise_6_6_q C xbar rays ⊆
        exercise_6_6_points_satisfying_intersection_cut C xbar rays := by
    -- The cut region is a closed convex superset of the outside generators, so the closed convex
    -- hull defining `Q` lies inside it.
    simpa [exercise_6_6_q_def] using
      (closedConvexHull_min hgenerators hcut_convex hcut_closed)
  refine Set.Subset.antisymm hq_subset_cut ?_
  -- Route correction: the forward inclusion now runs through the slack-system projection and
  -- Corollary 3.47; the remaining blocker is the coefficient-space closed-convex-hull
  -- decomposition needed for the reverse inclusion.
  -- TODO: show that every cut-feasible coefficient vector lies in the closed convex hull of the
  -- coefficient vectors whose corner points avoid `interior C`, then transport that hull through
  -- `IntersectionCut.corner_point`.
  sorry

end Exercise66
