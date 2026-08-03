import Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_2
import Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15

open scoped BigOperators Matrix Pointwise

-- Semantic recall note: `ch6_sec6_1_lemma_6_2` keeps the tableau relaxation as the source-facing
-- owner and exposes the Chapter 3 polyhedron API through the canonical `Fin`-coordinate bridge
-- `finCoordinateSet`. This file reuses that bridge and keeps only the corner-relaxation geometry
-- specific to Remark 6.1.

section Remark61

variable {B N : Type}

section Rays

/-- The tableau ray `r̄^j` attached to the nonbasic index `j`. -/
noncomputable def corner_ray
    (abar : B → N → ℝ)
    (j : N) : Sum B N → ℝ :=
  Sum.elim (fun i ↦ -abar i j) <|
    let _ : DecidableEq N := Classical.decEq N
    Pi.single j (1 : ℝ)

/-- On a basic coordinate `i ∈ B`, the ray `corner_ray abar j` has value `-abar i j`. -/
@[simp] theorem corner_ray_apply_inl
    (abar : B → N → ℝ)
    (j : N)
    (i : B) :
    corner_ray abar j (Sum.inl i) = -abar i j :=
  rfl

/-- On the distinguished nonbasic coordinate `j`, the ray `corner_ray abar j` has value `1`. -/
@[simp] theorem corner_ray_apply_inr_self
    (abar : B → N → ℝ)
    (j : N) :
    corner_ray abar j (Sum.inr j) = 1 :=
  by
    classical
    simp [corner_ray]

/-- On any other nonbasic coordinate `j' ≠ j`, the ray `corner_ray abar j` vanishes. -/
@[simp] theorem corner_ray_apply_inr_of_ne
    (abar : B → N → ℝ)
    (j j' : N)
    (hj' : j' ≠ j) :
    corner_ray abar j (Sum.inr j') = 0 := by
  classical
  simp [corner_ray, hj']

/-- Helper for Remark 6.1: the tableau rays `r̄^j`, indexed by `j ∈ N`, are linearly independent. -/
theorem corner_ray_linear_independent
    (abar : B → N → ℝ) :
    LinearIndependent ℝ (corner_ray abar) := by
  classical
  -- Evaluate any finite dependence relation at the matching nonbasic coordinate.
  refine linearIndependent_iff'.2 ?_
  intro s g hg j hj
  have hsum :
      ∑ i ∈ s, g i * corner_ray abar i (Sum.inr j) = 0 := by
    simpa [Finset.sum_apply, Pi.smul_apply] using
      congrArg (fun x : Sum B N → ℝ ↦ x (Sum.inr j)) hg
  have hsplit :
      g j * corner_ray abar j (Sum.inr j) +
          ∑ i ∈ s.erase j, g i * corner_ray abar i (Sum.inr j) = 0 := by
    simpa [Finset.sum_insert, hj] using hsum
  have htail :
      ∑ i ∈ s.erase j, g i * corner_ray abar i (Sum.inr j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hij : i ≠ j := Finset.mem_erase.1 hi |>.1
    have hzero : corner_ray abar i (Sum.inr j) = 0 :=
      corner_ray_apply_inr_of_ne abar i j hij.symm
    simp [hzero]
  have hjself : corner_ray abar j (Sum.inr j) = 1 :=
    corner_ray_apply_inr_self abar j
  rw [htail, hjself, mul_one, add_zero] at hsplit
  exact hsplit

end Rays

section Geometry

variable [Fintype N]

/-- Helper for Remark 6.1: the tableau apex with basic coordinates `b̄` and nonbasic coordinates
`0`. -/
def cornerBasePoint
    (bbar : B → ℝ) : Sum B N → ℝ :=
  Sum.elim bbar (fun _ ↦ 0)

/-- Helper for Remark 6.1: on a basic coordinate, a linear combination of tableau rays is the
negative tableau row applied to the coefficient vector. -/
theorem sum_smul_corner_ray_apply_inl
    (abar : B → N → ℝ)
    (μ : N → ℝ)
    (i : B) :
    (∑ j : N, μ j • corner_ray abar j) (Sum.inl i) = -∑ j : N, abar i j * μ j := by
  -- Evaluate each ray on the basic coordinate and factor out the common minus sign.
  rw [Finset.sum_apply]
  calc
    ∑ j : N, (μ j • corner_ray abar j) (Sum.inl i)
        = ∑ j : N, -(abar i j * μ j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Pi.smul_apply, smul_eq_mul, corner_ray_apply_inl, mul_comm]
    _ = -∑ j : N, abar i j * μ j := by
          rw [← Finset.sum_neg_distrib]

/-- Helper for Remark 6.1: on a nonbasic coordinate, a linear combination of tableau rays
recovers the corresponding coefficient. -/
theorem sum_smul_corner_ray_apply_inr
    (abar : B → N → ℝ)
    (μ : N → ℝ)
    (j : N) :
    (∑ j' : N, μ j' • corner_ray abar j') (Sum.inr j) = μ j := by
  classical
  -- The tableau rays are the standard basis on the nonbasic block.
  rw [Finset.sum_apply]
  have hterm :
      ∀ k : N, (μ k • corner_ray abar k) (Sum.inr j) = if k = j then μ j else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [corner_ray, Pi.smul_apply, smul_eq_mul]
    · simp [corner_ray, Pi.smul_apply, smul_eq_mul, hk]
  simp_rw [hterm]
  simp

/-- The affine hull defined by the tableau equations
`x_i = b̄_i - ∑ j ∈ N, ā_{ij} x_j` for `i ∈ B`. -/
def corner_affine_hull
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    AffineSubspace ℝ (Sum B N → ℝ) where
  carrier :=
    {x : Sum B N → ℝ |
      ∀ i : B, x (Sum.inl i) = bbar i - ∑ j : N, abar i j * x (Sum.inr j)}
  smul_vsub_vadd_mem := by
    intro c x₁ x₂ x₃ hx₁ hx₂ hx₃ i
    -- Expand the tableau equations on each basic coordinate and use linearity of the finite sum.
    have hx₁i := hx₁ i
    have hx₂i := hx₂ i
    have hx₃i := hx₃ i
    have hsum :
        ∑ j : N, abar i j * ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j)) =
          c * (∑ j : N, abar i j * x₁ (Sum.inr j) - ∑ j : N, abar i j * x₂ (Sum.inr j)) +
            ∑ j : N, abar i j * x₃ (Sum.inr j) := by
      -- Normalize the nonbasic coordinates before distributing the finite sum.
      have hcoord :
          ∀ j : N,
            ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j)) =
              c * (x₁ (Sum.inr j) - x₂ (Sum.inr j)) + x₃ (Sum.inr j) := by
        intro j
        simp [Pi.smul_apply, vsub_eq_sub, vadd_eq_add]
      have hmul₁ :
          ∑ j : N, abar i j * (c * x₁ (Sum.inr j)) =
            c * ∑ j : N, abar i j * x₁ (Sum.inr j) := by
        calc
          ∑ j : N, abar i j * (c * x₁ (Sum.inr j))
              = ∑ j : N, c * (abar i j * x₁ (Sum.inr j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
          _ = c * ∑ j : N, abar i j * x₁ (Sum.inr j) := by
                rw [← Finset.mul_sum]
      have hmul₂ :
          ∑ j : N, abar i j * (c * x₂ (Sum.inr j)) =
            c * ∑ j : N, abar i j * x₂ (Sum.inr j) := by
        calc
          ∑ j : N, abar i j * (c * x₂ (Sum.inr j))
              = ∑ j : N, c * (abar i j * x₂ (Sum.inr j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
          _ = c * ∑ j : N, abar i j * x₂ (Sum.inr j) := by
                rw [← Finset.mul_sum]
      calc
        ∑ j : N, abar i j * ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j))
            = ∑ j : N, abar i j * (c * (x₁ (Sum.inr j) - x₂ (Sum.inr j)) + x₃ (Sum.inr j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [hcoord]
        _ = ∑ j : N, abar i j * (c * x₁ (Sum.inr j)) -
              ∑ j : N, abar i j * (c * x₂ (Sum.inr j)) +
              ∑ j : N, abar i j * x₃ (Sum.inr j) := by
                simp_rw [mul_add, mul_sub]
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = c * ∑ j : N, abar i j * x₁ (Sum.inr j) -
              c * ∑ j : N, abar i j * x₂ (Sum.inr j) +
              ∑ j : N, abar i j * x₃ (Sum.inr j) := by
                rw [hmul₁, hmul₂]
        _ = c * (∑ j : N, abar i j * x₁ (Sum.inr j) -
              ∑ j : N, abar i j * x₂ (Sum.inr j)) +
              ∑ j : N, abar i j * x₃ (Sum.inr j) := by
                ring
    rw [show (c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inl i) =
        c * (x₁ (Sum.inl i) - x₂ (Sum.inl i)) + x₃ (Sum.inl i) by
          simp [Pi.smul_apply, vsub_eq_sub, vadd_eq_add]]
    rw [hx₁i, hx₂i, hx₃i, hsum]
    ring

/-- Membership in `corner_affine_hull abar bbar` is exactly the tableau equation system on the
basic coordinates. -/
@[simp] theorem mem_corner_affine_hull_iff
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (x : Sum B N → ℝ) :
    x ∈ corner_affine_hull abar bbar ↔
      ∀ i : B, x (Sum.inl i) = bbar i - ∑ j : N, abar i j * x (Sum.inr j) :=
  Iff.rfl

/-- Every point of the tableau relaxation lies in the affine hull cut out by the tableau
equations. -/
theorem tableau_corner_relaxation_subset_corner_affine_hull
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    tableau_corner_relaxation abar bbar ⊆ corner_affine_hull abar bbar := by
  intro x hx
  simpa using ((mem_tableau_corner_relaxation_iff abar bbar x).1 hx).1

/-- Helper for Remark 6.1: a tableau-feasible point is exactly the apex plus a nonnegative
combination of the tableau rays. -/
theorem mem_tableau_corner_relaxation_iff_exists_nonneg_rayCombination
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (x : Sum B N → ℝ) :
    x ∈ tableau_corner_relaxation abar bbar ↔
      ∃ μ : N → ℝ, (∀ j : N, 0 ≤ μ j) ∧
        x = cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j := by
  constructor
  · intro hx
    -- Use the nonbasic coordinates of `x` as the ray coefficients.
    refine ⟨fun j ↦ x (Sum.inr j), hx.2, ?_⟩
    ext z
    cases z with
    | inl i =>
        have hxi := hx.1 i
        have hrepr :
            (((cornerBasePoint bbar + ∑ j : N, x (Sum.inr j) • corner_ray abar j) :
              Sum B N → ℝ) (Sum.inl i)) =
              bbar i - ∑ j : N, abar i j * x (Sum.inr j) := by
          simp [cornerBasePoint, sub_eq_add_neg, mul_comm]
        exact hxi.trans hrepr.symm
    | inr j =>
        simpa [cornerBasePoint] using
          (sum_smul_corner_ray_apply_inr (abar := abar) (μ := fun j ↦ x (Sum.inr j)) (j := j)).symm
  · rintro ⟨μ, hμ, rfl⟩
    -- The apex-plus-rays normal form directly gives the tableau equations and nonnegativity.
    have hnonbasic :
        ∀ j : N,
          (((cornerBasePoint bbar + ∑ j' : N, μ j' • corner_ray abar j') :
            Sum B N → ℝ) (Sum.inr j)) = μ j := by
      intro j
      simpa [cornerBasePoint] using
        (sum_smul_corner_ray_apply_inr (abar := abar) (μ := μ) (j := j))
    constructor
    · intro i
      have hbasic :
          (((cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j) :
            Sum B N → ℝ) (Sum.inl i)) =
            bbar i - ∑ j : N, abar i j * μ j := by
        simp [cornerBasePoint, sub_eq_add_neg, mul_comm]
      simpa [hnonbasic] using hbasic
    · intro j
      simpa [hnonbasic j] using hμ j

/-- Helper for Remark 6.1: the affine hull equations are equivalent to an unrestricted
combination of the tableau rays based at the apex. -/
theorem mem_corner_affine_hull_iff_exists_rayCombination
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (x : Sum B N → ℝ) :
    x ∈ corner_affine_hull abar bbar ↔
      ∃ μ : N → ℝ, x = cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j := by
  constructor
  · intro hx
    -- The free nonbasic coordinates again provide the ray coefficients.
    refine ⟨fun j ↦ x (Sum.inr j), ?_⟩
    ext z
    cases z with
    | inl i =>
        have hxi := hx i
        have hrepr :
            (((cornerBasePoint bbar + ∑ j : N, x (Sum.inr j) • corner_ray abar j) :
              Sum B N → ℝ) (Sum.inl i)) =
              bbar i - ∑ j : N, abar i j * x (Sum.inr j) := by
          simp [cornerBasePoint, sub_eq_add_neg, mul_comm]
        exact hxi.trans hrepr.symm
    | inr j =>
        simpa [cornerBasePoint] using
          (sum_smul_corner_ray_apply_inr (abar := abar) (μ := fun j ↦ x (Sum.inr j)) (j := j)).symm
  · rintro ⟨μ, rfl⟩
    -- The same coordinate computation shows that every apex-plus-rays point satisfies the
    -- defining affine equations.
    have hnonbasic :
        ∀ j : N,
          (((cornerBasePoint bbar + ∑ j' : N, μ j' • corner_ray abar j') :
            Sum B N → ℝ) (Sum.inr j)) = μ j := by
      intro j
      simpa [cornerBasePoint] using
        (sum_smul_corner_ray_apply_inr (abar := abar) (μ := μ) (j := j))
    intro i
    have hbasic :
        (((cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j) :
          Sum B N → ℝ) (Sum.inl i)) =
          bbar i - ∑ j : N, abar i j * μ j := by
      simp [cornerBasePoint, sub_eq_add_neg, mul_comm]
    simpa [hnonbasic] using hbasic

/-- Helper for Remark 6.1: membership in the translated span of the tableau rays is the same as
being the apex plus an arbitrary ray combination. -/
theorem mem_mk'_span_cornerRay_iff_exists_rayCombination
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (x : Sum B N → ℝ) :
    x ∈ AffineSubspace.mk' (cornerBasePoint bbar)
        (Submodule.span ℝ (Set.range (corner_ray abar))) ↔
      ∃ μ : N → ℝ, x = cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j := by
  rw [AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨μ, hμ⟩
    -- Convert the direction witness back into an apex-plus-rays point representation.
    refine ⟨μ, ?_⟩
    have hadd : (∑ j : N, μ j • corner_ray abar j) + cornerBasePoint bbar = x :=
      eq_sub_iff_add_eq.1 hμ
    simpa [add_comm, add_left_comm] using hadd.symm
  · rintro ⟨μ, rfl⟩
    -- Subtracting the apex leaves exactly the ray combination.
    refine ⟨μ, ?_⟩
    simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- Helper for Remark 6.1: the equation-defined affine hull is the affine subspace through the
tableau apex with direction spanned by the tableau rays. -/
theorem corner_affine_hull_eq_mk'_span_cornerRay
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    corner_affine_hull abar bbar =
      AffineSubspace.mk' (cornerBasePoint bbar)
        (Submodule.span ℝ (Set.range (corner_ray abar))) := by
  ext x
  -- The two affine subspaces have the same apex-plus-rays membership description.
  rw [mem_corner_affine_hull_iff_exists_rayCombination,
    mem_mk'_span_cornerRay_iff_exists_rayCombination]

/-- Helper for Remark 6.1: the tableau apex itself is feasible. -/
theorem cornerBasePoint_mem_tableau_corner_relaxation
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    cornerBasePoint bbar ∈ tableau_corner_relaxation abar bbar := by
  -- The apex is the zero ray combination.
  refine (mem_tableau_corner_relaxation_iff_exists_nonneg_rayCombination abar bbar
      (cornerBasePoint bbar)).2 ?_
  refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, ?_⟩
  simp [cornerBasePoint]

section Polyhedral

variable [Fintype B]

/-- Helper for Remark 6.1: `finCoordinateEquiv` transports the tableau apex-plus-rays normal form
to the corresponding sum in `Fin` coordinates. -/
theorem finCoordinateEquiv_map_cornerRayCombination
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (μ : N → ℝ) :
    finCoordinateEquiv (cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j) =
      finCoordinateEquiv (cornerBasePoint bbar) +
        ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := by
  -- `finCoordinateEquiv` is linear, so it distributes across the translated ray combination.
  rw [map_add, map_sum]
  simp_rw [map_smul]

/-- Helper for Remark 6.1: reindexing the image rays by `equivFin` does not change the cone
membership criterion, so cone membership can be read with `N`-indexed coefficients. -/
theorem mem_finitely_generated_cone_reindexed_cornerRay_iff
    (abar : B → N → ℝ)
    (y : Fin (Fintype.card (Sum B N)) → ℝ) :
    y ∈ finitely_generated_cone
          (fun k : Fin (Fintype.card N) ↦
            finCoordinateEquiv (corner_ray abar ((Fintype.equivFin N).symm k))) ↔
      ∃ μ : N → ℝ, (∀ j : N, 0 ≤ μ j) ∧
        y = ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := by
  let imageRay : N → Fin (Fintype.card (Sum B N)) → ℝ := fun j ↦
    finCoordinateEquiv (corner_ray abar j)
  let reindexedRay : Fin (Fintype.card N) → Fin (Fintype.card (Sum B N)) → ℝ := fun k ↦
    imageRay ((Fintype.equivFin N).symm k)
  let e : N ≃ Fin (Fintype.card N) := Fintype.equivFin N
  constructor
  · intro hy
    rcases (mem_finitely_generated_cone_iff (rays := reindexedRay) (x := y)).1 hy with
      ⟨ν, hν, hyrepr⟩
    refine ⟨fun j ↦ ν (e j), ?_, ?_⟩
    · intro j
      exact hν (e j)
    · calc
        y = ∑ k : Fin (Fintype.card N), ν k • reindexedRay k := hyrepr
        _ = ∑ j : N, ν (e j) • reindexedRay (e j) := by
              symm
              simpa using e.sum_comp (fun k : Fin (Fintype.card N) ↦ ν k • reindexedRay k)
        _ = ∑ j : N, (ν (e j)) • finCoordinateEquiv (corner_ray abar j) := by
              simp [reindexedRay, imageRay, e]
  · rintro ⟨μ, hμ, hyrepr⟩
    refine (mem_finitely_generated_cone_iff (rays := reindexedRay) (x := y)).2 ?_
    refine ⟨fun k ↦ μ (e.symm k), ?_, ?_⟩
    · intro k
      exact hμ (e.symm k)
    · calc
        y = ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := hyrepr
        _ = ∑ j : N, μ j • reindexedRay (e j) := by
              simp [reindexedRay, imageRay, e]
        _ = ∑ k : Fin (Fintype.card N), μ (e.symm k) • reindexedRay k := by
              simpa using (e.symm.sum_comp (fun j : N ↦ μ j • reindexedRay (e j))).symm

/-- Helper for Remark 6.1: the `Fin`-coordinate image of the tableau relaxation is exactly the
singleton tableau apex plus the cone generated by the reindexed image rays. -/
theorem mem_finCoordinateSet_tableau_corner_relaxation_iff_mem_singleton_add_cornerRayCone
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (x : Fin (Fintype.card (Sum B N)) → ℝ) :
    x ∈ finCoordinateSet (tableau_corner_relaxation abar bbar) ↔
      x ∈ ({finCoordinateEquiv (cornerBasePoint bbar)} +
        finitely_generated_cone
          (fun k : Fin (Fintype.card N) ↦
            finCoordinateEquiv (corner_ray abar ((Fintype.equivFin N).symm k)))) := by
  let apex : Fin (Fintype.card (Sum B N)) → ℝ := finCoordinateEquiv (cornerBasePoint bbar)
  let rays : Fin (Fintype.card N) → Fin (Fintype.card (Sum B N)) → ℝ := fun k ↦
    finCoordinateEquiv (corner_ray abar ((Fintype.equivFin N).symm k))
  constructor
  · intro hx
    rw [mem_finCoordinateSet_iff,
      mem_tableau_corner_relaxation_iff_exists_nonneg_rayCombination] at hx
    rcases hx with ⟨μ, hμ, hrepr⟩
    have himage :
        x = apex + ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := by
      -- Apply the coordinate equivalence once to the source-side apex-plus-rays description.
      calc
        x = finCoordinateEquiv (finCoordinateEquiv.symm x) := by
              simpa using (finCoordinateEquiv.apply_symm_apply x).symm
        _ = finCoordinateEquiv (cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j) := by
              exact congrArg finCoordinateEquiv hrepr
        _ = apex + ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := by
              simp [apex]
    have hcone :
        (∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j)) ∈
          finitely_generated_cone rays := by
      -- The cone bridge packages the `N`-indexed coefficients into the canonical `Fin` family.
      simpa [rays] using
        (mem_finitely_generated_cone_reindexed_cornerRay_iff (abar := abar)
          (y := ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j))).2
          ⟨μ, hμ, rfl⟩
    exact ⟨apex, Set.mem_singleton apex, _, hcone, himage.symm⟩
  · rintro ⟨z, hz, y, hy, hxy⟩
    have hz' : z = apex := Set.mem_singleton_iff.mp hz
    rcases (mem_finitely_generated_cone_reindexed_cornerRay_iff (abar := abar) (y := y)).1
        (by simpa [rays] using hy) with ⟨μ, hμ, hyrepr⟩
    rw [mem_finCoordinateSet_iff,
      mem_tableau_corner_relaxation_iff_exists_nonneg_rayCombination]
    refine ⟨μ, hμ, ?_⟩
    -- Pull the singleton-plus-cone decomposition back through `finCoordinateEquiv`.
    exact finCoordinateEquiv.injective <| by
      calc
        finCoordinateEquiv (finCoordinateEquiv.symm x) = x := by
              simpa using finCoordinateEquiv.apply_symm_apply x
        _ = z + y := hxy.symm
        _ = apex + y := by simp [hz']
        _ = finCoordinateEquiv (cornerBasePoint bbar) +
              ∑ j : N, μ j • finCoordinateEquiv (corner_ray abar j) := by
                simp [apex, hyrepr]
        _ = finCoordinateEquiv
              (cornerBasePoint bbar + ∑ j : N, μ j • corner_ray abar j) := by
                symm
                exact finCoordinateEquiv_map_cornerRayCombination abar bbar μ

/-- Remark 6.1 (2). The canonical `Fin`-coordinate view of the tableau relaxation `P(B)` is a
polyhedron. -/
theorem tableau_corner_relaxation_is_polyhedron
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    is_polyhedron (finCoordinateSet (tableau_corner_relaxation abar bbar)) := by
  let apex : Fin (Fintype.card (Sum B N)) → ℝ := finCoordinateEquiv (cornerBasePoint bbar)
  let rays : Fin (Fintype.card N) → Fin (Fintype.card (Sum B N)) → ℝ := fun k ↦
    finCoordinateEquiv (corner_ray abar ((Fintype.equivFin N).symm k))
  have hapexPolytope :
      ({apex} : Set (Fin (Fintype.card (Sum B N)) → ℝ)).IsPolytope ℝ := by
    -- A singleton is the convex hull of its unique point.
    refine ⟨{apex}, Set.finite_singleton apex, ?_⟩
    simp [convexHull_singleton]
  -- Route correction: separate the coordinate transport from the `Fin`-reindexing by using the
  -- singleton-plus-cone interface, then apply Minkowski-Weyl once.
  refine (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2 ?_
  refine ⟨{apex}, hapexPolytope, Fintype.card N, rays, ?_⟩
  ext x
  simpa [apex, rays] using
    (mem_finCoordinateSet_tableau_corner_relaxation_iff_mem_singleton_add_cornerRayCone
      (abar := abar) (bbar := bbar) (x := x))

end Polyhedral

/-- Helper for Remark 6.1: every tableau ray lies in the direction of the affine span of the
tableau relaxation. -/
theorem corner_ray_mem_direction_affineSpan_tableauCornerRelaxation
    (abar : B → N → ℝ)
    (bbar : B → ℝ)
    (j : N) :
    corner_ray abar j ∈ (affineSpan ℝ (tableau_corner_relaxation abar bbar)).direction := by
  classical
  -- Place the apex and the apex shifted by the `j`-th ray in the affine span and take their
  -- difference.
  have hbase :
      cornerBasePoint bbar ∈ affineSpan ℝ (tableau_corner_relaxation abar bbar) :=
    subset_affineSpan ℝ _ (cornerBasePoint_mem_tableau_corner_relaxation abar bbar)
  have hshift_mem :
      cornerBasePoint bbar + corner_ray abar j ∈ tableau_corner_relaxation abar bbar := by
    refine (mem_tableau_corner_relaxation_iff_exists_nonneg_rayCombination abar bbar
        (cornerBasePoint bbar + corner_ray abar j)).2 ?_
    refine ⟨Pi.single j 1, ?_, ?_⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Pi.single, hk]
    · simp
  have hshift :
      cornerBasePoint bbar + corner_ray abar j ∈
        affineSpan ℝ (tableau_corner_relaxation abar bbar) :=
    subset_affineSpan ℝ _ hshift_mem
  have hdiff :=
    AffineSubspace.vsub_mem_direction hshift hbase
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff

/-- Helper for Remark 6.1: the affine hull of `P(B)` is defined by the tableau equations
`x_i = b̄_i - ∑ j ∈ N, ā_{ij} x_j` for `i ∈ B`. -/
theorem affineSpan_tableau_corner_relaxation_eq_corner_affine_hull
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    affineSpan ℝ (tableau_corner_relaxation abar bbar) = corner_affine_hull abar bbar := by
  apply le_antisymm
  · -- The affine span is contained in every affine subspace containing the tableau relaxation.
    exact affineSpan_le.2 (tableau_corner_relaxation_subset_corner_affine_hull abar bbar)
  · intro x hx
    -- Every point of the affine hull is the apex plus a direction in the span of the tableau
    -- rays, and those rays already lie in the direction of the tableau affine span.
    rcases (mem_corner_affine_hull_iff_exists_rayCombination abar bbar x).1 hx with ⟨μ, rfl⟩
    have hbase :
        cornerBasePoint bbar ∈ affineSpan ℝ (tableau_corner_relaxation abar bbar) :=
      subset_affineSpan ℝ _ (cornerBasePoint_mem_tableau_corner_relaxation abar bbar)
    have hsum :
        ∑ j : N, μ j • corner_ray abar j ∈
          (affineSpan ℝ (tableau_corner_relaxation abar bbar)).direction := by
      refine Submodule.sum_mem _ ?_
      intro j hj
      exact Submodule.smul_mem _ _ <|
        corner_ray_mem_direction_affineSpan_tableauCornerRelaxation abar bbar j
    simpa [add_comm] using AffineSubspace.vadd_mem_of_mem_direction hsum hbase

/-- Helper for Remark 6.1: the tableau relaxation `P(B)` has affine dimension `|N|`. -/
theorem finrank_direction_affineSpan_tableau_corner_relaxation_eq_card
    (abar : B → N → ℝ)
    (bbar : B → ℝ) :
    Module.finrank ℝ (affineSpan ℝ (tableau_corner_relaxation abar bbar)).direction =
      Fintype.card N := by
  -- Rewrite the affine hull to the canonical translated span and compute the direction there.
  calc
    Module.finrank ℝ (affineSpan ℝ (tableau_corner_relaxation abar bbar)).direction
        = Module.finrank ℝ (corner_affine_hull abar bbar).direction := by
            rw [affineSpan_tableau_corner_relaxation_eq_corner_affine_hull]
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (corner_ray abar))) := by
          rw [corner_affine_hull_eq_mk'_span_cornerRay, AffineSubspace.direction_mk']
    _ = Fintype.card N := by
          simpa using finrank_span_eq_card (corner_ray_linear_independent abar)

end Geometry

end Remark61
