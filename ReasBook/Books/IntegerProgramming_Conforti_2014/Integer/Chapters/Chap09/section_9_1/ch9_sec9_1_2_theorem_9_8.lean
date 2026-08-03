import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_remark_9_9

open scoped Matrix

noncomputable section Theorem98

variable {n : ℕ}

/-- The ellipsoid in `ℝ^n` with center `a` and shape matrix `C`, written as
`{x | ‖C (x - a)‖₂ ≤ 1}` in the local `Fin n → ℝ` coordinate model, encoded by the equivalent
quadratic inequality `(C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1`. -/
def euclidean_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1}

/-- Membership in `euclidean_ellipsoid C a` is exactly the defining quadratic inequality. -/
theorem mem_euclidean_ellipsoid_iff
    {C : Matrix (Fin n) (Fin n) ℝ} {a x : Fin n → ℝ} :
    x ∈ euclidean_ellipsoid C a ↔
      (C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1 := by
  rfl

/-- For a nonsingular matrix `C`, the ellipsoid `euclidean_ellipsoid C a` defines a convex body,
so the Chapter 9 lattice-width API applies directly to it. -/
def euclidean_ellipsoid_convex_body
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    ConvexBody (Fin n → ℝ) where
  carrier := euclidean_ellipsoid C a
  convex' := by
    sorry
  isCompact' := by
    sorry
  nonempty' := by
    sorry

@[simp] theorem coe_euclidean_ellipsoid_convex_body
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    (euclidean_ellipsoid_convex_body C a hC : Set (Fin n → ℝ)) = euclidean_ellipsoid C a :=
  rfl

/-- Theorem 9.8 (Flatness Theorem for Ellipsoids). Let `E ⊆ ℝ^n` be the ellipsoid
`euclidean_ellipsoid C a` for a nonsingular matrix `C`. If `E` does not contain any integral
point, then its lattice width is at most `ellipsoid_flatness_bound n`. The lattice width is taken
for the canonical convex-body owner associated to the nonsingular ellipsoid. -/
theorem euclidean_ellipsoid_lattice_width_le_flatness_bound
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : IsUnit C.det)
    (hfree : ¬ contains_integral_point (euclidean_ellipsoid C a)) :
    lattice_width (euclidean_ellipsoid_convex_body C a hC) ≤ ellipsoid_flatness_bound n := by
  sorry

end Theorem98
