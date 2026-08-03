import Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_39
import Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_theorem_4_47

open scoped BigOperators Matrix Pointwise

-- The rational-polytope / integer-cone owners are established in Theorem 4.47. This file keeps
-- only the Corollary 4.48 lifted-polyhedron and projection layer built on those owners.
-- Domain-style sampling for this refine pass:
-- * primary domain: Balas-style lifted polyhedron projections for unions of polyhedra
-- * core/canonical owners inspected upstream: `balas_lifted_polyhedron`,
--   `mixed_integer_x_projection`, `integral_intcone`
-- * layer targeted here: `source-facing` lifted system, with the projection kept as the canonical
--   direct image under `Prod.fst` rather than as a parallel one-off owner

section Corollary448

/-- The lifted polyhedron `Q` from Corollary 4.48, with variables `(x, xParts, δ, μ)` satisfying
`Aᵢ xⁱ ≤ δᵢ bⁱ`, `x = ∑ xⁱ + ∑ μⱼ rʲ`, `∑ δᵢ = 1`, `δᵢ ≥ 0`, and `μⱼ ≥ 0`. -/
def union_polytope_integral_cone_lifted_polyhedron
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Set ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ) × (Fin t → ℝ)) :=
  {(x, xParts, δ, μ) |
    (∀ i : Fin k,
      (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤ δ i • (fun j : Fin (m i) ↦ (b i j : ℝ))) ∧
      (x =
        (∑ i : Fin k, xParts i) +
          ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ))) ∧
      (∑ i : Fin k, δ i = 1) ∧
      (∀ i : Fin k, 0 ≤ δ i) ∧
      (∀ j : Fin t, 0 ≤ μ j)}

/-- Membership in `union_polytope_integral_cone_lifted_polyhedron m A b r` is exactly the system
of inequalities displayed in `(4.35)`. -/
theorem mem_union_polytope_integral_cone_lifted_polyhedron_iff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (x : Fin n → ℝ)
    (xParts : Fin k → Fin n → ℝ)
    (δ : Fin k → ℝ)
    (μ : Fin t → ℝ) :
    (x, xParts, δ, μ) ∈ union_polytope_integral_cone_lifted_polyhedron m A b r ↔
      (∀ i : Fin k,
        (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤ δ i • (fun j : Fin (m i) ↦ (b i j : ℝ))) ∧
        (x =
          (∑ i : Fin k, xParts i) +
            ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ))) ∧
        (∑ i : Fin k, δ i = 1) ∧
        (∀ i : Fin k, 0 ≤ δ i) ∧
        (∀ j : Fin t, 0 ≤ μ j) :=
  Iff.rfl

/-- Membership in the `x`-projection of `union_polytope_integral_cone_lifted_polyhedron m A b r`
means that `x` admits compatible lifted variables `(xParts, δ, μ)` satisfying the Corollary 4.48
system. -/
theorem mem_image_fst_union_polytope_integral_cone_lifted_polyhedron_iff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (x : Fin n → ℝ) :
    x ∈ Prod.fst '' union_polytope_integral_cone_lifted_polyhedron m A b r ↔
      ∃ xParts : Fin k → Fin n → ℝ, ∃ δ : Fin k → ℝ, ∃ μ : Fin t → ℝ,
        (x, xParts, δ, μ) ∈ union_polytope_integral_cone_lifted_polyhedron m A b r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, y.2.2.1, y.2.2.2, hy⟩
  · rintro ⟨xParts, δ, μ, hLifted⟩
    exact ⟨(x, xParts, δ, μ), hLifted, rfl⟩

/-- Helper for Corollary 4.48: the projection of the source-facing lift `Q` splits into Balas'
`x`-projection for the polytope union and the finitely generated cone of the common rays. -/
lemma image_fst_union_polytope_integral_cone_lifted_polyhedron_eq_balas_x_projection_add_finitely_generated_cone
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Prod.fst '' union_polytope_integral_cone_lifted_polyhedron m A b r =
      balas_x_projection m
        (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
        (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
        finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [mem_image_fst_union_polytope_integral_cone_lifted_polyhedron_iff] at hx
    rcases hx with ⟨xParts, δ, μ, hLifted⟩
    rw [mem_union_polytope_integral_cone_lifted_polyhedron_iff] at hLifted
    rcases hLifted with ⟨hineq, hxeq, hδsum, hδnonneg, hμnonneg⟩
    -- The `(xParts, δ)` block is exactly a Balas lifted witness for the polytope union.
    have hxBalas :
        ∑ i : Fin k, xParts i ∈
          balas_x_projection m
            (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
            (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) := by
      rw [mem_balas_x_projection_iff]
      refine ⟨xParts, δ, ?_⟩
      rw [mem_balas_lifted_polyhedron_iff]
      exact ⟨hineq, rfl, hδsum, hδnonneg⟩
    -- The `μ`-variables contribute precisely one point of the common real ray cone.
    have hcone :
        ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)) ∈
          finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) := by
      rw [mem_finitely_generated_cone_iff]
      exact ⟨μ, hμnonneg, rfl⟩
    exact Set.mem_add.2 ⟨∑ i : Fin k, xParts i, hxBalas,
      ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)), hcone, hxeq.symm⟩
  · intro hx
    rcases Set.mem_add.1 hx with ⟨xBalas, hxBalas, yCone, hyCone, hxy⟩
    rw [mem_balas_x_projection_iff] at hxBalas
    rw [mem_finitely_generated_cone_iff] at hyCone
    rcases hxBalas with ⟨xParts, δ, hBalas⟩
    rcases hyCone with ⟨μ, hμnonneg, hyCone_eq⟩
    rw [mem_balas_lifted_polyhedron_iff] at hBalas
    rcases hBalas with ⟨hineq, hsum, hδsum, hδnonneg⟩
    rw [mem_image_fst_union_polytope_integral_cone_lifted_polyhedron_iff]
    refine ⟨xParts, δ, μ, ?_⟩
    rw [mem_union_polytope_integral_cone_lifted_polyhedron_iff]
    refine ⟨hineq, ?_, hδsum, hδnonneg, hμnonneg⟩
    -- Reassemble the Balas visible point and the common cone contribution into the full lift.
    calc
      x = xBalas + yCone := hxy.symm
      _ = (∑ i : Fin k, xParts i) + yCone := by rw [← hsum]
      _ = (∑ i : Fin k, xParts i) + ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)) := by
            rw [hyCone_eq]

/-- Corollary 4.48. If each rational system `Aᵢ x ≤ bⁱ` cuts out a rational polytope, then the
convex hull of `(⋃ i, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r` is the
projection of the lifted polyhedron defined by the inequalities in `(4.35)` onto the
`x`-coordinates. -/
theorem convexHull_union_rational_polytopes_add_integral_intcone_eq_x_projection
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (hP_polytope : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope)
    :
    convexHull ℝ ((⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r) =
      Prod.fst '' union_polytope_integral_cone_lifted_polyhedron m A b r := by
  -- Route correction: the statement is false without an extra hypothesis ruling out empty pieces
  -- with nontrivial homogeneous systems. If some `rational_matrix_polyhedron (A i) (b i)` is
  -- empty but `rational_matrix_polyhedron (A i) 0` contains a nonzero vector, the lifted system
  -- still allows that block with `δ i = 0`, so the projection on the right strictly enlarges the
  -- convex hull on the left.
  --
  -- TODO: re-plan this item with the mathematically correct statement, for example by assuming the
  -- input polytope pieces are nonempty or by replacing the target lift with the nonempty-family
  -- Balas formulation that discards empty pieces before adding the common cone.
  sorry

end Corollary448
