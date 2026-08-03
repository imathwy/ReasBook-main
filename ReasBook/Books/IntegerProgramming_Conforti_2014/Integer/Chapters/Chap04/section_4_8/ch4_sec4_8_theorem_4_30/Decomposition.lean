import Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_proposition_3_12
import Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15

open scoped BigOperators Matrix Pointwise

-- Declarations for this theorem-local helper file support the source-faithful Chapter 3.13 step
-- in Meyer's proof without forcing the main theorem file to inline the decomposition API.

section Theorem430

variable {n p : ℕ}

/-- Helper for Theorem 4.30: once the flattened ambient set is known to be polyhedral, Theorem
3.13 gives Meyer's required `polytope + finitely generated cone` decomposition. -/
lemma pflat_eq_polytope_add_finitely_generated_cone
    {Pflat : Set (Fin (n + p) → ℝ)}
    (hPflat_polyhedron : is_polyhedron Pflat) :
    ∃ Q : Set (Fin (n + p) → ℝ),
      Q.IsPolytope ℝ ∧
        ∃ q : ℕ, ∃ rays : Fin q → Fin (n + p) → ℝ,
          Pflat = Q + finitely_generated_cone rays := by
  -- This is exactly the Chapter 3.13 decomposition, specialized to the flattened ambient space.
  exact (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 hPflat_polyhedron

/-- Helper for Theorem 4.30: a nonempty rational flattened ambient set admits a rational
vertex presentation that keeps the already normalized integral recession rays fixed. -/
lemma existsFlattenedRationalVertexPresentationCompatibleWithIntegralRays
    {k q : ℕ}
    {Pflat : Set (Fin k → ℝ)}
    (hPflat_rational : is_rational_polyhedron Pflat)
    (hPflat_nonempty : Set.Nonempty Pflat)
    (rays : Fin q → Fin k → ℤ)
    (hrec_integral :
      recessionCone Pflat =
        finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ))) :
    ∃ t : ℕ, ∃ vℚ : Fin t → Fin k → ℚ,
      Pflat =
        convexHull ℝ (Set.range (fun i : Fin t ↦ fun u : Fin k ↦ (vℚ i u : ℝ))) +
          finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ)) := by
  sorry

end Theorem430
