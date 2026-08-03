module

public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

open Polynomial

/-- Theorem 56.1 (1), the fundamental theorem of algebra. A complex polynomial of positive
degree has a complex root. -/
theorem complexPolynomial_exists_root (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, p.IsRoot z :=
  Complex.exists_root (natDegree_pos_iff_degree_pos.mp hdeg)

/-- Theorem 56.1 (2), the real-coefficient case. A real polynomial of positive degree has a
complex root. -/
theorem realPolynomial_exists_complexRoot (p : Polynomial ℝ) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z :=
  IsAlgClosed.exists_root _ <| by
    rw [degree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact (natDegree_pos_iff_degree_pos.mp hdeg).ne'
