module

public import Topology_Munkres_2000.Book.Theorem_56_1

public section

open Polynomial

/-- Theorem 56.2 (1). A complex polynomial has as many complex roots, counted with
multiplicity, as its natural degree. -/
theorem complexPolynomial_card_roots (p : ℂ[X]) : p.roots.card = p.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

/-- Theorem 56.2 (2). A real polynomial, after extending its coefficients to `ℂ`,
has as many complex roots, counted with multiplicity, as its natural degree. -/
theorem realPolynomial_card_complexRoots (p : ℝ[X]) :
    (p.aroots ℂ).card = p.natDegree :=
  IsAlgClosed.card_aroots_eq_natDegree
