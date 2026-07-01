import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

-- Proof sketch: use the canonical witness `Lagrange.interpolate Finset.univ a b`, whose degree is
-- `< Fintype.card ι` and whose values at the nodes are prescribed by mathlib's interpolation API.
-- For uniqueness, compare any candidate polynomial to this canonical interpolation via
-- `Lagrange.eq_interpolate_iff`.
/-- Theorem 1.3.46: for finitely many pairwise distinct nodes in a field and prescribed values,
there exists a unique polynomial of degree below the number of nodes taking the required value at
each node. Specializing to `ι := Fin n` recovers the textbook formulation with `n` nodes
`a₁, …, aₙ`. -/
theorem existsUnique_lagrange_interpolation_polynomial
    {K : Type u} [Field K] {ι : Type v} [Fintype ι] (a b : ι → K) (ha : Function.Injective a) :
    ∃! P : K[X], P.degree < Fintype.card ι ∧ ∀ i, P.eval (a i) = b i := by
  classical
  refine ⟨Lagrange.interpolate Finset.univ a b, ?_, ?_⟩
  · constructor
    · have hdeg :
          (Lagrange.interpolate Finset.univ a b).degree <
            ↑((Finset.univ : Finset ι).card) :=
        Lagrange.degree_interpolate_lt b ha.injOn
      simpa using hdeg
    · intro i
      have heval : (Lagrange.interpolate Finset.univ a b).eval (a i) = b i :=
        Lagrange.eval_interpolate_at_node b ha.injOn
          (by simp : i ∈ (Finset.univ : Finset ι))
      simpa using heval
  · intro P hP
    have hiff :
        (P.degree < ↑((Finset.univ : Finset ι).card) ∧
          ∀ i ∈ (Finset.univ : Finset ι), P.eval (a i) = b i) ↔
          P = Lagrange.interpolate Finset.univ a b :=
      Lagrange.eq_interpolate_iff b ha.injOn
    rw [← hiff]
    simpa using hP
