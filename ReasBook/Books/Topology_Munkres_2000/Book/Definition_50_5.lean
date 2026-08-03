module

public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open scoped BigOperators

/-- Helper for Definition 50.5: the affine span of `x 0, …, x k` is the set of linear
combinations whose coefficients sum to one. The affine independence assumed in the source
is not needed for this characterization. -/
theorem affineSpan_eq_setOf_sum_smul {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) :
    (affineSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) =
      {p | ∃ t : Fin (k + 1) → ℝ, (∑ i, t i) = 1 ∧ p = ∑ i, t i • x i} := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    refine ⟨t, ht, ?_⟩
    simpa [Finset.affineCombination_apply, ht] using hp
  · rintro ⟨t, ht, rfl⟩
    simpa [Finset.affineCombination_apply, ht] using
      (affineCombination_mem_affineSpan ht x)

/-- Helper for Definition 50.5: adjoining the complementary leading coefficient makes
the coefficients sum to one. -/
private lemma sumFinConsOneSubSum {R : Type*} [Ring R] {k : ℕ} (a : Fin k → R) :
    (∑ i : Fin (k + 1), Fin.cons (1 - ∑ j, a j) a i) = 1 := by
  -- Split off the leading coefficient, leaving the complementary sums to cancel.
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_add_cancel]

/-- Helper for Definition 50.5: a finite weighted sum of total weight one is the base
point plus the corresponding weighted sum of differences. -/
private lemma sumSmulEqBaseAddSumSmulSub {R V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] {k : ℕ} (t : Fin (k + 1) → R) (x : Fin (k + 1) → V)
    (ht : (∑ i, t i) = 1) :
    ∑ i, t i • x i = x 0 + ∑ i : Fin k, t (Fin.succ i) • (x (Fin.succ i) - x 0) := by
  -- Separate the head terms in both the coefficient sum and the weighted sum.
  have hcoeff : t 0 + ∑ i : Fin k, t (Fin.succ i) = 1 := by
    simpa only [Fin.sum_univ_succ] using ht
  have hbase : t 0 • x 0 + (∑ i : Fin k, t (Fin.succ i)) • x 0 = x 0 := by
    rw [← add_smul, hcoeff, one_smul]
  rw [Fin.sum_univ_succ]
  -- Expand the difference sum and use the total-weight identity on the base-point term.
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, eq_sub_of_add_eq hbase]
  abel

/-- Helper for Definition 50.5: barycentric coordinates are equivalent to coordinates
relative to the first point and the successor-indexed difference vectors. -/
private lemma existsSumSmulEq_iff_existsBaseAddDifferences {R V : Type*} [Ring R]
    [AddCommGroup V] [Module R V] {k : ℕ} (x : Fin (k + 1) → V) (p : V) :
    (∃ t : Fin (k + 1) → R, (∑ i, t i) = 1 ∧ p = ∑ i, t i • x i) ↔
      ∃ a : Fin k → R, p = x 0 + ∑ i, a i • (x (Fin.succ i) - x 0) := by
  constructor
  · rintro ⟨t, ht, hp⟩
    -- Retain the successor coefficients after applying the total-weight identity.
    refine ⟨fun i ↦ t (Fin.succ i), ?_⟩
    exact hp.trans (sumSmulEqBaseAddSumSmulSub t x ht)
  · rintro ⟨a, hp⟩
    let t : Fin (k + 1) → R := Fin.cons (1 - ∑ i, a i) a
    -- The complementary leading coefficient supplies a normalized barycentric family.
    have ht : (∑ i, t i) = 1 := by
      simpa only [t] using sumFinConsOneSubSum a
    have hrepresentation :
        ∑ i, t i • x i = x 0 + ∑ i, a i • (x (Fin.succ i) - x 0) := by
      simpa only [t, Fin.cons_succ] using sumSmulEqBaseAddSumSmulSub t x ht
    refine ⟨t, ht, ?_⟩
    exact hp.trans hrepresentation.symm

/-- Definition 50.5 (2): The plane determined by `x 0, …, x k` is the plane through
`x 0` parallel to the difference vectors `x (Fin.succ i) - x 0`. -/
theorem affineSpan_eq_basePoint_add_differences {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) :
    (affineSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) =
      {p | ∃ a : Fin k → ℝ,
        p = x 0 + ∑ i, a i • (x (Fin.succ i) - x 0)} := by
  -- Rewrite affine-span membership into barycentric coordinates, then use the bridge above.
  rw [affineSpan_eq_setOf_sum_smul]
  ext p
  exact existsSumSmulEq_iff_existsBaseAddDifferences x p
