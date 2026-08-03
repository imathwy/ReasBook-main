module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- Example 50.8 (1): The origin and the standard coordinate vectors in `ℝ^N` are
affinely independent. -/
theorem standardSimplex_affineIndependent {N : ℕ} :
    AffineIndependent ℝ
      (Fin.cases (0 : EuclideanSpace ℝ (Fin N))
        (fun i : Fin N ↦ EuclideanSpace.single i 1)) := by
  -- Taking differences from the origin reduces affine independence to linear independence.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (N + 1)))]
  -- Reindexing the nonzero vertices identifies the difference family with the coordinate vectors.
  have hfamily :
      ((fun i : {x : Fin (N + 1) // x ≠ 0} ↦
          Fin.cases (0 : EuclideanSpace ℝ (Fin N))
              (fun j : Fin N ↦ EuclideanSpace.single j 1) i.1) ∘
        (finSuccAboveEquiv (0 : Fin (N + 1)))) =
        fun i : Fin N ↦ EuclideanSpace.single i 1 := by
    funext i
    simp only [Function.comp_apply, finSuccAboveEquiv_apply, Fin.zero_succAbove,
      Fin.cases_succ]
  simp only [Fin.cases_zero, vsub_eq_sub, sub_zero]
  rw [hfamily]
  -- The coordinate vectors are the vectors of the standard `PiLp` basis.
  have hbasis :
      (fun i : Fin N ↦ EuclideanSpace.single i 1) =
        (PiLp.basisFun 2 ℝ (Fin N) : Fin N → EuclideanSpace ℝ (Fin N)) := by
    funext i
    rw [PiLp.basisFun_apply]
  rw [hbasis]
  exact (PiLp.basisFun 2 ℝ (Fin N)).linearIndependent

/-- Example 50.8 (2): An affinely independent set in `ℝ^N` has at most
`N + 1` points. -/
theorem affineIndependent_set_encard_le {N : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin N)))
    (hs : AffineIndependent ℝ (fun x : s ↦ x.1)) :
    s.encard ≤ N + 1 := by
  classical
  -- Finite-dimensional affine independence makes the subtype of points finite.
  have hfinite : s.Finite := finite_set_of_fin_dim_affineIndependent ℝ hs
  letI : Fintype s := hfinite.fintype
  -- The vector span has dimension at most the dimension of the ambient Euclidean space.
  have hspan :
      Module.finrank ℝ (vectorSpan ℝ (Set.range (fun x : s ↦ x.1))) ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.finrank_le _
  -- Combine the affine-independent cardinality bound with the ambient dimension computation.
  have hcard : Fintype.card s ≤ N + 1 := by
    calc
      Fintype.card s ≤
          Module.finrank ℝ (vectorSpan ℝ (Set.range (fun x : s ↦ x.1))) + 1 :=
        hs.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) + 1 :=
        Nat.add_le_add_right hspan 1
      _ = N + 1 := by
        rw [finrank_euclideanSpace_fin]
  -- Rewrite finite extended cardinality as subtype cardinality and cast the bound.
  rw [Set.encard_eq_coe_toFinset_card s, Set.toFinset_card]
  exact_mod_cast hcard
