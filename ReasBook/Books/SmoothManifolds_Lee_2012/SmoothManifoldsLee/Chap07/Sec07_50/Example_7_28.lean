import Mathlib
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Proposition_7_11

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch` only returned a generic Lie-group hit, so the canonical
-- `SO(n)`/`O(n)` owners and their membership API were verified directly against mathlib's
-- `Matrix.specialOrthogonalGroup`/`Matrix.orthogonalGroup`. The source-facing Lie-group statement
-- therefore records explicitly the smooth bridge from the canonical owner `SO(n)` to the
-- determinant-one embedded subtype inside `O(n)`.

open scoped Manifold ContDiff Matrix.Norms.Elementwise

open Manifold

local notation "M(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "SO(" n ")" => Matrix.specialOrthogonalGroup (Fin n) ℝ

/- Example 7.28 (1): the textbook description of `SO(n)` as `O(n) ∩ SL(n, ℝ)` is exactly the
canonical mathlib membership theorem for `Matrix.specialOrthogonalGroup`. -/
recall Matrix.mem_specialOrthogonalGroup_iff

/-- Helper for Example 7.28: the determinant of an orthogonal matrix squares to `1`. -/
lemma orthogonalGroup_det_sq_eq_one (n : ℕ) (A : O(n)) :
    ((A : M(n)).det) ^ 2 = 1 := by
  -- Rewrite orthogonality as `Aᵀ * A = 1` and then take determinants.
  have hOrth : (A : M(n)).transpose * (A : M(n)) = 1 := by
    simpa using (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ (A := (A : M(n)))).mp A.property
  have hDet := congrArg Matrix.det hOrth
  simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hDet

/-- Helper for Example 7.28: inside `O(n)`, special-orthogonal membership is exactly the
determinant-one condition. -/
lemma mem_specialOrthogonalGroup_iff_det_eq_one (n : ℕ) (A : O(n)) :
    (A : M(n)) ∈ SO(n) ↔ (A : M(n)).det = 1 := by
  constructor
  · intro hA
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp hA).2
  · intro hA
    exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨A.property, hA⟩

/-- Helper for Example 7.28: the determinant map is continuous on the orthogonal-group subtype. -/
lemma continuous_det_orthogonalGroup (n : ℕ) :
    Continuous (fun A : O(n) ↦ (A : M(n)).det) := by
  -- Restrict the ambient continuous determinant map to the orthogonal subgroup.
  simpa using (show Continuous fun A : O(n) ↦ (A : M(n)).det by fun_prop)

/-- Every element of the real orthogonal group has determinant `1` or `-1`. -/
theorem orthogonalGroup_det_eq_one_or_eq_neg_one (n : ℕ)
    (A : O(n)) :
    (A : M(n)).det = 1 ∨ (A : M(n)).det = -1 := by
  -- The determinant-square identity leaves only the two sign possibilities.
  exact sq_eq_one_iff.mp (orthogonalGroup_det_sq_eq_one n A)

/-- Example 7.28 (2): inside `O(n)`, belonging to `SO(n)` is equivalent to having positive
determinant. -/
theorem mem_specialOrthogonalGroup_iff_det_pos (n : ℕ)
    (A : O(n)) :
    (A : M(n)) ∈ SO(n) ↔ 0 < (A : M(n)).det := by
  constructor
  · intro hA
    -- On `SO(n)`, the determinant is exactly `1`, hence positive.
    rw [mem_specialOrthogonalGroup_iff_det_eq_one n A] at hA
    rw [hA]
    norm_num
  · intro hA
    -- Orthogonal matrices only have determinants `1` or `-1`, so positivity forces `1`.
    rcases orthogonalGroup_det_eq_one_or_eq_neg_one n A with hDet | hDet
    · exact (mem_specialOrthogonalGroup_iff_det_eq_one n A).2 hDet
    · exfalso
      linarith

/-- Example 7.28 (3): as a subset of `O(n)`, the special orthogonal group `SO(n)` is open. -/
theorem isOpen_specialOrthogonalGroup_in_orthogonalGroup (n : ℕ) :
    IsOpen { A : O(n) | (A : M(n)) ∈ SO(n) } := by
  -- Rewrite the carrier as the positive-determinant locus of a continuous function.
  simpa [mem_specialOrthogonalGroup_iff_det_pos] using
    (isOpen_lt continuous_const (continuous_det_orthogonalGroup n))

/-- As a subset of `O(n)`, the special orthogonal group `SO(n)` is also closed. -/
theorem isClosed_specialOrthogonalGroup_in_orthogonalGroup (n : ℕ) :
    IsClosed { A : O(n) | (A : M(n)) ∈ SO(n) } := by
  -- Rewrite the carrier as the determinant-one level set of a continuous function.
  simpa [mem_specialOrthogonalGroup_iff_det_eq_one] using
    (isClosed_eq (continuous_det_orthogonalGroup n) continuous_const)

/-- The determinant-one locus in `O(n)` is exactly the positive-determinant locus. -/
theorem specialOrthogonalGroup_eq_det_pos_in_orthogonalGroup (n : ℕ) :
    ({ A : O(n) | (A : M(n)) ∈ SO(n) } : Set (O(n))) =
      { A : O(n) | 0 < (A : M(n)).det } := by
  -- Compare the two subsets pointwise using the determinant-positivity characterization.
  ext A
  exact mem_specialOrthogonalGroup_iff_det_pos n A

/-- Helper for Example 7.28: the canonical inclusion `SO(n) → O(n)`. -/
def specialOrthogonalToOrthogonal (n : ℕ) : SO(n) →* O(n) where
  toFun A := ⟨A.1, (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Helper for Example 7.28: the determinant-one subgroup of `O(n)` cut out by `SO(n)`. -/
def specialOrthogonalSubgroupInOrthogonalGroup (n : ℕ) : Subgroup (O(n)) :=
  (⊤ : Subgroup (SO(n))).map (specialOrthogonalToOrthogonal n)

/-- Helper for Example 7.28: membership in the subgroup copy inside `O(n)` is exactly
special-orthogonal membership of the underlying matrix. -/
theorem mem_specialOrthogonalSubgroupInOrthogonalGroup_iff (n : ℕ) (A : O(n)) :
    A ∈ specialOrthogonalSubgroupInOrthogonalGroup n ↔ (A : M(n)) ∈ SO(n) := by
  constructor
  · rintro ⟨A', -, hA'⟩
    change specialOrthogonalToOrthogonal n A' = A at hA'
    subst hA'
    exact A'.property
  · intro hA
    refine ⟨⟨(A : M(n)), hA⟩, by simp, ?_⟩
    ext
    rfl

/-- Helper for Example 7.28: the determinant-one copy of `SO(n)` inside `O(n)`. -/
abbrev specialOrthogonalSubtypeInOrthogonalGroup (n : ℕ) :=
  ↥(specialOrthogonalSubgroupInOrthogonalGroup n)

section LieGroupStatement

variable (n : ℕ)

local notation "Eₒ" => EuclideanSpace ℝ (Fin (n * (n - 1) / 2))
local notation "Iₒ" => 𝓘(ℝ, Eₒ)

/-- Helper for Example 7.28: with the intrinsic `n (n - 1) / 2`-dimensional smooth structure on
`O(n)` from Example 7.27, the determinant-one embedded subgroup inside `O(n)` carries the induced
Lie-group structure from Proposition 7.11. -/
theorem specialOrthogonalSubtypeInOrthogonalGroup_lieGroup
    [ChartedSpace Eₒ (O(n))]
    [LieGroup Iₒ (⊤ : WithTop ℕ∞) (O(n))]
    [ChartedSpace Eₒ (specialOrthogonalSubtypeInOrthogonalGroup n)]
    [IsManifold Iₒ ∞ (specialOrthogonalSubtypeInOrthogonalGroup n)]
    [IsEmbeddedSubmanifold
      Iₒ
      Iₒ
      (specialOrthogonalSubgroupInOrthogonalGroup n : Set (O(n)))] :
    LieGroup Iₒ (⊤ : WithTop ℕ∞) (specialOrthogonalSubtypeInOrthogonalGroup n) := sorry

/-- Example 7.28 (4): with the intrinsic `n (n - 1) / 2`-dimensional smooth structure on `O(n)`
from Example 7.27, if the canonical owner `SO(n)` is smoothly identified with its determinant-one
embedded copy inside `O(n)`, then `SO(n)` carries the induced Lie-group structure. -/
theorem specialOrthogonalGroup_lieGroup
    [ChartedSpace Eₒ (SO(n))]
    [IsManifold Iₒ ∞ (SO(n))]
    [ChartedSpace Eₒ (specialOrthogonalSubtypeInOrthogonalGroup n)]
    [LieGroup Iₒ (⊤ : WithTop ℕ∞) (specialOrthogonalSubtypeInOrthogonalGroup n)]
    (e : SO(n) ≃* specialOrthogonalSubtypeInOrthogonalGroup n)
    (he : ContMDiff Iₒ Iₒ (⊤ : WithTop ℕ∞) e)
    (he_symm : ContMDiff Iₒ Iₒ (⊤ : WithTop ℕ∞) e.symm) :
    LieGroup Iₒ (⊤ : WithTop ℕ∞) (SO(n)) := sorry

end LieGroupStatement

/-- Example 7.28 (5): `SO(n)` is compact. -/
theorem isCompact_specialOrthogonalGroup (n : ℕ) :
    IsCompact (Set.univ : Set (SO(n))) := by
  -- Work with the carrier of `SO(n)` in ambient matrix space and use compactness of `O(n)`.
  rw [Subtype.isCompact_iff]
  have hCompactOrthogonal : IsCompact ((O(n) : Set (M(n)))) := by
    have hCarrier :
        ((O(n) : Set (M(n))) = { A : M(n) | A.transpose * A = 1 }) := by
      ext A
      simpa using (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ (A := A))
    have hClosed : IsClosed ((O(n) : Set (M(n)))) := by
      rw [hCarrier]
      exact isClosed_eq (show Continuous fun A : M(n) ↦ A.transpose * A by fun_prop)
        continuous_const
    have hBounded : Bornology.IsBounded ((O(n) : Set (M(n)))) := by
      refine isBounded_iff_forall_norm_le.2 ⟨1, ?_⟩
      intro A hA
      rw [Matrix.norm_le_iff zero_le_one]
      intro i j
      have hOrth : A.transpose * A = 1 := by
        simpa using (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ (A := A)).mp hA
      have hDiag : ∑ k : Fin n, A k j * A k j = 1 := by
        have hEntry := congrArg (fun X : M(n) ↦ X j j) hOrth
        simpa [Matrix.mul_apply] using hEntry
      have hTerm :
          A i j * A i j ≤ ∑ k : Fin n, A k j * A k j := by
        simpa using
          (Finset.single_le_sum
            (f := fun k : Fin n ↦ A k j * A k j)
            (fun k _hk ↦ by simpa [pow_two] using sq_nonneg (A k j))
            (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      have hSq : (A i j) ^ 2 ≤ 1 := by
        nlinarith [hTerm, hDiag]
      have hAbs : |A i j| ≤ 1 := by
        exact (sq_le_one_iff_abs_le_one (A i j)).mp hSq
      simpa [Real.norm_eq_abs] using hAbs
    simpa [Set.image_univ, Subtype.range_coe] using
      Metric.isCompact_of_isClosed_isBounded hClosed hBounded
  have hClosedDetOne : IsClosed { A : M(n) | A.det = 1 } := by
    exact isClosed_eq (show Continuous fun A : M(n) ↦ A.det by fun_prop) continuous_const
  have hCarrier :
      ((SO(n) : Set (M(n))) = ((O(n) : Set (M(n))) ∩ { A : M(n) | A.det = 1 })) := by
    ext A
    simp [Matrix.mem_specialOrthogonalGroup_iff]
  -- The special orthogonal group is a closed subset of the compact orthogonal group.
  simpa [Set.image_univ, Subtype.range_coe, hCarrier] using
    hCompactOrthogonal.inter_right hClosedDetOne
