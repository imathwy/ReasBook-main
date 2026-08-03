import Mathlib
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Definition_25_39

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v w

namespace ContinuousLinearMap

variable {H : Type u} {G : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Domain sampling: the owner declarations for the two primitives in this proposition already live
-- upstream as `SetValuedOperator.parallelSum` / `A □ B` and
-- `ContinuousLinearMap.parallelComposition` / `L ▷ A`, so this file keeps only the
-- proposition-level API.

/-- Clause (i) of Proposition 25.42: parallel composition distributes over the operator parallel
sum. -/
theorem parallelComposition_parallelSum
    (L : H →L[ℝ] G) (A B : SetValuedOperator H H) :
    L ▷ (A □ B) = (L ▷ A) □ (L ▷ B) := by
  ext x u
  constructor
  · intro hu
    -- Rewrite the left-hand parallel composition into a witness in `H`.
    rcases (mem_parallelComposition_iff L (A □ B) x u).1 hu with ⟨p, hp, huAB⟩
    rw [SetValuedOperator.mem_parallelSum_iff] at huAB
    -- Split the parallel-sum witness into the two inverse-membership components.
    rcases Set.mem_add.1 huAB with ⟨y, hy, z, hz, hyz⟩
    rw [SetValuedOperator.mem_parallelSum_iff]
    refine Set.mem_add.2 ⟨L y, ?_, L z, ?_, ?_⟩
    · -- The `A`-component becomes membership in `(L ▷ A)⁻¹ u`.
      rw [SetValuedOperator.mem_inverse_iff]
      exact (mem_parallelComposition_iff L A (L y) u).2 ⟨
        y,
        rfl,
        (SetValuedOperator.mem_inverse_iff A (L.adjoint u) y).1 hy⟩
    · -- The `B`-component is handled in the same way.
      rw [SetValuedOperator.mem_inverse_iff]
      exact (mem_parallelComposition_iff L B (L z) u).2 ⟨
        z,
        rfl,
        (SetValuedOperator.mem_inverse_iff B (L.adjoint u) z).1 hz⟩
    · -- Linearity of `L` transports the witness decomposition to the target space.
      calc
        L y + L z = L (y + z) := by symm; exact L.map_add y z
        _ = L p := by rw [hyz]
        _ = x := hp
  · intro hu
    rw [SetValuedOperator.mem_parallelSum_iff] at hu
    -- Decompose the right-hand parallel sum into witnesses for `L ▷ A` and `L ▷ B`.
    rcases Set.mem_add.1 hu with ⟨y, hy, z, hz, hyz⟩
    rw [SetValuedOperator.mem_inverse_iff] at hy hz
    rcases (mem_parallelComposition_iff L A y u).1 hy with ⟨p, hp, hA⟩
    rcases (mem_parallelComposition_iff L B z u).1 hz with ⟨q, hq, hB⟩
    -- Reassemble the two source witnesses into a witness for `L ▷ (A □ B)`.
    refine (mem_parallelComposition_iff L (A □ B) x u).2 ⟨p + q, ?_, ?_⟩
    · calc
        L (p + q) = L p + L q := L.map_add p q
        _ = y + z := by rw [hp, hq]
        _ = x := hyz
    · rw [SetValuedOperator.mem_parallelSum_iff]
      exact Set.mem_add.2 ⟨
        p,
        (SetValuedOperator.mem_inverse_iff A (L.adjoint u) p).2 hA,
        q,
        (SetValuedOperator.mem_inverse_iff B (L.adjoint u) q).2 hB,
        rfl⟩

/-- Clause (ii) of Proposition 25.42: iterated parallel composition along bounded linear maps is
the parallel composition with the composed map. -/
theorem parallelComposition_comp
    (M : G →L[ℝ] K) (L : H →L[ℝ] G) (A : SetValuedOperator H H) :
    M ▷ (L ▷ A) = (M.comp L) ▷ A := by
  ext x u
  constructor
  · intro hu
    -- Unpack the outer and inner parallel-composition witnesses successively.
    rcases (mem_parallelComposition_iff M (L ▷ A) x u).1 hu with ⟨y, hy, huL⟩
    rcases (mem_parallelComposition_iff L A y (M.adjoint u)).1 huL with ⟨z, hz, hA⟩
    -- Route correction: use the explicit witness `z` and `adjoint_comp` instead of unfolding
    -- the operator definitions.
    refine (mem_parallelComposition_iff (M.comp L) A x u).2 ⟨z, ?_, ?_⟩
    · calc
        (M.comp L) z = M (L z) := rfl
        _ = M y := by rw [hz]
        _ = x := hy
    · simpa [ContinuousLinearMap.adjoint_comp] using hA
  · intro hu
    -- Normalize the composed-map witness and then rebuild the nested parallel composition.
    rcases (mem_parallelComposition_iff (M.comp L) A x u).1 hu with ⟨z, hz, hA⟩
    refine (mem_parallelComposition_iff M (L ▷ A) x u).2 ⟨L z, ?_, ?_⟩
    · simpa using hz
    · refine (mem_parallelComposition_iff L A (L z) (M.adjoint u)).2 ⟨z, rfl, ?_⟩
      simpa [ContinuousLinearMap.adjoint_comp] using hA

/-- Proposition 25.42. Parallel composition distributes over parallel sum, and iterated parallel
composition is parallel composition with the composed map. -/
theorem parallelComposition_parallelSum_and_comp
    (L : H →L[ℝ] G) (M : G →L[ℝ] K) (A B : SetValuedOperator H H) :
    L ▷ (A □ B) = (L ▷ A) □ (L ▷ B) ∧ M ▷ (L ▷ A) = (M.comp L) ▷ A := by
  constructor
  · -- The first clause is exactly the previously established distribution theorem.
    exact parallelComposition_parallelSum L A B
  · -- The second clause is exactly the previously established composition theorem.
    exact parallelComposition_comp M L A

end ContinuousLinearMap
