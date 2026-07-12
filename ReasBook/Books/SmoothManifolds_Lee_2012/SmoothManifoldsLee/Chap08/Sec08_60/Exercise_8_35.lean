import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u𝕜 u𝔤 u𝔥

section

open Module

variable {𝕜 : Type u𝕜} [Field 𝕜]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] [FiniteDimensional 𝕜 𝔤]
variable {𝔥 : Type u𝔥} [LieRing 𝔥] [LieAlgebra 𝕜 𝔥]

-- Semantic search note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was checked directly against mathlib's `LieHom` API and local repository precedent.

/-- Exercise 8.35: a linear map between finite-dimensional Lie algebras is a Lie algebra
homomorphism if and only if it preserves brackets on some basis of the source Lie algebra. -/
theorem linearMap_is_lieHom_iff_preserves_bracket_on_basis (A : 𝔤 →ₗ[𝕜] 𝔥) :
    (∀ x y : 𝔤, A ⁅x, y⁆ = ⁅A x, A y⁆) ↔
      ∃ (ι : Type u𝔤) (b : Basis ι 𝕜 𝔤),
        ∀ i j : ι,
          A ⁅b i, b j⁆ = ⁅A (b i), A (b j)⁆ := by
  constructor
  · intro hA
    refine ⟨Module.Free.ChooseBasisIndex 𝕜 𝔤, Module.Free.chooseBasis 𝕜 𝔤, fun i j ↦ hA _ _⟩
  · rintro ⟨ι, b, hb⟩ x y
    let _ : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    calc
      A ⁅x, y⁆ = A ⁅∑ i, b.repr x i • b i, ∑ j, b.repr y j • b j⁆ := by
        rw [b.sum_repr, b.sum_repr]
      _ = A (∑ i, ∑ j, (b.repr x i * b.repr y j) • ⁅b i, b j⁆) := by
        simpa [smul_lie, lie_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          congrArg A
            (sum_lie_sum Finset.univ Finset.univ
              (fun i ↦ b.repr x i • b i)
              (fun j ↦ b.repr y j • b j))
      _ = ∑ i, ∑ j, (b.repr x i * b.repr y j) • A ⁅b i, b j⁆ := by
        simp_rw [map_sum, map_smul]
      _ = ∑ i, ∑ j, (b.repr x i * b.repr y j) • ⁅A (b i), A (b j)⁆ := by
        simp_rw [hb]
      _ = ⁅∑ i, b.repr x i • A (b i), ∑ j, b.repr y j • A (b j)⁆ := by
        simpa [smul_lie, lie_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (sum_lie_sum Finset.univ Finset.univ
            (fun i ↦ b.repr x i • A (b i))
            (fun j ↦ b.repr y j • A (b j))).symm
      _ = ⁅A (∑ i, b.repr x i • b i), A (∑ j, b.repr y j • b j)⁆ := by
        simp_rw [map_sum, map_smul]
      _ = ⁅A x, A y⁆ := by
        rw [b.sum_repr, b.sum_repr]

end
