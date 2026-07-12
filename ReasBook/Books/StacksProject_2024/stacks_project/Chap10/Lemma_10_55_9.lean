import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.Lemma_10_55_7
import StacksProject_2024.Chap10.Lemma_10_55_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section Comparison

variable (R : Type u) [CommRing R]

-- Proof sketch: over a local ring, a finite projective module is free by
-- `Module.free_of_flat_of_isLocalRing`, so mathlib's
-- `Module.length_of_free_of_finite` identifies its length with its finite rank times
-- `length_R(R)`.
private theorem finiteProjective_length_eq_rank_mul_ring_length [IsArtinianRing R]
    [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ((Module.length R M).toNat : ℤ) =
      ((Module.length R R).toNat : ℤ) * Module.finrank R M := by
  let _ : Module.Free R M := Module.free_of_flat_of_isLocalRing
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_of_free_of_finite R M)

-- Proof sketch: evaluate both composites on a class `[P]` of a finite projective module. The left
-- side becomes the module length of `P` in `K'_0(R)`, while the right side is
-- `length_R(R) * rank_R(P)`; these agree by `finiteProjective_length_eq_rank_mul_ring_length`, and
-- the quotient presentation of `K₀(R)` then gives the equality for every element.
/-- Lemma 10.55.9: for a local Artinian ring `R`, the canonical comparison map `K₀(R) → K'_0(R)`
fits into the commutative square with vertical maps `rank_R` and `length_R`, where the lower
horizontal map is multiplication by `length_R(R)`. -/
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length
    [IsArtinianRing R] [IsLocalRing R] :
    (finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)) =
      (AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R) := by
  refine QuotientAddGroup.addMonoidHom_ext _ ?_
  ext M
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ModulePropertyK0.map_of,
    finiteGrothendieckGroup_lengthMap_apply_of]
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  simpa [projectiveGrothendieckGroupOf, AddMonoidHom.comp_apply] using
    (finiteProjective_length_eq_rank_mul_ring_length R M.obj)

/-- On an element of `K₀(R)`, Lemma 10.55.9 says that taking length after comparison to `K'_0(R)`
agrees with multiplying rank by `length_R(R)`. -/
@[simp]
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply
    [IsArtinianRing R] [IsLocalRing R] (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_lengthMap R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      ((Module.length R R).toNat : ℤ) * projectiveGrothendieckGroup_rankMap R x := by
  simpa using DFunLike.congr_fun
    (projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length R) x

end Comparison
