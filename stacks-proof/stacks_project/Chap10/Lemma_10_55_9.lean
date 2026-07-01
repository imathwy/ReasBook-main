import stacks_project.Chap10.Lemma_10_55_6
import stacks_project.Chap10.Lemma_10_55_7
import stacks_project.Chap10.Lemma_10_55_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section Comparison

variable (R : Type u) [CommRing R]

/-- Helper for Lemma 10.55.9: a finite projective module over a local Artinian ring has length
equal to its rank times the length of the ring. -/
private theorem finiteProjective_length_eq_rank_mul_ring_length [IsArtinianRing R]
    [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ((Module.length R M).toNat : ℤ) =
      ((Module.length R R).toNat : ℤ) * Module.finrank R M := by
  -- Use Lemma 10.55.8 to replace the finite projective module by a finite free module.
  let _ : Module.Free R M := finite_projective_module_free_of_isLocalRing (R := R)
  -- Convert the `ℕ∞`-valued free-length formula into the integer-valued statement used here.
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_of_free_of_finite R M)

/-- Helper for Lemma 10.55.9: the left composite of the comparison square sends a generator of
`K₀(R)` to the length of the underlying finite module. -/
private theorem comparison_length_on_generator [IsArtinianRing R]
    (M : FiniteProjectiveModuleCat R) :
    ((finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)))
      (projectiveGrothendieckGroupOf R M) =
        ((Module.length R M.obj).toNat : ℤ) := by
  -- The comparison map preserves generator classes, and the inclusion into finitely generated
  -- modules does not change the underlying module whose length is measured.
  rw [AddMonoidHom.comp_apply, ModulePropertyK0.map_of, finiteGrothendieckGroup_lengthMap_apply_of]
  rfl

/-- Helper for Lemma 10.55.9: the right composite of the comparison square sends a generator of
`K₀(R)` to `length_R(R)` times the rank of that generator. -/
private theorem comparison_rank_on_generator [IsArtinianRing R] [IsLocalRing R]
    (M : FiniteProjectiveModuleCat R) :
    ((AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R))
      (projectiveGrothendieckGroupOf R M) =
        ((Module.length R R).toNat : ℤ) * Module.finrank R M.obj := by
  -- The rank map evaluates on a generator by the rank of the corresponding projective module.
  rw [AddMonoidHom.comp_apply, projectiveGrothendieckGroup_rankMap_apply_of]
  rfl

/-- Lemma 10.55.9: for a local Artinian ring `R`, the canonical comparison map `K₀(R) → K'_0(R)`
fits into the commutative square with vertical maps `rank_R` and `length_R`, where the lower
horizontal map is multiplication by `length_R(R)`. -/
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length
    [IsArtinianRing R] [IsLocalRing R] :
    (finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)) =
      (AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro M
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  -- Both composites are determined on generator classes, and the source proof reduces exactly to
  -- the free-module length computation from the previous helper.
  calc
    ((finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)))
        (projectiveGrothendieckGroupOf R M) =
          ((Module.length R M.obj).toNat : ℤ) := by
      exact comparison_length_on_generator (R := R) M
    _ = ((Module.length R R).toNat : ℤ) * Module.finrank R M.obj := by
      exact finiteProjective_length_eq_rank_mul_ring_length (R := R) M.obj
    _ = ((AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R))
        (projectiveGrothendieckGroupOf R M) := by
      simpa using (comparison_rank_on_generator (R := R) M).symm

/-- On an element of `K₀(R)`, Lemma 10.55.9 says that taking length after comparison to `K'_0(R)`
agrees with multiplying rank by `length_R(R)`. -/
@[simp]
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply
    [IsArtinianRing R] [IsLocalRing R] (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_lengthMap R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      ((Module.length R R).toNat : ℤ) * projectiveGrothendieckGroup_rankMap R x := by
  -- Evaluate the homomorphism identity from Lemma 10.55.9 at the chosen class `x`.
  simpa using DFunLike.congr_fun
    (projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length R) x

end Comparison
