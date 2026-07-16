import StacksProject_2024.stacks_project.Chap10.Lemma_10_55_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u v

section ProjectiveGrothendieckGroup

variable (R : Type u) [CommRing R]

variable [IsLocalRing R]

/-- The integer-valued rank of a finitely generated projective `R`-module. -/
private abbrev projectiveGrothendieckGroup_rank (M : FiniteProjectiveModuleCat R) : ℤ :=
  (Module.finrank R M.obj : ℤ)

-- Proof sketch: projective modules are flat, and `Module.free_of_flat_of_isLocalRing` upgrades a
-- finite flat module over a local ring to a free module.
/-- Lemma 10.55.8 (1): every finite projective module over a local ring is free. -/
theorem finite_projective_module_free_of_isLocalRing
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Free R M := sorry

-- Proof sketch: apply `Module.free_of_flat_of_isLocalRing` to identify the terms of the short
-- exact sequence with finite free modules, then use additivity of `Module.finrank` on split short
-- exact sequences.
/-- Rank is additive on short exact sequences of finitely generated projective modules. -/
private theorem projectiveGrothendieckGroup_rank_respects_shortExact
    (S : ShortComplex (FiniteProjectiveModuleCat R))
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    projectiveGrothendieckGroup_rank R S.X₂ =
      projectiveGrothendieckGroup_rank R S.X₁ + projectiveGrothendieckGroup_rank R S.X₃ := sorry

-- Proof sketch: a generator of `modulePropertyK0Relations` comes from a short exact sequence of
-- finite projective modules, and `projectiveGrothendieckGroup_rank_respects_shortExact` sends the
-- corresponding Grothendieck relation to zero. Closure gives the kernel inclusion.
/-- The Grothendieck relations for finite projective modules lie in the kernel of rank. -/
private theorem projectiveGrothendieckGroup_relations_le_ker_rank :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (projectiveGrothendieckGroup_rank R)).ker := sorry

/-- Lemma 10.55.8 (2): the rank function on finitely generated projective `R`-modules descends to
a well-defined homomorphism `K₀(R) → ℤ`. -/
def projectiveGrothendieckGroup_rankMap :
    projectiveGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (projectiveGrothendieckGroup_rank R)
    (projectiveGrothendieckGroup_relations_le_ker_rank R)

-- Proof sketch: `projectiveGrothendieckGroup_rankMap` is the canonical `ModulePropertyK0.lift` of
-- `projectiveGrothendieckGroup_rank`, so on a generator class it evaluates to the rank of that
-- finite projective module.
/-- The rank map sends the class of a finite projective module to its rank. -/
theorem projectiveGrothendieckGroup_rankMap_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_rankMap R
        (projectiveGrothendieckGroupOf R M) =
      (Module.finrank R M.obj : ℤ) := sorry

-- Proof sketch: surjectivity comes from the rank-one free module. Injectivity follows because
-- `finite_projective_module_free_of_isLocalRing` identifies every finite projective module with a
-- finite free module, so its `K₀`-class is determined by its rank.
/-- Lemma 10.55.8 (3): for a local ring, the rank map identifies `K₀(R)` with `ℤ`. -/
theorem projectiveGrothendieckGroup_rankMap_bijective :
    Function.Bijective (projectiveGrothendieckGroup_rankMap R) := sorry

end ProjectiveGrothendieckGroup
