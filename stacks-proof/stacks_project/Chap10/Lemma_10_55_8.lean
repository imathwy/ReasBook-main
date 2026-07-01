import stacks_project.Chap10.Lemma_10_55_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

universe u v

section ProjectiveGrothendieckGroup

variable (R : Type u) [CommRing R]

variable [IsLocalRing R]

/-- Helper for Lemma 10.55.8: the finite projective subcategory in the same universe as `R`. -/
private abbrev finite_projective_module_cat_same_universe :=
  FiniteProjectiveModuleCat.{u, u} R

/-- Helper for Lemma 10.55.8: the Grothendieck group of same-universe finite projective modules.
-/
private abbrev projective_grothendieck_group_same_universe :=
  projectiveGrothendieckGroup.{u, u} R

/-- The integer-valued rank of a finitely generated projective `R`-module. -/
private abbrev projectiveGrothendieckGroup_rank (M : FiniteProjectiveModuleCat R) : ℤ :=
  (Module.finrank R M.obj : ℤ)

-- Proof sketch: projective modules are flat, and `Module.free_of_flat_of_isLocalRing` upgrades a
-- finite flat module over a local ring to a free module.
/-- Lemma 10.55.8 (1): every finite projective module over a local ring is free. -/
theorem finite_projective_module_free_of_isLocalRing
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Free R M := by
  -- Projective modules are flat, and finite flat modules over a local ring are free.
  let _ : Module.Flat R M := inferInstance
  exact Module.free_of_flat_of_isLocalRing

-- Proof sketch: apply `Module.free_of_flat_of_isLocalRing` to identify the terms of the short
-- exact sequence with finite free modules, then use additivity of `Module.finrank` on split short
-- exact sequences.
/-- Rank is additive on short exact sequences of finitely generated projective modules. -/
private theorem projectiveGrothendieckGroup_rank_respects_shortExact
    (S : ShortComplex (FiniteProjectiveModuleCat R))
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    projectiveGrothendieckGroup_rank R S.X₂ =
      projectiveGrothendieckGroup_rank R S.X₁ + projectiveGrothendieckGroup_rank R S.X₃ := by
  let T : ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  have hT : T.ShortExact := by
    simpa [T] using hS
  let _ : Module.Finite R T.X₁ := by
    simpa [T] using (inferInstance : Module.Finite R S.X₁.obj)
  let _ : Module.Finite R T.X₃ := by
    simpa [T] using (inferInstance : Module.Finite R S.X₃.obj)
  let _ : Module.Projective R T.X₁ := by
    simpa [T] using (inferInstance : Module.Projective R S.X₁.obj)
  let _ : Module.Projective R T.X₃ := by
    simpa [T] using (inferInstance : Module.Projective R S.X₃.obj)
  let _ : Module.Free R T.X₁ := finite_projective_module_free_of_isLocalRing (R := R)
  let _ : Module.Free R T.X₃ := finite_projective_module_free_of_isLocalRing (R := R)
  have hfinrank :
      Module.finrank R T.X₂ = Module.finrank R T.X₁ + Module.finrank R T.X₃ := by
    simpa [T] using
      (ModuleCat.free_shortExact_finrank_add (R := R) (S := T) hT rfl rfl)
  -- Cast the finite-rank equality from `ℕ` to `ℤ` to match the generator-level invariant.
  simpa [projectiveGrothendieckGroup_rank, T, Nat.cast_add] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfinrank

-- Proof sketch: a generator of `modulePropertyK0Relations` comes from a short exact sequence of
-- finite projective modules, and `projectiveGrothendieckGroup_rank_respects_shortExact` sends the
-- corresponding Grothendieck relation to zero. Closure gives the kernel inclusion.
/-- The Grothendieck relations for finite projective modules lie in the kernel of rank. -/
private theorem projectiveGrothendieckGroup_relations_le_ker_rank :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (projectiveGrothendieckGroup_rank R)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (projectiveGrothendieckGroup_rank R)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  have hrank :
      projectiveGrothendieckGroup_rank R S.X₂ =
        projectiveGrothendieckGroup_rank R S.X₁ + projectiveGrothendieckGroup_rank R S.X₃ :=
    projectiveGrothendieckGroup_rank_respects_shortExact (R := R) S hS
  -- Rewrite by rank additivity and normalize the resulting integer identity.
  rw [hrank]
  abel

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
      (Module.finrank R M.obj : ℤ) := by
  -- The descended map agrees with the original generator-level rank functional.
  simpa [projectiveGrothendieckGroup_rank] using
    ModulePropertyK0.lift_of R
      (projectiveGrothendieckGroup_rank R)
      (projectiveGrothendieckGroup_relations_le_ker_rank R)
      M

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the zero module is finitely generated and projective. -/
private theorem finite_projective_module_property_zero :
    finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
  exact ⟨inferInstance, inferInstance⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the direct product of two finitely generated projective modules is
again finitely generated and projective. -/
private theorem finite_projective_module_property_prod
    (M N : ModuleCat R)
    (hM : finiteProjectiveModuleProperty R M)
    (hN : finiteProjectiveModuleProperty R N) :
    finiteProjectiveModuleProperty R (ModuleCat.of R (M × N)) := by
  let _ : Module.Finite R M := hM.1
  let _ : Module.Projective R M := hM.2
  let _ : Module.Finite R N := hN.1
  let _ : Module.Projective R N := hN.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 10.55.8: the rank-one free module as an object of the finite projective
subcategory. -/
private abbrev rank_one_finite_projective_module :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R R, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 10.55.8: the standard free module of rank `n` as an object of the finite
projective subcategory. -/
private abbrev standard_free_finite_projective_module (n : ℕ) :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R (Fin n → R), ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 10.55.8: the direct product of two finite projective modules as an object of
the finite projective subcategory. -/
private abbrev prod_finite_projective_module
    (M N : finite_projective_module_cat_same_universe (R := R)) :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R (M.obj × N.obj),
    finite_projective_module_property_prod (R := R) M.obj N.obj M.property N.property⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the rank-zero standard free module has trivial Grothendieck class. -/
private theorem standard_free_zero_class_eq_zero :
    projectiveGrothendieckGroupOf R
      (standard_free_finite_projective_module (R := R) 0) = 0 := by
  haveI : Subsingleton (Fin 0 → R) := inferInstance
  -- The rank-zero free module is subsingleton, so its class agrees with the zero object.
  simpa using
    (ModulePropertyK0.of_subsingleton (R := R) (P := finiteProjectiveModuleProperty R)
      (finite_projective_module_property_zero (R := R))
      (standard_free_finite_projective_module (R := R) 0))

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: `R ⊕ R^n` is canonically the standard free module of rank `n + 1`.
-/
private def standard_free_succ_iso_prod (n : ℕ) :
    prod_finite_projective_module (R := R)
      (rank_one_finite_projective_module (R := R))
      (standard_free_finite_projective_module (R := R) n) ≅
        standard_free_finite_projective_module (R := R) n.succ :=
  ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
    (LinearEquiv.toModuleIso (Fin.consLinearEquiv R (fun _ : Fin n.succ ↦ R)))

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the Grothendieck class of a product of finite projective modules is
the sum of the classes of its two factors. -/
private theorem projectiveGrothendieckGroupOf_prod
    (M N : finite_projective_module_cat_same_universe (R := R)) :
    projectiveGrothendieckGroupOf R (prod_finite_projective_module (R := R) M N) =
      projectiveGrothendieckGroupOf R M + projectiveGrothendieckGroupOf R N := by
  let P := finiteProjectiveModuleProperty R
  let S : ShortComplex P.FullSubcategory :=
    { X₁ := M
      X₂ := prod_finite_projective_module (R := R) M N
      X₃ := N
      f := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl R M.obj N.obj))
      g := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd R M.obj N.obj))
      zero := by
        apply ObjectProperty.hom_ext
        ext x
        rfl }
  let T : ShortComplex (ModuleCat R) :=
    { X₁ := M.obj
      X₂ := ModuleCat.of R (M.obj × N.obj)
      X₃ := N.obj
      f := ModuleCat.ofHom (LinearMap.inl R M.obj N.obj)
      g := ModuleCat.ofHom (LinearMap.snd R M.obj N.obj)
      zero := by
        ext x
        rfl }
  have hT : T.ShortExact := by
    -- The standard split sequence `0 → M → M × N → N → 0` is short exact in `ModuleCat`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        ext
        · rfl
        · simpa using hx.symm
      · rintro ⟨m, rfl⟩
        rfl
    · intro m m' hmm'
      exact congrArg Prod.fst hmm'
    · intro n
      refine ⟨(0, n), ?_⟩
      rfl
  have hS : (S.map P.ι).ShortExact := by
    -- Forgetting the full-subcategory structure recovers the split short exact sequence above.
    simpa [S, T, prod_finite_projective_module] using hT
  -- Apply the defining short exact sequence relation in `K₀(R)`.
  simpa [S, prod_finite_projective_module] using
    ModulePropertyK0.of_shortExact (R := R) (P := P) S hS

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the class of the standard free module of rank `n` is `n` times the
class of the rank-one free module. -/
private theorem free_fin_class_eq_zsmul_rank_one (n : ℕ) :
    projectiveGrothendieckGroupOf R
      ((standard_free_finite_projective_module (R := R) n :
        finite_projective_module_cat_same_universe (R := R))) =
        n •
          (projectiveGrothendieckGroupOf R
            ((rank_one_finite_projective_module (R := R) :
              finite_projective_module_cat_same_universe (R := R))) :
            projective_grothendieck_group_same_universe (R := R)) := by
  -- Route correction: follow the source proof via the split sequence
  -- `0 → R → R ⊕ R^n → R^n → 0`, rather than hiding the successor step in ad hoc rewriting.
  let η : projective_grothendieck_group_same_universe (R := R) :=
    projectiveGrothendieckGroupOf R
      ((rank_one_finite_projective_module (R := R) :
        finite_projective_module_cat_same_universe (R := R)))
  induction n with
  | zero =>
      -- Start the recursion with the trivial class of the zero free module.
      simpa [η] using standard_free_zero_class_eq_zero (R := R)
  | succ n ih =>
      have hcons :
          projectiveGrothendieckGroupOf R
              ((prod_finite_projective_module (R := R)
                (rank_one_finite_projective_module (R := R))
                (standard_free_finite_projective_module (R := R) n) :
                  finite_projective_module_cat_same_universe (R := R))) =
            projectiveGrothendieckGroupOf R
              ((standard_free_finite_projective_module (R := R) n.succ :
                finite_projective_module_cat_same_universe (R := R))) := by
        -- Transport the product decomposition across the canonical free-module isomorphism.
        exact ModulePropertyK0.of_iso (R := R) (P := finiteProjectiveModuleProperty R)
          (finite_projective_module_property_zero (R := R))
          (standard_free_succ_iso_prod (R := R) n)
      calc
        projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) n.succ :
              finite_projective_module_cat_same_universe (R := R))) =
            projectiveGrothendieckGroupOf R
              ((prod_finite_projective_module (R := R)
                (rank_one_finite_projective_module (R := R))
                (standard_free_finite_projective_module (R := R) n) :
                  finite_projective_module_cat_same_universe (R := R))) := by
          simpa using hcons.symm
        _ = projectiveGrothendieckGroupOf R
              ((rank_one_finite_projective_module (R := R) :
                finite_projective_module_cat_same_universe (R := R))) +
              projectiveGrothendieckGroupOf R
                ((standard_free_finite_projective_module (R := R) n :
                  finite_projective_module_cat_same_universe (R := R))) := by
          exact projectiveGrothendieckGroupOf_prod (R := R)
            ((rank_one_finite_projective_module (R := R) :
              finite_projective_module_cat_same_universe (R := R)))
            ((standard_free_finite_projective_module (R := R) n :
              finite_projective_module_cat_same_universe (R := R)))
        _ = η + (n : ℤ) • η := by
          simpa [η, natCast_zsmul] using congrArg
            (fun x : projective_grothendieck_group_same_universe (R := R) ↦ η + x) ih
        _ = n.succ • η := by
          rw [succ_nsmul, natCast_zsmul, add_comm]

-- Proof sketch: surjectivity comes from the rank-one free module. Injectivity follows because
-- `finite_projective_module_free_of_isLocalRing` identifies every finite projective module with a
-- finite free module, so its `K₀`-class is determined by its rank.
/-- Lemma 10.55.8 (3): for a local ring, the rank map identifies `K₀(R)` with `ℤ`. -/
theorem projectiveGrothendieckGroup_rankMap_bijective :
    Function.Bijective (projectiveGrothendieckGroup_rankMap.{u, u} R) := by
  let η : projective_grothendieck_group_same_universe (R := R) :=
    projectiveGrothendieckGroupOf R
      ((rank_one_finite_projective_module (R := R) :
        finite_projective_module_cat_same_universe (R := R)))
  let σ : ℤ →+ projective_grothendieck_group_same_universe (R := R) := zmultiplesHom _ η
  have hright :
      (projectiveGrothendieckGroup_rankMap R).comp σ = AddMonoidHom.id ℤ := by
    apply AddMonoidHom.ext_int
    -- On `1`, the inverse candidate picks the class of the rank-one free module.
    simpa [AddMonoidHom.comp_apply, σ, η] using
      (projectiveGrothendieckGroup_rankMap_apply_of (R := R)
        (rank_one_finite_projective_module (R := R)))
  have hleft :
      σ.comp (projectiveGrothendieckGroup_rankMap R) =
        AddMonoidHom.id (projective_grothendieck_group_same_universe (R := R)) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro M
    let _ : Module.Free R M.obj := finite_projective_module_free_of_isLocalRing (R := R)
    let e : M.obj ≃ₗ[R] (Fin (Module.finrank R M.obj) → R) :=
      LinearEquiv.ofFinrankEq (R := R) M.obj (Fin (Module.finrank R M.obj) → R) (by simp)
    have hclass :
        projectiveGrothendieckGroupOf R M =
          projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) (Module.finrank R M.obj) :
              finite_projective_module_cat_same_universe (R := R))) := by
      -- Every finite projective module over a local ring is isomorphic to a standard free module
      -- of the same rank.
      exact ModulePropertyK0.of_iso (R := R) (P := finiteProjectiveModuleProperty R)
        (finite_projective_module_property_zero (R := R))
        (ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
          (LinearEquiv.toModuleIso e))
    calc
      (σ.comp (projectiveGrothendieckGroup_rankMap R))
          (projectiveGrothendieckGroupOf R M) =
          σ (Module.finrank R M.obj : ℤ) := by
        rw [AddMonoidHom.comp_apply, projectiveGrothendieckGroup_rankMap_apply_of]
      _ = (Module.finrank R M.obj : ℤ) • η := by
        simp [σ]
      _ = projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) (Module.finrank R M.obj) :
              finite_projective_module_cat_same_universe (R := R))) := by
        symm
        simpa [η, natCast_zsmul] using
          (free_fin_class_eq_zsmul_rank_one (R := R) (Module.finrank R M.obj))
      _ = projectiveGrothendieckGroupOf R M := by
        simpa using hclass.symm
  constructor
  · intro x y hxy
    have hx : σ (projectiveGrothendieckGroup_rankMap R x) = x := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft x
    have hy : σ (projectiveGrothendieckGroup_rankMap R y) = y := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft y
    rw [← hx, ← hy, hxy]
  · intro z
    refine ⟨σ z, ?_⟩
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright z

end ProjectiveGrothendieckGroup
