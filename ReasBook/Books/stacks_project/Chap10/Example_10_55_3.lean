import stacks_project.Chap10.Lemma_10_55_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TensorProduct

universe u

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

private theorem finiteProjectiveModuleCat_genericRank_eq_rank
    (M : FiniteProjectiveModuleCat R) :
    (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ) =
      Module.finrank R M.obj := by
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  let _ : Module.IsTorsionFree R M.obj := by
    obtain ⟨n, _, g, _, hg, _⟩ := Module.Finite.exists_comp_eq_id_of_projective R M.obj
    exact hg.moduleIsTorsionFree g fun r m ↦ by simp
  let _ : Module.Free R M.obj := Module.free_of_finite_type_torsion_free'
  norm_num [Module.finrank_tensorProduct]

-- The generic-rank functional on finitely generated `R`-modules, computed after base change to
-- the fraction field.
private noncomputable def finiteGrothendieckGroup_pidRank (M : FGModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

-- Proof sketch: the structure theorem for finitely generated modules over a principal ideal domain
-- reduces a Grothendieck relation to free and torsion summands; the generic rank vanishes on the
-- torsion part and is additive on short exact sequences, so every relation maps to zero.
private theorem finiteGrothendieckGroup_relations_le_ker_pidRank :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift (finiteGrothendieckGroup_pidRank R)).ker := by
  sorry

/-- Example 10.55.3: for a principal ideal domain `R`, the generic-rank functional on finite
`R`-modules descends to the canonical homomorphism `K'_0(R) → ℤ`. -/
def finiteGrothendieckGroup_pidRankMap : finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (finiteGrothendieckGroup_pidRank R)
    (finiteGrothendieckGroup_relations_le_ker_pidRank R)

/-- The PID generic-rank map sends the class of a finite module to its generic rank. -/
theorem finiteGrothendieckGroup_pidRankMap_apply_of
    (M : FGModuleCat R) :
    finiteGrothendieckGroup_pidRankMap R
        (finiteGrothendieckGroupOf R M) =
      (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ) := by
  simpa using ModulePropertyK0.lift_of R
    (finiteGrothendieckGroup_pidRank R)
    (finiteGrothendieckGroup_relations_le_ker_pidRank R)
    M

/-- For a principal ideal domain `R`, the generic-rank map on `K'_0(R)` is bijective. -/
-- Proof sketch: surjectivity is realized by the class of a free rank-one module. Injectivity
-- follows from the structure theorem for finitely generated modules over a principal ideal domain,
-- which shows that the Grothendieck class is determined by generic rank.
theorem finiteGrothendieckGroup_pidRankMap_bijective :
    Function.Bijective (finiteGrothendieckGroup_pidRankMap R) := by
  sorry

/-- For a principal ideal domain `R`, the rank functional on finitely generated projective
`R`-modules is obtained by composing the canonical comparison map `K₀(R) → K'_0(R)` with the
generic-rank homomorphism `K'_0(R) → ℤ`. -/
def projectiveGrothendieckGroup_pidRankMap : projectiveGrothendieckGroup R →+ ℤ :=
  (finiteGrothendieckGroup_pidRankMap R).comp
    (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R))

/-- The PID rank map sends the class of a finite projective module to its rank. -/
theorem projectiveGrothendieckGroup_pidRankMap_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_pidRankMap R
        (projectiveGrothendieckGroupOf R M) =
      (Module.finrank R M.obj : ℤ) := by
  rw [projectiveGrothendieckGroup_pidRankMap, AddMonoidHom.comp_apply, ModulePropertyK0.map_of,
    finiteGrothendieckGroup_pidRankMap_apply_of]
  exact finiteProjectiveModuleCat_genericRank_eq_rank R M

/-- For a principal ideal domain `R`, the rank map on `K₀(R)` is bijective. -/
-- Proof sketch: finite projective modules over a principal ideal domain are free, so the
-- Grothendieck class of a finite projective module is determined by its rank, and every integer is
-- realized by the difference of free-module classes.
theorem projectiveGrothendieckGroup_pidRankMap_bijective :
    Function.Bijective (projectiveGrothendieckGroup_pidRankMap R) := by
  sorry

/-- For a principal ideal domain `R`, the rank map identifies the Grothendieck group `K₀(R)` of
finitely generated projective `R`-modules with `ℤ`. -/
noncomputable def projectiveGrothendieckGroup_pidEquiv : projectiveGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (projectiveGrothendieckGroup_pidRankMap R)
    (projectiveGrothendieckGroup_pidRankMap_bijective R)

/-- The additive equivalence `K₀(R) ≃+ ℤ` acts by the PID rank map. -/
theorem projectiveGrothendieckGroup_pidEquiv_apply
    (x : projectiveGrothendieckGroup R) :
    projectiveGrothendieckGroup_pidEquiv R x =
      projectiveGrothendieckGroup_pidRankMap R x := rfl

/-- For a principal ideal domain `R`, the structure theorem for finitely generated modules
identifies `K'_0(R)` with `ℤ`; in this Noetherian setting `K'_0(R)` is modeled canonically here by
finite `R`-modules. -/
noncomputable def finiteGrothendieckGroup_pidEquiv : finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (finiteGrothendieckGroup_pidRankMap R)
    (finiteGrothendieckGroup_pidRankMap_bijective R)

/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the PID generic-rank map. -/
theorem finiteGrothendieckGroup_pidEquiv_apply
    (x : finiteGrothendieckGroup R) :
    finiteGrothendieckGroup_pidEquiv R x =
      finiteGrothendieckGroup_pidRankMap R x := rfl

/-- On a principal ideal domain, the canonical comparison map `K₀(R) → K'_0(R)` commutes with the
rank and generic-rank homomorphisms to `ℤ`. -/
theorem projectiveGrothendieckGroup_comparison_commutes_with_pidRank :
    (finiteGrothendieckGroup_pidRankMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)) =
      projectiveGrothendieckGroup_pidRankMap R := by
  rfl

/-- On an element of `K₀(R)`, the generic rank after comparison to `K'_0(R)` agrees with the
rank in `K₀(R)`. -/
@[simp] theorem projectiveGrothendieckGroup_comparison_commutes_with_pidRank_apply
    (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_pidRankMap R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      projectiveGrothendieckGroup_pidRankMap R x := by
  simpa using DFunLike.congr_fun
    (projectiveGrothendieckGroup_comparison_commutes_with_pidRank R) x

/-- Under the PID identifications `K₀(R) ≃+ ℤ` and `K'_0(R) ≃+ ℤ`, the canonical comparison map
`K₀(R) → K'_0(R)` acts as the identity on `ℤ`. -/
@[simp] theorem pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_apply
    (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_pidEquiv R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      projectiveGrothendieckGroup_pidEquiv R x := by
  change finiteGrothendieckGroup_pidRankMap R
      (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
    projectiveGrothendieckGroup_pidRankMap R x
  exact projectiveGrothendieckGroup_comparison_commutes_with_pidRank_apply R x

/-- For a principal ideal domain `R`, the canonical comparison map `K₀(R) → K'_0(R)` is the
identification obtained by passing through `ℤ`. In particular, `K₀(R) ≃+ K'_0(R) ≃+ ℤ`. -/
theorem pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) =
      (finiteGrothendieckGroup_pidEquiv R).symm.toAddMonoidHom.comp
        (projectiveGrothendieckGroup_pidEquiv R).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  apply (finiteGrothendieckGroup_pidEquiv R).injective
  simp [pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_apply]

end
