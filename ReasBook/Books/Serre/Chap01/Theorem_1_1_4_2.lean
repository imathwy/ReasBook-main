import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Representation
open scoped MonoidAlgebra

noncomputable section

section

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Theorem 1-1.4-2: a semisimple finite-dimensional representation admits a finite
family of simple `k[G]`-submodules that is independent and spans the whole module. -/
theorem exists_finite_sSupIndep_simple_submodule_family (ρ : Representation k G V) :
    ∃ s : Set (Submodule k[G] ρ.asModule),
      s.Finite ∧ sSupIndep s ∧ sSup s = ⊤ ∧ ∀ N ∈ s, IsSimpleModule k[G] N := by
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k k[G] V := by
    simpa [Representation.asModule] using
      (inferInstance : IsScalarTower k k[G] ρ.asModule)
  have hcard : Nat.card G ≠ 0 := by
    intro h
    exact NeZero.ne (Nat.card G : k) <| by simp [h]
  letI : Finite G := Nat.finite_of_card_ne_zero hcard
  letI : Fintype G := Fintype.ofFinite G
  haveI : ρ.IsSemisimpleRepresentation := inferInstance
  haveI : IsSemisimpleModule k[G] V := by
    -- Maschke turns the owner `k[G]`-module of `ρ` into a semisimple module.
    simpa [Representation.asModule] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
        inferInstance
  haveI : Module.Finite k[G] V := Module.Finite.of_restrictScalars_finite k k[G] V
  -- Finite generation upgrades the semisimple decomposition to a finite independent family.
  simpa [Representation.asModule] using
    (((IsSemisimpleModule.finite_tfae (R := k[G]) (M := V)).out 0 4).mp
      (inferInstance : Module.Finite k[G] V))

/-- Helper for Theorem 1-1.4-2: a simple `k[G]`-submodule of `ρ.asModule` gives an irreducible
subrepresentation of `ρ`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule)
    (r : k[G]) (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the two `k[G]`-actions after forgetting to the ambient carrier of the subtype.
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      -- Both actions send `0` to the zero vector.
      rfl
  | add a b ha hb =>
      -- Additivity reduces the ambient equality to the induction hypotheses.
      rw [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, Submodule.coe_add, ha, hb]
      rfl
  | single g a =>
      -- On basis monomials, both actions are the scalar multiple of the restricted `ρ g`.
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 1-1.4-2: the owner module of
`(Subrepresentation.ofSubmodule' N).toRepresentation` is canonically the original submodule `N`.
-/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[k[G]] N := by
  let ρN : Representation k G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module k[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  refine
    { toFun := fun x => ρN.asModuleEquiv x
      invFun := fun x => ρN.asModuleEquiv.symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        -- The transported owner action agrees with the original `k[G]`-action on `N`.
        intro r x
        calc
          ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
          _ = r • ρN.asModuleEquiv x := by
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply ρ N r (ρN.asModuleEquiv x) }

theorem isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule)
    (hN : IsSimpleModule k[G] N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  -- Route correction: the proof closes by transporting simplicity across the owner-module bridge
  -- instead of trying to coerce the two module instances directly.
  let ρN : Representation k G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  -- The standard irreducible/simple-module equivalence finishes the transport.
  letI : Module k[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (k[G]) inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) N) hN)

/-- Helper for Theorem 1-1.4-2: transporting a finite simple owner-submodule decomposition across
`Subrepresentation.ofSubmodule'` gives a subtype-indexed family of subrepresentations that is
independent and spans the whole representation. -/
private theorem toSubmodule_ofSubmodule'_eq_restrictScalars
    (ρ : Representation k G V) (N : Submodule k[G] ρ.asModule) :
    (Subrepresentation.ofSubmodule' N).toSubmodule = N.restrictScalars k := rfl

/-- Helper for Theorem 1-1.4-2: transporting a finite simple owner-submodule decomposition across
`Subrepresentation.ofSubmodule'` gives a subtype-indexed family whose underlying `k`-submodules
are independent and span the whole representation. -/
private theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
    (ρ : Representation k G V) (s : Set (Submodule k[G] ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  -- Convert the set-indexed independence to a subtype-indexed family of owner submodules.
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule k[G] ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `k[G]` to `k`; this preserves both independence and the supremum.
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars k (i : Submodule k[G] ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule k[G] ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule k[G] ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := k) (hst := hi))
  -- The spanning statement is transported by applying `restrictScalars` to the `iSup` equality.
  have hs_top' : (⨆ i : s, (i : Submodule k[G] ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars k (i : Submodule k[G] ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars k) hs_top'
  exact
    by
      simpa [toSubmodule_ofSubmodule'_eq_restrictScalars (ρ := ρ)] using ⟨hσ_indep, hσ_top⟩

/-- Helper for Theorem 1-1.4-2: an internal direct sum of subrepresentations gives an external
direct-sum equivalence of representations. -/
noncomputable def directSum_equiv_of_iSupIndep_of_iSup_eq_top {ι : Type*} [Fintype ι]
    (ρ : Representation k G V) (σ : ι → Subrepresentation ρ)
    (hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule))
    (hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤) :
    (directSum fun i ↦ (σ i).toRepresentation).Equiv ρ := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  letI := DirectSum.IsInternal.chooseDecomposition (fun i ↦ (σ i).toSubmodule) hinternal
  -- The canonical decomposition equivalence is `G`-equivariant because each summand is stable.
  exact
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv (fun i ↦ (σ i).toSubmodule)).symm
      (fun g ↦ by
        ext i x
        simp [Representation.directSum]
        rfl)

/-- Theorem 1-1.4-2: every finite-dimensional representation of a finite group over a field in
which `|G|` is invertible admits a finite family of irreducible subrepresentations whose
underlying submodules are independent and span the whole representation. This is the canonical
submodule-owner form of an internal direct-sum decomposition, and it specializes to the complex
case in the text. -/
-- Proof sketch: Maschke's theorem makes `ρ` semisimple, so `ρ.asModule` is a semisimple
-- `k[G]`-module. Finite-dimensionality implies finite length, hence the semisimple-module API
-- yields a finite family of simple `k[G]`-submodules with an internal direct-sum decomposition of
-- the whole module. Transport those simple submodules across the canonical order isomorphism with
-- `Subrepresentation ρ`.
theorem exists_isInternal_irreducible_subrepresentations (ρ : Representation k G V) :
    ∃ (ι : Type*) (_ : Fintype ι) (σ : ι → Subrepresentation ρ),
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  -- Route correction: keep the semisimple owner-submodule decomposition and only transport it
  -- once, first to subrepresentations and then to their underlying `k`-submodules.
  classical
  obtain ⟨s, hs_fin, hs_indep, hs_top, hs_simple⟩ :=
    exists_finite_sSupIndep_simple_submodule_family (ρ := ρ)
  letI : Fintype s := hs_fin.fintype
  let τ : s → Subrepresentation ρ := fun i ↦ Subrepresentation.ofSubmodule' i.1
  have hτ :
      iSupIndep (fun i ↦ (τ i).toSubmodule) ∧
        (⨆ i, (τ i).toSubmodule) = ⊤ := by
    -- The structural helper turns the set-indexed owner decomposition into a finite family.
    simpa [τ] using
      (iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
        (ρ := ρ) (s := s) hs_indep hs_top)
  rcases hτ with ⟨hτ_indep, hτ_top⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ₀ : Fin (Fintype.card s) → Subrepresentation ρ := fun i ↦ τ (e i)
  have hσ₀_indep : iSupIndep (fun i ↦ (σ₀ i).toSubmodule) := by
    -- Reindex the independent family along the finite equivalence `e`.
    simpa [σ₀, e] using hτ_indep.comp e.injective
  have hσ₀_top : (⨆ i, (σ₀ i).toSubmodule) = ⊤ := by
    -- Reindex the spanning `iSup` along the same equivalence.
    calc
      (⨆ i, (σ₀ i).toSubmodule) = ⨆ j : s, (τ j).toSubmodule := by
        simpa [σ₀, e] using (e.iSup_comp (g := fun j : s ↦ (τ j).toSubmodule))
      _ = ⊤ := hτ_top
  let σ : ULift (Fin (Fintype.card s)) → Subrepresentation ρ := fun i ↦ σ₀ i.down
  have hσ_indep : iSupIndep (fun i ↦ (σ i).toSubmodule) := by
    -- Lift the finite index type so the existential over `Type*` elaborates cleanly.
    simpa [σ] using hσ₀_indep.comp ULift.down_injective
  have hσ_top : (⨆ i, (σ i).toSubmodule) = ⊤ := by
    calc
      (⨆ i, (σ i).toSubmodule) = ⨆ j : Fin (Fintype.card s), (σ₀ j).toSubmodule := by
        simpa [σ] using (Equiv.ulift.iSup_comp (g := fun j : Fin (Fintype.card s) ↦
          (σ₀ j).toSubmodule))
      _ = ⊤ := hσ₀_top
  refine ⟨ULift (Fin (Fintype.card s)), inferInstance, σ, hσ_indep, hσ_top, ?_⟩
  intro i
  -- Each simple owner submodule becomes an irreducible subrepresentation by the bridge above.
  exact
    isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
      (ρ := ρ) (N := (e i.down).1) (hs_simple (e i.down).1 (e i.down).2)

/-- Derived external direct-sum form of Theorem 1-1.4-2. -/
theorem exists_equiv_directSum_irreducible_subrepresentations (ρ : Representation k G V) :
    ∃ (ι : Type*) (_ : Fintype ι) (σ : ι → Subrepresentation ρ)
      (e : (directSum fun i ↦ (σ i).toRepresentation).Equiv ρ),
      ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := ρ)
  -- Once the internal decomposition is available, the standard direct-sum equivalence closes the
  -- external statement.
  exact
    ⟨ι, inferInstance, σ,
      directSum_equiv_of_iSupIndep_of_iSup_eq_top (ρ := ρ) σ hσ_indep hσ_top,
      hσ_irr⟩

end
