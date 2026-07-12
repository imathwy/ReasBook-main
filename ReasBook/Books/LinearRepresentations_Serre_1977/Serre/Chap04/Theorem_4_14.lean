import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RepresentationTheory.Irreducible
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped MonoidAlgebra

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]

/-- Helper for Theorem 4-14: the semisimple owner module `ρ.asModule` admits a finite family of
simple `ℂ[G]`-submodules that is independent and spans the whole module. -/
theorem finiteSimpleSubmoduleFamilyOfCompactAsModule
    (ρ : Representation ℂ G V) [IsContinuous ρ] :
    ∃ s : Set (Submodule ℂ[G] ρ.asModule),
      s.Finite ∧ sSupIndep s ∧ sSup s = ⊤ ∧ ∀ N ∈ s, IsSimpleModule ℂ[G] N := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa [Representation.asModule] using
      (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  haveI : IsSemisimpleRepresentation ρ := inferInstance
  haveI : IsSemisimpleModule ℂ[G] V := by
    simpa [Representation.asModule] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  haveI : Module.Finite ℂ[G] V := Module.Finite.of_restrictScalars_finite ℂ ℂ[G] V
  -- Finite-dimensionality over `ℂ` upgrades semisimplicity to a finite independent simple family.
  simpa [Representation.asModule] using
    ((IsSemisimpleModule.finite_tfae (R := ℂ[G]) (M := V)).out 0 4).mp
      (inferInstance : Module.Finite ℂ[G] V)

/-- Helper for Theorem 4-14: the owner action on `Subrepresentation.ofSubmodule' N` is the
original `ℂ[G]`-action on the submodule `N`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    (ρ : Representation ℂ G V) (N : Submodule ℂ[G] ρ.asModule)
    (r : ℂ[G]) (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the intrinsic owner action with the ambient owner action on the subtype carrier.
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
      -- On monomials, both actions are the restricted `ρ g` scaled by `a`.
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 4-14: the intrinsic owner module of
`(Subrepresentation.ofSubmodule' N).toRepresentation` is canonically the original submodule `N`.
-/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv
    (ρ : Representation ℂ G V) (N : Submodule ℂ[G] ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[ℂ[G]] N := by
  let ρN : Representation ℂ G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module ℂ[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
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
        -- The owner action is transported through the canonical equivalence of carriers.
        intro r x
        calc
          ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
          _ = r • ρN.asModuleEquiv x := by
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply ρ N r (ρN.asModuleEquiv x) }

/-- Helper for Theorem 4-14: a simple owner `ℂ[G]`-submodule yields an irreducible bundled
subrepresentation. -/
theorem isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
    (ρ : Representation ℂ G V) (N : Submodule ℂ[G] ρ.asModule)
    (hN : IsSimpleModule ℂ[G] N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation ℂ G N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module ℂ[G] ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  -- Transport simplicity across the canonical owner-module equivalence for `ofSubmodule'`.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (ℂ[G]) inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) N) hN)

/-- Helper for Theorem 4-14: the underlying `ℂ`-submodule of `Subrepresentation.ofSubmodule' N`
is the restricted-scalar view of the owner submodule `N`. -/
private theorem toSubmodule_ofSubmodule'_eq_restrictScalars
    (ρ : Representation ℂ G V) (N : Submodule ℂ[G] ρ.asModule) :
    (Subrepresentation.ofSubmodule' N).toSubmodule = N.restrictScalars ℂ := rfl

/-- Helper for Theorem 4-14: transporting a finite independent spanning family of owner
submodules across `Subrepresentation.ofSubmodule'` yields a subtype-indexed family of honest
subrepresentations whose ambient `ℂ`-submodules remain independent and spanning. -/
theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
    (ρ : Representation ℂ G V) (s : Set (Submodule ℂ[G] ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule ℂ[G] ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `ℂ[G]` to `ℂ`; this preserves the subtype-indexed independence data.
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars ℂ (i : Submodule ℂ[G] ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule ℂ[G] ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule ℂ[G] ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := ℂ) (hst := hi))
  have hs_top' : (⨆ i : s, (i : Submodule ℂ[G] ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  -- Applying `restrictScalars` to the `iSup` identity preserves the spanning statement.
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars ℂ (i : Submodule ℂ[G] ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars ℂ) hs_top'
  -- `Subrepresentation.ofSubmodule'` is definitionally the restricted-scalar carrier.
  simpa [toSubmodule_ofSubmodule'_eq_restrictScalars (ρ := ρ)] using ⟨hσ_indep, hσ_top⟩

-- Semantic recall: the canonical owner for a finite irreducible decomposition in this repository
-- is the family of subrepresentations together with `iSupIndep` and `⨆ = ⊤`; the
-- `DirectSum.IsInternal` form is a bridge packaging of that source-facing data.
/-- Theorem 4-14: every finite-dimensional continuous representation of a compact group admits a
finite family of irreducible subrepresentations whose underlying submodules are independent and
span the whole representation. This is the repository's canonical owner-level form of the
decomposition `V = W₁ ⊕ ⋯ ⊕ Wₖ`. -/
theorem exists_iSupIndep_irreducible_subrepresentations_of_compact
    (ρ : Representation ℂ G V) [IsContinuous ρ] :
    ∃ (ι : Type*) (_ : Fintype ι) (σ : ι → Subrepresentation ρ),
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  obtain ⟨s, hs_fin, hs_indep, hs_top, hs_simple⟩ :=
    finiteSimpleSubmoduleFamilyOfCompactAsModule (ρ := ρ)
  letI : Fintype s := hs_fin.fintype
  let σ : s → Subrepresentation ρ := fun i ↦ Subrepresentation.ofSubmodule' i.1
  have hσ :
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ := by
    -- The set-indexed owner decomposition becomes a subtype-indexed subrepresentation family.
    simpa [σ] using
      (iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
        (ρ := ρ) (s := s) hs_indep hs_top)
  rcases hσ with ⟨hσ_indep, hσ_top⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ₀ : Fin (Fintype.card s) → Subrepresentation ρ := fun i ↦ σ (e i)
  have hσ₀_indep : iSupIndep (fun i ↦ (σ₀ i).toSubmodule) := by
    -- Reindex the independent family along the finite equivalence `e`.
    simpa [σ₀, e] using hσ_indep.comp e.injective
  have hσ₀_top : (⨆ i, (σ₀ i).toSubmodule) = ⊤ := by
    -- Reindex the spanning supremum along the same finite equivalence.
    calc
      (⨆ i, (σ₀ i).toSubmodule) = ⨆ j : s, (σ j).toSubmodule := by
        simpa [σ₀, e] using (e.iSup_comp (g := fun j : s ↦ (σ j).toSubmodule))
      _ = ⊤ := hσ_top
  let τ : ULift (Fin (Fintype.card s)) → Subrepresentation ρ := fun i ↦ σ₀ i.down
  have hτ_indep : iSupIndep (fun i ↦ (τ i).toSubmodule) := by
    -- Lift the finite index type so the existential over `Type*` elaborates cleanly.
    simpa [τ] using hσ₀_indep.comp ULift.down_injective
  have hτ_top : (⨆ i, (τ i).toSubmodule) = ⊤ := by
    calc
      (⨆ i, (τ i).toSubmodule) = ⨆ j : Fin (Fintype.card s), (σ₀ j).toSubmodule := by
        simpa [τ] using
          (Equiv.ulift.iSup_comp (g := fun j : Fin (Fintype.card s) ↦ (σ₀ j).toSubmodule))
      _ = ⊤ := hσ₀_top
  refine ⟨ULift (Fin (Fintype.card s)), inferInstance, τ, hτ_indep, hτ_top, ?_⟩
  intro i
  -- Each simple owner summand is irreducible after rebundling as a subrepresentation.
  exact
    isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
      (ρ := ρ) (N := (e i.down).1) (hs_simple (e i.down).1 (e i.down).2)

/-- Companion direct-sum form of Theorem 4-14: the canonical independent spanning family of
irreducible subrepresentations may be repackaged as an internal direct sum. -/
theorem exists_isInternal_irreducible_subrepresentations_of_compact
    (ρ : Representation ℂ G V) [IsContinuous ρ] :
    ∃ (ι : Type*) (_ : Fintype ι) (_ : DecidableEq ι) (σ : ι → Subrepresentation ρ),
      DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  classical
  obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_iSupIndep_irreducible_subrepresentations_of_compact ρ
  exact
    ⟨ι, inferInstance, inferInstance, σ,
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top,
      hσ_irr⟩

end

end Representation
