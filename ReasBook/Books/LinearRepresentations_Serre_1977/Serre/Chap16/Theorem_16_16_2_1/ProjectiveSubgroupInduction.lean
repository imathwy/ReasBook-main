import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

namespace Representation

namespace FiniteProjectiveGroupAlgebraModule

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]

/-- Inducing a finite projective `A[H]`-representation along `H ≤ G` remains finite over `A`.

This is the actual owner-level induction used in Theorem 16-16.2-1.  It is deliberately named
`subgroupInductionBase`, rather than `subgroupInduction`, to avoid colliding with the later
Chapter 17 public owner. -/
theorem subgroupInductionBase_finite {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule A H) :
    Module.Finite A (Rep.ind H.subtype P.toRep) := by
  let ρ := Representation.tprod ((leftRegular A G).comp H.subtype) P.toRep.ρ
  let M :=
    (TensorProduct A (G →₀ A) P.toRep) ⧸
      Representation.Coinvariants.ker (k := A) (G := H)
        (V := TensorProduct A (G →₀ A) P.toRep) ρ
  let _ : Module.Finite A M := by infer_instance
  change Module.Finite A M
  infer_instance

omit [Finite G] in
/-- Inducing a finite projective `A[H]`-representation along `H ≤ G` remains projective over
`A[G]`. -/
theorem subgroupInductionBase_projective {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule A H) :
    Module.Projective A[G] (Rep.ind H.subtype P.toRep).ρ.asModule := by
  have hP : Projective P.toRep := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff]
    let M : ModuleCat A[H] := ModuleCat.of A[H] P.V
    have hM : Projective M := by
      rw [← IsProjective.iff_projective (R := A[H]) (P := P.V)]
      exact P.projective
    have hIso : Rep.toModuleMonoidAlgebra.obj P.toRep ≅ M := by
      simpa [M, FiniteProjectiveGroupAlgebraModule.toRep] using
        Rep.counitIso (k := A) (G := H) M
    exact Projective.of_iso hIso.symm hM
  have hInd : Projective (Rep.ind H.subtype P.toRep) := by
    simpa using Adjunction.map_projective (Rep.indResAdjunction A H.subtype) P.toRep hP
  change Module.Projective A[G] (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep))
  have hModObj : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff (Rep.ind H.subtype P.toRep)).2 hInd
  letI : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) := hModObj
  infer_instance

/-- The actual finite projective `A[G]`-representation induced from a finite projective
`A[H]`-representation. -/
abbrev subgroupInductionBase {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule A H) :
    FiniteProjectiveGroupAlgebraModule A G :=
  let ρ := Rep.ind H.subtype P.toRep
  let Wk : ModuleCat A[G] := Rep.toModuleMonoidAlgebra.obj ρ
  letI : Module.Finite A ρ := subgroupInductionBase_finite P
  letI : Module A Wk := Module.compHom Wk (algebraMap A A[G])
  letI : IsScalarTower A A[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : ρ →ₗ[A] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) =
          ((algebraMap A A[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  letI : Module.Finite A Wk :=
    Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  letI : Module.Finite A[G] Wk := Module.Finite.of_restrictScalars_finite A A[G] Wk
  let W : FGModuleCat A[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite A[G] Wk
    infer_instance
  let hW : Module.Projective A[G] W := by
    simpa [Wk, W, ρ, Rep.toModuleMonoidAlgebra] using subgroupInductionBase_projective P
  ⟨W, hW⟩

end FiniteProjectiveGroupAlgebraModule

section ProjectiveInductionMap

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 16-16.2-1: forgetting a short complex of finite projective owners to
`ModuleCat k[G]` keeps the same structure maps. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplex_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (ModuleCat k[G]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)

/-- Helper for Theorem 16-16.2-1: the canonical functor from finite projective owners to
`Rep k G`. -/
private abbrev finiteProjective_toRepFunctor_local :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Theorem 16-16.2-1: first forget a finite projective owner to `Rep k H`, then
apply subgroup induction, and finally forget back to the ambient `k[G]`-module. -/
private abbrev subgroupInduction_projective_moduleFunctor_local {H : Subgroup G} :
    FiniteProjectiveGroupAlgebraModule k H ⥤ ModuleCat k[G] :=
  (finiteProjective_toRepFunctor_local (k := k) (G := H)) ⋙
    (Rep.indFunctor k H.subtype) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Theorem 16-16.2-1: subgroup induction preserves short exact sequences of finite
projective owners after forgetting to `ModuleCat`. -/
private theorem subgroupInduction_projective_module_shortExact_local {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) (hS : S.ShortExact) :
    (S.map (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).ShortExact := by
  have hMod :
      (finiteProjective_underlying_moduleCat_shortComplex_local (k := k) (G := H) S).ShortExact := by
    -- Over a field, owner short exactness is detected by the underlying module sequence.
    simpa [finiteProjective_underlying_moduleCat_shortComplex_local] using
      finiteProjective_shortExact_underlying_moduleCat_shortExact_field
        (K := k) (G := H) S hS
  have hRep :
      (((finiteProjective_underlying_moduleCat_shortComplex_local (k := k) (G := H) S).map
        (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map
          (Rep.indFunctor k H.subtype)).ShortExact := by
    -- Exactness is preserved by the representation equivalence and then by induction.
    simpa using
      (hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map_of_exact
        (Rep.indFunctor k H.subtype)
  -- Forget the induced representation back to its group-algebra module.
  simpa [subgroupInduction_projective_moduleFunctor_local, finiteProjective_toRepFunctor_local] using
    hRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])

/-- Helper for Theorem 16-16.2-1: the free-abelian lift sending `[P]` to the class of the
Chapter-16 induced projective owner. -/
private abbrev finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local
    (H : Subgroup G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k H) →+ P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦ [P.subgroupInductionBase (G := G)]ₚ₀

/-- Helper for Theorem 16-16.2-1: the split Grothendieck relations of `P₀[k](H)` vanish after
Chapter-16 subgroup induction to `P₀[k](G)`. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker_local
    (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k H ≤
      (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local (k := k) (G := G) H).ker := by
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  obtain ⟨e⟩ := hS
  change
    [(S.X₂.subgroupInductionBase (G := G))]ₚ₀ -
        [(S.X₁.subgroupInductionBase (G := G))]ₚ₀ -
        [(S.X₃.subgroupInductionBase (G := G))]ₚ₀ = 0
  rw [sub_eq_zero]
  have hUnderlying :
      ((splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e).map
          (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).ShortExact :=
    subgroupInduction_projective_module_shortExact_local (k := k) (G := G)
      (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e)
      (splitShortComplexOfLinearEquivProd_shortExact S.X₁ S.X₂ S.X₃ e)
  have hMidProd :
      Nonempty
        (((S.X₁.subgroupInductionBase (G := G)).V ×
            (S.X₃.subgroupInductionBase (G := G)).V) ≃ₗ[k[G]]
          (S.X₂.subgroupInductionBase (G := G)).V) := by
    letI :
        Module.Projective k[G]
          ↑(((splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e).map
            (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).X₃) := by
      change Module.Projective k[G] (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype S.X₃.toRep))
      exact FiniteProjectiveGroupAlgebraModule.subgroupInductionBase_projective
        (A := k) (G := G) S.X₃
    -- A short exact sequence with projective right term splits after induction.
    simpa [subgroupInduction_projective_moduleFunctor_local, finiteProjective_toRepFunctor_local,
      FiniteProjectiveGroupAlgebraModule.subgroupInductionBase,
      splitShortComplexOfLinearEquivProd_X₁, splitShortComplexOfLinearEquivProd_X₂,
      splitShortComplexOfLinearEquivProd_X₃] using
      moduleCat_shortExact_middle_nonempty_linearEquiv_prod
        (R := k[G])
        (S := (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e).map
          (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H)))
        hUnderlying
  obtain ⟨W, hWlin, hWclass⟩ :=
    finiteProjectiveGroupAlgebraGrothendieckClass_prod_eq_add
      (A := k) (G := G)
      (S.X₁.subgroupInductionBase (G := G))
      (S.X₃.subgroupInductionBase (G := G))
  have hMidClass :
      [(S.X₂.subgroupInductionBase (G := G))]ₚ₀ = [W]ₚ₀ := by
    apply finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    apply
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (S.X₂.subgroupInductionBase (G := G)) W).2
    rcases hMidProd with ⟨eMid⟩
    rcases hWlin with ⟨eW⟩
    exact ⟨eMid.symm.trans eW.symm⟩
  have hrelation :
      [(S.X₂.subgroupInductionBase (G := G))]ₚ₀ =
        [(S.X₁.subgroupInductionBase (G := G))]ₚ₀ +
          [(S.X₃.subgroupInductionBase (G := G))]ₚ₀ := by
    calc
      [(S.X₂.subgroupInductionBase (G := G))]ₚ₀ = [W]ₚ₀ := hMidClass
      _ =
          [(S.X₁.subgroupInductionBase (G := G))]ₚ₀ +
            [(S.X₃.subgroupInductionBase (G := G))]ₚ₀ := hWclass
  calc
    [(S.X₂.subgroupInductionBase (G := G))]ₚ₀ -
        [(S.X₁.subgroupInductionBase (G := G))]ₚ₀ =
      ([(S.X₁.subgroupInductionBase (G := G))]ₚ₀ +
          [(S.X₃.subgroupInductionBase (G := G))]ₚ₀) -
        [(S.X₁.subgroupInductionBase (G := G))]ₚ₀ := by
          rw [hrelation]
    _ = [(S.X₃.subgroupInductionBase (G := G))]ₚ₀ := by
          abel

end ProjectiveInductionMap

section FieldComparison

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- The theorem-local name for finite-representation subgroup induction. -/
abbrev finiteRep_subgroupInduction
    (H : Subgroup G) :
    R₀[k](H) →+ R₀[k](G) :=
  Representation.Subgroup.finiteRepGrothendieckGroupInduction k H

/-- The theorem-local finite-representation induction map sends a generator to the induced
finite-dimensional owner. -/
@[simp] theorem finiteRep_subgroupInduction_apply_class
    (H : Subgroup G) (V : FDRep k H) :
    finiteRep_subgroupInduction (k := k) (G := G) H [V]₀ =
      [FDRep.subgroupInduction (k := k) (G := G) V]₀ := by
  rfl

/-- The theorem-local name for projective subgroup induction. -/
def projective_subgroupInduction
    (H : Subgroup G) :
    P₀[k](H) →+ P₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)
    (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local (k := k) (G := G) H)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker_local
      (k := k) (G := G) H)

/-- The theorem-local projective induction map sends a generator to the induced finite projective
owner. -/
@[simp] theorem projective_subgroupInduction_apply_class
    (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k H) :
    projective_subgroupInduction (G := G) H [P]ₚ₀ =
      [P.subgroupInductionBase (G := G)]ₚ₀ := by
  rfl

/-- The Chapter 16 projective subgroup-induction map agrees on generators with the actual
`subgroupInductionBase` owner above. -/
theorem projective_subgroupInduction_apply_class_base
    (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k H) :
    projective_subgroupInduction (G := G) H [P]ₚ₀ =
      [P.subgroupInductionBase (G := G)]ₚ₀ := by
  rw [projective_subgroupInduction_apply_class]

end FieldComparison

end Representation
