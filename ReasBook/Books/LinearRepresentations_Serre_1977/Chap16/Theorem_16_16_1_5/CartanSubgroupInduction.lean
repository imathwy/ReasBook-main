import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.ElementaryDecompositionBridge

-- This theorem-local support file keeps subgroup-induction support inside Chapter 16 so it does
-- not import later Chapter 17 wrappers while building the Cartan theorem.

noncomputable section

universe u

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped MonoidAlgebra
open scoped Representation
open scoped TensorProduct

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

/-- Helper for Theorem 16-16.1-5: theorem-local placeholder for projective subgroup induction on
`P₀`. The next proof pass should supply the quotient-lift owner by inducing finite projective
modules and checking the short-exact-sequence relations. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplex_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (ModuleCat k[G]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)

namespace FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 16-16.1-5: inducing a finite projective `k[H]`-representation along
`H ≤ G` stays finite-dimensional over `k`. -/
private theorem subgroupInduction_finite_local [Finite G] {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Finite k (Rep.ind H.subtype P.toRep) := by
  let ρ := Representation.tprod ((leftRegular k G).comp H.subtype) P.toRep.ρ
  let M :=
    (TensorProduct k (G →₀ k) P.toRep) ⧸
      Representation.Coinvariants.ker (k := k) (G := H)
        (V := TensorProduct k (G →₀ k) P.toRep) ρ
  let _ : Module.Finite k M := by
    infer_instance
  change Module.Finite k M
  infer_instance

/-- Helper for Theorem 16-16.1-5: subgroup induction preserves projectivity of finite projective
`k[H]`-representations. -/
private theorem subgroupInduction_projective_local [Finite G] {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Projective k[G] (Rep.ind H.subtype P.toRep).ρ.asModule := by
  have hP : Projective P.toRep := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff]
    let M : ModuleCat k[H] := ModuleCat.of k[H] P.V
    have hM : Projective M := by
      rw [← IsProjective.iff_projective (R := k[H]) (P := P.V)]
      exact P.projective
    have hIso : Rep.toModuleMonoidAlgebra.obj P.toRep ≅ M := by
      simpa [M, FiniteProjectiveGroupAlgebraModule.toRep] using
        Rep.counitIso (k := k) (G := H) M
    exact Projective.of_iso hIso.symm hM
  have hInd : Projective (Rep.ind H.subtype P.toRep) := by
    simpa using Adjunction.map_projective (Rep.indResAdjunction k H.subtype) P.toRep hP
  change Module.Projective k[G] (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep))
  have hModObj : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff (Rep.ind H.subtype P.toRep)).2 hInd
  letI : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) := hModObj
  infer_instance

/-- Helper for Theorem 16-16.1-5: the induced finite projective owner on `G`. -/
private abbrev subgroupInduction_local [Finite G] {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k H) :
    FiniteProjectiveGroupAlgebraModule k G :=
  let ρ := Rep.ind H.subtype P.toRep
  let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module.Finite k ρ := subgroupInduction_finite_local (k := k) (G := G) P
  let _ : Module k Wk := Module.compHom Wk (algebraMap k k[G])
  let _ : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : ρ →ₗ[k] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  let _ : Module.Finite k Wk :=
    Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  let _ : Module.Finite k[G] Wk := Module.Finite.of_restrictScalars_finite k k[G] Wk
  let W : FGModuleCat k[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[G] Wk
    infer_instance
  let hW : Module.Projective k[G] W := by
    simpa [Wk, W, ρ, Rep.toModuleMonoidAlgebra] using
      subgroupInduction_projective_local (k := k) (G := G) P
  ⟨W, hW⟩

end FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 16-16.1-5: forget a finite projective owner to `Rep k G`. -/
private abbrev finiteProjective_toRepFunctor_local [Finite G] :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Theorem 16-16.1-5: first forget a finite projective owner to `Rep k H`, then
induce to `G`, and finally forget back to the ambient `k[G]`-module. -/
private abbrev subgroupInduction_projective_moduleFunctor_local [Finite G] {H : Subgroup G} :
    FiniteProjectiveGroupAlgebraModule k H ⥤ ModuleCat k[G] :=
  (finiteProjective_toRepFunctor_local (k := k) (G := H)) ⋙
    (Rep.indFunctor k H.subtype) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Theorem 16-16.1-5: subgroup induction preserves short exact sequences of finite
projective owners after forgetting to `ModuleCat`. -/
private theorem subgroupInduction_projective_module_shortExact_local [Finite G] {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) (hS : S.ShortExact) :
    (S.map (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).ShortExact := by
  have hMod :
      (finiteProjective_underlying_moduleCat_shortComplex_local (k := k) (G := H) S).ShortExact := by
    simpa [finiteProjective_underlying_moduleCat_shortComplex_local] using
      finiteProjective_shortExact_underlying_moduleCat_shortExact_local
        (A := k) (G := H) S hS
  have hRep :
      (((finiteProjective_underlying_moduleCat_shortComplex_local (k := k) (G := H) S).map
        (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map
          (Rep.indFunctor k H.subtype)).ShortExact := by
    simpa using
      (hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map_of_exact
        (Rep.indFunctor k H.subtype)
  simpa [subgroupInduction_projective_moduleFunctor_local, finiteProjective_toRepFunctor_local] using
    hRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])

/-- Helper for Theorem 16-16.1-5: the free-group lift sending `[P]` to the induced class
`[Ind_H^G(P)]`. -/
private abbrev finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local
    [Finite G] (H : Subgroup G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k H) →+ P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦
    [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P)]ₚ₀

/-- Helper for Theorem 16-16.1-5: the defining relations of `P₀[k](H)` vanish after subgroup
induction to `P₀[k](G)`. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker_local
    [Finite G] (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k H ≤
      (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local H).ker := by
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂)]ₚ₀ -
        [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ -
        [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)]ₚ₀ = 0
  rw [sub_eq_zero]
  have hUnderlying :
      (S.map (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).ShortExact :=
    subgroupInduction_projective_module_shortExact_local (k := k) (G := G) S hS
  have hMidProd :
      Nonempty
        (((FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁).V ×
            (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃).V) ≃ₗ[k[G]]
          (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂).V) := by
    letI :
        Module.Projective k[G]
          ↑((S.map (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H))).X₃) := by
      change Module.Projective k[G] (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype S.X₃.toRep))
      exact FiniteProjectiveGroupAlgebraModule.subgroupInduction_projective_local
        (k := k) (G := G) S.X₃
    simpa [subgroupInduction_projective_moduleFunctor_local, finiteProjective_toRepFunctor_local,
      FiniteProjectiveGroupAlgebraModule.subgroupInduction_local] using
      moduleCat_shortExact_middle_nonempty_linearEquiv_prod
        (R := k[G])
        (S := S.map (subgroupInduction_projective_moduleFunctor_local (k := k) (G := G) (H := H)))
        hUnderlying
  obtain ⟨W, hWlin, hWclass⟩ :=
    finiteProjectiveGroupAlgebraGrothendieckClass_prod_eq_add
      (A := k) (G := G)
      (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)
      (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)
  have hMidClass :
      [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂)]ₚ₀ =
        [W]ₚ₀ := by
    apply finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    apply
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂) W).2
    rcases hMidProd with ⟨eMid⟩
    rcases hWlin with ⟨eW⟩
    exact ⟨eMid.symm.trans eW.symm⟩
  have hrelation :
      [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂)]ₚ₀ =
        [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ +
          [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)]ₚ₀ := by
    calc
      [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂)]ₚ₀ =
          [W]ₚ₀ := hMidClass
      _ =
          [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ +
            [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)]ₚ₀ :=
          hWclass
  calc
    [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₂)]ₚ₀ -
        [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ =
      ([(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ +
          [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)]ₚ₀) -
        [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₁)]ₚ₀ := by
          rw [hrelation]
    _ = [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) S.X₃)]ₚ₀ := by
          abel

/-- Helper for Theorem 16-16.1-5: the induced map `Ind_H^G : P₀[k](H) → P₀[k](G)` on projective
Grothendieck groups. -/
def projective_subgroupInduction
    [Finite G] (H : Subgroup G) :
    P₀[k](H) →+ P₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)
    (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift_local H)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker_local H)

/-- Helper for Theorem 16-16.1-5: subgroup induction on `P₀[k](H)` sends a projective generator
class to the class of the induced projective owner. -/
@[simp] theorem projective_subgroupInduction_apply_class
    [Finite G] (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k H) :
    projective_subgroupInduction H [P]ₚ₀ =
      [(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P)]ₚ₀ := by
  rfl

/-- Helper for Theorem 16-16.1-5: a theorem-local name for the public induction map
`Ind_H^G : R₀[k](H) → R₀[k](G)`. -/
abbrev finiteRep_subgroupInduction
    [Finite G] (H : Subgroup G) :
    R₀[k](H) →+ R₀[k](G) :=
  Representation.Subgroup.finiteRepGrothendieckGroupInduction k H

/-- Helper for Theorem 16-16.1-5: subgroup induction on `R₀[k](H)` sends a generator class to
the class of the induced finite-dimensional representation. -/
@[simp] theorem finiteRep_subgroupInduction_apply_class
    [Finite G] (H : Subgroup G) (V : FDRep k H) :
    finiteRep_subgroupInduction (k := k) (G := G) H [V]₀ =
      [FDRep.subgroupInduction (k := k) (G := G) V]₀ := by
  simpa [finiteRep_subgroupInduction] using
    Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class
      (k := k) (G := G) H V

/-- Helper for Theorem 16-16.1-5: the theorem-local induction map on `R₀[k](H)` agrees with the
canonical Chapter `17` induction owner. -/
theorem finiteRep_subgroupInduction_eq_public
    [Finite G] (H : Subgroup G) :
    finiteRep_subgroupInduction (k := k) (G := G) H =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H := by
  rfl

local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ

local instance [Finite G] : NumberField Lexp := inferInstance

local instance [Finite G] : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

/-- Helper for Theorem 16-16.1-5: the top intermediate field has trivial fixing subgroup. -/
private theorem top_fixingSubgroup_eq_bot_local
    [Finite G] :
    ((⊤ : IntermediateField ℚ Lexp).fixingSubgroup) = ⊥ := by
  -- The full field is fixed only by the identity automorphism.
  rw [IntermediateField.fixingSubgroup_top]

/-- Helper for Theorem 16-16.1-5: the top intermediate field has trivial image under the
cyclotomic Galois-to-exponent-unit identification. -/
private theorem top_fixingSubgroup_map_eq_bot_local
    [Finite G] :
    (galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup
        ((⊤ : IntermediateField ℚ Lexp).fixingSubgroup) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- The top intermediate field has trivial fixing subgroup, so its image is the bottom subgroup.
  rw [top_fixingSubgroup_eq_bot_local (G := G)]
  simpa using OrderIso.map_bot (galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

/-- Helper for Theorem 16-16.1-5: every Grothendieck class is a finite sum of inductions from
ordinary elementary subgroups. The next proof pass should extract exactly this corollary-level
surface from the Chapter 17 Brauer-induction route. -/
theorem grothendieckClass_exists_sum_of_elementary_subgroup_inductions_local
    [Finite G] (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, (finiteRep_subgroupInduction (k := k) (G := G) (H i)) (y i) := by
  -- Route correction: the top-field Brauer-induction specialization now lives in a tiny theorem-
  -- local bridge file, so this Chapter `16` theorem only rewrites the induction-map owner.
  simpa [finiteRep_subgroupInduction_eq_public] using
    (grothendieckClass_exists_sum_of_elementary_subgroup_inductions_bridge
      (k := k) (G := G) x)

/-- Helper for Theorem 16-16.1-5: the induced finite-projective owner and the induced
finite-dimensional owner forget to the same `Rep`, so they determine the same class in `R₀[k](G)`.
-/
private theorem induced_projective_toFiniteRep_class_eq
    [Finite G] {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    [((FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P).toFiniteRep)]₀ =
      [FDRep.subgroupInduction (k := k) (G := G) P.toFiniteRep]₀ := by
  let σ₁ := (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P).toFiniteRep
  let σ₂ := FDRep.subgroupInduction (k := k) (G := G) P.toFiniteRep
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj σ₁) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj σ₂) := by
    simpa [σ₁, σ₂, FiniteProjectiveGroupAlgebraModule.subgroupInduction_local,
      FDRep.subgroupInduction, FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso (Rep.ind H.subtype P.toRep)).symm
  let e : σ₁ ≅ σ₂ := by
    refine ⟨(FDRep.forget₂HomLinearEquiv σ₁ σ₂) eRep.hom,
      (FDRep.forget₂HomLinearEquiv σ₂ σ₁) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Theorem 16-16.1-5: Cartan commutes with subgroup induction once the theorem-local
projective induction owner on `P₀` is available. -/
theorem cartanHom_subgroupInduction_eq_subgroupInduction_cartanHom
    [Finite G] (H : Subgroup G) (x : P₀[k](H)) :
    cartanHom k G (projective_subgroupInduction H x) =
      finiteRep_subgroupInduction (k := k) (G := G) H (cartanHom k H x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro P
    change
      cartanHom k G (projective_subgroupInduction H [P]ₚ₀) =
        finiteRep_subgroupInduction (k := k) (G := G) H (cartanHom k H [P]ₚ₀)
    rw [projective_subgroupInduction_apply_class, cartanHom_projectiveClass_eq,
      cartanHom_projectiveClass_eq, finiteRep_subgroupInduction_apply_class]
    exact induced_projective_toFiniteRep_class_eq (k := k) (G := G) P
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

end

end Representation
