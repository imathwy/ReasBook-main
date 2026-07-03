import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct

noncomputable section

universe u w x

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

/-- Helper for Theorem 17-17.2-4: inducing a finite-dimensional `k`-representation from
`H ≤ G` stays finite-dimensional. -/
theorem subgroupInduction_finite {H : Subgroup G} (V : FDRep k H) :
    Module.Finite k (Rep.ind H.subtype (Rep.of V.ρ)) := by
  let ρ := Representation.tprod ((leftRegular k G).comp H.subtype) V.ρ
  let M :=
    (TensorProduct k (G →₀ k) V) ⧸
      Representation.Coinvariants.ker (k := k) (G := H)
        (V := TensorProduct k (G →₀ k) V) ρ
  let _ : Module.Finite k M := by
    infer_instance
  change Module.Finite k M
  infer_instance

instance {H : Subgroup G} (V : FDRep k H) :
    Module.Finite k (Rep.ind H.subtype (Rep.of V.ρ)) :=
  subgroupInduction_finite V

/-- Helper for Theorem 17-17.2-4: the induced bundled finite-dimensional owner. -/
abbrev subgroupInduction {H : Subgroup G} (V : FDRep k H) : FDRep k G :=
  let ρ := Rep.ind H.subtype (Rep.of V.ρ)
  let _ : Module.Finite k ρ := subgroupInduction_finite V
  FDRep.of ρ.ρ

end FDRep

/-- Helper for Theorem 17-17.2-4: the induced morphism on bundled finite-dimensional
representations. -/
private abbrev subgroupInduction_map {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    FDRep.subgroupInduction V ⟶ FDRep.subgroupInduction W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))

/-- Helper for Theorem 17-17.2-4: forgetting the induced `FDRep` morphism recovers the ambient
`Rep.indMap`. -/
private theorem subgroupInduction_map_forget {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    (forget₂ (FDRep k G) (Rep k G)).map (subgroupInduction_map (k := k) (G := G) f) =
      Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f) := by
  change (FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W)).symm
    ((FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W))
      (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))) =
    Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Theorem 17-17.2-4: a short complex of `FDRep k H` induces termwise to a short
complex of `FDRep k G`. -/
private abbrev subgroupInduction_shortComplex {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) : ShortComplex (FDRep k G) :=
  ShortComplex.mk
    (subgroupInduction_map (k := k) (G := G) S.f)
    (subgroupInduction_map (k := k) (G := G) S.g)
    (by
      apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      rw [Functor.map_comp]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.f]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.g]
      simpa using
        (((S.map (forget₂ (FDRep k H) (Rep k H))).map
          (Rep.indFunctor k H.subtype)).zero))

/-- Helper for Theorem 17-17.2-4: induction along `H ≤ G` preserves short exact sequences of
finite-dimensional representations. -/
private theorem subgroupInduction_shortExact {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) (hS : S.ShortExact) :
    (subgroupInduction_shortComplex (k := k) (G := G) S).ShortExact := by
  have hRep :
      (((subgroupInduction_shortComplex (k := k) (G := G) S).map
        (forget₂ (FDRep k G) (Rep k G)))).ShortExact := by
    simpa [subgroupInduction_shortComplex, subgroupInduction_map_forget] using
      (hS.map_of_exact (forget₂ (FDRep k H) (Rep k H))).map_of_exact
        (Rep.indFunctor k H.subtype)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((subgroupInduction_shortComplex (k := k) (G := G) S).exact_map_iff_of_faithful
        (forget₂ (FDRep k G) (Rep k G))).1 hRep.exact
  · exact (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g

/-- Helper for Theorem 17-17.2-4: the additive lift sending `[V]` to `[Ind_H^G(V)]`. -/
private abbrev finiteRepGrothendieckGroupInductionLift (H : Subgroup G) :
    FreeAbelianGroup (FDRep k H) →+ R₀[k](G) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.subgroupInduction V]₀

/-- Helper for Theorem 17-17.2-4: the defining relations of `R_k(H)` map to zero under subgroup
induction. -/
private theorem finiteRepGrothendieckRelations_le_inductionLift_ker (H : Subgroup G) :
    finiteRepGrothendieckRelations k H ≤ (finiteRepGrothendieckGroupInductionLift H).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [FDRep.subgroupInduction S.X₂]₀ - [FDRep.subgroupInduction S.X₁]₀ -
      [FDRep.subgroupInduction S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G)
      (subgroupInduction_shortComplex (k := k) (G := G) S)
      (subgroupInduction_shortExact (k := k) (G := G) S hS)
  calc
    [FDRep.subgroupInduction S.X₂]₀ - [FDRep.subgroupInduction S.X₁]₀ =
        ([FDRep.subgroupInduction S.X₁]₀ + [FDRep.subgroupInduction S.X₃]₀) -
          [FDRep.subgroupInduction S.X₁]₀ := by
            rw [hrelation]
    _ = [FDRep.subgroupInduction S.X₃]₀ := by
          abel

namespace Subgroup

/-- Helper for Theorem 17-17.2-4: subgroup induction on `R_k(H)`. -/
def finiteRepGrothendieckGroupInduction (k : Type u) [Field k] (H : Subgroup G) :
    R₀[k](H) →+ R₀[k](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k H)
    (finiteRepGrothendieckGroupInductionLift H)
    (finiteRepGrothendieckRelations_le_inductionLift_ker H)

scoped[FiniteRepGrothendieckInduction] notation "Ind[" H "]" =>
  Representation.Subgroup.finiteRepGrothendieckGroupInduction _ H

section

open scoped FiniteRepGrothendieckInduction

/-- Helper for Theorem 17-17.2-4: subgroup induction on a generator class. -/
@[simp] theorem finiteRepGrothendieckGroupInduction_apply_class
    (H : Subgroup G) (V : FDRep k H) :
    (Ind[H]) [V]₀ =
      [FDRep.subgroupInduction V]₀ := by
  rfl

/-- Helper for Theorem 17-17.2-4: the rationalized subgroup induction map on `R_k(H)`. -/
def finiteRepGrothendieckGroupRationalizedInduction (k : Type u) [Field k] (H : Subgroup G) :
    (ℚ ⊗[ℤ] R₀[k](H)) →ₗ[ℚ] ℚ ⊗[ℤ] R₀[k](G) :=
  ((Ind[H]).toIntLinearMap).baseChange ℚ

end
end Subgroup

namespace FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 17-17.2-4: subgroup induction preserves finite-dimensionality on finite
projective owners. -/
theorem subgroupInduction_finite {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
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

/-- Helper for Theorem 17-17.2-4: subgroup induction preserves projectivity on finite projective
owners. -/
theorem subgroupInduction_projective {H : Subgroup G}
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

instance {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Finite k (Rep.ind H.subtype P.toRep) :=
  subgroupInduction_finite P

instance {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Projective k[G] (Rep.ind H.subtype P.toRep).ρ.asModule :=
  subgroupInduction_projective P

/-- Helper for Theorem 17-17.2-4: the induced finite projective owner. -/
abbrev subgroupInduction {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    FiniteProjectiveGroupAlgebraModule k G :=
  let ρ := Rep.ind H.subtype P.toRep
  let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  letI : Module.Finite k ρ := subgroupInduction_finite P
  letI : Module k Wk := Module.compHom Wk (algebraMap k k[G])
  letI : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : ρ →ₗ[k] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  letI : Module.Finite k Wk :=
    Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  letI : Module.Finite k[G] Wk := Module.Finite.of_restrictScalars_finite k k[G] Wk
  let W : FGModuleCat k[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[G] Wk
    infer_instance
  let hW : Module.Projective k[G] W := by
    simpa [Wk, W, ρ, Rep.toModuleMonoidAlgebra] using subgroupInduction_projective P
  ⟨W, hW⟩

end FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 17-17.2-4: the additive lift sending `[P]` to `[Ind_H^G(P)]`. -/
private abbrev finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift
    (H : Subgroup G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k H) →+ P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦
    [FiniteProjectiveGroupAlgebraModule.subgroupInduction P]ₚ₀

/-- Helper for Theorem 17-17.2-4: forgetting a short complex of finite projective `k[G]`-modules
to `ModuleCat k[G]` keeps the same structure maps. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplex
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (ModuleCat k[G]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)

/-- Helper for Theorem 17-17.2-4: a short exact sequence of projective owners stays short exact
after forgetting to `ModuleCat k[G]`. -/
private theorem finiteProjective_shortExact_underlying_moduleCat
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S).ShortExact := by
  letI : IsLocalRing k :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ by
      by_cases ha : a = 0
      · right
        simp [ha]
      · left
        exact isUnit_iff_ne_zero.mpr ha
  simpa [finiteProjective_underlying_moduleCat_shortComplex] using
    finiteProjective_shortExact_underlying_moduleCat_shortExact_local
      (A := k) (G := G) S hS

/-- Helper for Theorem 17-17.2-4: a forgotten short exact sequence in `ModuleCat k[G]` repackages
to a short exact sequence of finite projective owners. -/
private theorem finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hS :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S).ShortExact) :
    S.ShortExact := by
  let Smod := finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S
  let _ : Projective Smod.X₃ := by
    change Projective S.X₃.V
    infer_instance
  let hsplMod : Smod.Splitting := hS.splittingOfProjective
  let r : S.X₂ ⟶ S.X₁ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.r.hom)
  let s : S.X₃ ⟶ S.X₂ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.s.hom)
  have hf_r : S.f ≫ r = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, r, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.f_r x
  have hs_g : s ≫ S.g = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, s, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.s_g x
  have hid : r ≫ S.f + S.g ≫ s = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa [Smod, r, s, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.id x
  exact
    ({ r := r
       s := s
       f_r := hf_r
       s_g := hs_g
       id := hid } : S.Splitting).shortExact

/-- Helper for Theorem 17-17.2-4: the canonical functor from finite projective `k[G]`-modules to
`Rep k G`. -/
private abbrev finiteProjective_toRepFunctor :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Theorem 17-17.2-4: first forget a finite projective owner to `Rep k H`, then
apply subgroup induction, then forget back to `ModuleCat k[G]`. -/
private abbrev subgroupInduction_projective_moduleFunctor {H : Subgroup G} :
    FiniteProjectiveGroupAlgebraModule k H ⥤ ModuleCat k[G] :=
  (finiteProjective_toRepFunctor (k := k) (G := H)) ⋙
    (Rep.indFunctor k H.subtype) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Theorem 17-17.2-4: forget a finite projective owner to its ambient `k[G]`-module.
-/
private abbrev finiteProjective_forgetToModuleFunctor :
    FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι

/-- Helper for Theorem 17-17.2-4: the induced owner morphism obtained from the ambient
`k[G]`-linear map. -/
private abbrev subgroupInduction_projective_owner_map {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k H} (f : P ⟶ Q) :
    FiniteProjectiveGroupAlgebraModule.subgroupInduction P ⟶
      FiniteProjectiveGroupAlgebraModule.subgroupInduction Q :=
  Functor.preimage (finiteProjective_forgetToModuleFunctor (k := k) (G := G))
    ((subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Theorem 17-17.2-4: forgetting the induced owner morphism recovers the ambient
induced `ModuleCat` map. -/
private theorem subgroupInduction_projective_owner_map_forget {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k H} (f : P ⟶ Q) :
    (finiteProjective_forgetToModuleFunctor (k := k) (G := G)).map
        (subgroupInduction_projective_owner_map (k := k) (G := G) f) =
      (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f := by
  exact
    Functor.map_preimage (X := FiniteProjectiveGroupAlgebraModule.subgroupInduction P)
      (Y := FiniteProjectiveGroupAlgebraModule.subgroupInduction Q)
      (finiteProjective_forgetToModuleFunctor (k := k) (G := G))
      ((subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Theorem 17-17.2-4: the transported structure maps of the induced owner short complex
still compose to zero. -/
private theorem subgroupInduction_projective_owner_shortComplex_zero {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    subgroupInduction_projective_owner_map (k := k) (G := G) S.f ≫
        subgroupInduction_projective_owner_map (k := k) (G := G) S.g = 0 := by
  apply (finiteProjective_forgetToModuleFunctor (k := k) (G := G)).map_injective
  rw [Functor.map_comp]
  rw [subgroupInduction_projective_owner_map_forget (k := k) (G := G) S.f]
  rw [subgroupInduction_projective_owner_map_forget (k := k) (G := G) S.g]
  calc
    (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map S.f ≫
        (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map S.g
        =
      (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map
        (S.f ≫ S.g) := by
          rw [Functor.map_comp]
    _ = 0 := by
          rw [S.zero, Functor.map_zero]

/-- Helper for Theorem 17-17.2-4: subgroup induction on finite projective owners. -/
private abbrev subgroupInduction_projective_owner_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
  ShortComplex.mk
    (subgroupInduction_projective_owner_map (k := k) (G := G) S.f)
    (subgroupInduction_projective_owner_map (k := k) (G := G) S.g)
    (subgroupInduction_projective_owner_shortComplex_zero (k := k) (G := G) S)

/-- Helper for Theorem 17-17.2-4: after forgetting to `ModuleCat`, the induced projective-owner
short complex is the mapped ambient subgroup-induction short complex. -/
private theorem subgroupInduction_projective_owner_underlying_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S) =
      S.map (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)) := by
  cases S
  rename_i X₁ X₂ X₃ f g zero
  simp only [subgroupInduction_projective_owner_shortComplex,
    finiteProjective_underlying_moduleCat_shortComplex, ShortComplex.map]
  congr 1
  · simpa [subgroupInduction_projective_moduleFunctor, finiteProjective_toRepFunctor,
      finiteProjective_forgetToModuleFunctor] using
      subgroupInduction_projective_owner_map_forget (k := k) (G := G) f
  · simpa [subgroupInduction_projective_moduleFunctor, finiteProjective_toRepFunctor,
      finiteProjective_forgetToModuleFunctor] using
      subgroupInduction_projective_owner_map_forget (k := k) (G := G) g

/-- Helper for Theorem 17-17.2-4: subgroup induction preserves short exactness on the ambient
forgotten projective-module complex. -/
private theorem subgroupInduction_projective_module_shortExact {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) (hS : S.ShortExact) :
    (S.map (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H))).ShortExact := by
  have hMod :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := H) S).ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat (k := k) (G := H) S hS
  have hRep :
      (((finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := H) S).map
        (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map
          (Rep.indFunctor k H.subtype)).ShortExact := by
    simpa using
      (hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map_of_exact
        (Rep.indFunctor k H.subtype)
  simpa [subgroupInduction_projective_moduleFunctor, finiteProjective_underlying_moduleCat_shortComplex,
    finiteProjective_toRepFunctor] using
    hRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])

/-- Helper for Theorem 17-17.2-4: subgroup induction preserves short exact sequences of finite
projective owners. -/
private theorem subgroupInduction_projective_owner_shortExact {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) (hS : S.ShortExact) :
    (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S).ShortExact := by
  have hMod :
      (S.map (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H))).ShortExact :=
    subgroupInduction_projective_module_shortExact (k := k) (G := G) S hS
  have hUnderlying :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S)).ShortExact := by
    simpa [subgroupInduction_projective_owner_underlying_shortComplex (k := k) (G := G) S] using
      hMod
  exact finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (k := k) (G := G)
    (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S)
    hUnderlying

/-- Helper for Theorem 17-17.2-4: the defining relations of `P_k(H)` map to zero under subgroup
induction. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker
    (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k H ≤
      (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift H).ker := by
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₂]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right (A := k) (G := G)
      (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S)
      (subgroupInduction_projective_owner_shortExact (k := k) (G := G) S hS)
  have hrelation' :
      [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₂]ₚ₀ =
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ +
          [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀ := by
    simpa [subgroupInduction_projective_owner_shortComplex] using hrelation
  calc
    [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₂]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ =
      ([FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ +
          [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀) -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ := by
          rw [hrelation']
    _ = [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀ := by
          abel

namespace Subgroup

/-- Helper for Theorem 17-17.2-4: subgroup induction on `P_k(H)`. -/
def finiteProjectiveGroupAlgebraGrothendieckGroupInduction
    (k : Type u) [Field k] (H : Subgroup G) :
    P₀[k](H) →+ P₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)
    (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift H)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker H)

scoped[FiniteProjectiveGrothendieckInduction] notation "Ind[" H "]" =>
  Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction _ H

section

open scoped FiniteProjectiveGrothendieckInduction

/-- Helper for Theorem 17-17.2-4: subgroup induction on a projective generator class. -/
@[simp] theorem finiteProjectiveGroupAlgebraGrothendieckGroupInduction_apply_class
    (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k H) :
    (Ind[H]) [P]ₚ₀ =
      [FiniteProjectiveGroupAlgebraModule.subgroupInduction P]ₚ₀ := by
  rfl

/-- Helper for Theorem 17-17.2-4: the rationalized subgroup induction map on `P_k(H)`. -/
def finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
    (k : Type u) [Field k] (H : Subgroup G) :
    (ℚ ⊗[ℤ] P₀[k](H)) →ₗ[ℚ] ℚ ⊗[ℤ] P₀[k](G) :=
  ((Ind[H]).toIntLinearMap).baseChange ℚ

end
end Subgroup

end

end Representation
