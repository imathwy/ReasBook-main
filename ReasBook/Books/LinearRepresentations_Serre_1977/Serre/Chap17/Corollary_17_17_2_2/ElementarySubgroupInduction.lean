import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct

noncomputable section

universe u w x

namespace Representation

section ElementarySubgroupInduction

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling:
* Primary domain: subgroup induction on Grothendieck groups of finite-dimensional and finite
  projective modular representations.
* Relevant owner declarations inspected in this domain:
  `Rep.ind H.subtype`,
  `Rep.toModuleMonoidAlgebra.obj`,
  `FDRep.of`,
  and `FiniteProjectiveGroupAlgebraModule`.
* Best owner abstraction: the ambient induction owner is `Rep.ind H.subtype`; the source-facing
  objects in this file are the induced maps it defines on `R₀[k](H)` and `P₀[k](H)`.
* Source/core/bridge triage:
  source-facing: the subgroup-induction maps on `R₀[k](H)` and `P₀[k](H)`;
  core/canonical: `Rep.ind H.subtype`, together with the Chapter `14` owners `R₀[k](G)` and
    `FiniteProjectiveGroupAlgebraModule k G`;
  bridge/view: the bundled induced owners `FDRep.subgroupInduction` and
    `FiniteProjectiveGroupAlgebraModule.subgroupInduction`, plus the rationalized induction maps.
* Primitive data: actual induced representations and projective induced modules.
* Derived API: quotient lifts to Grothendieck groups, evaluation on classes, and rationalized
  induction maps.
-/

namespace FDRep

end FDRep

/-- Helper for Corollary 17-17.2-2: the induced morphism on bundled finite-dimensional
representations is obtained by transporting `Rep.indMap` back through `FDRep`. -/
private abbrev subgroupInduction_map {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    FDRep.subgroupInduction V ⟶ FDRep.subgroupInduction W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))

/-- Helper for Corollary 17-17.2-2: forgetting an induced `FDRep` morphism recovers the
underlying `Rep.indMap`. -/
private theorem subgroupInduction_map_forget {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    (forget₂ (FDRep k G) (Rep k G)).map (subgroupInduction_map (k := k) (G := G) f) =
      Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f) := by
  -- `subgroupInduction_map` is defined by transport across `FDRep.forget₂HomLinearEquiv`.
  change (FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W)).symm
    ((FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W))
      (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))) =
    Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Corollary 17-17.2-2: a short complex of `FDRep k H` induces termwise to a short
complex of `FDRep k G`. -/
private abbrev subgroupInduction_shortComplex {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) : ShortComplex (FDRep k G) :=
  ShortComplex.mk
    (subgroupInduction_map (k := k) (G := G) S.f)
    (subgroupInduction_map (k := k) (G := G) S.g)
    (by
      -- After forgetting to `Rep`, this is exactly the image of `S` under `Rep.ind H.subtype`.
      apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      rw [Functor.map_comp]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.f]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.g]
      simpa using
        (((S.map (forget₂ (FDRep k H) (Rep k H))).map
          (Rep.indFunctor k H.subtype)).zero))

/-- Helper for Corollary 17-17.2-2: induction along `H ≤ G` preserves short exact sequences of
finite-dimensional representations. -/
private theorem subgroupInduction_shortExact {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) (hS : S.ShortExact) :
    (subgroupInduction_shortComplex (k := k) (G := G) S).ShortExact := by
  -- First verify short exactness after forgetting to `Rep`, where functorial exactness is built
  -- into `ShortExact.map_of_exact`.
  have hRep :
      (((subgroupInduction_shortComplex (k := k) (G := G) S).map
        (forget₂ (FDRep k G) (Rep k G)))).ShortExact := by
    simpa [subgroupInduction_shortComplex, subgroupInduction_map_forget] using
      (hS.map_of_exact (forget₂ (FDRep k H) (Rep k H))).map_of_exact
        (Rep.indFunctor k H.subtype)
  -- Then reflect exactness, mono, and epi back to `FDRep`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((subgroupInduction_shortComplex (k := k) (G := G) S).exact_map_iff_of_faithful
        (forget₂ (FDRep k G) (Rep k G))).1 hRep.exact
  · exact (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g

/-- The additive lift on the free abelian group of finite-dimensional `k`-representations sending
`[V]` to the induced class `[Ind_H^G(V)]`. -/
private abbrev finiteRepGrothendieckGroupInductionLift (H : Subgroup G) :
    FreeAbelianGroup (FDRep k H) →+ R₀[k](G) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.subgroupInduction V]₀

-- Proof sketch: induction along a subgroup inclusion is exact because `k[G]` is free as a
-- right `k[H]`-module, so a short exact sequence of finite-dimensional `H`-representations gives
-- the defining Grothendieck relation after induction to `G`.
/-- The defining relations of `R_k(H)` map to zero under subgroup induction on the free abelian
group of finite-dimensional representations. -/
private theorem finiteRepGrothendieckRelations_le_inductionLift_ker (H : Subgroup G) :
    finiteRepGrothendieckRelations k H ≤ (finiteRepGrothendieckGroupInductionLift H).ker := by
  -- Evaluate subgroup induction on each defining short-exact-sequence generator.
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

scoped[FiniteRepGrothendieckInduction] notation "Ind[" H "]" =>
  Representation.Subgroup.finiteRepGrothendieckGroupInduction _ H

section

open scoped FiniteRepGrothendieckInduction

/-- The canonical `ℚ`-linear induction map
`ℚ ⊗ R_k(H) → ℚ ⊗ R_k(G)` on rationalized Grothendieck groups of finite-dimensional
`k`-representations. -/
def finiteRepGrothendieckGroupRationalizedInduction (k : Type u) [Field k] (H : Subgroup G) :
    (ℚ ⊗[ℤ] R₀[k](H)) →ₗ[ℚ] ℚ ⊗[ℤ] R₀[k](G) :=
  ((Ind[H]).toIntLinearMap).baseChange ℚ

end
end Subgroup

end

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FiniteProjectiveGroupAlgebraModule

-- Proof sketch: the induced representation `Rep.ind H.subtype P.toRep` is finite-dimensional over
-- `k` because induction preserves finite generation over the base field.
/-- Inducing a finite projective `k[H]`-representation along `H ≤ G` preserves
finite-dimensionality over `k`. -/
theorem subgroupInduction_finite {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Finite k (Rep.ind H.subtype P.toRep) := by
  -- As above, package the coinvariants quotient first and then appeal to the quotient instance.
  let ρ := Representation.tprod ((leftRegular k G).comp H.subtype) P.toRep.ρ
  let M :=
    (TensorProduct k (G →₀ k) P.toRep) ⧸
      Representation.Coinvariants.ker (k := k) (G := H)
        (V := TensorProduct k (G →₀ k) P.toRep) ρ
  -- The tensor module is finite over `k`, hence so is its quotient by the coinvariants kernel.
  let _ : Module.Finite k M := by
    infer_instance
  change Module.Finite k M
  infer_instance

-- Proof sketch: subgroup induction is tensoring with the bimodule `k[G]`, and `k[G]` is free as
-- a right `k[H]`-module; tensoring a projective module with a free bimodule remains projective.
/-- Inducing a finite projective `k[H]`-representation along `H ≤ G` preserves projectivity over
the group algebra. -/
theorem subgroupInduction_projective {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Projective k[G] (Rep.ind H.subtype P.toRep).ρ.asModule := by
  -- Route correction: instead of expanding induction as a tensor quotient, first transport
  -- projectivity of `P` to a projective object of `Rep k H`.
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
  -- The induction functor preserves projective objects because it is left adjoint to
  -- restriction, and restriction preserves epimorphisms.
  have hInd : Projective (Rep.ind H.subtype P.toRep) := by
    simpa using Adjunction.map_projective (Rep.indResAdjunction k H.subtype) P.toRep hP
  -- Finally move back across `Rep ≌ ModuleCat k[G]` to recover module-theoretic projectivity.
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

/-- The finite projective `k[G]`-representation induced from a finite projective
`k[H]`-representation. -/
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

/-- The additive lift on the free abelian group of finite projective `k[H]`-representations
sending `[P]` to the induced class `[Ind_H^G(P)]`. -/
private abbrev finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift
    (H : Subgroup G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k H) →+ P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦
    [FiniteProjectiveGroupAlgebraModule.subgroupInduction P]ₚ₀

/-- Helper for Corollary 17-17.2-2: forgetting a short complex of finite projective
`k[G]`-modules to `ModuleCat k[G]` keeps the same structure maps. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplex
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (ModuleCat k[G]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)

/-- Helper for Corollary 17-17.2-2: a short exact sequence of projective owners is already short
exact after forgetting to the ambient `ModuleCat k[G]`. -/
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
  -- Over a field, the Chapter `14` local bridge gives the ambient `ModuleCat` short exact
  -- sequence directly.
  simpa [finiteProjective_underlying_moduleCat_shortComplex] using
    finiteProjective_shortExact_underlying_moduleCat_shortExact_field
      (K := k) (G := G) S hS

/-- Helper for Corollary 17-17.2-2: a short exact sequence in the underlying `ModuleCat k[G]`
of projective owners is already short exact in the projective owner category. -/
private theorem finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hS :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S).ShortExact) :
    S.ShortExact := by
  let Smod := finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S
  -- Split the forgotten sequence in `ModuleCat`, then repackage the splitting upstairs.
  let _ : Projective Smod.X₃ := by
    change Projective S.X₃.V
    infer_instance
  let hsplMod : Smod.Splitting := hS.splittingOfProjective
  let r : S.X₂ ⟶ S.X₁ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.r.hom)
  let s : S.X₃ ⟶ S.X₂ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.s.hom)
  have hf_r : S.f ≫ r = 𝟙 _ := by
    -- The module-level retraction of `f` is already an owner morphism.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, r, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.f_r x
  have hs_g : s ≫ S.g = 𝟙 _ := by
    -- The module-level section of `g` is already an owner morphism.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, s, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.s_g x
  have hid : r ≫ S.f + S.g ≫ s = 𝟙 _ := by
    -- The split exactness identity transports componentwise from `ModuleCat`.
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

/-- Helper for Corollary 17-17.2-2: the canonical functor from finite projective `k[G]`-modules
to `Rep k G`. -/
private abbrev finiteProjective_toRepFunctor :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Corollary 17-17.2-2: first forget a finite projective owner to `Rep k H`, then
apply subgroup induction, and finally forget back to the ambient `k[G]`-module. -/
private abbrev subgroupInduction_projective_moduleFunctor {H : Subgroup G} :
    FiniteProjectiveGroupAlgebraModule k H ⥤ ModuleCat k[G] :=
  (finiteProjective_toRepFunctor (k := k) (G := H)) ⋙
    (Rep.indFunctor k H.subtype) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Corollary 17-17.2-2: forget a finite projective owner to its ambient
`k[G]`-module. -/
private abbrev finiteProjective_forgetToModuleFunctor :
    FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι

/-- Helper for Corollary 17-17.2-2: the induced owner morphism should be obtained by packaging the
ambient `k[G]`-linear map coming from `subgroupInduction_projective_moduleFunctor`. -/
private abbrev subgroupInduction_projective_owner_map {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k H} (f : P ⟶ Q) :
    FiniteProjectiveGroupAlgebraModule.subgroupInduction P ⟶
      FiniteProjectiveGroupAlgebraModule.subgroupInduction Q :=
  -- Pull the ambient induced module map back through the full forgetful functor.
  Functor.preimage (finiteProjective_forgetToModuleFunctor (k := k) (G := G))
    ((subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Corollary 17-17.2-2: forgetting the induced owner morphism recovers the ambient
induced `ModuleCat` map. -/
private theorem subgroupInduction_projective_owner_map_forget {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k H} (f : P ⟶ Q) :
    (finiteProjective_forgetToModuleFunctor (k := k) (G := G)).map
        (subgroupInduction_projective_owner_map (k := k) (G := G) f) =
      (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f := by
  -- `subgroupInduction_projective_owner_map` is defined as the full preimage of the ambient map.
  exact
    Functor.map_preimage (X := FiniteProjectiveGroupAlgebraModule.subgroupInduction P)
      (Y := FiniteProjectiveGroupAlgebraModule.subgroupInduction Q)
      (finiteProjective_forgetToModuleFunctor (k := k) (G := G))
      ((subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Corollary 17-17.2-2: the transported structure maps of the induced owner short
complex still compose to zero. -/
private theorem subgroupInduction_projective_owner_shortComplex_zero {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    subgroupInduction_projective_owner_map (k := k) (G := G) S.f ≫
        subgroupInduction_projective_owner_map (k := k) (G := G) S.g = 0 := by
  -- Forget to `ModuleCat`, where the induced short complex is literally the image of `S`.
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

/-- Helper for Corollary 17-17.2-2: subgroup induction on finite projective owners is obtained by
inducing the ambient `Rep` short complex and repackaging the resulting module maps. -/
private abbrev subgroupInduction_projective_owner_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
  ShortComplex.mk
    (subgroupInduction_projective_owner_map (k := k) (G := G) S.f)
    (subgroupInduction_projective_owner_map (k := k) (G := G) S.g)
    (subgroupInduction_projective_owner_shortComplex_zero (k := k) (G := G) S)

/-- Helper for Corollary 17-17.2-2: after forgetting to `ModuleCat`, the induced projective-owner
short complex is the ambient subgroup-induction image of the forgotten source complex. -/
private theorem subgroupInduction_projective_owner_underlying_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S) =
      S.map (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H)) := by
  -- Both object triples agree definitionally; the only work is to identify the two structure maps.
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

/-- Helper for Corollary 17-17.2-2: the ambient `ModuleCat` short complex obtained by mapping a
forgotten projective-owner short exact sequence through subgroup induction is short exact. -/
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
    -- Apply the exact functors one at a time so the ambient route stays transparent.
    simpa using
      (hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H)).map_of_exact
        (Rep.indFunctor k H.subtype)
  -- The final forgetful step back to `ModuleCat k[G]` preserves short exactness as well.
  simpa [subgroupInduction_projective_moduleFunctor, finiteProjective_underlying_moduleCat_shortComplex,
    finiteProjective_toRepFunctor] using
    hRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])

/-- Helper for Corollary 17-17.2-2: subgroup induction preserves short exact sequences of finite
projective `k[H]`-modules. -/
private theorem subgroupInduction_projective_owner_shortExact {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) (hS : S.ShortExact) :
    (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S).ShortExact := by
  -- Route correction: do not split the induced owner complex directly. First prove short
  -- exactness for the mapped ambient `ModuleCat` complex, then reflect it back upstairs.
  have hMod :
      (S.map (subgroupInduction_projective_moduleFunctor (k := k) (G := G) (H := H))).ShortExact :=
    subgroupInduction_projective_module_shortExact (k := k) (G := G) S hS
  have hUnderlying :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S)).ShortExact := by
    -- Identify the forgotten induced owner complex with the mapped ambient module complex.
    simpa [subgroupInduction_projective_owner_underlying_shortComplex (k := k) (G := G) S] using
      hMod
  -- Repackage the ambient short exact sequence into the projective-owner category.
  exact finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (k := k) (G := G)
    (subgroupInduction_projective_owner_shortComplex (k := k) (G := G) S)
    hUnderlying

-- Proof sketch: induction along `H ≤ G` is exact on projective representations for the same
-- tensor-product reason as above, so the short-exact-sequence relations defining `P_k(H)` map to
-- zero after induction to `G`.
/-- The defining relations of `P_k(H)` map to zero under subgroup induction on the free abelian
group of finite projective representations. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_inductionLift_ker
    (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k H ≤
      (finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift H).ker := by
  -- Evaluate subgroup induction on each defining short-exact-sequence generator.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₂]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀ = 0
  rw [sub_eq_zero]
  obtain ⟨e⟩ := hS
  have hrelation :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right (A := k) (G := G)
      (subgroupInduction_projective_owner_shortComplex (k := k) (G := G)
        (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e))
      (shortExact_middle_nonempty_linearEquiv_prod_field _
        (subgroupInduction_projective_owner_shortExact (k := k) (G := G)
          (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e)
          (splitShortComplexOfLinearEquivProd_shortExact S.X₁ S.X₂ S.X₃ e)))
  have hrelation' :
      [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₂]ₚ₀ =
        [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₁]ₚ₀ +
          [FiniteProjectiveGroupAlgebraModule.subgroupInduction S.X₃]ₚ₀ := by
    -- The induced short complex has the induced projective owners as its three objects.
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

/-- Bridge/view: the induction homomorphism `Ind_H^G : P_k(H) → P_k(G)` on Grothendieck groups of
finite projective `k`-representations. -/
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

/-- On a generator class, subgroup induction on `P_k(H)` gives the class of the induced finite
projective representation in `P_k(G)`. -/
-- Proof sketch: `finiteProjectiveGroupAlgebraGrothendieckGroupInduction H` is the quotient lift
-- of `finiteProjectiveGroupAlgebraGrothendieckGroupInductionLift H`, so it carries the class of
-- a projective representation to the class of its induced projective representation.
@[simp] theorem finiteProjectiveGroupAlgebraGrothendieckGroupInduction_apply_class
    (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k H) :
    (Ind[H]) [P]ₚ₀ =
      [FiniteProjectiveGroupAlgebraModule.subgroupInduction P]ₚ₀ := by
  -- Evaluate the quotient lift on the generator `FreeAbelianGroup.of P`.
  rfl

/-- The canonical `ℚ`-linear induction map
`ℚ ⊗ P_k(H) → ℚ ⊗ P_k(G)` on rationalized Grothendieck groups of finite projective
`k`-representations. -/
def finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
    (k : Type u) [Field k] (H : Subgroup G) :
    (ℚ ⊗[ℤ] P₀[k](H)) →ₗ[ℚ] ℚ ⊗[ℤ] P₀[k](G) :=
  ((Ind[H]).toIntLinearMap).baseChange ℚ

end
end Subgroup

end

end ElementarySubgroupInduction

end Representation
