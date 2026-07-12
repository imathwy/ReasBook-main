import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct

noncomputable section

universe u w x

namespace Representation

section ProjectiveSubgroupRestriction

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-!
Restriction homomorphism `Res_H^G : P_k(G) → P_k(H)` on Grothendieck groups of finite projective
modular representations, mirroring the subgroup-*induction* construction in
`Serre.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction`.

The module-level restriction is `Rep.res H.subtype P.toRep`.  It keeps the same underlying
`k`-vector space, so finiteness over `k` is inherited.  Restriction preserves projectivity because
it is the *left* adjoint of coinduction (`Rep.resCoindAdjunction k H.subtype`) and the coinduction
functor preserves epimorphisms; hence `Adjunction.map_projective` carries projective objects to
projective objects.  Restriction is exact, so it descends to the Grothendieck group.

This is the `Res` half of the projection formula used in the proof of Serre's Theorem 39
(Theorem 17-17.2-1), in the finite-projective Grothendieck group `P_k(-)`.
-/

namespace FiniteProjectiveGroupAlgebraModule

-- Proof sketch: restriction keeps the same underlying `k`-vector space, so finiteness over `k` is
-- inherited from the finiteness of `P.toRep`.
/-- Restricting a finite projective `k[G]`-representation along `H ≤ G` preserves
finite-dimensionality over `k`. -/
theorem subgroupRestriction_finite {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k (Rep.res H.subtype P.toRep) := by
  -- `Rep.res` does not change the carrier, so finiteness transports unchanged.
  change Module.Finite k P.toRep
  infer_instance

-- Proof sketch: restriction is left adjoint to coinduction, and coinduction preserves
-- epimorphisms, so restriction preserves projective objects.
/-- Restricting a finite projective `k[G]`-representation along `H ≤ G` preserves projectivity over
the group algebra. -/
theorem subgroupRestriction_projective {H : Subgroup G}
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k[H] (Rep.res H.subtype P.toRep).ρ.asModule := by
  -- First transport projectivity of `P` to a projective object of `Rep k G`.
  have hP : Projective P.toRep := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff]
    let M : ModuleCat k[G] := ModuleCat.of k[G] P.V
    have hM : Projective M := by
      rw [← IsProjective.iff_projective (R := k[G]) (P := P.V)]
      exact P.projective
    have hIso : Rep.toModuleMonoidAlgebra.obj P.toRep ≅ M := by
      simpa [M, FiniteProjectiveGroupAlgebraModule.toRep] using
        Rep.counitIso (k := k) (G := G) M
    exact Projective.of_iso hIso.symm hM
  -- Restriction preserves projectives because it is left adjoint to coinduction, and coinduction
  -- preserves epimorphisms.
  have hRes : Projective (Rep.res H.subtype P.toRep) := by
    have := Adjunction.map_projective (Rep.resCoindAdjunction.{u} k H.subtype) P.toRep hP
    simpa using this
  -- Finally move back across `Rep ≌ ModuleCat k[H]` to recover module-theoretic projectivity.
  change Module.Projective k[H] (Rep.toModuleMonoidAlgebra.obj (Rep.res H.subtype P.toRep))
  have hModObj : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.res H.subtype P.toRep)) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff (Rep.res H.subtype P.toRep)).2 hRes
  letI : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.res H.subtype P.toRep)) := hModObj
  infer_instance

instance {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k (Rep.res H.subtype P.toRep) :=
  subgroupRestriction_finite P

instance {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k[H] (Rep.res H.subtype P.toRep).ρ.asModule :=
  subgroupRestriction_projective P

/-- The finite projective `k[H]`-representation obtained by restricting a finite projective
`k[G]`-representation along `H ≤ G`. -/
abbrev subgroupRestriction {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule k H :=
  let ρ := Rep.res H.subtype P.toRep
  let Wk : ModuleCat k[H] := Rep.toModuleMonoidAlgebra.obj ρ
  letI : Module.Finite k ρ := subgroupRestriction_finite P
  letI : Module k Wk := Module.compHom Wk (algebraMap k k[H])
  letI : IsScalarTower k k[H] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : ρ →ₗ[k] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[H]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  letI : Module.Finite k Wk :=
    Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  letI : Module.Finite k[H] Wk := Module.Finite.of_restrictScalars_finite k k[H] Wk
  let W : FGModuleCat k[H] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[H] Wk
    infer_instance
  let hW : Module.Projective k[H] W := by
    simpa [Wk, W, ρ, Rep.toModuleMonoidAlgebra] using subgroupRestriction_projective P
  ⟨W, hW⟩

end FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 17-17.2-1: the canonical functor from finite projective `k[G]`-modules to
`Rep k G`. -/
private abbrev finiteProjective_toRepFunctor :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
    (ModuleCat.isFG k[G]).ι ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Theorem 17-17.2-1: first forget a finite projective owner over `G` to `Rep k G`,
then restrict to `H`, and finally forget back to the ambient `k[H]`-module. -/
private abbrev subgroupRestriction_projective_moduleFunctor {H : Subgroup G} :
    FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[H] :=
  (finiteProjective_toRepFunctor (k := k) (G := G)) ⋙
    (Rep.resFunctor H.subtype) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Theorem 17-17.2-1: forget a finite projective owner over `H` to its ambient
`k[H]`-module. -/
private abbrev finiteProjective_forgetToModuleFunctorH (H : Subgroup G) :
    FiniteProjectiveGroupAlgebraModule k H ⥤ ModuleCat k[H] :=
  (ObjectProperty.ι (fun M : FGModuleCat k[H] ↦ Module.Projective k[H] M)) ⋙
    (ModuleCat.isFG k[H]).ι

/-- Helper for Theorem 17-17.2-1: the restricted owner morphism is obtained by packaging the
ambient `k[H]`-linear map coming from `subgroupRestriction_projective_moduleFunctor`. -/
private abbrev subgroupRestriction_projective_owner_map {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (f : P ⟶ Q) :
    FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) P ⟶
      FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) Q :=
  -- Pull the ambient restricted module map back through the full forgetful functor.
  Functor.preimage (finiteProjective_forgetToModuleFunctorH (k := k) (G := G) H)
    ((subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Theorem 17-17.2-1: forgetting the restricted owner morphism recovers the ambient
restricted `ModuleCat` map. -/
private theorem subgroupRestriction_projective_owner_map_forget {H : Subgroup G}
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (f : P ⟶ Q) :
    (finiteProjective_forgetToModuleFunctorH (k := k) (G := G) H).map
        (subgroupRestriction_projective_owner_map (k := k) (G := G) (H := H) f) =
      (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f := by
  -- `subgroupRestriction_projective_owner_map` is defined as the full preimage of the ambient map.
  exact
    Functor.map_preimage
      (X := FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) P)
      (Y := FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) Q)
      (finiteProjective_forgetToModuleFunctorH (k := k) (G := G) H)
      ((subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map f)

/-- Helper for Theorem 17-17.2-1: the transported structure maps of the restricted owner short
complex still compose to zero. -/
private theorem subgroupRestriction_projective_owner_shortComplex_zero {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    subgroupRestriction_projective_owner_map (k := k) (G := G) (H := H) S.f ≫
        subgroupRestriction_projective_owner_map (k := k) (G := G) (H := H) S.g = 0 := by
  -- Forget to `ModuleCat`, where the restricted short complex is literally the image of `S`.
  apply (finiteProjective_forgetToModuleFunctorH (k := k) (G := G) H).map_injective
  rw [Functor.map_comp]
  rw [subgroupRestriction_projective_owner_map_forget (k := k) (G := G) (H := H) S.f]
  rw [subgroupRestriction_projective_owner_map_forget (k := k) (G := G) (H := H) S.g]
  calc
    (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map S.f ≫
        (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map S.g
        =
      (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)).map
        (S.f ≫ S.g) := by
          rw [Functor.map_comp]
    _ = 0 := by
          rw [S.zero, Functor.map_zero]

/-- Helper for Theorem 17-17.2-1: subgroup restriction on finite projective owners is obtained by
restricting the ambient `Rep` short complex and repackaging the resulting module maps. -/
private abbrev subgroupRestriction_projective_owner_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (FiniteProjectiveGroupAlgebraModule k H) :=
  ShortComplex.mk
    (subgroupRestriction_projective_owner_map (k := k) (G := G) (H := H) S.f)
    (subgroupRestriction_projective_owner_map (k := k) (G := G) (H := H) S.g)
    (subgroupRestriction_projective_owner_shortComplex_zero (k := k) (G := G) (H := H) S)

/-- Helper for Theorem 17-17.2-1: forgetting a short complex of finite projective `k[H]`-modules to
`ModuleCat k[H]` keeps the same structure maps. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplexH {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H)) :
    ShortComplex (ModuleCat k[H]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (A := k) (G := H) S)

/-- Helper for Theorem 17-17.2-1: after forgetting to `ModuleCat`, the restricted projective-owner
short complex is the ambient subgroup-restriction image of the source complex. -/
private theorem subgroupRestriction_projective_owner_underlying_shortComplex {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    finiteProjective_underlying_moduleCat_shortComplexH (k := k) (G := G) (H := H)
        (subgroupRestriction_projective_owner_shortComplex (k := k) (G := G) (H := H) S) =
      S.map (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H)) := by
  -- Both object triples agree definitionally; the only work is to identify the two structure maps.
  cases S
  rename_i X₁ X₂ X₃ f g zero
  simp only [subgroupRestriction_projective_owner_shortComplex,
    finiteProjective_underlying_moduleCat_shortComplexH, ShortComplex.map]
  congr 1
  · simpa [subgroupRestriction_projective_moduleFunctor, finiteProjective_toRepFunctor,
      finiteProjective_forgetToModuleFunctorH] using
      subgroupRestriction_projective_owner_map_forget (k := k) (G := G) (H := H) f
  · simpa [subgroupRestriction_projective_moduleFunctor, finiteProjective_toRepFunctor,
      finiteProjective_forgetToModuleFunctorH] using
      subgroupRestriction_projective_owner_map_forget (k := k) (G := G) (H := H) g

/-- Helper for Theorem 17-17.2-1: the ambient `ModuleCat` short complex obtained by mapping a
projective-owner short exact sequence over `G` through subgroup restriction is short exact. -/
private theorem subgroupRestriction_projective_module_shortExact {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (S.map
        (subgroupRestriction_projective_moduleFunctor (k := k) (G := G) (H := H))).ShortExact := by
  -- Over a field, the source short exact sequence is already short exact in the ambient module.
  have hMod :
      (ShortComplex.mk S.f.hom.hom S.g.hom.hom
        (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)).ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat_shortExact_field (K := k) (G := G) S hS
  -- Apply the exact functors `ofModuleMonoidAlgebra` and `resFunctor` one at a time.
  have hRep :
      (((ShortComplex.mk S.f.hom.hom S.g.hom.hom
        (finiteProjective_underlying_moduleCat_zero (A := k) (G := G) S)).map
        (Rep.ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep k G)).map
          (Rep.resFunctor H.subtype)).ShortExact := by
    simpa using
      (hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep k G)).map_of_exact
        (Rep.resFunctor (k := k) H.subtype)
  -- The final forgetful step back to `ModuleCat k[H]` preserves short exactness as well.
  simpa [subgroupRestriction_projective_moduleFunctor, finiteProjective_toRepFunctor] using
    hRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k H ⥤ ModuleCat k[H])

/-- Helper for Theorem 17-17.2-1: a short exact sequence in the underlying `ModuleCat k[H]` of
projective owners is already short exact in the projective owner category over `H`. -/
private theorem finiteProjective_shortExact_of_underlying_moduleCat_shortExactH {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k H))
    (hS :
      (finiteProjective_underlying_moduleCat_shortComplexH
        (k := k) (G := G) (H := H) S).ShortExact) :
    S.ShortExact := by
  let Smod := finiteProjective_underlying_moduleCat_shortComplexH (k := k) (G := G) (H := H) S
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

/-- Helper for Theorem 17-17.2-1: subgroup restriction preserves short exact sequences of finite
projective `k[G]`-modules. -/
private theorem subgroupRestriction_projective_owner_shortExact {H : Subgroup G}
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (subgroupRestriction_projective_owner_shortComplex
        (k := k) (G := G) (H := H) S).ShortExact := by
  -- Prove short exactness for the mapped ambient `ModuleCat` complex, then reflect it upstairs.
  have hMod :
      (S.map
        (subgroupRestriction_projective_moduleFunctor
          (k := k) (G := G) (H := H))).ShortExact :=
    subgroupRestriction_projective_module_shortExact (k := k) (G := G) (H := H) S hS
  have hUnderlying :
      (finiteProjective_underlying_moduleCat_shortComplexH (k := k) (G := G) (H := H)
        (subgroupRestriction_projective_owner_shortComplex
          (k := k) (G := G) (H := H) S)).ShortExact := by
    -- Identify the forgotten restricted owner complex with the mapped ambient module complex.
    simpa
      [subgroupRestriction_projective_owner_underlying_shortComplex (k := k) (G := G) (H := H) S]
      using hMod
  -- Repackage the ambient short exact sequence into the projective-owner category over `H`.
  exact finiteProjective_shortExact_of_underlying_moduleCat_shortExactH
    (k := k) (G := G) (H := H)
    (subgroupRestriction_projective_owner_shortComplex (k := k) (G := G) (H := H) S)
    hUnderlying

/-- The additive lift on the free abelian group of finite projective `k[G]`-representations sending
`[P]` to the restricted class `[Res_H^G(P)]`. -/
private abbrev finiteProjectiveGroupAlgebraGrothendieckGroupRestrictionLift
    (H : Subgroup G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G) →+
      finiteProjectiveGroupAlgebraGrothendieckGroup k H :=
  FreeAbelianGroup.lift fun P ↦
    [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) P]ₚ₀

-- Proof sketch: restriction along `H ≤ G` is exact (it does not change the underlying space), so
-- the short-exact-sequence relations defining `P_k(G)` map to zero after restriction to `H`.
/-- The defining relations of `P_k(G)` map to zero under subgroup restriction on the free abelian
group of finite projective representations. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_restrictionLift_ker
    (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k G ≤
      (finiteProjectiveGroupAlgebraGrothendieckGroupRestrictionLift (k := k) (G := G) H).ker := by
  -- Evaluate subgroup restriction on each defining short-exact-sequence generator.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₂]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₁]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₃]ₚ₀ = 0
  rw [sub_eq_zero]
  obtain ⟨e⟩ := hS
  have hrelation :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right (A := k) (G := H)
      (subgroupRestriction_projective_owner_shortComplex (k := k) (G := G) (H := H)
        (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e))
      (shortExact_middle_nonempty_linearEquiv_prod_field _
        (subgroupRestriction_projective_owner_shortExact (k := k) (G := G) (H := H)
          (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e)
          (splitShortComplexOfLinearEquivProd_shortExact S.X₁ S.X₂ S.X₃ e)))
  have hrelation' :
      [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₂]ₚ₀ =
        [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₁]ₚ₀ +
          [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₃]ₚ₀ := by
    -- The restricted short complex has the restricted projective owners as its three objects.
    simpa [subgroupRestriction_projective_owner_shortComplex] using hrelation
  calc
    [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₂]ₚ₀ -
        [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₁]ₚ₀ =
      ([FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₁]ₚ₀ +
          [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₃]ₚ₀) -
        [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₁]ₚ₀ := by
          rw [hrelation']
    _ = [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) S.X₃]ₚ₀ := by
          abel

namespace Subgroup

/-- The restriction homomorphism `Res_H^G : P_k(G) → P_k(H)` on Grothendieck groups of finite
projective `k`-representations. -/
def finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
    (k : Type u) [Field k] (H : Subgroup G) :
    finiteProjectiveGroupAlgebraGrothendieckGroup k G →+
      finiteProjectiveGroupAlgebraGrothendieckGroup k H :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k G)
    (finiteProjectiveGroupAlgebraGrothendieckGroupRestrictionLift (k := k) (G := G) H)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_restrictionLift_ker (k := k) (G := G) H)

scoped[FiniteProjectiveGrothendieckRestriction] notation "Res[" H "]" =>
  Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction _ H

/-- On a generator class, subgroup restriction on `P_k(G)` gives the class of the restricted finite
projective representation in `P_k(H)`. -/
@[simp] theorem finiteProjectiveGroupAlgebraGrothendieckGroupRestriction_apply_class
    (H : Subgroup G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    finiteProjectiveGroupAlgebraGrothendieckGroupRestriction k H [P]ₚ₀ =
      [FiniteProjectiveGroupAlgebraModule.subgroupRestriction (H := H) P]ₚ₀ := by
  -- Evaluate the quotient lift on the generator `FreeAbelianGroup.of P`.
  rfl

end Subgroup

end

end ProjectiveSubgroupRestriction

end Representation
