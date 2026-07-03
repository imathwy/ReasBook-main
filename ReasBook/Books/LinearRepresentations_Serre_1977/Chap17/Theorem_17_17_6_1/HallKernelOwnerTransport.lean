import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {h : ℕ}
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance hallKernelOwnerTransportModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance hallKernelOwnerTransportScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: if a semisimple module has at most one isotypic component, then
the whole module is isotypic. -/
lemma isIsotypic_of_subsingleton_isotypicComponents
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M]
    (hsub : Subsingleton (isotypicComponents R M)) :
    IsIsotypic R M := by
  classical
  by_cases hne : Nonempty (isotypicComponents R M)
  · rcases hne with ⟨⟨c, hc⟩⟩
    have hsSup_le : sSup (isotypicComponents R M) ≤ c := by
      exact sSup_le fun m hm ↦ by
        have hm_eq : m = c := by
          exact congrArg Subtype.val (hsub.elim ⟨m, hm⟩ ⟨c, hc⟩)
        exact hm_eq ▸ le_rfl
    have htop_le : (⊤ : Submodule R M) ≤ c := by
      simpa [sSup_isotypicComponents R M] using hsSup_le
    have hc_top : c = ⊤ := top_unique htop_le
    subst hc_top
    have htop_isotypic : IsIsotypic R ↥(⊤ : Submodule R M) := by
      simpa using (IsIsotypic.isotypicComponents hc)
    exact
      (LinearEquiv.isIsotypic_iff (e := (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M))).mp
        htop_isotypic
  · have hEmpty : isotypicComponents R M = ∅ := by
      ext m
      constructor
      · intro hm
        exact hne ⟨⟨m, hm⟩⟩
      · intro hm
        simp at hm
    have htop_eq_bot : (⊤ : Submodule R M) = ⊥ := by
      calc
        (⊤ : Submodule R M) = sSup (isotypicComponents R M) := (sSup_isotypicComponents R M).symm
        _ = sSup (∅ : Set (Submodule R M)) := by simp [hEmpty]
        _ = ⊥ := by simp
    letI : Subsingleton M := by
      refine ⟨fun x y ↦ ?_⟩
      have hx_top : x ∈ (⊤ : Submodule R M) := by simp
      have hy_top : y ∈ (⊤ : Submodule R M) := by simp
      have hx_bot : x ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hx_top
      have hy_bot : y ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hy_top
      have hx_zero : x = 0 := by simpa [Submodule.mem_bot] using hx_bot
      have hy_zero : y = 0 := by simpa [Submodule.mem_bot] using hy_bot
      simp [hx_zero, hy_zero]
    exact IsIsotypic.of_subsingleton R M

/-- Helper for Theorem 17-17.6-1: the owner `k[H]`-action on
`(Subrepresentation.ofSubmodule' N).toRepresentation` agrees with the original action on `N`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (N : Submodule (MonoidAlgebra k H) ρ.asModule)
    (r : MonoidAlgebra k H) (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      rfl
  | add a b ha hb =>
      have hmap :
          (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom (a + b)) x =
            ((((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom a) +
              (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom b)) x := by
        exact
          congrArg (fun f : Module.End k ↥(Subrepresentation.ofSubmodule' N).toSubmodule ↦ f x)
            (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom.map_add a b)
      have haddN :
          (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom (a + b)) x =
            ((a + b) • x : N) := by
        rw [hmap]
        apply Subtype.ext
        simpa [Submodule.coe_add, add_smul] using
          congrArg₂ (fun u v : W ↦ u + v) ha hb
      exact congrArg Subtype.val haddN
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 17-17.6-1: the intrinsic owner module of `Subrepresentation.ofSubmodule' N`
is canonically the original owner submodule `N`. -/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (N : Submodule (MonoidAlgebra k H) ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[MonoidAlgebra k H] N :=
  by
    let ρN : Representation k H N := (Subrepresentation.ofSubmodule' N).toRepresentation
    letI : Module (MonoidAlgebra k H) ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
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
          intro r x
          calc
            ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
              exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
            _ = r • ρN.asModuleEquiv x := by
              exact subrepresentation_ofSubmodule'_asAlgebraHom_apply ρ N r (ρN.asModuleEquiv x) }

/-- Helper for Theorem 17-17.6-1: transporting an `H`-stable subrepresentation through `ρ g`
identifies it with the conjugate representation. -/
private noncomputable def transportedSubrepresentation_rep_equiv
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype))
    (g : G) :
    Representation.Equiv
      ((W.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom))
      (transportedSubrepresentation ρ W g).toRepresentation := by
  let e : W.toSubmodule ≃ₗ[k] (transportedSubrepresentation ρ W g).toSubmodule :=
    Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective W.toSubmodule
  refine Representation.Equiv.mk e ?_
  intro a
  ext w
  change ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V)) = ρ a (ρ g w)
  calc
    ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V))
        = ρ (g * (((MulAut.conjNormal g).symm a : H))) (w : V) := by
            exact
              (LinearMap.congr_fun (ρ.map_mul g (((MulAut.conjNormal g).symm a : H))) (w : V)).symm
    _ = ρ ((a : G) * g) (w : V) := by
          simp [MulAut.conjNormal_symm_apply, mul_assoc]
    _ = ρ a (ρ g w) := by
          exact LinearMap.congr_fun (ρ.map_mul (a : G) g) (w : V)

/-- Helper for Theorem 17-17.6-1: conjugating the `H`-action by `g` leaves the subrepresentation
lattice unchanged. -/
private noncomputable def conjugatedSubrepresentationOrderIso
    {H : Subgroup G} [H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k H W) (g : G) :
    Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        rcases (MulAut.conjNormal g⁻¹).surjective a with ⟨b, rfl⟩
        exact U.apply_mem_toSubmodule b hx }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        exact U.apply_mem_toSubmodule ((MulAut.conjNormal g⁻¹) a) hx }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro U U'
    rfl

/-- Helper for Theorem 17-17.6-1: a representation equivalence induces an order isomorphism on
subrepresentations. -/
private noncomputable def subrepresentationOrderIso
    {H : Type*} [Group H]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k H W} {σ : Representation k H W'}
    (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, by simp⟩, by simp⟩
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h x hx
      have hxmap : e x ∈ U.toSubmodule.map e.toLinearMap :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      have hU'map : e x ∈ U'.toSubmodule.map e.toLinearMap := h hxmap
      rcases Submodule.mem_map.mp hU'map with ⟨y, hy, hyx⟩
      have : y = x := by
        apply e.injective
        simpa using hyx
      simpa [this] using hy
    · intro h x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Theorem 17-17.6-1: the order isomorphism for conjugating the `H`-action leaves the
underlying `k`-submodule unchanged. -/
@[simp] private theorem conjugatedSubrepresentationOrderIso_toSubmodule
    {H : Subgroup G} [H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k H W) (g : G)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    (conjugatedSubrepresentationOrderIso σ g U).toSubmodule = U.toSubmodule :=
  rfl

/-- Helper for Theorem 17-17.6-1: irreducibility transfers across a representation equivalence. -/
private theorem isIrreducible_of_equiv
    {H : Type*} [Group H]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k H W} {σ : Representation k H W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  exact (subrepresentationOrderIso e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Theorem 17-17.6-1: untwisting a conjugated irreducible representation recovers the
original irreducible action. -/
private theorem unconj_isIrreducible
    {H : Subgroup G} [H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k H W) (g : G)
    (hσg :
      let σg : Representation k H W := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      σg.IsIrreducible) :
    σ.IsIrreducible := by
  let σg : Representation k H W := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
  letI : σg.IsIrreducible := hσg
  exact (conjugatedSubrepresentationOrderIso σ g).isSimpleOrder_iff.mp inferInstance

/-- Helper for Theorem 17-17.6-1: a conjugated subrepresentation is definitionally the same
carrier equipped with the untwisted action. -/
private noncomputable def conjugatedSubrepresentation_rep_equiv
    {H : Subgroup G} [H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k H W) (g : G)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    Representation.Equiv U.toRepresentation
      (((conjugatedSubrepresentationOrderIso σ g U).toRepresentation).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  refine Representation.Equiv.mk (LinearEquiv.refl _ _) ?_
  intro a
  ext u
  rfl

/-- Helper for Theorem 17-17.6-1: an intertwining equivalence remains intertwining after
precomposing both actions by the same conjugation automorphism. -/
private noncomputable def representationEquiv_comp_conjNormal
    {H : Subgroup G} [H.Normal]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {σ : Representation k H W₁} {τ : Representation k H W₂}
    (e : σ.Equiv τ) (g : G) :
    Representation.Equiv
      (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (τ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro a
  ext x
  exact LinearMap.congr_fun (e.isIntertwining' ((MulAut.conjNormal g⁻¹) a)) x

/-- Helper for Theorem 17-17.6-1: an owner-module linear equivalence between two
subrepresentations upgrades to a representation equivalence. -/
private noncomputable def subrepresentation_equiv_of_asSubmoduleLinearEquiv
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k H W}
    (U U' : Subrepresentation ρ)
    (e : U.asSubmodule ≃ₗ[MonoidAlgebra k H] U'.asSubmodule) :
    Representation.Equiv U.toRepresentation U'.toRepresentation := by
  let eU := subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) U.asSubmodule
  let eU' := subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) U'.asSubmodule
  let eRep : U.toRepresentation.asModule ≃ₗ[MonoidAlgebra k H] U'.toRepresentation.asModule :=
    (eU.trans e).trans eU'.symm
  let f : U.toRepresentation.IntertwiningMap U'.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule U.toRepresentation
      U'.toRepresentation).symm eRep.toLinearMap
  exact f.ofBijective eRep.bijective

/-- Helper for Theorem 17-17.6-1: restricting a representation equivalence to a subrepresentation
identifies it with the image subrepresentation under `subrepresentationOrderIso`. -/
private noncomputable def subrepresentation_equiv_of_equiv_image
    {H : Type*} [Group H]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k H W} {σ : Representation k H W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Representation.Equiv U.toRepresentation ((subrepresentationOrderIso e U).toRepresentation) := by
  let eSub : U.toSubmodule ≃ₗ[k] (subrepresentationOrderIso e U).toSubmodule :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective U.toSubmodule
  refine Representation.Equiv.mk eSub ?_
  intro a
  ext u
  exact LinearMap.congr_fun (e.isIntertwining' a) u

/-- Helper for Theorem 17-17.6-1: a representation equivalence induces a
`MonoidAlgebra k H`-linear equivalence on the associated owner modules. -/
private noncomputable def representationEquiv_asModuleLinearEquiv
    {H : Type*} [Group H]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k H W} {σ : Representation k H W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra k H] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
      left_inv := by
        intro x
        change e.symm (e x) = x
        simp
      right_inv := by
        intro x
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }

/-- Helper for Theorem 17-17.6-1: the intrinsic owner module of a bundled subrepresentation is
canonically the owner submodule it defines inside the ambient representation. -/
private noncomputable def subrepresentation_owner_intrinsic_linearEquiv
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[MonoidAlgebra k H] U.asSubmodule :=
  by
    simpa using subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) U.asSubmodule

/-- Helper for Theorem 17-17.6-1: the owner and intrinsic views of the submodule lattice of a
subrepresentation are canonically order-isomorphic. -/
private noncomputable def subrepresentation_owner_intrinsic_submodule_orderIso
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (U : Subrepresentation ρ) :
    Submodule (MonoidAlgebra k H) U.toRepresentation.asModule ≃o
      Submodule (MonoidAlgebra k H) U.asSubmodule :=
  by
    let ρU : Representation k H U.toSubmodule := U.toRepresentation
    letI : Module (MonoidAlgebra k H) ρU.asModule := ρU.instModuleMonoidAlgebraAsModule
    exact Submodule.orderIsoMapComap (subrepresentation_owner_intrinsic_linearEquiv (ρ := ρ) U)

/-- Helper for Theorem 17-17.6-1: the intrinsic counterpart of an owner submodule is linearly
equivalent to the original owner submodule. -/
private noncomputable def subrepresentation_owner_intrinsic_submodule_linearEquiv
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (U : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra k H) U.asSubmodule) :
    ((subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) U).symm m) ≃ₗ[MonoidAlgebra k H] m :=
  by
    let ρU : Representation k H U.toSubmodule := U.toRepresentation
    letI : Module (MonoidAlgebra k H) ρU.asModule := ρU.instModuleMonoidAlgebraAsModule
    let e : ρU.asModule ≃ₗ[MonoidAlgebra k H] U.asSubmodule :=
      subrepresentation_owner_intrinsic_linearEquiv (ρ := ρ) U
    let mInt : Submodule (MonoidAlgebra k H) ρU.asModule :=
      (subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) U).symm m
    refine
      { toFun := fun x => ⟨e x, x.property⟩
        invFun := fun y => ⟨e.symm y, by simpa [mInt, subrepresentation_owner_intrinsic_submodule_orderIso, e] using y.property⟩
        left_inv := by
          intro x
          ext
          simp
        right_inv := by
          intro y
          ext
          simp
        map_add' := by
          intro x y
          ext
          rfl
        map_smul' := by
          intro r x
          ext
          simp }

/-- Helper for Theorem 17-17.6-1: simplicity is preserved when moving a submodule between the
owner and intrinsic views of the same subrepresentation. -/
private theorem isSimpleModule_owner_intrinsic_iff
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (U : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra k H) U.asSubmodule) :
    IsSimpleModule (MonoidAlgebra k H)
        ((subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) U).symm m) ↔
      IsSimpleModule (MonoidAlgebra k H) m := by
  simpa using
    (subrepresentation_owner_intrinsic_submodule_linearEquiv (ρ := ρ) U m).isSimpleModule_iff

/-- Helper for Theorem 17-17.6-1: simple intrinsic constituents of an isotypic block become
equivalent after comparison in the owner view of that block. -/
private theorem pulled_back_constituents_equiv_in_isotypic_block
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (W₀ : Subrepresentation ρ)
    (hW₀ : IsIsotypic (MonoidAlgebra k H) W₀.asSubmodule)
    (m m' : Submodule (MonoidAlgebra k H) W₀.toRepresentation.asModule)
    [IsSimpleModule (MonoidAlgebra k H) m]
    [IsSimpleModule (MonoidAlgebra k H) m'] :
    Nonempty (m ≃ₗ[MonoidAlgebra k H] m') := by
  let eW₀ := subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) W₀
  let mOwner : Submodule (MonoidAlgebra k H) W₀.asSubmodule := eW₀ m
  let mOwner' : Submodule (MonoidAlgebra k H) W₀.asSubmodule := eW₀ m'
  have hm_eq : eW₀.symm mOwner = m := by
    simpa [mOwner] using eW₀.symm_apply_apply m
  have hm'_eq : eW₀.symm mOwner' = m' := by
    simpa [mOwner'] using eW₀.symm_apply_apply m'
  have hmOwner_simple : IsSimpleModule (MonoidAlgebra k H) mOwner := by
    letI : IsSimpleModule (MonoidAlgebra k H) (eW₀.symm mOwner) := hm_eq ▸ inferInstance
    have hm_simple : IsSimpleModule (MonoidAlgebra k H) (eW₀.symm mOwner) := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff (ρ := ρ) W₀ mOwner).mp hm_simple
  have hmOwner'_simple : IsSimpleModule (MonoidAlgebra k H) mOwner' := by
    letI : IsSimpleModule (MonoidAlgebra k H) (eW₀.symm mOwner') := hm'_eq ▸ inferInstance
    have hm'_simple : IsSimpleModule (MonoidAlgebra k H) (eW₀.symm mOwner') := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff (ρ := ρ) W₀ mOwner').mp hm'_simple
  unfold IsIsotypic IsIsotypicOfType at hW₀
  letI : IsSimpleModule (MonoidAlgebra k H) mOwner := hmOwner_simple
  letI : IsSimpleModule (MonoidAlgebra k H) mOwner' := hmOwner'_simple
  have hInt :
      Nonempty ((eW₀.symm mOwner) ≃ₗ[MonoidAlgebra k H] (eW₀.symm mOwner')) := by
    rcases hW₀ mOwner mOwner' with ⟨eOwner⟩
    exact
      ⟨((subrepresentation_owner_intrinsic_submodule_linearEquiv
          (ρ := ρ) W₀ mOwner).trans eOwner.symm).trans
          (subrepresentation_owner_intrinsic_submodule_linearEquiv
            (ρ := ρ) W₀ mOwner').symm⟩
  rcases hInt with ⟨eInt⟩
  exact ⟨hm_eq ▸ hm'_eq ▸ eInt⟩

/-- Helper for Theorem 17-17.6-1: a transported restricted Hall-kernel component is again an
isotypic component once the restriction is semisimple. -/
theorem transported_isotypic_component_mem_of_semisimple_restriction
    (ρ : Representation k G V)
    {I : Subgroup G} [I.Normal]
    (hsemisimple :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k I) V) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra k I) V, ∀ g : G,
      (transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule ∈
        isotypicComponents (MonoidAlgebra k I) V := by
  intro ρI
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k I) V := hsemisimple
  intro c g
  let T : Submodule (MonoidAlgebra k I) V :=
    (transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule
  have hc_full :
      (Subrepresentation.ofSubmodule' c.1).asSubmodule.IsFullyInvariant := by
    simpa using (Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2)
  change T ∈ isotypicComponents (MonoidAlgebra k I) V
  rw [mem_isotypicComponents_iff]
  exact
    ⟨transportedSubrepresentation_asSubmodule_isIsotypic ρ c g,
      transportedSubrepresentation_asSubmodule_isFullyInvariant ρ
        (Subrepresentation.ofSubmodule' c.1) g hc_full,
      transportedSubrepresentation_asSubmodule_ne_bot ρ
        (Subrepresentation.ofSubmodule' c.1) g
        (bot_lt_isotypicComponents c.2).ne'⟩

end

end Representation
