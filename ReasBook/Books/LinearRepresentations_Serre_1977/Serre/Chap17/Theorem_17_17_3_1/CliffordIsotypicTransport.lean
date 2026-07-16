import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance cliffordResidueFieldModule : Module A V :=
  Module.compHom V (algebraMap A k)
local instance cliffordResidueFieldIsScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: transporting a fully invariant `C`-stable summand through `ρ g`
preserves full invariance for the restricted `C`-module. -/
lemma transportedSubrepresentation_asSubmodule_isFullyInvariant_c17
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype)) (g : G)
    (hW : W.asSubmodule.IsFullyInvariant) :
    ((transportedSubrepresentation ρ W g).asSubmodule).IsFullyInvariant := by
  let ρH : Representation k H V := ρ.comp H.subtype
  letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
  intro f v hv
  change v ∈ (transportedSubrepresentation ρ W g).toSubmodule at hv
  change f v ∈ (transportedSubrepresentation ρ W g).toSubmodule
  rw [transportedSubrepresentation_toSubmodule] at hv ⊢
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let fInter : ρH.IntertwiningMap ρH :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρH) (σ := ρH)).symm f
  let fConjLin : V →ₗ[k] V := (ρ g⁻¹).comp (fInter.toLinearMap.comp (ρ g))
  have hfConj : ρH.IsIntertwiningMap ρH fConjLin := by
    rw [Representation.isIntertwiningMap_iff]
    intro a x
    let a' : H := ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance (a : G) a.property g⟩
    -- Move the `H`-action across `ρ g`, apply equivariance of `f`, and transport back.
    calc
      fConjLin (ρH a x) = ρ g⁻¹ (fInter (ρ g (ρH a x))) := by
        rfl
      _ = ρ g⁻¹ (fInter (ρH a' (ρ g x))) := by
        congr 1
        simp [ρH, a', mul_assoc]
      _ = ρ g⁻¹ (ρH a' (fInter (ρ g x))) := by
        congr 1
        exact LinearMap.congr_fun (fInter.isIntertwining' a') (ρ g x)
      _ = ρH a (ρ g⁻¹ (fInter (ρ g x))) := by
        simp [ρH, a', mul_assoc]
      _ = ρH a (fConjLin x) := by
        rfl
  let fConj : Module.End (MonoidAlgebra k H) V :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρH) (σ := ρH))
      (fConjLin.intertwiningMap_of_isIntertwiningMap ρH ρH hfConj.isIntertwining)
  have hwConj : fConj w ∈ W.asSubmodule := by
    exact hW fConj hw
  -- Apply full invariance on the original summand, then push the result forward by `ρ g`.
  refine Submodule.mem_map.mpr ⟨fConj w, hwConj, ?_⟩
  change ρ g (ρ g⁻¹ (f (ρ g w))) = f (ρ g w)
  calc
    ρ g (ρ g⁻¹ (f (ρ g w))) = ρ (g * g⁻¹) (f (ρ g w)) := by
      exact (LinearMap.congr_fun (ρ.map_mul g g⁻¹) (f (ρ g w))).symm
    _ = f (ρ g w) := by
      simp

/-- Helper for Theorem 17-17.3-1: transporting an `H`-stable subrepresentation through `ρ g`
identifies it with the conjugate restricted representation. -/
noncomputable def transportedSubrepresentation_rep_equiv_local_c17
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal]
    (W : Subrepresentation (ρ.comp H.subtype)) (g : G) :
    Representation.Equiv
      ((W.toRepresentation).comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (transportedSubrepresentation ρ W g).toRepresentation := by
  let e : W.toSubmodule ≃ₗ[k] (transportedSubrepresentation ρ W g).toSubmodule :=
    Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective W.toSubmodule
  -- The carrier transport is literally the image under `ρ g`, so equivariance is conjugation.
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

/-- Helper for Theorem 17-17.3-1: conjugating the `H`-action does not change the subrepresentation
lattice. -/
noncomputable def conjugatedSubrepresentationOrderIso_local_c17
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {H : Subgroup G} [H.Normal]
    (σ : Representation k H W') (g : G) :
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

/-- Helper for Theorem 17-17.3-1: a representation equivalence transports the subrepresentation
lattice. -/
noncomputable def subrepresentationOrderIso_local_c17
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    {ρ : Representation k A' V'} {σ : Representation k A' W'} (e : ρ.Equiv σ) :
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
    -- Mapping across the intertwiner and back recovers the original stable subspace.
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

/-- Helper for Theorem 17-17.3-1: the order isomorphism for conjugating the `H`-action leaves the
underlying carrier unchanged. -/
@[simp] lemma conjugatedSubrepresentationOrderIso_toSubmodule_local_c17
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {H : Subgroup G} [H.Normal]
    (σ : Representation k H W') (g : G)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    (conjugatedSubrepresentationOrderIso_local_c17 (σ := σ) g U).toSubmodule = U.toSubmodule :=
  rfl

/-- Helper for Theorem 17-17.3-1: irreducibility transfers across a representation equivalence. -/
lemma isIrreducible_of_equiv_local_c17
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    {ρ : Representation k A' V'} {σ : Representation k A' W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  exact (subrepresentationOrderIso_local_c17 e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Theorem 17-17.3-1: the owner `k[H]`-action on the intrinsic module of
`Subrepresentation.ofSubmodule' N` is the original owner action on `N`. -/
lemma subrepresentation_ofSubmodule'_asAlgebraHom_apply_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (N : Submodule (MonoidAlgebra k A') ρ.asModule)
    (r : MonoidAlgebra k A') (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the owner action transported through `Subrepresentation.ofSubmodule'` with the
  -- original owner action on the ambient submodule `N`.
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
          congrArg₂ (fun u v : V' ↦ u + v) ha hb
      exact congrArg Subtype.val haddN
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 17-17.3-1: the intrinsic owner module of `Subrepresentation.ofSubmodule'
N` is canonically the original owner submodule.

Made `private` to avoid a duplicate-name clash with the identically-named non-private helper in
`Serre.Chap10.Theorem_10_10_5_2.IsotypicRestrictionBridge` (both are file-local helpers used only
within their defining modules; co-importing them otherwise fails with "environment already
contains"). -/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (N : Submodule (MonoidAlgebra k A') ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[MonoidAlgebra k A'] N := by
  let ρN : Representation k A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra k A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
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
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply_local_c17 ρ N r (ρN.asModuleEquiv x) }

/-- Helper for Theorem 17-17.3-1: a simple owner submodule yields an irreducible bundled
subrepresentation without any coprime-order hypothesis. -/
lemma isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (N : Submodule (MonoidAlgebra k A') ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra k A') N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation k A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra k A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra k A') inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) N) hN)

/-- Helper for Theorem 17-17.3-1: the intrinsic owner module of a bundled subrepresentation is the
owner submodule it defines in the ambient representation. -/
noncomputable def subrepresentation_owner_intrinsic_linearEquiv_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (W : Subrepresentation ρ) :
    W.toRepresentation.asModule ≃ₗ[MonoidAlgebra k A'] W.asSubmodule := by
  simpa using subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) W.asSubmodule

/-- Helper for Theorem 17-17.3-1: the owner and intrinsic views of the submodule lattice of a
subrepresentation are canonically order-isomorphic. -/
noncomputable def subrepresentation_owner_intrinsic_submodule_orderIso_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (W : Subrepresentation ρ) :
    Submodule (MonoidAlgebra k A') W.toRepresentation.asModule ≃o
      Submodule (MonoidAlgebra k A') W.asSubmodule := by
  let ρW : Representation k A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra k A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  exact Submodule.orderIsoMapComap (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρ) W)

/-- Helper for Theorem 17-17.3-1: the intrinsic counterpart of an owner submodule is linearly
equivalent to the original owner submodule. -/
noncomputable def subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra k A') W.asSubmodule) :
    ((subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρ) W).symm m) ≃ₗ[MonoidAlgebra k A'] m := by
  let ρW : Representation k A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra k A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  let e : ρW.asModule ≃ₗ[MonoidAlgebra k A'] W.asSubmodule :=
    subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρ) W
  let mInt : Submodule (MonoidAlgebra k A') ρW.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρ) W).symm m
  -- The intrinsic submodule is the `comap` of `m` along the canonical owner/intrinsic equivalence.
  refine
    { toFun := fun x => ⟨e x, x.property⟩
      invFun := fun y => ⟨e.symm y, by simpa [mInt, subrepresentation_owner_intrinsic_submodule_orderIso_local_c17, e] using y.property⟩
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

/-- Helper for Theorem 17-17.3-1: simplicity is preserved when moving a submodule between the
owner and intrinsic views of the same subrepresentation. -/
lemma isSimpleModule_owner_intrinsic_iff_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra k A') W.asSubmodule) :
    IsSimpleModule (MonoidAlgebra k A')
        ((subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρ) W).symm m) ↔
      IsSimpleModule (MonoidAlgebra k A') m := by
  simpa using
    (subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17 (ρ := ρ) W m).isSimpleModule_iff

/-- Helper for Theorem 17-17.3-1: simple intrinsic constituents of an isotypic block become
equivalent after comparison in the owner view of that block. -/
lemma pulled_back_constituents_equiv_in_isotypic_block_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k A' V') (W₀ : Subrepresentation ρ)
    (hW₀ : IsIsotypic (MonoidAlgebra k A') W₀.asSubmodule)
    (m m' : Submodule (MonoidAlgebra k A') W₀.toRepresentation.asModule)
    [IsSimpleModule (MonoidAlgebra k A') m]
    [IsSimpleModule (MonoidAlgebra k A') m'] :
    Nonempty (m ≃ₗ[MonoidAlgebra k A'] m') := by
  let eW₀ := subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρ) W₀
  let mOwner : Submodule (MonoidAlgebra k A') W₀.asSubmodule := eW₀ m
  let mOwner' : Submodule (MonoidAlgebra k A') W₀.asSubmodule := eW₀ m'
  have hm_eq : eW₀.symm mOwner = m := by
    simpa [mOwner] using eW₀.symm_apply_apply m
  have hm'_eq : eW₀.symm mOwner' = m' := by
    simpa [mOwner'] using eW₀.symm_apply_apply m'
  have hmOwner_simple : IsSimpleModule (MonoidAlgebra k A') mOwner := by
    letI : IsSimpleModule (MonoidAlgebra k A') (eW₀.symm mOwner) := hm_eq ▸ inferInstance
    have hm_simple : IsSimpleModule (MonoidAlgebra k A') (eW₀.symm mOwner) := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff_local_c17 (ρ := ρ) W₀ mOwner).mp hm_simple
  have hmOwner'_simple : IsSimpleModule (MonoidAlgebra k A') mOwner' := by
    letI : IsSimpleModule (MonoidAlgebra k A') (eW₀.symm mOwner') := hm'_eq ▸ inferInstance
    have hm'_simple : IsSimpleModule (MonoidAlgebra k A') (eW₀.symm mOwner') := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff_local_c17 (ρ := ρ) W₀ mOwner').mp hm'_simple
  unfold IsIsotypic IsIsotypicOfType at hW₀
  letI : IsSimpleModule (MonoidAlgebra k A') mOwner := hmOwner_simple
  letI : IsSimpleModule (MonoidAlgebra k A') mOwner' := hmOwner'_simple
  have hInt :
      Nonempty ((eW₀.symm mOwner) ≃ₗ[MonoidAlgebra k A'] (eW₀.symm mOwner')) := by
    rcases hW₀ mOwner mOwner' with ⟨eOwner⟩
    exact
      ⟨((subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17
          (ρ := ρ) W₀ mOwner).trans eOwner.symm).trans
          (subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17
            (ρ := ρ) W₀ mOwner').symm⟩
  rcases hInt with ⟨eInt⟩
  exact ⟨hm_eq ▸ hm'_eq ▸ eInt⟩

/-- Helper for Theorem 17-17.3-1: a representation equivalence induces an owner-module linear
equivalence on the corresponding modules. -/
noncomputable def representationEquiv_asModuleLinearEquiv_local_c17
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    {ρ : Representation k A' V'} {σ : Representation k A' W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra k A'] σ.asModule := by
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

/-- Helper for Theorem 17-17.3-1: untwisting a conjugated irreducible representation recovers
irreducibility of the original action. -/
lemma unconj_isIrreducible_local_c17
    {H : Subgroup G} [H.Normal]
    {W' : Type*} [AddCommGroup W'] [Module k W']
    (σ : Representation k H W') (g : G)
    (hσg :
      let σg : Representation k H W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      σg.IsIrreducible) :
    σ.IsIrreducible := by
  let σg : Representation k H W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
  letI : σg.IsIrreducible := hσg
  exact (conjugatedSubrepresentationOrderIso_local_c17 (σ := σ) g).isSimpleOrder_iff.mp inferInstance

/-- Helper for Theorem 17-17.3-1: a conjugated subrepresentation is definitionally the same
carrier with the untwisted action. -/
noncomputable def conjugatedSubrepresentation_rep_equiv_local_c17
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {H : Subgroup G} [H.Normal]
    (σ : Representation k H W') (g : G)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    Representation.Equiv U.toRepresentation
      (((conjugatedSubrepresentationOrderIso_local_c17 (σ := σ) g U).toRepresentation).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  refine Representation.Equiv.mk (LinearEquiv.refl _ _) ?_
  intro a
  ext u
  rfl

/-- Helper for Theorem 17-17.3-1: precomposing both actions by the same conjugation automorphism
preserves representation equivalences. -/
noncomputable def representationEquiv_comp_conjNormal_local_c17
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {H : Subgroup G} [H.Normal]
    {σ : Representation k H W₁} {τ : Representation k H W₂}
    (e : σ.Equiv τ) (g : G) :
    Representation.Equiv
      (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (τ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro a
  ext x
  exact LinearMap.congr_fun (e.isIntertwining' ((MulAut.conjNormal g⁻¹) a)) x

/-- Helper for Theorem 17-17.3-1: an owner-module linear equivalence between two
subrepresentations upgrades to a representation equivalence. -/
noncomputable def subrepresentation_equiv_of_asSubmoduleLinearEquiv_local_c17
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {ρ : Representation k A' V'}
    (U U' : Subrepresentation ρ)
    (e : U.asSubmodule ≃ₗ[MonoidAlgebra k A'] U'.asSubmodule) :
    Representation.Equiv U.toRepresentation U'.toRepresentation := by
  let eU := subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) U.asSubmodule
  let eU' := subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) U'.asSubmodule
  let eRep : U.toRepresentation.asModule ≃ₗ[MonoidAlgebra k A'] U'.toRepresentation.asModule :=
    (eU.trans e).trans eU'.symm
  let f : U.toRepresentation.IntertwiningMap U'.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule U.toRepresentation
      U'.toRepresentation).symm eRep.toLinearMap
  exact f.ofBijective eRep.bijective

/-- Helper for Theorem 17-17.3-1: restricting a representation equivalence to a subrepresentation
identifies it with the image subrepresentation under the induced order isomorphism. -/
noncomputable def subrepresentation_equiv_of_equiv_image_local_c17
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    {ρ : Representation k A' V'} {σ : Representation k A' W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Representation.Equiv U.toRepresentation
      ((subrepresentationOrderIso_local_c17 e U).toRepresentation) := by
  let eSub : U.toSubmodule ≃ₗ[k] (subrepresentationOrderIso_local_c17 e U).toSubmodule :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective U.toSubmodule
  refine Representation.Equiv.mk eSub ?_
  intro a
  ext u
  exact LinearMap.congr_fun (e.isIntertwining' a) u

/-- Helper for Theorem 17-17.3-1: transporting a `C`-isotypic component through `ρ g`
preserves isotypicity. -/
lemma transportedSubrepresentation_asSubmodule_isIsotypic_c17
    (ρ : Representation k G V)
    {H : Subgroup G} [H.Normal] :
    let ρH : Representation k H V := ρ.comp H.subtype
    letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra k H) V, ∀ g : G,
      IsIsotypic (MonoidAlgebra k H)
        ((transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule) := by
  intro ρH
  letI : Module (MonoidAlgebra k H) V := ρH.instModuleMonoidAlgebraAsModule
  intro c g
  letI : Module (MonoidAlgebra k H) ρH.asModule := ρH.instModuleMonoidAlgebraAsModule
  let W₀ : Subrepresentation ρH := Subrepresentation.ofSubmodule' c.1
  let T : Subrepresentation ρH := transportedSubrepresentation ρ W₀ g
  let ρW₀ : Representation k H W₀.toSubmodule := W₀.toRepresentation
  letI : Module (MonoidAlgebra k H) ρW₀.asModule := ρW₀.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k H) W₀.toRepresentation.asModule :=
    W₀.toRepresentation.instModuleMonoidAlgebraAsModule
  let ρT : Representation k H T.toSubmodule := T.toRepresentation
  letI : Module (MonoidAlgebra k H) ρT.asModule := ρT.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k H) T.toRepresentation.asModule :=
    T.toRepresentation.instModuleMonoidAlgebraAsModule
  have hW₀_owner : IsIsotypic (MonoidAlgebra k H) W₀.asSubmodule := by
    -- The chosen component is already one of the canonical `H`-isotypic blocks.
    simpa [W₀] using (IsIsotypic.isotypicComponents c.2)
  unfold IsIsotypic IsIsotypicOfType
  intro m hm m' hm'
  letI : IsSimpleModule (MonoidAlgebra k H) m := hm
  letI : IsSimpleModule (MonoidAlgebra k H) m' := hm'
  let mInt : Submodule (MonoidAlgebra k H) ρT.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρH) T).symm m
  let mInt' : Submodule (MonoidAlgebra k H) ρT.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local_c17 (ρ := ρH) T).symm m'
  have hmInt_simple : IsSimpleModule (MonoidAlgebra k H) mInt := by
    exact (isSimpleModule_owner_intrinsic_iff_local_c17 (ρ := ρH) T m).2 inferInstance
  have hmInt'_simple : IsSimpleModule (MonoidAlgebra k H) mInt' := by
    exact (isSimpleModule_owner_intrinsic_iff_local_c17 (ρ := ρH) T m').2 inferInstance
  let U : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt
  let U' : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt'
  have hU_irred : U.toRepresentation.IsIrreducible := by
    exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_local_c17 ρT mInt hmInt_simple
  have hU'_irred : U'.toRepresentation.IsIrreducible := by
    exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_local_c17 ρT mInt' hmInt'_simple
  let eT :
      Representation.Equiv
        (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
        ρT :=
    transportedSubrepresentation_rep_equiv_local_c17 ρ W₀ g
  let Ug : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
    subrepresentationOrderIso_local_c17 eT.symm U
  let Ug' : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
    subrepresentationOrderIso_local_c17 eT.symm U'
  have eUg : U.toRepresentation.Equiv Ug.toRepresentation := by
    simpa [Ug] using subrepresentation_equiv_of_equiv_image_local_c17 eT.symm U
  have eUg' : U'.toRepresentation.Equiv Ug'.toRepresentation := by
    simpa [Ug'] using subrepresentation_equiv_of_equiv_image_local_c17 eT.symm U'
  have hUg_irred : Ug.toRepresentation.IsIrreducible := by
    letI : U.toRepresentation.IsIrreducible := hU_irred
    exact isIrreducible_of_equiv_local_c17 eUg
  have hUg'_irred : Ug'.toRepresentation.IsIrreducible := by
    letI : U'.toRepresentation.IsIrreducible := hU'_irred
    exact isIrreducible_of_equiv_local_c17 eUg'
  let U₀ : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso_local_c17 (σ := ρW₀) g Ug
  let U₀' : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso_local_c17 (σ := ρW₀) g Ug'
  have eU₀ :
      Ug.toRepresentation.Equiv
        (U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    simpa [U₀] using conjugatedSubrepresentation_rep_equiv_local_c17 (σ := ρW₀) g Ug
  have eU₀' :
      Ug'.toRepresentation.Equiv
        (U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    simpa [U₀'] using conjugatedSubrepresentation_rep_equiv_local_c17 (σ := ρW₀) g Ug'
  have hU₀_irred : U₀.toRepresentation.IsIrreducible := by
    letI : Ug.toRepresentation.IsIrreducible := hUg_irred
    let ρU₀conj : Representation k H U₀.toSubmodule :=
      U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
    have hU₀_conj_irred : ρU₀conj.IsIrreducible := isIrreducible_of_equiv_local_c17 eU₀
    exact unconj_isIrreducible_local_c17 U₀.toRepresentation g hU₀_conj_irred
  have hU₀'_irred : U₀'.toRepresentation.IsIrreducible := by
    letI : Ug'.toRepresentation.IsIrreducible := hUg'_irred
    let ρU₀'conj : Representation k H U₀'.toSubmodule :=
      U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
    have hU₀'_conj_irred : ρU₀'conj.IsIrreducible := isIrreducible_of_equiv_local_c17 eU₀'
    exact unconj_isIrreducible_local_c17 U₀'.toRepresentation g hU₀'_conj_irred
  let ρU₀ : Representation k H U₀.toSubmodule := U₀.toRepresentation
  letI : Module (MonoidAlgebra k H) ρU₀.asModule := ρU₀.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k H) U₀.toRepresentation.asModule :=
    U₀.toRepresentation.instModuleMonoidAlgebraAsModule
  let ρU₀' : Representation k H U₀'.toSubmodule := U₀'.toRepresentation
  letI : Module (MonoidAlgebra k H) ρU₀'.asModule := ρU₀'.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k H) U₀'.toRepresentation.asModule :=
    U₀'.toRepresentation.instModuleMonoidAlgebraAsModule
  have hU₀_simple : IsSimpleModule (MonoidAlgebra k H) U₀.asSubmodule := by
    exact
      @IsSimpleModule.congr (MonoidAlgebra k H) inferInstance U₀.asSubmodule
        U₀.asSubmodule.addCommGroup U₀.asSubmodule.module
        ρU₀.asModule ρU₀.instAddCommGroupAsModule ρU₀.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρW₀) U₀).symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀).mp hU₀_irred)
  have hU₀'_simple : IsSimpleModule (MonoidAlgebra k H) U₀'.asSubmodule := by
    exact
      @IsSimpleModule.congr (MonoidAlgebra k H) inferInstance U₀'.asSubmodule
        U₀'.asSubmodule.addCommGroup U₀'.asSubmodule.module
        ρU₀'.asModule ρU₀'.instAddCommGroupAsModule ρU₀'.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρW₀) U₀').symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀').mp hU₀'_irred)
  letI : IsSimpleModule (MonoidAlgebra k H) U₀.asSubmodule := hU₀_simple
  letI : IsSimpleModule (MonoidAlgebra k H) U₀'.asSubmodule := hU₀'_simple
  have hU₀_equiv :
      Nonempty (U₀'.asSubmodule ≃ₗ[MonoidAlgebra k H] U₀.asSubmodule) := by
    exact
      pulled_back_constituents_equiv_in_isotypic_block_local_c17
        (ρ := ρH) W₀ hW₀_owner U₀'.asSubmodule U₀.asSubmodule
  let e₀ : Representation.Equiv U₀'.toRepresentation U₀.toRepresentation :=
    subrepresentation_equiv_of_asSubmoduleLinearEquiv_local_c17 U₀' U₀ hU₀_equiv.some
  let eTransport : U'.toRepresentation.Equiv U.toRepresentation :=
    (((eUg'.trans eU₀').trans (representationEquiv_comp_conjNormal_local_c17 e₀ g)).trans
      eU₀.symm).trans eUg.symm
  let eInt : mInt' ≃ₗ[MonoidAlgebra k H] mInt :=
    ((subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρT) U').symm.trans
      (representationEquiv_asModuleLinearEquiv_local_c17 eTransport)).trans
      (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρT) U)
  let eOwner : m' ≃ₗ[MonoidAlgebra k H] m :=
    ((subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17 (ρ := ρH) T m').symm.trans
      eInt).trans
      (subrepresentation_owner_intrinsic_submodule_linearEquiv_local_c17 (ρ := ρH) T m)
  -- Transport simple constituents back to the original block, compare them there, then return.
  simpa using ⟨eOwner⟩

/-- Helper for Theorem 17-17.3-1: transporting a `C`-isotypic component by `ρ g` produces another
`C`-isotypic component. -/
lemma transported_isotypic_component_mem_c17
    (hC : C.Normal)
    (ρ : Representation k G V)
    (hsemi :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k C) V) :
    let ρC : Representation k C V := ρ.comp C.subtype
    letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra k C) V, ∀ g : G,
      (transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule ∈
        isotypicComponents (MonoidAlgebra k C) V := by
  letI : C.Normal := hC
  let ρC : Representation k C V := ρ.comp C.subtype
  letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k C) V := hsemi
  intro ρC
  letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k C) V := hsemi
  intro c g
  let T : Submodule (MonoidAlgebra k C) V :=
    (transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule
  have hc_full :
      (Subrepresentation.ofSubmodule' c.1).asSubmodule.IsFullyInvariant := by
    simpa using (Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2)
  change T ∈ isotypicComponents (MonoidAlgebra k C) V
  rw [mem_isotypicComponents_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Transport preserves isotypicity of the chosen `C`-block.
    exact transportedSubrepresentation_asSubmodule_isIsotypic_c17 ρ c g
  · -- Full invariance is stable under conjugating the restricted action.
    exact
      transportedSubrepresentation_asSubmodule_isFullyInvariant_c17 ρ
        (Subrepresentation.ofSubmodule' c.1) g hc_full
  · -- Nontriviality survives because `ρ g` is an automorphism.
    exact
      transportedSubrepresentation_asSubmodule_ne_bot ρ
        (Subrepresentation.ofSubmodule' c.1) g
        (bot_lt_isotypicComponents c.2).ne'

/-- Helper for Theorem 17-17.3-1: in the prime-characteristic case, semisimplicity of the
restriction to `C` gives Serre's dichotomy between induction from a proper overgroup containing
`C` and `C`-isotypy of the restriction. -/
lemma exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restrict
    (hC : C.Normal)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hsemi :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k C) V) :
    (∃ H : Subgroup G,
      C ≤ H ∧ H < ⊤ ∧
        ∃ W : Subrepresentation (ρ.comp H.subtype),
          W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
      (let ρC : Representation k C V := ρ.comp C.subtype
       letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra k C) V) := by
  classical
  letI : C.Normal := hC
  let ρC : Representation k C V := ρ.comp C.subtype
  letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k C) V := hsemi
  letI : Finite C := by infer_instance
  -- Split first by the number of `C`-isotypic components of the restricted module.
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra k C) V)
  · -- A unique isotypic component must be all of `V`.
    right
    simpa [ρC] using
      isIsotypic_of_subsingleton_componentFamily
        (R := MonoidAlgebra k C) (M := V) hsub
  · let I := isotypicComponents (MonoidAlgebra k C) V
    let W : I → Submodule k V := fun c ↦ (Subrepresentation.ofSubmodule' c.1).toSubmodule
    letI : MulAction G I :=
      { smul := fun g c ↦
          ⟨(transportedSubrepresentation ρ (Subrepresentation.ofSubmodule' c.1) g).asSubmodule,
            transported_isotypic_component_mem_c17 hC ρ hsemi c g⟩
        one_smul := by
          intro c
          apply Subtype.ext
          ext v
          constructor
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
            simpa using hw
          · intro hv
            refine Submodule.mem_map.mpr ⟨v, hv, ?_⟩
            simpa using (LinearMap.congr_fun ρ.map_one v).symm
        mul_smul := by
          intro g h c
          apply Subtype.ext
          ext v
          constructor
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
            refine Submodule.mem_map.mpr ⟨ρ h w, ?_, ?_⟩
            · exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
            · simpa [LinearMap.comp_apply] using hwv
          · intro hv
            rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
            rcases Submodule.mem_map.mp hw with ⟨u, hu, rfl⟩
            refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
            simpa [LinearMap.comp_apply] using hwv }
    have hperm : ρ.PermutesSubmoduleFamily W := by
      -- By construction, the `G`-action on the component family is transport by `ρ g`.
      intro g c
      rfl
    have hcomponents :
        iSupIndep W ∧ (⨆ c : I, W c) = ⊤ :=
      by
        exact
          iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_c17 (ρH := ρC)
            (s := isotypicComponents (MonoidAlgebra k C) V)
            (hs_indep := sSupIndep_isotypicComponents (MonoidAlgebra k C) V)
            (hs_top := sSup_isotypicComponents (MonoidAlgebra k C) V)
    have hindep : iSupIndep W := hcomponents.1
    have hspan : (⨆ c : I, W c) = ⊤ := hcomponents.2
    have hne : ∀ c : I, W c ≠ ⊥ := fun c ↦ by
      intro hbot
      apply (bot_lt_isotypicComponents c.2).ne'
      ext x
      change x ∈ c.1 ↔ x ∈ (⊥ : Submodule (MonoidAlgebra k C) V)
      simpa [W] using congrArg (fun S : Submodule k V ↦ x ∈ S) hbot
    letI : MulAction.IsPretransitive G I :=
      Representation.IsIrreducible.isPretransitive_of_permuted_internalSummands
        ρ W hindep hperm hne
    letI : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨c₀, c₁, hc_ne⟩ := exists_pair_ne I
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c₀ c₁
    let H : Subgroup G := ρ.submoduleStabilizer (W c₀)
    have hC_le_H : C ≤ H := by
      -- Elements of `C` already preserve every `C`-stable component.
      simpa [H, W] using
        stabilizer_contains_C_of_restricted_subrepresentation
          (ρ := ρ) (W := Subrepresentation.ofSubmodule' c₀.1)
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hg_mem : g ∈ H := by simpa [H, htop]
      have hW_eq : W c₁ = W c₀ := by
        calc
          W c₁ = W (g • c₀) := by simpa [hg]
          _ = (W c₀).map (ρ g) := (hperm g c₀).symm
          _ = W c₀ := (mem_submoduleStabilizer_iff_map_eq ρ (W c₀)).mp hg_mem
      have hc_eq : c₀.1 = c₁.1 := by
        ext x
        change x ∈ c₀.1 ↔ x ∈ c₁.1
        simpa [W] using congrArg (fun S : Submodule k V ↦ x ∈ S) hW_eq.symm
      exact hc_ne (Subtype.ext hc_eq)
    have hH_lt : H < ⊤ := lt_top_iff_ne_top.mpr hH_ne_top
    have hIndW :
        ρ.IsInducedFromSubrepresentation H (ρ.stabilizedSubrepresentation (W c₀)) := by
      -- Remark `7-7.1-4` upgrades the transitive component family to an induced decomposition.
      simpa [H, W] using
        Representation.IsIrreducible.isInducedFromStabilizer_of_permuted_internalSummands
          ρ W c₀ hindep hspan hperm hne
    let ρH : Representation k H V := ρ.comp H.subtype
    have hW₀_ne :
        (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to :
          (ρ.stabilizedSubrepresentation (W c₀)).toSubmodule = ⊥ := by
        ext v
        change v ∈ (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ↔
            v ∈ (⊥ : Submodule (MonoidAlgebra k H) ρH.asModule)
        rw [hbot]
      exact hne c₀ <| by simpa [H, W] using hbot_to
    obtain ⟨U, hU_le, hU_ne, hU_irred⟩ :=
      exists_irreducible_subrepresentation_le_of_nonzero
        ρH (ρ.stabilizedSubrepresentation (W c₀)) hW₀_ne
    have hIndU : ρ.IsInducedFromSubrepresentation H U :=
      isInducedFromSubrepresentation_of_nonzero_le ρ hU_le hU_ne hIndW
    -- The non-isotypic branch produces a proper stabilizer overgroup and an irreducible inducing
    -- constituent inside the stabilized summand.
    left
    exact ⟨H, hC_le_H, hH_lt, U, hU_irred, hIndU⟩

end

end Representation
