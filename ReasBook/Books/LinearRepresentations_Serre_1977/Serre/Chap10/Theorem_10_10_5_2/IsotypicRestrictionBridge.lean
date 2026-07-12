import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.MonomialCharacter
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2.SubrepresentationTransport

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_isotypic_bridge_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_isotypic_bridge_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H
theorem isIrreducible_of_equiv_local
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Equivalent representations have isomorphic lattices of invariant subspaces.
  exact (subrepresentationOrderIso_local e).isSimpleOrder_iff.mp inferInstance

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: every element of a
subgroup stabilizes any subrepresentation of the restricted action to that subgroup. -/
theorem stabilizer_contains_subgroup_of_restricted_subrepresentation_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (A : Subgroup Q)
    (W : Subrepresentation (ρ.comp A.subtype)) :
    A ≤ ρ.submoduleStabilizer W.toSubmodule := by
  intro x hx
  rw [mem_submoduleStabilizer_iff_map_eq]
  -- The restricted `A`-action already preserves the chosen `A`-stable summand.
  refine le_antisymm ?_ ?_
  · intro v hv
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact W.apply_mem_toSubmodule ⟨x, hx⟩ hw
  · intro v hv
    refine Submodule.mem_map.mpr ⟨ρ x⁻¹ v, ?_, ?_⟩
    · exact W.apply_mem_toSubmodule ⟨x⁻¹, A.inv_mem hx⟩ hv
    · simpa [Module.End.mul_apply] using
        (LinearMap.congr_fun (ρ.map_mul x x⁻¹) v).symm

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the owner
`ℂ[H]`-action on the intrinsic module of `Subrepresentation.ofSubmodule' N` is the original
owner action on `N`. -/
theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule)
    (r : MonoidAlgebra ℂ A') (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the two owner actions after forgetting to the ambient subtype carrier.
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      rfl
  | add a b ha hb =>
      rw [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, Submodule.coe_add, ha, hb]
      rfl
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the intrinsic owner
module of `Subrepresentation.ofSubmodule' N` is canonically the original owner submodule `N`. -/
noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[MonoidAlgebra ℂ A'] N := by
  let ρN : Representation ℂ A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
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
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply_local ρ N r (ρN.asModuleEquiv x) }

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the intrinsic owner
module of a bundled subrepresentation is canonically the owner submodule it defines. -/
noncomputable def subrepresentation_owner_intrinsic_linearEquiv_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ) :
    W.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule := by
  -- Rewrite `W` as `Subrepresentation.ofSubmodule' W.asSubmodule` and reuse the canonical bridge.
  simpa using subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) W.asSubmodule

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a simple owner
submodule yields an irreducible bundled subrepresentation. -/
theorem isIrreducible_of_ownerSimple_subrepresentation_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra ℂ A') N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation ℂ A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  -- Transport simplicity across the canonical owner-module equivalence for `ofSubmodule'`.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra ℂ A') inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) N) hN)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the owner and
intrinsic views of the submodule lattice of a subrepresentation are canonically order-isomorphic. -/
noncomputable def subrepresentation_owner_intrinsic_submodule_orderIso_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ) :
    Submodule (MonoidAlgebra ℂ A') W.toRepresentation.asModule ≃o
      Submodule (MonoidAlgebra ℂ A') W.asSubmodule := by
  let ρW : Representation ℂ A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  -- The canonical linear equivalence on carriers transports submodules in both directions.
  exact Submodule.orderIsoMapComap (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρ) W)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the intrinsic
counterpart of an owner submodule is linearly equivalent to the original owner submodule. -/
noncomputable def subrepresentation_owner_intrinsic_submodule_linearEquiv_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra ℂ A') W.asSubmodule) :
    ((subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρ) W).symm m) ≃ₗ[MonoidAlgebra ℂ A'] m := by
  let ρW : Representation ℂ A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  let e : ρW.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule :=
    subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρ) W
  let mInt : Submodule (MonoidAlgebra ℂ A') ρW.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρ) W).symm m
  -- The intrinsic submodule is the `comap` of `m` along `e`, so `e` restricts directly.
  refine
    { toFun := fun x => ⟨e x, x.property⟩
      invFun := fun y => ⟨e.symm y, by
        simpa [mInt, subrepresentation_owner_intrinsic_submodule_orderIso_local, e] using y.property⟩
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

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: simplicity is
preserved when moving a submodule between the owner and intrinsic views of one subrepresentation. -/
theorem isSimpleModule_owner_intrinsic_iff_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra ℂ A') W.asSubmodule) :
    IsSimpleModule (MonoidAlgebra ℂ A')
        ((subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρ) W).symm m) ↔
      IsSimpleModule (MonoidAlgebra ℂ A') m := by
  -- Transport simplicity along the canonical owner/intrinsic linear equivalence.
  simpa using
    (subrepresentation_owner_intrinsic_submodule_linearEquiv_local (ρ := ρ) W m).isSimpleModule_iff

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: simple intrinsic
constituents of an isotypic block become equivalent after comparison in the owner view. -/
theorem pulled_back_constituents_equiv_in_isotypic_block_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W₀ : Subrepresentation ρ)
    (hW₀ : IsIsotypic (MonoidAlgebra ℂ A') W₀.asSubmodule)
    (m m' : Submodule (MonoidAlgebra ℂ A') W₀.toRepresentation.asModule)
    [IsSimpleModule (MonoidAlgebra ℂ A') m]
    [IsSimpleModule (MonoidAlgebra ℂ A') m'] :
    Nonempty (m ≃ₗ[MonoidAlgebra ℂ A'] m') := by
  let eW₀ := subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρ) W₀
  let mOwner : Submodule (MonoidAlgebra ℂ A') W₀.asSubmodule := eW₀ m
  let mOwner' : Submodule (MonoidAlgebra ℂ A') W₀.asSubmodule := eW₀ m'
  have hm_eq : eW₀.symm mOwner = m := by
    simpa [mOwner] using eW₀.symm_apply_apply m
  have hm'_eq : eW₀.symm mOwner' = m' := by
    simpa [mOwner'] using eW₀.symm_apply_apply m'
  have hmOwner_simple : IsSimpleModule (MonoidAlgebra ℂ A') mOwner := by
    -- Move the first intrinsic simple constituent into the owner lattice of `W₀`.
    letI : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner) := hm_eq ▸ inferInstance
    have hm_simple : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner) := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff_local (ρ := ρ) W₀ mOwner).mp hm_simple
  have hmOwner'_simple : IsSimpleModule (MonoidAlgebra ℂ A') mOwner' := by
    -- The same owner/intrinsic bridge applies to the second constituent.
    letI : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner') := hm'_eq ▸ inferInstance
    have hm'_simple : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner') := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff_local (ρ := ρ) W₀ mOwner').mp hm'_simple
  unfold IsIsotypic IsIsotypicOfType at hW₀
  letI : IsSimpleModule (MonoidAlgebra ℂ A') mOwner := hmOwner_simple
  letI : IsSimpleModule (MonoidAlgebra ℂ A') mOwner' := hmOwner'_simple
  have hInt :
      Nonempty ((eW₀.symm mOwner) ≃ₗ[MonoidAlgebra ℂ A'] (eW₀.symm mOwner')) := by
    rcases hW₀ mOwner mOwner' with ⟨eOwner⟩
    exact
      ⟨((subrepresentation_owner_intrinsic_submodule_linearEquiv_local
          (ρ := ρ) W₀ mOwner).trans eOwner.symm).trans
          (subrepresentation_owner_intrinsic_submodule_linearEquiv_local
            (ρ := ρ) W₀ mOwner').symm⟩
  rcases hInt with ⟨eInt⟩
  exact ⟨hm_eq ▸ hm'_eq ▸ eInt⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a representation
equivalence induces a `ℂ[A]`-linear equivalence on owner modules. -/
noncomputable def representationEquiv_asModuleLinearEquiv_local
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra ℂ A'] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun :=
        (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
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

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: untwisting a
conjugated irreducible representation recovers irreducibility of the original action. -/
theorem unconj_isIrreducible_local
    {Q : Type} [Group Q]
    (A : Subgroup Q) [A.Normal]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ A W') (g : Q)
    (hσg :
      let σg : Representation ℂ A W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      σg.IsIrreducible) :
    σ.IsIrreducible := by
  let σg : Representation ℂ A W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
  letI : σg.IsIrreducible := hσg
  -- The conjugation order isomorphism preserves simplicity of the subrepresentation lattice.
  exact (conjugatedSubrepresentationOrderIso_local A σ g).isSimpleOrder_iff.mp inferInstance

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a conjugated
subrepresentation is the same carrier equipped with the untwisted action. -/
noncomputable def conjugatedSubrepresentation_rep_equiv_local
    {Q : Type} [Group Q]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup Q) [A.Normal]
    (σ : Representation ℂ A W') (g : Q)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    Representation.Equiv U.toRepresentation
      (((conjugatedSubrepresentationOrderIso_local A σ g U).toRepresentation).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  -- Conjugation changes only the action formula; the subtype carrier stays fixed.
  refine Representation.Equiv.mk (LinearEquiv.refl _ _) ?_
  intro a
  ext u
  rfl

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an intertwining
equivalence remains intertwining after precomposing both actions by the same conjugation. -/
noncomputable def representationEquiv_comp_conjNormal_local
    {Q : Type} [Group Q]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (A : Subgroup Q) [A.Normal]
    {σ : Representation ℂ A W₁} {τ : Representation ℂ A W₂}
    (e : σ.Equiv τ) (g : Q) :
    Representation.Equiv
      (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (τ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  -- Precomposing both actions by the same automorphism leaves the intertwining relation
  -- unchanged.
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro a
  ext x
  exact LinearMap.congr_fun (e.isIntertwining' ((MulAut.conjNormal g⁻¹) a)) x

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an owner-module
linear equivalence between subrepresentations upgrades to a representation equivalence. -/
noncomputable def subrepresentation_equiv_of_asSubmoduleLinearEquiv_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ A' V'}
    (U W : Subrepresentation ρ)
    (e : U.asSubmodule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule) :
    Representation.Equiv U.toRepresentation W.toRepresentation := by
  let eU := subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) U.asSubmodule
  let eW := subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) W.asSubmodule
  let eRep : U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.toRepresentation.asModule :=
    (eU.trans e).trans eW.symm
  -- Convert the owner-linear map into an intertwiner and package bijectivity as an equivalence.
  let f : U.toRepresentation.IntertwiningMap W.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule U.toRepresentation
      W.toRepresentation).symm eRep.toLinearMap
  exact f.ofBijective eRep.bijective

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: restricting a
representation equivalence to a subrepresentation identifies it with the image subrepresentation. -/
noncomputable def subrepresentation_equiv_of_equiv_image_local
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Representation.Equiv U.toRepresentation
      ((subrepresentationOrderIso_local e U).toRepresentation) := by
  let eSub : U.toSubmodule ≃ₗ[ℂ] (subrepresentationOrderIso_local e U).toSubmodule :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective U.toSubmodule
  -- Restrict the ambient intertwiner to the chosen invariant subspace and its image.
  refine Representation.Equiv.mk eSub ?_
  intro a
  ext u
  exact LinearMap.congr_fun (e.isIntertwining' a) u

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting an
`A`-isotypic component through `ρ g` preserves isotypicity. -/
theorem transportedSubrepresentation_asSubmodule_isIsotypic_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal] [Finite A]
    [NeZero (Nat.card A : ℂ)] :
    let ρA : Representation ℂ A V := ρ.comp A.subtype
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra ℂ A) V, ∀ g : Q,
      IsIsotypic (MonoidAlgebra ℂ A)
        ((transportedSubrepresentation_local ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule) := by
  intro ρA
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra ℂ A) ρA.asModule := ρA.instModuleMonoidAlgebraAsModule
  intro c g
  let W₀ : Subrepresentation ρA := Subrepresentation.ofSubmodule' c.1
  let T : Subrepresentation ρA := transportedSubrepresentation_local ρ A W₀ g
  let ρW₀ : Representation ℂ A W₀.toSubmodule := W₀.toRepresentation
  letI : Module (MonoidAlgebra ℂ A) ρW₀.asModule := ρW₀.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra ℂ A) W₀.toRepresentation.asModule :=
    W₀.toRepresentation.instModuleMonoidAlgebraAsModule
  let ρT : Representation ℂ A T.toSubmodule := T.toRepresentation
  letI : Module (MonoidAlgebra ℂ A) ρT.asModule := ρT.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra ℂ A) T.toRepresentation.asModule :=
    T.toRepresentation.instModuleMonoidAlgebraAsModule
  have hW₀_owner : IsIsotypic (MonoidAlgebra ℂ A) W₀.asSubmodule := by
    -- The selected summand is one of the canonical isotypic components.
    simpa [W₀] using (IsIsotypic.isotypicComponents c.2)
  unfold IsIsotypic IsIsotypicOfType
  intro m hm m' hm'
  letI : IsSimpleModule (MonoidAlgebra ℂ A) m := hm
  letI : IsSimpleModule (MonoidAlgebra ℂ A) m' := hm'
  let mInt : Submodule (MonoidAlgebra ℂ A) ρT.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρA) T).symm m
  let mInt' : Submodule (MonoidAlgebra ℂ A) ρT.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso_local (ρ := ρA) T).symm m'
  have hmInt_simple : IsSimpleModule (MonoidAlgebra ℂ A) mInt := by
    -- Move the first simple owner constituent into the intrinsic module of `T`.
    exact (isSimpleModule_owner_intrinsic_iff_local (ρ := ρA) T m).2 inferInstance
  have hmInt'_simple : IsSimpleModule (MonoidAlgebra ℂ A) mInt' := by
    -- The same bridge transports the second simple owner constituent.
    exact (isSimpleModule_owner_intrinsic_iff_local (ρ := ρA) T m').2 inferInstance
  let U : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt
  let U' : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt'
  have hU_irred : U.toRepresentation.IsIrreducible := by
    -- Simple intrinsic submodules of `T` are irreducible bundled subrepresentations.
    exact
      isIrreducible_of_ownerSimple_subrepresentation_local ρT mInt hmInt_simple
  have hU'_irred : U'.toRepresentation.IsIrreducible := by
    exact
      isIrreducible_of_ownerSimple_subrepresentation_local ρT mInt'
        hmInt'_simple
  let eT :
      Representation.Equiv
        (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
        ρT :=
    transportedSubrepresentation_rep_equiv_local ρ A W₀ g
  let Ug : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
    subrepresentationOrderIso_local eT.symm U
  let Ug' : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
    subrepresentationOrderIso_local eT.symm U'
  have eUg : U.toRepresentation.Equiv Ug.toRepresentation := by
    -- Pull the first intrinsic constituent back through the transport equivalence.
    simpa [Ug] using subrepresentation_equiv_of_equiv_image_local eT.symm U
  have eUg' : U'.toRepresentation.Equiv Ug'.toRepresentation := by
    simpa [Ug'] using subrepresentation_equiv_of_equiv_image_local eT.symm U'
  have hUg_irred : Ug.toRepresentation.IsIrreducible := by
    letI : U.toRepresentation.IsIrreducible := hU_irred
    exact isIrreducible_of_equiv_local eUg
  have hUg'_irred : Ug'.toRepresentation.IsIrreducible := by
    letI : U'.toRepresentation.IsIrreducible := hU'_irred
    exact isIrreducible_of_equiv_local eUg'
  let U₀ : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso_local A ρW₀ g Ug
  let U₀' : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso_local A ρW₀ g Ug'
  have eU₀ :
      Ug.toRepresentation.Equiv
        (U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    -- Untwisting the first pulled-back constituent only changes the action formula.
    simpa [U₀] using conjugatedSubrepresentation_rep_equiv_local A ρW₀ g Ug
  have eU₀' :
      Ug'.toRepresentation.Equiv
        (U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    simpa [U₀'] using conjugatedSubrepresentation_rep_equiv_local A ρW₀ g Ug'
  have hU₀_irred : U₀.toRepresentation.IsIrreducible := by
    letI : Ug.toRepresentation.IsIrreducible := hUg_irred
    let ρU₀conj : Representation ℂ A U₀.toSubmodule :=
      U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
    have hU₀_conj_irred : ρU₀conj.IsIrreducible := isIrreducible_of_equiv_local eU₀
    -- Removing the conjugated action recovers an irreducible constituent of the original block.
    exact unconj_isIrreducible_local A U₀.toRepresentation g hU₀_conj_irred
  have hU₀'_irred : U₀'.toRepresentation.IsIrreducible := by
    letI : Ug'.toRepresentation.IsIrreducible := hUg'_irred
    let ρU₀'conj : Representation ℂ A U₀'.toSubmodule :=
      U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
    have hU₀'_conj_irred : ρU₀'conj.IsIrreducible := isIrreducible_of_equiv_local eU₀'
    exact unconj_isIrreducible_local A U₀'.toRepresentation g hU₀'_conj_irred
  let ρU₀ : Representation ℂ A U₀.toSubmodule := U₀.toRepresentation
  letI : Module (MonoidAlgebra ℂ A) ρU₀.asModule := ρU₀.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra ℂ A) U₀.toRepresentation.asModule :=
    U₀.toRepresentation.instModuleMonoidAlgebraAsModule
  let ρU₀' : Representation ℂ A U₀'.toSubmodule := U₀'.toRepresentation
  letI : Module (MonoidAlgebra ℂ A) ρU₀'.asModule := ρU₀'.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra ℂ A) U₀'.toRepresentation.asModule :=
    U₀'.toRepresentation.instModuleMonoidAlgebraAsModule
  have hU₀_simple : IsSimpleModule (MonoidAlgebra ℂ A) U₀.asSubmodule := by
    -- Convert irreducibility of the pulled-back constituent into owner-module simplicity.
    exact
      @IsSimpleModule.congr (MonoidAlgebra ℂ A) inferInstance U₀.asSubmodule
        U₀.asSubmodule.addCommGroup U₀.asSubmodule.module
        ρU₀.asModule ρU₀.instAddCommGroupAsModule ρU₀.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρW₀) U₀).symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀).mp hU₀_irred)
  have hU₀'_simple : IsSimpleModule (MonoidAlgebra ℂ A) U₀'.asSubmodule := by
    exact
      @IsSimpleModule.congr (MonoidAlgebra ℂ A) inferInstance U₀'.asSubmodule
        U₀'.asSubmodule.addCommGroup U₀'.asSubmodule.module
        ρU₀'.asModule ρU₀'.instAddCommGroupAsModule ρU₀'.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρW₀) U₀').symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀').mp hU₀'_irred)
  letI : IsSimpleModule (MonoidAlgebra ℂ A) U₀.asSubmodule := hU₀_simple
  letI : IsSimpleModule (MonoidAlgebra ℂ A) U₀'.asSubmodule := hU₀'_simple
  have hU₀_equiv :
      Nonempty (U₀'.asSubmodule ≃ₗ[MonoidAlgebra ℂ A] U₀.asSubmodule) := by
    -- Compare the pulled-back simple constituents inside the original isotypic block `W₀`.
    exact
      pulled_back_constituents_equiv_in_isotypic_block_local
        (ρ := ρA) W₀ hW₀_owner U₀'.asSubmodule U₀.asSubmodule
  let e₀ : Representation.Equiv U₀'.toRepresentation U₀.toRepresentation :=
    subrepresentation_equiv_of_asSubmoduleLinearEquiv_local U₀' U₀ hU₀_equiv.some
  let eTransport : U'.toRepresentation.Equiv U.toRepresentation :=
    (((eUg'.trans eU₀').trans (representationEquiv_comp_conjNormal_local A e₀ g)).trans
      eU₀.symm).trans eUg.symm
  let eInt : mInt' ≃ₗ[MonoidAlgebra ℂ A] mInt :=
    ((subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρT) U').symm.trans
      (representationEquiv_asModuleLinearEquiv_local eTransport)).trans
      (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρT) U)
  let eOwner : m' ≃ₗ[MonoidAlgebra ℂ A] m :=
    ((subrepresentation_owner_intrinsic_submodule_linearEquiv_local (ρ := ρA) T m').symm.trans
      eInt).trans
      (subrepresentation_owner_intrinsic_submodule_linearEquiv_local (ρ := ρA) T m)
  -- Transport both simple constituents to the original block, compare them there, then return.
  simpa using ⟨eOwner⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a transported
`A`-isotypic component is again an `A`-isotypic component. -/
theorem transported_isotypic_component_mem_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal] [Finite A]
    [NeZero (Nat.card A : ℂ)] :
    let ρA : Representation ℂ A V := ρ.comp A.subtype
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra ℂ A) V, ∀ g : Q,
      (transportedSubrepresentation_local ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule ∈
        isotypicComponents (MonoidAlgebra ℂ A) V := by
  intro ρA
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  intro c g
  let T : Submodule (MonoidAlgebra ℂ A) V :=
    (transportedSubrepresentation_local ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule
  have hc_full :
      (Subrepresentation.ofSubmodule' c.1).asSubmodule.IsFullyInvariant := by
    simpa using (Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2)
  change T ∈ isotypicComponents (MonoidAlgebra ℂ A) V
  rw [mem_isotypicComponents_iff]
  exact
    ⟨transportedSubrepresentation_asSubmodule_isIsotypic_local ρ A c g,
      transportedSubrepresentation_asSubmodule_isFullyInvariant_local ρ A
        (Subrepresentation.ofSubmodule' c.1) g hc_full,
      transportedSubrepresentation_asSubmodule_ne_bot_local ρ A
        (Subrepresentation.ofSubmodule' c.1) g
        (bot_lt_isotypicComponents c.2).ne'⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a simple owner
submodule yields an irreducible bundled subrepresentation. -/
theorem isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra ℂ A') N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation ℂ A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  -- Transport simplicity across the canonical owner-module equivalence for `ofSubmodule'`.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra ℂ A') inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) N) hN)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: every nonzero
`H`-stable subrepresentation contains an irreducible `H`-subrepresentation. -/
theorem exists_irreducible_subrepresentation_le_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {H : Subgroup Q} [Finite H]
    (ρH : Representation ℂ H V) (U : Subrepresentation ρH)
    (hU : U.asSubmodule ≠ ⊥) :
    ∃ W : Subrepresentation ρH,
      W.toSubmodule ≤ U.toSubmodule ∧
        W.toSubmodule ≠ ⊥ ∧
          W.toRepresentation.IsIrreducible := by
  letI : NeZero (Nat.card H : ℂ) := by
    exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : Module (MonoidAlgebra ℂ H) V := ρH.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra ℂ H) V := by infer_instance
  -- Pick a simple owner submodule inside the given nonzero `H`-stable carrier.
  obtain ⟨N, hNle, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra ℂ H) (M := V) U.asSubmodule).resolve_left hU
  let W : Subrepresentation ρH := Subrepresentation.ofSubmodule' N
  refine ⟨W, ?_, ?_, ?_⟩
  · simpa [W] using hNle
  · -- Forgetting from the owner module to the ambient `ℂ`-space preserves nontriviality.
    intro hW
    have hN_ne_bot : N ≠ ⊥ := by
      letI : IsSimpleModule (MonoidAlgebra ℂ H) N := hNsimple
      exact Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) N)
    apply hN_ne_bot
    ext v
    have hW' : (Subrepresentation.ofSubmodule' N).toSubmodule = (⊥ : Submodule ℂ V) := by
      simpa [W] using hW
    simpa using congrArg (fun S : Submodule ℂ V ↦ v ∈ S) hW'
  · -- Owner-module simplicity upgrades to irreducibility of the bundled subrepresentation.
    exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_local ρH N hNsimple

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the supremum of the
quotient-indexed translates of a subrepresentation is stable under the ambient action. -/
theorem leftQuotientSubmodule_iSup_stable_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    {H : Subgroup Q}
    (U : Subrepresentation (ρ.comp H.subtype))
    (s : Q) :
    (⨆ q : Q ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
      ⨆ q : Q ⧸ H, ρ.leftQuotientSubmodule H U q := by
  -- Route correction: send each quotient summand to the shifted coset `(s • q)` and then take
  -- the supremum, rather than trying to prove span stability abstractly.
  calc
    (⨆ q : Q ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) =
        ⨆ q : Q ⧸ H, (ρ.leftQuotientSubmodule H U q).map (ρ s) := by
          rw [Submodule.map_iSup]
    _ ≤ ⨆ q : Q ⧸ H, ρ.leftQuotientSubmodule H U q := by
          refine iSup_le fun q ↦ ?_
          have hq :
              (ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
                ρ.leftQuotientSubmodule H U (s • q) := by
            refine Quotient.inductionOn' q ?_
            intro g
            change Submodule.map (ρ s) (Submodule.map (ρ g) U.toSubmodule) ≤
              ρ.leftQuotientSubmodule H U (((s * g : Q) : Q ⧸ H))
            rw [ρ.leftQuotientSubmodule_mk H U (s * g)]
            intro x hx
            rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
            exact Submodule.mem_map.mpr ⟨u, hu, by
              simpa [Module.End.mul_apply] using
                (LinearMap.congr_fun (ρ.map_mul s g) u).symm⟩
          exact hq.trans (le_iSup (fun q : Q ⧸ H ↦ ρ.leftQuotientSubmodule H U q) (s • q))

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: once `ρ` is induced
from an `H`-stable summand, irreducibility lets one shrink the inducing summand to any nonzero
`H`-subrepresentation. -/
theorem isInducedFromSubrepresentation_of_nonzero_le_local
    {Q : Type} [Group Q] [Finite Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) [ρ.IsIrreducible]
    {H : Subgroup Q} [Finite H]
    {U W : Subrepresentation (ρ.comp H.subtype)}
    (hUW : U.toSubmodule ≤ W.toSubmodule)
    (hUne : U.asSubmodule ≠ ⊥)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ρ.IsInducedFromSubrepresentation H U := by
  classical
  let _ : DecidableEq (Q ⧸ H) := Classical.decEq _
  let ℳW : Q ⧸ H → Submodule ℂ V := ρ.leftQuotientSubmodule H W
  let ℳU : Q ⧸ H → Submodule ℂ V := ρ.leftQuotientSubmodule H U
  have hInternalW : DirectSum.IsInternal ℳW := by
    -- Unpack the Chapter 3 owner carried by the inducing witness for `W`.
    simpa [ℳW, Representation.IsInducedFromSubrepresentation] using hInd
  have hfamily_le : ℳU ≤ ℳW := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    simpa [ℳU, ℳW, ρ.leftQuotientSubmodule_mk H U g, ρ.leftQuotientSubmodule_mk H W g] using
      (Submodule.map_mono hUW)
  have hIndepU : iSupIndep ℳU := by
    -- Independence descends because every `U`-translate lies in the corresponding `W`-translate.
    exact hInternalW.submodule_iSupIndep.mono hfamily_le
  let S : Submodule ℂ V := ⨆ q : Q ⧸ H, ℳU q
  let Sρ : Subrepresentation ρ :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro s x hx
        have hxmap : ρ s x ∈ S.map (ρ s) := by
          exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        exact leftQuotientSubmodule_iSup_stable_local ρ U s hxmap }
  have hU_to_ne : U.toSubmodule ≠ ⊥ := by
    let ρH : Representation ℂ H V := ρ.comp H.subtype
    intro hbot
    have hbot_as : U.asSubmodule = ⊥ := by
      ext v
      change ((v : V) ∈ U.toSubmodule) ↔ v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
      rw [hbot]
      change v = 0 ↔ v = 0
      rfl
    exact hUne hbot_as
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    apply hU_to_ne
    have hU_le_S : U.toSubmodule ≤ S := by
      intro x hx
      have hxq : x ∈ ρ.leftQuotientSubmodule H U ((1 : Q) : Q ⧸ H) := by
        rw [ρ.leftQuotientSubmodule_mk H U (1 : Q)]
        exact Submodule.mem_map.mpr ⟨x, hx, by simpa using (LinearMap.congr_fun ρ.map_one x).symm⟩
      exact (show ρ.leftQuotientSubmodule H U ((1 : Q) : Q ⧸ H) ≤ S by
        simpa [S, ℳU] using
          (le_iSup (fun q : Q ⧸ H ↦ ρ.leftQuotientSubmodule H U q) ((1 : Q) : Q ⧸ H))) hxq
    exact le_bot_iff.mp (hSbot ▸ hU_le_S)
  have hSρ_ne_bot : Sρ ≠ ⊥ := by
    intro hbot
    apply hS_ne_bot
    simpa [Sρ] using congrArg Subrepresentation.toSubmodule hbot
  have hSρ_top : Sρ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Sρ).resolve_left hSρ_ne_bot
  have hspanU : iSup ℳU = ⊤ := by
    -- Irreducibility forces the nonzero stable span of the `U`-translates to fill the space.
    simpa [S, Sρ] using congrArg Subrepresentation.toSubmodule hSρ_top
  -- Package the descended independence and top-span statements back into the Chapter 3 owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndepU hspanU

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: if the restricted
semisimple module has only one isotypic component, then the whole restricted module is isotypic. -/
theorem isIsotypic_of_subsingleton_isotypicComponents_local
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M]
    (hsub : Subsingleton (isotypicComponents R M)) :
    IsIsotypic R M := by
  classical
  by_cases hne : Nonempty (isotypicComponents R M)
  · rcases hne with ⟨⟨c, hc⟩⟩
    -- A singleton family of isotypic components has supremum equal to its unique member.
    have hsSup_le : sSup (isotypicComponents R M) ≤ c := by
      exact sSup_le fun m hm ↦ by
        have hm_eq : m = c := by
          exact congrArg Subtype.val (hsub.elim ⟨m, hm⟩ ⟨c, hc⟩)
        exact hm_eq ▸ le_rfl
    have htop_le : (⊤ : Submodule R M) ≤ c := by
      simpa [sSup_isotypicComponents R M] using hsSup_le
    have hc_top : c = ⊤ := top_unique htop_le
    -- Once the unique isotypic component is all of `M`, its isotypy is exactly the target claim.
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
    -- The zero module is automatically isotypic.
    exact IsIsotypic.of_subsingleton R M

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: converting a
set-indexed family of owner submodules into the corresponding subtype-indexed family of bundled
subrepresentations preserves independence and spanning after forgetting to `ℂ`. -/
theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_local
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (s : Set (Submodule (MonoidAlgebra ℂ A') ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `ℂ[A']` to `ℂ`; this keeps both independence and the top supremum.
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars ℂ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule (MonoidAlgebra ℂ A') ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := ℂ) (hst := hi))
  have hs_top' : (⨆ i : s, (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars ℂ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars ℂ) hs_top'
  -- `Subrepresentation.ofSubmodule'` is definitionally the restricted-scalar carrier.
  simpa using ⟨hσ_indep, hσ_top⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the local
Proposition `8-8.1-1` dichotomy for a normal subgroup splits an irreducible representation into
the induced-from-a-proper-overgroup branch or the isotypic-restriction branch. -/
theorem exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_local
    {Q : Type} [Group Q] [Finite Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) [ρ.IsIrreducible]
    (A : Subgroup Q) [A.Normal] :
    (∃ H : Subgroup Q,
      A ≤ H ∧ H < ⊤ ∧
        ∃ W : Subrepresentation (ρ.comp H.subtype),
          W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
      (let ρA : Representation ℂ A V := ρ.comp A.subtype
       letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra ℂ A) V) := by
  classical
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  letI : Finite A := by infer_instance
  letI : NeZero (Nat.card A : ℂ) := by
    exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : IsSemisimpleModule (MonoidAlgebra ℂ A) V := by infer_instance
  -- Split first by Serre's dichotomy on the number of isotypic summands for the restricted
  -- `A`-module.
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra ℂ A) V)
  · -- A unique isotypic component must be the whole restricted module, giving branch (b).
    right
    simpa [ρA] using
      isIsotypic_of_subsingleton_isotypicComponents_local
        (R := MonoidAlgebra ℂ A) (M := V) hsub
  · let I := isotypicComponents (MonoidAlgebra ℂ A) V
    let W : I → Submodule ℂ V := fun c ↦ (Subrepresentation.ofSubmodule' c.1).toSubmodule
    letI : MulAction Q I := {
      smul := fun g c ↦
        ⟨(transportedSubrepresentation_local ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule,
          transported_isotypic_component_mem_local ρ A c g⟩
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
          simpa [LinearMap.comp_apply] using hwv
      }
    -- Transport by `ρ g` is definitionally the permutation relation needed by Remark `7-7.1-4`.
    have hperm : ρ.PermutesSubmoduleFamily W := by
      intro g c
      rfl
    have hcomponents :
        iSupIndep W ∧ (⨆ c : I, W c) = ⊤ :=
      iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family_local (ρ := ρA)
        (s := isotypicComponents (MonoidAlgebra ℂ A) V)
        (hs_indep := sSupIndep_isotypicComponents (MonoidAlgebra ℂ A) V)
        (hs_top := sSup_isotypicComponents (MonoidAlgebra ℂ A) V)
    have hindep : iSupIndep W := hcomponents.1
    have hspan : (⨆ c : I, W c) = ⊤ := hcomponents.2
    have hne : ∀ c : I, W c ≠ ⊥ := fun c ↦ by
      intro hbot
      apply (bot_lt_isotypicComponents c.2).ne'
      ext x
      change x ∈ c.1 ↔ x ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) V)
      simpa [W] using congrArg (fun S : Submodule ℂ V ↦ x ∈ S) hbot
    letI : MulAction.IsPretransitive Q I :=
      Representation.IsIrreducible.isPretransitive_of_permuted_internalSummands
        ρ W hindep hperm hne
    letI : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨c₀, c₁, hc_ne⟩ := exists_pair_ne I
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q c₀ c₁
    let H : Subgroup Q := ρ.submoduleStabilizer (W c₀)
    have hA_le_H : A ≤ H := by
      -- Each `A`-element stabilizes every isotypic summand.
      simpa [H, W] using
        stabilizer_contains_subgroup_of_restricted_subrepresentation_local
          ρ A (Subrepresentation.ofSubmodule' c₀.1)
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hg_mem : g ∈ H := by
        simpa [H, htop]
      have hW_eq : W c₁ = W c₀ := by
        calc
          W c₁ = W (g • c₀) := by simpa [hg]
          _ = (W c₀).map (ρ g) := (hperm g c₀).symm
          _ = W c₀ := (mem_submoduleStabilizer_iff_map_eq ρ (W c₀)).mp hg_mem
      have hc_eq : c₀.1 = c₁.1 := by
        ext x
        change x ∈ c₀.1 ↔ x ∈ c₁.1
        simpa [W] using congrArg (fun S : Submodule ℂ V ↦ x ∈ S) hW_eq.symm
      exact hc_ne (Subtype.ext hc_eq)
    have hH_lt : H < ⊤ := lt_top_iff_ne_top.mpr hH_ne_top
    have hIndW :
        ρ.IsInducedFromSubrepresentation H (ρ.stabilizedSubrepresentation (W c₀)) := by
      -- Remark `7-7.1-4` turns the permuted internal decomposition into an induced witness.
      simpa [H, W] using
        Representation.IsIrreducible.isInducedFromStabilizer_of_permuted_internalSummands
          ρ W c₀ hindep hspan hperm hne
    let ρH : Representation ℂ H V := ρ.comp H.subtype
    have hW₀_ne : (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to : (ρ.stabilizedSubrepresentation (W c₀)).toSubmodule = ⊥ := by
        ext v
        change v ∈ (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ↔
            v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
        rw [hbot]
      exact hne c₀ <| by simpa [H, W] using hbot_to
    obtain ⟨U, hU_le, hU_ne, hU_irred⟩ :=
      exists_irreducible_subrepresentation_le_local
        ρH (ρ.stabilizedSubrepresentation (W c₀)) hW₀_ne
    have hU_as_ne : U.asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to : U.toSubmodule = ⊥ := by
        ext v
        change v ∈ U.asSubmodule ↔ v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
        rw [hbot]
      exact hU_ne hbot_to
    have hIndU : ρ.IsInducedFromSubrepresentation H U :=
      isInducedFromSubrepresentation_of_nonzero_le_local ρ hU_le hU_as_ne hIndW
    -- Choose an irreducible constituent of the stabilized isotypic summand and descend the
    -- induced witness to it.
    left
    exact ⟨H, hA_le_H, hH_lt, U, hU_irred, hIndU⟩

end

end Representation
