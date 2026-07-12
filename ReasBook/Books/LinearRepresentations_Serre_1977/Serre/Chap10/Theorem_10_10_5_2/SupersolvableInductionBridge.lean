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
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2.QuotientMonomialReduction
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2.IsotypicRestrictionBridge

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_supersolvable_bridge_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_supersolvable_bridge_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H
/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: for a module viewed
through `Representation.ofModule'`, the associated group-algebra operator is the original
`ℂ[A]`-scalar action. -/
theorem ofModule'_asAlgebraHom_apply_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    (M : Type) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ A) M]
    (r : MonoidAlgebra ℂ A) (m : M) :
    ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : MonoidAlgebra ℂ A =>
      ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro a
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro r s hr hs
    simp [hr, hs, add_smul]
  · intro c s hs
    simp [hs]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the owner module of
`Representation.ofModule'` is canonically the original `ℂ[A]`-module. -/
noncomputable def ofModule'_asModuleLinearEquiv_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    (M : Type) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ A) M] :
    (Representation.ofModule' (k := ℂ) (G := A) M).asModule ≃ₗ[MonoidAlgebra ℂ A] M := by
  refine
    { toFun := fun x => (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv x
      invFun := fun x => (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv.symm x
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
          (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv (r • x)
              = ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom r)
                  ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv x) := by
                    simpa using
                      (Representation.asModuleEquiv_map_smul
                        (ρ := Representation.ofModule' (k := ℂ) (G := A) M) r x)
          _ = r • (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv x := by
                simp [ofModule'_asAlgebraHom_apply_local] }

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an equivalence
between `Representation.ofModule' M` and `τ` yields the corresponding owner-level
`ℂ[A]`-linear equivalence. -/
theorem nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {W' : Type} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ A W')
    {M : Type} [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ A) M]
    (hMτ : Nonempty ((Representation.ofModule' (k := ℂ) (G := A) M).Equiv τ)) :
    Nonempty (M ≃ₗ[MonoidAlgebra ℂ A] τ.asModule) := by
  rcases hMτ with ⟨e⟩
  let f : (Representation.ofModule' (k := ℂ) (G := A) M).asModule →ₗ[MonoidAlgebra ℂ A] τ.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule' (k := ℂ) (G := A) M) (σ := τ)) e.toIntertwiningMap
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact e.injective hxy
    · intro w
      refine ⟨(ofModule'_asModuleLinearEquiv_local A M).symm (e.symm (τ.asModuleEquiv w)), ?_⟩
      change (e ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv
        ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv.symm
          (e.symm (τ.asModuleEquiv w)))) : W') =
        (τ.asModuleEquiv w : W')
      simp
  exact ⟨(ofModule'_asModuleLinearEquiv_local A M).symm.trans (LinearEquiv.ofBijective f hf_bij)⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a simple owner
submodule gives an irreducible restricted representation. -/
theorem ofModule'_isIrreducible_of_isSimpleModule_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    (Representation.ofModule' (k := ℂ) (G := A) m).IsIrreducible := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  letI : Module (MonoidAlgebra ℂ A) ρm.asModule := ρm.instModuleMonoidAlgebraAsModule
  have hm : IsSimpleModule (MonoidAlgebra ℂ A) m := inferInstance
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρm).mpr
      (@IsSimpleModule.congr (MonoidAlgebra ℂ A) inferInstance ρm.asModule
        ρm.instAddCommGroupAsModule ρm.instModuleMonoidAlgebraAsModule
        m m.addCommGroup m.module
        (ofModule'_asModuleLinearEquiv_local A m) hm)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: every simple owner
summand of the restricted `ℂ[A]`-module is one-dimensional over `ℂ`. -/
theorem simple_owner_submodule_finrank_eq_one_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    [Finite A] [IsMulCommutative A]
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    Module.finrank ℂ m = 1 := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  letI : ρm.IsIrreducible := ofModule'_isIrreducible_of_isSimpleModule_local A m
  letI : FiniteDimensional ℂ m := Representation.IsIrreducible.finiteDimensional_of_finite ρm
  simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρm

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a simple owner
summand of the restricted `ℂ[A]`-module comes from a degree-`1` character of `A`. -/
theorem character_of_simple_owner_submodule_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    [Finite A] [IsMulCommutative A]
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    ∃ χ : A →* ℂˣ, ∀ a : A,
      (Representation.ofModule' (k := ℂ) (G := A) m) a = (χ a : ℂ) • 1 := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  have hdim : Module.finrank ℂ m = 1 :=
    simple_owner_submodule_finrank_eq_one_local A m
  let scalarEquiv : ℂ ≃ₗ[ℂ] (m →ₗ[ℂ] m) := LinearEquiv.smul_id_of_finrank_eq_one hdim
  let α₀ : A → ℂ := fun a ↦ scalarEquiv.symm (ρm a)
  have hα₀_eq (a : A) : ρm a = α₀ a • LinearMap.id := by
    exact (scalarEquiv.apply_symm_apply (ρm a)).symm
  have hα₀_one : α₀ 1 = 1 := by
    apply scalarEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    ext x
    simp [scalarEquiv]
  have hα₀_mul (a b : A) : α₀ (a * b) = α₀ a * α₀ b := by
    apply scalarEquiv.injective
    rw [LinearEquiv.apply_symm_apply, map_mul, hα₀_eq, hα₀_eq]
    ext x
    simp [scalarEquiv, smul_smul, mul_comm]
  have hα₀_ne_zero (a : A) : α₀ a ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ m := by
      omega
    letI : Nontrivial m := Module.nontrivial_of_finrank_pos hpos
    intro ha0
    have hzero : ρm a = 0 := by
      simp [hα₀_eq, ha0]
    have hone : (1 : m →ₗ[ℂ] m) ≠ 0 := one_ne_zero
    have hidzero : (1 : m →ₗ[ℂ] m) = 0 := by
      calc
        (1 : m →ₗ[ℂ] m) = ρm a * ρm a⁻¹ := by
          simpa using (ρm.map_mul a a⁻¹)
        _ = 0 := by
          rw [hzero]
          simp
    exact hone hidzero
  let χ : A →* ℂˣ :=
    { toFun := fun a ↦ Units.mk0 (α₀ a) (hα₀_ne_zero a)
      map_one' := by
        ext
        exact hα₀_one
      map_mul' a b := by
        ext
        exact hα₀_mul a b }
  refine ⟨χ, ?_⟩
  intro a
  -- The constituent action is the scalar prescribed by the extracted character.
  simpa [χ] using hα₀_eq a

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a one-dimensional
representation acting by the scalars prescribed by `χ` is equivalent to `χ.toRepresentation`. -/
theorem equiv_character_representation_of_finrank_one_scalar_action_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ A W) (χ : A →* ℂˣ)
    (hW : Module.finrank ℂ W = 1)
    (hτ : ∀ a : A, τ a = (χ a : ℂ) • 1) :
    Nonempty (τ.Equiv χ.toRepresentation) := by
  let e : W ≃ₗ[ℂ] ℂ := (Module.nonempty_linearEquiv_of_finrank_eq_one hW).some.symm
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro a
  ext w
  have hw := LinearMap.congr_fun (hτ a) w
  simpa [MonoidHom.toRepresentation, LinearMap.lsmul_apply] using congrArg e hw

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: if every owner action
of `MonoidAlgebra.single a 1` is the scalar `χ a`, then every simple owner summand is owner-linearly
equivalent to the module of `χ.toRepresentation`. -/
theorem simple_owner_submodule_equiv_character_module_of_scalar_action_local
    {Q : Type} [Group Q] (A : Subgroup Q)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    [Finite A] [IsMulCommutative A]
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (χ : A →* ℂˣ)
    (hχ : ∀ a : A, ∀ v : V,
      ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v = (χ a : ℂ) • v)
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    Nonempty (m ≃ₗ[MonoidAlgebra ℂ A] χ.toRepresentation.asModule) := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  have hdim : Module.finrank ℂ m = 1 :=
    simple_owner_submodule_finrank_eq_one_local A m
  have hρm (a : A) : ρm a = (χ a : ℂ) • 1 := by
    -- Restrict the global scalar-action hypothesis from `V` to the simple owner summand.
    ext x
    simpa using hχ a (x : V)
  have hRep :
      Nonempty (ρm.Equiv χ.toRepresentation) :=
    equiv_character_representation_of_finrank_one_scalar_action_local
      (A := A) (τ := ρm) (χ := χ) (hW := hdim) (hτ := hρm)
  simpa using
    nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'_local
      (A := A) (τ := χ.toRepresentation) hRep

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: for a commutative
subgroup, isotypy of the restricted action is equivalent to scalar action by a single linear
character. -/
theorem restriction_isotypic_iff_exists_character_of_commutative_subgroup_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [Finite A] [IsMulCommutative A] :
    (let ρA : Representation ℂ A V := ρ.comp A.subtype
     letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
     IsIsotypic (MonoidAlgebra ℂ A) V) ↔
    ∃ χ : A →* ℂˣ, ∀ a : A, ρ a = (χ a : ℂ) • 1 := by
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ A) V := by
    simpa using ρA.instIsScalarTowerMonoidAlgebraAsModule
  have hcard : 0 < Nat.card A := Nat.card_pos
  let _ : NeZero (Nat.card A : ℂ) := ⟨Nat.cast_ne_zero.mpr hcard.ne'⟩
  letI : IsSemisimpleModule (MonoidAlgebra ℂ A) V := by infer_instance
  change IsIsotypic (MonoidAlgebra ℂ A) V ↔
    ∃ χ : A →* ℂˣ, ∀ a : A, ρ a = (χ a : ℂ) • 1
  constructor
  · intro hIso
    by_cases hV : Subsingleton V
    · letI : Subsingleton V := hV
      refine ⟨1, ?_⟩
      intro a
      ext v
      exact Subsingleton.elim _ _
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨ι, -, S, hSsimple, ⟨e⟩⟩ := hIso.linearEquiv_finsupp
      letI : IsSimpleModule (MonoidAlgebra ℂ A) S := hSsimple
      obtain ⟨χ, hSχ⟩ := character_of_simple_owner_submodule_local A S
      have hSscalar (a : A) (s : S) :
          (MonoidAlgebra.single a (1 : ℂ)) • s = (χ a : ℂ) • s := by
        simpa using LinearMap.congr_fun (hSχ a) s
      have hFinsuppScalar (a : A) (f : ι →₀ S) :
          (MonoidAlgebra.single a (1 : ℂ)) • f = (χ a : ℂ) • f := by
        ext i
        exact congrArg Subtype.val (hSscalar a (f i))
      refine ⟨χ, ?_⟩
      intro a
      ext v
      change ((ρ.comp A.subtype) a) v = (χ a : ℂ) • v
      have hsingle :
          ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v =
            ((ρ.comp A.subtype) a) v := by
        change (ρA.asAlgebraHom (MonoidAlgebra.single a (1 : ℂ))) v = ((ρ.comp A.subtype) a) v
        simp [ρA]
      have howner :
          ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v = (χ a : ℂ) • v := by
        apply e.injective
        calc
          e (((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v)
              = ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • e v := by
                  simpa using
                    e.map_smulₛₗ ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) v
          _ = (χ a : ℂ) • e v := by
                simpa using hFinsuppScalar a (e v)
          _ = e ((χ a : ℂ) • v) := by
                exact ((e.restrictScalars ℂ).map_smul (χ a : ℂ) v).symm
      exact hsingle.symm.trans howner
  · rintro ⟨χ, hχ⟩
    have hχmodule (a : A) (v : V) :
        ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v = (χ a : ℂ) • v := by
      have hsingle :
          ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v =
            ((ρ.comp A.subtype) a) v := by
        change (ρA.asAlgebraHom (MonoidAlgebra.single a (1 : ℂ))) v = ((ρ.comp A.subtype) a) v
        simp [ρA]
      exact hsingle.trans <| by
        simpa using LinearMap.congr_fun (hχ a) v
    intro m _
    intro m' _
    exact
      ⟨(simple_owner_submodule_equiv_character_module_of_scalar_action_local
          A χ hχmodule m').some.trans
        (simple_owner_submodule_equiv_character_module_of_scalar_action_local
          A χ hχmodule m).some.symm⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: if the restriction to
a normal commutative subgroup were isotypic, then faithfulness would force that subgroup into the
center. -/
theorem not_restriction_isotypic_of_faithful_of_not_le_center_local
    {Q : Type} [Group Q] [Finite Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) [ρ.IsIrreducible]
    (A : Subgroup Q) [A.Normal] [IsMulCommutative A]
    (hfaithful : Function.Injective ρ)
    (hA : ¬ A ≤ Subgroup.center Q) :
    ¬ (let ρA : Representation ℂ A V := ρ.comp A.subtype
       letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra ℂ A) V) := by
  intro hisotypic
  obtain ⟨χ, hχ⟩ :=
    (restriction_isotypic_iff_exists_character_of_commutative_subgroup_local
      (ρ := ρ) (A := A)).mp hisotypic
  apply hA
  intro a ha
  let aA : A := ⟨a, ha⟩
  rw [Subgroup.mem_center_iff]
  intro g
  -- Scalar action on `a` forces the operators for `g * a` and `a * g` to agree.
  apply hfaithful
  calc
    ρ (g * a) = ρ g * ρ aA := by
      simpa [aA] using ρ.map_mul g (aA : A)
    _ = ρ g * ((χ aA : ℂ) • 1) := by
      rw [hχ aA]
    _ = ((χ aA : ℂ) • 1) * ρ g := by
      ext v
      simp
    _ = ρ aA * ρ g := by
      rw [hχ aA]
    _ = ρ (a * g) := by
      simpa [aA] using (ρ.map_mul (aA : A) g).symm

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a `K`-stable
subrepresentation inside the `H`-subrepresentation `W` can be viewed as a subrepresentation of the
ambient representation restricted to `K.map H.subtype`. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    Subrepresentation (ρ.comp (K.map H.subtype).subtype) where
  toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g x hx
    let e : K ≃* K.map H.subtype :=
      K.equivMapOfInjective H.subtype H.subtype_injective
    rcases hx with ⟨y, hy, rfl⟩
    -- Rewrite the ambient `K.map H.subtype`-action through the canonical preimage in `K`.
    refine ⟨W.toRepresentation (e.symm g) y, U.apply_mem_toSubmodule (e.symm g) hy, ?_⟩
    change (ρ (((e.symm g : K) : H) : Q) (y : W.toSubmodule) : V) = ρ (g : Q) (y : W.toSubmodule)
    have hg : (((e.symm g : K) : H) : Q) = (g : Q) := by
      simpa [e] using
        (Subgroup.coe_equivMapOfInjective_apply K H.subtype H.subtype_injective (e.symm g)).symm
    simpa [hg]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: passing from `U` to
its ambient image in `V` does not change the underlying complex dimension. -/
theorem ambient_subrepresentation_of_subgroup_chain_finrank_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    Module.finrank ℂ
        (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toSubmodule =
      Module.finrank ℂ U.toSubmodule := by
  -- The ambient witness is just the image of `U` under the injective inclusion `W ↪ V`.
  change Module.finrank ℂ (U.toSubmodule.map W.toSubmodule.subtype) =
      Module.finrank ℂ U.toSubmodule
  simpa using
    (Submodule.finrank_map_subtype_eq (p := W.toSubmodule) (q := U.toSubmodule) (R := ℂ))

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the ambient witness is
the image of `U` under the inclusion `W ↪ V`, viewed as a linear equivalence onto its image. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain_linearEquiv_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    U.toSubmodule ≃ₗ[ℂ] (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toSubmodule :=
  Submodule.equivMapOfInjective
    W.toSubmodule.subtype
    W.toSubmodule.subtype_injective
    U.toSubmodule

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the ambient-image
linear equivalence intertwines the original `K`-action with the transported `K.map H.subtype`
action. -/
theorem ambient_subrepresentation_of_subgroup_chain_linearEquiv_isIntertwining_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    ∀ k,
      (ambient_subrepresentation_of_subgroup_chain_linearEquiv_local ρ H W K U).toLinearMap ∘ₗ
          U.toRepresentation k =
        (((ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation.comp
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom) k) ∘ₗ
          (ambient_subrepresentation_of_subgroup_chain_linearEquiv_local ρ H W K U).toLinearMap := by
  intro k
  -- The subgroup-chain witness was defined so that the ambient `K.map H.subtype`-action is
  -- literally the transported `K`-action through the inclusion `W ↪ V`.
  ext u
  rfl

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the ambient
subgroup-chain witness realizes the original `K`-representation after transport along
`K ≃ K.map H.subtype`. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain_rep_equiv_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    U.toRepresentation.Equiv
      ((ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation.comp
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom) :=
  Representation.Equiv.mk
    (ambient_subrepresentation_of_subgroup_chain_linearEquiv_local ρ H W K U)
    (ambient_subrepresentation_of_subgroup_chain_linearEquiv_isIntertwining_local ρ H W K U)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the mapped subgroup
inclusion composed with `K ≃ K.map H.subtype` is the original composite inclusion `K ≤ H ≤ Q`. -/
theorem subgroup_chain_map_subtype_comp_eq_local
    {Q : Type} [Group Q]
    (H : Subgroup Q)
    (K : Subgroup H) :
    (K.map H.subtype).subtype.comp
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom =
      H.subtype.comp K.subtype := by
  ext k
  -- Both compositions send `k` to the same ambient group element.
  simpa using
    (Subgroup.coe_equivMapOfInjective_apply K H.subtype H.subtype_injective k)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: induction along a
source equivalence only transports the source factor of the induced model. -/
noncomputable def ind_equiv_of_source_equiv_local
    {K L : Type} [Group K] [Group L]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : K →* L) {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) :
    (Representation.ind f ρ).Equiv (Representation.ind f σ) := by
  let inducedSourceHom :
      (Representation.ind f ρ).IntertwiningMap (Representation.ind f σ) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        intro g
        ext h a
        simp }
  let inducedSourceInv :
      (Representation.ind f σ).IntertwiningMap (Representation.ind f ρ) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg
              (fun z ↦ (Finsupp.single (f g * x) (1 : ℂ)) ⊗ₜ[ℂ] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedSourceInv.toLinearMap ∘ₗ inducedSourceHom.toLinearMap = LinearMap.id := by
    -- The two induced maps act by `e` and `e.symm` on each standard generator.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  have hinduced_hom_inv :
      inducedSourceHom.toLinearMap ∘ₗ inducedSourceInv.toLinearMap = LinearMap.id := by
    -- The same generator computation yields the inverse identity in the other order.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  -- Package the two inverse induced maps into the desired equivalence.
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedSourceHom.toLinearMap inducedSourceInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedSourceHom.isIntertwining'

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: reindexing the source
group by an equivalence leaves the induction coinvariant relations unchanged. -/
theorem ind_ker_comp_equiv_eq_local
    {K L M : Type} [Group K] [Group L] [Group M]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : K ≃* L) (f : L →* M) (ρ : Representation ℂ L W) :
    Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
          (ρ.comp e.toMonoidHom)) =
      Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ M).comp f) ρ) := by
  -- Reindexing the source group only renames the same family of induction relations.
  unfold Representation.Coinvariants.ker
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e g, v), rfl⟩
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e.symm g, v), by simp⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: reindexing the source
group along an equivalence does not change the induced representation. -/
noncomputable def ind_equiv_of_comp_equiv_local
    {K L M : Type} [Group K] [Group L] [Group M]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : K ≃* L) (f : L →* M) (ρ : Representation ℂ L W) :
    (Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).Equiv
      (Representation.ind f ρ) := by
  refine Representation.Equiv.mk
      (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq_local e f ρ)) ?_
  intro m
  -- The quotient equivalence is literally the identity on induced generators.
  apply Representation.IndV.hom_ext
  intro m'
  ext v
  simp only [LinearMap.comp_apply]
  change (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq_local e f ρ))
      (((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) m)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v)) =
    ((Representation.ind f ρ) m)
      ((Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq_local e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v))
  have hleft :
      ((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) m)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v) =
      (Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (m' * m⁻¹)) v := by
    exact Representation.ind_mk (φ := f.comp e.toMonoidHom) (ρ := ρ.comp e.toMonoidHom) m m' v
  have hright :
      ((Representation.ind f ρ) m)
        ((Representation.IndV.mk f ρ m') v) =
      (Representation.IndV.mk f ρ (m' * m⁻¹)) v := by
    exact Representation.ind_mk (φ := f) (ρ := ρ) m m' v
  have hsource :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp f) ρ))
          (ind_ker_comp_equiv_eq_local e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v) =
      (Representation.IndV.mk f ρ m') v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq_local e f ρ) _
  have hsource' :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp f) ρ))
          (ind_ker_comp_equiv_eq_local e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (m' * m⁻¹)) v) =
      (Representation.IndV.mk f ρ (m' * m⁻¹)) v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq_local e f ρ) _
  rw [hleft, hsource', hsource, hright]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: induction in stages
for a subgroup chain is equivalent to induction from the composite inclusion. -/
noncomputable def ind_subgroup_chain_equiv_local
    {K : Type} [Group K]
    (S : Subgroup K) (L : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ L W) :
    ((Rep.ind S.subtype (Rep.ind L.subtype (Rep.of ρ))).ρ).Equiv
      ((Rep.ind (S.subtype.comp L.subtype) (Rep.of ρ)).ρ) := by
  exact Representation.equivOfIso
    ((((indResAdjunction ℂ L.subtype).leftAdjointCompIso
          (indResAdjunction ℂ S.subtype)
          (indResAdjunction ℂ (S.subtype.comp L.subtype))
          (eqToIso rfl)).app (Rep.of ρ)))

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting the
subgroup-chain source from `K` to `K.map H.subtype` identifies the two induced models. -/
noncomputable def ind_subgroup_chain_map_equiv_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
      ((Rep.ind (K.map H.subtype).subtype
        (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ) := by
  let eK : K ≃* K.map H.subtype :=
    K.equivMapOfInjective H.subtype H.subtype_injective
  let eU :
      U.toRepresentation.Equiv
        ((ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation.comp
          eK.toMonoidHom) :=
    ambient_subrepresentation_of_subgroup_chain_rep_equiv_local ρ H W K U
  let e₁ :
      ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
        ((Rep.ind (H.subtype.comp K.subtype)
          (Rep.of
            ((ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation.comp
              eK.toMonoidHom))).ρ) :=
    ind_equiv_of_source_equiv_local (H.subtype.comp K.subtype) eU
  let e₂ :
      ((Rep.ind ((K.map H.subtype).subtype.comp eK.toMonoidHom)
        (Rep.of
          ((ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation.comp
            eK.toMonoidHom))).ρ).Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ) :=
    by
      simpa using
        (ind_equiv_of_comp_equiv_local eK
          (K.map H.subtype).subtype
          (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)
  -- After reindexing the source, the mapped-subgroup model is the same induction.
  exact e₁.trans (by
    simpa [subgroup_chain_map_subtype_comp_eq_local H K] using e₂)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the inverse of the
induced source equivalence acts by the inverse source equivalence on standard generators. -/
theorem ind_equiv_of_source_equiv_symm_mk_local
    {K L : Type} [Group K] [Group L]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : K →* L) {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (g : L) (x : W') :
    (ind_equiv_of_source_equiv_local f e).symm (Representation.IndV.mk f σ g x) =
      Representation.IndV.mk f ρ g (e.symm x) := by
  -- The inverse induced equivalence simply applies `e.symm` to the source vector.
  simp [ind_equiv_of_source_equiv_local]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the inverse of the
standard induced-model equivalence evaluates the unit-coset generator back to the source vector. -/
@[simp] theorem equiv_induced_of_isInducedFromSubrepresentation_symm_mk_one_local
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (u : U.toSubmodule) :
    (equiv_induced_of_isInducedFromSubrepresentation_local ρ S U hU).symm
        (Representation.IndV.mk S.subtype U.toRepresentation 1 u) =
      u := by
  -- The inverse map is the canonical induced-to-ambient morphism evaluated at the unit generator.
  change (inducedFromSubrepresentationHom_local ρ S U).hom
      (Representation.IndV.mk S.subtype U.toRepresentation 1 u) = u
  simpa using inducedFromSubrepresentationHom_mk_local ρ S U 1 u

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting a
restricted subrepresentation across an ambient equivalence preserves its carrier dimension. -/
theorem transported_subrepresentation_finrank_eq_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    Module.finrank ℂ
        (transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U).toSubmodule =
      Module.finrank ℂ U.toSubmodule := by
  have hUmap :
      (transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U).toSubmodule =
        U.toSubmodule.map (comp_subtype_equiv_local e S).toLinearMap := by
    simpa using transported_subrepresentation_of_equiv_toSubmodule_local
      (comp_subtype_equiv_local e S) U
  let eU :
      U.toSubmodule ≃ₗ[ℂ]
        U.toSubmodule.map (comp_subtype_equiv_local e S).toLinearMap :=
    Submodule.equivMapOfInjective
      (comp_subtype_equiv_local e S).toLinearMap
      (comp_subtype_equiv_local e S).injective
      U.toSubmodule
  -- The transported carrier is the image of `U` under the restricted linear equivalence.
  calc
    Module.finrank ℂ
        (transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U).toSubmodule =
          Module.finrank ℂ
            (U.toSubmodule.map (comp_subtype_equiv_local e S).toLinearMap) := by
          rw [hUmap]
    _ = Module.finrank ℂ U.toSubmodule := by
          exact eU.symm.finrank_eq

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: induction in stages
yields an ambient witness with the same carrier dimension as the downstairs monomial witness. -/
theorem exists_induced_subgroup_chain_witness_local
    {Q : Type} [Group Q] [Finite Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype))
    (hinduced : ρ.IsInducedFromSubrepresentation H W)
    (hUinduced : W.toRepresentation.IsInducedFromSubrepresentation K U) :
    ∃ U' : Subrepresentation (ρ.comp (K.map H.subtype).subtype),
      Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule ∧
        ρ.IsInducedFromSubrepresentation (K.map H.subtype) U' := by
  let eW :
      W.toRepresentation.Equiv
        ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation_local W.toRepresentation K U hUinduced
  let eρ :
      ρ.Equiv
        ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation_local ρ H W hinduced
  let eindW :
      ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ).Equiv
        ((Rep.ind H.subtype
          (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ) :=
    ind_equiv_of_source_equiv_local H.subtype eW
  let echain :
      ((Rep.ind H.subtype
        (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ).Equiv
        ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ) :=
    ind_subgroup_chain_equiv_local H K U.toRepresentation
  let emap :
      ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ) :=
    ind_subgroup_chain_map_equiv_local ρ H W K U
  let e :
      ρ.Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ) :=
    eρ.trans (eindW.trans (echain.trans emap))
  let Ustd :
      Subrepresentation
        ((((Rep.ind (K.map H.subtype).subtype
            (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ).comp
            (K.map H.subtype).subtype)) :=
    induced_identity_copy_subrepresentation_local
      (K.map H.subtype)
      (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation
  have hstd :
      ((Rep.ind (K.map H.subtype).subtype
        (Rep.of (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation)).ρ).IsInducedFromSubrepresentation
          (K.map H.subtype) Ustd := by
    -- The standard mapped-subgroup model is induced from its unit-coset copy.
    simpa [Ustd] using
      induced_identity_copy_is_induced_local
        (K.map H.subtype)
        (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation
  let Uambient : Subrepresentation (ρ.comp (K.map H.subtype).subtype) :=
    transported_subrepresentation_of_equiv_local
      (comp_subtype_equiv_local e.symm (K.map H.subtype)) Ustd
  have hUstd_dim :
      Module.finrank ℂ Ustd.toSubmodule = Module.finrank ℂ U.toSubmodule := by
    -- Compare the standard unit-coset copy with the concrete ambient image of `U`.
    calc
      Module.finrank ℂ Ustd.toSubmodule =
          Module.finrank ℂ
            (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toSubmodule := by
              let ecopy :
                  Ustd.toRepresentation.Equiv
                    (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation :=
                (induced_identity_copy_equiv_local
                  (K.map H.subtype)
                  (ambient_subrepresentation_of_subgroup_chain_local ρ H W K U).toRepresentation).symm
              exact
                ecopy.toLinearEquiv.finrank_eq
      _ = Module.finrank ℂ U.toSubmodule := by
            simpa using ambient_subrepresentation_of_subgroup_chain_finrank_local ρ H W K U
  have hUambient_dim :
      Module.finrank ℂ Uambient.toSubmodule = Module.finrank ℂ U.toSubmodule := by
    -- Transport along the restricted ambient equivalence preserves the witness dimension.
    calc
      Module.finrank ℂ Uambient.toSubmodule = Module.finrank ℂ Ustd.toSubmodule := by
        simpa [Uambient] using
          transported_subrepresentation_finrank_eq_local e.symm (K.map H.subtype) Ustd
      _ = Module.finrank ℂ U.toSubmodule := hUstd_dim
  have hUambient_induced :
      ρ.IsInducedFromSubrepresentation (K.map H.subtype) Uambient := by
    -- The inducing decomposition transports back across the ambient equivalence `e.symm`.
    simpa [Uambient] using
      isInducedFromSubrepresentation_of_equiv_local e.symm (K.map H.subtype) Ustd hstd
  exact ⟨Uambient, hUambient_dim, hUambient_induced⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: induction in stages
should convert a monomial witness for an irreducible `H`-subrepresentation into a monomial
witness for the ambient representation. -/
theorem isMonomial_of_induced_from_monomial_subrepresentation_local
    {Q : Type} [Group Q] [Finite Q]
    [IsSupersolvable Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V)
    (H : Subgroup Q)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hinduced : ρ.IsInducedFromSubrepresentation H W)
    (hmonomial : W.toRepresentation.IsMonomial) :
    ρ.IsMonomial := by
  rcases hmonomial with ⟨K, U, hUdim, hUinduced⟩
  rcases
      exists_induced_subgroup_chain_witness_local ρ H W K U hinduced hUinduced with
    ⟨U', hU'dim, hU'induced⟩
  -- The subgroup-chain transport keeps the one-dimensional witness and produces the ambient
  -- induced decomposition required for monomiality.
  refine ⟨K.map H.subtype, U', ?_, hU'induced⟩
  calc
    Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule := hU'dim
    _ = 1 := hUdim

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an irreducible
finite-dimensional complex representation of a finite supersolvable group is monomial. -/
theorem isMonomial_of_irreducible_of_supersolvable_aux_local
    {Q : Type} [Group Q] [Finite Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) [ρ.IsIrreducible] [IsSupersolvable Q] :
    ρ.IsMonomial := by
  classical
  by_cases hfaithful : Function.Injective ρ
  · by_cases hcomm : IsMulCommutative Q
    · letI : IsMulCommutative Q := hcomm
      letI : FiniteDimensional ℂ V := Representation.IsIrreducible.finiteDimensional_of_finite ρ
      -- The abelian branch closes because an irreducible representation is one-dimensional.
      refine ⟨⊤, ⊤, ?_, isInducedFromSubrepresentation_top_local ρ⟩
      change Module.finrank ℂ (⊤ : Submodule ℂ V) = 1
      rw [finrank_top]
      exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
    · -- Route correction: follow the source proof through a noncentral commutative normal
      -- subgroup, then split with Proposition `8-8.1-1`.
      obtain ⟨A, hAnormal, hAcomm, hAcenter⟩ :=
        exists_normal_commutative_subgroup_not_le_center_of_nonabelian_supersolvable_local
          (G := Q) hcomm
      letI : A.Normal := hAnormal
      letI : IsMulCommutative A := hAcomm
      rcases
          exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_local
            ρ A with
        ⟨H, hAH, hHtop, W, hWirr, hInduced⟩ | hIsotypic
      · letI : W.toRepresentation.IsIrreducible := hWirr
        letI : IsSupersolvable H := inferInstance
        -- Recurse on the proper subgroup produced by Proposition `8-8.1-1`, then lift the
        -- monomial witness back to `ρ` by induction in stages.
        have hWmonomial : W.toRepresentation.IsMonomial :=
          isMonomial_of_irreducible_of_supersolvable_aux_local W.toRepresentation
        exact
          isMonomial_of_induced_from_monomial_subrepresentation_local
            ρ H W hInduced hWmonomial
      · exact
          False.elim <|
            not_restriction_isotypic_of_faithful_of_not_le_center_local
              ρ A hfaithful hAcenter hIsotypic
  · have hker_ne_bot : ρ.ker ≠ ⊥ := by
      -- A nonfaithful irreducible representation has nontrivial kernel.
      intro hker_bot
      apply hfaithful
      exact (MonoidHom.ker_eq_bot_iff ρ).mp hker_bot
    letI : Representation.IsTrivial (ρ.comp ρ.ker.subtype) := by
      -- The kernel acts trivially, so the action descends to `Q ⧸ ker ρ`.
      constructor
      intro g
      ext v
      simpa using LinearMap.congr_fun g.property v
    let σ : Representation ℂ (Q ⧸ ρ.ker) V := ρ.ofQuotient ρ.ker
    letI : σ.IsIrreducible :=
      isIrreducible_of_ofQuotient_of_isTrivial_local ρ ρ.ker
    -- Handle the nonfaithful branch on the kernel quotient first, then pull the witness back.
    have hσmonomial : (ρ.ofQuotient ρ.ker).IsMonomial := by
      simpa [σ] using
        (isMonomial_of_irreducible_of_supersolvable_aux_local (ρ := σ))
    exact isMonomial_of_quotient_ker_isMonomial_local ρ hσmonomial
termination_by Nat.card Q
decreasing_by
  · rw [← H.index_mul_card]
    exact
      lt_mul_of_one_lt_left Nat.card_pos
        (Subgroup.one_lt_index_of_ne_top hHtop.ne)
  · rw [← ρ.ker.index_eq_card, ← ρ.ker.index_mul_card]
    exact
      lt_mul_of_one_lt_right
        (Nat.pos_of_ne_zero ρ.ker.index_ne_zero_of_finite)
        (ρ.ker.one_lt_card_iff_ne_bot.mpr hker_ne_bot)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an irreducible
finite-dimensional complex representation of a finite supersolvable group is monomial. -/
theorem isMonomial_of_irreducible_of_supersolvable_local
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [IsSupersolvable G] :
    ρ.IsMonomial := by
  -- Package the recursive proof with the ambient group parameter specialized to the current `G`.
  exact isMonomial_of_irreducible_of_supersolvable_aux_local ρ

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: an irreducible
finite-dimensional complex representation of an elementary group is monomial. -/
theorem fdRep_isMonomial_of_simple_of_isElementary
    (V : FDRep ℂ G) [CategoryTheory.Simple V] (hG : IsElementary G) :
    Representation.IsMonomial V.ρ := by
  -- Install supersolvability from the elementary-group hypothesis, then invoke the local
  -- supersolvable-to-monomial bridge.
  letI : IsSupersolvable G := isSupersolvable_of_isElementary (G := G) hG
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  exact isMonomial_of_irreducible_of_supersolvable_local V.ρ


end

end Representation
